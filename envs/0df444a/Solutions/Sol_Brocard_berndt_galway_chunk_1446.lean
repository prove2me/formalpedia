-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1446
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:01:46.35001+00:00
-- url     : https://prove2.me/submissions/f8a452df-334f-4e3f-a832-758e1650f038

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 259892086 ≤ n < 260071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 259893336 1250 259892086 259892117
    0x80f06131b09080601080604081b06040503030a050c1617090a17010b03070e07030f060b0d0e07150c0807020f09100312080606090d030905030d051215060f0307 70
    0x180d50103151044020704110011040e00d030050035480c007600701400501903e40c1800c4485a89680240c401408400002103c1ca8140303803401e011042d540700c640c16119141010700341075a40340c00075600310452528000200f00882c06200c100d40c100c0a007100c4409000713035541c45018441441600d5100b004408102038151691501e00c40c1d030140c4000e0303271a5200724030992619401c5400d2451924060f030b00120080c000b204041c03841550007441403a0100f601c0d42c03020440006407442d5841111001400b00d11012440890781000340c080400d40c040310242e41d43d41168813501c040c100784c410302003002500d0050104082c41e00130700c801d5001400107580106070102050ba002811030742001a00207614090042000507090280d0107001031400001c10b06040d000140a4070407440340c20b101c1c0c0113015940c0200740c01081c4120003400014255503990305001c201030b01d2540070a002e10010154030001680111121385030303441654016084909015000d401c3e81c0b9564000340100c0184900309004802c01e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 259894586 1250 259893336 259893341
    0x4230612010f0504050d0306030209180705040e01021207030516111203090a031103070b16020c060a0c0b0c040f0e0a0209060d0603021c1e0204021201080d020f0607080f0613 76
    0x140c42c1d66900044134030b403500700030f0706020300500000b0415013001c400300302680e5817000c01ca4200a40840a40c54242e1144900d03142901990000c0d8109040c541c0f2210080810b6019001030011006a60306d2691a51811030407101e0850341061300301407103005070041a1041c0e00720740405144104070340c4d050f0300d070244c100c144e07803c00c403244102517200c1040001059400300c400c8180d5103c0000842c00c000242e5642d4401d01001803100810292808000061034401c00c240307031020402504032962040c0540c2d00404240703000200fa5a02c0e500c6402140d1201000c00c11501121407026881442d50300700030186000c001c0150103507001c1740c1c003071012084070340d41d03440100301e00e04640c40d00107206451441171104101040040f10003c1c0110307840140071400c500c0150180b80502d0315512007090003031000a0090061a50103030507030b215a0000710742201300041c1da114490039a0219000924224021540d803c401c44854001481d80030100394103910351041141c0001006190b5004402d8003940ca004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 259895836 1250 259894586 259894601
    0x1020702030106080c030d020f0d050a02150406050a060b030603060c0310030b07091406090a05100306090e16051002190305090402120f010b0901020a020621090703060b0423061201 79
    0x880b5044144500e503240b1b410449450010020b0000d06603406a1954050300c0304480402c5209000d000122425031038420300c010b03054203840e040f00d0411428581403103001000204d4041945038949030000c00d00d170403e0000c0d20f205280040c01402d060740e4101c600c08040d00090b1200c1c8040902103000700000d00c000848900c60380c810361382d814006181c050038100d03043c1e104249038001c03c3c040052061b0b680700c4008110940390103494000c41842001000c40013410168052010540781c03941d07001040b030020603102030f4540c4030070800c01040c4e1500d0400200381968031524000da407214820303886a0651034a00000c1e24060f0500c10b041c0b40328200450143c1e0701aa40100a5940302020860440d00c3c0360300c01c81c00342500c1d104050400c0040c000107565058400c102900c80c030030200300303a0f160009041440300480c450b031443c41214140b10704243d9a40c8150300088400c00c0c01c1141c01505418144212256021104107010307a40c40e104514450b245c801a20564024200701c4030102040300c02d0140030b8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 259897086 1250 259895836 259895849
    0x130303030b040605090106050702010324030515090d120902060405090a020d0c110a0308101e030302070b0f03192a090f15050f0d141f03050712020301020702030106 72
    0x1d0a10084820001114515004903100d800b421700107121099001e415030b055640e0a00b0300103102c0900000c0d080400301d1812588081c008003500210411502141c81048040c02100491080d1507416445072180303441d1540500042600070070a203156150380041e84050300180c43c4a18087c5c40c1c1011072030701d12088868410468000451007003d60140c82070042680742840c08020701950f541409440d4170b842c010180411414501081025841d54000c20041c0792102d4000d01800c0401c4006162508a1005501500440c000014031311032200c21102c9014058510516540da45400441100e80501c0500c0700e0b25a1212050381d00c0f16441000c50003102000301d02c2c0e5100d0b41c40c4000500d00392481d001400401b2418004104000243c3c510801c00b4039030381821a01c50102131005402030052440c00b41c7e17030301d05017a0034002d60030003540414081e06121990401d1504000c00000441c02c1c070b40300040075580001400c0181d10008150420b0040c8018005840c0800a800185c00d448482e0004c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 259898336 1250 259897086 259897091
    0x1104030b060909063112090b040503030403060f02070605151002030f040e090a15060f061701050f010e040f0507080708070c0206071a070804020118030c12060213030303 74
    0x244144800d40384001c1d03001c1000c860700b0340c1c1480c28200c0b00351101800741c14003c9424500c0c0410a0540311030030003020320700c0b4285000c40c0d51006400c1007180d411b0445c1c4114007047c1d05a0b80400d034100680111000d0b0b50002d40154901451551014024012042840d118960a10808000505130b020380c600644500c4980480105d5000401c004940b59403c0c203004e641c01000b2a00200e40f00000341d408581c01e005034002c190740c8404c00d06c1d04010103a103004188800b448000c04c80040729a21175000e84d1558002c441103e0b8482030b0568011004182e10389c041c00c1000010882c501d0003d501a2a9100601d4840d24548002010600b5100400300316801c81740c13280100144280c0c041c1041d03500500b20320b8145d0349410000ca014025a0350180041e020b04c03030002d00c140c10301011084810b4464014200000b603071a201c0001402d800e8281c40c201d001465264070f409115421710a89010340707803c110000d15035854a00c02c0e12600c00c8140301101c801d50241b0849260b1080c0d00c03071000c0214000c0e2000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 259899586 1250 259898336 259898339
    0x60206043908250308031012050105010918030c2d111c0209010b0a05130e1009020a1b0c09050112030905220c0201140c1215010806060a0c061104 64
    0x65a0622007110b040c1610300d400c070b4655060f210a040c004208598210307005a03a0782e12200032003074a50491717411241551820160714000c0220550000e4101e0301401e40802c0424442c0c94100740d4104180310140c0055624440c07200810464220710b50407040100da11000010b85000c0a01900f0b1a800140c3e40081c102103008000d04084503001081070b0080110141500c6a900041004c0010701442d840b1610100f1071000240c0143d00310380c6a41c000c2e8018000c4c0c982d460708020017180003150a00c11082d80c8000024041e180c6000703803492101d5581f2006080300c034048000d06d90b42c0202800389c0f450049881c00040020701031190b940a000f003000150480c0c0703428280a1710311116940b00a005102000c80a08420000d00d0349404054080001045072058410200e01602c21850200c070050003181c28028000d654400401034850503c000c0a503990311025510404845441d11034040740b02003002031243d1509a006042a0b01541000c0300000b103130f40c8a050071601072084221440500080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 259900836 1250 259899586 259899599
    0x90f090717060d0309210c03150b0f011d0d06020a020102040501090617040f140f01050105041404021c050304030b010b03060f040902130209040f0f02031f0602060439 73
    0x4940d0b41c812825142c04880780030300d507401049030307425100e11001110980c0a50030124885440036001c82c3d000080c0004030794580c100107401800c034039603040000b440d0504030700c41d174203041e5200300d4800b005031160500a030082c025800c0d04000d01c0038071944400c180f00e00300005500751001c0d003800d50903a0300060f203c50408001400342446500980248039051400180f6080107004480c1e10545c00400121119594502034124102c00c2321000900d018050300038058440c150321150403100102c60600030800c0d1245490040041583e000c3d4200d02102c080c1101c2038008a12310b0b802c00c0c4140100d80c42c0c15600e03150520154000e800c44000b000000040c044940303440c00002c0300d0703800d04503803c11a04d039890b40000c4401c2104440000303401c3d00814418501d90340e0f9407240411080c0a4014001b007030140c2d82010003944201c4282d82c1c1c0b6650031502a20128070040700409580c1982c0082500e519580c40d000d84030018407800b10010700f1600740f00c803080c900501e60348070524103400c1034405441c1005c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 259902086 1250 259900836 259900877
    0x607020319060c020307152a120c0e030a0b15090a1a060309060a0b0f0a0b0702090a06081e0c210f06161101091209030c060c1502090f0907 61
    0x10203980865200f03101b0b02020403030310100000c2084030030000003180050f031400107851b28540c40144449294100b030110900c0e40046181c0c0350103208036420462401c04000c00d403081c0c10740700201038150707200b00b81290016406019441c0c001c0003c02000040342c9511000898500d8102c1d403401d40241c42c1e05896000d0019100320111080301100c500341545803d54280d5942d1000401d0003c50301d0700d4041c06d6816443d01c00812a0741c49014102ca4012138640e020409168024a81240a840101c00107210b50207203109420075942c00c0300c09003598040c4c00304104000352074001c002c5458068070000d50119520740b00c4801c03040b0907140c0e20200315864010321034104070019094065540200381080403070304905c0e2185640080d07500700702803041e91405040b4010003590100408819108030b16203035031078205140c402101c0c42004d01c01c3c0c84984542007100c0c000d4071264001c0503950050200c0700800c00f2900070302501b440180c880074841082200150708034000352000390210301c1942820829180a8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 259903336 1250 259902086 259902101
    0x3031b1506030a2f120102040513150513020c01060905070206100f05102c3a080913020c0106050409080904050c120709060f02010506090f06060702031906 68
    0x440c0a0090910180c4591007035800ca4a5a4030b1900a480b41d0f00c00304c00f00b0401c04007144000a400048015404c204140c000e520900170244641f6405c003031520408024011621202c2d8800c00141c211490031080c0012040313642a007001041e007c0c050020241e0092040c1001000994408190750a04040290510070041c0141501c81903824090260810070440c0c10201d88041d01e0700011024041003c03500300c150202003650304071a03a5141c0000c0c5940d5030b00429089812501c101c600d244501d520088001c0c421074545100d2035900700c0680c000070b070108940f80e0710700940d809031401c450722000441c50040c4000b000f582c00d0b4041183c0e90030140c00d22a500141c0b038141d800304181f1031207840c0c2000b90b000d0341072054850f5840b800000c0c1840d1122080c1c5507201c502d41008036550801510180c4081164060310b400142604420003201e84140142c40c040d21001e00b81196540700d0b2030f08040d4881c2c004145a4000c50104007500051728108009214412900c0b81c609480e0751a21b0004162140d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 259904586 1250 259903336 259903339
    0x306120a0c0f21030e0117010909171c1e02030f1902040b0f03060409140705030111030c070611190818030304030f0315051c1203020c030f0903031b1506 67
    0x41003030911039403d07490040344070342c050034032182c00e0400070012250360079034012000007400750307100000f0b00307071310682000341064404c25014020011040e1602c9045c0240c090034107070181c0d500909980100b40e1b501550f813854072180c600705902200268003060340e00580d078150003400c0010070006007045030600028407002a1300d042d031410b42b815150201c10301031000000321082c800004944150386503400078410680c8169001824403203214440c1e113030139542c401c0d03d0180d4200440329590406200880c0d214088003007940b4249521901c6110091526100a0740007400801045083e4440d684410701c0d403c8050707407a130800e0700e40300010303440440e10522101c4127944103009020000f03401c4400c50890b1800c5203000103801191041101918150741d100e01e411104e459000c0d0203028500c291162400e000d0071304540090102a8110102c2c451000c425007181c0040c010f42071022500c034014840128010200c0f8100500c110490041740411681d44009038030418004201c0072600354110745c850030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 259905836 1250 259904586 259904609
    0x70f020706021f02090a0e0703050a022802010905030409020406020f0106030308041511031504050906160c140d0203040e0a110712020a1203051503030906040b0306120a0c0f 76
    0x9000400b035921240c5114520020100d44803954a016059060ba4480c0400400e1444031301e84d40c40780c3c5101d500090341d1690000e82008009441000d060080780c5200e036090340e244042d90005100c800044604d015024110354075040d210700403560070000707000501211007005030360394030304000646492030082c917500340b590428104001290300040202e521940018610302d6118031114104c3c01040c44c80c030b01c00841e80001c03050140220302100341c826400c5045c0c83c02c019a40300c05401650340e030001c031140101c00c1248400c18464910500300d041e007030341c4201a01c44030500d448046074100800d9220010060b03001013400c2000d080902411034001020150410600c0d081ca0481e0103540714000f000703070155201041c20301c0340a20810600030308542108030326444400d840c174014041c08068410344820705840d413005400740340200803a1140d02006046d146007a150680c203001c02e4000078406c0d907200908401e4020940d20500000d42e07024455440070f154581480400d40d41c000c0c042d0404882c196 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 259907086 1250 259905836 259905839
    0xc1006090c121a060307090f0f180513110a120f06050c190516020915091005011b0303060302060a050309070e0403020c04272607030807030504050321070f0207 70
    0x50f816914200c5520191400c1d1342c1c0f0f83da41681640c1040c125031280036411003642c000100c174108140c03c00143d58000d2589060300c04000f81c01000d64405940144084001c0e0750142c000580001002400083c05403000c09100d0342c404484c04c440c14200001d5640b890203000040030403040c1d100d2103a012021440403801c00000c69107441140000b082290f050140c006090080c4007002040e0804e40350b8010242009031401d008406104025011680c1c000d10075100032031030240f00b0b98505019a201079486210082040710012004070066005505066950300c0c08805612000c004000702d075441d0301c803103684c1d00b0110034081c64004c6540c0701c0d04928503c0c00901001039400310b0081c905000403507020444108080d8040040c80004000350140040e5440f29800c00c0700003090364610503a64242c100780c104e1002c0078000305104039a00200003030303030341d000040119000b5444070390054028802c49040044525030071000c0c2800b040a01c008091400801c606c403503005103402c0d0070b00418406003183da03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 259908336 1250 259907086 259907111
    0xc0302180f010e04022b0201030b040e1002211e010609030201121d030d150906031a04050a1a0a0e0a030f050a0c0c0905010305150402030303040201050c1006090c12 72
    0x103038060080c0449038025001144c10355440c1801c1c003442000881000f941a2184100042e070342c003429804a0100f4107001c10a40e43c0d190a10070142880445000b800790060f1000411000758085050803055500740d030000b102460b041c1c92540e04c501442881c2c06040394040001d003048a905034042401c005a41d40180010303603000640001c040c0303010f00040ba2125541d4003d030394a201b040e148020500c000324007098140e01d6500500310b020b0308200d1440069031980d1503071065a00d5030102a04152050020f04008003801c42030341d03401401003055400003d21591043c241901122012a03012140000e115080d8001e11803c0c0380c9403c00b0005080e403540c00d54004d000c0c1c00d149107230281402030200301c181c41c0d1800b80301c0b480c00c1e0f00d6100581c1006941c84018400c0106404e01051392a48540c818001c124031394101c2071401550010f00950840d1b0b102c2e801122170380e00545440d4042e01402c0703c1800c401045000b02c4010300821103010030500c0c12550300600103e414181e07049038030b0510301400c205 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 259909586 1250 259908336 259908361
    0x909050402061207022b030609061401050c031e09040e030a0c0221070810050601020727020702060706050103020103050a0b090f06010203090a240509060d090c080a0c030218 76
    0x321500202c1c007203c140c1d00c1041c00d9050034030056030650b01800c800075100c030341d41040c01c4d48040d0100700d49003001500d8540310740c4030031282c0d5030181e06e41300303068042e041c191580508042c0ca24802910304480c5422400201c6000140800d0350140003004c0100b080c3d0f07030901c0e003801400070b00d032050001141455503656004144a240a2000c0c0c0108500c2c01030200040503580100056000e50045481140c0d545090f6075807000d40285445150713160801246041d840410707150210b0300024025500c030152144c0100c0345c0480116020b040759070811083d401a154000501426402150001341961450001405440c0b000b0685030500b841d0000e40c240703d98480081c5078008030700c5540d00070f017540c501005030302e1481441c1070b40303500800c2c4060008510b001c030140110007466840311003024000810f41502c840c00340341e403141e82c000802d11000e403a00810760b205c00c183c2401400c000300c0956440e409141802482001507600741c03400d8800b84158100701d60326090340320054110220701d10b480c40400b0720 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 259910836 1250 259909586 259909597
    0x215040503070212100e0c1e03030318160303030c11060c25080309160b070f110a0f0617010e0907050108090a0210031e061a0d060f06090501090905040206 68
    0x10031400c900d61341c0e00b40d0908012442d807500c3c00035401c001410000200d61741e10150312241e14416680d070501210344200c0302c1401c01c60324101074000c5003036440e070040e40c1031090141d502d140e8242c030500d00c1c1200c2e083d6500401c500210700a40b4005070f00f6960510042910300044d0030340b98a64441024045840b04001c112987e4a05200c0311101640040000100254411402a02804010090201090340440c403440c81a05a0524922441d0341c1c0c07500300d8075405121806042d880c480302c501c8011903014480030072a45030092000d44142d03158800042e11a40503003011000410038066448040f02102c010f40c007400000c64181e5407407500940890b50340325103000c0e25040003002d00c0403c0d01c444003080081c04080e8000c0c040403a14000d00c000600500c42d0700012550100310400307124003c6800e100301e40070340c0c050302801c0b040404c145425400c1c0d5030100c20352010b00780e503454000070840310a99404014001c681e03034039001603103054001440703095103402c400b1046203440248030060341c81008032071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 259912086 1250 259910836 259910839
    0x40c05090102060a052a0f130f0e0402060702060304022e021203060f0409080d020d05040b06010c1a060118080105150a0e070309140a03020c09090109051506190b0403020102150405030702 82
    0xc10900396104110b01401240b5140d10354110202300702d15110b600c00c000b17400b5150040070f19009155078803002ea0107a079050360302a4009a04002a0b00542041001181c2c01400500b08a141927084107510691078145400c582e00400384414000b40141e05110400c008007181c8409411400d0200c001055024000e40651159a4400c2000b0400014205903101d942a4500440d110811000c43d10302404088404988800d100c0700010f00c158040c1d002000d0711900a540611400000c0035059082000a44664180700380342c4d491745452002c800301e14014007a00400400c1b44d0030690010310300400e030404594400c9010580c10f0000000c01d015031548a44246008985640c581c205021034247e60721528849029010f441c405141d000110300c20702c028151000341e40f0355181824030f13088902c10f03d40100b65070001c1d0300495040000c09029908904000c1108041c0c002000d105421043c1030761103441d00c0c0c100400e0030010340d0b805120349260b412480715012000d140c00e43d0ba558880c4944000207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 259913336 1250 259912086 259912141
    0x60e0616170301080d0e0406271b0512070504050d06021303020a030b0f0a0513020103020904020d1d0f0a11010f020c040e0304090609020c060112050c040c05090102060a05 75
    0x300c0500900381e00c8012040c0d84110034503a02d5845403070035910380c083c201d60f000c0400d05550a54081c2d0600c0c0c45035404a4440120307581a1840d9a039001d90300400a07010040c036591190750b01d00f01e2940c040380b0100c0c0c1c036002e86c85040d61102d102c4080040311500412881c10b0000c02d000070840c944400641020003a44902c0c01680c8181c02901d16016a0950b000a0341100340e14101004004100d1001402540203a08036580303640c0724600b10054a0045070126440c41c1c4403424480103500035006480381402c024000750404101c0601c140440705840701780d100314081d41124030000801400000d0f8410550805400b900c111516024403000340009074904020501124540c51442031180c0d0000e100024024010403080103911a03481d04980140314015281020004886005100b1603e02c10419005802542c1c6040f20503840342c100040309450300d00502c003e80881c1d689510920205c0301c02c0b40c640c0b07512041e501000901c1c00d00014440c0782e00d40e14001c144a2a0420026080448000e81034503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 259914586 1250 259913336 259913377
    0x902120c0304030908100e0f011505010302210a0b0907050a0f1407050109060c020c03151302060c030705060a1d0a0b1017060105041103040b0c0313121206060e06 71
    0x210f4282140b5800070803171703009203607160f03416111640080364100101c408a5107442c0c0c1c002c003410b00722130041980d0842d01040c500b041045d03500030f030040c12130141d034200b55100d08144494050f5620b6000c4130401c11007541c50481003400d150294105401c11440d00e405814040000c00c060200003047c0c0f005020720000094215041c1386550803a0f0f16986d1290007400111507500c0c01ca4041e2007011103010150199055600b02c1d4100054502c2c003148402c400b0141030380b10304d4110380f600c06c820b000980e00700504200c1c0050040d000c0008022103442580207000328a090a00001114900300c109620854550380084007000005032140859400602a1031030ba19500d40d4850345200903404100c4154040030f6408121602188940c103c46058a0a01c00404110f056000d0740c80102c40c010010b20001010803010310350200510fa0000100200c608110305a4544065034400c5400b40000150304407010540b41c00c10340140c40041c071107401e100106179a2000024128054814075030581504e5041c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 259915836 1250 259914586 259914593
    0x602190803011a07050a050c0102060630071203081b0702030a121101060e0f090102030c0d0e07050405010b070c050303090a060c0206070f0305030a200a051803010f02130902120c0304 80
    0x858144560105c1120482c01c0e4500c0c050b0340b210000766210740580512400659030341400b0351034503c045050204500c202050b0b1242e0700441d52109510450352094503004520741c40303034500400300d05001c0c0d01c4014180c41c029a69801e01f40d50317854020541d5074140811801601c0020b08512800e5100045040080170f12000702d80400c01304081c0542036081600025104040e804290301035044040418480c0d9900001c0909074402954440d01c030320b500b003140007082d05c510303480404459505010341d00d150b562980018181c440a0700400b5680f00c2c0091003208100b02d40b10b28000401d0700790b001d942031003500d500080f111103440c1b1500007032250002403a8115554001103403109030784030f03507010b00e10505401c005001da0000c8803003901c564038010700c0c09081c1c122209a0048a60000344c15482c01035403960440341074011043c0c4e8004241510030303d15190f41c2c01c0c0203212115072182001030704d0703c0b4050b1140040311861fa003c1801e907481040078144510070600140c0c0d110a4400060b56240c6031880d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 259917086 1250 259915836 259915889
    0x41505101406090d0c0b0702150a0203040e0c0904020d0f1b02030d0f090f14060f0f04020f12011a130e060c1b03030703050a0c030c0206041202070e090304060219080301 74
    0x301300500341c0c003810360049042c1c3c40c07550203401110700030b4a44000300d2641e045210b030030744120060301c8007680c002d205c10018480c1c0402d89542c402040c001d4107040020900102d41a0780004c54605081ca07110f05420140c4110b602c15658280381180120f81071312031300c0c00d007c0d460344a4a503112101e41d40f501203907180c10b40340c0e8101d2144160b20020164842c1e0039400c01ca08400e14400c450030b12802094007007174a08125980080c0204082400781b240c03922554204000c0380b4402d00144d030401d03010122a0103200b001e225101c0810880841100e02030840010001e103010481180d010062814021455a64000031040c0c0d1010400a240d5600d25015181681c84400b510300c42006100000030003035081c1d0326410040c000d203000c9a044c00f241c440e40c0c100f6020740e01500b44441c01a8041c600040100d90306c1040b0800160079070042e40c21030343c0c803890051000c240407508052140d10020f81045010350400c45240d40000d900300c3e22030542c907a42d881d18040d1006200310700c002070940100c80c80c404c040704d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 259918336 1250 259917086 259917109
    0x30f010603050603031e0a08070c08040506090f03010509010e060a2f130915050604060c0b0a0e0d020309100207080d0c030306180e0d091a0c0a0b04150510140609 71
    0xf81102c814900346c80d40341814a922203070400d40020241c40201e03411a0080810140d00c69005164508007420030040c05501e421041e1400d40c0084000b50290035170b20b0a10625002c0c00381200042030b0128070038881c61408034042c0140c1145460450ba2014440b031019601034106903c84503101528603060100400307000b11600d03500b0140f0082400140d01c8000e620034401030703030300000d1241d903c0e913240200301c801c3c0228840c00c03020814168494001651a0aa45512a031341e400c0015812220301001c1785010401075440780503a20010320140280b600c0074110150840520043c8140c0303040c41c0c034043d164070904403100d0030720442c481010205806500054046d110103e25400a03480c9254504060044403401c1081c501801032003440251041032030390300f034500240480101c01c3c03200c4c00d802000e6200b1409905c850140101c0c440000c0e2554000381e004a001710004c3c25090301c5111100102c800c085c11200ba5250245001c00102080d45040d900800045070b030346442c1d0301c1c1800411121902c6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 259919586 1250 259918336 259918357
    0x41701110307090905061503070f0206010909020904060207020109030519060e06011a1b031602100e0102070b130b03070804030206070804050c0105030a0f062409140d051c081506030f01060305060303 87
    0x401040702701c60744410002c1035403400b542241d1003641c2c0c0351a0318040301d1045001075004142c40c00041c010801507001455034620615000c207410b5601d48419081944415000031510744e410b02000500c2910300400c0340c0c83c0f00000107010154900002d007000350545948600f00d4410200d0001c200d154114400082d914010050301da45903000c00b00b100040140084c203d22030713500d02c4003455801c0d101e49a50701036040180c0040c20200d013441a00381240c1c000101226401e914100d01140621800e409140204a25100c40f0700504291401900307105d0010858410007102000304070224200242076410304d802800c010f50380351154446c18010344113407109043d10720300b824400500c0303551264031400f03000041e00b510380002d00d491908503003550bc50321640324160911441e040d601c1c80c00c050192121845042199a40444180b00700320752000d1041240100c0c1101702003002002c0c030968407500c0b0f8107084410500d94a013444641405036810300a043c2099601c030006421510308004452a0012 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 259920836 1250 259919586 259919629
    0x30a02011103131401170403080f10080109061508060f060409020f0d0c03060c020c03120c0a0209040b060a1d13261b06060616050102070804170111030709090506 71
    0x886480804c292010402001d00050314154040210540c20240501565056850020316198035103805005c11016044081c01d04a0320340c0016102c1c000d10601095911500b008208500c400c0941038040324181c0c4100c405810a00c200411920200c020507402442110f0010b441c40c0140089096949000d03100c5802444403440841407144c030480c201c04592040100b80098501e880080340c03502c155002040d050b600003e401d859411000024010324220030048404c0360320903800007203808406813820f0300c401011000344011420400c0c184000b900f1f41d02c200a00c0042075080807407980800a048510300290068110700300b10190384000d10540d001c0506d10704460240400f08a507074001d0510031002115000c08041c96840811080d02c80c80300103040307606000c01040c83c1d03034000d902c0034000ca816560070000d84001800a0b0060405050b8805040c500c04003032040d01401c50b000896555403255080c401c110006511014202c01c0d80c40c50800801d0301d480e00004101c501d10b0309605100240d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 259922086 1250 259920836 259920839
    0x206040305250f060b0a050f09090307050102040f03030f030c090605071a010602030a200a0b0405070506030a02071202150a0c02010f0911010801060c12050c03090d030201020306030c010e030a0201110313 89
    0xc2e04180e40030030f02d0094504000c0c031101441080002c41503845004c1d0440305086090b100c0b4034000240a5100e001c10301540c1c50444169074107030881e4090307008a00032504100d4284103242d80107004a51001e0b031810200010400c0f10000b030710440c13151040004112000079a48104041d481c159510032840e4800300c2115615200041d40302d8005c0084200001c6004400c139a03603c2d000300c0460080b815250184c02002199103c882c3c24601c010020703a144d2080c0140041da035265500298072400c26108016200d408a00d4480b800b144800404800c56102000d0118800b0782e03e0034440e00300c0c810a000190454118909a000d0400d0a000148451503e02c108003400809011000c2011099807001c920340c2e05e50f002a01c01410950002d4590081c280c0710f65030300790044d0024400d40c1204011a41081c94a800242c6c0c4c00c4061002100180d40120034494a810100005031f00d84209080003402c0c03500e0701c8042642c506d19840041d04002850a2070285810248110b414401d05100b01c1111396 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 259923336 1250 259922086 259922093
    0x60109020d0e070308040306091a07080f0901200d0902030a140d0f050708030406090b0a0608100e03250c0306020703170408190933050a020604030525 66
    0x35049039000340821802d0904a0b0b215040c0401e00c40c00b9a940404031505190943e01d40ca0300411100e4000c54414107030442c009000f0480c00300071880340c034080d0340300101480c2400000d101034401418841a0313a0401400944080c90b54400c1c1031394421060300640c1302d13031018503180044d140c4403038007a405000c0c940803d414449852418a49003020f04101c0d20000d11349001101c440410200800001c1c50030310800c000540600b00840d0094011480829400780e10713181c000c0240d4040c0c4d00c0362202c2ea44c1c0c0d50100070160701489220b0b50503801e40400c1100c46c9a48400130b40328401d02401040b4500306120b0381d001c0340c81140d4290f0640d43c20a04585500d0b481c3d1030001c000b940b00b10000e1300030544a12003803983c1801c801040c0d20590340083e0280c28007040b010b600c0380d00d202c100005028840300740e0b000705600318441d290b4091601d4604a0142040510700054001000707015141f0401c00d040025803038447e0009a2243c001d1740c1440c2c42d99a03503003032010012010310000c030100c1c0304490045c49101407 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 259924586 1250 259923336 259923341
    0x6090204090905010c0503100905100b0f1903061202210a050307051915201603090512120a030209031506010e01030e120c0a020d0614100e0126060109 66
    0x103083c0316000030841c0707000c560b01c240d650b80030440f83e1030b0407000c42c41400e100d20012500055003050b05400720083ca0b0b6124440000507810210942803841c40114001c64800811003089070386640d103050400c900e5043c84c90720460281c0300d05010f0700440600c0d1f240000c490114140c4521101c0c402c0076580c014040b482c1c2941c5940c49184203035414411785d00080b0240416003481201d040c2d0041c2c0c00544030040880000c040c100180108000b1001760301d034100d40500c0600200440542e0034402522030f0303550310700a0400340745600034901a66149041941140c030019200b510000101d40c0b04e41c465141c0c1c5401c81c003a124801d4466052b0042000700d007000c402c542d0301c050103003000340ca0349004070740700800445c00c0360007031100e01c680d80d8041c0c815220781c84040e000400340c040b050800e40380650090b40210f000e1071000d4008550040d600e030500a1080340102c003da8020030380301032201c0568a4410707080c413a0001030049640075244034140024180501380d110fa50035507040142c0d2004d40c2c0d5400712000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 259925836 1250 259924586 259924601
    0x10090507060f020304050f011409030a0c08190b070309021212040f0503011a010509030c09090a1a0702071a040302040903031a0105040302010909051b0d06140409030e0111010609020409 81
    0x10500402000b42500c0c000301c2510180c64003c2d00703808000d1561001111451964494201c0340c51007004030030150b84050151040c6135000700d0451100c145020400b41c0760103c03401002d10442c00011440002480805c442e6401018602d00410302c80e0480c00014403a0b25103080c895000c0c40303480844112140c2a002600803103403a240c8001c40e1316510f409142c02c1c1c80d001e0520300c40c0c40c100d150b60408658012406468940c4000d800c907841c00e0020004648404000c3d208041e441e44400082ca08000340c5001d028510410761021400c1800c10280c0070356142458020200100982003007403890f22400c009a9006580042c818009000141005030007403049204a00c005022114490b201d54000c00868040f44c3c0d042c0e483d200c2d241d26012454008050140c1444150240c00c04103102c510038140c0605118060460000303070301850200301079014112101850300407401c05290b040405d4000601a0380e81e002800c2c07500c6132a100c6201719004141941080e50501c1c0b012074041809021540103e4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 259927086 1250 259925836 259925849
    0xd24140103050d0f0815040c120f0e060703111605010f090b0703110f0d051003060608030a03050a060f062607090e01051f0c060b0a031113050402060a030b0310090507 73
    0x104d41204c0c044200c601d030104455442d0301d41a5000b040c4a00d00749644070b002c0e400b1417403900c0050195030341d140100740c0386066100c0103036540b900d150183c0302e0002d0150079040001c0342010400f0449180400b41d6502903030340100107a5a03100e841c2400e0000039005141070200504042266254600d440900b044080d030344070002a190884103800d00f00007004561070981c41d413079000d041881280409014050003047c03000c2e22000c0000000008101d80500d102500c040d50185840e940f801000500f01d5000400410780581800d4040000da280c40d000305054607200c1c54000900100c0e000151100e03003d8905652603110001c0400420b15400510201a180801104c01d440c1c0d9842e000c00001165048100c07015114007008019114001e421082030244503080c00300704a14040d00040450000340e0041d2400711000012a00301e141120311211006911002008035003415000300b001409201200c04c01c0c55a00c0b001501c2c6560200141400120107100c01e1120030b1813483c145445907418801d00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 259928336 1250 259927086 259927097
    0x90806180c1005090621070206010305101e020a020321071b08031612060605091203070f0b100302030318010e0a06021513050102030708060f0d24140103050d 69
    0x505031070b15035100c0391490b0443d034850342002128000c114540d44545e410f01a03082d90703520202c200c0320405007107902c40c40c002d8014010b15851810300c5401c1c01c182845041c542890314240c000704984c2c078203c0d2036113008000001a00c0d952424010303072440c850616145071a440c0d031141c107604080c00a00081c0304940075a02ca500311000e08030031032180fa0441f03000038040941807002442800b280d00004003041218941300d5007918901e240c0b8412550329070041000954002410785483c20424910442022280700851410700c164550034000c400403040140f64690000c081084a10000d92120196070000c00b135903512404204c100030444a0000300e2070105000d1101100305282c0300c034210b011282103801418003681200d4060384030020003040004401c940c02a000c1c0800c0c0e09101540c86002140c85000315820490104038204200148035807003044c01c01c110381d000411202c07400c0740b400d81da5100303400225500c031500400307084651500410840c1540001003409400110645031031507540fa01d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 259929586 1250 259928336 259928353
    0x2030d090308070204020d0222030b13030c060b0619030b030c06040b03160201110d0b12030a02030405190509131a16050310150f091d07050a09080618 66
    0x40d641a015440082c014880c140400c001500b41500100304034811400014030309022140b0140d03030082600e4892a60007c0f68005108000c1c507015080c0e00f241c40c0241c4580103881c199802401a5860140202041c0d00c9074084240c5071600800d556400810316155104102c0c4000001c004101b00900c840c42403040040e60001410403208540070340c0c81071742c980b910355a82c5d003808015140f02c0e204a58219075949001510b12020304000d8054541214000314103459002c04000100c101a2081203950700708000494080703400000307c03001c989050300d15906440c01001d00200400a03684a1070300440340104000b0001d01c030602603506544502095215036001e00c00c1c8000c040001c0b90340a10b80c046007010b4100841c060400b847d4005088680d408030b203601d94500340c80300e45250340e5403400b0480385080140102e4100c0c02e02c0d4090300f81281100d4056032b01c0034450002900290881c000c3c005c0020345c034030003039110314030001c0500b0f120012102e00e0305240010780c0560000617070696260040c041c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 259930836 1250 259929586 259929613
    0x190e120d1116020d0c1d0103020907030c1b020d0b0f070807090b09150d0e06011a13050f060c010507020a021008090604140a021201050f180706030c030b0d06090203 72
    0x41e601101d1001481c0124000b41e5401d01103480a03031203050b500130042c00d5000409104034205d218081c00444042c0d07269514500c103002490720043c1c1218241804c08840001040c2d00849008009500c881d400840c005180041880c10b00c40303e00c01307003800e4150001c0258070b00072511440d01604540d0b4031a461596070071400c4031441307070301e0203105034040d400c000712442c900e0482031615064510030300151901c003594503900221105140c7c210919044800104245840104540c51184254441626003000848009084c0146005a40c4200a1881c0306d07401070303e4000544408601c250300030000e604080b680a035a40c005414100e01c01c1d654613139000b84841c86488a107001d052900018540c1b40c942d0f503180ba400500d4129407014601c070703201e5110050ba40d050702404c000f4192000000355400c1182074201c05007002020b402c42504091070503000c001000a2140498059180018407001c4110040340a401140422a8495000d00441c0140f06e126400101200c0c401c030200d408009440380d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 259932086 1250 259930836 259930871
    0x154d03041e030c0b060a0b0a0801050a060306030b06040911060c0606030d1d120102220e09010606020d0507030c06050115120e0304051908030418060905040b190e120d 73
    0x10010006141014900d002544e003000c90303504084000c140504c0d1507150010315000d40c000e051404002949800104014104240d8140c05000c09240501c080c9045440e514219000507100c24007c0b0f50b22118401441102d251603d13046c01c0080c00d05079070780590030580355240e20030340b41c203442400780c586881c0605d4064610850b650a51240b44a2601071071010450401206079504c0701c155020480d82c2801d00140e4003d030401180d4a000080720b5003443d00003107011500402c40350044c1e140400503c5069000070303040320011203600d803450761013129180c00c90311200e0201000384410709100022818042000c0f0030001c218082d55908000d012444140050300c038500d10242c0c0d02c1e08108014004d609014000300050483d03010881c03000b90359080c0c1c07a071940c1d21540c400b00030403145280001001c1c14900411008103100311080c49603003000d80719650685000341155031850442031000d108400c0e1b40e001107003d2400b0105031900c40c050620b171a401039002c0161300700d00500c4c062017424548203e9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 259933336 1250 259932086 259932143
    0x12040308071d0f01020c090109020a02011b050909040c09020307080906101a09060c070905060321090409020d021822050c01031d0105010f03154d0304 66
    0x202d10884405100e418046000089400349045020b4181030028940700c1942160080040f070b0b1005a450445040090849914507003e04901301d02c2d02c0d00c040c0e4284c0c040c080d61080081241c0d00240e075200c42c98140c0d0300d01c8090780301c07400c410b00100c00c02203030980004069104511002c152130340c1c1c0d0342c1c40e1041020907000f8040c0400384202113050440c050062005030003003241c040d202c2071034106160611880d100980e4070804405440f4401c100c0b1078101800b070190340b20a14106002c1d840701d07214071154907010f01c0084034025540d4250034000c0d036580c1c02c0e01040c0550003505056000d40c0310342d07083c81051000c07a1190307510700b2071180f030000c0203004480541c000c40d00440900070b0000c10f40011006406400094007032619090317282d00101d1000c0c8a4076000300f0002d80c400c0c4600e8075500e00a80034500402081e480d4a03e0a604240e808065195800100c3e9095110358800040b4458500c401f031f100000c0b040c0b16101c1c9200e8110000c20ba10300a40c042c82c01540300900c0400c080c007640b00d0360f1846 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 259934586 1250 259933336 259933367
    0x270a1b1e0918060911010207060203190c06020d14041b05010905040b030c1c170c0303060d02041b0c0204110f0d09030201060e07020d090602120a080c0405061204030807 74
    0x142400700540712540d480050503441d0307078603150726001180e119031042d503411883c01e0310504c850600c40901503804102c028010b00040c0040d40c1081c40c001003c289428600d030580b014050790845040c20000c5581c125a618004000c0170842c1d102c0748000300b1055041110103c4a0134121000c250580d640c8a12040459405941f4080d0b4903003000305010180023001001501881440e10b000b1240e079400705000b03247c801109001c654054141080000740b140300b031380d03490508000c005446441d100031089a03444a401c1d500c43c08010814801f190081c400c0c10060103648110590040c030311035101d0041315500e0300840d418403840440301e08040d180d1164458070700c0501010803411001a01c241c1005c4070450280c000080e00310f030384806003da1480c080315a2401a080740088032003542e00700e40444040c0400348028461110b6550410b01d4500c42d090700034090140f0000000c1d0250300280481d00905009400382d03458580c068013150006005403001c4010401000024410b984140c035645a8600c9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 259935836 1250 259934586 259934639
    0x90a1406060f06271903050f0d0f080403050c070308040f0314190b0414031803010f050f01050d05030c03070503090a090b0f06070f0b0403022d0303270a1b 68
    0x8030300300041c1ca00044455960304803a804207217008290f1a03000381130045008102400002640c481420305041d020306020b424000d2200e00840d4569120483c3c962242d03250400075511500080740c180790504a0b0700083c000c800008003ca0956641d5941d041241d104107040c0110400c071032074194861052015100320804481c8085c07012418849800750000d0040c046d0924405540b801d107421640403c1c0d4038150703070860301c4109246003800d1141040e000d003918010040d40c00c1070780c017561100c00c1c10310801c3d1007140400c403514144081441101c158403a0181101e5035a00140381c8584c8980280c42d10301d10031402e1080000d28801c9502030000082130040c00308150130714001c100231445d04944801e49440d1400b40c80c0e00300140400c0d00c003a010f58041e40003403810400402c1000486074a0b041a40390000d11854400b050035800001e5035000004102070342190740c03c84146c01ca184442000b004044e1140600311070502181a0171041d11605440509841548540e405428080c041c0c4403503a0030300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 259937086 1250 259935836 259935877
    0x7060e071404020309210403051504170702030c3d0f02030301150f03020c010c030912170a02030901141306060905060d260c0c04061a040905090a1406060f06 69
    0xa0201c0003c00c01810100076142040d848e070b2102c5182c03a49401d543c06400c00d5401c14403050080c4441c00590303a081c080c0809150000c2c40c0e001c039842d443c4103481d45001d002900d052401d04e803e282246842d04c0c00c1440e00303175905c5c2c2c40d40c0005010410141c60100201c1c003100382c0342002d1440441202e0517074650f41c08285510b1041001194112003c41c844800c05a00b8084102068400e015040f07102c0301559000c242c80000c4d081100001c0b1124030300f40140504400401746001d0303502703100359204e1541600183c481e5950000280500801303031701c1c0030755440f02c0c60422550101a406940007180541d8003041281d031a006084200c41c010786690b41c1c401030203848032002400004404034003928140c16812120165000c05656401c00c3c1c030544001d400695000c0581d00746441410000c000880e54581c2000300c005810300c8500ca2800360611154550700016088071040055020107503124881c00d1016803034003051900d80000b500d5481c070640c10034440c00b00a00e00201138500112510382541c8042 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 259938336 1250 259937086 259937113
    0x9021002061e040c030812070e0a06020d0809010f02190206090606062d04080705130b010c080a0302041503240f140a030818030601090603080306010c030507060e071404020309 77
    0x4000104121440700d8140004400a1b16042c050074494108a05048180c205004090441ca041344d84442c080e406941c0104269a40007a06200c4402c450400b0b00f00c41d1038154481c0d01400800600702c41060000031818102081129400c1040c0041c0d400c0d01c1442c0c48012145480d03610980780c46910038018000325120000d015000941c5140c00034590400c107e14183c1d40e4015081a4004001707608424010000b5081122769019952040582001404440c000280203401004406409100e010440d441424000ea0440e8040c0040c052000c4002d20406c81c028042d2000000c10036060000b031501950b03550f1200d620340240c4807110107840c1014205003851000302c0303c4035001a0300c03500210300003002c100808010948002c50070f0075038a042c80c0c0b60003071510349081a441001075915188040011842e0002940d400080c24604141524000d0600322460700032035801600c024902000408001000920801100e0100840d460300000ccd0300c040004a0008a805100d01c5c0c1145800b004031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 259939586 1250 259938336 259938391
    0x702060601110313180c030608060a0b181306060503030901020a060c02190b01080d02060903040306150308130513020c0304030f03020a05100e100209030309131b030902100206 77
    0x8055a19048030700f850500031341044400d07841d50002101d0301c295498142c1262803405624211409401e0900481e4a0711128903651080200f682c06080e03910030941685942d04d4401d1204290003090b010316504012940080c00e07038100208942092502c0000100390a001c0107460604c5016000b80149044688450015100b459181002c50041c01489040d40c400303070002d00540760041178180c200e507040580d11490034440313055038800d55010608120048a0000484c2c003625848100419214100204450620155000100303000c0010800701c00780718240300b100d41111012152881110850407801c0c04a00c110f85a00c000d035082040180086600e001a0502d854440d104982e40c880a07911080e041000c400080704003161245010114030200700010244d502c5034101c218505420140082d58a10409940c00c0c000d44241041c400d200c2115400400301d4480c10007041d038240c955440003802800130340022403050f400c6034125204e903440040d0f65031140c0b02503141d250303600c0489140ba01c0c0307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 259940836 1250 259939586 259939607
    0x60a05010c320f0f0f010e121e0c10060b0f09060c0a05030a090305010b010905220b130b04110315090405030f0a090501020f01091e080c0f0d12050702060601 69
    0x221200180b0950901c01420410228180c070b4220283c0b0f1801c0204820f030703007030a10100860300c2d80c0c1e0626002d92484400490550003c0c2110f004969942081d1001099540d0007005a2100b5a9011412000d20840402c0949038641c020780d04000c07041d150140611140100108107071010802c3c401c01e40325082c000010803e241251040b252050419900c0901d10341c0700d24144000034510050800c10040240105c06505509080601c011820000030400410300300d00d50201d845a0b9212041d0000c807103a0240c0d15002010341003540b24086e0500da440a0000c191409004a01e40148030000d1350519040c0ca0007190b405500c004043c841c98100710442d0310107803055910b400100074481c40300720f41500910f4008070548070b0000261a01c00003904001c9000540f5a25904100ea50000568448a0894043d4217140e208580f584035040c0000c80d80906000044a031180c00042031140500252640e0949002c0e40d502050344000c110340021350304191520030140c0e00c4400031036180c0d07001d05007d10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 259942086 1250 259940836 259940903
    0x4080d1d01051303062409020307050d090201110a03090f0501050405100c0516030b040c080307050a060c05040905090102040e1e070f1202190e0105071a04020303070b0708060a05010c 80
    0x1102262a912008121500302580240980d22a080400000c403451030b106c000f8184858110304504c5c0c16034000e0a0303445001c0d0043c14140d0f484030240c0443e8041c822039007480508900b11780f240c0e0729600d0090110180e50081000180908070b0001e107030340c0b14804441c00c0d80c1015000300c2c070034803102d982034800d10642e02c0708a450b4051042070101c80c85a0000110040d0300a40309141c890600703090003c20b01249030031a600c50740003089400041280081c0881d182540410001119114540110f03100d00464000001150400041c005c002005401a02c1030360400302d00d84005444202d101d0548442085c01d1581447c8200006011140905a41d0f401c000340e07401c05031480ca01c07140c0360404a070300605514500450102140b10344551103152914140c80a0800500d441010780702c3c0b45003e00040c003144061700d56580010110f45050081c6c5030301a5110050070114204114050413400003114514041d44c1914000225580b0452001e02010f40004920400c0309242ca24178a00360784060350382 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 259943336 1250 259942086 259942117
    0xf03040302210a17070503060f060912030403021206040312020d0902040204032109050a0e0a180506090c0316050402070201210209040f150506030919030504080d1d0105 74
    0x24158007000034500503440420b0304903503500c040d5100007601034040c3c140c070041007040d41e000700440c0c56040b8003142d40110341250b140c00310600c1b0000107143c501c1003041650b042000202c0380480041c001001d40162031080303c0d00140451290032495803408100c901030000340c1220101e995000c031580c0244120610401c01244800d215000305090764442d03882120a03c846481c03031421181156003030b00f0308030510304e0103682c2d41340f0341000034103a48060300990018100200100d0b03e901034580c00058400004a10490340d41000e007880b40d00c442080303500664600800d0617424a0313140c08144110461200301c2a00740712401c02090000940001c0c10880c10b01001d00c110320104070300620302d0000c8081509025030744003a40c1d000e0000380c590960b01c6c51061400e102ca120b469610501400090307a00a44140751a03a45001c1014034201007459485040c00c88a021101030640c800e004100340c0e59050300702e403100410454111140d450000d8400340301c10000201052541c4184010095640e015031f11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 259944586 1250 259943336 259943353
    0xd0201022805060c07060c02060411120102090a09060f0e0601050a0323041103010c0302070503030f100b0a09140102031e0a11150601090501050a0c0308040204090b0f0f0105150f03040302 82
    0xa26140403c1034031003041e2154040340c0501001000d001d00d003d100d85500c050700e10760402e40e544960089501c1d041c0c5200d075807920500d191b06102541914101c000051841e404156900102001481035000d0032029411411003c02c10841c10b0068501400040c1c1d203840c80c01d003529000302d004141d8000321120031044200044414141d0600490041d4016013042c1021a0064105402c44250384181c0c01814014010784c00071070350201c140c81d4042d038001d0200f065651740c500744091101d2590011802240082120b20306c450b800841e0700b06540300725072108480141c900059036207009240710900a412858003241c03600c1d24000144c061300032641081e0b04010340d10341d100c0d0300b0700c41c60990192800c11101c0070882103685c00980200141030178240f0314500188c00d07034000d00d00f540da814007805000c950b0010904544860f8040d80b500c54001401003d1401c080c410f41381303644020741d00303044a03c501c2c10000c0b40c18500f03c1240e1380b030b840c0300e98003007031a2200440f036910b8182c1000b44103409501603000c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 259945836 1250 259944586 259944593
    0x1101080c0702040c0e0d051e07060207031407120602030912160f060f0c08101706130c1a03040c081b0f04021201030c09050c040b070213090813140d02010228 69
    0x1000d4606c9481b030303c0a480c0511050701300700400c010340303101d0603050b9000010400c09507402194034001d0303c1c0c1101c0303090f816411485216280c10702c940d200080c0c5203036403030014041c400b0310742c00395004a100000755403031030740e03001845150b41c011001c075441c640d0703030b0361078140002040361405000c082d00c56003010031120340703141154088400c40341ea00030109070f44404001031207a00b01d01e21409045461032004040318801031907655603100501c5141c0e04c25854248400b80510008080014503280061b80700d1440c6844440f009900280c2d001c40d080d8240c43d03800300703441a0102d805203000c0155a10b60410403954001c00c40019024000e00c1c2e0420b608210301c204491520031068003a40c010f004010046291914881c11100010418120b00714240814000e4040141c100c1d009650100d90040319400c058a02c40c0c02400d40c0302d4010030440001400c015000e10310b0090604448082c00c100305140b13443c1040c0300d5075a01004000740160000c02d0b04090040780030300c10003104041000c40c50a003080940c1c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 259947086 1250 259945836 259945849
    0x6080319051804180614220c05152203080f131a1209010207110f1305070809010e0109020604030303020c070e010e04020a05041a01050f12131101080c0702040c0e 71
    0x44110b046004141240040c0800b078040d40b640d820702c0c40c038505070524201c042d48647e207612803c40c1200b003420746a00e03428010000460300207048028011090351551854100040e0b00c80d880d04090614201c10007242c0f11203c5030b0380302c00c982c1c110710304500e4200c000e0615206640010311200d0036001500c8046a21785481445003052019100c1283d81c070500310000000801000700fa030f041c0c682c010099400010010842c1824584060369030400883c2c5c0d01000800e00c40300001d0a06c40b103072501c01001803143c0c2c03080c0c0c0f05004000a038020411a110441281d0030380b54502d2010307420480400c02000003910079802401a041c102003503418a640720710424015280a07840340c4065190034040c0025450100b40c00001400119010404102c50148409552004122442c18000003041c000c401a00d240110b410820003900c02602528124007001c2c521811070600307954910b02c018125a244d4043e0f806070340a04121205642484820b500b048050025440c0c8007003080201c0c2c81039119a203132170 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 259948336 1250 259947086 259947101
    0x10204080f01090302070519030f03030e0a05010902010906140306060d0908180a0f08150601110f070f08031204080f0d050106030509160501360b040906080319051804 73
    0x101c004034070340c402410000d252018541155208501031b4891110380405041201d0860790f11000300c0c982641c0c141001c2c2d0081907441c034901d10a0042c40b60030700c108070041d0b00036840107100340c8a0840f4280c4840c0e0407201d050300d1039034020000c4002c2002c0303141c0e441d10002802580b90440404503011490307950350125a00300d4a44910000a41e000413004ca14200c0d8001011b806003000d9001103030f1038141c0c4956245180d4810b020b09180f4031022945903440f500c0c40401d07029850041316070720b4402c24800c0e1740e503042520400e500400d18a4011550b40c02c04000c4903a0b40300603a8450710141c8a40d1100b66a0f0340c00b48400c800c184104004038800307046180034290003401c01b074034006030914005051030b0500010300080022201c04080c01e03c03a981c1c00c06035500384030302e1040b4030385151000e41d10582542000a44d800441c00d181d0b180c0022138000000080c03081c0d60b0740790018030000c0c0d90361074415600e000b1014410552000a540100071602c01c40161140c3d001d10342c80101440006400300b0f0851304503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 259949586 1250 259948336 259948363
    0x7050d02031201060c08040315060504021c1d0c01120f061412060c031302060403080d0522020a0e07120606021c0507110907020307050316140609071701020408 70
    0xc01e402c1c0c00c0071840640c40d40109a6401c2a140c54130746039072520142d1040d404020041c40799075114403a4181d0603844440503140142086513280c28150404454103545d0008025440c05c120342c0c011070245101c141d19001500e0801801d400300f0031001514810200fa80905980395900420040181113000314001031002090417582c0100038130911181c450003100517081ca900034818072030503004050440354000c000c0100012400d409200161183c8956403029100b070780045208103074103225620a5009443e0601c0c00e40c10003c070500001c9514001c410061750081d1406020805080b2000c02c49921071f40340c0c0f5141802d1042c101032001140d000c1d401841c0160b1101030040d00042c040c45420440000c1420301c9414401141d6800c000015a108814041d00c9142c01243e080c038002c1040d00c1074a84d128007540d495114500f031085040c0907040043c3c8030101d4070b10f1200101100864100e001d1030106001c0e01181d0305110b414104220640c0310480306645c00c000000f1070f040180f0510719811b070ba = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 259950836 1250 259949586 259949593
    0xf040e04021912120c1104020c0a050601030510050105031203160302160b0f070302131208040812090906060c0c0f031e070f081204090b010c060504060506090702010e07170307050d02 80
    0x1400c0240e0019843c020031070520180b03d201801042c000c45407107440d1b1030126400346c0e4601000b200396003031022030f6000a20a103d000b002108001003c0356200d81a010000100300d181c0c0ea91042596845072a1034036100030394100302140d5a45050041c950031008141005864a204540405c1c80e41c501c11006842d514804002d0000c003501807015150407a2030f514003903081a100035500c00307030010188106d81042123240b281000f00f02002052340c00402008003524440702c810852220302da400182610300c01c00001d40003442c1403824000b501c6e450141c400052488401000c2405803000401c454281e0500c9902c09401c040c4020091041d101d10b8000041c103040782c541800304a5080043d000410b46030031a564404258100800762000c03110041008a481001003006179040d250100002e00303182d060004010510940b07410050051006490102091f0b49810040342242d0b41168118501d0700040ba00b003180c118001403c1c00c01004610607241b4102c150358445190929081d01100541c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 259952086 1250 259950836 259950869
    0x61e090723180f010908070b0c160b040812040e041b0801020f09010e0a1401140c07140306060102072303030405100804020102150906010b0c24010f06050f040e040219 73
    0x50120070f4a03c0c0c0c00b070070b007031103941c1c942004403c0c0e80b10262400b0b8100009000f1903095400f080803ca80e180881a0440030b902c40c985460392a6080c0d4040d002d030802d240300c1c80480d180610070b00c200b01ca044a8150a0000464070390703582e144c2a1141c6204405141c009111001c50b6851007880244412a0103010142d594441b0f040058032000c034800c520b500c1400c49401c1001145880b4200103090502441c003502d101c2841040c200c0c19024009101c0e00d148031303c400101d554003400c40451604003044040350050740d0390f0801240e440030140503658403d04082410422030f208080d80c0e01f214500201580e00345a11a0003142c0e0208602c0d80031800214507509100940d40c060001c3c00c010b14404584c04001d240802051f1b64034501032044c0b5130f44003c00108030032080d1041c001c0e10350350002245510720407100106100030300c00d028019a040d5050b02c00c000070f0325a0040049a4602c60460005810725140400326080300600a2059030003918121302c44031401012030350301b006810410040008076 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 259953336 1250 259952086 259952089
    0x706020d12060806070e0607201807090302150d050a020d0e0604030f0e010e03030703080703110c15060d020d08041a03060f040e0705040e06061e09072318 68
    0x1c0c4014009800103031911a0603c141a80400c00503804403003810036204154060000c035030305118040010b822550044031402d45102d101c1c440c28202c8008940c8002040e0045140c0402d01d517096580f040824a040010030041c00e00c031425030700b265111103106042011040b50103054940881340508080e500050036808032040744208816000240d0040415182c0350750090420110025943d0600c4000803081401e40c1c4a041805021100501503e448060b00e25020f0f1400d03809503010340100e030404400d02904500039064405200e100c0f0001c011300d41c01d0398403120480320003900080d044030071a501840540c40320b604600070184070b4407034542d42d0b031b1400714010031407800581c440c4000b01b8104180701242e42d07084080b559403101100d000420b618280011458284030b0307030165420900b0407010400d5500f003c51054418a004c0d121040004c1c07100309002e5a00b110031500f190720a04c11404150f6031445203071394a540c5402c054443d5891181d5403580c4c502500b0190b94808001c03403110030300030203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 259954586 1250 259953336 259953347
    0x20702040c050f04091a0409060203100509061804050c06040803040f090b0a05130912050405090f0702031207020a24230c0c011508010b01110a050303270706020d 71
    0x2950303070501c0e066083c400e1040c5124110f200324826080300075220b00c084040d0080c0803071828552600104100030b03540e010320f013080c0070350021a0744052034902d1100004040c10500304c2c2034411a80141021415148840c541247d0300300600152164441d245100c52300c1d40fa07010041010740741c3d98004548807450002c500311002c0040c1c005c02da01d1800c0020446e415101c0b21444020f60b0740071540030a29050083c0d004004150f119005031440505045580f0b0150f0040000d000782c0780c043e1180075407a40ca04103010045441900c203000142e004000240d02044141403054012003d072054802400c0e00391500c210490318182e83d02406d84018000e226020024842d24107a900380b19002c811620380002403107000d0000a096aa11100c001400c64203404290300141100217180c5c2c4980c54a611a100c4030300810952042901281c1391300341d0410384c002c0000784d05e51034651000c02186180e441c1007800702202890180880d60400e081b40311600150148115806801280c0c000c011401d05400003c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 259955836 1250 259954586 259954601
    0x403200304050102100b03030705070f052d06130f0b03010e0f0601170714070b070306050607120c240b0a09110412110907020c130b21030c1002070204 66
    0x303500030001004180d801140410626007094800074080c4900408079003107120700c0354001c1c4a409070781d1021820300010764403141a03920130380700501c00010940580620398490704e1254158100f600d0360700802c0c545600107150140107904005209643c07155980c03590135080d007100c8800040440140600c400d40e01880d03502c901e1918442e40641460340018203541c05101e81c8e41900010040001d240301d00412042c2e5180c01045103040c1d80c0d030054100704040010a9450000180c208603000406280c44001e46181d144c100002441c05040c005c01680d00007601c0000715408201c0c5601d10304202c00032100410305003000c2101160405048040041c10845a000010103510300102014900042401c0d10143c1d19503210944e12402036040c24410100000c00f5075910091000c1044a5540c0c00305607400c0c1a11b0035526128200c070025608400e03030f815014144d4001000a1041c0d14100100718140c14070060300c021f1703d14128151800500308840c40300603c10060b000614002141007500c038001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 259957086 1250 259955836 259955897
    0xf0d14061e1002011d01140a091a07171801050f0106020312060a50010c020f030106090902030c060a0206010b1c1a011d0a0504091a0403 60
    0x7090711209840c88851a448150500e0082c50300100c8503410303034003d50018429824400701812a010507011703c0d80a03041e24021600704042c640c0110791180d04c50701541c440c1030340c4580b1003100280b1101c500f0510b100024402d900b00b01e903844101420140341c5543d54000d00c180c840e40b914100805107002e0a481000c0c05c1980300c110740000401034903601206480100d0b4421440400c41d40311400011080d02c001d0300714005403007510104211509803081c0d0310754081042c410641d1540d818020030040c080c1000b82e03140d10901c507881e112030b00f507201b1290140713098801000e40c0300031041d0b00007213400c40c1d20390b0308031000c403541c0c0c0c203045015440d007004800c5a40c2c1086483c64502282c80000a44400044c4a030801c035440205040b12071400107400d5000b03011444108004840444a40c0e0302801485188140418510070380415007110501c41c0c0e070340c2c1050140c05d208421f8502414040203000101d400c1e91b424900750038180c02122100300040c066406541c900680701011900386400404010070342 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 259958336 1250 259957086 259957099
    0x10912080603210a0c0303060513140c03040503040b1c050910060803070f06051b07030302090108060d0b010501050f0405030f01060303111506060304020109080d030c031803050d0e030f0d1406 84
    0x40300100c1c2c9082180c0ca4121103207000c043d030444615040d8058001078002780d5100b09504400d001002c2103a01c2440c8800c4c1c0b1181e02113007070300d909400c10007d11090750b0107451303a0402c1000b40a24405e244c01010800a0000c41c030610011030300014084230b07001e44038803281c0d42103130201544100c4640103078809000d011025501d05821581c03080d01c507411110004003021f441d0400520400360071880b4002c11424485555542d006619000b40294003005049011030031000100d042410f11180c0320000c5688a00c0956059084c0700c010740303041e0000e0b0605145840200004202501d007407002c121040d071448000700341203082d840c014041c100325400c00c5480c1d034004070221009010007007003190007502c180d95441e680d40711800103c400d035903e90403040382449044168201c196060b807028040c003045590070041028600403000c1181404e260190010741d06001000200b40f003984120b00c40f5a000c0c040b80c1c0742c84510f204070300321504141088001190b5030380000c40c01c1e022101000358048400c40c0c25 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 259959586 1250 259958336 259958383
    0x190e040605040b01080612030c061009050112020607060b27240d060f1112040302070e0c04090b0a0806040312051f06030506010c1707030908010204050105041205010912080603 77
    0xd0490303c00925481c4550a021f500320114131040c41154000c41c004419100c039850001480c86503c0380311701c0f0351401c0c4c6103404000a4540240180043d03039540c000c0c0070901d010001c1d15840058440f980240f540141d0b41c10380030703416609480c01688003081414000c4591b20f00500d20510496162802c0c100030302d03130701ba91641d9590f940b0480d0080f1540c4144001400c201170102100105203001342e45100d00c8000582e44d012112141c141d5200e80d2281d800c031106c40da01c0c1c0c0c1c8038214141b0243c1e0808500a000d2005004003182c075000003080c507c028128808071580e0381d001c145040700640381074022511540210340b501c4014041c03a5401015020390490000c2191712501d100d5a0320302c06c4104050391900810031aa1107851070030009a0440403181720102286000d04080e0301c50602203011480324000040c1341c003018001d031400c6601c161a00741c180341c40d00813019444c0d12a003000721441d5503600c0a050010b40e4142407418850007a41d2980340b03514003001410720381031050180c0a80a00700241 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 259960836 1250 259959586 259959589
    0x151002011a100e0909030702040603060603060f0e1e1603031707020705030d0815040609020405040b090618060a03080d021e0304020a1701090501021204060c11060109020a05190e040605040b 83
    0x70001c0010f04291481d11440d5204070000d402c0d40a00c0d20002e51260403c4400810f0007800d40180080da4041c02d010000611980a002e00322103280101090700e03003000c0c070140c8480303a10780790307014609104a040d5110b00802c071210078100c95054000324007081421f42885c0d4000d01c01c0104607031100c1d031380c00240121400d00c0c0000e940c980e0355082c10705c01c00108100090820b25103181d909207400d070182051141903120848075020350424042c0d14055841c0c2085408941b40804605008000141c0514000f6100e1401e445800030014031694004012000000c002000c00d00101010559507030010380350031802c148180401ca07290740200103400d05000340000741c2d594003506811503a0310b503400741681520340c103020701429180d1340240070f9520106101c0161441103200911581c418101049010079289094600c106141110417803580120018040103003207078001c021905444c02e1040c141008250307443c2d405d4005003d403500140e40100404900d090500035800501030403501070104524890 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 259962086 1250 259960836 259960847
    0x308011e090f09020d050f010c03230c070807030e1005030408090103150f030506011a041503020a021e0a0302060a05060d0f02040b0622080d05030f151002011a10 71
    0x340072a00d03581e00140c018806442c0e1000780140c1d400340491807900350794244252075950300440c200c6194205100c0c100f4940c4284550402501c40340b51001443c0031022005988072001000c80200b42000c2000c080446d1099003e8401d0500c281d8442200241490a0151450b0740200f00414800103005100c0091003500c20344104035020b00c0e0020b0789402c69110b110030b40d40079600071528501d0310600407050110220f05181610b40081d004001702c40c000e2030812041c8201d00c240d41c400340b101820780611034881d4009000400e014412584aa141813120240441d00310107004120350040740303000c04058041c0803169020350301c004200080d01d03040c00842c07907420041d00010808504504040110745d901e82c485240c88801600c0d81d80c07240c002281784082c8020000380804108083c000024095100140804142034165983c0b4195107481102d0000b218005e000c8042e0303406113040c4402141c540100c520804c4c0042d6001090000c1c414409100c02c0140022042c0540119021036800c1500403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 259963336 1250 259962086 259962089
    0x1005190b010c15090312060807050102010b0a14220213080d08061c030507050f0c0a080705060403170c060c0d0f060509270109080702100305040c0504020f040302030a0507030308011e 80
    0xc0b88042911310b544c0c5422142011580e10000f8014907161010880602c0020180c040d5402030300200711101d80c010411488001a11503007040724090040081310307040000c00300d1020141d0003003c00762240030104640c10381e00301c45458900b20011090030400702004000201d45209a41003151070703401c1007008039480c840c1822203481060070b003400743c0f000c16105408446440e90442d0030341d03660b400080e02203500c0d48900840144555030500c000305101e00c002c14408102e4800a042074a05072450792400344107140c651200c25801c00500040c41c0851050000d68442c00b540581e155550500c00c001908523003d841940e0f0081c0d2800c1c03401c3c003254441011103508070001c501c0d0400302100715000c58280d00f2886940503141d50070032260380d0070000b445001e030684620844050702d84100c001c10880484004039406000314189103010412401c20307600030100640b00441e500c0c6000d8603034000c24130340380c0020303402c0300e5070ba10492042045c580d010103882e02401c1060000d4060110004551304500e64a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 259964586 1250 259963336 259963373
    0x3021603080c0c100504121103030105011202041205010501050103150f0e0a18080c060114061605101d011a0d0605060d0210030e061f060c02031005190b010c 69
    0x10304001c078000b40d0b4007000341e4007100c1e252011a000c1303c0c0241110b401401c029a0126400c18450114580060140c494400741c818004000d60540e072902004517410040c01d181045510390800012448550007644421958041c01c004a007a52425000404548500c11603140740400700318107005034020290000100c1e0242105401c007610391102d030200420448540c2240c0d40c1058a11004000803100900014003c00c0151070b416030380c13884200601c441001c3e2065101e1420008000600c0790705008400c01401903085a5010f201d406040c02140e40e01404500705564507040010481c10034010780080c08901d60103200c01107041c4d40130654a40e1041d1740146015100c000007295510740b02d541400903500240b4001802d22000c2000d0014901c00c030700b03004240248000603001c0340c81c00d80c2100c0401c550902c0c4054840c90080100c542214214080f6418001c91600200d00c0400380034460241d1030816001501c055002c1c2c1c1c4004503017000b104039051040c03901104020841d001d90400d10b801f003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 259965836 1250 259964586 259964597
    0x411090604060f09051b161a0610111606020a060b04180b13051e060f06010f1809020a090e0f0f01030b040f02090c03010f1208070303470103021603 65
    0x4401d1601c035641700390786c003451a65030004100d5140d5024105208034a29004840c1042500b62440401644640c22038801c0e400050201821146900c40d8a69100590303e45090324816500d0340c070b1840707070410f03241d1247c0c1c0103034410307121201400058803e001c00b20800b140c040202c8020380701e04000c1040103c4000d820b5030505000a00f01419080d20112000c0d80318081e50390010716454400048407030080c0c080400c1c81103d000600001c06103d0482c010b4105854111103030050500031241c000c2032003106043d40b61380e000e00141c14203460000c0d16540c0f405881e04c07000a81441d0701c00301c40d40d070014050714080110ba0280101c0c0200d1490f0b840c1500c0d0442d585e240a540c031818000c1d10880c8100000390015012010040607104a6001d181a181740144c41c42c0340554489100200707101c10325014002420822041001034001d500000e203070101084640c0000d01c0401c1d003085240d001d0b01c0d100c2000d2043e40c0149107002c0011562a032800030900307003141002d4000e1580f50844180c01c400034140030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 259967086 1250 259965836 259965841
    0x50c01090c1a0304320102160c0506031005060a0306050306090304030317010609061202041d15010c03050d09031112030f01050d08070f020310020f12070c0206070b0c0405090411090604060f0905 85
    0x40d100803200400302c5c0301070700a5540d00756910200d8030320320141109440000071002d0202e07442c90310004690264103a001c00c40182420704081000c0e65000620040a141d90350400040948081c00000d200c2d50001e80910344591843c01c0241210014008020090b8901c40051002c4c582040d0990240d80292400c00d44081d000c03070b51800240300e15009811609908401c2c80030500705551280d1080c060510718110401c00ca100540750503001c00001008504140140d07242d080326540440c500b64001c3c6070455400da0b6090780107040101403d01d02002d24bc00100300305400070a40c034268010a0143c1d525000d2440d191507000f4140151407000f008040d0b003052600035903904110320050f00d403000404544c0d442d150060b0005a0384040c40300c200c40c040503070001c0e1002e402131003c02d030b0164014101c50701c2c0800c140da40450001e0024512040d4450500000c10140c4070507000340c2c801c6100e41d00150f03100b242401008801c02004001511490402c0c6c0d09000c055801142442285c00e120004904d94 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 259968336 1250 259967086 259967153
    0x108010e06150c011a04020c0a0f0f0b04050d020c1008010e04052b080a0b0a0b0a020a1505090613032003070818091024050c01090c1a0304 61
    0x84811038042e5484030808503503a80034200650003006000194904c0d055000d450b0300600c01a4090403403d040f240d0800c0d5052408140c6020325016041d2244e003c1c0101d9115550310129000c80603641510707554060805020702c5a010440601c254070212901505181c0700400100000710501412025508420125040020030480e12001c84540d102c8034107c0750306040c09014890300d0b41c5000d4005540e0030042000320340d0f83c5c42003000080d0054254210300b41010030400e0aa84501240300851051a0141011601c1c0c0c9200c00304070003082501007110b0500103091450050080d00400d0f0004002d98002d000135041070100104104100a0721151051980e44074154010340360302605800c00091524240d14203503002080c01102114000b010303490b040103500c00c50002d4040c84031609100c8406030401d2011058200014801d450a1413426402d92206420f6403145070701110b512015a1b818002c80001683d50308403144100181411071500f5201c601d4548848017003452000e0100303011941c1c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 259969586 1250 259968336 259968349
    0x20f010c110312130e06030705060c1f02040e150d03080901060506040e1b0f120a02040b12010302040b01020a0f110105040b070c050906060406020a0b15190801050907050108010e06 79
    0x4001d0300070141c64114501c1c2e6608501540b0030034075405030101e51040498140c07203401c80300e4042c10025005251150802d0b09000c3c0c581d000005114051261449026165214131004c01800720803035030150b02c581c07410044402405000e024402d0030101d0045680300da844211101d140c491301403506607001d8450ba958207005040d80d8200d1504a0f1001130041200300c485040140120103144a01c0210103641c2c0c91054107005880c041c07818028100071580301c00c0101802c0a401c01c0480764010315055540800c01250307801407401e490510784000c010425480d00e441a030803690782c00e0003d0710500e02c09a865062443c03560340300400d1004500040c0001e644140c0944002c0c140ca54072040da18240350902c66880c6006102c5d0380e12034204003000410900300481600c0172034410790018042e504042d9160300582400030705040b80a800805261001c2c2e41d43c0910605c001441070482540a0502c00c0150075075078000d004c00029848480308100c6a680306202c00c2c11166040c80300b0b00e0b1a00d464000852 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 259970836 1250 259969586 259969613
    0xa0615080a140d09050306010320060d0c09080d0e0607080d0908130602120406050d0905011506090e0c0a05160b1e090a032a08030c030709090504020f010c 68
    0x41e10400040004102500d0044524030507400c045900e1500c180d4811180f91005001d104e405410100041001402082c03c00314003c61104030202044001c202140c02038200c0114039800315100d01084020b00c1d0001004400b500050020340014136190710050000030a5100490056200003201401d0222040030303142c3e80c0310035803028071904085040036995908a01005141f46d64201c1d00040c9603030000a0030104089408001400c1901c0c2c80ea058405030004442c46a07825103540e649400200203100d00c051a6010f00e500c681d140d03041550080101c4015007200010040860034041d5009101c42903440ea0400c07480e05039640c80002080001c818070000f030003440041c00c0701c18408102c43c16034070045080320200d0000500d5542844250755056400e038040d0115800200d42540480e800c200143c0800200090242985059031181250b500c11102480031410100510052660002d90b000003414060b40510050410b03800143e004050200b0181c14401c4100c0403c040240040b04080c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 259972086 1250 259970836 259970849
    0x60c09040b100804022e030903030905150702010b09010803070b0415060b04050906060306010f1b0b0c04060f050703121d010f0b190602061f2706170a0615 68
    0x600e06482a08041c0c50440d0a6070104d10803450204412004012510145041601244401212107021b0425801000744440a41c10140c41d0710719600400d0041000a4a07066002c82c036003281e103800d01c002821108802c0e00030307108840c4040104203e04000083c0d03000e0350341014800001d515280340010902220300100355402d8144000000c000150702d01400466100b40e800011a584101c10044c1501c02155128003284407040c22180031845250f040000c60b01401c2d1005481d0490340310508140012140c1c40140ca500080501055601c04112506100d941c100f040c2082c1e103e640103406442c586200740034503030792818070213601c40519030300071510014a0001c202001441c42c0c01006452881005e43c003030541000040b040c144400da40004a07045a03000d4102c584502d546400311070000c0c4071204400300c0350a0042440d01504d00c101c0e0020003c0910030500e400354100d082c081e241142d0124030300a0042000d010442c6005c2032008142d64040070010790792410b25081011170100d6044803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 259973336 1250 259972086 259972099
    0x1412010e06070c06153215071103070b0a051303140f070611030406030203090c030d09140d0b0a0207030c0602040603020a03050f0103020607121e1e0e0102060c09040b 73
    0x40c01604240300540e8240106005c2c0001c0044844100c400d644078440e00c0710700058150800000a00103c05a01302a070a0400e1030208030113000103003680c8440f00b1581c039549070000f4440708010300d0031110540807509402514505191642c1c401d802c0c02442c01c0c4209200380090200c0d40c07034071090079800203180e1040a0506400c1d0146006981b08151111880c6038400c121010488601403582030100c0030441e0b0080d4a85410504101d029410240c50180c03144942818025160f405104007091110749540d2040014035080d45c2e80003007071400c4407850041c0d42181c0c0c2c07440490300c890441c59020a0786280580e40306142d140481d0003900400707000c0d10705803006c180815440e078903800401ea051140d0303809010549a0703805c03881000b00203200003940719208100d00030001d00c00141c40d1011000b141001541c020014444001080c41880c3d5a8009100121844c00b000711a49042c07001e00171a15100303019400c000300103980c0381c01c0604810740d00500454542d025035210b4100c805aa90040d088 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 259974586 1250 259973336 259973341
    0x190318080601090f0c0c0c0b0906040e0405010203100b030402010f0c02030a06050f060f0316030b0c040801020304080901030f150501120207060216120c12030216020d1b050102071412010e06 83
    0x3d0b10010120007005180391410302c1c803010b0166224000c2c4044041e0454031103071050785440e503220329940c4078000c195000b010130b0100180341480b200f411449180540b0000d039a0346407000980161003021b8009c84221038041c4180409030f6400508110060b100d41800c5403444480d00019107070401303c18004225a0900c020020952007903a03900d40103c0b0203aa680924040d00b4040540740e50300c52401e050250502c0780c0c20004501001032481c0c000704903000039490f01d620341c203055017a80e1040302e05641d00c1100240c42a07413564580301d0b2488900300c0d42c104015143c0c4600b00d1003400100c0348200f40c10811400204102091160b0440348078a074003180c02c5588500742c42c0b905154140c20713581a02d45408030048031102d1801f07030f4046140c007079001400e400f84400d5001c00340c000f500610303100f058a0394107180364070040c0c85101d406400c640c000c6000307541400e101c00382c10500070881e40089045410180c82004200d840801980184100300d4014240402150105004040091503000d1620a0009 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 259975836 1250 259974586 259974599
    0x114071a0a0e011a0a060f080411120d090e0c03011404050402011b031706010f140a050d0c0329150913060f2c06270a0617190318080601 60
    0x351040351304094a0010199548400981d2066510341907100403802c00c0c0c000038001100401800e401070f40091800500c1100380329240e1900140c050b004c804200b40390000d105a040c005071700c1c0c0d4090700c05080070b032841d0f042ca00c13103900711000c0c0c042080c0034648410201d4216030107181c0d01203600b01220000815003d09040c0107007140c0020625150b080c0300103000c920b80c3d510841c0071103d0490f01d902c031152000440100341410313502c54a000f000300700d030922414007800e00b1741c002d1240049282d070740407851507501484c0c000c802020000c92460744a40d81c0840000c2e440d4a0300101011344a03625160721841c4c54400b00300c580c547c0d01d0020101c50b25001c40402d5941d24441c012051725103807500030309070050340c0042e88414031b03410705090407004007500010300c0c518118a42900c0304045120807400c0304050f414200d42c00b036080d6191480d05440348414440c5d407000181d00301c0c0b40c0c000440200305010b00130b030843c000010040030140400c5902d504a0308510a20718808008200b4802211040d40e50b511 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 259977086 1250 259975836 259975871
    0x6060302120d0809010218010c0311030d06081b01022a132301142709010f0b090105090705130312081e090c12010b090a0b0114071a0a0e01 61
    0x103103403004143c090010500415051082d200424038003419514040180301c0107507840c0461001c00c5081110481c004c20300d00c02d00340083d01c0c005010307001c08900c55042201460038040d841c800c441c2c92a1014070624003d03030f030001e41006c0c50500450840c00b4800d04025004201082709040c83e00300b0303c50700341d0107854482e5900216030340c0341004200000c0c0800e990342c081400820f00c2008078000c0c110600107124a031802c0840c90b06207142c03078005001c84841b4000c00f0b01c0d590850314111280d549007454400091a40100020000100d40c0c1c450a98104000180006000b426500410501041000705402e60302d41442c080d54200455902e04014200010540c4c01c0481d03241324200e5104000c0303e48141c019040a004e1615040540808901e1384240509088184050407241d0b4031940c200b1080e403100e50169010341214100412130100c008009070400e440d0b5569000c45e440200702c010041400c3c51210361038883e000c00d071440140c640e856414041c1c0003440a0708565480c1c034102510528012 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 259978336 1250 259977086 259977103
    0xc02011d0607090f1d06040f0e0a050d0f02030301170f03030108010c090b0c06071d0d1109150a09020a0e2d01020105011401050304060e03040806010806060411070f0606030212 77
    0x2d03900c4070f0440e61a1080d071004011030384920605a035440150220030042c0110380d950152014000150243c100e41010f0260344101c03500e15015003107440301c40e050003018003d0a0000c069414010110f100504d4029a80d04c41403040e0419030700766101601c0c8002090000e07184030b442c24401c49889584a80e40c0b14000c2036143c1c6043c0204e00403400000307102041030113903160081c1607130151101d6520ba0707500f0344810003a44201852058080700d1030a4a40e81c44081c900030300c0c000c50b08403c4000c2d200c800c0c01180c40000c0c2c8200d1a5100300002c4901c2640d460480c1c10540704e03d80c6d000341e00c3c0c1d05424029103003500c0c424600744d03212a81c04803800c2f08041c50110200d855121208410048003100016801c80d0341c02c1c01030385807043c081c040c214503a501541c010741c2c000c0d1044400144640341d840803a415500315406c49192608400d00400400604000c1240c10031000c880400038040c2c040d040740780500c50400d0080c240b10005184005000c101e03031244d40119005008143da0405107104a034990804 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 259979586 1250 259978336 259978351
    0x908130801061d0711030a0e01140301050a060c05150a0209010e0a0302010e0411040504090b1602010c0c0b071b11041401050d06020913020f0304020405070f020d030c02011d06 77
    0x11000144032201401240300b1600c42008180781c0400030301c000099034800900180600603c07041440c0c1402d400c10007044192551758407011754030f18000005141d55040da0316082d50507020320050101da50f65111800072650700d4100345a481c034031031410310300380144101c20780d1915002c1c030104203001005030014041110241d8030508100010810881c840d0340c207000280c0003400042004c680b5003055440994481c2200c0c45840c203043d03a50000070117560440d5012521050b182c82400341500c0800706000030030f01140003d000c1040d001c0b0b802042c00c2000b1901801190010303010910280c02010984041c062080222079420f441e404c0c000509414410740c0d278080d502d40301021072114118813569041e110002c02403826a40310303880f0f4002030b4003d101c0305548203140a80f8050b00904502c010440d007641c94818946070302c0e15004100c110b0304020640d10030f2040300b13980700a191ba808120000e25902a00700002c03400c1005108a006010108280038203858040e0020018000007804505c00d814 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 259980836 1250 259979586 259979617
    0x18080c1002010e0c090615030103060b0111030c0c1c1b08070605180415080303040303090c0501030506030a1401110a05040e181207031718070e0601120e100908 70
    0x1030303484049007200d0488280000d540c00c248158401c5151801085811000c003c00140d48411625000c40c0d00f0760081c0e00485003203640c5c50031a1003950b0000c480559040000002c0c50a11103440c042c1515010241e00051007000070b910f0b203104018045401100b0305410004203607118030200706155400055004010755403140240014400b481402101d60340709120403900c0420021605220160107030070b14464040106d03803c08138a642d004c10185222710b020340c0c0c0204d08400c4904000c40c400180e80c000798100360030081080116280090900400b6500614185032040728080b45401404480009100c40d032002400c4901300d40d00c503000d013007515041008003007280c442c07014508000c540b50004044940100d9810313040450488043c24005000c0e06200074041c003052803e1808460071108500003130346581c86003002d4601000303210087d002881010302182042e60010b024044c02e031880c1c5281c181c4591003e00103903001d00107e00c0da20b00300403090041d48024604006036400150100343c5105 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 259982086 1250 259980836 259980859
    0xa030507081503070e090f0f1605040b06030103140a051f05010f0e01050d08040f061709060c040b16060e010209090f0421032009040c090e011518080c 66
    0x2c90103100300c1021009000300101480e080c070341c06100c8001803001d80280984410001c56502c144006103900200c0d5010340b110a00040254400c825035410080c000c0e440d003015145552119811281503d1300030304214501500030149038600949054000c105008003202510460030300749035100c03d0807030301b0810700c40707a030325007075072000341006846104140c2c11910b004000604000007820300712801114501d04c2c0c1900c84489845100c4d80754007001c001038580c0414102c169408101540200c1c48202806903401c00001c0ea4983e030055004010304a000043e10082881c0003121000e03185034803a03c1440200c0308a0303040e600130340000b4821030044054400103410801d0b020701181c841d90340a0142c542d0a030041c410040050211880d6a00303040e51048001034801c01000d210703541c0603821015a50b14020381040c4010b0780c44031004c007010b105018009000301c08040d159181034070b44060f412440800710346001c0384c00e000c004c2e00e81c0750417038040f24000c00e0303c1d10089004914a10700352160b00c0d008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 259983336 1250 259982086 259982101
    0xb1201050603060c0c101406040f0b011e091a030a0e0604051b0d08070f03020714060403020f04110c01020306100c050c01030515150903010b040b0a030305031b0a03050708 75
    0x84a088405070391503001000040c00288100c0050b040c008410030854005001b9440c841044400c2690700f5141c01102d8003c00129180c103000300440d2100404080c051200d00100203003001015400901c0c4110449295484261058403c440100304c1c010a03c0ca0604030310440c2007c4e5401911084100c41c10b1081c848040440082e440d4016540f0400501c200c41040080e01091f030400716030640d0041000c0c400e000851003000151010900030148402c41d00a80d10b8003a10740071035940182e0342c0d02484482e000d481e5841d101501c003204e070107840003840120703c00001801400021002100c005011544107007400301580a540305035019156090700d00301121003039490080c0342c04004c05540c0311400240081d4441d0300904e810100b18a034a8070718403205400902d00c69002d10306030149080104200c00b003803800740542c5403491400d9400304040c01403680426001901d0b80006024040008081540342d540024590030030340b2034480240e1240042071009020700016907420700081e49503400b0a520 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 259984586 1250 259983336 259983341
    0x60e13020a08011e09020307050c0c030606030a0303090602120405070906050a0f050d050705060c211603111903050403022416051009030e10030c090b032203030b1201 73
    0x500103511910b0640e0310302160002c400d034000344401c00d6140c0340c107030000c2e03042c1580c000345014070015240c858903001c40d076498a181803811320b4614442d9001905100309910040b403407030a21a01440e000c51811107604154000e846604e090041c0c1d07041c04010402070000200b080b000340d03070b80302c0024460a5900c1c0108066601d0038062072484107004030301000350b85494001031103100e1141c416a505030b1f98520001d4400d4000800000c215000341d0700c0403044000c400401c5056810034040c0c1410031140d050640c4440354090740013018800c1242e081414540d0410103414641c4a00358907104400141c50b0080c02e03604944012409290b0b6004d450058446c8101c080003c191500082420700e2403020f180c00290924450a0b07480340503401c45202148001d0003115103090103500e440361100840e07828401d400e43e0101c00e0108140c503003500610700c2d50b8452440000c407004034605649903110030303604152045681c441c10095030b528107203030401c064041c1c1145010344000c80b22000c417000d090200390309 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 259985836 1250 259984586 259984597
    0x6070203030610121419060501030221180a0609140a0218070c0c2c04030806041a120d090602010c020304030b1b07050c0301050a06081c050d06060e1302 67
    0x42c0507095520003448a88180101e0404958041d408a0b01c050340e1784d00072176400d8058806200040b10081015003824543c0162030003400c080c03804610b4045200c0d0705c0d0f118010702d410341560500301d4401107610b004106400d40c1c80d07000c0c043d0540340060300c0c07454400b000700410b907401c40e03030607408480d000c00e00000800d604504070f401401255200c0b9100a0f0300480d02130007005030041c030907510f40020105180b00089000b400841c50170509100100554208401c01d40d1420824052a50304200c0002c0e408140d0940080050b20003203050308500c51a520440d0a226009070403044071041920b40d414005030000d00205039441e0300c13072001d4407020200c1c00e0b0b440014154016070700c00c10040000914405140d60311440c025240581c032000481400001c5c0c0c0041801d484627400710b40f20045600d02803007080e40009503990100103c40c0f40a0f0344070f03203500c1e03a41814034042122080c081c4085004000b00e41d400001e11004210054482030041c103080c403141c404501a812450030301d0300701e004070703c02c407807 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 259987086 1250 259985836 259985839
    0x4260a030f0c1209170412020906030a0314030406112107090b0f030604020903030423010513050402070528170301060806060304050f07030b0601080f040c2c0711060702030306 77
    0xc007003e0390000c904000c3d1184550446036100c400d440b80b045015100040c1003d003460048003425200c281c0108528148060840c61180e00440241c0c00042c0d0001002e07043c000045004030f86a0f6500e0405800602d040d64001035402c400050030110400403031008040081032210714019502c0b101e004856005c1d86008601301072904215800740c0c40c4025016652208000344007500d80b50341386d008281180c02580c0100c01c03450300240360514114031070025582e061030030b180030b9092070b4165a5903160541644903c6014690004020f410304c1000e00c030403030703510b100e1075501f64010602d0303c0120f0200742d038440142c901e0302281078003070402c0d072140048074100e4170180c0c0d80c03a020703494190070010755900c083c00895841c4101c0e020b0903400081401300703000560041c82d2000751413034940005410001c1c000c01d10090358000c881004001418004510f0507900c0356050405260300b21500000c121900b80007141008003040100640180c1c80744268410012031419240c41da10b415109a035680010340300d5a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 259988336 1250 259987086 259987097
    0x3310602030f070f02180405120a020c010302161403040612050f07030507020a06090c060908010903081f03082701020f251d06010e03071a0304260a030f0c 68
    0x1110000c2e849014280042c09400c141100366240d03400500c80b10341625840c2000c1c50f9080804c070500c501070040c1c05000d1101181a03241c2aa2003400940b103824403100141895030125040c0c0c00c44450928000d10294014900e043c0c511b60800e0b02a80e03034202d8030031503000840a5070681e41c400d4984c0602c6008400c00c1c10b68280c586c981480980243c00010060402c40c40307911080804074165002d4200240e0013806112003031400c1c404020b06083c016044405545e0410301e4034800280c1c420541c075070003a81d109096134104881392000001c406264400703004400d012502c500d5807501d0889143c59200140c808041c40c1c0a024011f9803114103c5074600c1e6150003912403114031101d51081e4248100c18076642d000301e02e84402c440001c9002540301e00d03103030b1503100e0200310980d60822014060130200300c1c01400140c3c600307036408440c00b0f49180c04110100700400070600300032000601d680703580d0050f840309081c0e205d01041d0845c3e54000034040070010381400c41200b05040d49100318500031b0826940d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 259989586 1250 259988336 259988347
    0x5040302041d06070c061515140405040c050c0d1704060e03121f0e1006140f0a02150f0601050a0e010c060c1709010612120c050331060203 61
    0x204001009800e500d0300b08410104a448031031201440803038070402842d210801010403d0902c01c0458034501c450300c1080040403014090740f014581c20042103140d9140850307c01210000c06007290041d948039036041410700c0c6640c0300e00c03038100028011034003202080b510301100c04402110131502c62921144810b420710081404140950021032400c0407400460349000105602e191340c80300215290064042c0a81302d03000001307005440c2030010604240600310905110944500003200780c4505402d20020420103044051040255200010f0f600c0c035240c0c4071040300c54041c2d141c1300b2201c105104403000d0310001d40d00d503000d40109801520117a40d03003810030907071031010742c1c0d07502e103107146203062080c161003800008400703004500d80f01602c0e9560300c044032800d500d030070140c010140c1050400e9040a00501446104040301e00c8040e0b00b000903c00012841c240c152680440440090318034040041c0c1c010b031201030020303003e02030b0b19400010f908000e40c01101424801a03806250f0068208200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 259990836 1250 259989586 259989589
    0x13020d0b191a16080702010f020c010207060e030c03060901062409050f0d150b040c0c0f02060304080c03030703051b030405210c0703050a0204051f05040c03020d1e060807030305040302 81
    0x5584002000b04110346000b500c1d000700d4007014001030046814500c0010403404550340203104111300303003690004281d011030000010351641d196014010810101c009220b039160382c200310300540c03928060b040d60b10a00701007040601030640c9000b11124000102940b2800403a0100d14980d02c0905542c0e1a400b00d04000421035110b412444007076102c00300443c40c03008504078040040c1d43d60300380600000d00300c1e0900309000039910107034000000d002110901c2d1000c0b907841001d40c04520b5045903442d03a13035591840c0015281c001d080b081b0b0300520010040005640d0140d0159025a005800c0780c40400c103070b5910711246120445005141d60440c0d00d100d003021800b0008920150725580d00170303040940f40760041d403401185074420b61340c55022504400a40c01d0601c1b0340c5400c031504d0440c9d4000001d450660101d408a00d121b078500031a940e0b416415024030a40c10340c0c0804001e4442070017408242c0c406101009884280d10641d030b03140c1240000d01100019200341126410b440e490b04051440c1c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 259992086 1250 259990836 259990859
    0x5030c03100302040e010504050714090a110c0d0906090905041509030203090312030114040203010e180709050f0402131817040308040f03140303070c02100e13020d0b19 74
    0x2007603440035006001c404401a0754034040c1d03140501250000250b9854a4202103150070101e500001c85d51121007024507031910390145842d44000c034035a0200e10b82214140514540c461020520424042c1108000c0c05907401202e02044540700c2c1ea400e0f480d43d272100c2c0300904a40043c0d40c001d148070a1021000a0b400b11070704803010450003401a43c0c1090801c201003400d02c1c21044141014a20010052066200e01c200c2c07100e1101d010f460450442d81048859002d901e00a0451030034041800540400120108100000f520101000b03100710300304500142c40b40a402c1d14101e20419401611281031802c41c4101c030310098001c080240104442d4941319883c01040700c80b01980d04c000c100c003001103068000104018a9011b804600461440c02e00441d0741ea50820031280d0744d0400c009001c0c10540c0400c5e5000301940440d50f004c800b4260010aa0755080946070081d00b2508065009501940c2035000d44802903440c4400e000c0c0341c0d5014100901d0b003404420702821038030400000c1c440004040c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 259993336 1250 259992086 259992091
    0x30c040909030207080706022805060705070c031a15100801060c0c031b1a041401030f02070c06020d110105100b070c0915031707020a03060c02030f0f0415080705030c03 74
    0x2401603600c01a2a02405d60038642c25820540c0940d20a680000d00c101040d4468180080c1d0790030b000f00c03907084940d5400d031200c5001d400700c410040c012038940705008050706108011540301c0c00c880000d03000708101c44200e0381d08685401c420702959040958030305041c2400501c2c0c0e0129a2000a2682030034420750300c91030600c034251b880e1070440034048001a0b015100a1081e542c074900045410320381401c1c152800c24441e1109540b800c180402c000718401c0314a80f044044007420042100c0743c0c5200410028001c0540c080e0692070240300001e6559004251190240c21030ba40301e8030251b80c40d00c401030030b9440a441c007003550b00c0d400c8d00400c40211410701074801c0600c2000205001c542d0b52032000103480b5513942c030041030071101c40b040081240c00c80e1080012001031000a05040c016000140c2685031444080c04507600c5546a0b49007a00c24011034200e0200c103d101a21050061a6207007250010b0040841c812024440c2101c07050080b03080300d00c90715082d41d0b52465603543d00140c403400c0c0c001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 259994586 1250 259993336 259993343
    0x1060327140c03010f06030b0603030705060f040303090209041a01050a05090109050406020408060906190b01270b040609050301050106111b010215040303021e0c0a020409080f030c04030b0c030c040909 88
    0x42c0e10a4039859a0203000d00d40c030446a072600850024194101030804010213040302e0b1080d4410800c1c20000f03980440c01035444030410080c511103541c0c1e070071306501411921000035404a048410003040010700403000d141c02c0c5443c40005126070700c0c0d50910034000c0703450062690040305040100141c803c0f035045140e00602c291400740c00c0682ea191002c1c075104013960b004040303400080800920781100910013030312a039481014082c0404550010307140c00c0d107800c000c0d080d800042c0c600c0b2a4668031301c4190320050144680c00c603076079071351114000e014036024040e8511035403c3c1030000801510680f001250400c4c0c00b030241c47c1c2d204482120341c840b44241c09442d410750141c2120082c0400009121034400d6000e52409640c1d144460b01454114035044002800030405120411442c074000900344035440d815500010000c0301404c000046000308128826202c40000410804102610142c421280328541200d100d80f12506c20400030301040318025807000d4144003c012440064020b461020300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 259995836 1250 259994586 259994593
    0x7060504020a0f150f020303130209072f0c030102041a0d0f06030308090c030607080a110f131d060906060d0b0d0605010f0e060303040b09130606080106032714 70
    0x54031030350074420f910140d010038000200100004400381e0882d10309840f8001510103180b81d40340c40c040f81c1401305101400680034500c07060000b522240600d0b11001c203259240440c025080240300c40d140c0345410038481c0c012a00403845030010701d0605009440a895006880708006a400314210146c0c2c0c01601e40072101689031140140341090610940000e036000382d80d801047e1030560341c01071411013660f0866000780d204074208901c0300c0e44440e01c1034220031843d04c0460070440c20780b580740f0140a401c040d400c07031413000500015088070250300e8074102e031804400e003201107603059003001c1c001c42c044400581104180000500343d1070028001c226900d100d070300016501c0c5000d000704102201e18402255031035a601c0041c0071174880807030214010308000310a90558541000842d490340035506c5070780c10b0301d500860121015078443d000159190040c040c104012039454800130040705080c031a10000c00d151410040560104000f0326103c202d8207450544600a030340d0307401004d0b1525603440c1e030300c902 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 259997086 1250 259995836 259995839
    0x50f0301030b0403030605060315090a1d160f1202060a12090303090501050c0f180f0925051603080912120114030607021e0a080703031407031107060504020a 69
    0x5540a14040c5000d200078011524041c41c01604590068026078401d000920800a00100c2e22142615184050b68414015151600400c0190807454040146101901300d02c2c0344d40100000c2c0c1c02189840d0302d0104406550b500c042c000300701414043c0134081e4102e11040030150138110000c129200c09480d0180c0e2441c081200740e401c07200403100403400039450304c1e01041806024010641c1040e060280145030040703211060b40f0522601c01110280100005108082e41d01d1501c3d03074503400e0010344081910b143c215110b03000303d58601000800f000701010080701ca544100140e6641c030300303906154510001c03070362416178070800000c1c02d05289104043c0181d0b40305076444041c2c4003e078000100c81d01c4550602c4100e02c044032080071000e000b98003580800c8902e940c002500c0c2e03a4941d5244500175442280140c02d4142810000b010b4041100004c10204050313050740211041c050703021008410780c850003011410346020703281c41d01781d1210501510011901c15403050341c00c248014a00480303103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 259998336 1250 259997086 259997107
    0xc070c030c1707050405070e090a020c150f1f06031505030f010204080106050301051e131e0210020c0901150e0310060f0b04050d030c03120e070501020f0a050606010f05 74
    0x80d1464221a09515101008402c88141002020007804d400c580510041c545071000500020000c03034884e1050803c0f10100300003241030703811100d0003101c503c01d80b81a400d04a00c4104000410b4a03034207244e840000005403000200001240442c1040308a080e410f45414130850241c402c40040b208070205c4101c0024196a08200310341d41040e081c40090b885510b00b604042c2101e441e0381c0301c03074000e90401040028252201c00450841d4040303076141c0c0718a0f00c8130101c044840c04100c0c1e0003081c1400900514052803040240c584005d4421a50a40b03100b004100c100c1e100c000c060036942d00690940c005000f5610090542c0542096518285032401d0740f45c4002450818840e90740d2130710b1651942c09001e201c2050003481d010b4422880c1980c40c01c1c0c5410b0116122103070790700003c1c04010a00d420791081620444284030703040340d20748040c000d445801a5850315004244580c602500c240714400419402c0881e0407103e458100002e0403c1e9603030305005482940f15800c800041000800c1201141c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 259999586 1250 259998336 259998353
    0x703020c010903123b1005150907020a050615030f0709021b032d040b030906090d030b01090905040f0c030b010603052202010f11030c030702040b180c070c03 69
    0x10a4081e41c1c81e8180d05003031900342002c0720224905d481000c0301c80e18071110300300f5412141042e80d01c4903c003075103201c004100c003403410450000c4a10901a00300720038045044030008003080b000c5401c0b21205030030b850b13002c01685d4403041c10000400e141c01a400054240c48403042013800c00e60042c094500480d2440b0403542400c0050300440082c603808108415022100c10a849a880034003008616040f003058400104c403881e10744240041c11100500300404581c9000d90b4020a8101002e54403414a044140d460326001c03180441c00d441102003014001e40310b402141a900b1042e110380c20f50a06104408010b41001401903c00366034000f107180c001885801d4442c0210701070741c0714800039414901c004080e0354024004450610500f82c0d09203002d405400301441c001d5090070301e10b03140000210142c40e004000500348105000101301444840e00120040200c507108507410000c8441c0c040c10400744130032400400400314508000903036040b85a00003130000c90301034102090850307034a6a0391b000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 260000836 1250 259999586 259999601
    0x303020a0b0912210105010804051002030c0906030406090302100b01090306050c16120f090f090b0d1b030302010b040216020d0510050a0b090a1406040b01030f0c020723060d050703020c01 82
    0x4d2955140c0c14006020000410240503103002d01e00179500e42410307141c403075a56031403171007071759a50364000b0104605440040c00c44aa030303c0058125516407500e810400014000c07140e0903400342c0a4401e481c1c107280034038402c060fa10788050710380c0284903040d40c940800a0030000c00351261003030104071108200c0d20742c000400195201c2e82440f4043c50341110018203c0a02c580d1540902040788410b00141138090540c01c1651024078001450403440710018040741a00e50b409482c291441d07054014100100314201c054034002e8000b884001404e40601080b4418030050610f0740c000c0c10190300041c034269403000c070882d00500490300e803200004890703c02c9400a0b501085000d030740b0200425503090000742c0715031010710384208221043c1510b58111907000d0082845103e582c1c4c4140cbc9541c0c580c044d0740480040709100c40d040084228180700699600348030b000754501c65503030070056a00400d9541405451441c0503203207508103034002c0d4150300542006840f10060640900900b14060801d114524 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 260002086 1250 260000836 260000857
    0xe01030f0f061a0304051e0c10020f01060503060103050c0f01051b0a06060909020d3906030506060c0307030c0f0503030f16021b0603040501060f140102160303020a0b0912 75
    0x660758a002030700070f40c3d0b41000400c441090410700420003c42c0000c05c8555440b102c1c1c0804203a1783c0702c0702c2645424500200130b4154060520800c090b0001d500088041001e031040c0002c0010507147c03010160707111400d00c4010b040d5485644004103d08195240c1d031007200042c140310781000e50a1008040c0e03400580f12041445d40011003100a000e01c034016000284080303e401c2040c0b5166030041220350030440405409054070b50f00e44c105403855203504507001020706003001541d00f401a100312071900c0e2032040d140002c0c240008a03001d8a889021902c3c031a07900e10066161204560f01950f5824100800352099658404d240300800c00a10040d41714100d8401e000c2d0b035929001c200003400704025004a01154000c0c58001c404001d0007010080c01c4000b1140c0c1034881c0e03110b00e802c3e800f4010315004104003240c0740c80d002403225100000740c0c01c203541c00d03001d49004061a1a5044005501c0d20001d0016440340c5549004035503880401a0490509410b0318030b0398031900f039481c00d180e002680f0348 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 260003336 1250 260002086 260002091
    0x712062003010902070507090506010c0b0c090301140406051b04090e010f02040603020a08010936020303070302062a030a0213090e0a060f090305091504030204110705010c0201060608070e01030f0f 86
    0x1004106e810311660015280c1a2030070029820042c0008019405a1100600d510355080204144011358010390b10140e00090082c0004d503480840344800c0502660120b51450811020502d160880d02010107100c01c01140d650420345080740380006000301058a0010755642e104229030b0101900080001c4e0003d07490140c0d40310600e060082032954141c0c09089418138200e5107104107902c0140d08180010b451862204c00c00c0c04407508030303400f004900c0080d454800040d002c0c01f007640114603c3c2c45030526100c02d1a00902f01c0c1172141c41c4280310003440128100810005482c41c095502a1004101401c454075019498507400401c80e2009030100f801e5074081c5620004100d298054034150051031001804622425038005e0240e02426210754807844155500c1091038414006440c000c40d001001401601181000d202050b444a01c007540c041d403c000d03018070b41070300500650013140c0322a603a0006a580b6400120703440c440c003605003410181c545402c080354401c5406140c800d071075101d400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 260004586 1250 260003336 260003347
    0xc011803020612040506060103051b0702190312080c0307080a0507021903021b0a05100e150703090510080403020a030e0a030b150418051b150a02011407020712062003010902 76
    0x5ca0300d070520061a25040500b000c0410a130000b90307a80c03805012007100e06c030540b12885840000c4120fa1070380410442e40c4016000041072000900c03000002c0c0e030694680c0011902d8140c0049141e2208481200c0421200000714103040c045501455005050b0720548070000000440055194008181a00181d2000f03529a02e8040fa0341e240c0010450111020040c440c0740030b01180c21000f043d036161050004004103005241c8a4911405200d100802a0381d600c0b08545000b40052200740a120300a0a40c0046000d05074003a02c003041c00307580c00d0703002070225007195601140d0340c1d00b00d060400e4110084500002c006404c424585019298481a409100940409001c100c440ca030f10802000c070016003138000800c50205002c84288a611403145102c4000c001041c04c840e440d41c0c504098400001d0145001941035000301c80c44ea92a440d0640552107aa100326600c1e50035025107002c0050038115000024502ea0062a221420000f2a480419520120149a0026485440800d0300081c0c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 260005836 1250 260004586 260004593
    0xf0c0905010806030f100c030e0a0f03030f0501031e03110708010914060408030a0c02030702060a0f03050906010b090909070e04230d08010b130302061b07090e0c01180302061204 78
    0x30701d680440c1c190002c0c40e220480f00122562121486c1c1403199269454000e54030307030340c401c1c1c1180c80009100c0c01256405003c6241006481c6443c080c140d0001c2d150030400c0b05000c0440c001c142c100e0b50464606241d04407480082c0c2c000184200040b410f01491000c8400144403d0000000401e400000052814041c3c100b015014024609400c40c0d038009070308000001d43c0c000140c90704404902070015072840d003d40c09034514800c100029501081c08140c507440e2650182c41320110403000d50b014450760700c6960545590748401e0107a0341c450f0006111128050420403043c1d0b600410060481d58460344e90a40f001801c001a901603590500c3d0740c2295400601200d0002500c40404000380034809004d01c00034103506040c090151101400256092004040d0618102441c5c00602095807a03040d00c441c078494110844412101d03000744c0d200080d41034503500c40c8086180c2200d000c1c2800e41030210045034000f410a603401200c03146c80c1000310250316400050098071003011004412810b01d800d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 260007086 1250 260005836 260005847
    0x180603020f0f01050304141f05090f01090c120312180b1f030201140d0608010c11010605030303010b092b0c05091504050c0d0f0204030c080d05030f04060f0c090501 72
    0x340d00074082d61420100703072120b980c064100c9a00c6078010030007402403994042c0450070a180e00c0c1180d10301d0248800d040845500607402640a51001ca040b14035030075034050b10074260360362980007038000704800508110203044044000c00c118032031b140c030340c1c081e4181105e61012200d5a143c421002c81c06900500c0403c0351622100e070f008124803140307207540d03800402010310405035404024100085034800c0ca000070540c200b0b41b0114000c03140144045034550345c0d01402400754110380c8000230218002c2e101c50802c1881008242d03200a80030b14950380c200000300d8203d0344909441030304a440c40c0400e0b0071031140c1203040322104007a5078038090080e100741071912044425030429442840480103104040341c82c210104c828140556002c01c2a541d000d2540219010b0030300340c0c041250520ba034041e107020f0300d0f50081041c3c0b4400c003800481c590311401c000e552160720140e540c020031020030110b4140501409801c3e40140300c0c0c40081094a408032114040d1880c0c2c10346500070032849071082c0070755030304103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 260008336 1250 260007086 260007109
    0x6030a0507090501080613050705040c1b030c0213020a050909181501030c1d0a0902011119020a1d01030609050118030314060103273002010b09010b07061518060302 72
    0x1006c0307039200d080f01901d83c527072101c020344551845140c0d0364000c9680c040c000c074080a0116540500c030041c01c201400d016180c1c42000d0b03030032031280c82c103040002c9c803a100b64809d4411001050b03481508180c00030082c494201c0c0c001e80210400480e0510100e61240100015a1100c0c088414203a1552552030710403031604a6407c0a10079142c030401c5240c5058030b80d4551035210202441c0810800f006000585008800020014450090410790b14200c0c0d1002c0c500032141d48251010ba004641d150404050b0041c50304c004030303110307030030200400119500e0340000c81c903680554000035100c00068443c40d4089403a0804801098aa0000d00040700007900c00710f03480170082c00c0501034003040f02007009450590700104040c10000c00d03c3c0e401072003d940040c0a0381109a004c0b2004a084120a4102c10b490015464010360801e01c0c582c4803410441c0c031490407610a4850035061100550b11100134010019810030030100c480d5000035030900c02e0100500040321307098006016811401400400c10b2003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 260009586 1250 260008336 260008351
    0x30706090f0515030c0a030603020a151101021207120e03130501030e070e1b040911030919050a0b151513120807230105040c05040b01081009020306030a05070905010806 74
    0x5950f070980448004030480ea40107000ca4426544d804205000b40e00800b02030b0006900b0042a500200e041c07010a00c0c0d0741d00d00f10454440d4080d46000340c1d4074500380d2080304894404100c0d5480401d0b03205000f0700d183c0d1402d464000000c80d072440244031240c591340203034030103074803003607543d0020000765815103d90681003202501620905040a004102c00d00e00a04560300520942484e404c403044403000751005001d02040038010250044a911910740050764001014002d018022000c00c0e08070044031045a4014007409442d09217881e814520360b4024110200355651816101d61552200c01d00055441d0108480f915145400d880f41004003681d002051700008a04101011520240554030240c1e809600f21419007a030304e40700c0c0440303400e144000131079600b004240001c1081c0c0d00c11401c141d85095070700b008011001001111000b0054400384c40403103414805000740d8066800943e400400502114230550295480070300d401110307404008107607034680043c016404280175040e0070054 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 260010836 1250 260009586 260009599
    0xe061c050114040218010509061606060608100e01030b060109090513150c020709020702010302090310021804020a0503061201110403030203031e0c0a050d0605150a0206010509130b060f030706090f05 87
    0x11000c403d0030013101c840170050600c40042154442561644211a00c90180c5800341207804a245002800790619001f040082440f810005000040c4001c0c11000c0310500c4901c01e916134650344501c500c1c000050820341c100000c8010108440303125014490180e548540701150b0f0f40e01905115485c0098011103017821420408844c0c100d0754005125020359440c54401665403040c2d01c0160001d120b08030f40190140220113a016050405070301400003408481c030710505410101c0204000c9225507003108002c100288081078843c00c1039141a4000d685101c00003403c160600903143c0c080e00700d54001c07401070380000200f04860410199400118203800040a01e40c01c00d0b4243c1c5a0501411426008004c00402c40c07445d400b425030400d1300141000b40c01489605040c48203d0a41e601c1f001d035400151007508000125420095200341c4110801070300801a22416a03a45044082c007400c0c0940c0068600c8071107210355014014403004090703d40703071851300700d15104090f52441110b030306c043c0c444c21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 260012086 1250 260010836 260010847
    0x50c0f0610030b0603010e0609070602010f020328110301230a0f050d0804090f0209040e160506070222290d0b09160b030a0b0a080c010e061c0501140402 67
    0x210404800352a8410f46402d074607521000440c6c010141a01d4440c0c05114190500403000e00100301d00c0c080d140340e58001e100b129402c40244c02070784000c1d1002c0d01580c000e42c050243d4a255150b500f0f201d140303c1600414292030341c0707410000e41c2d00280c02c80c41c4100314040050002c0d8480600c80c0e1520032054410303000e21807030a250a4200f00a030300c01c4502400d8003100d00f104004240003107501030705140070708020710328000800d20000c0d040000d089002d180b4000044259140000e00203114010080b5013804280c203010a0140740cdd00500c2c801c9030000300f486d001c81c0300e484881001144d8034190110005041c2e04901d0703000d100c41c020203401685001c0c11400b22075261181000721800a800001030001921000c0c070891504005d00455a14181c0914011910035a040011405206110002e205032141c0008003c01c500142c841d58029a010398040755a550041c2840b03817510b24010489070504081e01b180542c080342440b031030303c00d090391440140500101980b580b000350720305950860074034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 260013336 1250 260012086 260012101
    0x19140a05030a111f050c04090e06040c14091b070602030112060507050c03031f0302031f0b03010209060d0b04060f120506070c02090a09110d06021201080a02030303070e06041203050c0f06 82
    0x40c00c0c1401d405207645c0c4903c0000c007085580c4048600a0041d400200050003256000644841e000e4130126042c00c2d40b080002010034020340070a1688500410b401e00f503840e4159004079000e01e074a61844508002c2c4225400300b032a40c40610300030010100c4ca00e54003200d503c4e1a0003101c80081c07182701403103402c0c000603a503550004240c1e1342c0100d5420110841d143c65030070b06412030480c0da1000f58188200011041c0c0d0b54101c94480c001c0c01c1c0010014801b1008000070076082c3c0c000c1c00002a00040244080303111301c4116002912081c0025000003200c0381c5540c10030015001d10b40111003c401745158020420500700412a4003041901c1c00c2034560340c044d80005c481080241036a24815110410041449a940c1c01005500c00082c0012000c0e001d41ca4004040e400c041c0c00011112030120001070346040c0414240211030f03006018515690360716605031402c40c000c075407544c4c12078014070000c104501d41002d0f03000c005000b51500768851400d1001c1a00e0514025240c4070540c200c8400e000e42c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 260014586 1250 260013336 260013373
    0x40e030c0a05120708030f0603030d06080307021009060e01081e091606210b0a08010f060e100e04031d0301090809041a0a060c1103011a010f020105070219140a05030a11 74
    0x7460f01900110070303490b260000b0340340d401303a2400960317024a033850002703013070800000429200384280c030703140c090303040f00882903803d81440c0c030072400401d1251201500c01d40c07190350100c0d0700062254500d21100060200e02580403000c07034010000e544081060440c2107400d0025800030030507850070101c01408003007414401c8180c404c0d43c5230380315202c400d8800180d907480300320030203080d0705402086100b2040a815015010600c208505848082d0205d00da00809407158010358103003003080006d0b43c803a954111074050304c0c9500840460000d40807080e9031340c0e0a01440a0304ca026600f05a00c07464041e080000300c0ea04001c480c2589a02c048440e01581c5401314598100c52050038098a00d03c0b00d0b080460b079420002a20592552800610860402d078a40140044082c2a610802a0b03a860348090f4221401501d107100560301404019030803007404244059807a10482c05001903002078541c10740b409502c0b145c119220740010811041c0140d004103203050800c0008002d01c0706040b40e00d4140350 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 260015836 1250 260014586 260014591
    0x309031b060d090f0f030e120c15310905070e010c03030b060f03010e0405010c02030a2f031306110a0c29040b040e060d0209060906040e030c0a0512070803 68
    0x6402d5150f0b50108207002d103c801c0701480d190014540d078a007a01900d401802850b40700c0780a8031904410706404051700300003409440034000076050742840300484002c0410b0750010280d041900342581d4840204c4000700d10028141d50715028074000b0a401c1020718002d841c0010b00c45001c004070220ac070707011030b0390224128140da50075050000748100c1560114605105600020403822800030001035000c0612455a1007903026600030032805190301c0341241c8070710132224071340c1c00200064030304641c401e40f41c46100861f034480c00b5a503150980c84000340703045410044452101504100c8100101034100f060302c40d0b0060020b010340020b81643d911006040190302074986200c2d0341c004144620f03d800e081c0c0300700c0c041c840290720b0b840c0e640d0307034095148075445401181140503960b00807035504d0a007840a002d03c25801484500307560344803010b00c5440440103200030ba03c9038440300540381102c01032004058154414018008800701420803d182040d40c1000b00d40300513003041008041403550b8181d81c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 260017086 1250 260015836 260015857
    0x9030102071a160e1c05191406010504020f03040809010302160f0203010b030d02120f0c01020729160c061d071a0a021e0309040507051c06152a03020309031b06 70
    0x1c2d698540e80c100340d49802c942d000c1c03191040100180d10000d0209101c501045049230004583d0b082ea00c410600069000310f0281a40120050000c0f40009a490700a460841c5040c074005040503a422201c40b000039404200341c41d0030b0035029941003541000e00411105240c1034009105502480c038009507229020f64000c41d04180108207020710000240440d200ca080030002036440d00384504010a0015a0b052059185082c0c1042c3c0c1d484202204500b61040d2483c00300120081d2006ca0b080d42e0141b5880c108452141c0d880d4001d40c0c074400780c00480060704429000a000c0c071400c00c140751501600d901201a22004180010340c0d449231b0008201e1480000d6102d40c611401034101c5540c41c50048100503035000b42807100300000240d012001d01181001210031b14015035042c0300705000c8610714000c101d40c210446610b10f403c1c43c0aaa006404080c8030108036400b1040440301c01d003960b880b9407003200140c20015800c903207440d003001a40c0c1ca1802c1e0000f4040071f1941400001d0040c490620001f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 260018336 1250 260017086 260017129
    0x3131721090319211b0605041a24010e06040302041806020a0e10110c04050711060109060617100e0703020408030a0804020415030203060c09030102071a160e 69
    0x811151018058014801c060600a103020041840c0c09207400c4070340c01038070f5135491001d013000d6402c61085c0702011040440c4034401104a900780ca50b80050240180103079190170501c180130801c06104140e8900c901e00c86040b021010804000305000304014000290411485020403803042ea185400c07074085a0f81120002a000070509038820329202c60000a0862840860202503203904020405900003040b030f5001e0b080403200505a1321900103a071410780e254008420041182842d40c002031b000700090505c0104a022070301c1c8646040001d0308100b4416454240c1040055084111014159101c00d603c2c01c00b45403402c94440580064480c50400c0e011540201d00303043c0c043d9049070050081c80e810b03255a0400c55001802000c1c00746d0b4120301481c0740c401d6600b41c1080119100c0c09880d4010084d00032607c40e04204135540e004034252a6140d5400c0061400064050403e00c480c144030140260142c03030030400051b045401d5030944001e2044032030868150b40e95840100c203800b400c0d4070b80c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 260019586 1250 260018336 260018347
    0x90504110d0c090b06030115030e010f02130f05040209060a0e06070206041409010b031009020f042126040504020a0905030607020307050105090f07050616020303131721 74
    0x3a1100c0d6800509160304039150320840010302503103200103020b89030f8a41082c0185958041071085a11007407280003101060070303007030340085482170700b1030429110044e002080b4003010102e101c0480e4003100540e00c10b140029800c1122030400c100d030314000c101c11079085040c80401004102030340310710b20030101000810480304031203903030303810a80e13042c944c000d0702c2e05840c0c5845003107804400e005801000e1290b00306000004101f6107160480b4410442c403c41c005000d442c2810b03a04c084e402c01250184000d0092002080009008501078030445032054054030761710300c50070501580300542d84403541d403071140c6901d090366031140000c0350101e0350107031401a551114440201c03940d1401da003100c0d615015240506c131146600101415005018400800064a41c0034256958080c0001510b10304d030804034082085261000142500a8840b2000c04040810394002401d50340044400d100e04c02071074400307020b030b211485411003e000761031000380000140544a400e45201440c100c21103401c0020300e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 260020836 1250 260019586 260019593
    0x140a061b0507031826011d03090f0a05030d020c1504061e030e010504061d030309060f040804030b0c0304140c03100f06120803070314040b040f030306170d0206070315090504 76
    0x994401080c03d0084135411208121003001251740180c00c003c100c1d070a049482404611000e0210003040c6440300942c5050251001e00440c960b03e41c00441d407202d074082c00011341d030300c00307100f82c4240b000b041e030285c000154450200910b82100c0445c8400c00ca0341408207001c20780c1c0007544051041503544010720540102c400442c0a00030401d801e141950030a0309010810031180c00c2400c00201c204003801e05404014540d0b90b40340011200c1c05406c2e0b104402103003d4600200d001e03034121780100e01d014178068807038039441e510344000d6036141c80400000040100384007041605112180c5a2805001400c00c2030340001c1d42c03480b20005900c3d00b2a551200f00059046c56441070008012020040c08840749034200540690011140c10002c41e04110440761410711705007040d0b203d594064003000d95610399807101a14040703030074070407414155220000701d041d45180f0218615807945800400340117000081c002c0c10309601400720400e05080c0000464041400300407a02070b102c202c0400210340d45c4c0d604 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 260022086 1250 260020836 260020877
    0x80c0706020c0705031009080d050c070f12020c04020a0f0e01120e0102030f09030f120a140103050a1502090a06030f020d0612120f0507080304020a03140a061b050703 73
    0x48020081440007551160101c0c0114982c4100c901c12002d441d41c00800d1400d01050f90760240005008078400c210003078004155903c00c40d00f0249447c459400c00c965a90b1f1408085840700c41550301c01644504940c03140c0e4104410660044e0030759065080c68512500605a240402c9030380050040c003d00d10700288c0d2290a00c00f2403440c0a64050000303603054404076000750f000751074941401d5240800212424000000c468039441c02c014002d180c0b1142030380a00b400d0b1405006040c0c91034654094000441d81c0223501400b075801500038043e8501e042c646000c2140261000c02c2d906801441440b847d0f56844201200712140750502160011780e40f18440024881c0c1d143d40c01c03e007490072801242000c1d501e0f15500c841c511401241c080d44a1802007030b600b003a02240c0e181c0000e0402c0018200280902000e0341d0094406007490000c5a22079480c038003d0700038000141215031086001c00f0074009280910150328002340340c4c40004081500c0014042c1c450440d018090200300c0d81e525601d06000c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 260023336 1250 260022086 260022097
    0xb0d060507030e0606271009140702010b240913020a02030a0f03050f0c0f09030f0d09120f0803090f03030103060f0b1905040e100f05040201020f06070c03080c 70
    0x4004010390701c1d0090000d0018601c0101d0014548181000038049040200000c04c04400140b41021824142c070300210745c000004100d440040c0412000054107041d074040d880c100b000c04495604180b5181070700030b007122260700d00c25224209199204800d14003441caa596007110010200b6911004540404d441d441a0162a40c4552000415051a030f5021014140500c080d9940d05006000b42108901380c910680312841106130810128401040316070040280780c042d0801c1d1420852a030001908003500241d800710141c000d07002d18800c0950204040b0083c05004c8441e40c40c0d00050b843d840070754007014170001c10440000003c140084020010740401c00005400c89503650b84901c1c211000d080d01105095185003410ac0030640c519010300300c2e4080140b0306c1801007407145040700300406840600700129942c014207524803400e0b141409903240d58007110030040764a04151000a10341048050580d00a81150b030920882c10b500441e900125605454288200d444412010007944200d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 260024586 1250 260023336 260023343
    0xb0a0c0203060405060103050c090709050409031e091e08060606070201090f06051905030c16020a120c140a0303051b150708070e10020309062d040906080a150b0d 71
    0x2102d08010030442c0000d040b5060b01d2290040d074281c003807140c040c0980e9070015185030000c5564014184040d0500c2d81c0303c156210700a1414074284041241e42d006910209c110200001ea8034620500c0200020f03281484804070020714034030010300d40038600e5250100a05010300ca240002421025680300c0e1a482e8080c144500614420b0380c0d8400c8094000d61001c491030100624414501c1d507198040d5007540c0c0326012501a035803500c48003076031184e50190310003800c0b03a02424081021a50010c50802c00200c1c030b2003030205111282c03d104500700c0c0b15064485052044080c11401d10000b0380c4001920015076460416021000f841402035040c0050700c2101410a5542c40800113800e0b4842d259501480c1c19441c0d00c0d020700c0344002440b01c1f450600130a40c01591080101e0b4120f814450002e01c12115108070714600040c0d4039002008030828032036100100e4802060501003040385120707240042042400901d800305c1d0b03660b180125041406055444680d690130b00310307019201e0f0701c00d02e0b00c1c941c0e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 260025836 1250 260024586 260024593
    0xe04020c010501080304060f0203070b07080402030a120909140709030201120b0319020f040911150d061203170103170f12180106050a0e0c03091009110f0409020a0b0a0c0203 76
    0x84561404d5540d80103881040001507100100c00c0030b40b07002000312002290400e17a40000d5035981481610300103005002203805105103960840854030883c8140900151a580d0104280c81c0c42021002d442c8594800310442071400240440c2540104d00d141c01c4030350a08082819080b00c1c184680140b4031030100c0707a054000c01816102c444034488070012002e10880d0382c000c401c00110700b403008031801c20600601105124160501515260500d01e4186600714a01c2e445c040072001c060341903500643c0038080421201c501081015002841c0d503115451608142090350701d55103401c050802210080c5031460000507001c0080e00b84081204c1c1d280204082070991402c000d03101c90800030b81c0c41c03a03401c0c0350b520700344000c20b1034a080310140c0111200d01c4080012a211104044040ea0020f89000d1a51042c40c080308441800c5004600985020b940038240c0c074140c0c9001d01044441c0381c0103541c802d038506802030300141c2e90256460140c8036442422501d5110110007981e4100c01554065814030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 260027086 1250 260025836 260025839
    0x909020706050703110a020c1504090e0312090312040210030f141801110304020f0d02090405100b220b030309131505010212120601091508101509060e04020c010501 72
    0x18058126500803d410b40c0c0c20400481303441025003e42c0504a2114010780040403210a5480c016807203901d94286c02220b1032602d659126440100c9074081c080068582002c529401d8146100920940c040301c00005903290482c54840103540c410000d1000b0b210780910702c7c01c070301410f100c2d6020380000c00ea9140c0411103c2000710f0f120742054002c60340e01c115004154020400c0c4141801041490300c600d2041e18290707292a0308014000944868080c2c000d161030b0300350030141e0380b0b066500f8000c0d400740010b0000260754100b1181501c9044049078020303840d060044e042200d4400d1408041148010002100c1d90140000b89c21b61061400159000225610388040380307595070300c1201002d00c10403581480c19030360001a601ca42d20714000f441c045106008406c1404500c550b420707408038051500c41d00b0070751208188400c640441040000040c0708904114861191811640240814859200c5203650030b080081091440340600c200700715103c2040132280e01c0710f4055071468501807009111a6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 260028336 1250 260027086 260027093
    0x40f0b07050c0102070501050d0513060513050106060f120903032004051e06070b0703060306140f070c260904090501020316051806070f1b0503071a1909090207 70
    0x290082a801d60300d80c001c10341d61004543c000100c0748125034040e160a8200800c0228803070051034001e21219401d680b4418110006e90284a21403060484c5100070040c42114100242120302c203401400c103001c0e01b172808801075034210100c1c5841d840b0419011800741c42a15048010b003005410f40c00070542c1c2c4050743e088608064001c1e1096507019110b41e10700301101c11440ca080c1c2c2e502d80c2c00c1038211000301b2110b4041118903c100307500808504010a030a5070b1b0740e81c0c210131549084054108a1038000500000b04034026140c2e41100d03452402402c8041c1039241e01480c191102007029040720240701c070301d07041080c4500b501d071690001401080f2070380e26410511302030350048032215403030a00c14a603090194040d10a0b03480c10011643c858224150304806e11440c2e41c44201c050755044040d620300000602c0d08284481105030380c00440710242d142005140c40c202d42c0d030b048215071440700703074003420300725005025110002c0742c0c12200300c40580f840302c06a41c1c003d840c0c1c1001c01054000240030701070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 260029586 1250 260028336 260028359
    0x1c0c0f08010507050706320a0e060112170c03031e070503040b1503010b0a0b04030308060904080904110702060c0a02010f0201020c15040f020306010b03240105090108101707140409020306010b0f040f 87
    0x81c8c0401c3ea0f040c892090040100ba0310b0b030100b4000c2c00c19460b46000003c0c04524128145040c2140d10051f0340d2800075014240c5113160021241818104c11420000c2c000d1500c10300d006130041078a08100f400c42c1020341d107054500c40000c0001c8100100c8d10201c46c49541c094100900800f0050f0144c1d0045454503400b606580c850302040e001300b04410301141d400d0501c0c901d110310590304203000c00d0601c00c800b0104005890101b00940035401c0612001300560385040040106100034030081c648c1c42c0451001400714100d01011400b50791061113000340804005c14140158401c3d81c82960b02d5655a14000c0c50842e8a258080c0d050309c036800001c601d003650100114002ca4002d04200c10041d160f620494100d02c40203409400590f0902ca1000b280d4083e0500d150009400d510302601c81e503d403101e12041883c0103c8a4042d035105c07aa04002c0c01c0c280d1144550405002d41d42448100c4803a00440d0b581d010601c14181d500d100021034a000030681c000b501d0180404144aa134401d694002f02c0c02ca = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 260030836 1250 260029586 260029591
    0xe01020918150114070f0804050405090d0807020d0e061b19060b0307030317060307090c02010917160818060403060b1018141c0c0f0801050705070632 66
    0x106581c41d4074030070001d40c000d04154001280d0188038030b01d817050b5640c5d9a000c0901444003169902c0c0180400f003015a510b0042910810207440206000020300030001c04070070018100c80705540050510180455101c05601c0b0410000c3d42c0055448460340158a102130410701d070704985001d5011800100007075401203401240c001d90041c0304a444000c2003584910491000a01051035401003d100d20445554660300041c000c098a040a0f500c2c0c1c820001d4500c0070303c0d070b0780c01030355507501c0c0c03104101c00c941c2d43c8117090500f82903140c24020040081d07045500c000d600178108003000f2684040f0030700702c3c4000c8920080050b104130348071036580c0340c040060645401020320a002c03207012055414814959060403800300c0c096007055600c0d01d4000000f0140309034601e81c02000d00c60b015162071982000000000c0c0c400d40180d03001c24034000041d040c134016071700b240c0101c3c4d0420040c800341c0d5a10600341c03034090340c00003000281801010202d0120071040d4421f00c0580e003810004d4022000042610b91 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 260032086 1250 260030836 260030851
    0x3080301171b0607060506010201091203050115091802090d2f010e2803080c100e0a053a0c050115120b0c1e09040f060e0601030e01020918 61
    0x1842c0386010140c0c0990a149082465040901805410082400d07508160342200040c000022100c41d0f2b500c0e040b015280c401d0b404008a9150001049030103041d89a030b802003807480c945040c03828248043c7c000e088031040740084005402052a007030300c1c1e072481c415140e00c5600c210020395680b51050704103c0b440c200c001c40c4c1001d000840345801e00e540102d0707000800060080041000000b104d0307030036622890840840c04004046403000c000101e01d4030081c04136000020050003240303080e04041c400c0c0d4035004110038043c1c000000c000c0c0010000900e5440440c400d04030b0302e128807030060300d9080c4000050068040940791690b88520103801031034015140d40104000e0000903444203880c10924140d2090383c070700d4a16140410040f401051300140c2242ca071945e40e0f0f181101c444580510f120072090701c822610b0002078495002c0c0740921801800200c07464045c40030034580140f00500401c020300440c1410703290410512543ca0079170488210400c018440101032076100d4000c00060002c45009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 260033336 1250 260032086 260032093
    0x30708010f0b0d1e110310020403020301060807182406030203040512040f0302060304081902061008070f05011d031014130b060d03090504110c01140f0105190308030117 74
    0x4407420b0030030140380e90a03e508610751480344003001c81110340c011840c2009603181001180380ea801560288454850016044c00c05600c070303030450040600b19201540464404e40c4008810890103654000400c2c080c00020302c001f0344003001c0703904038111802403070040442141c0f58101141c01a0103034007a5000ba4040c40c00c485514450020800743c030b12490007000303841c1c07100c10020801407078084000c40d8024481c0d143e04d81044983c103190140507104481d00b60140c1c0051040059116240e49074400400741c40c402890b29900c0c100a100d4003581070b0252604001c3c5001240d5400100c20400c0300e1524170160071545100412450103004050b440e0004400d0021440070520380600b00c24160405904001150f480b52070744010040c903075494110880078000c600c900016155150b01c034034a02441400070b40c40c1d540c4251303400142100c0050452410907031488080c00000344007583c0590644905850007014085400241640102c86a00050803260004000308500281603e500046940101103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 260034586 1250 260033336 260033351
    0x5090c092a0c1603020a0533040608150105090405090a0b01080309040f0212012105010c0804110603040c1421010e070e010305030d05060f0402210702010e0a06020d0b030708010f 78
    0x51845003c078440a5406407801e80103020354641540c190403421004190b911208000c0c00580074500c06210300e801082801144c1000f503a40c06c00b4416a210302000850381d1000380e103000281040c0100c452280c0200e0b030700e5001401641e010401d0003110341e00b2450903840f660355500d24503500e900c00c0503600d02031810000c6440d44481c05000383c8031420f0500c0f881051603803d103501c490160410002040c005000c0002c82070201c0d80078480c0c00b44180c4542d036414064549403c00450103011808140d010703150030010070012940c0e19600205403042008071b500d418030780d20700003800c1c03600010f152440800c1c4d1110a25800318150b10203020b1008110958105659401140f11102c0e400d1101a08642007080703402805c3c442da0f0700150348198000d0000c00d4149441010400301c1e04002c02c21300410f0351140c00828040510400326501c1070311407000b84a142100d54203240c0f1100090f200600d1117401180902e071500540e04130100520001e4103c42d1282d50b00c00c1c0080c007a120758251a8000f610b03242c00e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 260035836 1250 260034586 260034613
    0xc080114150a0f0e0a0204031a01030b060f0f0f19230306040c1401050d06031b14010c061d060f010e010e010f03111f050c060a05090c092a0c 62
    0x101d482c122003680400c160100c0c070782404514404002046140c800d9400c1002000068420221050750710419982028660541c076154200c210043c14817489021802c080f081c0e141d80e40c2d07509520001c2d06503440800000ca03080030400b0070813120b2030701200382c0d0407010200f5200110502404240140d00702282100c00c128289a1201020785014000c003014034818010b003000c4410700410040103141c62407808592004176021078041c0c2e0411074000020030302007120101c45140200c00303000c8003101180071604590020f41031841e260300060601303131a140c00506c04d580006488140e202d8000907070388146031a002d1811200e4003401500780e041496000403070042a60100c11b816110709902c02d04019046480d40301d018644003184503031084050b41e96841d00e5203006080d074951030031a19a84d468a4544040c281082c2c001030129101d1440d280c104020340d0b000142c1c400140034262140c15183c0c46905240840c00841c245810b00095841e40c83c911050300c01d0000c000380740e6079038180c80704550f4451 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 260037086 1250 260035836 260035849
    0x50114010e040b060304200603040b0601200d0e010c060203071e03020703020d2d1112090f041805030c0607030614010801030201110705030714040b03071a070c08011415 74
    0x201201d4200758281700080c00255020040c0a5081d9840340440d000300101c030018581d81d008032030880c2d2903942c6100303104c02940c004c110a4828842c0000c50380b1600d0988966136079901c00c10600400f00306402c0c00c010060303405400f000070900c0d01700358150355038031f04183d000c4d05c03942d15840b50041666180c41200499442031081e115404d41c1503001e46000c80ba4400100c2d40311044030b098060000e60b0307030040c002541b214400000020320300d44030504010321046519050203071904a10320440c07010006240d450340c40c04241880e0100031100090410107204100403110791460b0000e056101c001741102c00755900054840c81313918960f130148a40741c3c9074101c0340c410030200300b0340c0e0740800c02c2c41c401400190b005000548105142e0710131903241650b41c800281c5009166888150301c4851200c4144c101d080c03a001d00c011040060b002446d000e854100d0402c0c0c081c0410781e0802c1650383c045440e4003082000280b44c3c006000d250000d0001c2a1170b074180c460290800da0720304030a81c1024044140500b040e2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 260038336 1250 260037086 260037101
    0x702010e0109080304050d060b09090105070e04020f030a050403050702090709050a09090f060902030c03011e0e0c0a0312020a0c06030f050714071401090b070906030f05011406070510050114010e04 86
    0x100141d414980741109111f044c90803520211001c3c2d458514090b41c544440303103280d100702d02c042d0000c900d50420100240c960b600c01d01c0d280d402513004103e5224103081c00822241c020126540003d0560f0340c6050032201801040d50083d4091b803000d00380300440c0d50001c1c5100c00e6903400c4079240507071552004c1103000c6840e024401000610001da0446c08104603901c42c05400380060296080d04041c10002403c41c1c102840103056507015814140c002442f03442031044ca07210803401400e1000c4200002807502d1403911000f4401c04800101d001910310a00100c444150701c181a6400d2a44500c2d001d13001d004a07201003020245020b001402d40380c441d55032002c8440744501614508407240c1c03104400d005c0905103418280d0341310000b1100103043e80003581e2040503da0b440002241c1000e0303004003950101a400d60086041c0f070018420714141c81c0a030b8900c1501201c5465a40c0414070300b2031700b00030501c081104280d10b0074000180001c3c0c0b01d028000c000c802642c40b04c240789400000c0204690343c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 260039586 1250 260038336 260038349
    0x80d0507030c0f0f02030706020304230109031b0306140403020c15041403030403170705070e15010f021e010f0b010302030c09090613020a03060504060e0f0c0a03090f06020702010e0109 81
    0x4811842c001c00c50340c03031050028500440e0210f0040c0d09940210349071003a65400480164000a810040483e2081c559483c0a0801148032550701c0d910000030032400ca1400080c06000e01c000c0500c0401a0f51401c10004640c0040103201090b003010038a54000011103043d0054051a601d10100b032410158181014a4200072541020300300040760b06101c011880031a0141f00030000030004c1101039445a91290342c9105199485201c1c2c6401410f1102560008003c034102c601400f06080c408101040400c0782840c20a03484000703a20120f20300300d42c5101466118031140c400c54070b030701c0064000c42c4598000032424070840003143c004500320321045030141d01140d0b05200702c140c149840260709402c55002000c9090f145060700928003242d0041c81700001095442d8402c01c51810f26028020060100703030982d14180c0740101d24031000880060002c005c0807030000d0400095400703940310014141d003240120302000000c0c6441c80c02980f0420302a03020400c0720500c4200b0798801e0051100740c88a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 260040836 1250 260039586 260039597
    0x905010804051506010201020c070803040f0b0a020307110d0b0f0403081e13050a05030d0515090603100b0a0f0803031b0301050121141f0b030601090512070902070507080d050703 78
    0xc1104500e500504040c10704c0d411075400700101d844603075040100002403c040030107141c0c1c6a00e00700f001814a01254070005100005010000300306402000b69a181764000402c02481d80304140050761540e203810008007811b40290901404100c2000b039144200e00c281c1310300400352119090603007504050443d641122003803c00085040800e887d64145091190003100c1c0303048000d6541c142035801081c014411540e8400401c01c080c1c05070803408a4980003500c03489490f080145c042a21103043d50301b0003400c541c448048100a0b121011060010580682130080b026101c80e1020b88039442911036031700c2103c540300c03152000250041124120782c0c0c16114508001551903808007820385030481540340da6135070001c0640c1c040e8502c056912400300003000003545a2144032505c2406032640015081840910070132402e0390304035410b41c0a0300c0d000c9410030000340031600014076117031144c0c01c4200e500b0700216201e0100080080c050081d03901203810f80b00880c4600004440c0c80c0202c52016000a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 260042086 1250 260040836 260040853
    0x12031c06050d14011b1805040c050f070c0302030d120e0d050417010e06040c09050f06011202180613060f020f07062016061206080a12200706090501080405 68
    0x120342100740b0329643c803107000100c2c1145c025050320702d243d5803a0071100081407015024403100300200e1106805441d04450030008040314180040860043c0b85a0707a4552400207480002e03c1441c94607000210341c0102100c1d400c0900482c003d0566079480420160725041080d0703140d1819005c42c001e03084058030750b00c00f07042516040c80541e4501d04020714040035580c9845042c4041c0382400020721441c000d4440c04041d51a00400c2800c462009010100e094464828400c0c1030fa07001e000c004100407650b001588810007603800256001c200d0190592242000035101302c0600400c60035004c858071a155500d03214044035081e030b1510880d84882c00190020b1400f40151170194020a0807050318000e1001e1081c4003211071458074115103c8090f1103990301c08104600350340f044020008003200c1005001c140c0c5483c2c103041d41e900c58420000c04954511583c842080e1186880e04000d1311020300c0c7d000c54004001445880304480d00600c80000e0281c000030030594003c04d070079405660b01800918025 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 260043336 1250 260042086 260042093
    0xa1203080c040f0303080117030a0210021b1902190b0a032a03060e0105030309010507111504031103060f0f0f061507060209030d031104060e0406030212031c06050d 72
    0x1240080002801c8541444041040c4007000d440030003645c4240c44a00495050103460590a4040b424589942d8030402ca01c014295010400700750741e80c050000075032038800042460f50300303691900708007215104842207540319a01d85031341100418000d40e288681c0c0e02009094058441d103a009660703101400304188a0b510303220307600000e00b02c00c020303445005048661082501a442150044c0c00198a403182408110410031215004100072401140b03000c0300b40340081c0140c080c0c0040580204581d0322a42032945a42420301050503100b582d807030b6142c3e26031815118040011087c9030281c0b180600103060000d1701d9591502400700054004140d54030f60040f8000003034010015070b009160402c0355041d000c41c1c0d201074080d143c8201800350b1184000800c1c189004101202c0710101400c02c42c1d8864903c0000c0100c4007603d480d03250111143c4103842c00704000c2c3c03071590b20081d0445451044008500740c003102405110401300000600400744030010f4054034410300445074071584449201002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 260044586 1250 260043336 260043347
    0x6050a17030405130b030f0601050310110c01060303020d0206010e10030b1b031501110c0904031107030f030e040c031109101419020f1b060702040b0a0605180a1203 72
    0xc800200200c038542a100d40118058441c0140c84000b05034807211483e00d0fa1400780508041003003110010034640d03241c0000665a010480303c2050080c1d941c480c00c80500444900300c803012031000d0001d010440d44c0e454025070f500c864818410041c003808001042fa440358204072801040050030102625041d6101c0402c9400d010706121407203d40000041d05058104010350f105e101e924031420004400500050b0900c00c010079050500d40103c140041c1c2e03076a595040d280c20a4240c503100300c1151031441203624004c070642000e4818003101d50b24004165101400545a0703e09460074045881d400710f00303805807000d091901d032040e01c0078403411985080c0b400740d007080e0714000c0c0762000c04003080c0681041c0365400011b00d05803021895644c0c5440d0350301003144845070481c000042104400e035144054604210403500e505c1120001208025550795030846980e0300d60003404440c0051b526003011344076a114119101c11191040b00011941c5480c8452408491141106511050b903da80c103c40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 260045836 1250 260044586 260044619
    0xc0902090f13140a020d060603060e0f040f0507030f0606080307020a0b16020901030602030901060501080f070f0509041508010506150f0a2001050a1103070f39140106050a 75
    0x1c2da56075400380d400d0200d01c4080054000d1a04c0d0703200591707030001046070006964803504214141070130300c0010481000781d4090f45601104031215125507445600e0700b403500d448410409001e510446001006004c8141034500090f48959001c00c00595074101c015224011458041d50285c115241000407420400090002c01d88031481c001104146500050040d502a08103880040c3e0200800800003000d01c40d240c050103003401c01990030324044a83c01c2d60711b2001071401041125644108a9541c050401d55003160070080082c81092554460030400c6500d600c2140441d60a0002045a0b414007640750030075502e1910000b441e21000d00c815440c42d92100000c04200001c280340544010b01592800081c1c2c042040017140c541880b542c0d503030a5070f01d0700450401c0104d04000340244c1d00d4120300900140c203a14144000700a00211103003800706448e88003141241d041e00010150f4441c504401c0886070706ca480709002038802e440c1890f0881d41c040c0640354101d45060740901010300c60740c18008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 260047086 1250 260045836 260045869
    0x314210106052721160605041a0405061b12070308040308180a030e0d050d0c030f080105181e15090c040b041806080a080702011101050408090d0501060e010b070c0902090f 75
    0x44402e00c4c005e4082103d111658441000208041810300c4035804802d5010703865070044102604007400d18000404601c00c1804000c2e05490140c5240d0842c2c0041c4a402e500b5180000d4075500c070700d05820041c102000440d000c41c0022103020006003900780b080d000b030882c100d03030800600e1450140e945c01d584000ba1001f90740d41c420208402080090400c0100b90a9007125503180c01c80111685005425141e0312151700c0107010710310f0018800ca8840300078002c21310014119496082e212200f0910041550070480c100709001c00d0708000842e003100308076151801d0144c0c1c41488582d14150a014140904e000e00c2189401c1000104040800940c40f06104101e2110001314950342e000c034540f4003e044d0000b203e021402054050941d0380086102e440c00f404d400007481907141035525004d242c0304400f4007a110301ca4005500080c00800d42c00030024000e181d160f03005558452407442c100d0b800681d01190001c40c0550301188520440c003e0340d0783c4050152070100b1b544d4011040100d001e03c08402c6a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 260048336 1250 260047086 260047093
    0xc02070308040b0703110f0c010804060f09050705030c0301141512031305040609020a21022203111014070f230c0301090314210106052721 61
    0x840826800d0004000622a48403529550681e9145c060080c0d512814100300c66007009609030040c84d008583c416800f0f40c02d18144610396030f14a4004000c003507241c40701c2c007640d00c0c01c000a000c10400148003030560318200c3c201d400c0da42c0703001d04050a8445074900780104000c2178021412621611250304052100203003001c004500f200d483c2442d6400100d00c02e1030611100c8030801c42d90074184aa000a085660000d5103001c00c140400350115000c48030982c824010450014500303a640e50554030041c1100d1400415902d68240c40e1001c0ca040e030209171149102040092400e117020500c42d2013104094540140105800702c2003003040d00140e00a40b48049803861800001e0380242c2200004d1800000d101d05c0c2407100c0c140c1c1c0b4541952642507034066854041440d02107904480d50500140669508650b41c0211302803c5c41030071503078049014600d17a44000800c10a40100c043c25201c0140c4001c99108980b002303048a10016800c030b081c4d080703100e0301072000c0c001e80b640c1d4044024031000c0049 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 260049586 1250 260048336 260048339
    0x207120305040e041a090a12050306030d0f0e030f010605030709090c030b15090f070206012c060607020a08060403030b040c050901050a090503190501050123061b06010f050907031a01030c0207 84
    0x10f070914171001c0741c0001003a00520131180070001c3c519108490a07515103405400c614080d40840ea41d4030301800c9840c18402c0d82e110903120180301d04080009100050140c649030240409031601170f0501703005462181c0500c03d004a035500d49071150488160308031f440c0080040ca1910303080c410010140c5a14030441268008010b69100c0341c0840f80103505a07141038029291000c0020b0602034180c00c109458042c040761403040703011007903680300203c0190303400490076144c480000c3c00603c19800000c1d00102900000140d20001050381440313940203483c180000070242c410001250b810800039001f00d8402d0000306210b5104c0c0c0c0c0075010310196810b00580c06030f110b200091900301401c0c02c8080200240641a080140038003405005004445d061804e11035031920b0034148408203189070f40501e9020400203c0c01e002c0001071011a510030040d2020740d610340c06010b41c000318600845001e80005804030344000c0c402c0c40798829a0010b0351100c404000701400440241c800441c0c40b40451040c00700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 260050836 1250 260049586 260049623
    0x303140304020616050312241807030b060d05090303090724050d0207020a090c03230c07050a120f030c021f020309030405121e0f0307240e0703030207120305040e04 72
    0x20032401000405072300b00800704540b400445c0d00d184c600005010300742a084511074400001e40d001c1e00000e4508000c40e401d03202402140f114018290144007240c2000705000b14000e0104c000c50081c0100c030151804103442b500301769420002256082d4907001000b2031518458401c0d005000d041ea102d1001526104082d0002100d000803504420b20041d640e0801d81103851309032007440781910740c10811040e1b000f034403415840b604800400e40d0a0045c400100c100412605101c000525540007800b450b00d141c40c04801010143d40c18000b002080c608140c020102e800020115991b00c03a28140110307090800162101941010384110f84a10060001198075641c2c1b40c0f01c1d1000481100007881c6070b40c40c0070300780c11a89c0d0041e40540307159008502ea513040c0590101c2181c10139600551500e04c44015a5486524494030480c03a0802a00d0101044054003000c5505003c9900a600712074240342c8440102e0310820092000601150042008100600000328095400b90045e410600e250b540140b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 260052086 1250 260050836 260050867
    0x306060c031909090b0f040c031e06080c0402030103110f0103020c1504060605060309100902191e060504081b03030702030601030b040b0a0203040807030302092803031403040206160503 81
    0x140c2d40c1036101500035031010540d40c0007041400900e10b403c0b0900506a6120200b1616034203114468019a00d5401d200900c60198104048007244c00082c0f0980203501c5c500302c0001c0006d809040403501a0841c8801d2900d442d00940c0d069a07000250b054a4141c40000c10001101284442e418940c00b84440346100400788a1500c050016815070b001e6403074645000d13001c4a82c1c40d00501d1040b5010705c01d01848075800a803401030400003e900081d60f010b51b000064081d00e400e8021003104202d15008034011420410703400220703c000606040903a2603107400d444a0003117000e0b449169201424031046502d1015400c402a10080e0680e864040950040390804009820643e141d40c10700050104102a03502042d92100480d4411402c600b05035541d20501d101d9194081c04058012030348042c140d41c5d2503140c110200c00600401e0b28440e50040d0189504283d2006070040344140340c120b001c00098900b281e100f15401403c07145020744514900b2a402646001907940780302c14000302e0048070001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 260053336 1250 260052086 260052097
    0x6041805070617010f0e04170702041104080d08060f1009090c0f020708010608070608360106091806110c030a030b130c230c0102030f0709060903170306060c03 70
    0x15a10380d25043ca08440d40b03c080d04045c0d100d81810043d242081180d00ca0a8402c0c2d40c03c59448480c0f2100030800011400080c021149c0281d4040e20342244400c011000780c4c014411528844281c5080c2d102a0100b610102412101e494104181c0c9203405014503058103420b8090502d400c02c2e0039640d480ba2050021119004990720110b41d203c520706d500950100440c0c0700030143e8100a005841c20804080d8848070b991040100348140e11004c61040409502c3c403e05050359246401800b0b0740400d11900d07003411258503203d803540b03060800f1481c0c104030700801d00010315a0f0910300441c0c1d1660f0381e40d00200b5080b220082c0002d030070701541844800500c020140c501e1903540101303030300300700742d04002840c004443c45610051130700035514001e039004201d11004558008040072101e40144046240e4811000c8c401401e502c00010024602c502c5044540111429551964095219201516110424000034005004003a03000c030a4030722030700c021680b1034800b41025040100d02e40d041443d60300b00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 260054586 1250 260053336 260053349
    0xf0203060904060b2b0c290d0605030a050a031404081f0e0d080702060a05060d0201030b1f05030411120a2009070201020a083102040207021c1104020702090604180507 73
    0xb59000d8180485156844003030000c1947c0015081e16907020605000c4401420308550540400c0701000740c000c0d6807000f0000c0002400f81d0341c2c02d00080c40c00640f100202e15044001c01c0c0300c80308c13140002c41d0341d10555090f41e031036a00900c6000e902c0032500180d12070003403185146507181c00141619101c03d01c9000c1c02c4a555880d1240241800000641000002070802a4443c80e1904001c3c141e0340300701d445040300b602070070700040d040c00034008100312071484844034140200300303200f41000300c2d0b1180c020740c8164000c0500d100492021020000302910300e13105000f141c2d204a0812001c100e071014005c9942c00d4079a0b00c110984c41e00004a1007450089908034050307540442c8500c0900c3c0c001c46072076401003001034402e080d20380c0805182d00411040e00381c0000700c004a030900c021904c03994120307041e07a0b8005040301c0003185101505104040006411207000c060b0308c40500c2c0e5030807e4000ea031a101c1d40100288481d50ba0942408000d080129090084a15650350580421400d00110018140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 260055836 1250 260054586 260054659
    0x12021b0115090b04090b160210020408031b0105090303190b04060603020a1b020307120c1a0901112404030e04050412020708030f0406030209010203041805010303030f0203060904060b 80
    0x900b28000e401c0302d407000c02a50295013003561960000e4203084c41e03181d00c00c45051503080b041600302d408920304110311020601d0144002408202508000054a144402d0788601342d0001800300009007070300c60030349a50b020365000380701040c0c0c00d2107088020b070000f0544000000e00c1d103288200080030b60342a94480c0012039030010380031000550000210001018958100100c0c22036a400b0903074502c22403040c1c11000c15004100320801118000c5003008000c808641040c20001200504a03680560101408101820020302c87c9410104412524841844030303100f490140054039a14010001c100302c0070003000c0320303d04040c0d5841d880350f10300890040c1c02c013034540100480c000e80760000b1900b10030f81a6005003c06086c607613605084034160340d07041c134000d41c5403e44000140d00e0344c041e54010b00c080312000c01801042c2120756003e54105c03400395906104000f00329030f10300200c0c881540e030150400042c40014000c19030a4110803c0030718090b0000780a186e20b46200e060904000c099000031a1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 260057086 1250 260055836 260055839
    0x190603090606090902030d050a0309060914070f08060c18030607030e010f3305061b120c0a0f0516080303090c0f0307030b1003080a03020306010f0e0112021b0115 71
    0x1189100302d0010f84200c020422000d5503980010703540344618100310081004c00144509468820b4202c423040b0740d4010414440e0030f01520742130f59014000d0604011b0b62040000000303950300030080f1401161540320142c030407a29601166526603200d000e81c0320049048100e00c0700240c0b41041064810256643c00140444005140500f503448840b0300a203814100015525100300990070304280250207695402e03102e103001d808540c0c03a1802e91205611032404550602080010041c48100740c45010546821081d0a40040601d000f168038910095108181042c000ba1803502c074002c00601813002c03240c00c0171401d01107102801941c0c00071429038001005201140c00308000d4035040c44030031291a8034000c2050007180d950130f02807001a00400c1190046001045020000b00295421100390f66482e94003c43c0034010790710a4a4184c00120f521005460f66442507140f1490742c40140d40703100d041a20340a51030041c2d0056a2070b81038140c40c03004043d028038403d00c03a0310b17001c1c1c061085201d202d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 260058336 1250 260057086 260057093
    0x305041d07020705190504020702030c0a0b070309080a03090e09010b030106090902031501050f0607060b060f1803070e0a1a03071e06080103050304060302070f05060106031a0301020f0a0e19060309 86
    0x85184e500c41801880310040301d0740750920303030b441c40001c0e51030940b00103869819a00029180904c0d44591035040301090401180b101c5440c0d0003450614001e480340800907658012060b81d46003441c1d000b8000446078042488100c1c0203003071040d0004001000415075500c01c20019084074210f62010312901d5560b903c07542141420b025079102c3c0415542c40c05080e6140c500810310000e03020540c3d0384602000070780481000300300d40c0200000c01d0080c0201341c65000058040110b170f4410400c48184465042d00d820303a42c076001480c0303402c0c0c6400011059054942100800c040d258901d0001c0d14000d4806c0898015141045404000c0007003c00b50341c0410f81c1920994210342d900d0b0408010002442c1c0140041070000007194201d0340c6903d00140c0d5031800c0d0410041d02011000014400d0141d400002040d030742c507030490300e841d161031200d072140c000010b030400d401c0b4841c01403203140301e2109010160511380144c0001c401140c010300200d00108003501036411003101a040b4402207a075a944c02400d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 260059586 1250 260058336 260058343
    0x50901020d0e03070510020a0611030f090328090302030a081e0a020a170f030a1a060909040611120903030709170c0d030909090f0611040608010e040305041d0702 71
    0x4000d06042c0000e5140803039002c40e07100c07140c6014090180d100c00c000d8a8034548208600304040e604180100060440d030300c400482d55200f561560400700040000c504081d1010044452201803039114100700c81940521940c400f40c1c52403e03a0030301c040e010000001d62028001491f0040c8600c0150b6900c10800c100c4e0410499400520425040705009106090b5000038201c485150007090391001c800711f410082c03000d0300c40d40c4190608000c010003401003440c96030708511034003c101c812a0b070444403400203111a9000b049210b5901107082030110b004682c555001e94289010355107913500c0c105280c811070a5500c000c1e070b060700260307100004008d00b6a6128010360040c00c41500005114651031601a0351000c00440311849802110ba0030001c16000302c0c076141c000d120105060001c0078250624900c008050f0405650f15820071355801c8120140104460036240203841d40460b503400d120005002000040040341400410400802c101d02c41ca00c000b00e03100104000e204061500d07910080c04c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 260060836 1250 260059586 260059603
    0x30c0c050d031110060807180f06090f0501060203090612090f0a0506011403061006080a0e0d17010f1a071403070606060f02070f0b07020a050409030305040b0c030106080610120c05090102 82
    0x284d05141c100b0038013041e07101080c0c410854204d40c2261074004c068004001c000c001c40c6040c1502d480c0303070480020380b485480d00591100260182d082049a0307880394203a8a901ca40002c041e0302c440300304213243c180105d00c000d1582100403001100d6a120016903558a4908012400c1d19140d200000400c4008071071048400ea03034205a000e0000744c204140e141d610341a4a02841050001241c0011550503182c0c2c0201a0201560121410961208005480340c2211500f00b0309049440c0b0021882c6000c500000e000c4548980707000002108420b00160f050f082001d048030348010301d507000c0072115400c0021304615402520001155490300e40007410034599140d0850554101c00c8007004000241c100507012a4203960446945000b18400125130240390741180741e015107000540030a1643c141d0080e485244240720342c00365a2610100740000380403d02c10310000172071743e01c006220b90a1401241d0800f441c1410940c400601006c2c1610a486210b6400c90000d1000300c0c0302d448a6030704008008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 260062086 1250 260060836 260060863
    0xf050d05190804020d0b0414070b030615090a0e01030c050109060804050a03031d03030411040b060c2109060c0c03011a090c09011e080a060e090a030c0c050d0311 71
    0x3440d1800c2095485000d400c031a0803207052203401e8000905545401440e101c08030b1340241001443c0c6000d01d0440c13491041004498401c6c8204100031072031b402c2200c12207000344c5005080c020001001c29561401e5400f032203415400c40290f113000540306100714902030280d4403803807450340310701e050000051a0702e4541d03211004001c449421302c0702048000c900a020140c01d460082a9441c03866140e0308006000171402c201c2e888004100814488000c1c546615040c084605120301c40c1c140c410007401c0d014107803074041c01d60030007042000d030310400c4442807070180d00c00b032169400c1112040006045420004198249401407420314410385404c0c410601d100c0c940da1511800c030704045003c507074800b5000342102c288120001d141c04060780550580c410440103110200c408071301014000780351100aa0b2903682d090308080022038421030007200c0a10070900c1c00000c0080c0902a02d0440d4071310140b081c01d0301c61324402900480c043c1c480d0003194820728000d4880c20580e81072074044503c2d10f0750110002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 260063336 1250 260062086 260062097
    0x40213200c100207111509030d0306140a0509010e07020c04091113200903030904050103050a030806040c080a020702010c060f140c0c0d0c11180105090a11090d03020102040e040f050d 80
    0x801c005044c45e244500680419103060a10036a02082c0400381e2140004444e450f01c01c2c500c040e039040e903050300b0410940b44044a00000b190500041c031041d10502c3c020540d020121800502002d1045004940d00440901c101c1d01007400040128045078030018081e2000d0304200b61407100c50400014a01340c0828100007004800e03082031300700911100c0c2e0000008000000552200c403030b9820030682e004188001c2c400c1125503034902c0c0c070654945040c00c0440105002d680090002d01e080d1081030059031701500c400d02d050b034510201800070340c070440f0228144040841d91a000c0b132030300d100391b00510a4103880055603071840d4840d11100c0d0760003403a56a5a5200b000721701c61802c008980c101c03591000c1d081c000b080f041140741c0f500d030605002c000305800c070104685801e140307400e25100c581241e030182c59144a645030006c00b0341c25a0b80003142d0005842e401c1142c96401e0a100c4401050240a031000500f025124480300035081000c2d201606d50741c0403641c1d880140318040c02a070246841710b0615 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 260064586 1250 260063336 260063347
    0x403080301080f16060e0307090f06030b0702031306030905100f020307032a050319020a0f0e011704030e04091b080d09030b0601260702060f150108040213200c1002 72
    0x1e13911400058003880c0c08024124464117400c5d00d0802100010f8440c0550a2042100380b521340c41c0203006074401900c028100e41c020604460010046620311203540d1611585281426803e5000e0052024115200e1242e2011207540c844c13640b01d881c00c0c00780b00000160362410500c40081c151030714541ca2502c0c0365446c80c4800c0c1c1c3d40d0f04000c0c0c1a0790044d035070b00740107803070359168842c0785d1104c4410000706019a0000802030701d00f9502c40040800079510342c0712209a80c0d542c3e03004503034000060480303600c3c1010040c04078003c28041c4080b02c6803030a0044c804980e01442c1d54550300c40b0103e0541e0b1070020a07410790b050104c00c8061058040c1505286050140a0b18540710a00401c0703020348540c1c14401c0103091400240f40d5100398014054945500d44180d040c080780013560783c41e007110345d1100c0c0072200300450b1404104140b0b200d55840b050351000000d845a80030800283c0c801403218016503030711a0349002c42102060301401c40c140c03191503591280c0021400c14144107003942d25100243c8100a07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 260065836 1250 260064586 260064613
    0x312060a140d111009064a120d02010609020313060b0301020903070618050108071704050703170a03110408030a05090301200c0d23090d1704090b0414071805060403080301080f 77
    0x3004c440221029040d087c1210f4120314074002c01d00740369004e40264842c2c101b100c011000140720043c03d8032642c004c00a0b10b0303551246d48201d00043e0b40310540610340c20260408282a0340104209102c0100018a8410310800107890b1407901d5008401280c404d442c038000d54080d40c22841c000341401c3c04c2803001351410080003001107030b0501525801c0b160200205003403000030403000020310351040c240c2d40380080d480341a0800c1e400414074400042c0c00d14417601d400301c078100282c500b2109040011030601162000680b0f8680050200f240c0541d43d41440003244800d844406d0040c070958001203642d40d1503d0112070030982602409414080e440c1034084006240195011000d45010550f64031102c0e003100091100315651030140201033f13526243ca906802c900d000300b003251500323402044600170300030911050f0b400041a16003d85200c100240307a8501900a0082140b003010041817401c1d00c0e1780020701c043d0026042a59070000110052148210070800c900100c1700038001007224810224 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 260067086 1250 260065836 260065907
    0x91005091510081504020d0b0405090a02010207050402210703020408240f0703150806180616030e030408010f140702010b0307090c02031b0312060a140d11100906 71
    0x81c0d20b03070411405400180180c070440912840c0b50f40010001d5507101468402c4002606124130120701c901d20303000108403541800580c182c0d00c0c0d5030680140400c68a410b08001c001d40081c1c42c0b1105010646150342050310740c000e4407902c26141520018cc4440c100992031345043c0b80400d200c210584d1004007005030304d0700052a02c0c0c0c420b5080e1500401030b80e0b01c2d1003c5019145684034840d00482c06800841c2c5204003240c242c0c440d459201d03203158400c00d00210325a841202340c4048289400c02302c0c802258910a030482c4441c00350050440345400c2d52014203600b107505210381064550341d90791000802c001036681752600111584000e02c20604140000781d01c4220324440c56262580d01c9500d1090071b4002d0084e119211869040800700f400300c0c403e107585036804038002800a140032000500c2c1c0d0300d0680d05010550b00707840542d240c450010400d0103c00c8004a2095440700030300d18072021107540d528801311002e09a60b03203281d21907140550140c00744899820901c2c51a00550304600e07118100b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 260068336 1250 260067086 260067109
    0x60e0904171c09030906020f0a0305090d050a0c06020d030f0c020c010e031009050c031e06010303050a03090f0305070b06010206072a0c061106012c060a050910050915 73
    0x7401065612001c1c2840400348101e010800b00c051030030b08003890300385070b0451031203000c9940d1340e000e940116200d48411901c44c0b021120090109078140021181810506102d0a1282c400d80440d0400300f042e8445850540c2c9560107000181d004105150900740d050140080030307240e0000500c0390a0155601940340c40d10f01142c9030404c44003a640c2c01e07140c3c1e0100200012428400340c07c001d040e0050402c03e490b180e160002c6400f900c64040d0344203645200c000d96009090b00f03030014050507400c2d5503089400750b0240c088141099102d26102c00418000c035844c0d0b5000c0d11030740fa555907400703151401e1802d4010062185055410101c1041002500410b0354081c07811012044502001020070f0f1525000b00cc08001e02031206842000c43c2080e0461003200c4080444422200d160b0f80c0c605c0c004c0203c51030b01c0c443d0500100000c81c040c1c5c0c809001c48030a40c1003030380186200b1803c1e446034007041c8048002c5072582c0040c2030314481001b443c1404004203070806440c0b4105052a0940c0e000304140c025103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 260069586 1250 260068336 260068373
    0x150e0d031a060d0f1b0207140d0c030f0c030803070e0f04050c0a0e04090b01120201021011160312050a0b040c080c0708070311100b0f10021e030708040f060e0904 71
    0x9444101d8120140c2d0f41c0a640780005e12103108401c95062100255a0106ca00a000c18610341070070b0344080749440480d403c2c40c1c1381c1c0301044084860640e92048800307100e108045901c940d4003a00840001c1e0007130051881400d1954511006180000c01c1000c0c1c85c001d207050384c0c0101c0c0742c00306205072416010120b500c0000a8100071590503494008500248504034002c0c154440d1800040340ea40e07103c24804544d14002d90890728800c1310881c42c541164540141c620100301c0030031841c1801a407c012401c8018002d081060511b1046005c3e541513800849070031150980c0c03030155000d18617062241d804800810b150584003454510b00703860252056082c041c018a10204542c400c05201e0a6148500004030060307600141c10f45105101a0041c5e0300141d2041c1e0440805103190b0421114220941820380d004040f006086203149180200c4200d102845000805c01039000c210500c0050008010f0703020007402c040d1600e68014684c43d901851188580007207801c2c00301040c5140c4081000c07242c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 260070836 1250 260069586 260069591
    0xb070c11100f05090109091a01090b12040308060d02030d180605120c07020423091b130504031b031101050603070620070f0e100503010203160309150e0d031a060d 71
    0xb1400010783e504419584022011820f2505501c0740032001d0f19231002505003030f261141d241c3c1d190340800916000b00f200b0f5040d14100309002801080c4207203440c2d40c01007406401c1c070b004101e981e00801e040c071046400c81e901060414558540000c15045680d005107598a0441d0810494060502030341e44042c103a5020301d40b000c01c0020642d582d07544250020800c507001c07c00000401038540c0d00c0c44800322101e03410750081031156410038103120072a022030400101003001d00c2d0310b1034819000500001d0419001c1004c200c0040c110041c0001480030458081d0729140c10a8582503045070030744034028400b41c042d80060300c003040519002035403100b041040c1c080164042c40c510149609c3c00c500c81d070000140c2c02e041d200026032030101500030b1303014000406407400125100c106150a07480161030544a03100c0500818040340d100e5440060308a100e40c680407400031020101109480e41111052040d412800014068940521810701030151005401641000c9100000c9980c0500d04030200c01c2078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 260071942 1106 260070836 260070847
    0x924030f0d081906210c05030f0c0f040e0703141c09050909010501050109090f090218011518031112010603080a180b19020a0b070c11100f05 62
    0x5000400b24481411208001c0003580424442590341c40c024020100c7c0079901031000c9222600f41c2d400814040119104000c1c154540e680d00034030491414000a00000010810204a9410011b08201c1146209000d8145a0050003401c05450102480340540c5d401028550a40364103413441c2102c1d941c1c84c1d030302d40c3c2280e100303004882c0071480b24482048000820b401114901c4030402c00458241000d1780440c500c2a4071702c0d03030b8121081d4041d0060000a0402560101d030310094a81408801100c0001426106140c04050408a500c00300000503869950840c940800c0e410020080681e84c1d040ca65442e4004082590020700051200d0300104400722800c004d0303860800445203003891602c100c9601c030001c029048250f00401d0122800301d002c01d20102d03c120320075110b91002e08a10303c0c05045001031650310a201e00340d10001809441d500c03049161025206040059440 = true := by decide +kernel

theorem cover : BRFrame.Cov 259892086 260071942 := by
  have h0 := BRFrame.cov_init 259892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 259892086 ≤ n) (h2 : n < 260071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
