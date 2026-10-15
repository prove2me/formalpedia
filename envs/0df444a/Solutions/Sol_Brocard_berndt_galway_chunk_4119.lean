-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4119
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:37:11.744781+00:00
-- url     : https://prove2.me/submissions/83bda81c-3c59-433a-8010-6dd10eaffa82

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 740647482 ≤ n < 740827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 740648732 1250 740647482 740647489
    0x608030301240320030f0f0609060d050c090405030a11030a05040b0322060b0406090e07171504030e01111605130605030a05030a030507020a1a0705070503180f040b 72
    0x40000103408882e903680c0035584120b200303030800304051075044540780a003100c00c240201c05510840350140c45086002c00f169003d410003034028014103004040c982d981c0c0380d841c2001864a9583c00c1160303d840307186150740300c6407501481c851085d4091005140c580c1103000019155a091405080c02c1e908100004500c2a811a0954054804180c03125440390b07103400d00c90b0700802cac55020802c0c00b8558000c00604010f05038214502c1c03400d0a0b501840030ba03035145840800d6440010340280a07400a940c240404550002042580081c4400b101c44060ac80702101200100596041d40003840800590b25507507082524604c140c41044010481c00c0c1c078505c210301d071580f0540203140c820b0700085407a034a0b8101c80c1e04150040e2000405640e0300740d1092610586e240d004444013070100f428403000030000c43c004206d141d501600089400d0710701c000400c025074040b50040c00b410074880b02b40070b4140451020001380002a044200307031168500c0e50400c000c001c2c0007821040d4416820114860b0907502c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 740649982 1250 740648732 740648759
    0x6010e010803030f18030705070501020f0a080301050d050109170c12030103080304120509100804110607150504060207120e0f0303190309020402090315040c090902060a050a03060305070f08010608030301 89
    0x144c0c20001104d0b10348a03400d199500d00e0012030940500d200124003a42030000c045450000c60b1403d0702156031200c0c200032051b4030780003000e901414094083c0700400c064204509450701c824850400060104003a5aa00354010f0350108407440104000c03880c0c80d4606010084d81a0024801490b0350540d85075580c1c01c0350034440200300901c00403a482c0d01f8040580648207031049000c0c01458540107100c0c40310000e0200a003218251006542e84001c403002c1d003044801ca4200d075406c10492440c00c0c4081e4005800b418014004840c03d40e403c01c420300c0030440030121010780c91125520722040f005c1c2402001070301c122003545644a0b40040101c00c6e186014950490820200c60a01181114080c00000c00034000e2601c0250107008031501d25084400307803691580310f14482c000d1389170955207440305081141c2041d0300081d0020f0003003040076441c50082000c3c0801d1061850082115910703565021f0410015900805040b0144c51090103288420300800f0050700540d4025070466240c0b00801d003d1a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 740651232 1250 740649982 740649991
    0x213051809010c0e130c140c0a1704030f02090c13090209090a1505120f010501060302030702061302130203062107051c020a140112020f0304020a12031211040302040f050906010e01080303 82
    0x556035902c00f800700038000c0b00311841800c6087c06030b54460b0302c00007130340e034031401c84aa003120600c003035064100307180c1c0583d0280ca0960760071207000c0c2d00c0c009141c0e0034480103c001a06940b04200240000303420403072001402c46c090042e95001503104e10384101801301e2203401421030110301d41000380344406c0002c020005000c450049420041440a01c0d001600f08900a8140c024075424072001040f01d5405400440c02440b9035401c5640700d64902201d200550040b420095000f0015803403a800c400c0036070055030f00540018071141c2041c0000030b00c2104000000640c1015401c844d10410251410101078455002d01d8525110441110b0b40003440307a03071260107034074002c00d1004010480d0380d206d0400e005800c0950201150b54600b0030344616815001228201d101d000601404190041d02c0001001720907410380741c00c1165002001d040002d40840d80e1100c080300c0f814480080560b640e406160a0362100e5080041c00f41000c2c801d05080100581005022401c103030010044201c0000032641e00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 740652482 1250 740651232 740651269
    0x40311240a0905130204030309050d080a0e040204051c02100507020f0909010b03030301080c030d11060712021306030614060a02070605071509080d0c0305070c02040213051809010c0e 80
    0x81e401a018266565655500582c0c0c0041c074007815580450b03c3e640c018010740303001752200302c80d0f990b9803010004804100803004102e080306000714000140035a40c4400e058200810140c24242c840002c500c0e4104a54580e4606040d4082c105007581414520b01d0303002c401034a4070610f061000c0c2c0200382c001070308842c0d0900818500b000204102429441501501d10040c15a170f500c3d6945c0150680d10032440e15580c0c46809500d031116510750056900e25106240301d4042c1074107075a1042c0c2550b040900c8000c00704c5203074007003100701d03907030510300d1000b07405000d00d92070025159007002c811005000c2c00c0c444680c0100c4040100d050400c0c2c00068100441d502c41c03520300c0c2d64108501d404051500c5540030005118140910442000b80d0300d4003800380205a02d000701300f890702c0410214140c90058500c038022406151102000d403c081d00207000c9121598400055165503c0c04104440e00b04a144408000c07039405001aa01d800c0c00b407a460070340c0e03920700742651a54010004803110300c00c2480d0b4a1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 740653732 1250 740652482 740652487
    0xf090603010204030b09060907140a03061a0402030a1401080102040b041e05030607030209040f0605090105210319090b0c030a110c0925020616030e12040b04031124 72
    0x182a6401d40456025550101c00782502e418114091950f4880943d2409128040e6a9001c03501c2c82090740c030603146910040683c0c07101840c58481000925994191b82d4121804000d0040d0f1522540005e40c05042c100d200081d5503482c10409000717914041c1c101c021a030b4010401044901c1005003500c0035a41c4a800c000319240015130030707802514881d8400ea8150040e24204504140c15038050b0140c0c5c507040d0360a0000b00f8030340c4c8e010000c50725203014442c0d100c01410014015401d003420700c40c0e90440d1400c0c11070911028944210b00c1c1d60001c00c0a02c6030711400b500d1040c102580001007000400801001900700040140042c3d00c0b8010403202c40100003d000d510b00f0f580d4010051368002c0903010305018000d081c0921070b01c845c00345a100f0b4501c1c0350305c400b0050174250700c00900584642d00130641d481d04500c52440480180c40701004092079403150540c2d44944194100050004104128016684518610f051f2000c2540c0c181582e103d04c00c1441110010300c1c0715200c030009070609d81d01032079 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 740654982 1250 740653732 740653741
    0x12060e04260d090308011a03240d2a05190e0c0d020a200714061b0f060615120415230f09030702221812110c0f09 50
    0xd42c000c0000380c1c03195506040c1c4960a060b00000c40c00c0c1a25841e003070140304071204d0008401305100a4691502c0240c0f40c0c1c0301011150b09600141025020050101c08242190303210f40d81141d80d04441880700d4003d8440304040e041a4080000040c00c003079900c0301c10ba64030b6540150f102c1e8128881c0045480f075032030000340c403103400307004803102c1078414402191142c611403401445401400c00c0c609005110320b528081d070b940e0003c3c0c4003040b1802114044180c0c41e0810031300802d5081000070512039044c0300710100080754280b041c0742c00e4600b00c000500c6545054800c004004403400d02210072124204000e02c3e08841640e0700981c8150440701042a109030703215954014180b5041f07044010050a801d60207039080c60514501030002030200c0364280d09da400c0f03000c1d221b00c2000745c02580320340e1110981c0b08107422105c2601d0701d130074130410024494007218009640c1d40d6201070112607240841d4800f042c0c49030402d125105840c4441c00070f00315000101c010a20101040707158034442e25103000001d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 740656232 1250 740654982 740655053
    0x70c080a0e1c0602090a0f12031805040c23070c0519080610030c05090c0301032010051b0706020607050c0118030c0b0708061c031e12060e04 62
    0x9094020208100b2280490a414800020742004500a11506075054002180c00360405040280d65003404500009003a40c1d40a41d0f1514642c06404401007407410000380e6942d4034400d40100004e80d44170119020442c4c4041d60520300200f0610085d01818040030010841c0150000c1c29210103032204000d082c05e8031203143d5004106c0e845000d0b20f2081800300246600c2c002600390403244503403143c0c0300b9640c07544104502ca0398201c903c03495842060004002180981200d03481103051b90035180350310107128006c503c0c2c08107681d001d8004941c00007003510b902d601c0040e10b1a403124030718004e00016030805070020344541703000e01410108071002ca014044a0740a43c048442ca0001c862103082802c840d1a010700545c1c414041503407090238040c00107018900500e08644541001030800d40342d203981c902c49101401013400154104004411008081c80755002c003006500000d840340c0407000d20a01400043ea406a0000c0850001c99014080014a04004014001f9a01c08089400404041d11 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 740657482 1250 740656232 740656249
    0x9090818131b11012f0408010920040e0604030e041d060f010b03010e012c040b0f1003020603150d051912030c17073005070c080a0e 58
    0x80185140401c2004009040c00400d0003484003511070340b8051404a0b1058201c2c0c05101202010000801c141c818075190000b52510403940140c05c5418076031100710150844182800c100d03141480c0046840841030b01600344035003d1421141441965003624105844d20000f510040c14004204000034442e036a50700003d24190f41036002003150002c43e400f5030b90351101a00c100e042403c491001280350190900dc0340e060b121045e2500c6056441c0c04010f5006840500588100d5115440c0b00d00e03828562a1500c0d001e10b014044040c46424400d03180118800080c02254001054010810050300c079001502c0d4483d500c1a4041c20600d108404501b44007607244005026000c1c403900400103041c50440c2011711402640044842c0311640c00c29011a407140110b8004136103040180c00e544049200d429501085514040c0c1c040800e01c442e81c1081d1145441c0d11828648015019010808602c65654480700500d0310415008040c2c40d50f03421440740035031000400c824066090030f107403100c1e00b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 740658732 1250 740657482 740657509
    0x13050c04091113050105120625051b010b0406080601060f0c02150a020f0105090114270d090501020114040804120507030f0605060909072718030509030709090818 71
    0x300b412001240c20f41800800090181c82d1055420780b95000701c102002501e6807150350400440c010800c0c10000d581c0b128010000060200001005418102b9480e00c980c80610f201030f000106071902600300304419580399811403440c070b03480300d401088403d6001900c0410948181404402d84c40f4500100c1e50220300300c0600d41291100040442c86550700103035075081412500001c2010b511000005426260028408524000c00c032010915511792409161035920400c0105003040c0482440ca07402c003843e420805012402d2038000b003225507021701480d0a5a030f00c0144540c9149440e0340d4804043c0118010111400d000410b0442044401c0100401950704600e03d50194546840c142002d001c0840e40345006441180c08540c0180000400300241c803000820400304107100180c050b03031051029002d60050351a540305100c00414584401c8100780070ba44d445650300024014940303845040d03881001e1840c43c01c2d0032500031400100075101507003405040c0501d440c01c00c4000450b100e0a004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 740659982 1250 740658732 740658739
    0x1b11031b0d080a0c0c030305071b12091d0a180804091b110c09060f0613031106070812040309090203100303030c141204080415030606030513050c040911 67
    0x340c0400325032100044424800c038159031070580e150380744411402a40e5000308071a000c2100000d455000900941126034003003403d00d4454900c00e02102c1804500d04064400c0e02c203c0e480000103a0b086500802c1032000d080c11002041000169501c4000f080310000d00c109081e96682910100400021540520b816045102a41c03995200d101100081216008075a0802c0403060580030844c060722032942014a800d0290460414410600c00c4c191401490304d9404801c0722200003039981c600c4003a109038502030b11a01c414604500d440340c200c01d056130318144550000e00c1280300154400341125000c211040c0308058640fa43d02e000d946404150300301e050020b0010003000308440311b81c9142d01c02c6034080d07582844001d4410006a81c00481d140d2240c588074001c00c0325081c03010344482c0703040d0040e1242075240e14183d52200003000032030b15050700783d00003610b1301820030000e58503000d219000040740c0040101e2120030740d5400d40d01c100300c265090051f611040000d0900550352401303509110040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 740661232 1250 740659982 740660017
    0xd0306061d0d14010e160305030703030f020f040605091309050a060f0b0a08010b360417031602070e0f040b0a0b0a060e1813022b061a041b1103 63
    0x82d00b02d40607003160720158009129420900c01507401c0c480a5108076900302000e0361828ac42074600310098101c001901d1000f41c0c00704021021420f01e20000c100070710807a507525460314a40c9040050710b82865001102c640c0c1400741a1010400200302c44403559803101001980014990310f1001410010480c2030303004503007010000341d0101c1034000421921007100c07141144410348030401e59516500d8858082c0d112540180c4403d0310682801c25040360080845100d100180d0303080d81e000b68422500c90740d000b04005c4000481c0742d01005110301428000d00340c1e00441c64050201181440300038005007002030300c00007207036804006900c40280341c10054201c0c003265031602c07005488100c244076640c0c0203c800307a04000a1111011030305000c1c08510000e42021071141d0200420b0034000702e041c80700091509410b003e14110f10a403e0b4030306d0300c246408207403d40c422021454040310004030600072801c20002d4802c01180c03140756800c0c441345003021081c1c0560301d8811480c0d405a60b0310808155050f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 740662482 1250 740661232 740661263
    0xc070302190b04230303010b090a05040606031407030908090105071103062d130311030f0d06090e160e07090f080c0f0a060e010c0305091c02030d0306061d0d 69
    0x40341c4001d203c0c0d8024107100106076491140300c2c01400f8030084981c03207a00180014812418900f00030162140000e2880300b90b1074943d80054100c900c1a4400400700b981d940040040f00000d150b410351007091420200319140c055291100a44115150030f41000070005443c0c0070031450a40344059042d010b03003100c801d0301d801c0040401a400034014960300985642e20340307a210005110b054416625402080d0041d501d96405968480b2540c565104a000600469444007142c0c4050702482750700110107d0b0041c9003150b450101c079000070002c8202d400016046091071400d000300070480307110801840c40d42d51102c01c00c88505045e600180c540b80300c0440000350b580720009014a150b9021070340f079a030302d030000c50400003045154483c05002c142c40107207502c80366000d05200800c1c5402424410f04d40007411f00040d00040350410f41c0c0c456101010500004d5007410880005140123600f0200a00b0341440c00180070040c01c20350031001680c2c0c0d40b03100724681d11540d10768124168011850b2190070003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 740663732 1250 740662482 740662493
    0xf0b031306090b07021b01140a02010b060c0d0e060f03040213060801091b05060408100209150a08040308011a2a0313080c030304150804050a150b04110406080c07030219 74
    0x404e48458006104210113041003e5010b0f8070020380910503116219600584a2100f803990086032081003595a00c41c070121468480600402a8241d485c000d009040406100030b400f012052203001e00904050000c0355900c1010400c49401c240c0484082d140c0a490b041c5844c0a072a0a81210101394204001c407420807440f003030140c40c492842c1111241c40c0e038a44080c480e2078011751180c840a80e00290f03100f0081d02d40e42c0d009004105014000405854940240c610307079500c40040c110000301d10604100034582c0c0300e0740c894050034905541c010010004d464032001c501848606084190803070b40d036501480b0b5500801021aa00b12003070300d484002c90813050880c0300d420b20440741d85000b0300501c5101481e02004907416541e443d1104808078241d42d604940c91840108116428824401007101240140c90080800d004402c0f011400466403002e2000344c45004d112035130784040501003800160b070044c100c00d0307100c20100742c0c040e143e5a007801c040b031070022043d1007420001079034005d01c0107000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 740664982 1250 740663732 740663753
    0x31a031b18090d08100b030c0705010f0e07090c03142d060d06090206070c08010605030d140306150d050408031b07030c02220513030f05040f0b03130609 67
    0x510840ea941e07591841c0400444611400b10b07840041e5801440040c1d18241c000c1c841142c108034100c507075011281c0c0f204010b0074036510540301c401042e1000700351981040340074002d02c9028250003205100c21002c0044440ea6460180075880c0720303540f100502c0c00701901c2907118081e10656803000c01c5035800d01081c009122407640d084810301c1c0c1d2943c501e2400d100071403c011406014082c1211603001042d41b03a41e8020030200804990103401001583c02040a011081c4081d1a0074000010044d15005c105446c015584d41ca090034086101c2d6008a414500020703658400d5080d00d8526180c242c244000700d140c402c0030300e60428280b4090030f00091000700c50280d031050181c4040c0b0f036501466084455003500802c000280080c0c0d510115100504110b04081c40540103450b4629603001440c0080c0d064441c11208510741100000640007417543c8642c202c04c9114480c20040d1805003401c9000210060314080c1002e45080000403403040d20f03203c603041010170380050082010541c43d181054a45 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 740666232 1250 740664982 740665033
    0xa0311070609052404060203180d0215160801140d050307080a020d03020c1e010f0e0109171908070e1c0209091207020d050708070f09050106051603031a03 68
    0x40c461904280803044a0544203d61320495107011165503456544a42c003a600c0100f581c4d80003009036140340e0251400700903590020009802a041c6040107448400002000400700e00380601c0c03401400c4c80464000344114151600201c29071a03005016000c00e0619040d100010314502c400aa480240913400300038041f0111a42c0c2500c10000204404038103900804145000a802a151030000e02e81030340107031560400b1980000c01c20300e0038100c0c441c0848080302c6655a03642d4440f60894200f04030300526400c0700b146011a5030400c144d04841c607580d90b01d081d02e150180a04040402d600d01d000301c0110b507152030000e10240400c5820781d03802c900244684020ad0084003070f4030118051400c08958582100520402c541c01c0a100360201709540d004150142d510f07002c1c810000c1040b500c14005103010307000032400c031003820b8a0300c002d01c000ca0788147d02c0081000418041ca5141e048883c4000b444680c1510f000b051043c5040448400c4484442d0106d07854819900e90a680e00e0b440400303641c4c80c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 740667482 1250 740666232 740666243
    0x1b0304150f030204140607030909050a090309050405043810050111010b090a09030903080705031c0504020d080703030e011e060f0305032b051f090b03120a0311070609 73
    0xa281c0301110079001e034020382c00b41000c3c6072000066614a41005005080014028604240c00715503e10700c0030f003100d50075074040b01c2c01c9496101f85824542c2048652000700710039a010003061030240c0719400c0c007404c4000f06c02c2618a406000d441280102c00c283e03052030054034039880c2c1505000781e0480300b1006611440380404c040444d4068540c2d410700c20542055405001e0390400d07038035003070345400400507050114288100d2210110100304100040d102c9648120003c6541e001d4101903d01085001410303d00890b003403100b0000182c0b151007210340c1c0b11fa8030072100ea0700c6003040e142c15405044010300b00c4030190319100c16150700c10380e105010162081e004004004643c1c80700f0540070051201d0102038241d0b4030811500c074040d643c0c0131520039202220310018016441c3c81c5514400d81d1800e0300c904075a602c80e54859240d138400b807c01140284040941005000c0c01d19010030b80740c002d06c543d11440079002141a00724280640c01011201110802d240e94810340e520b040310081c0214081620b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 740668732 1250 740667482 740667497
    0x51003080d15120b040308060324060301050f011401350103020a0602010204060206012912010e0f01120b070905030d090e0a0c02120a0309060606030203090615060f1b030415 76
    0xd8100c3e01640503019190810807028155031a501e05403400a80a040681c241c030904581144c04407036001c1001c5042c0100c1c41c5080c10342414000c040c2928800f4103c0d402c41d00e614001041202074a6101d40f000c1319003030802914083d40999411001126030541024451840e41c00e03030081e0862044103030580c2e00c21154017050648030303071089080380030702c0c0106000740e4002c20051209003110043c4241c114002c100c0a6850440f200c5041c100b07812102011040c0c0b44e03140c005100001454079561391181c02614005c40f590714011018801c00c0058202074181e40581c000300300c99034403c5410401403c0c0c00b404071105010081c1006240b4045c500c0f0b900c14002d032402c00304d034070841980144818160203030f0041c00300b20030740080402c1c10740c441c8101e403050690300c00d00f031000100c003401707034900410450f100140c41e40b4041000c1400c000c4018a04bc440342514400c5145a586520607a41c040541c2001d680d02c03a2190780c1040c103c0c5451080da108548000b15001901c0c0341a85425409600c0d26a149027 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 740669982 1250 740668732 740668739
    0xd032706020307080c0316032408030c070605091e0414090a14010c090315060f06030207050c01020109120c05010612060207030f08060d0f06241703040513051003080d15 74
    0x100d00060b10002840030002643d00a5031b0710940050580c841d403130703903031400c880a00089c40e5841c980d035620440d070b00d410115010112800510909006100c5810058078181002c40000c407403200072000c1e4015850300c6501140a900c85038044c54482041100350301c29810804d4800f60346c0e6280a40c200c841c2c0c0740c9025030450100c4107014040c0321104070344864a502d41541d58040410f40040074501d00306039180e10001d044021107008a008049a88005a2382c0301c0b5414113a007001b0071801e106055a0601904200007042d041c035810900a8504d0021003000c2c035881d10b980582107591080d0351341d4082c0741094040c4031141d4002c0c1074583c4245ca9001c0019100902510700036011500740d80d200c8000c0c50400081054429413480c4644608000215045507120042c0074205450030340b07945540c40102880b100d05282003008000300c00c00001d50805241200203003401c0300440748102c041d034a41000c04e0100c071402c10404017075a40319400e1030b214100341e003000004100382d04508031000722288000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 740671232 1250 740669982 740670001
    0xa030b27100c1803030c020d080325261009020d02030109060e041527030c0213020921030c0a0803040b060402091003150b12040b06060c0d03270602030708 68
    0x1004603403c0c0d6202c2c24100c034035545058940800c5280c080e40c001d04040200303000180054021481003410118005102c3e00101c10007860842039086003050001303d054400825449168401c0f0f100ca402c0d2140d44250746000380076601041d998016490b07203002003055107115a042c0c000e1030598500c0d0600300600d82d6904e1800718411000d85000c0c1a2100482c0c51800c4080b180d0000c65100c040745003c140d00190120a08600c0580088290000b8112040e80070461901489410410b142c5032415030a1501240024604034401e12501c80b8050203041803500c280700c03d000745c480d20000b0205070703090920f4a041c2050180d20842d0221100920080082c0da40c4c072b441d01c242d4041d400c0107855010402c0404d2020760040c03040c0b000039031000740e104400241740c081600040186039000d0020034082c2c02c2c02e1030f220380740d01c0024010a200d48402d028816a80e040040d10f1001c211041c50080740a1306041080c802c0c2c1d034050301444e07408110103d00c2d1340c01d001554000314010340b011799503107503a42e0340c00c0800d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 740672482 1250 740671232 740671247
    0x9010f110a050919080105181606180e0108030304060f1a0f040f0c030903031802240408160608100b031305070902070b060312090a030b27100c 63
    0x22112180d0140580c0000e24801d6014006505020b000303820602070070b080d8071035007201c40e0b8041181a0b4403103041080040c401d100c1880328640074002007000b01a04500c00d600350070140501010414504c0d40700c000d841d030040000000f0300d034650fa40d044558480703041d1601c2c0da0003140c050751a0b034101201c1c1c40d03a80f01e192191251481e2580000c0c030500031901c00f0462418280350700c06070b0042d142c51000000c609a40705030180e5000c15100003484c1c0c104c0c1e10b405019074614070880820f08082c013500b2409a200c2c100c6000e258500840041407034494065142d200d03000d0f541183c8003501c280710b40e0824181a5003000019243c1c5903d81103010b6a5542d8041c1102e504d60149081c441003e201107009101c50154580085105409035070381c2c0b6440380085800c170b0b0496074050b0341012210b001d00c049400c0920000c0304500c25035048618010140b808a64980080d210082c21030790740c140060000800b0001c500c044a009041505105c080c000380990394290244114644519144130b128003079025040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 740673732 1250 740672482 740672501
    0xc180303070206190f02030a0509040509010e0607200303130b06060409090f0212010b030a0314040b030a0605120303041a040f1a070305070306240e0d0b04050d1d040506060d020a0809010f 82
    0x80d0542b501d1508020300000c0c01014140441355074890744010a280b0013885000e214884130358a004c0076800c6600b0364200301c09280c40c5114a07410400510003418004e00d2148200e582101400c481c40e1501e5022030320a1047d580041c442c80e150400381400c0241a14507040035034021203215241c40c942c25406d80c00c8601400c3e07010352560200c040000040d004421000074600040c89603800c19589040100d0541d00450722002c07540c0d42c50a05000524001605001c0c11004000039400e5117040c2d83c9071202441004400f280b00640400007900300140c005803810025803080c01c4c0004280700b40d0005241d4074050b9040d10100b4203010000e80c00e148244920407c031940144402c415407a040e10716210ba1101030008420081c03130280900701d5031144004406c6161180030b003220306180506149003080030cc00362610422248448400398425101e003c560030000449002500f5203074180040c0840c49114290609140045400004250004407032131059050030024004400e040c186c00f41150300d41e25 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 740674982 1250 740673732 740673737
    0x60b0607120504032f09060102010608010e1c050901020a080d06150e040c08060102151005060705250501050d020c010e1f0605120d05030a0e0307080301090f050c180303070206190f02030a 82
    0x7007405c1c061030403032001c6030000018000010003540b203444480c203662000000648bc0c0e4028000180c182140e44561498020301c1d1400302d042425040c0000d485807458a000380a0300c2020501c414401200d80c000f10003408a500790030000c00754140c02500c40e0014110300c0b48102c3c940140c0006150040180d1442088142d02502043c3c010000040c003915021307181e2000040060400306640d16907000070504580644000e080715400154044808140f0800c0c01c01d011041c01c00c100002e90704042669540e442c0080050f0315451107640c12801081e05280c920700c0c500c16101950300281441510f102150b41980307044c06181d4565003480f943c1d41c02c1c141c481c2c0311703a0b00007280010700714800d202440d04050411400304031403d12118407072440d00605415580307250004010403517010940714682811540010900503440c10310440200c0303005140e045032400c0c01614451000d55002e00844c5d107410350080106441c1c081c0b41d082d90140720b0400c0000408200306008201501d800042680e81c541c0c4942e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 740676232 1250 740674982 740675063
    0xc030509210a1e0806031006050d02120c0a03030908010b04020304050307110d12090905130302120306150403061d030f030406180b070e01020c040c080103060b060712050403 76
    0xa404520680d202d041194100080542030102015040c0580d0754004103582e02d603080c0741805001c25041004010221040c945000c00400064441020106030380340c0403203101400d906d400b490b590074010085500c903803200c80501c01104040e00f00b0362500c15078001d54000c2042d010400280405ca203c1560094080d500078004800001c1c0b01d0600070080c03200290004003091200d0b51203c482d160f5040004010a852503010f00852403503205507030b8065581420903800c503080782c6001e921040c2c514400100031400100060081c0c4594550401590170096103a82c1c4503035030f0500744020082c500303d0500400e0144401010360000006581c0200c090039025495900c1c0c0e542d0707040080030f0791040b01c0c0d819034200840c0000700c4d00c6000d01c1845800d850321184202d100a4000a05058048400302d1146203010240800307654000326250549911520000e0151102800a4607074000c11200524000c0d002d8100e075102039110340038104072072041031072190000c00039000c141200d00500f545481003018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 740677482 1250 740676232 740676283
    0x5061303111513050718050717010b030406051021060b09060618040b090c0a2703060f090503071a01230409060f051003020f091e07180303030c030509 66
    0x441d40030b4400c0d40d128100f15210f9590303912001c074401c0c500800c242859076450041200300d503044049d800c40b86030186649000c1e503050801c0304009000140028001c0b03a919000901c5100030010403502500051805429469081c007000741d10807440c80b01290f440b0b0400250b5641030405d01106400b842c0014281030901ca01150030b1100040c1d00c1000725802925100440380b151112400c01d809041c1340c4600c2503669401d940094486110040c05032800310300c6041080281d2100781912080d613604c00c00120f40e40d805005250701400c0342400180c0540800a001800c00141d4039540034189443c0c81103031101d0ba0381d454040d804103001982350204801d00002c14100d480c141c0c1c004050144076500016800c4200c41040080703400465110060f4610f04000344203526044600c0310681c042201d41d01000e2824604006000c803242d42c88522054003100843c00c428000c803e001a8800200702d8203881715504d0038010068050300345144c010a24210104109200100d030100c0780000300144015545034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 740678732 1250 740677482 740677501
    0x8010512070302040203010f030618080a1d061902210906070302011415041d0c09060604090e031314010e011202042103080921070c03050613031115 65
    0xc452103100840c022030001000507a03461001d14082e08c01445c03060b4070350382146001e81c02c0380e614201c0c003881d40700d08c2080c0c0343c0000d9001080ba4450701c410b1601081c03444070114850502d010300c1003841c2d88100007140440b071003d40c4c3d0101c4607401c01540d00b16003400761100e582c2c4100715860a00c40c2c211034020000c0b1a09030070071500602e5032507c03910000074800c180d0301c1c0603109000281c0390300a012506611400c602c4c5050b02851080c140403100205010380c401c1c800782e507034040b101e058034003650010000400c16918003050300e0041400c0081841902555000030340c0300ea0041400c03100d400d008a03000303d005900a0a80d804411041c5c4444024582070401034400c89480108404a00c1d0200800b05100030b4000322200802500d40100e10340690a00e00a0841d103c0100903c6056000040005660920502c2d2038118107260520564038426414442145c040b242c1010380544650f074103101702c1010001400040b58007030303680c00f442001880481038036840d14000b02d1902c01e6260011440049 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 740679982 1250 740678732 740678749
    0x1141015050c030a020a1b0f0e2206020d1b051209030405030f0c040c05031e070c023303160e0319230a02060f090103240f0e0601080105 60
    0x200d46003422420111010003481c510740c0325072600310068003c10004010040607070790480081c48600b500c001030a0500042a401036940d11030f49844030300071004115583c501000c0048994890b418940da940042e040c02c502030f5100040903084149420140c44103840d0782c1c0e084144e60101e580e90245080640505540f00620103022040340c0e01042200250540e030130001110341e01000000f034860f0b06680c42c20401100c40100b400c41c10700404000b00070b540302c05088402038100445503500302a03211281e0071901c2143d01c020003900152060803805140300700c04615010000714a161300100c0c0000041b0080a00054440c2100c0c94541044080d05500800c410640801b01a045928040340080b1849101d0510682603070340c0011580c407486082e40741142c0c2e4020b003a940d402080300000300d40c0899664803450306201e9115a0120300e03001160720a4000140750310180442c9207003500d9015502040c3e03001c5114900700b203c000d80c40010740c0761041e05114400c1074161200750942e8030340410b10100a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 740681232 1250 740679982 740680019
    0x7030c03120b030304081605100912030c0209010b19020c0a09090302030c0607050306090a0204030c1401030e073b2a040e0a0b091017010f02070f0203011410 69
    0x981c076451805aa43c400300042c1c4010190b040003050704400f0440d03d50310011054100c2ca006c0c0c05001249800385402c004070b042240d601d4070396a07188804501741114048440c0c00c0007940004000000108502d81c44040c0c0165042c002a21840c02000c107001d80c0c1d6480032019091f080010703504108100049940444846802401504d1034400340300302d00d90428504891350300104001205115080c142103143e144d01c100100c400b10718041c11500c03040300419052180c9900c40540b01240003c07644603800000c01c009084c8204c030111600c5d22075000603d0002403080342c440140c1a40c1c980c0305554072165075075003000d1440840043e2500d05404c0d4000d02040600802996904288174061008000030802001c0381580040170707040001c1001c060383d001443d981d124040b075100703001d006840300e6030100494004811007849144041001405031220441e002507291003c50308409006001a41140c0d15108900800260407000c420681032402a5112503542c0d8014009020b0390070300d12003070041c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 740682482 1250 740681232 740681267
    0x200c03040b031003030e100903060f1d211215060c030304050606010206100b19030b03120d05010503030f03010e0c040e010b0d0c051c1e180b06030307030c03 69
    0x900e601c41c54505455030069581145814110904105050788110000c0305542c0c2140c2414000b4081c007001805800b080c00050840c1c1d54409920f00601d810303602c24014503d01c4550007107813400b002e90060b168441a138180c0e1400500003242882c09441d44200d5207400340e840104141d41c1c40d80c81210320070101005441d50021020405080c0c0340e10100040c61040d40300d50020b104a281940009080a9000c1c02c0b041c4407401480c4180f1114010205481c100e4004a0311907845a240310002c50150003c1e20020b034140c0511071401355950185001810280600301060145903651402e041e03aa00c82d4514044402e5410300041c814005402503803038010301000e1040741003030f0302d801d540c0481c8038082e40007509050000410741c01c40042805040258402e90600d0b50400300074041d03403c9500c2c2403808c84e400b100e035202c0510110883c1140b940845241c4030104014070840b040c0f88100c070218501050703940c0d441120004401d8600001195102503140d968000e10f00c0b8940d80a03608080a008404031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 740683732 1250 740682482 740682487
    0x140f03041418040c090c0f0e0409170a020d53070305040228060c0206070c0e04050717030405040b210d030b0108010302030c01051e0a0e13200c03 64
    0x7a40ca4110801c0d0240f401585102e1360b60385070003801c00460320000084e07070a000f0110001d11081d50030141c511a1158243c5011904034002d1500030000211850f6003940c0040101c0c0d2014030039800544d2280700700081d01d540341042c080d140719001d011004512040d000025810300300800010310400c140030026008030360350115140044140d1745904030f4250ac0080d5640701080154a8040c40d0442d0384c14800481041c0303024100d014042c903170600d00800040c050f038103070030b80c0031522100c00302c804141e0084010000c0300e841700d100e950144010f03201660240309003800031900542041102070546040801145414503040c18000540703007643d041ca602944200323044003051012401c101000b8580c0004d03003107110204101408883e01100d00030f0400030a14010300c0141c900040001e4094000d0070001c2c3c032246202e406104242c2101045441c0482c04124000a0b44d00115007802009044035004085403401c21340c0801c4420400904c6c8400c102140381c0301c01401d1240c024026059810b00707907407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 740684982 1250 740683732 740683759
    0x15030e0f030f030601030c0e0d021c1a06010e010801081b010309021f110f06061e1c020411030f15030c151c020901050703030525020a140f030414 64
    0x5095410442540741030b04400010440b0355a41849990b80020a07800c16882c28009040458590489001c001780101191032008602031550b0b1001150980e0000740d002004a8000c040100e0320b006640b0113000c03948111300c9003d958003818042c1d0595a411000706441300d00206240c42c0414a503428506140d0f4644030000561a001035548480000400c0c4440700c10789248001d04c2e045201c61198041d0304030b6140c0f05520640854201d420180440795441180b19038074110281c90040345809034440d10361846412003078105444071040394002c881c00c201209005c0110461448120360031002d40a081000612501749015000c40a407800340859940500e01e00c04942d00b0504442054612702000c02c0303411444502003690107412400030021b43c10440ca90700080c20343d0040344001418542c4035000079003920000c15011103104507509603800908070960b4043e440b0607940c0e00c199083d0080707a410041d0b41000240d80e480b01003004000314a0140381c944414104503080c1400d99109142d8610744 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 740686232 1250 740684982 740685013
    0x90203010e1006030e070b1c0213060f08040b010605071b2304060e071202090405010e06040e1501061d030a080903150402131a0907110d050415030e 65
    0x5501814458100110a00b0001501c4180d101d05600001c00c241c106000e0011442c1301148aa080707502406082c1e448020f0480c5c0780110308081c4000a0b0035a1010031644d02401805c0c3c07480007112007a80b5405241f600844007100d60510854020704004400401004128407980080203500d0241c1014080990407175030b02800c0790001d61048859032202c41d403034a40d660300317074407030348450312040ba0100b150130b15044d440302108000800000502030900038600c0d0003411501154502c95000741304100039a1904042c02c4d917030605855981c0510b1600c0048446001c00050444680c207104038000d002d6881e000d411950100c100a07601c000c0b103030140071003c1544041060b0307090240b2410400e0380322414901454604074000d1202ca1001d000c0c00103200158540302194101200e0400340400c0c07c1c40300d840d9007600c80b442049075682020010040003001c81e40101780d851078804d4401502d4085400d4642200c1c41e0190b406881e25140388032040c401624013907480380c260540031100765404901842d402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 740687482 1250 740686232 740686237
    0x30c061b0806030d02061005040903020a051006140d0341070201020105090d0806041d030a0306090b0303070215030406060503190b070c0305071202210702030c0303030c220902 77
    0x34001086003001401034525050149240fa09610b1000b041e4900d0030418100c510a020b02c1290300517640e5400480502d4400d1107401d820a8000782220403901c85001c140006104a100d6403050b85c5d00e0312141820f910348400303000840c0e034059940302400e000c0b0340724601e0050740d2821564906074000c0c0003510300310000c0b02d403803240c5080f410400e1344030b8000d40006801d40d00018524905900206181040c1c00e411841458000c01e040e01d000400c00c0784012040c0d0804114106041d640c4400f00d8a0121180c1c150407040640d0710828007400220360b0002407541d80e0241d807000075800382003c002c0c03110f0280c01c94065607101d8041e1501241c002e6071b03140807905004034603812504091540011405000c20325042c0c50f00034000f450300f034445d0111601c004050307000714040127294295000044901078403c02c130030940226554008400401c83d0100c40c9003541c0f10800403402401000f040c0c1e1170340c1c46c3c04400da070b00c1440c0350743c035152402d03116801007a0a0f09280c0c001171921900c094010500c400d85102 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 740688732 1250 740687482 740687531
    0x70305030f1f060c1a010312120207141c030506060f0f040b030903070b1303090b0703030f0e0f010f051005190801020d0f05130c18110a021c080f04030c06 68
    0x1920304d1808401e00f020b00d0903505e407861000540100000400004040c92010700c0d9021b0645131200240c030b11100b001c006407192110240284198500000e04039030b0104040040084865528250b010706c0c075019000d0328800c0703e246030703c56420f00101452080c130780000c116202501260038a0b04e40c45171f44c1e1206c150030540780e0f520980c2c00403600b4420002142c5080b03401c02103c40810b0046151950002d00c1510140a014071800b07020407072008040c02908203490b0170381034038010b1080342c0b0507000756543c1d00e81001c00c9234255030800005d802100128803035507000d961011451018142000140800300713100b1213103500354407100e050015140320b013803000d000d00c61000c40d00843d50300c5000d65a10281d401c06402405c4541d40c2c2081c60b8006000c114005c0304651645d840e80031141100c20b5a90003c20a188018010300c50004000100d16400701e240318003c101e11140341281c1081d40821200140119031171034800c801c640224000c0713806a00f0a01002d4030402c1c0208034441100140e01440d03280d800d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 740689982 1250 740688732 740688737
    0x5030301180209060d090f170c01150503120a05041802030f06031507030b120709050f100f0603020d02090402220801090f020904050c030f06071202070305030f1f06 72
    0x20041c04805040c040401c040da850050039414140c8000c00686188241456081c20a40d2241c80e0380c00c00120450004445030040e2a032101c000d5801921b2401b6841144090281c1d4a0840718404c01d2890030100c00c1520406401001c4042040c030818845920220080713060000611001450003650b00c409540d10f41002805602c81c1000c0c1c1080d42a0040504824860303044080e001c4000304001e940c444e0700032000c0c900452007500304000718000002260b040d2010340100280412030883c0c82c7c100c41e0180841102c20314003a0307a11000e00c40864564022855404403600040060703a100303801500f280154180c00514080c0e07403a0000c1c0803a440441c2020680d4004601a44840c50110175040100041402071041c0040d40d903641144d000d581c20024450118100030405000040200c00b08601c0c01170308482c0003501e141c0000d961035004440c503000242e1601243d804801c118003c3d00c0d000c40c1d0544a850450b25940d8025006230300041c900055990300603c0400c00200154603040101080e8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 740691232 1250 740689982 740689987
    0x312050a030f0b010f030504060e0a051606080f0112060605100e090c0301060927050705070507060203090d080a1e0c0303050f06090c0d0b0a03200102010c050d02070309080601030503 80
    0x10310240c180c030490403050000c546844800446640c00c01080c642c1c0312200d06e1300080d40e50b1a4a000402411020b00302485403013100403100c2000f400050f0240c82c1503078076032000001070350358608a484142c200d0b00e00e11085520801000b54650060740000c0d160300c40c01000c034010746c40f80301058000e6003840702c0e000000d072085140c3c2d1a0307003014181140c120000900c15031456042513005003001c0aa4801e001b11402c800800a41a01030401080c4e50303014035240c24081410007801c01807550708058401e4a060003078840008003180008211000040050309070304003441c26841d004510341001e049a810f12125134140011010416a0540008040d45030003404115504004044980082510010000030320602000303176071389180150b01c240c0b01100d460b40d0708920201c51020304103138807580b80c000031815804402c000441c104819039000720b4550f00e5600644400484c02e0702c81c21141e10002c981b0801041b10840d040e1303001040c10a009082c800d81481d920118545048003d07070003504c160304007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 740692482 1250 740691232 740691247
    0x6050307120525080705090f0103090c0906030203071d07081f0e160e0607060203090a1506090c030203040c15091d0708060a0b120a0f0903120b03210304020a031205 72
    0x1500f0400c0e04030300140c6020000c41c82d10444c090030900c2544542c0e131082215190250880c0c1c4a90015003059501c1b40140345400c0e0740e1a040d10103007140780422403003401b580001040c030b04034401c1802441030460300a8186900c802c041a0b445460241c4005008060820044c0c1040e460302410f0004128000b498601ca2820100c105140c1c0481001c050802103001034140c0303140e0780e4406450b002a04080010703a01e896422a592900c401280001e0000c055a040c0c0d40c0503041551281e8201c4000400a1110714000e0101b10100e1204440041400211403030620a035001458689408180c07030400304059511420600c1c1c14a42d801c0c1601603003066038041010456000c0071031a00200107480a085050074082101e141d40940c040009403404074400140c012140743d04030344030204070414100300054450030014000006d040303d4200803070070f00c1500c00090a0008101040751101c681154203250440901032860b0310160080c0c0e881000e40341d02002083d108a90041c0050050700c0b4140c0d9a4003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 740693732 1250 740692482 740692531
    0x60d050f06071e142101080102121018050402060904142203080c0f071509200a03020f03010b040231060e01030e0703150605090903070507060503071205 67
    0x2000c2030038503414860304450f41c42d03150b0010030f4501d2103400c14008070340f2903c6914900d84810f0b0b50320316600c80b900800c000012140c40650050001c0e1030107680041850380c410348800300301c8182c2d110300c0e5100595101031442d0030a285d801680c00510082c0114505101580024140c0c2c11211001003e0f40922061090000c040005120304d402d4502d0000304415507034802408a101c000c160301240900010580720040080c0c080300c12031548400800350100c0f5203800d10000b0300b4200300482e010301290311401050410b00e0000140344030028984954242180c3c00d210610420313808803501592109400c421541e03450000d0170103200480d030440200601242c0c3d241400c102042d0400c1c040a003900700341f00b403d92106110002c1d403000c1c02c0108400c4031101e09940303040861f90000d045a103001c10043c5903105039401c42800c48808540d04000c9442d1000d145880c1d10419070000c1c05640145000c0284078064405150f01070f4641c18841c0891284468080590701c040b40e40c3c46103c0074040c40c0248000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 740694982 1250 740693732 740693747
    0x2070b1818010b070f0606050a26210702012c0a0905060d060e0f070f1703040f0501141e0306010311031501081b0c0102030933060d050f0607 62
    0xc4005050740000d51501e101e11402d4840d084002c0c189030000c60b695014001180c00043c0103140107011407110a540b003102141c882200003c20b1003208074034458031082500029440000c0341a0b01c000228080411034902c4d065012003c200e06000c40d014040b696074105605103805140307a4036136411040c00407001c0004281094201c0c00307080b80303070206009031601c800c01040b00d40c0c0e40c03040c0b000409020607018949040c0c9a4414002c2600c5401c1c00414040607100790039003160010308002d204500f80c810703850380360f01540c011015405c040000c01c0201d0341c4158501c4000b03501c640b00041c9002c103400c207094100c4451078542500c04000005008484d40e1600c20500c44402c2c0321285070450030704c040344408030184410b10358108040d260204403203145d8106c14808140600303480e47d80d07409804400d14007175002295004058090307408030503258402e0201600384402180903c85c002c4030700c551030ba100c40d10050502c0fa0441034a4280200044041180342d20780141c0500814403458241001000203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 740696232 1250 740694982 740695009
    0xb060c15010b040b030c0304061103090a020a08071d060a030807060506010e01030204050619110d08090c03060f0a051e0c1c020c03071e1b031a06060403020f0102070b18 74
    0x2c08100402c10039245070200340ca1b0007682c1c1c010b40302d0707032625641401c102405681d4084000d0010000030302140340030000702a28030324070a8030140c4031140d88052490303c808583c818556941d0708225003c2400d0082e51304240d0002c4002d28580b81180c40c1c0e00e54800e250001d02003158140d950742c040c070040c0c0d070f0003006030041e9070340900c0c0c117628150510000c00c40c02c0c0030343e5031923803e51212441903443d0140246280c007180c0c00e0020440b0b513048541c2e900148900400d54100300d40e406808002242420081202d0344544e104a20b03400168a504070040000d040050610f240c501a03100d1516403e1074000265010301c3c5c1c80e581113a200c840c5003070111072101c900d1402e446500d10402c01c000d245031003c8140d071540c13900180f03001080d195070b0202086178400148014952045140740c002d4441141c180c0f0703c01d881c080c1c41c4c0301100c440d02c4410f107820444140c403000d0307100f402408204014504200d4400341d0301e4041c81680c3c41d40e5a9924000066040310743d03101c6140d10354605c8800ca5051849080507603 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 740697482 1250 740696232 740696249
    0x81005040504020117060f060d1406030f070e10081605010e01020a030e0411070209070c0b0a150314160801050105030d0c1211070803030109140f06031f0b060c1501 72
    0x440c1043d0340080c01d1184886072151945450a000800c240d848042ea440000b80180040342d69103190b602c4000103083d50503051807c0e0b4001d03030204145081c0061078201600301d010042c245903042c40040399070ba20000740325180307980c40c101012800b44000d000310344404d00c07500d0607540d0703060a0400240504040c0100a811980100c8051001c03075801107100c5c000c098150780020b842c440035001650244100e0308080d40014152040c030142c2c0f0741c05440100c01e00e00941e1b04088030f1301c40050b60000d50b0113141c3c0110312110580014808980000740c2d003a0303a40c1110b001c03500c401c4d98100288201c040c19900c80d008995450004000c03506013070000c4001380c83c59140a040282107030f50340b8080050800003100410420490103080858100041005441c0c0701c030440352079682d40c0c0c0122000d480916100502864218041404040020822400703920014050208452884940d030880f00a000846c2d40c5c51b6220280107126458250040c11750150710805010480c0199002008078801a0701404030f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 740698732 1250 740697482 740697491
    0xc060a05010617070e01020f0115060f0908030a0e01110607020f063301170a0c030b0409050a02040b040b0a0326090a18140c030a05091b060d090b0708100504 69
    0x4000340340b070040d070b40a4005c0c1410320b481521000101c0c40e040d06c0c29200091036190950400030401070b40044021100a9a900348442002e5a01140c06882e144035050055000b44002c010075030042001c0050343d40c040c98000f1010500c003c0403490b1078000e40c0c114015030000c141c241d507503103c1800500d074800c042044966803c001c1189901201c410103002c100034403a41c010389480c0ea84200b20a18a0030f1141742600900d00b0480500b800410b80c0740300070340100b4a00200d1134000d040c540141c1c2281c0d07800c90090248548507409202c041c05404c2040c503845551418000c6840d0340c2e0740028800b0350f0107581c03004040801c11928a0303503005103403101101c440c42800021a188d4400c40c1503029200030b07010500084010361009400360100c4038112082508290801c41c510380d02d41c000c1d52050003c0c170420302190311100001038071070820101c0342c4143d01e2100c01200f01810502c00030204001407840c00200d520164070340b22843c00c030a5817a0702c0000c5480080c0841002481e18101c00340400711030811 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 740699982 1250 740698732 740698757
    0x70c0902030606091509030304260a0f021c0c06030c030506030a020901030f0303060305100506010e0a0e0a15170f1c020d0309050f0a110a08161214030c060a050106 72
    0xc1d10f40c09948802d030b214004a0503030000140d001015a0302800000e4201c9072100e460b8100884041400c10b001c045c041d01020000c00da0160006010100d19040180355041680503001c0c000e841c60381c10341940c0642d20004074000010790b07250042000b4401c2c1e5030300140e2507440321001000d0710005003140c1d11a40c4034400040141e0b81d8071798110f0440380c0c000360f036a50301500c524050f40580308660003e07196014504035160106e40700d821461280009aa596880500740070400107610864042c41d02d50181000000d903051445900ca05500b030584006840b85a503100160702c14819414040780c529040120120030079042000040b2490080070381220244201e0900259240100300060b0b040685501c0c540c424018103101e0f40d40d00e460b0080c181e5448001504100b9210340001d14000d005126520f0000703401d05020500b00b01025100500784103607850700450a1020130641c10030350301c1c20f03180304c50000088020001400d440b5151005011a4544220b1440440c1e005034050740601900f00e00d0708 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 740701232 1250 740699982 740699989
    0x1009050c19092c0105010c051e07030b060301090c050103051b071b0b0316030c0e0904110102060a0209060d0e01060b1605010c030c021005220507140d05070303110307021302070c09020306 82
    0x8134151030083c40e1441901c409414007515040c49118907900079100f81c1c0d80322120b0380300400d100b01600c1c0980c8900d504c684460342803601b203130107400d0068920095610148010340c880d07008a07401c02d9001d0305140c10044000038440d000c0e442684119651540380480351540c5403039034128802004000b03484e03400e5103400921348001c1c1c901c0321071500800d90f407119580b100c0d900071403144031040000b030034a1141b4900ba2612010f12641c4005031030140c499880055484042c82c02110074009001d02001d0602c00d280c0d1240c0d018198010342c480065480310000b00301182180060460742d214034444901c0c0d040d060400e0342c00c44009a00507000c05003441d1041c0c0145400051000d9a017a00480008541c0d942c141c01440d2829608101c042980541f043c0d00c01384180042c1c1a8240d6800385080c42d840b40c042001c10100c2d8459a90040c41600000810004070340a24840f000c03000301a800c1e0b030324006403135000500000303800c251200f0843c2e01048140a0081500d0700e00054000c81008625605142000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 740702482 1250 740701232 740701319
    0x90203030304110a0b16110a050d0f02180c0414010206060907080615030705090301230f180a06060920040521190b0c031009050c1909 59
    0x1502c111108006510f050711a1155100100000700403240ca1308601288000308400003070054031340c0b1112003000c0c0080e1420580c02811914002c100d0300c0041d002e0794800c0e1035510054010380e07010101d0070300042c803003001088a0b84a894202c403075960303840c00d15550b21409944040010704561000c010003006803603520540d03401c40d485041500c02565501d001407035014000c010b50480c1107020090040b841d4100000d803412603001c80080c01200320820291400492032507603081e042514401007021083c1107a1000e8201c80c900320b000003448081c03c02903240c9a02e1010071a6070343d540b26810090070070703a0301c90310040031101d41c8000c0350309000100b1108a802103001d02031040358a0b1400d40042e0340c0005e5192000c1c0c65803000d039415042c80300c62405400c2e045030300139142c4501d07120020300446440011a4400c034050a0b0ba03000355410050100c0c01081300901c415802031082004035054251442491780200581c5d50742d0b00d54600309071b503050b01007c1120380c82c1d48410000c0000b00000148410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 740703732 1250 740702482 740702491
    0xc0e030f1f02030a150320090c0a0302220303050d0615090302060d061a0702041518090c0e0907060905010e03030f1e0c03040503070e04051504050313090506090108010902030303 78
    0x142c2c881d104d032070b0114002d10403800c614924083c10200007003017007810300e0540805011041f1507056507950900380a16000c0482e50503820300c01c200489010540071750301a055a094900450090740c8070f4445a40203400e050304194042240441c803520682000d000701000f0380203005d00051182101c99002c4e1125a442c00000d12a14001c104205d210324160b0051008103012640e07d42d000140c445250040c2d807000200ba4007941c00d00c9008207100d80007100102c21101820f0760304000c0c0314414100002045078281c121054014408000781412245240c54000d81080b0041c2c4005840c1c03d10180441c0c0881c1c0c0b03c0d40c184110140400b03101e86c0c2c0481981d24500d0000706a40d512054280046203480c0f1861461501c9a4085014450781c0c00000c050026141c080d811508546c0e10303102c210465880c12200241240e100c02c000310704441e0000c2101e5000b40c482c0c401c5906240800710083c240030074980005940d5907031002000014a401e4100314010300404008100b030007819000f00b52284070081 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 740704982 1250 740703732 740703793
    0x1060932010e060d06061215030308191d010e010623040509120a09030b010e0103080d0209031005070509010311070c0e130204021c0b01030b1e0409060c0e030f 70
    0x2102d90b65a110007040700c841d403511000810080307072a448007502d083d07030007907000c0c610518251800c405105181009410b8903050b8850300001d0ba5028641481541240003940c60980c4564071814011514117420407894070242c0040f55039964040c10740e003190b0556205290300d2403043c1103020405009244044000c0c0181c6020540c1c2d541c4112a602e0b0440c40ba102d6810b9410003d000c0102a60214500080c0d80c494a1f5001705030340da038034070241e246a0a020180652200f040b600fa0303110308660090080c0040038055552027074039296580c1c1190003c035441d10108100003500261582c1c1403107082140003010310158117000305070b1540380c0c00c40c245001d200d40d0740c01c1d8a00070031500310005a85450059005000703640d211080044c000300f1410403212400418144242800198083d0080e9018980050002c0034002d0040c10102c0440105000ea01c0c1c00941d12a1414040f40f4a4091442556070585580c0d4034145194107061420b001081c0400710f5800002c0902c0c00d000c07070514030103130040511 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 740706232 1250 740704982 740704997
    0x30a2427030207050a081f05061e010c051006090e0712021207080a1209080a2a1a0702030f0d1d010e03100c120e0a06230106093201 58
    0x14075090b840d061207034000f40c2d0300c00e40c44000020b40c070800003500580d0709070200807410415140c0c1c01301c0056440c149c0300140e209601c00c4a118003008126410303a44900c0514002800d4905515428100b4a4054001c40702d80e84a0006010522060140451b4a0034840040074014540b028200c480080311800034481c2c4031480680d00440342c20404580a40408070594141e840e50f03240511521102225002c0440c500c4a800506000c020030080945e0b5007048a18071072114180d8401811488036038a881140c03d58500840c0d00310100a20107030140c40c0421040e40c48806004062518602c1d8001008945c898440c00c0c0c10070b90f00010074820203000c041500c26600500f00180c0700ba0195088407a01441003050310001004140c22010351090f4680310030a13407482001e03000042d1130b20b0b103451080580c0908920340c0096801d920000070f001d09910102c43c840022030138801c060070283d1060000034010b00c0180803819540c0420003142582d0071031195100040c070700824850004084090520600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 740707482 1250 740706232 740706311
    0x312110703061808030f061e0102030919170a1704030f24020f0316090803040b0d0e01021b0114190221010909051e0712030e030a24 58
    0x80d2a940e04603039801868107850b480d00da440302c0c0f0811800c9511910810020a0b101b850402421500b84d900230180d01444c03815081d903040c08203d4405c541002142d5040440c00a01d45100101c1e00401e6504103015111003203080c10030142d41e400b250554101c50714100010000940c40c07015141403e50b010600b00408121041d8038940da00d8688454000b9500004462110240407401903220f01c800008074065001002421113215010303000313091550f031007000b0502050384084064283d111601102040340001520641d0980c5c02c44401066441c1200b2110001c1c4802030241d044500c030040c0c040440e519181040b0342d1144041148002e009500040b11003081c1c001003415022140d50f400e0100507540d40b10341040080000541c156201c1c021002c24525500d00541c018411800e00da00601c100b03410910110004180303600f0440a0003420aa8035411751030510110300d51500034140c80c0c0c050356020a41d4014105640f070900030041c5080c0b03031805515100c0014882c401104160032140108 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 740708732 1250 740707482 740707511
    0x1512070c050a050a06051e15130b0a0801050f01150c0201050d1805062a03060108060109031703010e0901020c073f02010225060c06091b031211070306 66
    0xc102e50040c1c41c0c0d0145842402c2441450b03007205010384204007100340504048915072498600a0b0707041d01001c1590003002ca40340c50310502031841d400b200840082c89480e81d000250280491b80c0c44081665143c404103c0d59010503040c2500429030041c00032405214110000c1c4504003044000b8140400401c868414a89076440451140f01d20f44104007604040d0408940d100703011103044084142201241e44102d400a40302489103032440c03041811600e4880054840d1400100400e04204c0840000804115020140d44d808a400300202c1d5882d41400c54080d1407280007841229140c1c0100030500c203c4400203500c0301140e02c03412041c25081542603604040f00300000303040700209a8500c00c00b0465a000c0144001903200740c080715900020548680000518807188100500d801c0743d04100242c0104403203026140329210000b80100e00d42e0359440c030f400d4a000e800011101e05001401085410501c01240c1302075400c040c940b11204500310380e41e80409002c01007141c3d031102d22801c0300c0b10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 740709982 1250 740708732 740708743
    0x12f03190c170a06030218070e1503011a0c0616020102300105010905060403030c020301020d0c0201051e090309040e07050a27060b04060804050a120903021512070c05 73
    0x1500000a110101c50660000e1420340a100c0d039506291a400c0868021081441264122030f4003401030300170105c0000750040315400007001d5000380011604205104c0e5035820000d01407a5807036036059143d5040c001c0314036010080518884c1802004c00c1211100d1400090b81035020915440c884d10280045500700d0190044112101c01c41120007580640100320401e40d440002c5c5614803207169a9076280115903140e403a108064014008000c18000709100c0c1002205860002d8009407038105c80081040403100130844140040c0d5648083c000000c1d841c0780009102c5102068100441c200141060748138402d1b030100601c1613130b94041880300510180075280003418000c0101200c6540d070101000c892100744181c94522401a02c0e40444070602d21456040c1c5030121100d5050a08141090700c03201ca0140c01a0707140c0c42810389003070004041820240510403035588985466146205010002d02c01c0120010500d9084c0b088507c61aa2004074039804801849c09010025590a0660030403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 740711232 1250 740709982 740710021
    0x717060f090a0f050a0b0f1201060f030b16110601260f0106080d05040602070b07031701091b0203030f0c07020d060501140a0e0402011d04020904050117012f03 70
    0x400c81104001071030310154402107858034031003001c2c13041e5a2400313010340882d440c00340310175401101d5203103003135650130203001400c40b140e4550b000260050319550303201c1c41d2060640c011100b05008a0030044142112090340110090300c2c2000b01362030000c80c2d01551255414015076200b01580741072078a149a120407003241031720b071103001c0d503041040030010980a40001d005419861040e01c03800c88030326125904031002c41c0c0725030740070301411410300e105440294004002a003c000200e07100c01b02c1c404075009030300e000740304582d000168680c04030321202e108507420845a05542042c4104400c081084030100c0e4440103e824113a0f60701e0b807510024400c02342000d4040c008910708000414900150034880c3c0c005401140c0c8200240d0360380c400d1441100c400c0303500a00003640040c5006601360702d09011001c1d408010000750601c051003003c20100c400c244d000301209100c2200e0944041020301c100d01d8405000b100000030302c4040b0043c281c0c07124a000c40c07041072100010000d000c80a543d026409003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 740712482 1250 740711232 740711239
    0x3120509150c03092d1c080f2a010b010507051e030f0403050120270114130e0a050105010f351b1312020616150c03050717060f 56
    0x40010885c10850000c50854040d2a40200890b4000061404424049400c09001c1c01d005503076002d903a5500990700300b00b89060340c000d418402540b41c00c2401a11030103403100904603035000d20340d500c0319900b075a480f0480303a810302004010b5400491408901a6584440348580a215002048000b8618422101c60000081020401004120064000342c00340500305411158541941884c1c0c0074a20521620807508010a44030340c0d03040d206104080c0e02c600e014103108203100e56490441000743c0c06024000c0d405900343d0420302c4011154141c0c5500581c00c850100015810040041c2c0344441c01e503041e030103002c0c404030b02c0101290b03450712004110000e0540300c44040040908120148415503501c204500c1c030302580f03c1443c00c1c480030b89448800d002ca9102c4058035104070740101e2a8103d034182d0b002082080010100340f0341920f0840d8841c4034401030194184207003807000031a44024800c400701800c2000b405040ca40c400c40c2e011138203c031000c0304005500c540700014100d0182503e540e80 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 740713732 1250 740712482 740712499
    0x90809060c102a0f020c03010606050c010e01090201050f030a02070828031b0e03070b030c2101030308011809150f0605090402130c0207081603120509150c0309 70
    0x84030740c0045900eaa140c006510140940a9050709185500121407a100c0000b00c08004807200300d0311412090384066124016580e4104560012a00b501d0b0190401400300d0000200c1e401c45039000d1103540742c3c1c2c0642e840200480806980008c0040c425500c070305119140100200c0c2101515904070b5854a50210300c890391130004a9000c004410103c01c070030f2342c1c4a60409141c415502902812030406200c160b1030086103200502a10a0911109000d070148110f8101041c01d500c1d00d0000c5000303105541a0b9a00d50701080c101000c50345003041c1d0310081c600e00780010400240c0007014a0f06685041c0200c0041031030000c409401001390002c064050034107003c15400c0c081541c1e01004145c0740c2002c041c08441e80351400d000178071a0660300290000303d600d9400102c007641d0b5018000c407012500c15031309445d9aa5107011300d042109480e1030860003241c24100308104046070990100b0045090550525400341c0000c1d012940c0c3c40b000030408a0006840001c800c0280200c42114900400450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 740714982 1250 740713732 740713747
    0x61602031603021506180420041514060a020d050a03110a03240305030304081803070602070f0905060105030402040e03090d06050a0609110f07020a0e0108160e070c0609080906 77
    0xc0d642e449011415519013240b0340880e15a04040141c2c00c8103684ca4501000aa155603842e45030380600c1000c0411210303424044a140d41d81e03540142141e04845c0980703c408c032810940c18003a035a039505400c510820f41005118003194010409803411030072428100d442da104424140d0140000c0400c010020800041c81110b030764155220100c07121002826030030300c2400800c00f04082010740000f4225074000d00008000400c500d0082020340748039012560305540703d101013880e0964940001016810105042c400d600b0003c1c84030008000c804006c4c001414101e001030050310000e00b020307001c0c0782c50311049807911030204100c0311020030207021408840510b09248000300000d80b080d92100381020800a0407e8031805500780d04001c0e018803a03d00041d410070248164017401c8203e820040042001511203c049441802404a480680f1509039030180308501503071642c00114280f0f842e4000d100a040d4003030f461441d9103034004030000d0300c02c000781071001a500031442420b40c000c03000030712103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 740716232 1250 740714982 740714987
    0x6050c090405190b010212220302030706020709050a05070c0201052116021c1b06060509040b071b0c0504020703030f0504030c05070803030601120903030e01090501060f17061602031603 81
    0x601e07070200300d080400c013100c41000126140d0040c01c59244c40040c0500484880360207a43c3c01d048a280c2001010100564a0380481c0c00c00c4e51690015000d608240390030046641075004003603208500782020085071a20300005000c40300c5c009400781c1040400f00302078510208089035a03000f80c015034159481c902d00358410340f502881540b0804018002d0f03802e45440440c0001031410128000c0d101c81c035415500e07581d40c03410860201ca0507240262203220028103602d071407140c030f40900c1c0100440480c40c039203224046c000500008101c00d07284202458840800c0c100301c103020030b0301c10031280035a43c0c0909084c12005081c03601101e05405160006210030149c110040003021446081a100c41e00c0c1c0d28405903450380403c840b0350b03012595007041c10000003003035801010441e1180c14002008800072200a08640c002001115903a40d220030a1000980b86d6590100602c400c9415402c90707410307850302e662118800b610341441130344540c1c41091075a00a0081d00d403010b0242c1030040c01550340d030500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 740717482 1250 740716232 740716261
    0x10e010603060b03070e010e0a05100f0b0301030c080d08010501050d0204051507050d050408030a1b08030a0902040b06040303050706020c0106030203060a06090f02030411010c05030d020c07151b06050c090405 91
    0x550b00c240700714000000c202001d070b81c05904840c611301e80452250755006189c1c024240040c4001c049051644000c03480301450307036105000e030050b070b00490740325815860b110421034820b802c060660b51000c400041c80a174880344d0f01d0305480081c03030056140c540984040001c0e0043e5048290f0001c2e2407420340d1410890344002d010341031300800484001808400e4107a5407440356014081d201d4004115580a8500440e070505070402d0300701c1407004403400303038903030724982e410039540c081065445400740420352820707000b40c0c114a502145c01c40d00d000e181d0740e005801c51194000081c00c00d03401054050041d0b2081d480b6600458000e130554106141c00d1104030300810460040104140c6840c250215000c2d45100352481282e00503c04000030b003800c8010b61300d50382e4040c000c07503840c0302c20051603c2c4c00015001800c0554043d400810006080401d41142003086100c0c0c001085207039603040c00d15007000501c1844e1139801800005640e1034403c01e1b41c41c64803070350100c00c2e04181030109000c00e01a4000380c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 740718732 1250 740717482 740717501
    0x1110f0c030c060301030507031205360f0102190507050a0305031b34080102040f030302060a090314031003120512070c0210110a02040f052a04140102010e01060306 72
    0x190b40401e004901001801e000a00001d05241d11402007403001800c1040100f03808086c0303083c10743c00c081003110028100e1044001410310300c03a4100504520520300d20880703082d4041190302042410002000035034801e00c6100d00e18000b91003c44a0042c4002441004050040541800625a201e00313149640340e100c06640000e12010000e801c41a00d8080b4002d46404003084001c104090400f51580340e000c503030818244030444080000441e84000d2005000502c2401d400c04000307031440c10b02900385031000301407500090810701b449002aa100d1b420083e8841002010368480e100c40751401d00c0010f0302e400080000c5081c4a02c00189c80e0040c020301000807041500022590b96070204603000300700c443e00290040416040f00c01c072640501410160441040c00301c172107440281d000a0140c981f480f1045005656070004c1c050350070b58000e440c0e200d059620301164044500f000a581030340c1300324455428541c40c40c0031000c1250380f007904010b02d42d0303944500a106194481c20054000c140004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 740719982 1250 740718732 740718739
    0xc2116050a08070b0403080c250510030204080d03180803010f0f06020c010804060b150325050f0403080d0605040e061501210507110d05042108030a0b01110f0c 70
    0x480010340765800a00b200a503013403054818203041c519a1034110f035803c103a0300440c85000b865040c1f4080c0a540c21150351340148989102c1c0c0003480d01c018040c1c049100400c0c07008141c0104014006460300050403200c1032501d14001500b803505403844000082122001132009030004000661202c500800400759807400d101c40f0074080c2c1e10340c4143d0742c507040e51100074049200b0a0025012074843d40c41010480005840091b0410140680040c40d81c4200c45081407821090a9008014200803050030b41400e01c1c01c0003440c01191010b5040c043c02144001401032100241031100201d91382c01810003010b010384107002c1c0091840195454440485502e43c80d072044030798005d502d40c840c0700217001c40390480010300c45c0219421486000380200602c52401d120101c0e039940c1040004000c00c0015a4640e80c48640b2079040504440091201500303000403814828420b50104981c00100d903040b0840c2c0c88002003d00c80308005071041c0c1414500c114540c0030301c040100800d00d01007139003040ca88084 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 740721232 1250 740719982 740719999
    0x3060a080f210903062a0a050d0c0809070e070302090402040303020102070317100e220803100b0f1912020d14130b2a03101e06020c211605 61
    0x1d26003407070203000f4140b15541c154000780116600c082d095444805011444200e00304101000102e007003950b00a80050f4001000000c1c59801448540b041e9055000545010801d504192000300c0d5282860300800b404d07031403201c010820050003139048522111000c0e100f5502c80d566402d02a0003034002c414240c020030403407440302a107100100e106510403101e031a14201c5c0b16040054080f40300d40000e00340070480784000f8420485408149110700000d02c41d0300f103da0749140c070881c0ca401c0d0350070301d501c000c1c041541401030525410b81c03070003550400000303561040c090f995690b0080b0345441800320020780301c902c00981a604000c1c0398000e240701c010342c00040c41032905d0310f0700200022031049402416541c03c0703001140c0284903004400e4503e030000e00000b8600b24103110301514507441a5824641c29040b40020403100c3c0d002d00e80d203a48040040c0180700304500e861000794846048100d014400c0703415000d6074800c00604c0040114070b48040c800c86000b08146283d8a2401c2030078081c1b00d1094004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 740722482 1250 740721232 740721283
    0x1d040b07180b03010905091c200726030f03070c1a0403030c0e0d0f060207170d0c0305090c030601090c050708030a02040f12051b120a0609170403031403060a080f 71
    0x15081d000481d61001544100c2e0100009c451580c032407103881c4110b007000f0500c0700400b5010003814000d170400c010f0040d620904911429204000075100c0c02d800d4106120784c1d0120301152080e40e0b07014a150030310800d0403100e49040075241d4130701d00040480104403001c0c4424907501d9440070b21420308039190203105c502c201d0304222513540358200090142c1004041200007424070f8024004040c4903000c404041c00782018049035a410042c0005d16240e642c464034030750b00e5418001c850700003a80d00c01801d0700c40103035030100c2d445040501501702c040d500d0781c01c1240c400f445803084a00740c0e600801c2c0b030342d1030f8140148600040d51141c8126440500708100210340c554071081102000c40d0302c0b60062800e13011000107290000040d403000355110b4194a10040400024003c00c04410301c101c0000418880d14030344500000300c00d4411780a4007200348028400079402150000c10b00d2521141d86860f0354542c00000c01c50b042603048908036000f10743c442e0780941000541a6828091308a040c2d02000c80c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 740723732 1250 740722482 740722501
    0x3062503090c03020409081225050405090402040c050405061303050c0906030601030b09072612160303050615040f0608060d1a0603010e030f040f1d040b07180b03010905 74
    0x2061801a0601d240b0030020801480c0903800421040c0c030841c003060614181401030b070305c00c0c03204484003840d03040110081c50401c0c042d1483c00700d460482e03041150403d81001f01180100c0c600902c003e00859484460140082c0618180c60081070000e201503070341d28001403a8101361000388400c80c7c032841034003580e040301e15058003510701c5110050b000303200e0380e0719544401c0030240014040d0a040d015103200800d0740999400150000d180c015210800c000880121500c3c0500128241411303501c1401210b0205401c1d04183d8070464061602294580342d40c0300003114110f21504240848200040024418040d00c4030300c8121740300c2d520b03001c1c0241d483c007080c4034440f0340601c0c0040c02d52583c40f01040900720211446030300454050000030302c140032030310094616403001d04890440c0401003410000044020560400340c081403140071803884220300841c0301004041d00c02010700501c3c80000b20400e104000c0380c0203a01c2c10080c4e801555030b595480c50a250700c01e0041620b01820500019a01507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 740724982 1250 740723732 740723741
    0x150f1404060b120402010f140304061e05040c120501111603080c070503040302270a02030a0e0a0b060105160605100e180a12210b100c0f2003062503 65
    0x301007051801040c1d80350b80c0110351f0303400000702d181c080c020000d4950f0050302403503001c1c0d0302c0703548100310001d410001c0c00d034036098074001c2954004200d42080700b00300001e1141b040540440395007420808002ca102c0c90140d001d4011131003420a0054003060900c185841840c49502c1e00d03000781c45100403500e5184018400307110f00715000d8040c0e48104400c00041c00c042501c0c0c04582c091040442e08110480d11403590702d0419289070748129004414444040d8881c4070303400c0801c019900411030802290343d079410b041c00080115050010103d103220b502e83d81d0440c0c1c40710003540301ca020801494400142e001d000c0041c045c5100340d0180300c0000e805140585550302003400030308014042d0001c0d0b5540c0c1d0110020301c052000401100040309100c5002c021141501c0040300325020032101075034018001081d010707108100800070005807250201d80302c000900c14a642090421600403241851580e10140d500748543d09807081e40100006a92510000c1c034400201840c01e42017a455801c0403810385 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 740726232 1250 740724982 740724997
    0x6060306051006091a0c03070b0103020307081f020310050d080d050a090f0209040311370b0a09020402090d030518040c050a03021b150f0a060e0109150f1404060b 71
    0x549200090054114405c2c081520410403685d9925111b2020035050a60b084604203c0d490071140006204510b01840b00001800900d002020309400b020b811680400468000384a0941d000000c10400c5035600c13a050080c00c07001d0b041e0310080c52140380805490b48050107910302503181002041c00e040e0315005980206d86c001494151000c41034003000445c41c4c01900403010300a000c0c0c000306d40900140200301c1d2100c940440b58110f140c0c2d40c4407592600c0c25403180b545541040d0101c9000040d10350f8101a044075070180005030408080c030103c0c00900c5030746403082d4800781d080d01d00b0f010141e108005001700700f0b00030500351741041c0f894148401c1c0d9880c0d0200340042901840585c2d82180b203580640304071a904d6840001c40311041001a0030006001c50b00f20070703148038400f08803001240b06a45a00444101c00400c200c03858803644040005060081509440c0c440140d1640408030118400203040e09074031444089035075407400d0340f000c8411200180110f083c030740002050028503054540d075 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 740727482 1250 740726232 740726237
    0x90506030709050f01020c0a150201110c070312170c0301080d090308040618090c0509030d02070e0f0601030905070e0a1a0904170403050703030806010801050d030207062a06060306051006 82
    0x583e0800c400c11204a0a41c1207081c110304c900c00303941c0003035900c601000008201c1c0c501d80b14845580c0920007801d4480b1859202040d035020850300540e000005482030480703800c07d031040b030007414106044410440c2c140b01d45034425800e03070a004100400d03800460403200d8203000c8614002102506441da02814400602004014841001028080c44883c602040b8060340d207036015485010b6481100c825600d03000014202080798580390600704980241d120550000b046502c0c600300c00c20f4a800070040c4501015240341000c10050b034080e4106e400b20f00d41c080292100e507516281505548072088940d80c42c1c5c282030000420142c003460903940d81da20b1001d03000092030703541d54407500004680d441030800c4686c0f0030000003000c91014846000554441e603212000c2d4280b040005101c03400680015101e5000400f0b40c8001a800140746012503503d400e191102c4003600d4881255082c5595240104600c80f02501c1e003000f00c2984070409403480740303104104a84414085600618490150002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 740728732 1250 740727482 740727497
    0x30501170607090e0703021b01090c1d04021309061d07091116020a0e0403020c09010e07051602131107061508031c0b06040608150f01140702030a0203120a0905060307 73
    0x51325007405043d0f001031103080162500a0a4506000e00190f484035201e140c0d5448801340200000ca0041070003c0000125409a91188244107140800d02400013071040040c06003503601c1400b41d8000c03890003504610b0800c41e19013920301c030070207607100342e01250601d020b044800715200901d40300d08054019203901d21401d00842a4511140605440050b80c0c40101044000b6401040011291140348294087d1003244145818071401007010307040078003410381c02010090341c0342c0d00c40155a40d1420390100d4060440190010a030448034003031840d00001e043c480020f0701e0503409802450000d00c9240200710981203206000e540c030390306010b114425001005404044603903072805e00c0d200310100034001020b003030003000118103603c594460408110500204241161740c1001c0c40e15040041d43e0f901d0f034003c0b00000082901c10128241284000086900015501c082110703190055000e070858048461411107940e131500100c40d60f4000503143e902c0403c5500705001924018091922a00c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 740729982 1250 740728732 740728739
    0x3130303050415240b070b070522080a0b1006090b0c16060804060b0109031205070f150203061c050d1d0406061101060506040e062e03050117060709 65
    0x300945030207441502d50000700300b079000c201c2d031851044c3c1c00f010001e40b8040d4002145003510207440d182c9903002ca50700032410b02c912004261000c0b02154464030500d407450780c0d59a2030b8011918496045000e80d146010380902043c040000580e142c011809040b04584a58451881510340c1c20319009180000e41c90324000c200040c0d082026100d02c0d031340130060701e0158210416403c00440264032a10008180b9020b22040c082d80d8030400c0004034007840c0086d00241161940507000c15081610340411078000352031014004e24914000002e0390140300c0001c001d40700142c3d100a901b096607043e2180e0089001000310910103101d0900c21a03000e0060480724a0009080c5d4405210029401c44041c0380d5089880c16a10b82c803450003d02610740781c11030305a6071520668216050f6800403801070302e080006010f04440414410340c060381c121141d9400c80c9081c481008903e900b0040d24001c1c070380e8412100071154040d00428141c409540b07100d82e480a0704014242e0701c540603900329020038010320061 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 740731232 1250 740729982 740729987
    0x6020c04060513020a0c0b0f06150a021c0c0605010e04060b0303130e060a030212061611060c070201140324061c0506190e0a110304020102031b1204031115031303 71
    0x410f0b00028500748006c6100d455112424286800c940d0a03800842d0b002c200002c2c1c0c0b03098410001501d9020140c0c6060400001029590315854202490880361003001500102c1c03044611110706a807000040c0907035613440440424030003050b0b40856001e070a00b0040760700e43c100081601c0d2411124450964140e180c4411200320050103491584c00c4840d0a070084050385070380a5803444107e4000c004d1a20346441d49540d00d46486400b03030081046480d503d039400c00030300002d032540c00200d00060b542d5510114401a600c904914100250210b00403080000c001e0ae0303844040c1c002c0140c4580d02040e8000c41040102e144228030041c829460300d11440c49403020545d10041e4029406000c0d910081c0e1040aa000484416800b0703041a45284040003480746003401044215401c007210341d030840c105540042c0d240e010740c122000c08a030340710025861003c01008290004401403031141e0f5180d40320f051900440354001c021078004c1d000d0031001003004001c902140c0c0b05000b20684c1c006110860f80d005c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 740732482 1250 740731232 740731237
    0x60a1806020906130e0402090a290a09140a0b04050c07080c01060512031b0d1e090f060e040c090b091026010303140304030909022a060106020c0406051302 68
    0x111034101000740400c507282e081c1324404402801310800414540d1409104010034840c0007007400e1901410059001070f50010a203200c105520946074a4039840031000100340d015006a006c46182d505218001c11850040c000103401507655480034450304400c2d0007840203651069803a41d021500801c101d1011520400c003070010030800800202c0c070241c2d5640000d0901104070316102c0c00d504002010b42040e8403800030f84800000c1c1d000036100d60540e440303014080005e1403180f84511030018a02d080458840c041041c0a401c2c0001c2d03c4501584583d40185a024420051809589400c0010130018010040002140c40c2c1500e614640319076103040c031144001154110060042c101080303100c80840307010200d54150040700254043d031545c1402800c0341001007040c10040c10810a01010079804a020419522283e40144e40d8550300c1c01d041a05622030a90054010070344039500180d207002096081c1264800da0845980020307810800c41142e91501c2943e40c8101485c034403e000c100590003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 740733732 1250 740732482 740732497
    0xc09010311071b140415090b0a08012c03120c0a030f0518070e0c070b10031202070e01062a020303091e040507050a02060402120c1002010b03060a180602 67
    0x461030300b4060140d44100c002088003608010025190006100b02481e1490130074840400312014031a103c0403c0d041d4103924607a0064070340803512045c00d60019202c0d078586c24010300b0324400030030000301c089a15803090140c0d0103208214a030171800303620b1402c0000080e80c0d006038144124040c1c46e00d0704a5a0261640240400c605050f01c880703416406038598400e440c400c0550302e45c03460020060000e0355080c50013076001a403084204d041030081001c5030200fa5440e0b50340c001a0700714640c0798146460708050455000800c807900d03100c0740e01c0003158080381d00c004603030241e500580f0b1031b46c98800c02e8400c050b10012900f560800c0306844c42c0051031005001403298009000e42e4a00319100c0007150f01c000c090224000101d4140220004e076003420301c1965841103e1340b4081e4141045084000c0d250f04d005130000c4d200304914200c4002c81e09043c4600f4441c0b510051401d0700e0600c1000c0064040c00c45500c1c860702c2409084000b640c0c3c201c1d180200011510503c80e102a40c590340da641e90b000390003690 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 740734982 1250 740733732 740733761
    0x1c090801020a02030301090f020301030b150a03080d0b040b010306290c1207050c030613140718090c12050706050a210209041a1e01050c061005030d02060c090103 71
    0x4100144480003880140510329560340030750f03501c2d8140004841603900070a18403460358810401000454450804107800440a103004410b0070342031000120410706c0380d007019000140010f0140400031040d842140b0103401070b24207000800000e03006600b10b5000e4400d800e007400c54080c4240602130740c01114582c11400001c55030424a0200c0420b00d0011045800300005000052810070b00400300007207049440102d004100b64500046400081c100a0500030079160706010110448041400a075002c0c001043c44041c10301101c03204007000d08510384069944411520b0003140f08080403070345020103a0004000c01c012854554111910360201000b08100030034a00c0182201485281d10f1502c3e441022000d030329a0404802c103c22200400345800030a0708821100b1150740b191000c0c6034810120006c0b20603000c2641f00165158401c14410031410b00400c802c000300c6000c044a150305480080c0c0446011601c07007441070760303940070507504c2c0d40d41440c0900400b42c4940c4030741c00c10860300081c4c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 740736232 1250 740734982 740734997
    0x50f07050d0f05040506010302010206250e030a0506100f0603181e0f24020702030a080903030d0518012316142a010209010504090b01030605130501140f01021c 70
    0x28041c02103c20030384088945402180040003950f86c10440d0700c0d006042043d103040003400c407001c0a02c288002d180c136101032051208040070150b405119070343d06270741c20405480303c40c07920300070301c0021051034010380a8110404d98045141e610030310841c00c130b102425100c003a80b20300c43d4507600315441b00c0b06906c20b84800240314850005030720100e00c01c8406d00c80d158130ba42e58032071000010510100740750030708042031041c0402c82c0540d40006804484c00e410084c9140c1d0782c1403102c0880d00394480c0020301034009041c8401e02c40118001c400b0505201e81c96002044950010b82107646044e40e80c2074202e04002102001c500d45600c40c03511440c4907101400d08900004e0481032280c10342c1c0100302010300401d2103030489880d0342985124100c1c038121900c021450542e0380380028009000d103008203030005a44101e075044507402540002d0107010014000003003040807a6101c0c2c06800c0c02d0080c0240114240340001c400c1c1014000381001c2001600035101140d0b110303070303690200c25800d0218010800e84 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 740737482 1250 740736232 740736251
    0x40e01140a0f15030605060102010605010f0e010c0512070c0311040504170f041a130503070501210917071a060a15031d01092922050706120e01050f07050d 68
    0x3d84964000441c802e4a0200b49032900d83c00190856219900003410b104031101401000c60b404892181c880301e090814075901b100c01d040c0b0300c2c80c2080b11181188403440005a0800340f140e1000e2101c2100d2182e5540c1203803603102020300095450079100100301b0074800001c0b0707000301e01200141105000c0c2c0c040090500380e550b841d0a002001888100085a03000100d11400107001e0320000090700c0305500038001c0a03d050300007047d0f400512002e40842c8050588005035810b59005410404d40205110a60b00001d1000000f50740c01040d08840340b0400c014038114028880325094810200200071510039403400041030520740d1403521203001c050747d600110705c824240c444a0440005c03440000107c442c52880c00003851040310a02c581c0da54403405501da0282c071001c0308183c0c080420110002c1c0c1c00361840240910504582c40240320303002c3c0000221b00c499000343c0d800114951018244040351103412150b00f00c2d2002d40b202c00e0440e00181c0010f90041c01100145148c0d100741e44001590303082d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 740738732 1250 740737482 740737511
    0x405010f08030405061c1a1905010e0409030c02150307020d0207120b040201051b010204140306090a031148130513050f0708061806061005040e0a0605040e01140a0f 72
    0x1210000d5008050803051840818240800710522207420235401081d418107000010b00041002980982b20ba510340a000042511a101c40c8644036809054048408079186940905400c1110303080c0040c810141c58056240c4002102c0003160307442110104040001c0d110b41000720782c01002681402010010016004c56424201601d084588001602c840c00d142e80a24030190a1400c644a41d1110b41806015400869030071141941420100c0c4c522454800b41401c000500510341d41031240c1000325840110000c403000004c101e08101c840300841d440d000b182c005907448803a50380100540900c61814490303640318a1308900340181c42c604a01c06035945d00e240110031005c411190b081a801000302d01001c002d4240c210b200300da024421b110400b01080e0381d0b6003000308102e10130280d030f03c0035000c0350703001d242240c029050a03044000c5514060344148045c207850b1140314010f51400804800720801846049100e001e00c5d15400c2803174490f4009000507009081004140f40c0d90f8400c1004d0010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 740739982 1250 740738732 740738741
    0x40e1203011a1215030606010212040e1509070f020c10020d0f110d0201090b01051f0f030207150510090509120d060923010b04050609120106090612020405010f08030405061c 76
    0x4580c00590003d041305074090505000c2e0160420f8103651040c480030305518400b00580d41550000c8094065030390718404240103450480c2c107043d8124000200780038180750710450a4016000c81d40880f42c48144d400184415000c00000823401a00240c40d5100e416206100040c0038405601e02000080754880016040c410030080b02000f5079500d2001d00304204100540c60f0040400710b03580d5001c140301d0451051100c2c029010401000540010038000c24001d5040d00c8415401c0600c4c0d150114810068200400381600d0710b5246a000d4040000c12956a00034944a400b11700040c00160001e42d1b00ca500c5078000203901048240c4644000c19107540030311400121248001c1d81c01e0700020910b050007030004040c0c00c19140001d0800052010740c0380d0100303c481508080d15188041d11090440b84d0050042c2e0f0401c45045091110020308003e10000c40510a0f00889041120f80d9031401c00000040b01403041701282d4009220401041c902200585000004400b84528541c60b6119080446 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 740741232 1250 740739982 740739991
    0x2090a0321170105030712061e0e060906091011090612100f05030309012609100b010801030203070608090f01050c040617070c021e0d05010b040e1203011a12 69
    0x4004501030200c4a40e00071403900c0c5145030b007902c4030380e194100700110307440c0c0d001e40c0645040c44c10395541e11010170409522031b8800441000100004005070a4030b60003501490720842200e10032280440c00e0b4000214000c0e00840c05800203041103040002580081d041c5441a80c0c0c0385441488003844580314000204652502983d442c0788624200c2511484030060344c201050840c00348000f800940c0f800421030300345807824200841e468107403034402c200c2c04c104018424000030210041c010038850000c0d03481d008450400042c040d82031490011134141409100c080e6040c0e01c05042004080c0c091303143e40380c1101740c0f4400c0e198101140320b210742c00c4d42d4040e11018548100000c003040704560060000410302020780e06101142400307400100b228072450b078080d101d032000400c1d1647c49050074084585501024021343e141d017505090083c02004c43d0b840190189041c42220441900c010507461070300b00307072641c0b06429039007424440c0f0f0f499000684480301060b0100b22092880c45d694400c10302c42d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 740742482 1250 740741232 740741273
    0x10c050102030a1b020a0503030a180501090605040c050402400320100e0f12011e0f06080a030c08040e090609070803040807060c150c180b03041502090a03 68
    0x20f084a55404c00c0d080a0035201e03010854021046900c00598080f00f20390708840107402c0032a1000c10541840c0560003c2d0100524561a20070008100080340c0c0001e03120310702500020504540d80e80a0006912603801444032101b481a1400354980f6007800c001d062001074072007500c0a48000e11110021001a0810b82d550281803030700a0f0f02d203601502415000c40250740c1c1884980e41640c000d001c401c001e8a80c2c0e8428030340c284201c20292200b44182800f102c1c4d402c000d000c45064588400c80c107152603c81d0681541c10700c0440340e40e000160081c2411201404000c1500c4903203910216500c002800d001c4600031001c1100085048414101e42e00440002d000340126003003074055140341c0541940107502a81080c40100041c40d4046070f400c0440d9020304103258100e03518602040f44002000407401001d01c0d000ca1502c1141e40b050781114503017030540003a4010f17512030b0760000c244e01044400030b20051809402240355a41a00505120030010708071035222601c2c0c2d52909010096075080d0582e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 740743732 1250 740742482 740742491
    0xf04030c140409150e0a23010b060f04050904080403060f0b030f0115141f020319030b0d03030e0a050f06190e070e040c08030a0f03061d0f06010c050102030a 69
    0x1915040001e00020000201ca007008000b1a0b070b9079800d8083d503050341e038082056a0306849402070300248081d070f0702980d02000f50344440340382c0942d940d02c0b8a14503c80032150342c40c00c05890000d0504408984580007021521414245082c003080050a8018030464004405120000002d099402001e14002e051640400c4418098040c5894480b9250b80c0c10f078168144894054810011504682030b102c490400b68003100e002d10209100c1c0907520207494010381d048090808440e8080007509081000d0008200309512007030303007142540e4802c4407803503100e050240c0780340009010380c0c0301000220075001520107420751380d2900340c2006060b80300760f03089812142c10009010503100c00c54400c003811840400c4206000c9020550baa540c5010710380403000000082018031542a1648006041070b81c21030b82d40d0a8be540d40180a10b2001d5003c6020904007074001c030300b52007080060070000302074544070fa10320750301c2081c4881031a1015100300e06210b0110305443c08a4420300007103129260010020a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 740744982 1250 740743732 740743739
    0xc071e020108060402071a07050c250602030c060c0a11060a090606171c360905010612150f06090509074503050604060f0510090e030f04030c 62
    0x1484418014100c0341300314410080000010581c411249010408100e000444d0780c440000342d070a403013090301091192084045603014031241850b80e862000c00300c0061101d25646030720680c0e41e801110b022200d140c03c8a000164541c5070080035000c582c42903c2d21441c6108007240e45402c0c0342c020b0300d007001c0b0107855620300b00c144020b03402114000c2031488410000e08210002d1140c032126031500251445210780765078540c1e2131040c050040d804503c031402c059280483d602a05900031043c0445090000e030000000d0b0011281c403072141242c2040c0c41c1e10050018800302c460003400c1e81c1c0c1144038595800b034808a00041c990604d80040e040702e803a5807001d2802e01041100c101d400900c12000c204501e00c882d105d100c0006010190503001c803030015050984412001070310319a08141940700266690000244000010b1b43c500881c0503000c00c0108100003031039501a80c508940326036190041034420080482160b10101320180100241d078200303e44000588034a03800b691080d80e001c824041c051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 740746232 1250 740744982 740744987
    0x50307090b09032a030303092a1807201e030f04061809020711130c050306060c1504230a170a050702130c020c06040b070b0c071e0201 59
    0x301900103000d00e0341c00e010790007000030ba948100319400754400d90100008020415000002040c45600506070783d1030340b81284425035903c2c00607810150030500d54440c40d01d9000c041d981c1e541a500301404103500c50341c40000d00d060800b40548000100a18501c0c2e0070884d050104044c0060704d8500040d143c5200840c04400100110380300400d180e404c02c204140c0c000040c441100d084446074140390b2000400301003c80240041c6510404990b400010b5203000c0011850310708085200c11100ca074842d03d000621402150b140710b6058010450410202d0b500e4941007003c3c2241550380000c07510700603925503921000c03032001c1d28104d81034000403170b500700721714039143e10381d80d20584c21801032a01004e01c1d20303000c90884404001050b54000080e4034004544110304458842c0d03000f5050b90f89030601d800c001b0005140002d142001400b0307010702c40d456031600e401103070225210300e0701c1c0c181000310300c0c0c03500021144082c01d403403210f4004108900004510301c0c080d071a5243e5000e5821280032190001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 740747482 1250 740746232 740746247
    0x1050d060e010f0b13060c140a1101140c07050111070302150c21030118060b1303050105070e130b01030e0f01020a0e0a03020d152403200303070605100308030403050307 74
    0x40d1383c00d05050200110300141690078000b103481e6850003c885107051309120000e400d08020804050188007804400d10009480145800314283c1c1e900803c1804005c03d03e00710b024050480507182c110040c200b1081d8482c101e40050000c0400c16980707641d40d6540020303031a00d03540c068914480d81c00b00300c8500d030100900c603400c40c1c001000c42a01c0207803d1802c402c80c851105000c2e000100410100302c0078488015403110b00940003410800d6501d1294a40b426200300451104a17150743c24100010203051042c1e008204200010300801c045404810031036000e0014010a03d0400d1750318a1040d0369000200101c0429482d207800040e40c0b82403102c8003e105c0c180c4084024001ca100280800068582d1f030003400c1c0c203681155000003a511035203d01c0c0c001e015940343c1720140c001090020000740041c803030000c00b124411030380510081d00c003000d1040400c0c03c9200c0700303034140c01c1803111501103a81d9410441d40500d00403540c207102903e960303442409030802da406500081012040018283d000041b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 740748732 1250 740747482 740747489
    0x31b0111031216020105090a031202040e0a05041b18020c0c060301060f09150c14012903240606070302010e1605030105090a081803100c020c1504120602070201050d060e010f 76
    0x83c81b091400e0180e456075504400402001c111143e01c5100c11010143d068502900307810044034070b0303401c0c04c031142005040181c40075110f10b81c240c00710022030900c840c4103201701c0b164801d03032a0241c88415032400c02900808900285c60054500d4000e1301d549080041d800b0308810307100e8100c01c1c0308490340140080e001d80c0103612401644004c07046459005021008071a40c000d0f485000d0110707110300a40074240401500180251540941c0d0002c02c4600c110500c01805408442e075081861003812804240c0d01417909044c084800491400e00300b000040403180d00a000100300090210076807858035900308003200480c8207085051000385030038010903404c03915030801040b100c403464803032200d184a1100b80d00000076110403001c046850500c5102c0310180c556008221100d80110040d454103000c002c02881551405100c040e01c0d19040305450548603070001500c4c802010303a80301e2000790302181c000e82c14040240150101c00e1040d000704030142c000c00e41c06007010b5143c0a000c07020001141c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 740749982 1250 740748732 740748737
    0x30f130201020a0f0f0b0103080307120501120807050708060c1201050102030913021614060a0c23070606050402071a090c01082e240905031b0111031216 67
    0x40001607070b400208280c503c1d80000780a040030426140800c80395280c404000c10009240000202340900c10014520416080e02c0c1c3d440c4502c9040102c0c0110762013401202100004154460b001c10999070140101c41d11840484400c03a403100070583c6040c40c00c0700c0e0071120140000c0c001040300340460702e190042c40280002e600306400c00b4005281e2013007a00740020196404180980101d900007060060140c2042d091458203448202058542404555114074a030400240e130305458480d50b074240e40c540303004100c01c0c90001301c54042c0d200e5510401c02540d900d905c4030b0002c65540d80314802041c406102da094190340803e00750554040c1d210041082400d9004075440004ca070341c11100107030340800814076081c1000e1a0415039082d0000d41c00e4003a0f03c010740103201207140141d401984201d9100c021800c02c000c090706404407208003090103100c2d0035411500219520100c1140000c1118105060810740e05001217181c0345150401d2050b0f0442034481c00038040103000b10071031841181c07041d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 740751232 1250 740749982 740750011
    0x3361203150e090106050108130b15060f07020405150108041202160803130503010606201c05030718230d0618020405010f240c062d15050609010203040801050a02030f 73
    0x2d00c030403008d950f07203e20060b04102c02000002e056100c20360032010220750040c10507840300405080c40c81079401c00ec008074000c0e850b003800702e000c5d280d880c070682441c1e060513901c1610a6031596a000341400502c0c1c00201944200d10030300000450000800303001c2c05c0340d14010354603881c10b0b544403d07040d0403030b500040c002d91405c0c005002c040e6100d6078400740c21218002003510351902254040c40d2686107031200d040002e200025840a550040045000d025295034184e42072404044145d0403250922840c42c0702c1b0032404940e071044000150300c0d10340c058000c044c08121f4030542c0391081070358014000c080140100d40503500840c03402d8070640d805040e5000700c04100a080c8102034818000306c07102207410220b416201003105101d420454001540800b06000c444805800006010075800c20401100c2540f6103507041d6080b0391180382c00c17400c0101481224180f9020500407998400412681140000c010214450401b400360034002d8418440040c1d0305c0c40c080f41d100301c0e000c00282a13610401c03141c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 740752482 1250 740751232 740751241
    0x10b0a1409070305192a090f080d0c0b0a09020d12140c0c1507141b01020c0d0303180209040b09011803020a030f0e1003361203150e090106050108 64
    0x5041d481c1c074050445c001030820440d55400031140104022204001d40d1601c4c041211030340804185c0445404d04a80c036000c54403050f81e40d40b2503c059010340c0000700d0001041000c03a03d17400b215170b0048048000050002001e0b008201b8040a00350709640b90110100c5036140349901080c6007895400c070340840c1e828003c01104a5440c1e8400105c0030380303e16162903050303260490b644200c41c0300a50040c24082e40454200700251a9140020620349a140c4c1010051040d40003040602540340010f140c001812802c1d68103030024280342201c1ca46000284401d100144c646244003806030303000e22005515403420350581c600307444c00b9030085c07005607611140d0302c000290005800b05207542d1605003e0641748503043c040304c0024644050700d901c64648136400c44d656415521600714244224a25040208142c40c0d92014008403008140580180007440c000306140407c00f80b810031280c500170651404136240101e11800a801140c55a8410800c0c030403a001d00344030380c10090100b0309024606181 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 740753732 1250 740752482 740752501
    0xb180f091009020607021318060f180201080a09030318150501080a020a0b0d09080708130f080a150f2415082a03100303080108030301080c010c05010b0a1409070305 72
    0x56440082c000c5c0382921541d2218502c54120000c80301e18001c0d02c4040c2452350410801070007101a0b0f1540c2ca84c5440755048581581009403200913030181c442c815982c8a0350f41c42402443d00c0541074082607501c100482d55038510040e40755125018405403113808101e016401c04640069201d506103030701a0303401c4030040e2202562441102d400c0501a0380318003891800e100600f52040d0001d105e0180015000d0800000780b025120141c100d41c0c0122000b61503403401e06e4410460300401007194803e00801001810711003101c1c1d040545090040780110440403c44c09407209201c05029049107030000501c0300034242c1c1050000e28600c400f8000b0f01c007000e0800360481c00064521b0159044468001c000500701d40b03140c9030b0407948910070700e6a9143c409284440d03003803980001c500160701c010000403c80400001d4906a8071010003a01160a001005481c541e130641c0080320700b5503c5501211066030b445101c50002c20444603e084041c001d00d041120280c002010002418901400c1c0081b001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 740754982 1250 740753732 740753737
    0x10906061707030612030c14070315200c150f070804030c021212090a05120303072f07030311010216030e13060b0a140c0a060b180f0910090206 63
    0xc10581d0740300034a4861860031009052940c01404038003400e5007050007007603031001c9201112400b440d1401e400000c003c40d01c030380342c800c87e120192540044180d000d040d90703244d502c1140e90340700200c07c41c0d203005248155071115400000e400c58241d0050040910325100014019074042807460b41030301140740000d030140044101810203410444a65800f504640303911030a401c0c0504800c00300e0700c49040010750821542e11110302640129182e0900148604040c3c1007200410401e00c003850441d13889030000c507088680c41420962281c202854814480301c02400040308140784c90140142508508025000440300080148981c0c0304010410a0721284009450016814584807425040201c006020141d2031188820072500c0c2010028585004900900c0305a0954440d80301c0312030b200307020b410980914004036100b1b07040b890014000170110f0348808407001c0c0041540821404609010b0070444080314070950803002d03007050040c0c6140c100000c01c2c1003880c4440c24440301c4199400304400e030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 740756232 1250 740754982 740755007
    0xc0c0a06050d0b040609090b10080a0803340504030605100305030a110c040c0e03160317070507090501030303141f031506080d18080c150a02010e0d0c02040501090606 73
    0x10f549001c01c0e076895840b5000400100a134000a20100e0001d040030032014100b5581c05000382c480d0b210003e240400813500032038a03504400c2c01800c540d182707a11040c0c1d0345540b9060301c9129032040e660383c022012100c409410041c0329074920f52180e065140050840b840070304a040101c04680702080000c4000040f500d00c030f41d0360310701080d1040364880756519048a00b40b100398002c1c101002c5d07a642c65441101c000c18420301701d08031101d45201070b10f01c62451707405000c082c000c010703800c040070a041c240c10001c1c580a84580110b454081d6503481c1c0d2400ca810a8108034002a1100001c604080171001c416420031a103505e140355400c00502e031140d254855200040c01d17280d42030307003040000017103a20080050072600240e4032102d40e054801002082d4100120380c00c102000d80101c0c03103490006083c000607101505120b404c070800084540c0f590484c03550031045640f03800c821402c03004107004c481004400307a1a0083d400c0600d1040000b5200160048100c092411000700840c50344105200c100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 740757482 1250 740756232 740756257
    0x705101b030c02150112021e0f010f09050907032406020c010309020a03080d0b011409011b050a0c06051b010b0d02090c13030f111e04050901140c0c0c0a0605 69
    0x1c1c40b6410380590820100d040c401c48815075810002400e200e042035001c0001e80700b1692080342098844c021400304025071201a00603c003602c4000155006112043c440d031071301c0c108061502d81d40c60020700701490440d200c42c0001c0c0c981144070368442d0003500f405000c8240701b00c07101c1450309041d0002e503981c000e108032f00e04064682c04c0d04429500c80d03606034405107030031010a9a80b410040c2e140e00c0071b00001d040d210b0000e41001c00780c402c100b0000094030011f142c165161603000b0003610502c00d4500b251542030f039660141e801310f070000800c079113260002081180c96030398503660001480d15690318101341042c1c02d40d04090900380e46035661051801200d60441e030110707a586402c4901415030164191001c1f00411100c0c0120a00ca00380130840031140c414102202d41000e0803041c40416600400366030041c1c1c4c100740c0482030514094008a41c0201040c000144003a20a81d080900c2703c021b45800100410000d59441c0000b414040b410313504005440030391a240c5001c400406520a22000460 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 740758732 1250 740757482 740757491
    0x105010806012a17190c0507090506010509130b010915021011070f2d02090a1a0d030c02040e03030f1302010e0405040b180105010605120a1508030705101b03 69
    0xe41450041c028039007603820a0b80520803502c001403101030750380290a24002c0005c680d0f100240310788105041056164000003424400e890004440003500029000741d06201c01030102101c00e480e0f0300c50090403c1c9402c5400b1071210400c90016100c03100d19003000b6119002c00c841a184181c0004240e0891821094001a500382c1e0240c6080180505e10005000700a0718481c1d8051011914410320312018861840c00328400c0250030b040c2480c1d100c54020b40262099001032a6141254001d03905000040b001c10110981d0f0300000f403100020030002c602003204094001e095003414826481d00b199140015031031418103d003890312000c8000e01c0383c208285908640400c59108510303e66048801400a02482c1418900150271400454804210303074507000e0703140c41075101401244e04030345aa40301d0501d0194940c498034203810f0000c00f8030000544501c03100312082c2c81c02d0a000004c106100c041c54441000b45021820702c8000d1408540780d0b42440c600c2c1c2c40980c500c0815488004480c2030000c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 740759982 1250 740758732 740758787
    0xf040c09150e270f06070c0f0305090a1e0e090106060816020f0706050c0c010e0f010e0f060a020a0510140f09010b030f010b030c04050c120915040507060305010501080601 75
    0x454085035a800e00f403001611440305109100014001050b9224001554250399600c6c07011290400104d40c0542001040000000468001c4004010806020b420b440b41c40e51100b42c13610b808080d04100d11201700c0d00160070401a54414001908040414000c0c00564688503008207040c0024041d45070480f821119881c0c464000c021024003040540d084d503401c030b50b880c1d002400d40e070000440c2201a001e000c150046640c49181107000c0c03c0002403a035031401100000440e2284611015075800c410b840b02c1d41c540541c5c0e14070160118014aa00402180c0780d913140c1241403071504035011003c1d0341400e40303d4040d031201a02241d40b0183c10490314100344d952401442c050004d000b14580c1600a00310880c50904040d0092281c1a50070b404860380344074504244021540700300c407101c5542e10180700340194199034090b0240c010140604860740700c0503a684800d000041541c0c2100d903544001030801540f0f4050041d2401820f090034410b01518140002030a1100c51281000ca0321080200c81d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 740761232 1250 740759982 740760001
    0x6041217070c080c011b0507060305191b09052d0f1002060f100806130606180e150f070c0c0b040b03040b16140702010c0b0f040c09150e 60
    0x300c0c411900402c004039140d9880840c0c5440d043d01200c494002280580f42c140707221150380d1050880765001000301201c902d404822001800080d10f2040c0211640c4847c1d030284101d4020071a007480c058586404104101601602001d1a40c2c025070050b030001c0c0c03d11541818400e0741042d0b8400700c4046183e080c125070000740460545003180c5c1d52100180f40c91070012540010524400c110303801c2100039a4686624002c038210b2507204010659101200107880095000166a10a442044c0101c0ca9940711034401000e41207108403256055518919888405400c020b6099180f0303012032203d505003018600170031110741c024600c20511410200b004208410661004024009c0055a03512240c0b200502e2201c2d5009071400e036045200140401c42e40710f10007444200e403000b607846805071395a086007402c00035000600141d06126410304401d0201e8030f00ba14952144001c180f40e1005498541340c903212601c0983c00c41c1c20254588040d0f159205074405210b0305855500359003404c55079070b200c0034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 740762482 1250 740761232 740761237
    0x30402040b100809011d07120c030602040b0706061202150c160803070605150a032301020403080405130507050904021309020d0204033f0e1f02010b06041217 69
    0x1e00e6004004400c800c410a940651914007600b0325000030b220088224540111849843e504000207410010341004205140007020764082d101360600544160307030b5110031040f80c11990000354014400200c0c4020081e40d4401d800c05484110b08200554640707401003071a441520301881401d000006031038006000030045282c2c040e000d040510070140c0c80d202015203130b410941c03045441900b01404075012074122000c103030f40d42c1c01c007404001c0004d00d035131507041b8901c03021044080b0f0760b0801d01611072206403e00003000614003d01a451f9110310b031600784914201084158100f041c079004c2400380c82544030302266a4210100e80158540d42c030184003082d400a940e00090b40c191001407101e02c0d0b50f403540c0180007128000c401c10200c5c20700c5a005200210307400c4111134031000101e0311a0301e0b401c400210f0a04904920702d01541c1c034012810101d5881c03469808008a8440801d980002080d4240a12110b00d001554201e0810b450010341031822620054001d080011b001d0031120000401c905 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 740763732 1250 740762482 740762501
    0x7140d0b0907090504200307050307180602210930250602190201050a11030d0e01150503070e0c120c0304120e031005061f051206010905030a030503040204 68
    0x70328005081c906409031400d409441000d024a0400e020b50101d6000440402d212841c07440c2d4a44c60741d82c0764801122a03030b000400040074850045180b00c110b44044072041c0142c041d03a00107103414006203109040d0001328050380400814108540121a210540807a883c0554a0704000b81c10310003034003000007508040d040407820b100e44292074025028242011800d41715104c5503a956588881c0c0482e2a000c6a907000280320b4020036100005510403802060352516a25003107807000d401d03410781415039000e130600404032911000303441140c100a2040c1c02d404490141d800c500d041c58840400d8848001c2d110311301e802243e080c0094440c040c1c007030485040d50920908200315190202c210306460f041076405640b0701c450702508440f868014152219100d100070000c180d20016004040060f220080040d41c00088480b0103081c1281458070003aa40110343d2a900c4d2122100d140541e43c100006000034100041e09400f0480d0307443c0403400402c0701c1d8042c5452a90f0350758070300204020305100301 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 740764982 1250 740763732 740763739
    0x161b050f1009170a08011701020d18030e040c0c0201030f0219020a11041104030f050703050d09080c0d0305070b09070506120a15030c14031e010504050d0807140d0b 72
    0x10aa8000030303580701c1031070b4610440108812034484800740e11240180c56108001c1880e140060149582d1401c0e1031405456010001d450401101d8880b01030768240c007218820707010900c0a079420948c01075007003030300c0e02c4055070304014101107818010104102c40b03038081d06041e92585219807502c0b040d01264190700c440030f1080d680205450000b5664a0340d000b0580b10002c04000745900c03440c10b8055030500307505080189007484d007107403a6041011100c4000315030718812003900000084060006505000458a800700c02c2c614042c0d80700c3c2000303105001c3c01d108112103610300c40007a130131406407420741703400c00303e190000c0c1e885944091411050703411040e030003040400c0036203000c03d03950112841240b0b0b85000b841014406409400c05034000c2c000101550b0a94070300b88543c105000390f11083c660014111a803090100d42c0d4201c0c40626094402000d0f5101d00401c01400700401c11038501e0581854078011b10b00e00040f00a25818022900944040e40000ca40503441c1031504002c98091005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 740766232 1250 740764982 740764993
    0x70b0f0c04120812100501090e190b060c0a110a05040e0d030234030f0e011e021e070f05030f07120330060812090f04020c150609161b050f 61
    0x404407210105c510034140050240140131511700b8a002160340204906c10707640500842846001d0040c100100d40b0b42e82100041c8281300b2405000c0004c042c0320b43c043e44041c1c118004030014020581115003200d4021802d00f10080000e520000b0b401555040a150050322251205145e0a45a01400307a421400c0c2c60f078982042c10389030700d81c104c0d40c41c94801e44414000701031003141500c0c0c50a01d070103503c0c041000c003944001141620004035944441501c1a541303442e440900ca14800d480e84003124a00e5409a003080c0b0009003004040006030a00b14018a0704941140e181c03036031901e05000d00130f043c1280c034070b00c003040500078561600524030b0803107210003d883c2151100c8140c1da1b00c003048000c51f82440da00081c0d036580400d015803010f510040c1c55140482c1501444050f0540b0407515400586c04c20044556031014410310f1402c01302d500ac18101400d200003046a1000040d001d0700036540701200b52411160003030f4807805101e420a000f02681085400d141c0d007410400d0000303a07014001c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 740767482 1250 740766232 740766241
    0xd0203060a05090c0a27200712080609010b070c09020304120305061f08060303070507030c060e09060f0d02010c020a0f0e0901050921090d08070b0f0c04120812 70
    0x40342c00141c820300c2070380200c03032075040000b0800a0b040d600f40715006542c4014a1a11401c00442443c10911580c0c6d507008100d00d08413004003840c55000d00b141d1220894045000710400c50b04c42108020324107946002c18080c18140000703540d1190600c6040c00700c084c0002c8103000c214001c2e401000505414a0071074503454941450300c1c804102407640360001349010700144051070320b403507401d082e410308038440340120400070000d031414030000d0710141d4584800c0c4100e0340054010072814010b1803260f101076011600e031810160169025216080c401c116120030060706490741d4042000b4030310b044492100440d0140010799060350100b001035000001032601007135011005948500b100c008e000d03007245075a1001d0545089940641d02c0b1003460b08040f900d0b01d00100843c044030380303040d6021519440d000849002a0900700c20540071915038202180d140d050203e80084a980040700603143c500c40d00c0d010510152a2003103010f80e80c0b52030012402e8105000c81c41c07040e501d4261100b108810641803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 740768732 1250 740767482 740767501
    0xf100e03060a060609122f040f0507050306040213080d030c0807090b0a030209060d05282a092c06010f0c02090a060302030a05011a1e060f07060213081b01090308090d020306 76
    0x910740b5030b68040e506040c080800e25003cad10405105071215655141582c48501c10407010f944042d00d03100359048160000305000b0320078041ea5001004135100010041d003c42405401004010700301828845500c1c410050f080b01c1d50100c0e030702a421490300503030b1080d01c403002400b940140d56540c03000a2603c400c0040004109003c1c130390310b0b43c4c040041d0011188118440b400c0d1130f4204448848016042403200c10040580700c4144024a03d040100395580c445181444c42c0d2030140d4019105890300248848a0306801c901c250821004e10f00407146110100340a4401c0380d0381800240150316010002e1b8034614141c1c45030025607802003e444d0000c5140c140035010b04100080610b1030604424040107030300c0e0050741e07154448403008800c0c020f81c1d1024100b2005400024000140c0e18040080e440028440e20050084c020591800406682051070080c600003d21007004403022106603103a51076a000304488080341d0b480440c00d95035420700408510101d0031080000e41620a01c03050144401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 740769982 1250 740768732 740768813
    0x3040f05010608240a0b102f06040b1b1209010605120601180b0406090e0601081204090b0301020d0207080a170103020a0b07020f100e03060a06060912 66
    0x50003100240b00703203a1658801070320b4901048640e245001c4120710040303241c1080c050740d64084024100042c0141d454404901c004040c10310303c0000450901b00e2644100b515500d0000c403405c000ba43c02d018183d0514207941c1d500025001034a019448400600074210000c1d840503000a03440078262a802420502019014103640c0301c95103500307100c004642410b04000414141400c103005200591078420a0701e041b04c0f5160041910715140c09984070703242c4960007000f006244429000401040030003019041c04030607040b440e4940c002d5251555140e0200041d03a06403041d444e0006880840040001d0080c030408403458049800840e0500a020540c0c0190586000071303142c007100c0840c040d44555003000c003400000d5220001103428413580c20b006001d404240c0c806452030317040f900e83c00002004c0c0803500c43c4c988009000100001050b080a00985400c000d001100303011041c20000007030506051400f03140c240104100504051020410740136460740e0343c061500503502c0c680e03101c43d041c09 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 740771232 1250 740769982 740770013
    0xa0605061b100e03160f0f12030f0509031e1b0705030706090501021504060b0d05030307170f070503130b0a0605040b010e03070303030e030906030a020a0201060f030b0118110304 78
    0x14040c100d190b10052010b4041d2522500840780503500e40800c8810300401035a404109580d01b2140b05a00300014600c0e203501d41d840340c000c219914200c0361110b070040a40c0c0c1c10400444c440c50400e405c1c00408140041070340c1c407404510040d00080c3e18840d6190209004000440b4180c00c040c80d007501908001145240c183c9006506540303d1a883d40070503036840840c1c0c86000e00583c0b00040c2800c4001c0044081c0c2c0d08148210004203d960507000000c0210040200a40e031a80001080c42081508000700400c4444292945c400c1031800c0c010014000030010f12000900c540080010910520501020031466202000c440d032800c04450041c0200018022280207a03c0d10030340c0e0381990700403c0c41c55000b00c4010020800207046070b030308401408502806070780e240f0040c060b00e191940e0b16005544940240c40d40184c0350400b40e2402802d44825502203c0811140f40c000d001250b080034425041d179000d040c10307804621002000703c0003000a07814107201c0780d41c040705010410001ca022a03451 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 740772482 1250 740771232 740771287
    0x3021c1d0313090c03020403050f1510030f1709090406050f060103020309210d060305010b1e030709051e01030b1608100311060409150306150b0f030a060506 69
    0xc00c0c0d0605055500e01c21104560410b411450003040402160f03041030b80700d0012442c02504251342c82d030740d03d0701d00f007200726580c2159004001e603401e40b1980e200d481503004ea01031070805011403850301c0d070740d040401144014000c0c50074951800c140503003500440f240914090a81401d030300c0c0904040c0020f02040e242e25560b40c020394042406980319000366030150303d80c007025045c000c110140c030311840151103d06c0c500c010802c0c4684003a48440e4410003008601030030012420408060070401040101e00c00b14a9084040c11008140e460004000082d29030700007000810b0780385c00d07084034100018070804440c2c08882d0b00c004000c002011040c28024080303980a032120040c2150151859001142c00d5180480800d1040000c28400300c42240500710103404245080d0f103078840c000613030348840c1c42c80c201298850b0041003041200e2117292a1190380c00203a050041c18079802041c68441c40c500f03034681ba040032000c5400f074a580d0b44803400a0a0091241d6039074540c0b60081c0c8034026100d10b980c00f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 740773732 1250 740772482 740772521
    0xb09030408010c02060c040501030c090e160201060906151409041a040b01032d091406010303020d0c08030117010b090a0b01020c030c0303070303050712150509010b090108061003021c 80
    0x4005000048003401858210610b900b1f09090200440041441c0301500d8100014498006a00c4944a402d1400ba11001161605200070204060709640550b4070501106190010420043c05c1038801c1da00130307035443d2034505811040410000d0702409800321050307229140201d50720142040101d4403080c00740544040c001400c440c00154226201c4204180c001201e081407403030900003100d04942d405810703107000114448962112030181030750000d03d50b02035101000500c14150100104101c07000c2c1480c10078000d4505a840380103034007061080581d0b10f07100b9a16104110801e400c0001800000b91101d1442d10340001c4050151160304019809070041d00400042401c000ca00402c0405c0c002c2d0096241940c107507000c400a000c0185500308001d085504000c41c0c081e14040c0c0d41c003203410a50f94540640c140420050020010707486100502ca00b001410582d0340c01035801c41d401042110100300403140050300787d02902c0344004124041c82d000261010350611a484500ea940030380c0d00c01c62 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 740774982 1250 740773732 740773751
    0xc03190c03151d161b050705150a140d090203030a0206180106050312031e100303120c0f0c030216030c140405090a060b030111030c0d0b1f12090b0903040801 69
    0xf44021980c9812002044442002404041c1c40e01a544132000003464650310303c91801d160300413410742d20401110250010f9804210310b20388240c04009a1010008051030071018000c050240040e22018440c00000401c02d1101c0000d9a070001c214590040d040c0c0356540e140010094036542d003100d180d4455643d0311a8003881780300501c00c2d60701703840c4050014003810051110310142c0d900300800da500061071101003441416240449580a400460740e800101c50840c40e003c0d0440501e035a440810070b14061055a19550002c000380320034055050101c0301c0403490034101d0800004034182c01010030454000401c100d410700a030703021140c1561020790760086400812065460a43d940074065120904800100d50b441e8884034a0920003400080c2602442c108040c0e99001141d0030036200c40c01044500001d01d081c060040a481c080b40c0c102d0202c3c00440c0e60398008552101c01c1c4d010000310f846408074407003040d4419014183c000c1c040ca00d180c9810042d06940354014015107005508008911 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 740776232 1250 740774982 740774999
    0x607020f070513050606130608070e030312040f0510110403301404080d031b020a05060a0e070b0c0a05070614030117030706050705041514030c03190c0315 68
    0x3030094902c000c010700300008142c200200a410003074682e41c0d000d8410050351741011104400c04000b088240c5030385055140c40100a80b54030383c070b81c1e41d0704d000360810000400700700d1140c59415403081d8003450354808002507044c0140382c0300d10440d45900081c9001f051200c190300d440045c0040700e20401520300e8151607860003140070b9845100405d40840c40c41000d18020340255078200c240d4030140407642c1419580c0c1200d40c41c00c400050b165002c65a25080409842c04a01d140920aa00d6000a118070401d641d1a1a90340d20002c0c0381d21091941d071070003082d08100c18014030b8000c04020224a40b21409080340700e444d05120b0000302c60910034184c0c0012040d004102e41c03c2e20070004403407181542e10b004040300e1111500d218400702d6002c00c224400c001016840341030701603080c603658030f070310742e4200200d00388941d00d43c0c41c0440038070019160704001c850f800c504483c1c0c00301e0340c03000f466202c0e10740300d400c55402d4040c8048080101c1c10030800031800741d0f040d4030140f2100c0001c90a030990b50b503103241c0d8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 740777482 1250 740776232 740776243
    0x6160c08040902071b0621050f0103061a030a140f12030601032307170646060c0c0506090d031d060f0415180e0702030f0a020607020f 59
    0x1452000280010452241c10341c0c0640135150117016403905082c03011510184901c41500418040f0b8501141001c00c003010050403800070ba01d402081005043c80008411410b82c140f10080119442e90300100200090000c10f290342a806005c03941c46040d01e00e050141b84030b2003421042d0921030500c0f00c08069000054000f0075081008159146807191801100649070010003210904a420070b602642c6800d91074040c8560440e9541000c00902c41c500c03421840b030043e00c9184114541301c076182d15119411803031061080011451408003d40412051068141e4601468018800580064120303080490a00014403421855030501d884004004950180360a000d4201d5038240d1880002030090b00365419503551000d02030310303941d210400582c1c00c1d4440311003000520300104081108646207501c44103044094100241d640c80e5070900130340542c86622541d0b4000d4000340101d4159030091084503400207904403469621003c2d030001030350300c0c10280d4416005214480c0038001c214000b258 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 740778732 1250 740777482 740777507
    0xf02120d171b040602061b0a0e060309010f11030a0606031503080307110601080313080d080610030b190510080907060f0e03010608060601170402030303040f05030d0e0616 75
    0x886200c403038002420600301000c0106403111081e519000d4040d4411044003070f000070492a070080201e0302e0304018051003450310924010410034140b0900c4001500001c850300500703025203041f5244e68030000c0840c09004074101425078949000500c20070500c862009503c24007103032000b40011351f84e5034012002c4a103114205103071029403200520000c1c0b882c100842e00000d0b1480e004482c0e072942103005091000a07488001194400110644d880c1c5c00c81c56020010078144015218911000782e0241400c000109030350302c01c40d092103490b5211380c06a480b0020b5088081e00808444240d4520f1206800e842e0007414411499508106c24062040342c07680d10401c5613102a000040c035080d020340380141031200c4032051081441a100990300e007485a2001040860028440b50410400140c0340c00b14540076011860301d000708000141e14000100c0345c12603030003002038a115100e4101a81140900ba01c14107120f420b04562403403840b4009405da000c0c0d5140c031514070401e4500031080d60044031801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 740779982 1250 740778732 740778737
    0x60b0108010e04110d06020c0105010e010f0605190509030f06010f090f02091e0a050613090615020a0803060d0605190c0f080a0b03120c01060e0705041202040b060d090f02120d 77
    0x51484c44034180a61405c03d802c1c402d00d0094104080c0c0c1c000d1a0942d60700b42c000344119007080004010005844602400a01042c1011468601c00b20000e01c2000c0d480010001032050010703202c891074904020350b800502840054503210758441018982c01c1c18071344507507000b860500742e6240f285142e0344200d440030b060080468590580186142c0310030101074003a5231b802001008001a5a02d40c80d0007041400e1072101c072050014202000141281e0040c0c01c5101800f030110b401c0f00c0da2a40008141400d039401500c2651642e480e400050010125914020301d081c0c01c00303040c4102c6000541140e5601c03280188144a8206d08071000c80316100801c0d0050005103902d004502070610507400511101005415280e000c1d24400b403001166001c4400126503a40d1181e082114665210586400000e507241c541e00e03007441d04146016451700d410020388516519004118203541d0300d81110390b4495511004c1c4514003042c04c00785083c1101d59000e0b80101c0f81164082e8010202140c10b1000b02c0164 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 740781232 1250 740779982 740780003
    0x3010c08070c0209040215180a0e0c0304080706020d0e030a0305090c0105090f0d0f0807120903080a11070f060309060b1504060c03020f1504030e011e0e030c0607060b0108010e04 78
    0xc3d020482d40180c05801039801c010b01d1078540300310b00780f00801000303014140342c101e060400704e55090000d504c1440d03111960b100074040030b02440d000300108072600140c010405d5900c804032410004000d10130144c0746c203070482c603082401c0c102c110088003401450002d51800c01450740e03030514260300e4902901c40d01d40055410031600400386083c45805100040c09001e20140742c100b641d9411000003015029951081e01244402c00c00a0003001c40220000364036045a000340307075a1324000f00c0e010b0420074005115a40108012010080001500800841c15895101a5a044050020114030030242d031a142400c01c503440764280030204129001140c04170500d01071070000b0407100700c003050900314110f004001407500841c008104550003c07400c01140388203404c3c18a00508102980c56000741070004680c917048881d109101901130085550610f01c021500000000b801e01031804442d0b640b110001c2419414041c1c950f00110354070394284c07580310752a62180040c200c40307803048030300401c030071080f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 740782482 1250 740781232 740781257
    0x11a01120216050a03030510090b060a0e0d050d080a1a030d0f120204090510080f070303081b04170105072a020a0918020112150b0a05040f120203010c0807 68
    0x10340d40100100880100014660a603603075595040100c60b03801580041d0311760050020095160380448020700c9035490400080d400c070030101707009008904c041c900b4407030580ba1072561520341144d502c85180e881400d88505a10000f000b8080c1d03c802d5039124601464501030302c00d0b40e41c203412828030100b8024001e1040080d44030085030304140d808400c0d400c000c05204031842c0c8111600251000d000075041c0400e1601d009000a02140d6055104400c036920042c403e44100c04042400000d1f250107190200b200c0d07640440f800e046142241284180c0751001500103041800d0400000004a00000a2185849000c01294280303c0034801860700c1d18811008010003585080f103480d00c80c0702a00000490303543d44120022640c80214074500c01c031414400758115a40814801e80a00e4443d40400031803110300351100d2070f10700038007032015103030300c00111198000d01071401d5400911607981650644d42d1945c0c2411281003c0d048124000e40c24489400320840c0a190164411800350f80c62041c4000c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 740783732 1250 740782482 740782517
    0x606110c0907020c1e041b17090c060d0608010c08010815061c0503092e0e04090f05070f0e01030809010e01091e0614030903040e04051c090503011a01 66
    0x360010b001d511640b0b00e4a45541c0b2505d0350f1400b80740c0800d90358940b1201031001e00056400e070142c116080321850b5400301c001a045040f600c08071a41212000042c0d0398940364620b0015061803203981b04c0030100d2140728020880e0888019541000e0080c001d04440303007415185803800780111002500060070055020448844241d072040006084001c0c1441d800c0101c401c0d0f5050320004c0e10380b50400039000184e0b08204ca00c5454040810400e282021012034107002c008a04141d40c4d000c0144884200490340d03229080b1200f942c0c0c01101c820101500c070305d01199203030400e1180c50f05406003030f100011100040350809040340e80040c1e095141c880e0241c01180c1c10059036100d2418490440390100314a43d05440002509264000320024241800743c0038020400703495049034949010410091b1010021055030103d810031200c209050b10b56203401e034180f448100302600c2d455140454001072640c0800c8a8045400a074001c12130b02c04034207203489030031442c600e000380801d803d407110b005a0308 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 740784982 1250 740783732 740783749
    0xc030309060304060b10090602060907080c0411070204110301170607120c0c150f18020604360507080f0402030607080603010f0e0715110601060e0d05150a0606110c 72
    0x244602c40024210181701e000841d03908000c8603440000e582c4d010280509070b010000503401503009801410309601e003c104940e0b40d0008060a13000c2c0c2e88071810380030702d145110203a1b415540e005006103c400340c0c203808021250000d00c07487c080003900bd18000259030020400b00d0182a0503560f014034810440d803410007800c5080c4e445e1040003240085400468003501204c4010b4910b2080494152a0141000192081e80e00003d0000d68810340c4100141d03500d4044800301c40f01d12100217a0408490650b14007182c12031800304040c20040251000d001080d0f0100e0301c00d541c80d803a00d58640d1141002c0300c50100303080714001d400d41d0003200800c00150268655a912003001000410401c0618202906940302003140361041d5200000c1031003011460a240107030502c0da89811950101d070510440c1d80c500301071082c40c1c1440002e03400710711142c03101d1584800050308901210464803086111030601c010403603007100300d28138259003c81c410348108045082101002c005012a480c031104204400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 740786232 1250 740784982 740784991
    0x50f1e040809090f090c062b060f0305070e070c02060304061d030d06030b07050712030b0303070b09151602071e050301090302030307030e010606080109150306050a06050a05030c0303090603 83
    0x40c00a02106001d5510094118030a915507180c415050506414546c545038002031010b12510080c0111204407050b851810105081d040000035444075482c42c5000500803a045079514003103051010060220000d0100c0844d406040f1641444e900c8540880b95003d000300001c1d031018042000c02d011a400d500501012046121070490035080461b016180d90310041685000e43d481d03802c01c0003840b0621000c1580b0a205003801c602c0c01c1040c0d9500120096000b0100051554400d540d400a407002c105540030319074007000007810b6040c21a031a50342d070310000d450080314900e0000080d10381405900504c006103803c3d0002c050490a0a082a4001500e0a80803641540e124400074a9680900984088034040d8000e95501c1c10080402829600d444140f84507030380c1008010400d0560141d4940d0440d1082c0c40f00203024030441b0b241c0c114102e071075030002c0e02080c00c7c04244244c01400364400801c0b80c008803445444990f889060584441480101503410380080c005190181403d20085902 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 740787482 1250 740786232 740786243
    0x702010b101d061c0e0a051504030504030818030c010306080705060703030e0604080a140307090501050c0114240409080d0905120f09040b180604020c210d050f1e04 72
    0xb001c80c4802141090308142c040305400200c54800e000001c81501c5141c03980101c8601522050801d9281c0d50390b1142e844d507001c950201c2c1c0c00000703400c1c14403403425640515444000950f40f20f00f07401010702d5141c2c01040035803090142001a10a960280c4140c40c02c8030b040801500c42c0510f0a002c010843c0c01440060f414980c4462504e200c2c2c0b041484124480c0b489510708075160640c084c00102018921422000e440c001001403010f6035070005520780071a2400d1a150303613a91b680c0b4003081c0c00b4046d5405480e020114910501924658510755000e403003a00380406013031810810100826147c0880018021020400c00e06040041c0340e00a82c07882805401229020000d00e04c203641540d05c4000f01b6200e182000c81c4c042e480c1d103400d005140391208102c4410036141804102d01501c034102804044c810340c0d0024040c96006014400c900401700310100140700900800d415000c15807200e652204020f103000001988802c94160035809400c20903140c5407101c2000d0170080564401030300503941d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 740788732 1250 740787482 740787527
    0x6050601031d100c08040b0c030703020c061018021c15030203030409090b0f010605030718150507050d02060c22090911120102030c0a180b0a11060702010b10 69
    0x605003888a009007119a10700804007040103d54001c1110400d005100c1000000410311000c10381464105401a0800c11b01650304d40301c2d80702c01d4000340f1852030301012a000c0c110400a07164001c180320001c44052444292309078201045c0d8604900c18005003030515a0b03400028120480c541e0320040855141d000d007100b036241c507900080d2464104d039100301846900c2c3c5106030204514040d66940044000d0028102541852005001800000d1000c8200410040c200451164201d2140000c0c40c00c1d0143c2117032441000360091840d030080c0710560b03a5215030b810180e655031000a074503228151031006641010340c003407410342e0203500c0c40b900200702e510000d0000c02c0d140c006119070340310184a44141a481e044550030b01100501054111800b42d04c180104031a100300038049420700c2090b458150015641600c030031468118540004040030400b00d100304c0815005424802d202c0000c0c01242c450307940b0315104900340e4a1034035080d60480020020714042a021b503c0c0c9030f0b0340040d85072a204 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 740789982 1250 740788732 740788751
    0x2010b04181b0f0e090f0c1012140106050702041506020d0f02073c0b030711031605030c0601121e060e0615010f0801030b0c0913050a151d040605060103 67
    0x90f50b03441c03660000403880301c0080900c640d0300d00c00c0003400c11602281001d030a40700c3c000c40000750740303074a444d0303550302440200a1000c008002c1544900c00c10368011074101e545584518005045802c2818200c0c040c0e480c0240c08000c0070b11007902c8004507880c540c018a80003e1104c03003241c1c070744a03028002041d41300361030011507420030032803100d0001450410102c40600c1d0b00d00001075520b88565901715902d4141c141881f400810070110399110701c55040440d02c61070504a810320b180728481824600d03c102000345000c129022005001004d03001c1c2c2183c011b03980381d501d0382d0000e10b0300c014020103039811013400000e40840f9400f041c111a005090002d4550904d200c064184401100c201e401d1f40481141e00001d982c018204488074805860410895030640c0c1e01c11940f45005010082400004a503c03406a525030090024030250801c0611803410901c1065000c1d1522412175402d590b61540c0105485c51803181e1070340680e1054001454603240c6440b140c00402d0040c00c43c604040e2100382c1107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 740791232 1250 740789982 740789999
    0x60c0c060c0a05010e0115091e0506120a0b07140a050a0e01091211010807030606050f0f1e0409180b0402090601110706080a0e01020703120c050d14040302010b04181b 73
    0x40036903017243d80045400410390420b00e0f80c90000c1d80100b89158030704410031200d45030412484a031001c0c0414009170701d4035088009000325460b030000e51064812000c0601c200003800348698058003041c3c0700d6a10b0381c02c030504401f040307001c1c00c032610740095002d1100411452040c50a0b42100006040003850305c0d8540d8180e003c10b1100380e0381550041017000c1141b00c41e583c00060707198001214074007042021b00b4000002c01511a007140745501010210782421002d0840301144c08880070007500c2c442000e450165002140c2180c4680c1c1c46e4540343c054211200140c4000455507241e100c41201046d9480c1c0d42003100701c590140402d410842c050701951a40c0c602040110058103054031a0505850071541c114141c5a500d800c941141e40103114107400207410201ca6140f10015400110383c0c08030b004d804403058001c248004000c0c41c10a134101d940f980461004a000303e00030740c02070140c4000e070000d01065076000741d003d00c104907070640080042011990100103901000b40a000025641c2050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 740792482 1250 740791232 740791241
    0x20a03050a03110304050a03081f0e0c0f12070905180601210509031201081b100e0d112d0f030109060507111501050a140301021902010218060c0c060c0a0501 69
    0x103d0345940000b07400402c0c941c00481c100c0e13011500300d80c490030030b1402b05521260f00c01184101c0c0118950080801d412882090594001c039141145160b25014001e0007a0910003040c2c8035000890400300c00400c190400d0820300d84800ea041e000300c0220f840302001110840b002800a07810403079065003684040c10640184c41c00b4040c00c1d0019a1210000340000200d4501a80204a6640228944907001100c030015107040c200c03c40d4031860320031042d03000b40c0c2c1100840a031164044515003848003002100156000019000d864944512143d41d1110203441e1010440006681007003550b5040307858410510142d20f44040e00100d0020800c2d542d11050740e01c19501c82010400c2e08110440c40c580410042d4101e5510072404505545000041401d900e114000c2c2501004c0d40341c81403400e51400d4040f01d4003241281c0c403188103510b0014009000b50803100c0d1000c841c4c0ca010020000d41c0c078080b400d4840f000040000b81031414070300c408110041e4850344549405004090b803500c0414428401c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 740793732 1250 740792482 740792491
    0x20a090b03040204021e0913090c0e040302070e130303110c0c040e1504200a0b09241b060a230603010603080403060f0c052a0309041109120c01020a03050a031103 71
    0x50303554590440b8420071501d55501c0329007041d00b500d000920402b18812220800480c0c0741c4040c0140c69449909080b8105941b60b0091009094000c0500c038203c10080142c004140c042e80d030800c2144d8000b0940d000700e2080c40560301c0c1a6005c11240700302450a64000501100d0503011038039022400b800c01d515007003040710b055034090b01480b5684000040da0742899041e807400c540c031180c010b0900c0e4102e645c2d07000c0c4500080c0124200445c00300c014624a0b28441c080e55070700c5034144c44000c4480b640c8000000390022006500440c0e001c01c0140b40e280c017a822104e0200d0119010b0282e01c185050b0404400402c0280e00d07640700d24000000c03551480040014501038280410050015849101a2562141c0d0744040110030000164034840d000a143c0140304282d40304003946000600181c40c50060403d001d601074038149405041c145060010040000151180710a8940e540030841d103a0305070308410750143e0041c20407000040d20400042c144043e950800081002c800d80d141c039007075001101d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 740794982 1250 740793732 740793787
    0x130615080108070e0c040303050c070b30010501052d0a0207090c0c0b040609051507030f060f0b0a050f040f120b060a05100c05030c01150608010801020a090b0304020402 74
    0xc0103001044050240310050003200c1e64050072400c000386280240d100e0751101504001c4042080b0109040510040b07005001c9800a5038840d8400302c20744511559051000051110213101c5034400b14415045d05c1c1200c90503103031a8100444038500601d18082c148001d0603880b1031401300700e08450050040d108104045e4020440a07090020f10400c44808500103814008500e44e20400170780140845913206901c1000495a01d41514116142280c031300e03240c00c1d00d001410b0402896591540c010100c610140c0000d01055036503280c1c01c4006001d0740152130f26104200400071440380100014040b180428400d0b030720302a034403d11590041c0142d04a000c0c2c40040d03d4a80d0244803402400c1e0303401c160300312883c9043d1447d1500040c0c0380001303a108401406000001c201c06c0c41710500942e40200d03840c1c03000340044102010011160000c42c051b10004c980a00700108214034140b00360786410202e911a040000d0600b140c4180303a800040c000c982c03180d001c00403800c0c0120a06002d01000c9030300b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 740796232 1250 740794982 740794997
    0x41b0f05270106030b064b03190b040609050a0c05040e060904021212070c0b0c0715090b19032a0e0d02040e0714030a0206070609020a0509090a0312050105030606130615 74
    0x307d64081c6402125400b606a000700c600e900c01940d0561048903044980c1a0b40c22641c5030007041d07400e02400a51302516442481c1640009082002d0340215120b8801008100190f003080001604e03136004038041c00480011180c00502541444800150000d000501c4002e03904000c903a424074100d0b00120340c1036515004509042003020f080e00b50009004144030703040c28981301450780707a503030481e6100f00520012504084081d141c003400301c004c00341c0454150a96500d0160b003030218a02c0d2031031450400a4945005103049202404041600e01200b280200c1c00c0b280b010021140803198000c0d0300e500144c06540840140d803640704542070b188a11018151141c40e24000034443c082d43d40c2441d0080d04501e81220040c2e49a43c00c8030000c0f60320000000301d400107400840c055042c1074010540002e1540180f0842e04c00001e4100081d910998451002c0d008824501c01510801c0c4151a0141e1029003c600540b07441d5a42021140c4407080000b41203a40d25540c440c0d04004400724004650322 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 740797482 1250 740796232 740796307
    0x1518051b0d020105030703150f090b101b060b0a230f0a080706080a0f09081207051206370f080601030503090603041b0f05270106030b06 60
    0x50a081103400481298004001681d41e00080c00d203201c000d0403402096518011030502800300c810000151200c0020281c00e03640b902800f078010010782c41121300c240300c1da0306542e01c254424408200c84001d00100d81600000c0c59840c03a0181c10080b50f440e5200d051a280031486c095103a0b1183c0d51400c2d08212101c200380750382e05000c42c0d00c10011166005281c24001480b149900156003412942503151140c0d082c0e0310000c1000007046a8a09110720302d0030300c12410144098030740505003081c841018400d40d6100d0440c20b448920950459818200c4480005040d6181480c8144015490000050340303800c0000c0c0d05039418150400c4040000c000010b0074000d5540d5094501c000d400300740020007413541552140d030381d60301031059007030303c03e420000c009400c000c0c81d040c103100454088081e10b0303210341d19480c41228a400c04d0080c1c0c0c2c001c441e041c0e05001007140d0070700440b00c4c40c140c5030000042a424004214007402d102d6120a410900c00c1040c1c0965800d02c0b020400c0e80f60544030b41d2990900c0d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 740798732 1250 740797482 740797513
    0x6010e061c0c080412020c0102031902070b0a031e1506030b1309080409110c03040e070504080a0510051f032d0803040204050c190509011e0c030212070b0103151805 72
    0x501c05c10707840855105480c43c040c02c0e40c00004413500030445001c80301060b00c081380124035104e01d6811047c8a19004620011a25019000030b465000b60900c6810800d0b1421500001c40c0d40b000780c4110100345040c1d0400c50107000b6484002d4041c2c02810100724441a250444141c03280c602d0b044a40750350000301000645072920030944030001c92802079249c64081442c280d40ca0085000d248100e00001c0040b440d0b241c02001104d008007500d4060b1103840c1d2141c01d00f01d07201e40c0c0040a1035280c03403c1c00001843c8000142030326100d03144c1404c41c103031002d0841d29400a02d14030f07064a000929660030303090000c0003042140b1100c46120301820f035603903c2c051050009954020b4050070b0030803818000200051188940da041130380b0103180aa03220100d600c0100d611881410aa0601030b080c0200600700a500400c1c44824501a808032100200b002020b50003e2085c41c8001e080754903c02c00500001d01c1c4420f030022203240d01880403c4400504914040e80c40c454032044940341d0150340341508044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 740799982 1250 740798732 740798753
    0x31118030601090612020f0103061206150b0a1719140a0b0103110d02091306062d05040b03090102040f1e08060717040201022b031406010e061c0c0804 66
    0x501c3d1040c0011845e2245d1000d4601d6602e00081c400d1f03203408081c1c2c103a40d12961006004059000705405103881c40c0c02c12800401c1d8480031a504402008004140d0000620460710450719580d03940d041c08580d50041401440040c0c0f8810714251242c10200c20383d12a805140c10380840c7c130071040c1450900001c0310044400ca03d1950303041c1030900d11a0400e4401100584213440e001c181c0c096075807610080081c0d00402210040c60745d207850120082404c56000301088070842d040c00515400411807620780001c0306040f0b407900001442000144580d88080020751b402c400030030300250600e0f4507041752500103170701c41e041080501d010b0909090440c00d62010701c07005104800182000d0704000c08024402201d0825102da214503510205085910802c50f038034100000f280030399031000180c3ca038030401e0030304110306600090030402c4402441101090141c0500320503150506410f10b28402d10900f604150300e902d82c072041030203482c00049858001c0c01d1101d0343c15900c02e4034a1409180101c0704d10f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 740801232 1250 740799982 740799989
    0x9060e0d2a02010c031416080a02060a090224090409110a0b1204110112050a02040911030624070b01140114070f0209060a1706060909060c030a020a031118030601 71
    0xc40d2840d0701803016036008060301c4003094262803c2d60003c80410829a00c500c00e82c0c10b200e2a0007850b101801c1400300880107480e850710260f096900940f502038448091780c1c11007901035030185048270840702001820716000000e50030a1300c01c1d41070a1540000408840c24402300b50340340c00f40346c1500e40c41841d0281c1884080d2064442d01ea040c02000000501c40390f40c010f1004140038404101044135a00400a03441060007590b0700380300c140b0700115801c0c041e4006105120f013903804d1070004a18100040c064a12460014210034000404180d00c0680c042075404908400141044040c0c0418100a42c1e14041e2421f026031101c51128600010088600a03000b0600d01809008a40c00190070b0000045050340480310036126072500340009130b80070710a6220400760183c00101c02c10002012452603c181c008030341c4a10903542e0044019250344084940400d071240400021f03002c0b282a5000d02114012468000340250702d000c043d8205c0d80c0050010704585060f40da8040311450300f040b119014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 740802482 1250 740801232 740801297
    0x1020301050a0630060503030a1e05070b040b060d080d050720030313020307091806110c06010b070c051c05010c1e0507050a080412060c050403021309060e0d 69
    0x81c9242690450b44020030304100258008a00c4c8111400503802c0c2c01000103068010f0569035650364040018040b15049108030f1004440e004000c500d00313014a00f610500c54204a6003c41d6945c1d59940001070000180000c0e80034800388c51400c04a104040540341c0c000041100003068108803c010309030078007084111513a800109824001c100c804802e81e40c104416180b030412000c25880002d051021903040034021500d002883d0070440d40e0103e020a25600030381c5d04012076034683c4000030042c801d0f80c16454840c0d0103000100310a040b5040100000c0d0300070722a1805190712240012030f00d07409550491b146402105901c401d00500784500b52051391241415114500040305052200e0900c0e04080c0600c400070030841d003403200a112a054803503210911036076070b41d01c41e80c690000c40803408081c1c0f109841c1210f20651940620100d50599800400c000c1c48001c10204000103040300c44030403203015071940039071001c41e4810040303180410b040f80c4908400300000007001010802003021a0503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 740803732 1250 740802482 740802497
    0x1e0b060d0804090b01020c130f0516090b0d0209031606110c150a020a0b0c070516050d0f022e0e0a0f0603020318161802090f21030c01020301050a06 65
    0x1c4804080702d0444101c410003042030608800142d041545028449400c00071000d100c4030740c40a0740c0d005881d29034800c0001c00c2551500fa40e40c50900c04c0c580140404105448024000c030382004003e02040d0118400240c580607250303000c81d041541e04d401c9504841c203c10f80c2444210b4200b011a10b070ba4003c0c1c2c0013082c0b407805810000310803083c040d0407956904000600c90302c00c140300f8014880002d4019038152040c1c24144204085544200c2050300c45024843c1050400d101c001368000c2111030003454901c0e4502181c8403030740000d030070034800c0381c0c0041c1840c1518040c2000c2140e10940e01201a118030800c441c00350050030f402c030003a14180c45131410307400c00d008030003506111100780c410300d203001a00d0b95900080708170a103203894200c5866110781c503081c1c103020411108180c29500f0351910405440707900b2810405a015206040341e00c43d0914105004c1c9090034500308007410b80011145010804241d89182150b201901c0c0c1075075650008014003113410251850310080110740b40094 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 740804982 1250 740803732 740803759
    0x40311040519020f130312020d08010303090626090a021e0d080c031b06060a0e091c050d06260a080d02090d1202010c0806040e070b03060d1e0b06 64
    0xa082054281e11a4500c940c0801e08009264030b500517540c400c00d105400c00201c9071a030a008102c00d0111800c40e00500c90700c2800908140303d82280e90480b985510307810215810b00c9015101011075030a40c030b448008000700301e250303c04402c80a07801040719070090145181280180119510082551914031240d107104802c0d58680c020b102c2c1030107030071040386600c40b007184c40303885d085104030300101c040124040141c2c00601030115100d030041d44100c500c417092a985005040000f2411180144103030068206441c9514004611001d80402403405a00e0000100c0550085940c90780245507902c56050b103130491b41d505850700540140c0c80784010024003120344d81c0d00d030040c40355400104130240c0120303120095489258400303040c0c0354081d010060b400700c001c0c2d00900070920b071030191001810070380c00708100e414548116420340040100ad445000e00f0100305078020390001d040141c01c11100d0700c841000c5881c0405510801c505600c10511110260406510841014001c240704418859062 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 740806232 1250 740804982 740805001
    0xa08070503030f0f090a03050618010501062f0102030a0905010f15060c080705010203040305031f08030f0a020f100c0801060302120a050402010302160b1602120714070f09020403110405 81
    0x301c029003c50055a0399035004100d050106014808003543c01c005004000300c00c04c40c0108100d4400d074040e100307003031070500f442c1380490981360b003817103100b0100d904020044c8500d601035007400640b034581c0c4015070210000e001c0c02422603000b00d4030340010b0703035951750007100300042806480341c0400b0611042c412203020514010399070200e0311802d001c2c80182748494081000e0042a41d003000d412000854481c6000d040242180d881120310099a004100d003005680c91200781000c15101110021402c11400210710309180e402401041d007944503903100c46005d60b5040011108071444603501040c45040090b01910019040c3c110341e05050041c040503083c01c603a41240c6501c251000f0000c5125140d0b400181d0091003640321001008000d284d144c001d001015401c64003070900f00b40310000000c4c00d503200f00d885403c61003240c00202e00410958020600d803e9900d107a91a02005490103155204000c43c80f1004a50040d01c010350085800c10500c0421102030340c1d4004184c50600041ca003c541ca0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 740807482 1250 740806232 740806237
    0x924070b0403021c211d0d03050106110d080622110915030c07080a03110304060605091533030f07020c010807020c0d030e0a0e010503010f0b0a152c0a0807050303 71
    0x1131007205950342850244402e0703a0b0441c0b00106c0e20700b2082d0f403112504584000c4c05480c0074018400030400180c9012642440000c3e0303000124074640c4c42c0d946507101c4008001540501c042d05441286070040024182c4220380314010910010703010084c1e8070800c4ea000d0202101c0c0c0c900241c1e003c00d0301801000001c3c0c2907601128400e5610a0b1a0341d40c0d0b01d8002c0003600102149460f18407240c402004010800840d9804081900e00403074031511940c0da0348051101c410359804950ba04041044880c56191402c40301100881b946585240c00310342d60745860040c43e4000319041e1043c14400703000c3c000300c50f07018080c030000c180d420319107001076150407440690703950719030388203140942010b00701e41043c144a03031013481c490080200b49081e016500c00c1820642682800340a04c69444d0042c0103212080510680314005805080c03201c6051610705e4400500451100400a001c0401400c031106034410402120560300c3c031350481e90000724401070001c2440305411410841d4042c1200780400d940001c207 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 740808732 1250 740807482 740807537
    0xe06180d08190c030b0411030907052b0503180319020904060b10030c020c0906010c0803090307061d010b01080103051e03090307060804170924070b0403021c 69
    0x20080d0541c0c5904030314001d0140309440c1a0b079401e1034091420071a80c0d06402c8203c4c0d07940f0848050000e081d030300314074940a01c001c1c7c1d00c03002150311025041000d0b080c12080c0015054188070060351181e29078030004440050070500301e5042d00001610400c40c1c1c808841060300d01000d40040021880c0c44079404a1a9049007010303218031505400a41040b81c48c0e0080480d441003d0160082500360301c80140140c12001c2121015020381c3c00300302120b050074000c2c9c41c41400165140c4480000076102d00710303154005405450240020401d007404201c0070302440414070203400d000c24194464a0340d460844810f80025030406c0900e40042000c13403030018500409280442c20a28148651107100c4d2851081030b0200f90540500500000c000b50002c044a10660040d20340401480d62001c4940300c512403044802d500c1840f000300c5d07880345003d41e4107031950410752070781640c03900b0010740710042003a908a13001c0340103a0100200380740c01c4032a146608003034031181c28070201c00c50441107022186a020b21 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 740809982 1250 740808732 740808737
    0x120c0206060607080c0106060e0103060b03150114040e10150e030a03030b040b0a15030b030307031e05090d0b070f02031303120e0603040c15050f0336010e06180d 71
    0x143d0380090103c01d0086880c10044407000700017007560344001a000351390701c07030030140421728010340000c2803941d0000702d07403288030b2803000a0400c800c80401954405142d1400c04000407041c40003040d0380c2d0498403a80d025481c0240c1d41c110f00351401040c1c03140840360f503070030004000f440268204103483c0010310b405c1440d454100810803010720310200d40106030140c440c9600c505a000001126206101103000c0c03220315a8007404801c40d40003e1654a101e85180100003840f426540e6030f403d034410465600c004014a4101c2c6050305900c001042d800c5140c84c00c0e1280c00c5200c1c140481a500900d04608028850010350300303185455503403010100640c44054007818007a041e004403184121010040020002c040c80d4903410300b803d005c0480c00c154002c00c02e0600c41010804145402581528069083e452143d0314ad99610f5200e200c07519500030802805401100c44003d400304540d61000756010b01d000000ba000a40d81980e6203040d0b0080c000d80402e05142c291044c07056404110148400950b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 740811232 1250 740809982 740809987
    0x12050c120a1704060f020723010b03070303030c1407060c08060114070b090102160302060417040f0b09030a05010c0525020a0e1305150405060711030315060c030712120c02060606 78
    0x130705045028024a602d0304203401e01c0022a1010400000c0720b066145c503101e0420150080d140107006c1c00c90301015045a41507000c03081c2080043d1280c2c011803040800c80c50b0100c80c00003501424855030f00181c1c1c04683c226150301d0300120031544405e0b060b51110b0240781050803c4048041d041c1c0c244074541c0c1c064540d01d50203001801c3e8680940480b10b44a0310419590402c4849060003511203a00f41c03000c640032040311548109140f001001d803000e45070f0480e09008024507080e80600755034403c041042c0c040c000c008110002c2182840b40c1c601d1043e098032003035511641d0480340305680d528058500a050700d1503107810b0268458440231400c5d510303040c007006000c0e2146041003000c02c4103800001c0c820b11440c44d001007a00c81100c203050199100b44222030942e00e0710101990408860384070381805a00510026056510b46040840210070203030000b4941100da5104c00e085070b1018506541c1c3c0208a141c0800d03c0ba8007152071a50142034001c100040600880002e407901d03c090f184a1260a01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 740812482 1250 740811232 740811241
    0xe072d080f102309010603052a0a080a1e020d06050109031203151206020a0e101d0f0d1b0f03030c02060915070b0a0e0d0e0904080712050c120a17 64
    0x120400c04420300001000f010131507035648401405824112400c81201051800406840040d114451407106030540d1190500920740300440d902d600091807070700d0454a52405503070044900b180c50f2800d41e4408800350b5140b0084403010f094560f5644098100240d40d84200042006c5460310009888140b9020078682d80518044106902d590130001c5101400300740982080480d03401080315a4a680350301c0d40000c1840100080c1070384240f41c031000f0501210326800150300c80030b000400d0440061040d020081840c022071036149010508440b48001840304891058010041e1001000307200c1000040d2070440c1d40c001c081260704040240a840c2c045420901070350740981c80c40240801d8200d03162240704a0070039a185040543d018414145084220350415402017a0360102e03240c1c64030703a585072542190505c0f9014000030420780d0b60000503c41b110005142d081d000440e00e500341e89070b036200c0c0300504400b402c01001c842c41140d058810000d06400c01d412a00078640c9082d05000000309588 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 740813732 1250 740812482 740812529
    0x607021005090310020903010f05010e06151b0a0605090a0327091b08060a0b0a0c050c10110c01020d2703120207030c090207020306010e072d080f10 65
    0x50490040e605001d0740142c0720081d13050307901034010001c04400920000300760012010403214203028114540c4004000210740303091500407105182100c1041500c0c207040580c00c2c09140e036540002080d560010f45181040c0303e20b50040c40c0d080001c501c06010030159030755010300210080f0505103100c402d854080b06410151156450003020503703000e101e0714003224002203008c03010001d60780214040e00301040301424103a00d0013003a0703005180e005107803c1c00f912096079500030106080703d0502c00c032441c1c11600d48842070283c18072610354444120882030b05807038609104001c100c50b81194448540e030010b8580c4141d00e01c0c0c196072883c40e10545207041c2c00d0100410011a040940801a140308001c9050750007c1c46a04a0303000e14091000715486400c035005034032400c1c00c0651b241c0c0c002c3e0700502c100390358030070259040302e1541403454540e10070000c1501805030103908100515490507070080320790340201286a0242c03020507100302d91705e00b202140c02000c10078094140340c004120b102030301d0040f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 740814982 1250 740813732 740813737
    0x5100e09070c0f06050109150506161e0506101202010e0907200714033c01230c0a0c140f01020c03130f080a020f131b031a0607021005 59
    0x10b4000b036000c125181c0c0ba00b4881e002d485c00788124a1141d1402810745d07080d0000c0c82e50351007034074402408a0700d0034100310700034031440c1120f0310195116100c0c02480b5900c1d200070202a1012845180500440c0c0b62140c694007a400700e90f4040c04004500c041c52400603070f0711024900d01a00e00b151140640d031188007044a42050740c8040c100317140403140201c120010006094030803039450b59140102c600c880c1d0149a1a61030141d0048c01a026809403090500c0100555030001c10030810b2550700c455004010f02d096408400b10170542d40300702e00b440e00c0f1480850388002d5100030b5000046261034007000c4000e0600c09000406000c9503065209210700100610522001950607c0255210003c0c88a496141e41c03102d01c01480c80540c8000019120910743c0880e012a11020090300c40e000300c90302845004500c004039194441085500107103510500e00c5121025120b41c0708002420a502c0c2020342190a440c03411909207007001c80d0642542d4942c42116074a56040c1e600d00b50400b003501003aa21130 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 740816232 1250 740814982 740815007
    0x60a0c0203031803010e21181e010207060c120c05030f0a1d0103090302070603020a120c030b010815030c0d050319080708011d01170c060a0c0c05100e0907 68
    0x60200081061483c0384855105065030f5040f0001c000036000c01c100240e94104c1e101300304d0320503210300170820104121070000d854692042072608407030840440004144200200c1c00b1005c0189c6954540d0240d42d041100c4000381499003050102c1d4011911120380c41c001c420803a03000c22090f03c008504210b000e00c02c1d54034184880d44440d8840b80c2102c0041c0907180801c90120785003003400c0880e40c056110340114013074550140c010b00b56440c10145c0403130180d031090038044284214401440113401c2c46202c4c0d00f0501c01c0b0741e580000e203500c4c004001010003001500f0940c0707034ac81d03000480109a0380070811791413410b81114140c40464051500303600398052a0007104110a0a00c085142541c00024a611071000c82e44d514210380c5c0c0700c806000f11100c441c11181b800060705801408014021300030700c00710040401c2141d845401c9031002074103a5100c10071040009503481904010000700e0104140608001c64000000305c90421000300020645803550307125003441008541d00501480c2d101012 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 740817482 1250 740816232 740816239
    0x8090411030a0b12011a09180703030e190302010e061b2e0507020c06090d052a010507080304031b3e100f090806040c050907170105060a0c02 62
    0x1d074603041c50010001d1201c0d02c10140141c403107181c00c0800345410712600908030701e401c01d42c4c9100d041c800184000d01000a0010b040b036840d0300c440688096041080600642c441e82c0c034041c40e1801e03101401303154211301982241d41222a40d013800181c1e0007000c2140e0515003911065100c00075082030b2142004e507100ea850395030280812075102160320400302490082c036101e5020402003461044011940111040030040e0000540620b281c03501000030003080c2c00c01400c1c440003803090384515040585400c0141c0010200c0829412400c48051811894034401d0811a06200550720340070310900c0002d00040800548604250644814184010034107030000c0c1e0454154800c1100507203a41407038201e00d0100c1103100c0790a82d120b10b100001441340c5a000d4501c002007481c1d49000d664400005118078144030b21134a01060f130410800009202d103010b098196805442c0805101466001401c5041080000c0303500d07a80300110031b00141d045450540786240da03420600700c00c403940007403041d00075031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 740818732 1250 740817482 740817487
    0x30609050a1a0405070b0711040f0605120f060c070503040b0a08060f060403211e02061014010912110a06051207031a0f15070821011208090411 63
    0x1802000500c00107100e21030b00b020311000c400c1c0c820064800c038003103c1c010306990040303200340301400e041005411001d10564410920032542c400040c141c1d4012903e4075006550381104008510b441c43e90300d10801251005814000480c800c040d07124107006101c03a42c45a000a8041d08100040044400030300220700c51030303211044114000d01d240c0041d119581300f4201390b00c2000c000d00c2c1000886041b41d0303200005012500b01c0caa02c201619190b20000f0040c8150704000354455030f4005103000d800021030740644880d1034580e11081e81c40301d6a0300280c60024003405241d0840e60010100f2050341c1c07512000703c1c0301070280c1c138110320031914a0071a642c0201c1902d500148950b000b101410b142d401401c0001c0b05075403603030400c500701c070440c64146c0b0001154102582050034204c0350241c00c548050412081000c4070003000b84113500a47d800c4038000030024240304464104003100c00c40d40d107104031a00180d45068407110303482c2801d0340c001e0301e101b00010b0800c81c7d60342c448d4801486042e50300099074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 740819982 1250 740818732 740818751
    0x5150103090c0506030f0f090114040209040317010803120a020c0a03050c1f0c0e03010504020901050d17031f080c0a03060c1704061a01180306050402150d0902041a15030a060306 78
    0x1b80c100159100003603516290301184200606012301854122107071030318101503403a9000c004076420058030682c2884280100500c00c80c043e110414041e059880045030f582a84490750800000b00902ca000301d0392061001404444010800311008c0703405160807038441c01c0704180799090404c0c80803001000301c24585070ba88421000e800101605c0d40030307151b14510400810515007a9039049400940c0302421100500462908c641420081d80c002c00e1040d56400c080300500c017a40c0d10a039150107c580142c80602c03104444501c2d03080242c40c0010141c00108030190100740b0031402c50000810451300c8401c51b420a92280c0000212203900501509840c10541001c0c4000d0031900300b80704034024000c80d0003010b54002e0050591600c0c1001c0240e80551558443c8002048041c2c000c0764040b0034049c021201e100d404002c0c0118281d801c4d80007951911350710400c0300302c4100036444039010b0020000030440e503a5005c80f0300150b40c120004641d4940d6456960b0006000d2500000e10030b0340303028584d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 740821232 1250 740819982 740820001
    0xf15120b01050f2d100315050112061d040c08030703170411030a030e0102010f02040521240a0605040b030a020405071112030136020a12020d050a0f05150103090c050603 74
    0x744d02d2000c0c16209002103952104085040d540710b1a5484d01d03448074101d08006651165100381d1780b03401c0864000405588504003802e204800c0240d8440b1607050800784400d102009014030000c1c02020f00452501969980c058012811001c2100d079a0b104000001e041c0900448404014980141640c000307404500e4081c11421340700d004603005610f0b00c1c4403001801214401c5805807000244151401d203503a02c4002120a114118542d00e80201c4000e2910444100702800c1d00709102d606a42c0b0074076144050000311541e0740d0002d0700c03450815a046510307481c08522503070030b26019079001c1420398641100340c1758030311401c1404506114600b0210580d44021010714180d420101c03503009810400c030540501d000c03550b900c800ca800009500e5400c84580c950040000403114102003240c01c0c20001c55800320380211102c2c8840319251010010030a00e18031840010b0825000b00704514104085180b1411207903c0040e81455034545d040014000d005450100810000700b44641e41c1c9003001d180c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 740822482 1250 740821232 740821309
    0x12030e0a180509011a0607021f080a150303140c0c100f030f0605030706110718020d0507020a08031b0d02160209090f0d030c050d0f15120b01050f 64
    0x1858456260101043c3c12a406001d50080c020000c0101000c06038a84108951580809000c1340d20600c82d815010200d984204c000503c1c0145898602c2c242ca88440c2100a807a002d83d904a60307008410414400a81c01004009002442000703554948090032a050314003c05080d1305035201401d050511071180e44040c0280c4554055070f41030248004081181d8151040c42c01115407540004070284900f03031184c20b0600100001c0d030b00301c0308000daa402d44410b83c000f044241c031070440e40019441d41c40070000d000d22500504c1c0d503c01003113071000545038041140400f0b003810642070841407441101108000070380d500710b2245481190756281000c0315035078014041c84224010411a00001c26a0174085252102189001c000e00300040c004042100146a49000d00d414040248294904001e40d4400d15903600064100024966410344000e0001011070380074948540c03118a1010010b020010600d04640007a80c4041d00709003044000b8820f0305000c411558110707612039420247c41d502d07800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 740823732 1250 740822482 740822519
    0x5090405010e1009020304050c040b0a1205100509160501030b040b04150305010b030601060f0531170f03090402070203190b190b0303160503040801150e070203090a12030e0a 76
    0x7034002c1d00d1340c441c540c070240e00040380c0141690b0000c1d240e641090074503401203101144001c000c020f100da15038140400d10f8210000544155011004144445040384a900c0d04036582a00801d10310840145400b5614003501500b41050344a11408050351959001200c0401c00148103025100c3e5200c0d41020b0320700107101c1030f01e640d0f0034005a5055420085501c90503030322103680b04800140e402c1c81c02d4071030350711600e01707010464104801d00140102101c0103104040008201d69503840c5060750710030b41d26103075584211340e5801c008841625218000102c440240c800d480c0540c44160a00011f41004030304c103414180306280300e4101e02046803a820003440360320340544250f0542c1516100c07108882c503441e080d51300b650003001440031344480c3d041c805841900c2041180e181503211100103081d9181d0003000b0401210303501d803d100d02c0f4495900c0c582d0003000c501c0103504005119002861091051246201440c002c1c0340080600d841aa658078814001074486110160f413000465200450881c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 740824982 1250 740823732 740823751
    0x9021803070501050c030d11090d050d1206060e09040627060e0307080301051c1b0302120a0203061602070b0f0d0506010c050c040222090b0114120c090105090405010e 73
    0x740042015800784080e6000200044025800e00000c08101c10080c900c18540001122040c001d0721419640c400b03a100d04a4814405800700c24403201c80039040d01203e070550118a070030814188019640481c480c44d20303500c21178405500e9203035420800700070303e140362080c54440308080700d20012003400d40c52b803c45148201e008000108440500584901230004010410201040104050308d020713a501103c40700d0040d6441d41202c0c8a640c1d520013500c2c000340c1070811045000b002c00c1949828018802c0409078000609417151980e030009890b03c83c02080390411b01c807414000c2484a108011080261012910705660740e1041b5000d12415004485080702d69824800040c5055118820385025268424018a0001d64807070800000e50040207611103000d0702a0041c00380d10b230080070500c0041c0644100060003991180005001712101380ea0303403010490800c18140d000c54a100d0155000410000194940003002c004946500c00c10f4541c070791160a10001103008400b6400d880e0146c01c114 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 740826232 1250 740824982 740824993
    0x60405040c0e120d020d050a022a0f030c0603340207090501060f090911130902030f0915060f0604090905101b020303010b030a0905060106050a08060901030f1101030609021803 77
    0x2d0f44000d039610000303840c410040e00300040c0034520501440250104200030300540785204600d2510308100b049500b01001c013440010107030b2080d070405550395130924000390701030543c4012080c04a4000d100241014607012800054545054110a0700e001c3c2000041041d80020000c200000e55500c11405525101c41c43c00c00006042e50241c085880e4941c040e40f51508601d01d0103503004000c1c01d03c00102502e003181005038084070619009002c02030000c001d4016106c0c20008241c0c40603200040000023950300480f031003008030650720350b842c2d84400d048544440c5000c04501040c0c0c5c3c4e005580c0b003044124100200070307007004004100316a81d05c1c01c2010801440480040d03004030b583c00a00c80d5030250b00200018817095003220011580b2900210012400012a036100361920109034800c60011342c0100340c50300a140d1020300c65412440407200368a1a50454449103d500e101c0320000301150701d40c0c551703843c141c0d019800c484002e041c0000700f15250014843c18880080840c080c01c0d100b400b90 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 740827338 1106 740826232 740826259
    0xa0e030913150509010f091509020f0910020c1005090f060708041a091005090d0804060f02150906060d060906060303120b0a051e060405040c0e 63
    0x1a8040002c0c0c0c01081d0b0003880401070350740c02951051143c00c004004802d1455003034419510342c4040051412030b5041d000000c22242d61000c206140040fa030100d20181000c090858800300361445102c020150310100e8441c1120402298408006002405420b214002a00b000d00c07000d0000042220844002001030b08065022a080744001900b400310006001c4d86541031084000700504040500c0c2c001024110740c90090010428045450f4005689442140d056203410132580c554881e12504000c2c03020351405124000b40c0301d884902050007c0f01c0489505c0307165850091300381e0313454000800c52207201100060314140c0d100d488890110302c191080b4801103109032950207641c11100c1e910400d85583e001e84902c50310030034000700074a480f03282c000c0c0b21034050551a500f20380300040008509004540242e0b41080ca44502030401a800c00c0520511084c12166120480f04 = true := by decide +kernel

theorem cover : BRFrame.Cov 740647482 740827338 := by
  have h0 := BRFrame.cov_init 740647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 740647482 ≤ n) (h2 : n < 740827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
