-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1860
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:56:11.617054+00:00
-- url     : https://prove2.me/submissions/afe1d495-6919-4468-83ca-778950a4e918

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 334352517 ≤ n < 334532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 334353767 1250 334352517 334352531
    0x60611100506061b0a08070609110414061c0803040c061b1502090a180509010606180e1519140402040509160932061e0a0215091f 57
    0x40c1d581c000f510382c050110142c041d0040e2100c1c8800d0b181c42c04000e0000d1407a4004107005040c003045500c49c40450f409608001c205180040400040b280000003030ba1285642002246d80c41c107003050b0a41080c0305012100078082251340314040307280c008640481c0d02d00c00300142409000c1d4030204444036151150040402c1c0040c0d0380d2038000214842c8104000036502181d1800c02c3c9d504c0300c4110005050540340c0f9500007602202110241000311081c01b00c0d0341c04c0000001d00140b01d650b90000600a0541410340f160030004e21414840010b041d1391540c00c0e507184100e8080c3c0d81c1c0007600141c0d0207403840006289241100382c004018001d45918403070741c4180170411542c6c55071609140d1080d48400038103041c88411f4002e403054076258001e228020030798504203941205162500d28403010101d100141141070303508002c0c0301e1043c0482c814014185e581038080ba4400d000150070400d4090058400f0703544a0043d01590510445c0d403000580e110850348094290000f0381412410001c1400344205 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 334355017 1250 334353767 334353769
    0x40203010e0a023706110f06070516050109120f090503120f130801150f09090507061419030614010306081914030307090f0b0705070303050f0c01060611100506 70
    0x200c0d04c6608503030640500e03546103007200c0c00e0402081d6892035007a01804c0d202501caa000404216461031211554454003482c44142c62000600d00d106801c03690b85c5624200051020745424500c11347d04680c2503484401c034000090b1b00003d9400c09005941e90740900a051300801085562268456402a040080c40c0316802c26030204980310449420703615a03446444000c216000301255101c044594601012075240d40c2c9014200c1d421600c40705184c0c60b0140e02c6041c00d9040360b10582e40104241c0c4500c00c00c00120b4090360034141c1c1900b00e00700241c10300c510880c00c2e004a400200c0d035200000d83d100b0b81801940010b1100814070013080c41e04000d02d43c140014070380d550000181402d46210859903000070805030802d10030400303c15409681e00c80c1050b0f800942038805500a180744c907059814081031001122080e40c1589070840f001706601403564030156001d5016010714000d0840030059003120800074080c980c0180704039520102105442e4140c241000140154440b143e0b052a041c4142 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 334356267 1250 334355017 334355029
    0x3090c0b2d160303020703020f15071103093a080a0801080a030e120a080d0516020f0c061e16060b01090e15010c17031006080106081801150e040203010e0a02 69
    0x1140e4941001652502c541c20149d20341201e003500d40c00b00344a0003441e80101c0410384c0740c8034000d00351a1036075046007080100240d244c1c00350b03030701580c2c1004541524081a083e618103d41c00e402c0ca030364240000c0031540d51261704800c40104250f0b40b444001940007007a580c0445842d0040c80c80e01c01403c00740419aa0062004968000151144141c5113000844040500804009a911034085c0e80e450750070b40c00e1000070f440d00b01e814116090552509016890010591044244184001d0102803c0307000400009030403d040b01c03292144064140480491040010700c3e2011f40020311003141710b050300e40744045d1440d400121381040032040f020421441c00b200e105403c58030318011800c1034000c0c44012200300780111400f4155219003040008600c03c0c0070011409002c0c501e19400c0200d40b241c00983d9032020130b01c0340500040c0110300007100c42010007840c0007801c0c0ea80002044180d01e016504031f105841e900541b03401c0c0d9440c02800210b1a01b44902c0c511085a103001e054690380c99000186 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 334357517 1250 334356267 334356307
    0xc0d11090c071e1511041211030d0504050d0803070e060726090f06030405121204030f030504080f0c0f03030a0c09050906010c0807060e0a0c0303030e0c0a050103090c0b2d 75
    0x2050715100d10845c00360b0038802c0c0c180e80107460a070a624101c07903603038104080f00840c0b184110707005c0e0050301380603400320303101d40100c0d0146d030400740881d2003081d8907070b860707292070760004286800300310b1014100c8816a803050300900285000c0e02000d1501e01c0e00400c81b800000904542109506003040029100e0300c036592005901041200c40c0e545a40d100d003861400c040311900301c02483c010000c1c00091680d400e440b030038050b501a581d140701082c49410260b003128416240504415002d0080e00340b812640c0f0001d0004000322015102001c0b203030180030345580c1041d2002802d40b89ca900006000550054403507004000c2120001010300b4480c00107440b0071003000c0d029088503070006102c0107000e41600281d4100d4183c508561341d41415040c090014040c50000300c001908010118a20a600150303002500300c004182000c454984801034005144517141141c41501c8400005a1a004140500b5150180500c00014100d900c0c03100360484100f4040340070345240c2405007000e2400e600100c09 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 334358767 1250 334357517 334357553
    0x602010e07140d020406090203040614070f0905090606070209010305010501090b01020703020609011404030f031706030606100e01030908040f060e0a0806040816050f0f010606090501020c0d11090c071e 88
    0x10f040f800c9400400d015003981e801c000a000c0c0000140001c01003180d00c01c2014103c000c0c01c581064070743c6d640403140c800d5200718240025000203014462490301841d100e80010008244a2425406038040341e4079a500f68030903220b0742d56500c010007081a5030b0181825018091003d064500e0850740000c00740e01540c00d460781007001098907041904100d01c11140510342201c0c4d00c01d1190300500e0f00a00d0080d62043d9480340d000f0100100f00c690800241050040c00b0051443e0119001c0e4501114003510003400c442c105503c528010003c03951100c0140003030700c0d000d142401064100040a00203003042c00c0910702a1444d281c08100032800820159000b0713900001c0e46070340301d4800c20f2401e10401420f9028149003c0c1d0b0401d2902444000b82d102203d07000700b0000e008555503440d060341c01d214944649800758000310300400c410b140607090b619101c1e10542c60148107504100108901d00411112410040400500c00f424000020150403a505880400c111254029a40c202840854207606 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 334360017 1250 334358767 334358779
    0x2030c1503011a0403020d05061f0b0928030c081e100906020909090307020901140a05040e030d060e04140c01120c03110a09030632070207080d090602010e0714 70
    0x120080300f2400c1c0854005540040c443e074421b62250811580b06c02c001e82d004010031070b20f00d81450400100e802d8060440b0001198942070a44280602805140c001e54030080f4090844118007113040302080704000c0c40c01020b00a1695080040b070516000b00304c50f016000300c00254841d0702000000036115043c52400401207540a02490040041c0c003402d001107a00200443c200020300e176000002c2d110840c001c0b50b04c031300743e643c0c2d80c03c4044e1246c0080907159003010700e800b0306126508240c1c01003a0140a0003040701d00d0301e000745038034604844d803030b4004d40320b00e0700924140000d00400003112204074024002410101c510320001038242129800103205c05900c60304141e4000780298812000203600c2d051250796030800038401002c4122a000c1214102d19145031a441e00030300c144080e456546106455260070500280b6040e1040c00811345c17421803007402408641d0313032010310000c08104c1d903903182c09880303a05225000e030035180c40091040160b07104c01d07000c100c07114038120030079100e440030744071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 334361267 1250 334360017 334360049
    0xd0503040521031c0f1a010c1103030a2001050105010801121b0602061009020f070305091f0302090108220b0a0609150f06050307090302041802030604060902030c150301 74
    0x20700650301040c214400310901004c594808400340362049248400300e916410455480c8010140086800d0900c1c103844211155001c0d04055000c0e18012043d10b000741600d050148040001038610340c031490360000011500d00304680d80c01c040034514081228518000d120702e41c10200001c082c2c4005120344100020400031744002d100c8083e45075a50b84030240c0d9034225103a1141400313950f5000036503c696455001520010399018603100366101042c00c0da10140c54060705032804c4855400c00c5594980c44401c038182c1d8098030451042ca07548002c460340300942c45907050b5002510410004000c5001400d030020180750043e01c41c50444001a44495901c4190301c07a519060028007440d0403440705030b42f800b800c241c0700c100c040104008446c5014030407200f0b41e4540c50100c80071f010984802d000b0a80f180c40071b2006107801d400801405c68410000400d40510341c001901d031020580741500c501350b940e9011001d40c01c0900230000c60703030020740b1000440c42c003500b2241d003244414400c1401070b000a0030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 334362517 1250 334361267 334361299
    0x12031206041b0e1201231008070806041b140409060b0301060f170d05030703090305070602040e06030c01080601020c190b0f04140a05011407020307090612110d05030405 74
    0x1002c2141242d10082010382e55141d07800142c440e00c0d840d84468404c50322448642c1e407a800500810019140ca5202c0e0010b5008080c448400000040c02c45c1d1654810a08041030303064013000903c0041c44108002c100b1400c15040460069100d81e884000b6040c0f5140705008000361040015503d071030030b40c0d00203802d00203810305030001d028400390140e155080020000d002c804a240d40000e80b0200c480202c80884900d4440d6070b102c1c52541c160f0041002400082c0c14540a40d0000d07500b80c1c003900f00149010469603c0104907880b5030082d090740340900090008506082190010280c001c2c00c1030b50550401c1c800103950340b481c098116100704500c00b80c0c0c0c04444900340c0460300400711602031f02d44409041c0c40d100ba407038005010340c2a19518103200c20181d840c0c1114075900b21030040e11541c04406001101080319401a40180d13058840c2c0200043d41510920420300204030200d00900d2007a410703d031250a03515041c0b081ca210710000700c08240894804002c4800311081211a804900f40110b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 334363767 1250 334362517 334362521
    0x307050f010522060309021e1011120412060b01090e01090e030706060b070209070c020a03060908120106050a0f0c02090610170c09010f080420010504091a0f1203120604 74
    0x41d0407184580000800062421741540254950a10864100b17803002c0d42c803440700c01d00400d041c5405a11108604540400502032141d042c0800120b40c140d9040d03441c92402020603601a6211a00740162068140d0038002c4520940c9500002460958443c0d481c0c2018007940300018020010701641d01d042803a0101d9040089a08080d03102d281400352990340d0b4201e12141d00211070580c00782802d10001603031540b15160307091901c1d034010303d9200b0741c50950302c0c0c51000f484c403120120b0f0940b404021041050740f9032034485000b050141c2e2016a00c1400c550010310000c0d01d4126a8140304071007100300010303600c0303000030b96102074184d5016200d1100c1241c12510705e10b5140205401c0600007090201d00c40b0000e0080000000a0300c881080b00c403141c00172146044203c502501c18620607a40c44a11420041c00000c0c208052400506240e03c541d140e00c2203608100d4450f00003120302441000c40c1c1002d18212440880460300565000c3c034581540d0b460f4891417601c2002030400500040d1381d07541ba6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 334365017 1250 334363767 334363807
    0x20618030d060905070905030a0309031101050d150528050607110d0837121508010501090507020607090905041a010b03190c020c0d051905030a0e0307050f0105 70
    0x280ca0610115544242c000b00400080d6031550011b110b1000104c3d00317090020351500b0080c0d0541c2c600210501d1615030b801c41144050400e030410400700720440c0c1c401d885008840082410210040805203044200b29813095071306200c15600c6030305510240004c98020814003211401d4800990b54080d5290001c60000b800240e02e6020120340310080a120304034014207800c8a9000c9108030001ca2844210205003051803209030175141040c00f482d80c544110b0191460000602010aa01c2c0d150804882c00d9441500f00300b0380e030b0f0740d50401013215a03024007506402c0030940c00603004600341050020b100f019a4050502d1250b26100840e00b0010400c603001c0303440244034840446961a001c2540442e401641c0d14980100c1d9407400b5101e1380981c1c890396800c29000c1d0010184107480e4400d000700ba4121a82c10780d4540944a071054180b41d01029a2a082e44910003a5a0b5100d920101500840740c10b003b65001c1d600004092243c1d4031a2422890580380900b8229100c004501c402003007801c01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 334366267 1250 334365017 334365037
    0xb0d030e03030409020c07081207020a030618020a1d0f040b061e040207061d011505100c06020a03050402100e01020706210c021c0e060306041d011a01080604090302061803 75
    0xc009501da400385000b141d48025039156200781c0754400709002700040d41d801407031000795021101480800008460b50b02207a286040040d564840d5005600020079000710741d40000000c001c26025440d01030f60032090158000d411f070311007039039a040a48a45030003503401002c06000316458100100a010061413031844108000e00039542c0b4282454070300e0280007213011484500f03507500008030f28020180103207a40d100420740404011071804c4200498080506000d00521207c500b210700030924031f00060400c08819140418942410b00c14800066044082481044002c0c4005081a030380854000e046031060b15010b204100409801d081c0e000110303444407251894000340190303868010403403624a0883d82e02c81c016440e00c6010641d0002500510503500400400014910303142c03a40c0b0080102130864201c941c2c141042a0707650846407540350889180c0304c174038140f109545e40200e250b035004009030303002c0c003000030140d40103580c0c2c020241c030080e0500407811507100300510800980344d50800d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 334367517 1250 334366267 334366271
    0x1030b0a08161a1c0f020c0303010b1e030705090409110d0c080c0103020403050a081602120a060b10050901271403120c030708091c0b0f0a0b0d030e03030409 69
    0xc002070314a848034100b4801d92441d03c00c55400a160301801c20309642c607041202510481c14036903589050000d084d841c40d0261040c1c2d003400a241800b10400246010f40005e411281d668100d450f1100d02040300c00b0f1040d26400b6040082214955000c0f00b178400c80340c000e032008180c0e000c0340d1404002082c0c81000e050b410406090240701401031203912802190600d0042d138400508980045060344130310f01001d40503071311012112001841490040540e80c031030f90600c030514901603001680968494482441544c407500c00081800090303c1070300706215080314140d205041d1441d001c0d15a0146030300140c1800307a14405a003120011030b1100e01e00084442002c461151607c510802c02c502c05181c65009226420252080681c840300300d801c1440301100641c24025903030707a552001e902107000c0b01d822515080e00b1010308100c80341a0104244580c00b00051490008070ba00d0200781c0c014403001a240c00c6c1031404202d03132510007010000c1601072400100e907032401008070346180f146511588130b140c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 334368767 1250 334367517 334367533
    0x3060f0d1a060d020904080306120d0219170c03190219060504060b030f01020a02210f0d02090607080405040f110f0a031d01051e04030816110a060b15040f0501030b0a08 74
    0x4007d400096101d888100e0301804071841411055a03244815642c01016a20015640c10580b480b0703000ca00065110b10300828486a503000c108405404c0300020105917440491014681c440c149090003a00407288020309003034000d4400c1d50000c1c60f4021000c2c14240c0d642020400307024954000d01450440034003241c04a4aa950a081c004d60040c2a00c0c0014055a00a012361a1092030b132103105401000f03503107040900d00021780c88250301c68254a00455800c02c54002c85880f541c000d0080c44d0b00038071b002c5403198030308006d00c000d98200102400c2000d190030024801c20341d4180607a21038988005c242515841307440070580041000006c03c0a0900d00075140710703010141504424403920201c1c3c203400c50100c03422601030283c0c80648005000c2200c00c00011121240101b0081c680f0440d850903011032030304281c08500f080da02c4503042c0c17034060326160b079084503040c0303820118038801d880c82d161840c0500d45202012a42640d0003264101030304c0341c0089206943e00c0078410003030040a02503840782 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 334370017 1250 334368767 334368773
    0xb030f06010e090c0102120906130f09092102071401030605040e07061b0308010e2205160f0303080604020d09080408030a03150602060f0a02041a03060f0d1a060d020904 74
    0xc0d8000b2245102c03944205042001c2c0c5501c04030f401f40c180402c0c0607045042c06901c03001c20050b40c2060703042c480440c643c0d081c0003443c0e00740203840600a00120500151503081e60801e202c140c00d0108281003203036000c0e5250407025a001801e0012106002a0508031031303400707001240540002d82c4807c0e441410f003c80000030b40e4012880800721219a100c01002e0040d111155202c8404410080c010841c1480104046541c00356419400391368a100551588254120408074400704042683c0c164000741c100540c0050b0f00e16054090034800f00001800c81c40c50f81c005090400c02003c0c42e0050360042104100d660706a04816800755021807a5600c80351140d0784665650060380c0a0303c002410b048817420f201c4458203a82c0700740c88095024102035603a84003144041034000d8204001c150303082000095001218031a44e000008c510301c44c13a07503414070707400308801a0009810984101d114001c9480000c009800701c070380d841c600d00d1034030312550f55400024500000360b500107074000001c0405c001c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 334371267 1250 334370017 334370039
    0xa021303111801030804301209061803080d020d0e06070206100e130203120c07031b21030c0c060917160b2503020c01080a0e03030601030b030f0601 65
    0x540300d050700e20350b80880242c424515120b0b404e1101a00040080006100c81605010008036914591900c030301006c1c2114403000402c045e0741415204180a034602c02d0705103078014006402019181382c0800d04088038901c0056107200d902c00203010000c00100440c407422141c05840c4126060314007040109011410241c8034101200c41100601451001607106c000d102c046a0070781da030603451f0a805546040052510000081040e42e0510800e000404170f607000d00003d18100300c03480090141c041c6135140c000981c442013940140c000c01400c1040c00101e1745065540460b01c8600d00c00c100144031824140ca2401c030b040390160400481d0500443c1054100084000b2151202c42e424650700c60050010f440b0113003d070301944201c030055010010f0341090030143c801c803c1019040d112800c8408602450301c00c3e92031045000d44c003ca4040e81c409d68002e050075502c007021103820302c140082008456141c0c8001400c1d2410305683d00403004c07242d141000a0402e04205804803409940c5600c82c0d90300c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 334372517 1250 334371267 334371293
    0x8090601060305040302030d09030509090c091509130b01110f01060e01060309030f0807030b21060c1201030b04030c051b0a08010b09010342050a0e0a03080a021303 72
    0x100910680000003032a62081c0300d1a4030480d0076a01460a001030410590040c100f604000d070704002090001a820741d60310f400b114081d0416505180d40c4402c40e40034072007407200c2c078460a00c11400501881540d5103440c1031084148652803000a036120b120700040c1e40c07101c0003e40061640c4201c03101246507000540c4075406842030006c80c60202d81e80c1d030004400307613101054010300181000321034070a03190152a50701c0e0411541d041c0801c05000d00703000f1400011b46011101da41e03202505460b004a0001c0c032066030070030044c84056207008442380801c41c6420041c840205a41e0030ba100190605210b0800210025445002d4580b4840d0303c1011521a03006644e40600c112a610000a4100c81c14424200d005034068440029a880e40c1c0700c1d0300d50900c20701c500521a07485940d001c034015a94090944020311040c200010120071007282c02d0448a004048840d00c0340303007540c44603001d02c001401000f03960345480c00d40d1441d0703a55030b4080043c1c040c1d00d4020110181c02a008410041e03032b800002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 334373767 1250 334372517 334372531
    0x1509030304260706051017062e1505070c06020606090a02041809050c060705030d1415060904091707020102060a0c1b140d0809150c16031103070308 65
    0x540100c41d0b8440301c8980a4550742d03142a0700010031140000074203913000141c0c4643c8142210080a030b0351084601088140d0ba401c0c001b07500400200840c480c1131b02001400d242c40b643c6500011078a01d901011101d02e50301449405001040544402500c00c1d400c03a422150b011155150076540d81d60042e603207000983d4401d205084810020301030407002d20a84044881a0410b40031812802a054004116101051302e00780141c0440700103980b10355004107003041c03058000b950707030f46410001c54044401942580d500001140305015a05403480c460307601e2030744116100759844440000080040c5a0254010049000c02403185880400407015003906070007a003d42e14250703100c800040889842842c41000704140564404c2441215000501c02611442c51283e441c0281e601c80c51421909c24520700014000e80304005032100180034480090103000700c02202411b101d141c9240c24054900160041c0c000d001d00b61040c1413090440c02942aa45401d4a6880035207050081002c1d40894081c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 334375017 1250 334373767 334373783
    0x40e10121410050609070f050d140105120d020309130f0608010501140a1208070f1509020a140a031103010b0a080a050c010f02030703030914100c0f0906080114031509030304 76
    0x1002d0340e00924024244a581c0080000c04650b541c482c0c01e071520089001c541c010080c0c14841c5200c001028841c0c1c3c5a048a2404186a6980b4010030040b24111190070468030307402910b268080ca43d000000d641140714115924110000d103a460107006024030b002444095007007030b40c0080e8140b03040d031000303040c1d50310309500700380801540f400c0c040c941640d445035820500740b500d5020301280045015100b41d500c10009030051070403903103403407010140070b00e036445078180e171440000c045252460702d602c010800c400000600112440000303548602c9072002800148804d05a10100d41e001e62100c203a1140003000e000c0900d8499507100c2c1e03178644801c6c04980318410040c0b1002c2030340c002c01a621003000300390700962810f10700342d6003180a0000c8080c11900d0b040707070041c1d10504420500c1041c0d14281d140308002030408090200405a00351740440c03401b4880c07031107428082180d020003c14103603000e00301200135240d4003502003864130200c18807000c004080c0b0000d00039030203004801540035034098124 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 334376267 1250 334375017 334375033
    0x3303111c1109060904050a0b0307030b061f170411030a060203040605150a0b0a170f0403020709060602070918050105190c0302090603040b09150106180e0606040e101214 74
    0x40d480e0a10503901c001d80c3c0048244a52240313032070311ba000198040b00c091004602980340c0030102e851b042854000315903007070209082241d2030070245d10341b0a00140a9a8240c0c000e810100c000d0078078944503111550aa8503080010244a15100e0314041020090101d0713a0810b40790500200a4000751001c442540c20b02e07000c2100c030340340443e080d41c50341c030700400030f681840c6007a402100f035030b100c41000414842c2d442900403c0c2010300d07142e14400c01c0c0c0008443d609103014507000307080410a4000d8900d0700d1401c9800c1c4004caa0019840742641c54030000080c2c00010250a080d000091450042c1158240010003403c0100d00e810800f1560a40070203000c1140b80700e409a050b4092030b441c450700820b0038000a130100d03d91400186d0020804010341c2c1500082280e0f80041340401d0b0404000f00703058003a58042c003429000083d008100c0e01454550900700b080004440348903030300c5045103003c0940c01152042100160783c0008000110580c004403000d80340c80e102d103001e0020407100c14018184 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 334377517 1250 334376267 334376291
    0x40e0f100f11090603010b070c0e011203020f010606270f1e0e040b0a050402060c0607030e0d090803040e0c0c032a06040c0b0a0909090b090105013303111c 68
    0x800d40318603d50040049007181c2c00c03c0d41c8240b10340c001080c161481c180540300081c1070420000c40c0d5003e001d0010f8140c04046050401074070305440d032007075841140e00d0600300300710056100410540d01d500d40b0010000c104401e07481414a250150030501130490b030810005145a03641e03280120050404518003016035a4600003c561081218050090007440000622808841d8032583c0d105100400031410300e01004c038001d05d49501180e05c0e901103540ca280801c004c144c10005502450b1062410103d20f41c00c22909588078000c922071005584640d401003035170741c40144181d4240c0d01c445c40407a0b8603260320400c40b640a8441d4445500c2038084940c03404541940460300c0b03031250b80c0020104080c24a80800050141d0100581400304190f049010074119502d005c3d100250707010340040c02241c01c0201d162803c50300182c2c400e0300441c01c0c080b0300805a1080398280d01300003150070f010401800040100703030050400107105200109001030641b030b4084400c4c0007103d0107552038800b08500b8035191 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 334378767 1250 334377517 334377551
    0x1612050a0902031e030f210a0f05090118020603070e22110a05070215090607110f030d170a090b271612060f0e060411040c0509040e0f100f 61
    0x1448412103174004011800003801c00c60001c00078141c440710303540b5080a511681c103103201425500c40c10704548400760954052060f029294004042c94020480341c60380c4c0c0d200c0a000210b400340240290000302c0054856030040d280400700c1e6002a0102030070080c0c0203880201d821484101e00c410629040320b514100c5100d800380c07010211140c136418a0705140e902040205030100e45100650f007420000d18980740c860300b0150460500c551100d50402c0c001000b04585488a1040030f40a54041051441019404001c0c03400c0314001040030305007500c81c0030700f08000c1d24813041c016103002409170a102d030740701c3d0002801a02d140070301120038241c20940c4506480c1c200001032010301d07050304074080c406002d01008a500e0710380b082800103407850381134107400c041d03802060240e42590011000c100502c40c40310000c40f041001142d040045540303e01018215018482c000c2e80910380d00c9064070b01c00f03002045002c0711084c1c0f0800f102e000c0c0441366616030141c100248056405802c12011040c3d4040304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 334380017 1250 334378767 334378813
    0x70609060531290702150327010e070b0a0504050d05011103070c11030105090c190f080a0201080a0209091306140a270803040314040314070911121612050a090203 71
    0x1012020034400410350706c01c071604090b021240e807580030480c4040c11000c10100d10407196480c00049072000c040546c1c60b04141141e8084068100f04103c000301280e80507003107400760b801c00c03a070703404d0501103500308140145056445032010017400001d00062640100102882ca03204a460701c56800302001410b0a0301c2081d50301c4241395000f4141c0740c401e450136440180001c00e80000d0b405040d6035800342c004015070243e00c0f201160304940c04013001e40d42c0c40011b29601c1041000c040d80b80c0007141c400b050000a00800c60594084001e030081d041280c90740280416004004009003d424a41001c1004000c0c18803546c5550009007041c0c0f050131407403124100f8003030b0420300d29811507545440964070902307904c1124062107400c2001000051a400c40b2618007596440280b0a050400083d02c007150035101da010a603810510240c000b1a04c0303c015160b00c24100304814403d82801441541e8810201d980c01e2203403420401040703d01805503001503ca81d00880c1225140007003100556949440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 334381267 1250 334380017 334380019
    0xd0f15030204020f090a0f0620060c07080415030501081b06030f1b030106020f0c0a05061e09060d0e0106141003050408090d05010509070609060531290702 68
    0x254601000985099800341c4010642400a680340c0400f1500044c4040780540000424003810b4000b40b0841c0d900c801025103c2412808030082c2c220450030b05039850760020140c410412000030b030b050030884c0382c0058800400d2141c2da201020040468054040c120900a58800f07120306071481c0c10341d100540604007034640207041b042c070f140c442010b00205058020440d00c600d8000121800e600c0a002c0020f600074402c40d8043d2404c039003c14101418191801c4030f079032044400407024000d80d51880f04640100402d856541e071140071b000c1d404411340c001c0c0d0b0300140e440a800724030840ea0b504903411042840c002d01008104058883c082c05801c5241620043c0e04507800f902601c0c1c3e814003e074030003908240180c1c25a0f0078010803d00150000c11041c0701160b1503511039040c4a10b6140400154018003014186681c25a01344103008056002d05040d0400c0c640740350004503280020b0462450035484075a00d05800d10703032144101003a00704590b01c94a0505440740640070300850181c2aa601164 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 334382517 1250 334381267 334381301
    0x8010b0403080705030f2106090c0d150b03010609060206061005040b0706020c060406060303030b030c1003020f0910020105060a0e103c05131e0e070312050d0f 70
    0x4210b032280c54242e04102c40880c2c80d0300c410480410503444001c0034029043c4014011b41501e06180e40d65010f155015040701e0040e0051414028522160005d07610990420f400001e41d54089600000214450303502ca02c029110000020850315032005425041d0b031516000c0b030b0003e888100500944000c00101c40000480512050211222040052036228001c12016042c00c580c04102030506006a4080b19401c3d40c0342010002c25415002d81c0960039000c501512004210201141c6d04411800700c42c0105640000d103d00000003200550b01c5150014002e15114404800040e0013010709483c918070541020307a0005070040364005507446007003050301000c0201d06e4031401d01b81c0d8400e4418941a40e41484400d40504003880c0d485004c01103822026800f200c0ca0041406456202501e05101950501200407401c4180541d44600411a804002030040d2060700381c904010098000420803009128a0100c2075480401392407410304141e810081e45d5194165942129100400105171f48 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 334383767 1250 334382517 334382519
    0xb07080703020a0506131e03020627030708040305011104030804210f110a23090702070e0103060c14181311040605040e06030604050a1101200307060b0108010b04 71
    0x10404006032005900c2801101c2ca80b040a030380300d50400e01e044840c42503038081680d0800901400300c0207004440c6581a1000e83e250301c80d03c00075110680181300d169440640d00c10640b200c191046111202c00310300c1e09490321081c46140900c0c0b40d6105200594940d07082c5032082007a00e26110403201280c0d0710103a030303070714141c0b428990f022010340c2980003000d85226603403c180030510110084107410311841c6c1050031100340302c0c01c01c420001980c10244111216420b466000509881c0c0d00146120440380b2400aa031161012807800d50300741c0110b00e40c404540000000c1220542001007429078503260220304500b014520700b6540580d23000e0300f0203080d85410319202801c1114030208090500e550205007400c1d03a104540c0c1c1d940c002d40c0014000f450014041000a5903840400d402c100200c01500c524101502e501e544d80c20b007a1005000001d20781d00d4080c590b030007000384180c1203330301d00060304608104104041e10380d0010380c42640c00d1410040400c81c190711648446060300e0110680c2810a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 334385017 1250 334383767 334383773
    0xc031f0e072904050a120204050c13030609110d15050603030a05030424020c0c0321030c030c0d06060804140a0b0c070201090b0304080319090809010302031e04110414010b07 76
    0x102c800104202d01c94001c000c0850907484074001440039100d00305014503043c5d218030520040f504000c00381034012406100300e80c40b1580100c1c01104498010501060020340c500700b4400c50107a0b44056035024111701100300400450941e03400752140d8458080000b55a20700c14540c40e0300c03441210302d0000704100700140c00160140c0c0e205d1462a452000c07181696007400c1c180c07040743c0c03000b00304a22070752180c81d03001c406240801010301c500641c2007078180c1078001d00104d001c3e6800003501240d00c3c0300740070001030414440d1038151201c0508200b4188442d82d0f407904043e00401040e03401769408040d903541d003c201d080000e4201102903218400e0001550f03444506007040e01b2209049041240c00c1c4030001e40e10312f41341c2c0614041e074040c190440d681c2c282001003000d40b01c00000d10b4507800341880252000301f42e82109807000988203003405aa039580300c81400c5d65000040c079444102451101c148030600004641304412a60b09403020001e02d00301078000324848500b40300b41c2d10088010001d40e000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 334386267 1250 334385017 334385069
    0x140c01020c011d100908010b0f0a0603050912040b04090605011e0e03120c0f0723090a060e0f0a051807051201020f041e0e01260c031f0e07 61
    0x19202c20f4a107030005668014000780501e004180d0090000b5002e2506000400c2c00703114455030900d0445080384051038650124800d041c0314440e00b8107041d07603078002176000042070180c143d120b5007040805545646a4280d0180350704203000f05d40e07451b443d00c034010915500410812601e290741c403da41c00c0a030452041220110300310600c003a00350149180500c0800b103040d0151208043d00c2c0050404545c214910078542822a4000100e0005a608800f140c2500b41c45210364590241e03140415555801c1800c40038114070361210500203450f004020010100c200708034040c117401c4805100585445444036a4200c4920032881c4581040c54108518030b0404520303410120590005400c001c0f80e00ca400c1495045544044845240441c80c8001d4006040301900904415002070a00e541003183e4800307152a40e45a4180f03113401070b40c07102c146400400c851613070810003c0c00c03200140843e0411201140b1887d010f114164105070340b01443c1707103002c80c3c0d26094850507464050f80581240d01d04c41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 334387517 1250 334386267 334386287
    0x90105030a1509020a03022101061d0d1403090108060a0b0d180822050402070803070c0303060e07020307020901051005070312091b18050903030114031f050103140c01020c01 76
    0x128881c03080c000400c43c403107001a044581c10798038010b0311080d1008650000e01160700c000d11000c8400e40043c03007086d030042440d0055415110035402c40410745004030303450000031070300a414101404284196140000000c1c0000780d000e9075485440e407641d00034064401614052110280c0d4140b04c0d48100036840c0d4058414010007030411168601c6a44840e80b0340d60000141d02e03ca0700d1480071a1005100605c59580100004d4038114505002e50701c9040140c000508040b0401070b1960b224014103200707811a0001d061202c42c000f00d6401c280c88003a5803036022000480c020181791000213400e241c800c02c050b017500070b03076141c0074940200da6400711200c102821003402141d81c1c44464101044122551180019500b18490441e60914071f0f02064090034a2132401f40a0a00e002c002d040b07200030068904440c5001110310390021140000390401d1403244c0100381d0700803c44404e1100100c1500014104c038069407020003116a002d200710f85480300c283c1040c1c050380c0b01d5400715945503c1034a54017 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 334388767 1250 334387517 334387541
    0x18060412110309130b0901080a030507120509100918091101030b130501030302010203010303120c09050f0d0b0f010603060602031801051b060403020f0708070509041205160515010b090105030a 84
    0x3850f050340030001807100765609810082c0141d54021103441c0e8101030b03900a014118100080100700081d94008016100f0702070028200c2078030282c0e1035403090241d0192449004001c21400240041e20001000340741d16100d9126545800100241d48003158420020070329040600c1a007412071410040d03021b8040091201d0304061460020b1704055a10f1007044d010350302c00c0c0d00142e84c1c1c0d40341d824024070702e03041c20382e80c11440303883c0580b00118503800c446020200d40095901340e2001c14404000b03007003480c4603000509442c031070000300440603808039102c1d81a109207850400c091a1034803822030307403030142035900e0102100241ca40c1d04198003032009030103114000040f150381c2e00f03280d0740000d01b4503030f0a030f6007100035a110444c0c0c2060302e0b60901000018000c47e02c0106a2985000005211500c01510240464484650b042030441c072510441e050b4125040c013080c00c941c0207141456452508900d400400b018480012405103800d400319422200143e444600b59150414184014119030b18a1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 334390017 1250 334388767 334388773
    0xb060a030b1b130603050f070e06030406110c01020a020109050d02011e0213090c0203120622150f031506080606130e0a05070b1b07080a120306050303121806041211 72
    0x10a0f0042c1060b507040060002950045414180b4240000100001500340d5083c000c0d40003141c12240c9521043c4da42c02a0051400300e0448050008581544540d90804625500004600c0845501508600080b0f40704404558040c451400c04a080310080001b40810b0000079a160056040e10b80203486601c0c41d403000310091540d91540003084904a0324000d0240e003001c5541041c0c6002c140b0070b680d021009030781c941c0d032005408840302d10060181654107091551816464424204d4000c2000a40310010200503c25100c0c10201092a05c0300c2e41c030507240d8181000411205c202048050290b0006004280c40a29040701c11020b800c0781d030070384001480342d0100200410801c00000d0014200f81c5213503130b030700c55161642c0c5000c001019003007803165020340c104110800c070001d4a16803464110170b0034501002504c408030301504e1a640441c0c2d1501c0081880d50100c0070000400d4059248418030740e401060710390314181c0f10781003164050b00507070310a000a480b0070f00404140e0714008841c1c080e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 334391267 1250 334390017 334390027
    0xd050c04060f140a0b09011b050313260d0804031809020307020d0206012102060706020d020901170403021f020904050921070f080f071505040b060a030b1b 68
    0x458100c030801d41c40302408000340b800c20000710341010388004240d0415526541d5490500f0304e40d4540303103c0e644204c0d040080d510552080141d00e11110b50a55502c4030943c0e44c4c03210b00003483d100c060814003444202e401c2d80300e0f1151113161400c803009400d01180010303144241c1612000d440342c01380140154180403249407803c12000c4510307201c1014080b4542e0050710303420400c00003440e0403101c02c1c088041d907000e01c0040c484036100d10312200712086801e10280201c5a10f1020801900410000074030040c004101c50054500d00c2d00900055a000c0c0d0711050f4024940000806000c800e40700075016800000c0e59103407240ca42580340002c05103500c0302610b481500c0e00400d00700da008807081d640c241c003c1e0020702100c01d90751154210100300396407207508000064070341c081800c50400008201460004440711101070b80c005941c161034000d00560840301d41d21442502402045030304486d0300c040342d0002103203450401c40314070a50b60048241c0d1001c0da07601e40901c030b07046115040d1041028080c0a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 334392517 1250 334391267 334391269
    0x5060c070f08070204020d18120c0308010902030c070f03170a0221071107080601082512051f02070b070203040b0d02070215030907030507050301020406050a210e0c120d0503060d050c 80
    0xa200019804080c8007a48d102245c1090394254181048020800c05156003400c046540088801d0540d0001000117aa0b0745460480c00410700c40c00d0001840318120003903031170515420160401c2c01c0142c50042c40d21036034440c00703507100321f204101658000030122001e140008012510880d0700420608140451040c101c840c14a809819849210507a1140c0010701c1861b1052010b0720f660007040c00c0340e10400440c6070301c82d03101c2e502c540a00115120304032412820b00c40300300b05840520f09403000842070041455101c50180d805140305550081041001c50801840081207400311807800c0705040c18a45e0396040c54010b544040b5003a41d0000c50400c00c02300d0413546400650150303003440c0051007018554580181031409035804140300b03900c140002c11500307070040101d5010030034500d050b20100e402000244c0c400c1c00682620356030076241201084540c40c00180d1301030340c040d040341c008000c2813900300e1441e41c03454002c4205001130014004610f50341000c01e08040014400e1090b1422264558 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 334393767 1250 334392517 334392521
    0x601030603050610063c030f02030a0911010e030304061103041d0403090f080a062a032405240f07030c0b130c060f020304030602070f05060c070f08070204020d 70
    0x50b4114010043d45001001019044420309030140012449030701c580d1444011480400c2c100c01c5c0122001004000740310346e040c0309500c041e040c002c80c54811505c90402894500040c540d200c2d08486a000c0c02603050f002d5030259020803641070006004516203400c2070b100f02c403946141c4003284050b11080c44042452000541c17900b1854a2020070041d0310328150800804a03151644140c514200030401801080408902c3c0c03110550054004950010498040034014613912094920f2640c40d981a0740155810340200303521100c0400810203109402c0104804030440c0d11509510568000d040e20040c1103034446401d80d1500c000e0301c642828407008102032540d01c110300071400250461f058000b0003a1038245030b80c00001c0e504160380c0541042e40d502d4010400d03400f40009010060b1201d0548500c00c2045901131540103106540310441468901c0340b0301c51468080317034140548030006a0410201d07041e282c40303503080130140d4aa08a50b0701e643c102940305141c140d80054003007003c40e0543c041c2d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 334395017 1250 334393767 334393771
    0x30f0216150c0804450506180702060f24040b0406050d0c0504060b0a17040501110c0a060b0105030601090b0d0609050115120b010f031a090405030a181d06010306030506 74
    0x10354480300c5800f034024400480307140d2a54100a06012603803010189117100070b50551501c0f1000c00000d07907403181000580c006400311483c0160702c0c003130020403484a5012440b503001d400322001c10003054941095420310305241032400c2e2241020845101002d00d07080d04003071205940540006061511a030105121903200701e030a40f89400b81d040d003041503040610070f210080800081090130900e0791200141102901401d04009490040c0070400784402135001d02101000c03541840d607213030380001c4038a44a9034025003e17036900785406100302e070550051b411640301e2201691500e1700343d402c121039029580c1001d6032400040b42d481d02c001c25004000d1141c140078048064070404451500f030380c0103000c1a880003030486c413241440121142a60000c0303590165003464180811810b2081c0804091281e004500c80c2d0311810f2001030105000021006000306039090340c1d01c0f040541d444120382c0009041e4840c81c9410004141242c442412103001e842c1c0240c01450085121079880e04c40324a00003003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 334396267 1250 334395017 334395029
    0xe12130f06080405160f050105031005030f0109030813120507060f0c030e061302010509130e1212160c0303050603030d0f0b030c0901080303011a070602030106080103030f0216150c0804 81
    0x2e900c050100b48901040300c14074042d00d07400040b0702c0908151800d02d10400c0d92240506000c40171021030084840c2911600141178050704440401d050340340c42d0b03406000903e406802240804000c0b80382045602003102000b5044100f28100030300d022021122a8007114041d103030036035180d40d5a0b80c60700043c001c1200c01c290b583c2c0c01040c2c2202c0398102906041001e002101d410b0705059000d00140d030040162141c06104440726114820b030003034202c0260840340d946006600a00140303d040d12403030f401070090004581c0d10365025548060031001000340034800745012400d135a00680009100707421580d8403410140950f07050006405c031043c15a20218400e500254490300020428282048501907150048070028030139454280216141e201c180642c0c04003001500203403683c01a001c040310400d680c864000c41d0b0302c0d030b500d03580204210000e0000b140025411620351504510000d0b2505416600b0083c0c00000703841e045440d0080c0b148000703c0c0080c08440030141000c0384141e0003030401016 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 334397517 1250 334396267 334396277
    0xe060603061c050105072118020f0102030d090b15030604050307020d0212030a020601091107030c06150e0406230402090a151e050406080f06010b07020a0f06170a0e12130f06 76
    0x4401000440c00c0c4180e509080307d01d140519500d03e000b103400c20200280d8054404070401415400100d00f0b600c01c01401066650404108400300035004040ca4031602e0072850b400c081c2182201003540f1a01e003948c000c0c10030b80c07081c086103000d4603054402c1d1050a10091050342081003d01c00705055070071920000015030000700041080d05c030640110b154100880701074500d00036139039034040c0035100010000307400640d903004400144a9040f040b5400f4210160b407503810780c030781482c0c600d01070060000c801000d04460b2150382114165681000d01440e17000303001c05080c0e80e403100c4000003852400c1506000a150361720008060301c440c21050381c401c00c214003030102e1500388002c1c07006175915507006170881c0e4040b20070203003400d8000c0b4925041d104501051503035a09a03000103a600f41e0141c0001000512440c40004c005801c10b0841a184c0b400f018884900e56824b056841214414804c296140c1c100074144034951001100070503c1c8152030700c2c0b500308561a80d0503504002540c1d041440815 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 334398767 1250 334397517 334397537
    0x61a03060405090705030a3f0e1813020103200702030606060403030f050a02161502242a04030f0c080303070e060d020c01050a060f0e060603061c05010507 68
    0x1c202030186541c40501400100318040c03410021a60310007101c1c0d80035080c8246803641da00c20201d5401140c0704801e4000c603070b4050640c0e01c2c0340c0b810203245000500d00840c452003416021130604600e0240c015103080f030b0b403021540d502140601c2101a5420403410995074410041d0910006000303803c06080440d411502c0318060310505142100207041c19201d035500b40b00c00c0000030b03881101e0351030703d03a101c0ca48a501c40f00d0714142a45041c0c1503111102c0b02400d00300b000b19603280c00d801c2d80501202540e08855140002e5400c183e010303200c2e8000342c0f00c0030283c24001209a0301405501003041003160030480080050082d819054101e43c00c12180c080010021505100c020500c40014081440165155081950014041d1001c0c0c6642c40d000e00f0011440c41e081c2d002d19419100401c9800c0000c0c80b29250502c100001040c86004120010301c0c51000442c0102100042e640305103c003510962454403041e0401441020024100c66101010a07012000450a018160180740a0b0704c0d184909 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 334400017 1250 334398767 334398769
    0x7020d0605150d1101050a5702010e0303120916060f020601210203061006020f030715090602070210090302040b060a0c02010c260403050d08010b0f0d061a0306 70
    0x160180041a610456110b4411008200401c24070802d048003420100e69441c200d45058030b4024051701202c2d25021114150452103c0f0030350b0701440c0c41c03010181d06507007154101c42c20223803000c510551900c400d03255075180c006500800c0709007043c040003000c4a00340002031840b41070f03034003040f941d040f5107402000d039142a25040e24000700103090142002e113601c600c03080000355111014401c8504408407480045150b0881e1041b03075500b107801800b660300616140d480ea112501007486220014840c00b000040c41c5400841900c0d0074540c0845500012003509801e10b0140c00704030320a803100caa0800905c001a5194541c13403100c1c00284e01c03503552031441c50040004445503505401e00603003042010a030b100b031703001c540d80d21b40a82c242400760724503005c2d050805019030b0742408040380c0c5075032041703042100d6182c9024100f00c81c8107608a8030f48011001c021038076030800780b0450749200d00500180b01501107050140180b07032001d441c0003540503074955910424000c412446000e51400109002d26 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 334401267 1250 334400017 334400041
    0x908030c031c052203030204120b1501050306010f35040303050604050f010b0c0f060916080a0503040524070303060e13020a0909020103060306060f050307090e030f0c0307020d0605 79
    0x20a414000400492511882c00c40c10061036016404c6008620009503040500a9041d2405070a6194a805004100c0d1500040c0b2031426201900941e0101300c60221340d601c5034040342c1c440d0106945054543c2006c031310540c2d03012140c42c19240c40f05601b58084000c0000c0c0c04214064841c0703100070321404e043c1410060100e86000c1c01c403a010b28203213800c04c49262945101e0f81e0454600780070302550f525408204d04c0c10022031019402c6203003d07210500022a400003080c0054031100703010110007680d00c501c03142e034801c824200280720780c1080c00100200d1503d1900303880c0c19044503450507201500c560000001c3e034403450013103010940e00c0702c0c240100c1d500c1405042c1e01104242c0050229400d540000360034034964418800d075a91178001c05400c691103034004030b0045902175024050303580c030350321600c2c041111030041a000380700d945030010313504606014a202c40c1c0d403260301940c1350610081d07040c1e4541d801000801ea140c80108103242c010b8a0318881d01411074022080050306042c1f810500340c0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 334402517 1250 334401267 334401307
    0x5010c12020c0304030b060303090d060510050d120f051207030c080901090f06050601090509090615190501080421020c0307060207060503011412120306102109030908030c03 76
    0xc111031042c03080358000d940000840741501c0c1c102e55559516510707040042d10714440d5040d91038100c00c1c116000c034200541078004600540380c840c1d540002e43d4864003400a06501e6410183c10030070701c1001071210300e00800b000343d40c00e031062800034500340c030340d91540f42200c400380d400d40c000a541d0681d0000d81544001515001176401d8000d01651141e600c4080100350303150000b1f0695a80d0ba40400d03601ea018010a20040c0390141040306c0c2340c038003a44c080b501c8003400c03202801407c50002d003404051416101110001c8003008200000c1401d00d001128540b4005000300c41441c2409060f0b0310f0103074901814070440410781d0080040007005014503050220b241e1003c000d5500000c000c0c4800781e0841d05483c19516201c03146100658074200141c03243e401098011401c2c0200702c00801079042d4135006520803441510180b601c0480c0c688121607601d00a003080d0460320503050440c00610094201c0c14000303000749850300b5255101c2c1c901e50b041d64040080001150310006404880c8004000300741c1c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 334403767 1250 334402517 334402547
    0x2032b09060c0b0601050c0f0c18090706050d02070c090903091707141504080303040b06030d080f0403031b180f05060304140a08120402040e010614010302160f05010c 73
    0x46005180090141901c02d40e8800244904001800100d80343d02c0f540c20b480002c199801102c2e000c0780303484d881984410240794120300540914010911115100e000140900861b0005041c140d203021030480f440c2d000100400c0c0802d4082200e00081406954254081c2c0600613001610380c100b0f01d405019004550721000c2070486600c3c600048400c080b0f8003d045891540202c120a0143c01c00201252480c00302800240c1c2c0104002c20100030000c0994419403051400390307416222442015910110b22065100044800c0005a80c14003c0803086404c24420b040c0414a1071030300407a0180100b10398070716000281f4820300c984688141115050007458800c04042c40503041401203022840000c201801c0e40a1100c25016000800c100b0110019000802280c48055020407111102420b44050788650b040c00814400b9050600c5058212000c2a4040700c6a055080041d0301039042201d5250440301d48d010b40c64003091400c0070449260b44180c00029100c441020060480e104000c011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 334405017 1250 334403767 334403777
    0x5120a060909110913150c0c050114010612060302032d0105010602030307020c0a082104180219050a08041e02031f06082e0b0415050a05010c0c14030a02032b 69
    0x170b80b0206102801d042041c1902000125104503010001d460544442d070707006155605e000700101d48100801c0085059030900d564642c07080c140103a0042c09d42d0b156000280d415002231014241d03a10703841e2811080e0f000a4061100c6418100c1180c9084420980c05880540c1002082041041d4117004001c4485001c82e20004910b0905001079500c152107408a41d8480070740c004040105a04001d542c0104440074001020580c401804d002a401401c0e003040040e1104c541500001e00400a40366071080d81e550f502855502c0c0c1e20b450345003500e013001c1d0200c03180c4450400000341e2002d02c014080c0100c0c0c0c0c4e000224401ca86401081216801d6120000b960000810b000208601e2403c19100c8000c41c0d000d0a00704a00c0c01c4503e004010510f00709030310034a810f031441c2140c07180500c040d045070300031501c0042d9159642e00544180216140c020641c9100103402e0000802c8c0329141c150051000d0304480880b4402c3c2c0c003081c0fa06441080d8205028810780c2c00c07907214041d2046008100b241e51400c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 334406267 1250 334405017 334405051
    0xc1b06072d0b071d120c2404031a1308120a0f060312120b03070504020d2316090501050901080901141801050c0301050105120a0609091109 61
    0x103030007001010070210040c2003100e40d00710018001404000c801140d0824414400c50401400107425455110510a022060341500c03403a00d142c00c0d9803540028440c50080e225140c41c0d40c003040b034021748240700417410500f0700e010522501c90a00160014500c61031359030b00c80d4400c1016941c000e46000b40500c010034405500440000c0f0700900392071024809405003515503c1c0d00c42c105020f0002c980513480c1c00351800300c0000522480b580703440c0c00007100ea2900c5802e05000250042030301e40d440303542601584207140c108107a0509900404007040e0014001401c0d6414140c0c120103d854911400461030144051201c0d0018044032902103400034140764560314a06000a0000c0c0918035449041c8100c0e5400103103108401c0d0030074081c1072161a905402c5190240024070162000f0840601c6980b078840007681c08118507040340d05a8030142c6800d030038160142c41b0300c00c08010081240815a071a02000a14031106000c0d031007226100d044110740000c081c02c184000c0070001881d2424090708090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 334407517 1250 334406267 334406273
    0x501021b0312070c15120c02070e011a0f0a0305191b031109130203090f0c060706020a11030301080109060b010e210a02060d06140a03030819110c1b0607 67
    0x20303126070014844800d079841d00042e080400c0c48101c11740c80681c14000034100208141e610035801208240807210403c00e100f503081040703940c4c60940c0142403280c42c4d81c1006114005003802e01082c0b000340c90303940030300c0c00d076550000280d503402005507072012035151814802d03d508090712005c0e8100d40e003d001c110740c81e0f0065403007010803c82400c10090550b0340005d0344000c103000048030f100c104007500c00c1d03a031200c2d01c0f0300c0a4000c1d13100301ea83e48401c0c0030750380040c000e01c0f4010500805c5c40380001e158508201950319140001d601038030950341481502824484181130904c0658020400c0000000b000242401c1c882c040c0d42d524247c850400c00d40281e00070060343c584c0d68440304a0440d0083c01540900d0044281c501607050501070b60042021a1148400889030060811340388030040701140d4121030024042900090f00001307010034074a00014080c00c5000002001c1c0c02c0100c01d021901c88104200802c4980c0400e180350400c6c3c200140024690b606424031000c4e5103001d0b1002490003030551 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 334408767 1250 334407517 334407523
    0x20f161202070e091902010903060c0e041a031c0509120a030306090e061b090415030c0e09030d02070201020c060d050f0130020303132606040305030106030507090e0c040501021b03 79
    0x215903c0e046442c85c09510a40e4031920460700910781c0448204403803400242c001d001c1d00b0700410030346d101d03e04250781c880c10602e880c04412217440002e0000e1145203500302102070803c400c070041904100c0305101d503080f182d03648140e600801c40c280380a80407003062400d0040640e01690040303e1600d0a01c160a49424000507039540d0080c0480d81c00c83d141800c0000c4050b0030720840d40c0d1180e201d800c00c041407003c1d0b40c1d001d0802049a02c6a035801903e0359403101c40403220035003242c4000c16030304140a1450307454500d4008103580d80c0305105940d4020b10001c0040d2440d04803240542159a8134800c000540200580302030141c401021070220380b415104804035288040101e0909a0080383d08190031501d003001039030703002011845490b0400e034980b6030700c201c00100030f00c203c25041141940b0b0a100c200c00302c0da82d400f541d09075448034a580e0800390150042c00d006003003c002c01070002c200080c202d180c80f0205004038414641141c6d00c034a4407000924114030969001699007828008a01c9a5000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 334410017 1250 334408767 334408783
    0x3031207081018020c07080609060103020d140706110d090503060105041509050a0902030610050a141305181509031b100207031e080402090406020f161202070e09 71
    0x1d103050794aaa6070301c0542854480345500240600c0e4680c002a21505070325000760000c00c2009044403042c1e44c0e00c4c03040584d0360800b5201880c5c103800c840010b00c0941080c201d400c0545024440b0361a2901a00b0072280c07500c40d40394802400503910f490303805842e50003801001803440c1c035460280c1d210b506001c0029242c50040c410a803199541c0c2c8e40301ea06e90030b99000040010048500f0800c420b29101075000003134402c0c42001c91090040d0000200d884841c03003440815500c018003003030b8a203801d03c2c200071146243c101902c3d038010102c054004001500303000b40c5204d01019500c103001004003018040c680700f041480c0c02415440401000301100c2c000090b00c2103451940d50580003100717803002c0c660400595440040d403240c000075026081c1900b0844406400064034481d6500e00824141102d0b5503038151402503100401c2e01c0450086046034001e4011700c4a41070841c0c1c501040c081b0b05201074006440f0480781d88002c1c2c04184030700358060000f50010306800c203c0800034501164555122002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 334411267 1250 334410017 334410031
    0x907090b040b012a051501031202060c07060f0b0904060902040507020c0d0f11032a090702100c030204051c020312031006081906030302060f09030901020c2115090c030312 75
    0x1004a600044c4821510f8450196820100303030303150012040301480307491509000650301c42c0b2162418a5803d440001c205110b261030a0205d800e00d415603072070001918807520134030441600c0d400818030540d940c1418500030361184400280c41c400b580705100030b8603401801c03a001c0d50041c5405901075105d50041e41e030034541c00107844107040e01c41e2400c0f1407c65000e110854151048004030b403003284020540100c0b90602034500c00780d407040300d81042418070301101c900005810072048c4013880c401e217070001c2c000c1d20203d0401500f0b040e2148003042c0c400441d0300303042404900264001066003020f1100b040a03106400ca820318502e0080850500340c8030900c80c140c10410114001411941c0c81c1c2c408000d6041d5440051103110780e03d04009540c2d210549500d600048000c0100e00c051800204480345900180c0142c001e043e0010100b217031402212440c80d14101d1503c0320340d100b85009000c0c6034084201300543c505030f4102204800c1c07030000043c00441c040c0d803040142d030880380010099143e220070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 334412517 1250 334411267 334411307
    0x10510050d021605030a110111090d03030f0203090102070312020a0c0f06111207030b0f01080115110f0604050607050708030c16061514010206220f05060907090b040b01 74
    0x556440604001d1150910f080c0d0f140a030141c94204000010000b08000041c6940303258400181c5141e01d8203d48003880c0030a0940b00c200004145410a0030b01408128043e0400203094120110040b00b66401141c15032842c1e54006140020150800c2200001d04401c403021818040e40e103e026010200011001d0001c8403002c101c00100420b9810044401844407440c544480d0302c009030840b4120240c0701d000c042810090405082d0074200004290704805946550069191220001e00888681c07044400c1102c281a01c13105c2c2c4908001c001d01311264003005250626182c02d01508000016103100300b00501005401d012550000583c1d811940103000307165501c1844c00300850b8454460740c001c200500740012000c851140c2ca80701c00c11682c11000620b10f00d003101e401280c031424200c94800f80410100d11504503038004c3c440ac20710b1a44603614541d46c504007070701c0d014540482180c0c02411a403083d00e083c49001014003030081e01c444181c8081c007082d480100064030204150104c820105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 334413767 1250 334412517 334412527
    0xf0807050411070606090203060f03010209221805030307020c0a1401082d07030b0103180f0f0213050601021b1e04060b07030c0218100b0313060f020d110301051005 72
    0x5040500710754611307900c0201000419500c60351203001e500200c5969114012204e8801340508040c02241c940081c0100310301c0003a1041c00c03280010402c44051070328407aa03200e1800d800041c0d00e545030707500c660041c002107842e4a041c000003860404013046040c0502d2541400700040c1000c41003402c5a0f0400742010011079442d80200c211101d0040504c070303d1007a41c0703800189106070400e43c0c14082c210942c2c003803204c80d81c2c090044d002e44800c071030000788528000c9001c1c2c0100f0341c00e0504070b038000d11508000405c884035400180d02034190043c50440d01d0382e982c090100c1e80da01044134110741020310394030042a00421000489510171418510343c1e200100701c2c080c015039a00c4c2d001c400030740401541c0075111070f5181801000345030581d000301e0081c03c076407007828450103e544146116040400700703001c0d00343c20201440c000c1c0e00b01a011003680030841c805c880c0055050301804e1520000c140c40180c403164a60220b105446c90f501209417944420001070000d500c9099130140c1ea00c07120300700a941c80c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 334415017 1250 334413767 334413791
    0x150b0a0b090f0a2403110318010b01180306110c06090d030513020904120c140a020406050402120103030507051603030c02030c010f050d1a040218011e020a030c02030f0a080307090f08070504 83
    0x6d0141107400d9540101c00004011403401c041e2080304003d9402c000800802c0c81074001941c00e140d112040030f8140e2a4a0f404000141264110140400a8109080c1010f618041151415005032904080c907003105c0d2346c0b803018503403511600c0da1089405141c40c0352403013103802042135051301400c060555000200c46004c61405592500c00e5241d0004000e130395072030b100c1d26040e15600403c100300c3c80346050000000c5e8a141900030794805209844c10405507900e076540a4440d944521011243c1c0c0c040d07803000311001d0400e103440300020f501a0316130200e0751942c0e01c101030410303c01c0964503050103203080d218440c1c587d0000a88904408a0000080c802983c0748103245d41042c2120040d03101c3c1c00001d40a80354101c00148001c1d400c0b003a01c8812042c0441218552202c03005144600141c0c0103018103800b080c4141c0c0300860b0503001905903921003030709441e02800c0a00070b80c0192100300300001804061980141080018485801100121400c0810340c0707442c0d41c01741c42400d204688640d210840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 334416267 1250 334415017 334415021
    0xc06250813020901080303091614060702030703080c030910051822050a020a091a0f0f07021306080f0714090a020c07290405010804150b0a0b090f0a2403 67
    0x1c40c0c000704900b4041da50b03844607954940c81141c4440142c06035a6003500060541000041512000802050048140303c1481505d400c050001d07a4584500721000010690440090030480000d0000e595210071440c144206245060411420072508026901072120f028603400e0002400710340240d69290751880480c00072401c102014001d620b4030062000ca1691580184100e81c01912240c10300c599400e0007241c507144030038407050a0202001001c12081c038901c0100b00c0d00e1441c04031142001125000700f134106045050035030034079139240d500340b029803003c2210078020b020100c01080340900b417000003103590303c0b150400c50198441d4030114003d04403940581e485080380d0012105200c0d5283e40f52114500b001b41c94003010b0a00401072481c090344a802c95050f0340d01078403510810f440c0e6a403010000e074a00c18039103000c02e5881401100c44d41da040580002002400c0d90076840701251810084944a1500a90320409480d0307010041014400381640c81c0b640c068a0125001d0700328281a00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 334417517 1250 334416267 334416301
    0x10806131518050406050c04030218060402160308070806090c0d1109040912090602060f0705070201110d05090108090109120503130606030311060a0c0917010e06010b0c062508 77
    0x700b020b18801468440d0031150300c454456802100103200a40b2031502c0004180700310301000c1c3d00a012115902e8150805d021450742282000d0401854001120b1048684429101c8101d00003070048092000b25a40710340282d4100b02c1c108c408080904141c4040500d5104890310548844e0702c0790101c200b020300d241306803040a1009801070003050400d10f0428840702d41c0340d0f1144089810140040b6900c0c0c4000b490782c0c8203050812180c401a21002c03400d96442e04541ea00701e04100d40312101020410007808004001c1e0001d0b21850b8030f805003100054901d0301c00601440941c7c0c581690704010480c1000644807803080c80c1080ba941c3d44501422064110710650b02421903424103800008041d8440921494108200d05462240c0c0751043c0e50300c1560500280c0c5000225603030020301c8043c1401c10294100030b4040000200c46031602869810b0070401d82c0007014cc2403002c40ca420200106201c8103074096040004032001d801d6815085040c68410b4900c0420040316800288900950140e248 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 334418767 1250 334417517 334417529
    0xb1b010212130b0106020604110d0809040e0303180102070809010f05070f030504050405060405100b0f070b011502011b0f140f0d0f0c0f0c062d02070203010b0108061315 74
    0x14009103000c10602d421504551021240e0465034000000c032288086405405150f10845110380e450000041014250071014140c954803800c12003031742196180d10a0401555480300a9a02c03480d0442401000402142240791141d004125103000180c0078012940d2410090130941d0032080012400c5074140550003005221b200d0001c00c0c607090581000180c0219281280d051100d40d640307506000035a102030700c3c1c54440c020071072000c0c4017198120740500458520300c4001030030f24030309031192102ca86c003c3e0303c0341c59824105850a40c5040d42030094041302c8203994040c0f40c015140310310003010000741c08603034400c0200d800e0003a0081c070700010868041c0502c2401d280e46905600d00124001d1a00c48070610440c0d1400c0c004240315030184003842c044007043d403901c07441c0c82e00341d44500000e401d188040440d01e5134002121030b840c40703a140c1c800026000365480141c681d0700c05e1040c1800c40381d808000a051150b8401000306555415150300d8040c10f04420205440c0604015080d541410b60009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 334420017 1250 334418767 334418797
    0x601170304032a090603050c0405040201020f0a0303050610030c0518010302160506100e0105152206120c021204090b0409050304090227030c06071a0403050a11070b1b0102 75
    0x40501100300400001c60880703c101c0400b9190351030341280211100c5110040c2580c215200c001110f2401d541324a5000c0e00600560705842c00218040d410b00c40001c1d821000b1a51306d00c140021410300d00c00c041c2004042c0c0c18208040760b001c10340502640581400d65900d05400544c040c3c443c0d200760141c03408500114901003050083e450b100d600c4000031143d8607605e040819000515000e49100b280c1214030241c04610800e4480f42031400c1580070401340d090800c0d000c3c0410840031181040c040c010489550b43e0395481034a0600d840a88140e010301c90219488503e010b440502403000300d5023201d900c41780004548201d10301040280c041d40f18041c2c054000490001001e02140c1c00500c0c00340844800f20f80c01c4503030241401070008406442da034060748800828405410220001c010241c020071000788010018030642e1040c100445044002030790118101100d1900202d2081d44000080003030111207040c620340e038038140110000c0031020385e21140351103d03110084d412a0004181b00b590 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 334421267 1250 334420017 334420043
    0x201200a0507180e0703020a0b09060c030a0e030d170c03040311071403150c030c07080409020a030207060e19081305030109110907141204021f030c090b07020102060117030403 77
    0xc803c4441c44a2502402ca0500d00b5449540b6004a52442902d074000c0490b1385203810702c000058990040703018903401010410101c80c00b83d900b04040c1c091801d01340d4030341d4802d1242c3c0d0249030419510a400d0780600c048182c482c01b4501003031003450760200680e149113880c0c0d50341d4103044070000c0c990101c0050900451a01003130112102044406030301040d4121070180094022403c1d1001003200c0d40800702e02c0130701c0803600004080c0000c2034428001c9010034181922503113288201ea01450039800441d60004514003002018040d08440c0c810503c0504a6043d901d02c0100d2141c81c2c4030350081ca9000e0000b60040c40390f9032002d40801504014008000100307036480c0c43d00b010104003d01602c82c0c4004400192424441d140d180100c1c3c64202c0f501e42000105044843d0245000d44101c1c0e000c60384100c05010b00c8000c8004150704003941e90081356540320b606024182d4a0a50002e0104031010032201c80982d0b000502c031411107a003c9000b403002c24500b400c140c110f01598000400100d8610b20f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 334422517 1250 334421267 334421279
    0x30b06070f05070501050f0915120109021309050403200304090606110f010e0d0e18040317070503240f0d0c060f080105130203100e090a05190201200a0507 68
    0x3688550700c6101c0c1085071501d0340c45200554a50103000190314204030b081040a1160410030411044000340003003003820a6100016456080c0c0240c004c402c00380d0b07020a41040120041c25103500510012400300058241074400400c08100c8407000342800303000d4030381c00030496820000c40c7c00a1141d400100326032601c54800a2203099580d070040401c0c401c507220b050500106120314440c0100d10781c02064a01e1081034192070503180100442d5226010125038001241440e40480c4110320964540c0a00c1050001120b00740c84058480000c00c1000d10810103801420310030514100c91514501441500503000103001d05104012150440f07001d103005010001e46900d5002650099129404a452444401c031000d0809109007644a44ea4030046489568958003c41c0c100040804a019550b1510204880c140301902c001c00d442d1700c60105103040c401c0c1482010803c0c82d20400600180302d085d0002440914a007007041d41c1c540b80e0103248107808008014900ba1903900005840314156584 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 334423767 1250 334422517 334422533
    0x308040e100312120b04020a0804030809010e010c0c0201021c0504090f020903011802030d080f0402040504060212091006060201090b0c0a210b0109050f090a150b040801020a031d060c0703030b0607 86
    0xc3c1140308241403e89521441c41c080c026248000308e595281491640d80b0340b011248131201404e2a8615543d0740104148410300380200c4603190f82c59101d444995015100091800080c002c1c1200038803844640382c00416807080c121012927080b0800400c6141a450044c0300034494400f195906610301030301f0355108940d41c01c2d0a00c08030300032825940a2801000c09451007502100d8040d5281000c1e000580145403560146421500075000113044c2985210300e5560080151032006c0c0c540d0141c0058082007040b80641c0c00540090b00c003d00001416640e10000350030041c04000710036002286406610b17101c3c0c40e240008048101c0f280b5501d85240c0301c1c20b0000c100f10b0341051b00103210000041041d080180c2c2c030140400d80644845041c0da2410702c400b0080c07500c28408080c906107010700041740004600034002078194140016550318507610050b08584400c2220003944154400c007400481000c18041e5100f410700c0070055403007034a403901700c0c010a140d41300103601010102c0c152007440700715 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 334425017 1250 334423767 334423787
    0x190905150607050606010503100e0f180c0105430b010b03040506070c021c0c0e0109090f1707170a03050a290d140f060a060308040e100312 61
    0x103035080d4100c48190014064035228000700070b01554000303004161254032903401198000241000340b6201c82c1c89003042d20494206130340f29160301d00804103001c88946094004248040141c004007000076020b00040c025004880c0381e02c00e50400c00c8c140c03e02081e68001c0c10030204104804006083c40c110510101802080906641580c0024004618001e0803000c0701d000c0c0d0b400000401545e515100220380ca5080e407030381240c00803034840400d12030303800c5420320001c80361040c514812298208140c42c010040f0581c01600740904241c40718000c24285540d15060581065407107406004494545003c1cac85100320062156481e80c238603541e0b1400e1080541203e4000390b17000d01550700e614046500b41c440c80d0415071104403001c120317040010325034030030030301c0128024010700b0813039440c0d48a08100b0701004000d94250b410102029030200024403010394081410501013000c5411604c1c1d110311406a4055804800c01403400700301c3d81801c003201c490046d6800501300e01041d924040003800305100c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 334426267 1250 334425017 334425031
    0x1e040f03020f240c1009080f0c010b04051314060103080a050a05040b03012c07140c01060312020304150f08010330020c01020c09131e06090c0f0510090b09190905 71
    0xa25117002030394458600842c8207031600031034280d052908a10300c4c600c02da800108503540b25907959101da0702c04c1e00d0768000c803803040d60001a034401a0081382441e0920003505103c521442e04000010310003d0281c005450040e541458002d89490341100c01351038070f04c29a000001042408000000c2e0051816010b611035002609104501c0c044010300420848003510300c6008124800044100d0820404c003828821032140000f041071641c07502d5078200015241c1030540141c2000505004405603080701c600c40c00311074a46201c03000a4402d0042001b4010700008003940242e0800c0051100b0b94005898844500240f01d800001044000380d56030a041518134003500842600d81010f20b040036030b0900c910034210a00840385071941c1c1c2c00d103000c030046887e4200006903502240c00709035144070300d1060b58420031100d1901402c08098100054042d0302c130303900c2002d074005840303001c9600126445c125000410a40e0302d0f44c0d004400540d1108600040300065200c0110019600403503411040c01850 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 334427517 1250 334426267 334426273
    0x20901050d0513021807091a0915090f030a0308040201080601140a02061603090f061815050603010506040506100c02010905060d02031008070312080703090210051e040f03020f240c 79
    0x103c49005020801710403a004808a180e60100b00141003140507003084d104640d06c00306d4544140d0000090044a10a1071002141404075002409003040030304220440000ca00400352084075640081419034024030003030412142d08040389940e400b8009040c038411a5281094030340c24603040095a8090880c1e50301c0c006c2c40a06d000401043c000c0c81780f9400385800c002041c02c0b009060721a50054955401c070040e100310b05d548207c0c003141d64800c0798900d038038216a000c14182091410582036030342c050101c500c114900002d01ca0240c0c5c030b0300a0308503038031030a0810014000c01c600051700c0c08141075015a8210500142c0e40745540714550003503126411120580b241c2c10b449082c0940e035103945020041004907580b402c1c06882c0d01400030a41c0c400c85500e40840c101d07040c0e9022600b0b4a40d500040c1c00861b1010030071101605e102c50102001c0140300c150b850803e0324208804211100a12000c0e0140c140300c0d0100d0129203501040002c6110b40309480030101980103501d880c0b5902c4002c040210380 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 334428767 1250 334427517 334427539
    0xb09030d03050105010f0315080706020a05010515090105040b0a0e150925180f0b030f070e0f060d0b090414160f090b040b0a0902130f0b030406020901050d051302 71
    0x6402442403d0582d107043c3c2d91a00b0310003c0c290b0603002044141c3e200e428503c90341100003495101000000f01800c0c980d03000d4000043d4616200f030070341d007003c0e108010302c09100d034510442d0740b44e001966046500c122804101c2143c902c2c04181c1c1110303541c010006c0d0180c0c0030200150b11403110300d01c201d00715040d50184030603966070b81109285c011100e01d4442c00d2181c41409140f2754400c1c54000c840d004901104103e05688110b196010b008660140d00150b1000c0200140e40003410b00702980a003090908403510310a17100000e0205104c21040c1e445514082a81d0240b003049a201500404026050380424182410450f900206817441e91101d44600c0c2500410f444c1640200b0044031100c0c00e003807410b0340c1041c41c030322b001c4c007001000c0641160b920402d6101d280d0740c14114100402c007581c2c3c016940c001000d00910706a40740c0c1c204080c88914103c00f0403000020608aa51044d084800103845000840040300d440c420011200c1c8154140307400d124a0103c2c001c01841c2183c0700303c41d0f00c2d000d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 334430017 1250 334428767 334428793
    0xc0d1a251b151a0114030423070e04140606010f0f02011104081b0102030c100507140316080105010302070b1b040e090304090507080403021f0e0f010501050a0504092f04060b0903 78
    0xc1c55001841d4034105e600340082000110315070b0640300015008400081c0c070641a420091424210b5803182c0c0400d501d2409200070f0100303540c0e070507458110301c00c003030030040c9003000c0003030199107650b40c4d500c041104c69429a5603181c400c0d40400586518040400d581c0c0d59101101e580d1000d103d0240150644440a038000c40d60000045590b1901e203400900120b94038005080e00070000140150184001c090705840e81d944c02100440c1b1920313800d061420140917020300104400016005181410301c10040000807075410286154000b4a0342200020b104210b0241d8a46004552003250400711103414032000403004800b410542e04156000c11156980400031204d00c01c09540180140c0c100c40c020755034500f216403a003464807440150100d1003400c160440b40ca040d1120850380c1d102c0e59254014081441c0441e15a0010031040b54180022400d81d2a140c00c424002c6031200203480c03a02515801d000c101920341a40d00e18020010802135645e0310041c0465841000454860b004980c051182 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 334431267 1250 334430017 334430027
    0x15020106030f0b04020f0904150c0801060507060e010b100c050c040b0a090c030e0708070e01120b0c0d0902060706050a050a090302060610020c0d1a251b151a01 70
    0x1241d40007404206800129103645507100f03c040d009a03041504062460025100c402c4240e002c1da00c140c9034100305915080c4140111183c20901104010743c40700100000c1c3e03441403d954102c1e40105000a283c1c5049682a0041c10244501c40c1c00480c918080034449422a041d1500745005a041c0c0d40021480401c200c120b0b10b08001701a0b2000c0850014000c1604a61003141903a5031400c000807010411a0b0302c070319001c0d82d81e000d80125031001509021410140754440c1c010300c220290019825015602d072034407a04001d26112a101010840c46040203481d08820b1820b40c02400e01c958416090070200040c01d000c8070205010f509000104901301e81603c00d01c02550303003507400b81c945601c8080801c5400d1a45000000461183d0220303c915030b03840d1b02481072800c1c400e0340c0c410201115038180c48104080108141c11200000280e0001107080c21042c1022403180c3c0360034a200040484510100065040050400c5044030450589501580d0005141010113104170b0340c8000310f0001120 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 334432517 1250 334431267 334431269
    0x51c020c0306132a03030c05030d050114040e01020c030a0305060a150305010e15030c06031003080f0403050c0102340905150a080c011706040e0d020109150614132415020106 76
    0x80c07041c0c1d134110f040010034450040260303624030540c1641d142c448256020310640f80d00703070010b164212644844150503d0140b1800141418810080d03040650450183e9200d000314034208040c582c40781c0000c4c0c80c9984200d581c4000c1c0480207108000b40801185c024000d080034054400409015400300b10031400750340c01c0b51800b040060041006038000c4043c400c50b03402c09400700003150013408000c00003030341c500702411900204032103481e100c0d451424142e2804401414550540d00110302c5110512a240740485401301156000b08411801840101415080c4c0e8040c200940ca45020b1012220108500410130503085500360310a13621a02c40751f071118151603810b404107c6050710080e002e00a00c030b0450744070764010400560300418806007400c0500e603148400c0142d641d01c080c41c040084507100c4000d443e096034010095541491810510900c046004034070072403410078211411a101e401007482c050080005500ca5079205441e03401c896000d0260300c4480c80f0140c0009a0135105100701d40c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 334433767 1250 334432517 334432583
    0x709050708090a11120307060203190501082806020304030e030c01080108031e041e09150b07061e15060809030a0f0c0f020405010f15020604051c020c030613 69
    0xba00d00699440130340843c00e0184c442d0b00020003100c22070300c034802440030700b541502400c0c0150780d910b00078000501083c10080440682c0389802c00603c1708110014460052070340c0080f50f0300d40021030040d0782403268100003001f02618000020080cc1650180d1445640b910540c1242c0c1041e00390001074030741c4d4009001c0d202c3c05074820b01840ca1040c2d030a41c007284404803107034039042c80c0030380b034580c0101d80403410303481e41034201e803000b008008194130391042030844071a00c150441c4a9041298580b9203100d80304c4044d203019180d412070b40406243c40c051008071850100d04210450948103d591246000d1140001250340c04d000100d00c08004012501088041d984d2000200b069090985080c03d105000342c582c103d22400030070041c1c5407441a01e000c2d101c0c007403001c484ac070301d018084c1e02d1401864203200110b400c16002c1c0320004000051604500d07413a8450340c031024500b042c04920301140c003514680d15224010502246050100c102e404650140c0d2400007107698400c000c40e15401034900c29 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 334435017 1250 334433767 334433773
    0xc0603050a05040b2205120405150f0405040b01180807150206060d17040b040e15060a021e0109050105010e0609011203020706120e0f0f010c0c080403080306030c12070905070809 78
    0xa031150030011781054220100c200189000f580d9900c556240c515182c4940305100d50014083c1710364500700040070810201c6001302494411503072492101405140300e500d0007140c980b503940580e0ba0062818808807405040d21100304c5030342d0b81d14190307503031480c0c07041e40c030095a07040f80700303107100d00c0415854031070400604407188002c00780e0f5541d801c003c81121114801e80c0244404100e5140388001000101120800280f990902d004000c003070400c000c00051007034204001c103002454021501c116040d5441c000d030080e07499500c01041c00741180220040081d440e0200120b52403070880f8005000b001c042d120811641c0c0c9612601031007110740c3c0c9000c0d0269202040401500e88500540004d0001240b0046074013400e07404100d1500022110242c0a90840724a54210820074815040303111414608031402c01c145880340f0060b44a2800003401e00e250001c002080c03510104501590b400c0c002e442c08100c0512003540d29180d2440d40200c5010a0a16000c1207040384140c500e1402240c1c0c04001d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 334436267 1250 334435017 334435021
    0x2a0918140f04030e09090d090b18220f020403060f11030a020903150f180303070c1401060305060f0405060106030c050a03090203070b030109020d05093d090c0603050a05040b 76
    0x70440791018010300890070003108458440081e25521212070044000380000d001a1070034620180550a0b16005030a20034014072151755003400e98104010080403d5581048400301c442d8103021400703076041c4170000d46003041401141c4501590048c42280d0240d0800c2002044802040301a6a2a480c400b0103c0d00140041a5495a40e23402010f90f03000090443c0e002c440c04103904c45074074030f00321090300ea182c05e04010800303400240030010307094112030302c099484e44c41e00810103440310428080161440840d604040e000b03070402d600040180d9007103000c56107a803601d0030030101d034610304813004c48650150301e0000030218040d0183c154041d00980f582c80c14180d04044c11401030052400a9074580b04600e070020b850f041c08001180a0104003401580d02c1081d1600542660f0b800340480f5415030188403034a02021120203100350075001104140d0310030340401c0c1210358003c07041510708403051802100ca01004201c603010b030110346c0c4a032001d000c00d61307440c0464000c0f6181240c001d000070400d000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 334437517 1250 334436267 334436281
    0x606020705100306051009060206130203070b0c0f0708240106050301140d0c08010c03181a04141b040f0207020d0602090102030705010513110603040c092a091814 71
    0x2150a00580c43d00165050740c1d1400113031800035450b4040d001c1038031690309002c00b580c10300c05d1307d42c081070542403000900440e2380030030b9544103184219040070501140800a10000f44810b0310102c90010403210f00740e403030b00c1d2035540f50490000c1c0443e04e00c112040030b9030180490300c00c00303048907010303120141540c0c605038113580c0c1e29102809090707002d002d04514100140000804c00c01505080700009900c0629042c00f400f201e044001000050741d01c068021700080b2090741a610020384801040001c0d2128640b00a240c206d10000b00070900840c0d540000d101c4141203075038040c68003100d06024912064261400302e01c030310000a50441132000e4500046000c50700100403280741841100c2c90044036171522400c50303500341c450910101c911036850051102c0b0355001c1c1d50044040b21294554200707513548082000241c82141030302501d82c5200c5e08500401c5001e141d20308895201c40035900c0141c0f100a1020100e4010946006089200b0900f60071540c420786901d559141010100c4c0d8031501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 334438767 1250 334437517 334437529
    0x30f0706050d0f020c0c01181a0703020c0d140601170c0d0302070f0f080607051611031507031e180215361008070c11030607050c100606020705 63
    0x620b103031460940303400440e100d40d031042c4020846840b000b4098045040c11100042505514401c207403041003034000c007800b0390654520802d050713004405849a681d070302d625041e418010405111980100d03010035200a020b140030610403e1003409050390001e80c1c884850300f140f41c1814042000700c3d40400c40c192a0360404650f80301034140a030040b45d2900703a40d20201903004100d0742113003d05584400081052034401c00002d0342015040c20000c3c2400b03d0811500a80c40444030050100c020148101c411a10306000c1c2c1103460828039401426860410310160141c01c95607400311060b0a00701003010803010600c1014052030342c00094194914507a0200050101207140e01300c000c007802c114055076107030305031600f940c2e03003008000c0110117582c2480108200384480c41414094949650b174007001c240d010f50000d0780682c25003440c003514503550a003480c20021490003a40c040c440c840600044603040400381c042c038908001100c4604400d81a8001624100e2058001690090100b030080307127061 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 334440017 1250 334438767 334438777
    0x17011505070c080106080f0f1c0815030109060c0206062407030e06070302070806010602060601051b0a0f0c050307050105090934030c09050f03120d14040501140105030f070605 77
    0x82c941400b00162140c00a508507183d640c00310455500c011441e12400c0d1041c402e45000c4044400070303001c0072200d03002c00201c0b07100020300e4034100310b51000060040c0d0a400c00c000c04c5484094001c2050010341e01c0c0810050181001c1c80e0050b01c9814001261440c0c088240c0c05540e2071a4103000c0c1c900781144084100303800587e400c07418425840d401142a44515004c2c0420074003942c000d00350b0522f8003403400d00340b0f04183c00c100115003011081012590700b003000c0700e120440d00003e81442411010280b401e21803180e80007804c91041401e11000c0c02264200c050954000301e0950303010580c2c400044da854401d0b618982d82017408100080c03400490f401904010a01c00801400e440303240c0d02c1c814804160f0380b942100825607034404001201d5000440c540a098199051240302d8200700000b6611400705034008044400056040d80300f006940011035280b414840c880d14504080c5000c0d80030304082402c0c1d400f107100c08800025546000200c800301030b080c10028082041c1055070444460b804 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 334441267 1250 334440017 334440023
    0x1401020a030311040e0f06090709060203090f01031e14090a1109060a03051e0c0a06021c0509060c060108190b010603151a0a0305151003050414011b1701150507 70
    0xf0038000020100c0482c42d40a120300840412201c0c0383c50403000b041141c240150440040150a450502c40160000100d17803203007000303c1b0005124100f01c00100e01400c0a5114100d400c1c6d428000001c01200a800180500801c102061a199282d808d507642c9c0e8450aa4040c00e4070350744000140141c1801ca1350305810010103000080e645440c1c0d11043d140c0070004160b50810041843c2c00c04100506210500700c10404980c0c10240c10b28216000303541da0710029004000801061400f11a01d0146045404105000d42044d40791b480c2e08000c0340e15003000b40f0444503e805a240b00c84000c400f2401d111041d0f55100c20307100c250340d080c14000c0b001000f4081a0000038000c507080460003a2316091050f80c050f901c1c0048035034035204100b00a0070307984041e01a10200700303416840b00c41e0b0b0780e5500d8100c010580d2072030001100e644a08164045411445911440303503c1c01005d070341c07a07030a0014103803a2011180c03180c0c1c1d1495484000400100303001d1088003100101018401107c034070640040a040d40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 334442517 1250 334441267 334441301
    0x130807050114010b130f0617070e0307170106080c1f020a1b0303020c100818070f0b041d0103080a0c2108150103110301090216061404020a1401020a0303 67
    0x501000da20301c2d40c1c42c0a030062581301e0f0003c90940d411007420b1013080094085104025452454001f011340034205075401d5106403a41d8000181c1024403500303840750440c10003012100e04591301c610001c0415843c064848183d42005008a00000009401d80511201410317070340b00c0e60f146003946800b072101c004100301103010f003810501c041480c415940c0341e6105040009084145140b0b03010740741202c10a00c00d802542800c800c0308186410203419035100e41e200300380d541044610700740613080c2900c030f4002c03c403240103401010503400241c03400361040c0c40000c203449600f540ca225056210074000d00c00189011004c000040b141d511644400c90340610844489851880b19404507401d40300d98402440025809000c10628440c410095080c00c7d400303003820461000390526200c4248014084c0011281c0c00060051150760302c19045800244c0280e020010700c81282501c291038541681c01740d01c900c0c00d0070008104014a14903031216014160020038000c0020f5170160050211811010b03c021 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 334443767 1250 334442517 334442531
    0x3020708120406050a050601080601120b12030f030403091719060623040606050f090d0219030c050103051803030708180a0b1803120c09030304181d061308070501 71
    0x90001d900c95801944500c01c041110f1070064683d80846500030142c50400251308180a566600b003502a024080704000108405a0300004500701e101069480c052a220018055080d00c042d60040d50166112350382c1e9a05007a40c1d0a148039100d00d01d003007044210f03000038148104030b100140c00e2070a00c42c404e000105425550f10110340319000300c2900d10010354018101808070b46014800d41000d040b40381807080c2410a1480d040e03007980104405203000e40200e0f1041404c8d5510405080c00107054034456040481d140d02d0605500c40380f074410307607000c242410045100451010a4610300c1990940214215591080304958500001d0107405402080c1000b200075201c06011801c0381d41c0c01210a4800c50510451034903d0300324800301401d05800a200c0120b4459640030140d820a076203158007602c80080c0c8001904502c074a502002c03204c01c16504844c1900c07840e8008102c582d80003034000b001103681c0e01040380c46010403150036404850024413080060045005450444d0154000040300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 334445017 1250 334443767 334443787
    0x303170720010b03070602062e0506030c04031101081306150305030c030901120e2d1504050f0d080a090305040902070b0105130608100504050102120f09010c030209030c0103020708 79
    0x3200d000c000c59030742a515003030001d8081c00d08110440003000e452000703000038076110007200728550074440032081100c0302614850928848040003c084d101c01011996281010011908a64001e104c111107160340c10800c0115580142c2400d44504664000412885016550403000380506000c8030000075001c0c1e030200100b10200b01801d0803406000095641d00030000009d4198110f62007944001801c0c8500310007070140100c3e00700050700080e1010788034088095400041c44044840178002171040e041c00c9d80d14544481429030060313000700107880e43c07060800e0050b91136200c0d181d17a040c0402c0403074020030702090a81e8400542c5500a00e002c070704150721154204183d92260005444000744040144201d2a14860141515961020402070645414805900c0b0b400c4411030814295035500040d081c020290100c65541c40e8118140b082840d1680a400f03000b541500d251030a0b40ca07011510000900074400c80d041766600070000d280c2c004404004401a5012450882e0100400e010303041c20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 334446267 1250 334445017 334445057
    0x609080f011808031f290c070b03060625020108090610050918010509010f0e0a03080a0903050417060702010c0203311502060106021005040b070305041e03080f06010903031707 77
    0x1a24144428901b03043c0e1403005007070480380340d0100c0790710540104003c0b161000c001910a040305e4240c2100d13616031761402c0c0010400e020b041e0a1050915502e1080b40702d803402e400b40f1181c001e100341c0340d070402c2d51140c0c80388982c3d82000711241c0d0180d1501c00028030030391600302c400c154001690b02c4402d0244a0700342d00242962030503190103085a4445444603900040da0243c641500509402407002801a8400a10300400030f0031021005507601c06038000d061060045401511512000711011200c165045545170821201c00d40154641400006220b1010045440558005a022500c42c1130003440000308400e003072401e031040e5a49400004c2617060b000c0009040e480b5038014002541c50400d0103401c0416001444038014075250030440000e051500d96904445e103850000390603641d0785030410080482200d0f000135102203d40f102c040683c80b00740d252145a11a0380741d051a1191001550901c465000c0240031981442c2c08848052098003455400f003103d00d01100706c07000044c02645 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 334447517 1250 334446267 334446269
    0x1209061605011d15090c03120f04050a0b0d0c031503140c03150717010b0a18171006050a03080412060209151b070605030c0901020111040609080f011808031f 69
    0x1a13040720000d103054402d0704580c690b00c00c11180141030900ba100000a1703c3e11b5820904004203030001c1501200c2e80c030950141d40203404090441c596860300c0b1034004005401c03000000d4250303402c00d00700440140c440d0041d0b10800903600c0c14401d055045584186501c0d2141060304010301c1082d82c8210700340d800b0440008120313000040c501c49170819000042c89104002c10007074006030381600400c68800346100b01e038003031041890b201c0201403120450b1000d480183c0c1c407881400030740d24018070640f5000b050710035030349040f072204000c00c075940c00074403656000c00c1c40301420100303060008000085a00142c503840381d100d030400604d0050b1310000241d001400a1044480d014003162807510040314103522055241500000c044880c036242d4006c05911008202c03020801c000300b4481441d900075008512380329500c0709003a8551342c5032035004002c0c45e01032107400941d01c0b079001a0582210184507815482510009184100300551100d0105510140882c90210418000340800c030b000d40c52200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 334448767 1250 334447517 334447571
    0x309050105090d1a0906070c0506010905091501060504061d0a0b0915040e043005090105040e0a020307140f0708070f0b041101080619050d030302090a1205120906160501 74
    0x744980c208545c26901c0c00c10018486414465046d1003d404101c0c0040c1c0c05044412541020409517035801c1c240d42490b40046404030084045000401c440d80c026010344255401c966400307100c0c42c0300c0d020b078000e480c041490361900519859402c4c0000910741d4000c01c0003c1000d8030110f0202909401141c1c1c0d54410342c4144190001e04080c001000130002c0e05501e01041e00140f40c903100024100c0003101c02c0c14404d50780500500007881900399000e8410f540082004e410b14890702e28041d0f140707001951044981f0400260b12041c04201c518451065600090054211904201655480c0c01440d0f20454080d03424010a60007030b0002981c0e540349501c41d030712800001c1003800e0460009400b54202400c0d031489075408a035080c5514003102d0703990701225800c6824100010503400d040e0002c0c8103100b07005803c04156180032861340c002d41c01035034100344182c080715070f4128160b0b803040341c4c3d01550b0010b40d444402005125210700b20203a40a00c000d00490001034240c0e940302214807403e0a2540030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 334450017 1250 334448767 334448813
    0x7090506031002121602010b0a061716021c020102040b03091e060601141b160e0c0405090105130e0717010f0e030909090a0213020c06090a0309050105090d 68
    0x3000ca81002e020030709540224100039418581c02d5200690395003030003003101c01d810542c0000185424401d411034002d0300005030003011a1504c805005210001c2c2d205c4d02c010317601810010805003600c001d0822010101940901640400a003001c4020340c40f003011402199002c0c000400c1d40740700c3c07800a50003021300d2001032010a007030290702c44504400c9083c902d602c2e0080010084141d81010318460240d049002c019954450468000b40904a0160389041842103550349104905485400010307180c101c040c241c803541e07400d51585c00e03900c2503015480c0c1000b4104010005c40c20400900012490300741008900c000400c1042482c007022a4000502201e82002141c4028400c0c8201e8864218183c03050210038845044240e030b80c45070603034140c0034200c1c0c4000205403030428807042144507070007443c0d4003c0c00088206040603401910000c0514002d0b072011601c0c0040001d110150540d060311001c025030f02e02401501c09801c20103c4075041070010141c480000c05d01000342d56800c54180076 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 334451267 1250 334450017 334450021
    0x1c08040902130819021c1a07020c01120204140907110f01020912010603020303031f030c0e10090c02060414250303080903040b0906070f05030a090e070207050a140111070905 76
    0x341c3c0b61000f05000701c1c008001804c40340015864001e03484e000c444c07500781e44160b02039840c64600340c161a030764031a0461580d550280504a030380455030001c3d41c5c00998901c24802041040c0104912441c45540c10941300e41010150034180305481c00d80c0400b503130600e840c8245550200394280400e403079800c141650b0000e241e00007803900c290114201c2c010100200900303411940803036503a10014000c40710550031090440d02108421145070702441e400604804103990780c14510298a600340e030140391064420b600842c07080220b21681441751410f41c0240b0711a162a1910b4480390100c14059141c0e004108107802c5283c210070280450454880200080074650305004125082c00b034a1400142c10402040169a02c080b0a8175215841154619502c013134a00d004400800301c4800181540808a0008081500a071001089a110f01903103140c40d624818103e81b204900d0003055807100c109401031000400e80890034420307a2060600171790401d2030703101c03031842c021095220502c1705440d081 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 334452517 1250 334451267 334451279
    0x60b21010e160305060a02071b03080a12020a08270d0507150b06030106030c050418050604060f0b180301060305071502010f050105010f210234021c0804090213 70
    0x1040b00290040107240da803016096642d25600ca0704094041c0c1d0740c00f80c0208010083c0916140c50081445000560b154696900d07d0545101d801685419000c211406001c070b80200b0b4038002c80b00c86042075a101c014943e00c0c034080b2400c0e00702c806041030104040b5017182236040420403c21b0208101c3d91074080c1c40308c1c018a0701003100c01403a481e00e0040e9007400c145030396030b0700c5803000d9906444181c18040340c0181514400c8880d401a680700700304180800503000ca40350b00c107a12903402108190750502955486901b02c14030b41d00113104003810b060040001c00381010020380d0310300c0508001400410040d9880e1a010700d000040d402132031925a00c0b256440d0119024451900000000d031000d200d107600d401d0000e8070b019443d80c10b15081c8103600594212404072002d90f400b040300b00410464a0f10702c520f40c0d041081e1071907442c0307007140030031042c0140203541a041c1031254954010f1142980e00ca02c40300029000c0a5075104985001c028440820781c00e440c2d001400080710411944541589044 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 334453767 1250 334452517 334452523
    0x1003060e062b050a050303100305100b010f110709020f1213020a0e09031303080408011401121e1205030a060b160b1003050a0f0209060a080703060b21010e 68
    0x1628842c400c0100802c0d0180b9004000c18200d20b03850740c1c003008800881c0034188507084c242403200c000d0850100000300200c41c829800724005583c0254210f071102450b68a81c034007290300d07010a09002c503e4001e580040f0a20075200814130b54101016900c62543c2d914440b42640c021508c00c3e40d45000109116103403c0d242c1e080c0e50740c010324410407603460341480e80200780d500342c80e4051030340350082c0600010042d940800445032039a400d60708841009a880c1006005a002805101c00035401d12100c0084100c0b5036107140d05807180300c42508140404d580c0e850910010200800c5440100b030700c15800032070741c0d030503d541407a1019114950b892034950714401c120b07501c682044418010901202521050405a10f00032a51110900c132482d200d03590008260102540010003030300c00e030400c4408001c0c00ea400200c02520a950f0f45199171216030422845000500079070445511000341003000c030302103801c0303811502c2d000b030030f19020700b0030700c08400441e808400940380303060b074491000481c90f900070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 334455017 1250 334453767 334453771
    0x306010809030a2c1207081605090606160c1206200714120706020d0b0901031709010e130e0d0e0102101e020a020d080604090b040209151003060e 64
    0x5202640c0352840300c4074054032044100040590076060103c150155a5825001042c400d200a00440418902ca40115a280c10034011600709010361b400c03054506815800d1901903803002030520311252f8554044c0000c6400c03e80c00d02ca00800990403444c0410b60700007414004c1d040c100c1000e050300c40c141c1082d6054401980c12048800110040940032680100c19105615480020b045924000c40405407a01024004810021070000b80c6e02c401c1202940c001c000403c2541000c0c400400060f0402c4400c41c024072010703010082c00500d080e407090021000744100d0205040201050030b421011507a2416075544140f095035440e91241400c036020044c071484805145402c54000540d900000e4403602c8844000d13400715140c0c2200303a0303410000380407a82c062620b07807c21525031860b541c0003951500520302010100381084041411820f10b405031041e0542c010080c47c0c11521540d092058001c8004c02c00e071002404c400d41410103595882c146024141540c0e00442c0650609003c42011100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 334456267 1250 334455017 334455031
    0x403030e0303041505060a030510240f03020118120627150f0204090f0b090106090b190333170c0609180403020d1b0308060913060207060203060108 65
    0xa00070000003c0c2c804000715004c42030000041340d1502c400340450703110450354200411034026000340c000c520344d036035000350358040c5e070403c86144209210721000d525000f40d0241040b0000c1c03c090a0016500603c20f0442450f00000c05ea42555030720b125001056401c0607040300e41545958840280307481401c24211072008103004444826400d903600b4012225103004100d260b916410904010401603041e6002481480320502c41d49080d240b0f910f00800340b24220500c547e80d0b100001c1000c91060107000705491116070b5251800080b10203010021517142d020400301915039003104920258042c01c40070014480b0f46009407a140205085040b5240b90000003201400000440c1c2d100f038002140d042d1006c00395401ca50b03550074100030404021000464400280707010041c0010564006415408240156aa200b20765070001c01103641d41004d10f0043d00080d0594045002403a041c9000368010101d4028140c81e1115030313071102d0503030300103280655119034040100455540c00070002940300c10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 334457517 1250 334456267 334456273
    0xc09030c0e09100c02010924060f06080f060a12050a030e1c0618230c060306011d01021606080906091603320604021203040f0b0702061905030403030e 66
    0x5080d5040741d03641d50700e00d8881c0f141c0d140c40700b41050f42e060007944107aa13a540c0110f2032290f02408003210071084c88140340380c41d07801c41c070f00480052440600b80c0030400392031a07030b42c1c1d0f900642c4581c110b201c8c81c01d6010702842da00401c00500010200c20b2221540f030424841d001070010f0800c581000342401720740a8030036021b0511401240803007892803440300307445a80a80c2c0011072502004881819000c1c41c01d00408041c1d851001d409012102c00c0c803d414000104111054904403d00f404114003013607607807d02066410304842c50318803002c006201c003e88188111801101468a85401ca8402e0f5010401140d00581400b00150084c01b500c4d601040240c0100f403c0a1100341d03040d03c0207050b2001812040c029001c00c59000c807503411101c0c202500c48122401000b506243c19160681620b04038400e90048160030000b60010064904482921140c82c401c2c80c41d10041d050541d00500c0200d0384190100810440c0c02000d0211040891a0f9a681c2d6143d152600c0c019044951002005920358 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 334458767 1250 334457517 334457521
    0x70e1002120a0c060f18060609090b0a0b041e020702031204290403023105010b09060d0b03060108010c110703050d0507050c0a15090e0408041a0d0c09030c0e 69
    0x855a000b2a80a05a2850328021040060412000804c1360b00c3c0d8802402d0708103100c16001c060b014407a017111034000d0004004180d074030000d440440305c1c110f0000f00301c01c0c42e950020364115520b030700800a00c030b0701a201150000390a852134603c10080c600c200c0034954042005c0e001c5d41000c00c000343d60032900440c0c603403919080c400c604920f60582460305203c80c0743c4d4006400b20142c83d8041c0d0b0700556001e000404012409003040e10810000c00952182248060741002d45502600586040303814400d00d480c40c00c00c101c03040c0316407607010a1140421070f071185c0c030303010040e01d040120900920841000003441e041000008080a03000740030440c0c1e0764001c810034400f14601040c0c0d008900791505100d9918500340c43c2490901410080e015409201e03030000184103d40851070011b00300c2155200c000c0552100038500e01d00500745c0300a00030300401d00080c454007101d0160300e0306d1214000040d07402c001182c0207540681d10290080c000081d0038040c204100000100a80050400003143d0b01481c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 334460017 1250 334458767 334458793
    0x906050a0e0c1c14030c0114090109030f14040e0406051e15010309020a051306050109170c090a0216111c020102190201031104060810050d05150a060b03070e1002 71
    0x1840301e000f00c3c0c2e200d9454428500c42004180000030b00c0410840081c1c0707840d998141034290003401c5407440e42c1c0d041b01081c80000d0180d0b01c103100e20442c2990549454052210480c1c00716007841c00c480319101213440420001c98081c00d0303070046500c114802d00001c82e403072078561860008400c456025128022446091108101c030208240b04202800c1c640040c0c107403041d00010741100211341c084c42d041381407900400442c0704146c0041c1c040c1c41c4281c8402200740d586101541564110504d000c400b600254410301e813502d040320b000b07a046081e152000d0700b002030910003a490425a884101c4860000e1484100c4900b030088440444040c52070b802d00e151001c5400213520741000c41892132000c07030a0340e0b07a542168020b520120f12110b15041c10717601c840d118200609000000d0f43c00724044001034800040034501500c0940b0459841005000d0805d1040c8140c95a440050452411070752140000310305510710501461041c01d055846001c8100018240030002e0b04084a0404640006441c00c504c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 334461267 1250 334460017 334460029
    0x605011814010c0f05060403020105150a0b0f04030501060f0609141309050109050601140f040509030f030c0705010903051b010e0d0f0e040c02030a1403070804030e0111010906050a0e0c 81
    0x45400203902080401c01c00c0c80121140340255500600c3c0407810111300701030240010380c061082d417080c2c000f08003d8650482100c43e5520380b2010aa01c410906800e008030344180010b440d55041039520f05050580720b584030760035074616810040c070014000c01d04205a540c0810900300070305987c41120030414011001c19140780001161014264032807891904204003507001002058000c010780e075055844400c10b0340c184000407056441101c004001d0070051a00340b040c0c6000700131003002149031101c800620017003600300610000302e0880a00c211400301c1c0c028080d00d07645c0d9210740d941540e200000c800a070110003c158804580b40e140c10400420f43c0c1000446600da00c406007000078402440050481d07108480c1d40070150002c2c2010003940c51150004080c00007050a500c4070384842c4c02480100e490360008480d40340c0042d540002040101707000b4510000b4048041c989034188920001d909829609200c0044482d146c0e103804000300070b8a00c0c800c00341c10030344420140900002c10300001e10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 334462517 1250 334461267 334461269
    0x30201120207030203130b030603122502030a06050a15170703080d06050a080106090b03061b030a111b071202210a14031324110c06130906050118 64
    0x8003065001030340360b05150080007515109110795544880f030540b60107400200d600b003504c18601a00c1112400f4a207859144103554070035050102d0112081c0c90484061041d05039120180e030180107840c54003000c07900a0190310300c03500c005040417400894081c040d030031900c401d80c814640844405504240403e001c1980b9003281d030021100d03602d030031040c1c0c0c10301c00500503503000b56031028000000140024041d04801c040f14a03030300040080d21210380038992141c50840e8884a00f6030381e00303a10103110500c10051030704003100e24000030344407664102e5100c5541c00000390407280690841080c5c0351b148100030300d4001d000e540c0140c220309850303035010641040000c0c0d250252071144c5500c940d0251400c00040888903000300d800408141000d25094580e48400582d0310603002c131940110b002035000504e000c0e14401a8460380e802000420216600404540c079803209000c0d0303915000c5c099407001d000c6e00390085551500152503292a410f6002c4030715952215062141221280c0803240c0411443c034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 334463767 1250 334462517 334462547
    0x121801090302220209030d0e03070e0402060301090e0c060c010917040b1605160b1e0f0a1b020a0b0a11010b010203040b0a0908031204261602010c0507061e030501030201 74
    0xc0e601c183d000072006070040150494040c82240c20a40c0d11070750281010b00c1ca0181070f0b080c2d905640e01d1f042c25490340c0804035401394001a042004200900940e40140c002550040565502100e074200090f0700d503000c1c3c0d0036140f090b911180c001007845240080400700340c2c0010070481c509803a201190303403180035084444d03e11b5022902880d003400004c3c0040221540011040c02e617454035a000040b00d81c10500521003256521156142124600c804a8032140c21010049040c400034140c00c4031806103556807032080b0701540100c0001601c0c2c013140c0c60f0150000706065602d0385d0100c0b074000c3c812440241c506c0141da04142070110540d80100c00c65082c3d076988040f01b6a0350b200c4e2101518402c046074040030b83c603c000542c684900400c02d403114083c600c1b8420003004060600d1020b04009070303004400d490403000300300e03e00301d4043c0701c0a88095244181001000300c0c6154596500b40202e42d070206010400c500b800a2000c90f40030f19194600146040c108115411500000c141a1b4020505 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 334465017 1250 334463767 334463809
    0x60405100c0e03070806011509060813141509010f0603021509031f021b1507030e010e0616090608040809010f0905100c0302010e0106031505040303020408121801090302 74
    0x9600751901c90200c502068101500300d81e600c50740c1d2030116503208001d204002c43c4494182540c107040380304030104401c07140ea03680c58000c142c807980c0a40500d15801582111240395891401444140c00c2c881e107500543d00c002016400c1c900300300c1c1e031401e640d10607224030340c2540703410070910040c0d850107020144c40c225209010741780c0c2341500101e80360040301742402409400405241404c130410360010320f4901d050380d4000310403016220509a450b1590001ca450b01c6c00c07880c001036000c501c20307032083c8581070301d142c00452040e0000305003500340304090700c003001b030f01c400c0c0036600c0d0b001a080000704d4001c004ca880c4c002150b00c0c2c00d841c0d17494580030760b845481c1000b61075440059182e2040015401911b4014803c821819460710b010740300f520700e1074046016500305140c500d940c401c18400c0c80b0849400401003d08009030103880c0005000042084080c1a800d00004c58980d00420a82d8040d51407079050940e9841c051008168026042071100c4c10400300d4801800140c40d1003005800e120ba039010f003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 334466267 1250 334465017 334465031
    0x60907030e21130806100f0303120b0604230909070605040e1504060b0c12040b0d0908120f09160b0f03040f02030d050a1b02062508030c07020906010206040510 70
    0xd9040346200d101c20b1203440c480c81d0b0401003500500412841d00071b00010050b40201540e40e00c0003246500c0c3c510014000c105503581c1144107a8003900420304900d802405940f5060300c800c1d1560500030300225141e03128981251104203070506406807030b00222010010040d01d4600f100c0189148110302072140b20344407420100c0c0305402c0d04261006e00c004024014011551a181006042d400c040d890603118441c000364900703403641d10021141501c100c580001d1070704c0e0541c1582030103840080790895200c001040003040c000781070300c031480c01014601c1d8a20127909100c090b9500d04032a20684809445039924100105c51000080300d140c01e101800341c980b242c0c0e65041400d08a0b10b0404040d405000d41c070514a0020340c00300043c240c1280d151030740c0100400e1150b801d1070120700c4401c000e400540420481d6404052401c81604d42000c108110003503003003e80c0c46580541003510104c006010200d4413404620301000b16680c440c00a00c010a013924140d12032035654131030012084502d039a5040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 334467517 1250 334466267 334466323
    0x50a030f080c010204090504030e10091710061203111504020103090203010902040f05100f120609080c1b1c0f0b100e13030318080307050f070f030206060907030e 71
    0x402d9901c41c0007084000c5407903664500f901d001030207044034100e0002e150910f01c0704141c0791200c1c8000780c9854541d255810f07541040300203034036005c005100e041030b881380030029680c0c0c0d080b50059002410490315000313014461858058804039588000c1c3c5501d0f08003503c1c0322011203d03121a03a52042c0c0918010403e5022400030a00422030740c10060b411074140350b14158101443c0e0402030040028142545040c2d0340c911007001100300c81c2c060512460806010300b00480d409401180c00d0601a00394249800c2c51100d601e07140000d10360029048000a1507003489a190807250550300d40811100c4246004d8203603582403001241080c0204030590400c040703140811750b81c0c429000f40609251000b07003414091940318044213a03100440c0001c0c1090540074a030f0443c69481002c1c540d20000d944d00b1a200c101040d150380e048243c210040400500c00c0b4130110f48407a184403141c0c1d000e40c010302100c3c03d1220520a403504010308940c1818244a80c224410348005100d6040800340c07403012034450b101c41c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 334468767 1250 334467517 334467533
    0xc150a020c09070c020402030a050f0a02090901033f1e02031902070b13050f03031603030f0b06071a1812090303161a060f0603010918051222050a030f 66
    0x744d40a90090720210401c07501030090350207070f40260801c0d880100980d83d921850f100380e200700d003110707900401054010000034400d0009110107103160401c03444400401400f118811805a1803102c1c2401c07405a0348030703155041503408078402c0c1507000910000d401200041e5803886032020700200755181e50710b016030703941c401d10024000d4200e4007030584d03076500023a4050904505c07501402d8890301c021034040300c1501d8000111085415204a0152002d0050700c2c07e400500f00c161609400d0b135254a020041562008000e00c003061064a00c0c504801d14262440c04d0140c0041510131000400700c5205800b003000181c107032107120324280c001c0e40c0300701007408a8114090000c074100c0768036180d07580e01e00300305003410800207041c110103040300300e81c1d00c02080000580d011314255401c03800802c0144040d030030f65041018108143c2d2101100700140b80d942c0d500c0c0039240c50500c03540010100750840c4001c40401e6200d0401c1c04801742c00c5001e800d041c0080d41813180c61100414007540752050702c041000c42 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 334470017 1250 334468767 334468787
    0xa0e0603070b04140f090403170c0d02070326041110031103040c05031002280201140f1b03010b030a0c1b0309030c0e15060a0c050703050c150a020c0907 67
    0x6440030749813076495410310801058003e000d8070a40c0101700c039205030308203602c4082c80780e905582c40c186100c504a50b84003407910003a10482945604128803106c4081a000524102d0b01c00e45c0c5640e02640c900e88040c41c101107890801119040394024840422230303060400301c41c5501100c0543d03c42801c078001303500500340c03022001c451990100801c018084541c1945040390302c15401d45118030745404904081380300e0928581c518070300700440030041d050001d00b80c10f056800ba000018540c001c080d2240701d0300e1f0007100c4c1d00003201d9a9004000e8001000584000d040c80c0110541341107505111000100e8080105908266595141d00c0018140714554441c11003444500440002170390b4203009095406900040c0d88000c9407072000550003800b038030080d100d03100e020350b5110301a891004105590380041c03031010400000240385d101180c0140041c2c0000c40c4a503000780034120b41e5006115140660306070b2402e078101c0034094168044d4005c20950f048200450b031030304565803240000e440d08012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 334471267 1250 334470017 334470029
    0x112060909080d05011e031101030e01090606090c050705061603243201121e090b06030d02060f09030d0f05090c1203091519020601030b090304050a0e060307 69
    0x40c200c1c8601030140c0d00b401031484200c0701c0701c2401260307290301c0c6000311801040c0b81004e980b100108200042000354800c84c140d180e0514010860041e80d914650035160520b000740c9291b66190020000d418091050402c911828207209081903c0c644501380c80e0200200006003000c4085180d9071518407d03070040c2184162041030f1803814132200c800703201410481c0540c20015140540b58500b0030708a0003406100320300b000ca0040b2610440d001195880b0700c1c44850382203181c444064132030403820b0f100212049100510000303180f1b656414006602c0d08094078240c003a1f044810810001769021035682d42c0590703c0400c00e111502d4010704c882c6144605000a4801071404810a030079480c9030b001103000c0d102c51021a0803030001d8404220000043d2010b0080329842044444440d0034071091402c03034151091005401d00309619403207c40824680001c2005030003e00041c003c0111680a4a42160809000b90704003403c140200f0900c0000f0300400079656008400182503039420864003029100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 334472517 1250 334471267 334471271
    0x90c0f180f030305070b010905160302070507170c04060b03073f02070506090606010518030a020d0501020702030601120203030f0904020d0f0b01020f2109011107060c0c15020601030201120609 84
    0x642d0b4107000b0980c1e0000f402c04c4403101424400010b03284842e025076400f40038000528502d045800790203500030b5003ca002110b0318003c01c80001241903c0c038030103d10086a40000d0b04004210908000464110f6009a804010184103001700030381d000840051203ea001024401056183d02512400c0445c00700c50620385000140d00c2c09a14140e005404040e110314200c80d00c1c1e8841403001074070b07184100c8000380042c0c1c06101d14040110001d4050418a0000d17054510301440c907000f007811900401401d03a8140c2d00052010300314102001060700411100c40351102441056000030f40728400d401028444140100c0c049038665117540c1103d4208076212410054810000507002c082c1615051481c054041c64403102500400070440801c031070940d01c4901c0c0c0d440c500c2c020f2284150051040b050411a8210318411003010130414040548070ae622226400c001a2500700d000241d10342181c0d81181e0708400c52044150000707540e0381900e609083c210b264444080361100100940d50207185118 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 334473767 1250 334472517 334472519
    0x304080f1210090b010c02180a091a040309060f0f05071a0f0103020406050612180f0d05190f0c0b0402010e0a0b09030c0108040215090d061b020106090c0f180f 70
    0x42c00c81220b4500721402940c00740300560445005407102802100082d40210380200b200141138003201050364040c0c201c4e5800a40d091040d258802c80d0311011144a4804480307106000900d030b00000c010006051526100415100086008000c1507000421105019000c604002040078a1075019410904800036144520300081c105003621001c0c441640628034120000c906400d00d541142c110030b0b620305102103107032118034252003880e50080d200c01003170082d61210401030000b4003c0403940c88407540d691342c40b03900511007240c00e180414126424004c4034a8010348098001d108241003640240c8100403036940d13400141c59040384c9800a82d805403611801090303442850018000c480d40c2542260000380c6000010745941d40151000b0303521009605801040120035001010040c8000d01071603042c601503030350324040c0c1d48401e20304180810240707240080182c3c24800c2c60300401c4468000e201c0300800040c050300c400b000000984c200710100710548244080c0c01c0c01140102158030b0101d0081e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 334475017 1250 334473767 334473781
    0x415030b0909100501060e010504051302070846030b0109050301061e121106031902030109050105011e050405010509042417010504080405040506031006062f030304080f12 75
    0x200d02021010940f24644000464041d01ca10550107050704103845040c941420082000944140e1100c0001c40d5a02001b6a070300080742c0030007400052040c04a412100e4107040710002801c01920101010b09921101005085018503140040740300315080015206a440c00100d03000781503504a00c1d095800c00d0b000156591540044424017118041240070854561089a002600b5440c0150407a10010700340c401074603106c3c0c020b41d04002901911b09000400190703510a0b41c0090303100c0700c11903548500400c0a960880c0d05801c0390220b002c01c410031150201405403260145000d414104880071403240600e442c1c0b030780030150f416901d0702901c1002c03c2842c800e4240300418001c0c01c1ea5103585418030a00e150b014050355028541c4000741a0505003010144402444024002a0301d13101e1010546001c1c070080c890600030744860703500c0780c0e1860102092948240e0001083c0710034000e5100c10b02141c24008803d6135001548469901e03680c003440d0111101c2c0780150245003400d119964144070380 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 334476267 1250 334475017 334475023
    0xd020414070513140a0902160b010b03060a08010507080f06130e01050117070e071d040c020f0105060607021c0501060308130311060c0604031101020c030a02010e060603060106050415030b0909 84
    0x19002d8060030743c090f48074002400c00200843d2500c0c0c00c80c0e030045040c801031080d40c000d44002c03501c940c602010200c00361210f100800c400c2e40805800500001481080e090900c50307240603280e0040280010b04044500624070f140007030140c07101172104004190241d6030440b100c42c111082407018081c0606000c040c500803c1d01f842110801c00341c81c900071950200208540088489520108045540b101400c0c2c5003000500003200e42e0202c20040e543e5540d50f41e01c11166400101d500400284e420741c0707001c5003141ca02410386480780c0e0040c407501c00180da4013802c03080808100c01ca0304c8d0b4100c0030362902502602650b000104550390204005041c002c3c2810030a0840c0c0c01095a840405005024020305120b0707020305200d26000710000130042409040e000b51410081800107203000380d50b000d10750a580014050300d005035121105800207080030096143c100100b10f0141c60b541d403400801403c540700b0b922440b2038011000684c03004443c0268080c2c084c0200107000781112b85840d800d0702e91 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 334477517 1250 334476267 334476277
    0xf0a09090803010512070f231e01090b09100302090301090f030c0b0a09080d0504050f010c09050918071203030902030105010b0901030f050601051b0f0106030f0507080109110d0204140705 82
    0x4003a111450391740c45c82c500e0000d444011502e031700b60305118890074254612200a07046944001c0d08409048040b107545a055100403040482d8103121160503045000501c85001544130f1400480706110604441e501c004801c0d07151151400d006a0701e11164000c84d02428000d04040d1204e00701b5091b00303083c160800d58450002d84100351985d03403a0349000d00c4d90200d030303030b00d440c0035100380020302c14582422055030095070003900410455401c5a40c41c0100b50a41d00903103619000104501c00400407820641407c0350032199821202d510850340c075041c180d0b5048640300d00801c41c000c0710041420b06001c2c1d8811000710390060024030182d038590100e09901d500054800d80068500b0250901c10a52031040d603025141c142e560034900802d13000410000c04001301240090302031220100400c0e8024410b0710015072060004808100c05820850308052040c1d100314440c0e4100084000014000118603501c544102c0300c0c0e581403005800418002c100d441705070001c605900f414401d00c02d410101500d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 334478767 1250 334477517 334477519
    0x40c181203091706010303142802210d0b010c0606060c02150c0d0f02070b0d05090d0914150f0711090a11030a0e0f070314010b01050f090f0a090908030105 68
    0x400641e8a454038484200c52103d40d0085400c000c0040c00041e20038042d00740b40ca0344114071b0905128280f416007071a003d4003100241d003101c0c41110790310b0541d01440180030b0310034840ae03a140b10040c802000c0450380f08404c2e8142180b0398442d1405411303809415901c035007130f401078810450b03503880e264080c040d901c0c000000c0e40708ea9a00c4c400240034207001c40c200c81c0d01c03c2118001c0d0984500c0001c3c20303684024059000415400740c05804507a03214904043c124134106404081403905040e20224140070b5440700b1142005051401804100c645110310b014181094481144402004040c503c443c0510090004200c20005d900024407c070481c040e94800011140b80700e151704c5159402084910041c20750042150500018078441c1e17030b40d0b012050804949094800348882010001d003007102540086654001d001c1034540790b41024030504030342c2e02c42800c0c220715002e00c20002c007034a0700848202d0b038810706030f41d4080c0e800350b110603800c8802270500c80d806008401152800d12443e400074086da07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 334480017 1250 334478767 334478777
    0x902030901141e04061e090215040e0c070516080307140c240405090903130e0f15040605040c050705010e010506010e09091203070c030807090f05040c181203 69
    0x540c51100007622140d009058824881c24160000c0c242c1070f1003000300400640701c0c15525114140001c0b0000c4c0340003920040990700081194442c41007018510b0a2244288100f0060005020a90002656640104115030515194443c600d441c1d4500007104c40c0c401440f4280707200c0018904000806000c00c00c2c40703680030740750000d0044085566003e945480950200e02044002c213040b00301ea00040c4100d02c4e82c526146065290b0b800306240c0001918000c400ba800091103030788403480040803071f001c2c002c440401e800a0610752024002240047c2a400300045080f991002d03d5a03681e01c10001080301910900074420540005401c507049480c06950550801012161801c0c043c03198a1003200140c55114101986a0034802c040304004c4c1814460302c104c81101c54000800300203903110784110b544800c580315a519005169410180c0b410052001c0d0110911101e0a1643e621064400940c3c00051812110100312070b60f03852010100300040074410b001c1b031020100c2401c04540f81c06034840c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 334481267 1250 334480017 334480031
    0x20d030e041b021b060705070b0a021c090308161202030306040c030b09180f070e070e010201090b28110d06050604141905040507031d0f0304031b08070902030901 71
    0x241d202e50540c50450030016049000d1080007108480e0a0110000010b0051810300500b940c420340307446c9940d00240d928500110720b1207003869041041d10107040f1106a100000d882d2410054400b0855010041885102248c0c042105c401c080402000940046c030000c01c454620310041d48940c400e48a46024a0030a030340180094064014610300d5000906040c003986d860380040120004160721400460080907841c64042004002c0140509680c00c5042060700307141c072000c1c00340f0b00c002e045a415a4140060817020039070440c030503988050f20b41c2000040d50016010502c1d41085907040b01da0340707072402903c48801d490000c01343c41900003100041003900e894038200306071406280b0610450300b070fa01c07440c501c40341041c00805505154030030341400802d0b00c40740001c050340c60441e02c40000940e0fa014180c403d20f8074600c00229110b03079802501d6039008849088d0307160712840c0800b402c0c52100d8580404030080045408006000185c16500040d88525651000e548240d0b2030b01e80c20342c20140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 334482517 1250 334481267 334481291
    0x402120f1611250e1014120a1101110d0e090117030a030b01020106050d03030516080115031a030a0309060206010608060d12020a081812010212130f020d030e04 70
    0x2624101c07191400020031115081e01c0308000591a41000348114040900c0001000d40a02d1285406102e10117940c100b90790030b01c148600c400c01807031201e1784111001c1a0300380b100a0041100a402c0b81c1200c1040b80c5c5c00706080c0140c81000d00e03e004000a441450b11000724142d05c407421089000707007252304501590b41c0f0341c0c0c4d480301c5900207080840c040e00100f0483d8a0103001343d01641000303c041c000072507482c0c1e0301c20000f14240014482900426103560800041440300c01c00e03160303550014107000580c0e504080f5020740010148021006250b62000c0b412010302071640d0030348042c8002000c582171014985801004007030188110380242c0b080c80c0c008500d45004900701031141c400038003103126035445c0b902c8410030030110700c0802c01075014903002071011411840003050f00202603600160290b0b83d08050141c0b051180d01d500c45a030348140140f03080b441080d03008a0b0469400c2c05d2018481545040c14121903040cac000003984010800781000c20076801c5001040403c0c41242c0400001103514 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 334483767 1250 334482517 334482527
    0x90f080d110a0314030a091211010b010309031209060603080c0a200108060103110c25060c08161401050901091406090a03030c05070c0801020711220b0402120f16 71
    0x24030010041100c520070f0b102010f1010015586c408000c080104810031142c6501c0080302c2410808000076042c40400d40d002e41c1d0034020401e0306802031034100841400303614028051f10f00c0c11041d8004a0b00c80c20090140149508001c000e10340082c4110b80e504c0344480c50a42c0d90440790002c941111a041c69401d2903088044a08103401045e150421a5900c2c10011001444c1144141c08071400c180200e150070340040240415602c0440c0344134004060070520f04200c91603a60018003040511a840c00015040b070080d00d4050702018805841030f00c0d5484c20284044403141403407507940ca071004003c00200d054004040d0340d0301407001c0f403103011038142e1055150740b000c50300c042d82540800250000280309601c0040541c01c030749403150070b02200382d82d644145030040d4049001e507074000c0ba059003070001c5140c3c8002d00400480e0744407041003207401c81c4910044040c00c542d05265541911400e01c0d101d40d0112524039009004510413403504000e03400c108441950301d0030760b8184070f99105454500038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 334485017 1250 334483767 334483783
    0x90c050f0f09010e090f0c070606120b01060201050907082109090408040e1806070e150408010603050106050a180e1002030112120315030209041505010b190c030c02060a090f080d11 79
    0x20101d46c801d15030304c46c0c16001c03880d44100000c580560780d52500290b41c0810701e0741c028803103100d03028806955143c41402801e42d41d020b806e22100e60050702e01040a00d034001600284070384218600341080300c07070031076480360341c020081005e0f000030f032043c00c10081041c124010400c3d500d01d031407400c002e6210381d0100c00d28003020b072402c0b80244c0d2290b80451409806448001294880140140c040c1280d18449230200c0d0059800340449a4544805100b0000d0a000741c401910040d1903c010280ca018904d0940c1c481898410301c00994841c4104151441440f1054000c040c040c01990345c7d5030740c0c1c1d070f40040302514200c003130b1880380200a00b08080c43c807a000310390080f40f041d11003a00050440d001c0101000300500215201c3d00e4905952003101c08034042c0c580240040c01c600c0d0385800c0c00004500380c072041c0010080401c44140b40e5100000d8010000107e61601a6002c0303803204030b0100250368240e01a0482404c000355028002441c000001d140098030a02d0b0b5a54907900700c1004d1240e5071a501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 334486267 1250 334485017 334485031
    0xf01090c060804060603171c15051017130b152d0904030801060f0c021509030a200a060311090402070227250207090c050f0f09010e09 59
    0x101500410001c0e01c5103000580060056100207021a601c2c0c1d1480010310301c880302502c2c080d102080b010407005003901403100e8140c400740c0c24440c0d50000720711150b514107140915031086010040c52504e5904c110010380f451101c0141c101c2c05403c03c490380401c00c5d0001c103000c56000550b07e0020303200b51038400c40072451031005050300400300b01044006140f1840c02c4540741800140d00c5030108165692480c45008034060b880c0c0711170650404100400c0380140c00720b001d003405403080d00c0c038005855003400d180011982c01011078540040314002400d004180002401d56501d5111020000341c0e461162031107500d04903102c03000c031139403541d01b42e05440b038902c00c4c0d607103500c010f100401e01402c20381c00400c01c0d180300410703541c0075411501d40b100811200d03d401200c50314107041048007250300e02c2060b5103c0c1c944c1d00b94510180110240080d5141814002c0004107629003070310351002802401518040c507140308515485450000354200c85401c0340a0050004512218040c0c541c1011620755001d06c417 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 334487517 1250 334486267 334486283
    0x51c0203091315032a1d070206070219140a15050117070509040204021204210c020f010c081611100302071e0c030c090f15080a030e040f0c080103050f0109 68
    0x100e103840c2d5180080d1496030405840004c203c0e0a850b030f038551002000644607a03088055100c4901403006d9000c000102000155481107050080d040e40000703c0200a011009a4035030030003407440e018900c50300a02c4920040e211b2103000a04012044111880641d50300c001088142e0b81c400881840e942281110700194100200600040c00c10301021035010307001420262510303000c481050369440d001c840c29a82c50080e089080080c503e5102c40d40c04120349442d03c019078081c81e40000d00c00001c948145410700107200e45020801020700280c0741c06001c10045408401c4c0c0c9402c000d410040d46460440c0304415000340595514040d2094890080e000600e83d0300c1e4090003004850010f41c080404d42d070054945800100103040000380c1c03c041c0901510100b4008402c21115060301e90312841c4050752615083d0900c040103000803600d2106400d49460211001c0217000708000300889150315010608160022038a180c1140825040728410790888001d803900024182c201e990808006201c01c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 334488767 1250 334487517 334487519
    0x20d0f030e010209030610030323040e040f060e10141b130f15081b030601030908090618010f14030f09010e060103050c0f030a0c12051c0203091315 65
    0x9403181d070200e1070071103400700010b1078441000006032409200300d0780f070408059442014000c045e848070300b03824101a6124420610b140e07020019605003d00d0240c1d0304030b0014607000805104808801c4040640c00480400c04900907901c040d03201c21429504a02d02c9081c011901300c0d00e40e0f03070046240308100181107000040b0b0703440b185056a901c0b5482d40c0f6001c1c6100030340854003c6402c02220001d16001c002d1a50401109a004d0304054008040c000303503038800900d840d0140c03107507800c4070ba000382c09281c0081d5070f50b442d2810b0071007070140c1c020154000001040c101c1c083d40c03180d5004444082c0989407110b50402070241120340c150300d0080d10607007400c1800412221040d4180d01504903080000100d00c502e00401810b1601209a00a42d059404049100c0e042d04020b005244182e0094001d40130144040c3c440c5500300c02a441480c000c0d0035160209024072509000210841d0141c02a031880b1880544000b5966008081c9181c481c0400b103c91301c00f0f04001d8030540005103450301180100d6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 334490017 1250 334488767 334488797
    0x2012904150528152316030806010c1a0108010b030a0510150909030e01030c0203090604030b04020f03030313050c042904020c030a1e080108301c0b01020d 68
    0x208525039103000e0600307260000413a400720720a0407083e100401d83d03941c400c141c641d000401070100042041d03811241c02004450142c28044d0301156200e034040c20070500070b89990300103c5200180203c0078190461035420740300741405801401d4129000c2c54000d02c0213f050000301341e00d410b4034a01c002d01590040404d413400d050aa080b69005189150b03114071103503a078816610680e500d1407000c400003500d448120000d036030107101350000a00140f00440c14000500702040461203035001c05054180544005001c55031441c8450040101c0502580e460f41814801c486021154076422200ca002c0c02140c2501d070b04061140d40714415400c403800b000340c0c0504131007a03038041e4844d2003030303400640800c03c0e5404100100b005000c0350900d55901204a001c00000c007508581754600b5004204940d001041668000680b0004040f091001d030b403400170b40400c507d120380261032408941c0381c0010a00b440b90256900307450b1004072200760f0902c4811002001261941494003d0742c0100300303250524402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 334491267 1250 334490017 334490059
    0x3050f01181d0a05070b0f120603010b0d03020607030f090f230712050601051e13020403060c0f03140708070f1b08040515031312020129041505 63
    0x40e8007a8540c0090005000258480e02110750700100c04140d00c40310107141005402c1092500501e020544c46052410243e40c12226208040500c50090740810100b21142c0d4298440200f2440041c003020000c0100d1901944400b4226084e2002c01d00e414a1344280750b20a010700c03141c5d6035000510018690311a554550342c0c07800004091001c0f5034441590102a40412925014201e04c4108822046007440d141d4034011058001074022501070034031020747d61a1a0301d00b81002000c5582d010400405d42181c0000e000c1d544c40908031900f4506170702c03242d503040600504184a155428002288501d40601e1881403d8849800240400000900c540d00c1940c40f01c1a8642c1480c1610100441162102070518034070f2040d510b520000404004519100f00011100c00c070444c41107056242c0b00450f0307025072810240c05080c04210740f5024054510070340c004842d0180348a050032040d9401120140181c548007440c1c1d0145142030243c82410303501d02404012921300903e00e1a11709501080c4104d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 334492517 1250 334491267 334491299
    0x50304050c040f0b03010e19030f050c03030f1005030c0f060f13030501050618070207030f0221011a0301021c020c0304050a0602010213050114070212100f0204031203050f01 76
    0x6418000c0c0200600203941e035024050080201540101c4c1c0404080201801c440d0b1080c8483e20b207601a0380c545940500001c00c203131540c3d405007402c107003020200c01c041c0d8080c8101070545a040c00000300300a04c07203020b882418000e682060074080d100f500c943c00e00d03036030341d030401001c031b91040c40d20411000c1450580000c1608158039a1501d04044000396807080d1011640c0048945035121000c04c038684c02c0410424540313650140b200d440504060b407029440340345901001d0310842c8482a06800c0d51902219000e0a1940c02d0484941003280f0710300c10700810100c19508681120801c40061a02c0c6c1402503c86106031040f804402c0500002075100a5210809100d0b545c001400b00140990301d1a8403074004000940015030780302840d9803411070040c0c05030411410b20a40b1044c0007016400f0600b0b0395a45581075560006061001a240d483c0501c00804118003e0504024100b0131915401400c1282e200c0e904145403800d0320718080d401e40b05e00b141c2c03044d2444183e030010440d1103c0c0340c041034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 334493767 1250 334492517 334492523
    0x5101d060103110403080304170405060d09050307120f1107141306090c0503042603130224070b10060c0f080c030d1a040905100e120706050f0a050c0a050304 69
    0x18048a4008403c0d190750456442590181c00200820041c8408107428001902889210340d02d0681400c00084060050010154071035545003d68410400c1c10011101c0381a003100e403110620041403001003120307080204010000daa080c0358901c82d000300107048010355007083e20100c1385d0340420003480884481c109001c1c094076180d010015090b251442164080811543ca00e0780e6450103081a40010424542c0c0c500c1a600150180002650490560390840c5c1d43c04d200c04c42e400b0325800003d80390f030302030001103140040c2c50084e1203081541c540103264051003840039861641c2d030300407503007001c843c14460b581c040b442c40c41031540024140c811000384d00b4450310041d8204004004a10b2454122141c2c0b40030729603560b071040d120030342500540b0780c0c4401c04a0f400e0004a5240c3e4400f03440742e21500c0c0e070900c03c540303d85030742c0e000b00005d02040e9248038200e0803464545440e0300784180640429904440d0781021500440d00c4104a80682032003030122080c86490040522011110795200030019 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 334495017 1250 334493767 334493771
    0xf03030601030b060f040f150e03030a30020405180f0f070c05010501080c040e010504170c0a0b040501020a0314150d14060916080106030c050603070504030506040b090105101d060103 80
    0x84400c0d445c0d1101070000f4110320b00d00380111906151908500400508a11051200322004080c03990707000000c481c807441c00b0b4985000c0711100348151605ca42c0d41d46890100700c404046840c1d21507802580030380122102118039034100c03880b40c0541e494140042e41c206060a0340200010496101098200d4001c1d4240ca40515440010745a9608441c02038005507029045040c51400916190242810110003c40200080c1c101507540030742c456010b005182001101051500c0c011906100030762001d608903140c0c10207440c162402c28000d510500c1c81402003440c0503d00700650780d42000c42481154404001e144805c100c40c01c00182c031100c81022100d4030382d10b2440c0c00b003c81d1300740031507801449200b004264120b0b0681a24070315101a40020310075a140c0030f0304001203000503210700121340050711025541e4803207002c2200c481c8185d402c0a4a140700f40c0040c48204942000395510414500c8020070440d11094050450012180308408161320f048482580441d82c590b21107412070f205040c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 334496267 1250 334495017 334495027
    0x2090114011116080d03051501180915090e0a0f030503040615080309040501090b0f0616061d0f2b020703140726030a0c1a01090903110f03030601030b06 67
    0x1c2d01c2c6060701c0c02c2d1090341d41004012040002c0082007010070f0346105107003000d100500e400c0e51108001510400d409040012521910310171400040d4402e0180c0010340c400c0c42100c1c80f0320200c0c84100c0e4103119090b4036034640540540c00c80c0010980403100c0d50f01200807241110591000c0305c15800140041e43c1a0780e40d00c4200c1c0c0e840f100504154001c10801c80a9074031801e4100c104800c9410592041715101d00303081802d8200e40d6040e290408403c011110f46465030b804100e02e5929060201c00200441d1420030305504041001c40107130824a442412122401500c006c1039440c1c490702c082030001034240c00d140f1903049042e00768000550001c1e104807106165070340c803404405402541600c006401159040c0455540306800e06071400e03a00c10450300c0d1400d01c2d001642d17a41f00d545045020824606030320310820540034000d40c2e044404a20000507561260000340040102e10800c40110702001c00e600550310020850780c0035807602c040603504560f10701f00107402511480780015031164080003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 334497517 1250 334496267 334496297
    0xb120f030c1b010e0622060f0f030c0f180b0f03010f0b04030b220b16030f05040b0f09030c01020a02030405040c1b1103150406020703021239190203070902070209011401 74
    0x4071340c0103295a5480b8035088d004114050a401e00f04903d84040605042c10740b4800303500a9100c005030007003441d04802100d003080452000301d48a8214003080e01d0002084052a290366000e54145c883c11401403081c0d940d24850450348ac0b25601c030091801c190140003030402d549440c0c5058501201c00b03102029500c1942d21080b08860880c0d11080075075801141d50500350b07051041201120300707140c0800690030305032513035241030000800710f0a0302a038150001e04c0c0801c6c02c0c130982c8c1ca06d02451009545400081c1070194032604280601c070300913407420700c0c20340341e052103004506042207c40001001d05000c50f11140e1420f80c01c1513070681c16101d00c908085070302140c0703416188540e00a020044c0c40b89a140b4000f41030060908415075460000c2c400c500d10405400003c3c0d280007022031032900241a0940c00d00350010a06d40820143d000d1000c0208103510300e1400a0300c484d1003202554496511032458008070300032030101075040030790640140810000c040307444420200504000c4107085000c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 334498767 1250 334497517 334497577
    0x140a0e0a050a1d01090c090e06040803090f0d0c020306070305070507030f05040f0308070501050109050108060c0a1701030302210a050a08150405090d030e03070b06040b120f030c1b010e06 82
    0x10890b410f0740e558601501c240865107042074051b000d0108103100300e0340704001d450355412003d071018104290000100b181c0420030403810900840d0b05060305d40341502d02e4030281c0b01120f011030980c003a0044900151245100e4070030240708e0b01260b1202e07800d158040d2070890350107414055410070321000b007102080414202c000c49004501c030b591941d68a008510304142900d10603400120700c20304140040c40103200c007251352580031040009503600c51440d500f040302e02e84030015400c03000040910011084c941d0100b0f18201c83ca41c072280482540840749404411446844032113000203c060054014880c03080300083d400c1021045045901c00c0300c040081c04548007501c100d2419485640c10071032281e018011950b8041c030320005981000d40c5505c50121070403008100724401e03035507004885025a2030102140c1040780f040c0c00c5400a50300200b000b6541e6004402440c62403180b440c032072101d654410400c0c0f02007039060b541c0441140c01002030007107a401406c400002c4034900b2102c1e452060010f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 334500017 1250 334498767 334498811
    0x70e180a061a090102070506070804030b180606120304090e070504110903060906010303140702060d1409120f070305090307120c060e0d0b16020a0507030c140a0e0a050a 74
    0x80c0c64001581d5181514412007820905404a000c0e603007403000105583c0c010581c5402c480c0c00351201d0340d07901d055140100d058801c54000900031485a414006006490b039070704402060400c0c02c44a032a01c500d41041403c0e074809403902a83d80c0104070034003400c40c16170801050b00a0301c40486a00c6034a0390000b4042c0c40104510a410101c0400c0c40c55061500b08000c0e50400e0882d03010b492554110344008007144201005150713003881c005424811500ea5004903540007080d40300402c80014180030340e20075240181e49100320340c842c44400840c0103003020101d500b20488a08007900d02000c680d07080c2c4158000b511216450301074070b840065500983d0041003501807003403201903170b003a0404c030003c2c140c01000b0034018000d1156455080005d444850b1103034108030841d070410400071241d64100d1919000e040004c0441c01100320010130403410440c01d10075250f25241005030b2054480520610310010322907982603600040c0032500c0300010394081a001032480401160391262542810185071403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 334501267 1250 334500017 334500031
    0x509060901110c07050607080f032509080a022808070905070e010c0303240e011a070309092316020606040b10050d0209041b021212070e18 61
    0x1200040090500081c4148001d090a0081c0503081c50480700603103030386903140c0c0a0180108800501c100910038070324140c0b003160b20410700f510b41d01d24055011024021040c141e41c03c10b4020740f1030300d07481c5a0180300401d0a403154400240804005902002618680310a14061284140d080000001130b04001c05000c0e08080f030023811214580381c03010045a80007000c4108000c0301c003403025640e03030340300280111998140c50042180d440c0f0711285d0b259940850721009007440f905500040b0302e104d41030941e041b502c803080d08543c41d801c6043c3c07284a42c0b03e0002c0003000281140801d00071011681c1c4a0610111450701c40d0181d6200c1b0070503c03c01080c29208007462a2100d480c07140000e904010f1503034089019142806004800b07404188015075007290740040c0000421601051513140d070503640b443c0001032042c003503242102c40d1304501d0013065940b6001406411008215044214102c510742ca0840c0624032203561a61011148280140302d410390200b1081800f00e04400341120741405200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 334502517 1250 334501267 334501273
    0x81c110c04110705010501270b0d0803040501110412060e12040b0a050d0f02120702070b0d0c02030d0903091505070506060103090524090d02071505070f050d02030304060f0e07090b0409060509 84
    0x85080301e1006400b50f60782300c042c0c10b0602649a2071030702c0f849440660f496000d94040d0701ca0300c4924160703015006080808044810100f00000d140005400b04e0019070300442041040d000c105000a40340c06400704c1e402410344c0100820041550410f0041042da000b1b80361080c00c041c0d9009180c0156410805100c03070706034020449600304424030b6421500103010340020000c0900d81180c0030340d01d006031201583c4480d030300d032500c03030b20140203104403168030583d81e5041003481c03000c1c500501008400e002e06d200655254100c141d505002d481100c04540d0410003c0481d551800011005040040c00071200760050b04003688418410504200d550b0840a4880c041c51600004d007600c0c0007000c0203000d045510415041088002d81d040d00c4000a405d4500035030784189504080c440604d090400908501c80c42c001c18001c1540030000d0341c022807183c0000d010480c9034031a100159094100344140a400c82d4000300885a41a0b000d0f04039030101400c0400c0080d82a11100704488c011600c07842d240d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 334503767 1250 334502517 334502549
    0xf160c03020406060e090c0a0903020a090507090602030a090315060504021303050c040209010903111915080106110c010f2003090405130f1e0804081c110c04110705010501 75
    0x8a000d015001c06014645048505c003c245e00c0010f101c104003074054003d00c82d0008003405c2a91244840d4809160041c11040140303036038001c544020101102c40c400021481003010401318404230840d541c500ba80c0d6600c21800d402d41d01c80c0c1c480c602c20804c45699540d5101800551a10380c2c0c000b07000103110304400e80c9031051450402504122079121540c1c440ca02c10400c1c1482603800800c0881601c2d000440d440c100184070000c980c0c00e65041080c07a0141d140040002810380107240c0d000703e151070683e01d118603666281c1c8113580740d40d056801013120380c000e03519210055200d80030804002c41d075490841c804240403141c40d510050a04002c1046410001c0d8800c05810030303004031a00402c84010303032401901103454012a11aa80d10010480000395800702c0c3d22030b04a01d031200e00c1c030760401e920707039a035039600c46140d599400c82c0c00a0144442e1090311845110b03000c0c01c1981144140b020207040044198010080100244011007030754030001c1c860b04001c035400340b0a40f4040c101d190702ca00c04c04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 334505017 1250 334503767 334503769
    0x27080310350105070504091107050f030c01060f0e01061110060f0e0606030105100c0312050a06061707050a030c020114090607110d0c0b0c0c0d02060a060602010e0303010b0f160c0302 80
    0x540c001d88a01d2105a06200038000e000307500c0411241111003081d00065420208610302e203a0f0f2240000c0038090b4400c2501e194808200400280801c0514000810031f40703030b54180310f40704c0486504c00c941c03010280000411455006410080d002080107003038602c1c0d1301d1426520811901540c0000c10300c0f04401e5814811401c804002c107400c44804c50380a421076251400044030820221381da0780800c101468000b041502500c004c01c81d02130b00310014003203890011181c500402143c4a410b00050180d00c260000b10301060805000d00110340e02e4602d4807002000c11740103404040c0d0030f80115981c3e807440400d2040309010041c0541414000b400a6080c10382000380848042c0420030305a41102034417001250b040326000c140e05900141761410350741d485101c6900b6001e1061041c54a0190304c1c141c60510340d010400520a84010f5410040c01d03480e0b030000c0b4201c8210403d02512a8400c0005021025008002c0c162100e1000c100700d2400d0320000c007a40c42c4000e1240102ca02d2403c204c414411 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 334506267 1250 334505017 334505099
    0x6050709050105040f030f0515040605041101050a02070512070e09070608100b0316121b1b02010e0904020a0b1b0d030e030a080405070812090427080310 67
    0x148070034604141403a04012404220107151303c03005010752000d00c500001c12109028a100450790200290400e00d041d0501d10044c002c01c40d4101c480c812412010007003503000b80700781c4100d00060381c0208441800c21052000032406814002c0303241c4980c020018240a5a060030307840f03181c24070b014140c25494030302c0c0a488888050440540c801110740c090203449012000e0341d0f84150b2500d5100e0b80c51050041c241c4100b20042013120581d4185401c100021118100c4c086006045682e003083c28020502444141da5115078000e0020704101240e06007880c2c4034216a401a0005103403440742d691300d00b0554003561001c4035111002041141528030384c0310521100c25040c02500301030140081d004407040d101e01c40c4000a2041c0100d171004242440b108001080191400003f110303124220b131040c4aa450300a2030000e40309a0408441d1034023072046903802080c21000505218081034103aa031401560002011101140c21109000400d40201c014460144c03c08010740030841508070804a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 334507517 1250 334506267 334506269
    0x70302251b0b030a0236010e010503060310020304050c09041a0105062a010b0418060506030a050c130b150403050124060c0f080414180105010e01030203150d06050709 73
    0x1c200380003008200b044407050002c42e640034865000059441c010742c00b00260000d106110848a03804441c0328440b01d03c00c0c400c0c0c540780340d4426214000441155401101c040c0320813213560341c00da008602021540040740d0040c1d0f4001d0321401c01c0d2041c40c0710640101e100000100d50540f44031400c0851901408450000f9601404086d6100303450501c5600211a0145080001a66411800c24055110002988aa03500c1d86000340240074481d00e0001040710402c1081c0c0076141c07a841c00000c9410ba00d80095041c10b160f5000300600080c072509070401150240c0403106106841e1039681011340d0f039840204800e0030060120284d42c80c1c5042d4140203084800c820340f0681c00d81e0398000004a1000c0c08889841141d00a140c204d1400c1624541354012510401d40144882d00100300462541f91043c2c80c000c15442c15111120011884001c00c01e9000081c829103010a04011000001e54401d03002582e1200e030054440a41034114400700e580d8030110a07041e225a81e80f01c060000070340d800349080c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 334508767 1250 334507517 334507553
    0x1812140a0206070f0c0204050a020a1107050a12080c0f07031505040b190e0f0708010c0f0c1704030807150e070e0a02070501060e180d1d040507030225 66
    0x900344028098082c0d954400600840c0074420031070049241c0c01e10031815001c40b580d0143c070602103402c0c01c03103200c0041d401414030b08011564501032848210740c0000c6a5003141d030020400ca8181d8904812101e0044801409448000c3e0400091030350079410000340310b42c00c1d1000c0043c9900b81c03845c02c1c981840b0040200250800b801c103010300c001300f0b58801300141c000440e41c0f0b0310798945843c58565001007440340c2040696009109800c4541140840d5901c11140203074001d00c9250880282182d5000580000070040b07010a107820000c600c000d82640700b00024035019a02d00b039241d84038280c50380c0142ca411170b42c1130542904426010020f0249855002411008010450901d10707c038608107801006040c1190b800b0518a0a00800b500b00c0001000082001d40b03050030b05441d19207400002441c00d0015200e143c14034003000344070324440c5000c04500c10745029006142d408001c09004090403000400da000d002003410540d4000c40706270040914008225007100030b2504512050b201c0d1404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 334510017 1250 334508767 334508807
    0xf0105010b07081206010e0301090f110102030304031d010203091c1703090c04050907151e050406050304030e01140307050c061b090111010e162102030309131812 71
    0x10b180028081d20546948500c030b48020740041d640d900c0100c07070115580c001c1e17581c55800d040d054424800801c44149103d070090b60385900600c1020010399032032009540003000150f103000302e440c0f04848194100c0581d82c0500c140c13880e12844c0e400051200070341070380507402200c81d08100003c112080d4a14070600000c007801e0350961400c000919250303114410100d0003951a040050560300081c8030203c0600480c0100304002c19401d0320040070f421500d2071800121111070300600341140240e00355002c640e09a6110380c6140d603140d6040720f00300e14a250740b42c1442103481d41c0c5052602d03c82c010314422882640c030a9242d942800071b5526001c0040c0c0f81c0a10124501030710300181440800303d901600080c282041000300382c0d40150300520541c82e941c4042d000318000300300021400e120205c100c0d000c098019071401d400c00c0890b005080007280095256104100e108034900380f01c014800009200000061203085041d501300001e11000800c4031880d42003000440b620b0303000440c980d55042d1005903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 334511267 1250 334510017 334510027
    0x2713020a180803160f0803040620040e181006080c040b040608060c070c0e0405010c030b0f2808010f0603050d020a1709041e0605090c1303230f0f0105010b 68
    0xb1651680320f14011001848415078051042c00a003003206150183d10801c00d50b56840c0c103003070080c01084002c0f0079280c000140040d40b0366085460081d40c0a54940000c20001c070345441154421040308030300d60b184140602c00100c0c04a00280c0300da140200400c20103411810021401c00c411940303840b071074910803850950244150000002d049510400480d901c0d40c0d12456414007030041c89440d880001e803a02100108400c100c4190048000d01e00ca030b0310144040d5070124200500720306d946072000d8000200616070800358801e9842500d48541000c1590505a01c4d80b84140c00c1d40c800351200c02919880390350400400c4020005030404552602c054100381145a0354440b42c100d10848040452002044042950340c1e1f03030303000011030b00a07240e4401180c8004134001002e04510700c1179510990181c1c000030b81c902c9191084444440405050b400554210340d5500c20044e900e2466410340816800784221226042101d103000181c6c40000340000d0301e1075030720542504c1058208007207801003440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 334512517 1250 334511267 334511279
    0x907050f0f0708090619030f09051b0a050a1d0901050f0411010909050103030e0a06021c081f0803041505040501143601030605152713020a18 62
    0x140c500440001c61869651601d42c107050035240103981060307502810000340e0342c1d001041901d05890360b40258506100007003107a5111021120315020117000d5400c040c0216015100f04007a0403040e0b1001800e12440c00d85a1010411010139900600b101640c0381c10202c401d030603600502540564900d000740002d02c0c0a06d410701040e800a0001481c101c0859214001c5a00660042000e440d4007030301000550b0352401d005100b15120b0200c07a020700303001e64020031303481d01c08900f50020300000031001c9224003c02c10101c84001000300205c01d0032850702542c4c4840d00a1882c8113000f07091200045440301e04010310844c40100310814801030041c100810822660010038010007220f80d2103407581c0f1002c40c00c4000358625071401c1440c0520440c183c00c6042440e9440000c180c1c00000c0c2d07010841d6984400a104e1100c41c0d400c41c14010000c10310042940c240b103101c0c02805944094109c420b0030300c41002240c5030070009080c100d00c0a80110340c4411103a07000aa900141c2000714449004d1031410b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 334513767 1250 334512517 334512547
    0x1050c031506031e0a06091b300e06160809152203050a0212180402090d1b051f09091104030512090a0509010e0a02070f080d0b090705 59
    0x1014028600440018184e0450038204081c060300c94148140904d0019004c4001708414000c1c031102901d8000314030702240e002c141d81e2003c0c03a05502c0d046104400005a4074464660086200c0f81c04088410340302580c10700d014080c900480d21005040904186a61805c0c074450700300800f007084181c0f8100049424001545070140c1540d4010b4007003500d400100080c0c11105001c1d403450000c4021420081603402801498268005c0e801d40701c545021941d0440d041c85041c4a0842e12403030903400060070f18180c1e0007482c010300300401c5d42003211100d5851070302d11442c5088543c0b030082906010131132414140c0c2080c101320300f822244100096503250240c0100d00310f0260100c440e03507a82d251086084400d045a0146800c84200c80c4e942c118084c080c241c030360020b00010300031800100c00042c0c5042072071449060f9540910a801107540d40808840290080d100941d030028220071a0008202140000d00e0b00c0b18040002055503260a07007800040710000c1c01400c00c1080821081c5541e800b40c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 334515017 1250 334513767 334513801
    0x3050c18042c0703230307021302070b04030801031b030b0403030504050c12030408150601021504020a0e090607091a04061407020604230a12030e1203160501050c03 72
    0x21900001c0a038085502d040885401804031001c5041c5446000c410701400180340707084034400c0c500c48019106124042002078002d2007075a00560041c0005d40051034400c0751880c0308110070400504000040c0c0b108440c0303490688080d0003040c5000014001d004031015010781c2c5140303003110003d01d24550fa50700321f2810300c0100b01404042e6220007050820005010705142c80200619050300c21030b445400c2c9490740c1c400c1c8100d0f1502e107c0c3d14024505000400340840c41000d05030040c118841041101d5200c1000c01801280d10207003050009c86c080b001400712074000d0124800500d0b280c640444082e01e80d04150b0042c403802200441c0100d560402c02d81210103480c007515102e01100500400b04410f4050001c000b54800e40100740032542c600c4900142c22020911000000d424900106000800d4210301942211900c18580480864001e24510201060140078a110020075120403811a0004503c055078013000e071500c802400800d001d85900b25442a401501d1030912003941c0b415030f04030b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 334516267 1250 334515017 334515019
    0xf0403050c010b040c0509030705040c020c010f03110a03060503060a0504110609010c050f0c030d11101d011407180b0a0309080c01020408071d07021b030c0613050103050c18 76
    0x81219400800790016000b020011308144800800403a014005801000c0c2150181c0310707600300042d042c40c0a014040b036144450700a00200c081c4440111510a03090769100185900c504102d445a07281d00300622910f050356038006400c9080034100b50070041c000d84541001402c0c0414400482c600c03075440401d02104442c2640d50307041800040e1555424914040c0c160700880200c08100d81e4007190074100c0a10840640c1d4400c020018140c034443c0b03a02d9401d00c16984031a403465015403d1383e020790750f5144c100c43c0c46203d001001028909682041075541c4506481c2d606100300103030804003c2080c0100b08008100c0c00341040c030150140d01824601504164803807590320244001c800842d51b150146600030b41d80e07581c880c1003050791240c4038415981c00300d1407094a1b4540c0b54903d04128016012a406401c09517880c0380c02640c030600280d0b00540c0360081c45c0214896070b456000600301c00e0704801d0408142c0d8a410005012504014800740c4600710806c000e1621444001c205050154 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 334517517 1250 334516267 334516277
    0x17150109151403040605160215161103071a100b090f2b02031c05030a0915060f08010f0606020d0507060605040203040b04021002010606020d0e120601060f0e0301050f0403 75
    0x415800300d80d0942c04526524803010004248014001c141d00218442c0c00780409144c17488801c0030301203a0702c0341c46480c101d204032859004500711001d045d4548100310703a50302e0001003841900c001d040c02c50340070703642c00c954800841106401541c00c00384c0341680710805141216031145000200c0307100e031117400206407140401c0b00c2c3c40c4403170b60399001801041e0251001c528034076039501c1404600401143e60140c1c480e210b800c2c40110202036000107221a1405640c5860542c2c41c0c16032a0005007200c07205c100c90380920600041c058240d1489900700402d20891b1000d070143c80c0c07041381400c44901e04480c2a010b0f06001061006980000d6001090400352600550390782d520305141000f07040542050764018000014401441030710070005001354022201102c07811740340c40082e42202c129100320340141c0c000d20a400c42290007071110401c1624043e00150504160f07441c03450409101360054004160168480c0c5103880e801100400c0d1140103400803c51400c1441d214140c0c0040100001c04100d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 334518767 1250 334517517 334517549
    0x15110703080901060e0c04091802060d020c07080607030f0e0a02010c120912060504030e091b180406060c0b092e0207020a090f140402090601030902030a0b040317150109 74
    0x80c1007584454010140381d0b218030a241000840c6c40d0a6601c1441401710540c04c0803003203a00700f00751608980c03005600401c580d2400305c3c894246000f079000b503441082c0398000d000f000900d414007801990f105135035581e03001030010511003d0400f140c3c40000e26026640c8070070094001170342c1044030079185075002002c9103200c0700c003d202262440155004450440c000101c00800c10140d030300084d024a00c41d0711040a444180002e0244003001100c40c0384030ba41100c0d158100d01d1440100401c06403004400341c1003900c050001007000e803006503001400055100d0406001e010442102607000201e00019091525107005e449902c0c2c02d0843c03108410419102c20112011a184d049440c030a80c040c025101c180c0d914040440104900399012400c141072095400e580c500c0070400034442c9900a000406540350400118010a801f05007240c051041012a40100e8900c821141c030980c0320303580b19440a804600741e0111540c01904132451040c5020084105070b03000340d1030009541e9052030301b001039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 334520017 1250 334518767 334518781
    0x20c011a0d021c050a03090e07021f0b061308060901051b120712140907080703020603042a080c0f040203040201020c191a0702040c080402011b1a0708041511070308 72
    0x90280c1c410000c04c240b04000c0340004158000407a20100e81c0e80c1010f10003d0340e1007000903a260413250503030340c80030f0f1244000e03030720302e095180c2c400c0c0b0384144040c00e0700c1e050600b6a409000702c02d98940042466034400070400a540c03000b402001e520000f0740b109a06548510942c80c1003d001c0d00081510a42090380014001132103003c0c001c2e1010741c0980180401004079000d0b8519400554000c080303409040004117101b9000100c01c811030754080c3c541440c6682c7c5460f80b41d080807010407005110454480e01c1648440d28803007203005013600d48040d0118491104c104408541341050082c0a280107104000150383c020444414803041034480b0710580d507540d00c1034030300384646411001c803449500d03140b41206a501c002914050b4825182000041c1c41d001c03095a4a070f0040b0740003400034006064170549980010000b1110724800d0744103e1048000380c40241d52980d04450110014206004000030f000800328909a40b122112013000110800c0c0507a030b503103105070304c409000c1c01741d50804151a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 334521267 1250 334520017 334520059
    0x30309150319090b04020102121e0d02040909050d0305070c0c03020906150415091212050a0c0804090203060405160504060c020105190905120106050121021c020c011a0d02 75
    0xc0703105108080010300c105140240600d80d00340c5c1c09900611802c071140b0300e4403070100115020b01c0a0003a20029070a054051a0010340c0702d079003aa640a9001d200000e2040c070203006250060713101c0d50242c590160240e1000b000c442c0000e00190070040c1d400c0764500803803080794481043c0c030340503215100b803941d8010224942d881c2c40c0c4a100d00129001500040700c1265403540c12011000c0e9036420081c40d41c0740110100d80b02d040c03a01829850b174024800c101c1034003810080034100020301f0104c00c10740b0711f81c84d41440f541150744800032541d00001000752914151252560000c0304600741004111202c2d070060140c0654010031040c44500380b1280290f80c080c005542a030003019142010355081c940009180403102d102c4c0380c0c000c4034900e1501c4c000c44e00600505d8143d4806a482c903030602c01302840c03600c1010070081041402a820461002c13096210386210a40c0b03144000c01695850382a002542110440480c80c500044103824040e180e0f900d6038000800c090301281c0d4944075400220071074003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 334522517 1250 334521267 334521301
    0x10c12091a0c12100914060f0d0c0306020403260a02072303160801110313030e0d060e01050712060509010b1b060412090f0501050d09030302040819060b0303091503 72
    0x80002e4000013081602c10f1300b61200d1013070392009801032280445180b0b01310700d811420b0360038540c4201c40204c0c4a50a003042000342c014039000c0c10602e010280e41385c4850003280d00c90b0300259505e01c0d03081041c45241e045015050000d0200c0c034581031404441042c000d407a00514000c000003076010844807013501085071400c1038030b00c40041c00e603042142d070180d203180328403001c5c400c403c078550800741c1100000c403591081c0e030322450b03c08291050030782556401b140c01c41c0001522503171001c0c0075503982010520038810b107002c0110110000940e4241510043c101741c0116200540040c28103a040c0115294008000c0c1101c00d10f5000d1074075034607405d60111100f50000d1503c0c3ca248124004c00081c04a462941007501c0a80d40340c92a500391100c0c0003048441c103e0180f28042201007105880540096100300d102c2e070b000340380c014102a16805882e040c542041007218541940024590034003002d44500cc2008ca81140194074041c00d030800714007015044120341542d90404000900e00383c50f500c010711 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 334523767 1250 334522517 334522537
    0x14040818040b060c030d0b04090803160201020d23062413030615140402040f1809202b02010f0c080a120b0d1e17030108010c12091a0c 59
    0x6841d001300c3d1007480e9881d0808910351803e5810003110242c103050a01c1502ca642e034019100d00d03c0c541d544800040740600000004003190760811140b0300011041c881c1031190085c0b201d0ba00d00c40000c2e16100c0001000280410740b24102007021204820007a01c0e280c0b1142128240c10758176091541c8001d0080003080d40090841418404103c0010100c0c501c10b06c01c1d600c00d06400e8825240c60310030300c000c07400707076029440443c03443c00d0080c010a20506080c070410f085099001c2400c0b400b6a40d070450100035045814040c0e0301c0040030142624181005683c230301c007100c4061400d8882c8800c11100122140c2019060000714030610032003034801c06000306199005401c2940d100d840c041c006002d0340d21506841d400d02c2c88e047d4407201038030b044518128900e400030369121610071000c21081400020030002c03a40c4000d4608008a410b40410145000b80030700d00000442220003c00503140b90740c08024815110f10707010342a00021540404820aa0160703400345406545286400400d0703c51a103800c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 334525017 1250 334523767 334523779
    0x4030b07090501120c020a0803060d0c1818051203040302030f0307050d1d060a050910090f1109040f03050a0e0622060201090c0e04032006060414040818040b 69
    0x118241c12071071210445800b1390764080303000d09200c412002c543c0c01c11000c0c00181c10001a00d0003154460002d1a08071000925030490790340681d030b076206a2412940100714a42c0381001d101c004001500c03a50480300040b00b140c0c0c000302e9643e9a180d031100745190000b00c202d01c0100204080c5403081040c1c40f400100840d5183c0d4032b0506a202900340c3d000360302c184074000e08226041c181c55000d942a40c2c2242101d000a0075a40c0340d8030454030180c035004081241610a012a49940054600400c00607900030000940170f05820f0802d0510854009a001d009400410501000074010006040242e4140c50241e440c0c41100000320360380003200041c140d21002c00301d0003080e928990407214441c0645a0395021000e0742d5800203a00783d032180c1201030050203080d0020040e400c0c49a417030715402072091a261505c035040349000e2607000d01a45460456134410001c0100e1030810340300c0c440d03954280c0214a40f96140030350f5250154850345036461402031600100c04840d489030340011548040003051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 334526267 1250 334525017 334525021
    0x9020f100509120601080c040e0303160210060303120b030303040503180102010609060e061002010c09030807020a030b070513350c060f0a02070f15050a09030f08090414071b020604030b 81
    0x5203613503030b80b400c3c0121005400390071046141450503200c2c2c800065042c6016600b140d4443c901800410b0040c0f450405600810745040d200325106c1c440c1c0c80145100740c480b0848001810454812070b5901906070380243d10410034040491000402d1701c050000782800c5240e16540c0200407805415154401c130701c4c090401d0001300303d418055028610810050b69145211008084120300381c808400303001000c01c132456420310210340d5080041603928005480707a51515901d0b40c3c1d1400260301100c0c000000792000c1507030919450800b04030300043c0040d20520004207850004040454412011065421201c620441d8020814040038034280d01c01000203890399198200c010103648580800801401180360200e00a115200c80318145c4041000003103000c40141002d903131540c080300e0b01340207004100c04d0000000f00b0b00b1006030f54680c801c4140d5030301e0b42024010b2005840075110101c010381a00740401c0207196108440211000c140b40c02d1400c03a100320300100e0907034800c540000d8204221041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 334527517 1250 334526267 334526299
    0x160602013225050c0c0d0b010612021e03010602161512201c05040c060c0813081507051606020a090302090f100f0f060e04110c0105060901050409020f100509 69
    0x1c09840d40008440603101242200400c115050041c86c0d8020006450400184152840362460305400008003d0041c83c08404ea0440d1141d8119580d810f482d4841c0003005003d001e50520500390408000302015482d82d00307020f68403010400c10411340d800c0210b5a822016140080e40040d000305009601c0621a0030841d8000400c640c09107040080c000f906500000c210120303441001c0c41140c200c5907141942e410850219000c4036456001d0b120310400740510b02540010015010040076800c006101c00c203180250a0701d03c010080c0071205000e82840800d8800c0240082181241e51150700141c0e1100d0000d0b0a8070b0280c41074002035000102c42c01040090051510594040d44849401440b155590054114556030500410b03604031140d5604010940c020010400761300b10060020551704100b038641d41c1e05801070f120054084e91201c0a000583c180385c112240581400d540a2058595540110f120803001d42003040c0150034880361901c40d2442017042d1640c1650042811001d03601c603007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 334528767 1250 334527517 334527527
    0x1d04060906090309061808070e060607020306071715131e0f0506031506030d050901140706090c150c022b0c0e0906191d160602013225 59
    0x8011750780860555800d2400781400c400680c1c1c00ca94514000303001007030510b480c0074040c91010b052150490400c2c8004801030740c0a00c4018401d42c0d131075407000c0306921011205a03a0031009049000e50f0400488228029164050707092248038007188d010427045078420402000e550364217000b164461a000c40c0250700d1115401480c09050218100da44a203031210030f41d50f04600c20f0b40d10703135410381c0400041094940a0005800c0519050420300410301c503048160703540790320400f401c8038050b81c0e0b80c00060800040d00c809101800034015180c0700304141680162194038040c1003c0c1c851103a0481210309070514100701e11381541c8001c40203103008030f00e20300040c070060180101c50b00314485100140b1003071000504148600442d1404114283c040165140100107513240a03142003a03207644030701002020065a0f42e840c0100c100f52064500c1c0140007802c41d007040084e460b4810700710030104242d404004120000f0031290360003404941b01d01c0141005908441441d00d00c5a40e103112818071316400c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 334530017 1250 334528767 334528769
    0x100f0207050c0603010609030209150603040b07031a01021f020d02040f030c0815040b060612040804060e01110601210611040303080a050613050606120f1f1d04060906090309 76
    0x38000302d524840c115000c21556000034040e4000040c031509040000d4a4521456a0000b20b010f4607142c031550b10ba4040780442d4001c4506403080100303a03040c0001d855041c8140000050300c801ca2807808041140000c0d16000e00d084414009200b01b0181e0080c1c0c0500e60413103480e2006039400b1503070f8991343c030a104101011840160342d01416040c00103124238012503c4030301d2200c1c1c40c19810140c0d955640d5810096030180550fa0801428011790580b481d19800140c0a1409000143e403920b103401e034018074040c203401d281810041e11486c11450b60a0006542d8151824060050200c1443c0440700c0d1f0f42e0b10070084082e00140c1405545a0f460500000038000d680c000c0d40c0d0f84d0340b6a40e620100c2c4e41910410344803580c00402c02440c250b61002c2c039602054221500030011032429100c1110741c0309203541070314a00d0b1503041c40018000003980c1418508070b68480001c81100f8680760100800e95144560064a03e008422001074204030242e8050710860364800d000f00a01c1c00f06040040442d441 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 334531267 1250 334530017 334530023
    0x6060c191211030a02101109090a060503010b040b0904060e011e0f0b0607110405101205061603050c16050705040507031e0b030a080f0f0c060703050c04141002100f0207 74
    0x461182c90808030000310883d984d89070b090300181a195010170180c0c00603d070040f83d10503004011b001180142c1c0da244411802494050380102c2c0b45800d0104250840f0442010b440c0310b20700d480001a11501d5a079001a031098200100003000507460f000039026143d04a440803424042c1c2812080c00301e426030001041114600080142c00040810700c90580b040e080050006034600b40081c6079032400350004c990011103c0d280303e11b55030380c032a85000c2003441c0010884054022900b044415a4514003858801420349028441d030704199452400900c140c40c07009083c902038030741020912004005960003004090000c020601d003c400041c01000108032429a8803808541480001420300034080030358001405407000c450b1b0756032444a254014000e0114004040c007044482c545130402420154441d940079000c6440d0086000b030858900400919800400307100904c000500d24508007480303802501d182ca1051050607041e403410011044484000e4100240c0a81c24485034025000c1148 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 334532374 1107 334531267 334531277
    0x18180f19060810050630070b07030c0212060907060e0a0801020f3a0506190807050102070609150f0507050d02010c0e0904020906060c1912 61
    0xa0345035108105035040442c11030020f19650140c1c0e81e0205044a074801d19501c1c01007802d8040c01806604650040300c01d05c007580040303080241700301134400031036140e8480703034589002020040801800ca00451101c0a02c80c84200c000030b6107401043d039180507041030707030a02204642062201d030049601c8020f04400207601002813009090340701244c160165a04030508806190030160507100a40c200c0d14a00b0b00808104c90403444c1a102c180c480c04039981d1a50400100c450101a00408100f0f40e0300c08001130004000410340c0c00c41d0170a8090302e0342540c0e28641602d00c9400b0748a410071640c0b6030200300d21024440c0d1600c07a17034400c0030b04080d42448596160545481540e540700000343c1e54a000c0360a56a0701300300b221014103800c90b050000b0745001d6001c2400740e0f01c040c041500840011501c04001001406030a0140340d48030300c803901d1516070b0b0825080c01d0422002c0d0340c0c0451 = true := by decide +kernel

theorem cover : BRFrame.Cov 334352517 334532374 := by
  have h0 := BRFrame.cov_init 334352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 334352517 ≤ n) (h2 : n < 334532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
