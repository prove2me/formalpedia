-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4432
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:35:41.053462+00:00
-- url     : https://prove2.me/submissions/2d5e1f0c-cf08-4d62-95bc-d0920660ff5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 796942446 ≤ n < 797122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 796943696 1250 796942446 796942463
    0x504060908031e03090c090108010b040f1407080c040f0f140a0f0b090105040819050d0f1d0111100c0e0a0b0f0319090602030a05090f0a2901080703 65
    0x41031416001084400c454008051110f181d464062504200c0c3c0010b014907465010f08010642d85940c0c0d40c8030140a8018800001204c995120400044a81c0301105207545414a001140b0308200080c0315a4002520b00709060b080c0d5541015082c1442213070400c2c0052140f0318804102544031004403010b0310a00410412005840c0702040b40d604030a224540b40c0842500080c0040f080300000b40034480c0040c1070083c2002e455440f140e08202e03600040340e59407040700300c3c0d0350240103080020703101500d2903007001c40c0780030b000d008010000301e0403400c0203d540e1142501014a6440350700c2c0002e4110b2004262080701428040c031902170240310415000040700c03000240020b2a080040340121035902170001e2a00642a420b8001600b00030030700885c100c210302400b1094070341d501480b8110380c4615001a82e91406000c030b44201d80307024190300b034640d00c215500003080500080c4e002016800c0003e010201e00603040c59840106400c040350b51a9001c031000140211001569000392031081255 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 796944946 1250 796943696 796943699
    0x4080a0f170c0a050d09050105040501150815190518160b090907020c1302071e03020307021519090f0605030c030403110c0402030c03060a0b09101206030c0605040609 73
    0x4440c184502054101c40d01c107410003040034640d0308001040010b42030700304a810302504059400440310303e0303201503c2c10b9441d0001c1104010342032142c0f045c45400c0d080400156410700c400c450365054148148820b1074400301c00314082ea07020f40c0c000390350401da428040c0868030300b1001e6943c0807040d04080150602c502e000c8403c00c4920443c1c2c880030389100c510b0300c9081c0a207000411254910140c80303801503003e4040180f41d180c48001e40184c0c10100080c015030b82e48151b00d48540d03520034070101c1c81200404001000002903000c0112048150116002601c40c00e83d0240e1401074850008084512801441b0000d48103400c04030b428121030f0441c684203130640c4d6511064480d84012100c40b08190001c00014002074000c0c0c1400030b144980740200e4081521500102e012640180d40740000c40b4004000c1002c1c2d850300851050240100d01806030419a007400070070016002c0e0f08200090041d500a46200c0700b8040d8050002160440500b03405955900310180150780f0a009010005140000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 796946196 1250 796944946 796944977
    0x4032a02181504180609031106220206030a0b04020d0c02011107030c080d0213143f10050a0212100b03040f03180906180b0904020d031704080a 63
    0x74614400d0400008000300140718004100041c007201c0303802c01800c005804080c0102d011803240f076103028420f8641610080e200da103a585014030050024001000041d444022902004010441c055060b1012a220b4440e98409800383c101c40d5807650b0441d1011803c0011030b02c2d580c20410101c04c07150020844100c201d107540c140340c440e074040680802c134495000e1001415103401850540c030003c0c401410818000168a05c5403455400300341a2414141d1a48840c40d10074050780c3c15002e052100702020107862200ea4070480600c60101040b1410511419001818000d43d81d0103a00b243c420400b500c2c060401da002500148126000407404900149142d400340d40b1210685030010000c0e0b08540d1a503940301180581c410049007044031048116440d80c003c24250b60140c04408004202c090418881c0c41c0509a2480380c00c00803810102d40b40b001c0d49844400c20342090701550300380032203030301ca0074159200c42d00082429905110f180030001440013140c0900702c148020740e903140d40d0110451 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 796947446 1250 796946196 796946239
    0x1e031603050408070b04031b06090b010501020d020d0e0d0209010e0114060307020c040c0c050105070f031a060d0b011704030314070f080f07020c03030f031905190504032a02 76
    0x3900141801001c11848001c611005c240540c80b070320910700210180310044800c03080002a081c1101c903203031108000810480d810343e5440c0500b03000e200500c01f0036031600000b9603400c0032481820900c121141c050309151580300001000d2174004e84501c0e81e6580d543e00e140d002030320074070801142d8007800303a091015242c008201d90007552706078024441032460030100002031403030103044420b010811000c41d001907070a00405108918948500241315a030702c5014058404070803031468142c59001c20b801c580c2c0d490360f06480c00140e4800d4001500c01e445001070382c0f0341c815014440c1032004c00c1001c1004040c1d054100400b259140c0200d2401a07c070b401003501c01c003103c03140d0348000c148100002406142420202c40d80040d191045548581c29134000c281594482c208000c280d050000401c5482c49000c6180b07989407881500070495803410f0603103000c4860206022030b03913490702ca402140030b1509c03542c2c8100800840e09400b4545880055215040e600da20380c040740181d0003c82d080030f82d10f00c000e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 796948696 1250 796947446 796947451
    0x3010c090b0f0a090302040f0e1006121511040803040609080102041511010912020d0e1008130302010222140306042105041e031406130b0604021e03160305 68
    0x8401c500e00301040402c19403250b410034141d5104119030f1200000160f0340714040c0c50301d0320703585070800101c4201000d059818224034500c1c40d4246030402208200c44c0e41d10b890881990350b00100f040f4103113441b0b1050903001c1c2612030400d80108101040c04103040c003001c40244225001ca40307807422a9640c074840caa00307034081c038498280c1c604030552420a00f00d0090460398910a860400015000120380d5540046000000c1c80401644680d900c51044c9401c01941104202c080320449044281480024080840144a400c400034850846c030201030003501600c0d071190351003803c406004250750801c050059103220b00800b0b81c0c000d4412003624100452b41e98000d0b0b410251092142e0b42030a4a042011201055101000010040010710405c0c00c0903800600c001207a22041c1d46245003821429141010aa015142c10100c20700680c1020741c480b46c00c02c0c44e4080f040c42486c1c1e48000c0007038000e000e8140d13034410051300c618505c00041e40040045104007445212080c224400d0308048040310000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 796949946 1250 796948696 796948709
    0x31c020f15010b040504051305010903080601030e06040b04140a0f0f02041a1018030204091406060a0e0a2a11101107021311040e010e0115120e12070503040503010c09 73
    0x41200b401780e070a250f000194000c0c8108018903848905903074140c00c50782080010380c0091584814400c2a690502401c1e080248040041036141069102c0d030040b000007400c000c151002c1010002411042408111788136600621500081285400c2250260f8081030040748120b152400541c90001c80040c031000451010305009100a215403003540e42d1040300b0000204004400300000059840f80211604144150b803a1b0224018a201c0f0610b0114051b0505204403421541408010091020241c1c0444a4a4045038189041600c8041610701c0c02d040c04920155212810b801500708155075100703042402105e440164015400084820241018041c15401c211450142ca080702841583e41c5212000040344a0b00c0154440940c1c041e034490b240080f109001000104500100b1900600e0303820a001c411700348604004101c0d1995014044005945030030480f8441c3c010001412400c0108014540d2014142040f582e0781d006441384a200350f0038800c8401d0a0380c4610034200454030f8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 796951196 1250 796949946 796949969
    0x20616061103070e0906041d1b060c15100f0311190501170a020c0f0f070501170126011802041109030703081c23070923031c020f1501 59
    0x912101700403081001070309066200e51035019140543e40d0810100c0b00030007004000301041710114014054a21881c041d280c4514014400030318003810203d11550500308000c0e111007540d56048003040030b000550007181003414200004003c2040a803261842280101c1d03020035480d00d1096803c0205801c0c0c01a140001c480c8044030a00c03801e850646500503214881c00f41c1001104104503240405a101029080c2e0203034842d244144401d0050401522080c43c02e220030031880c1e03d42d20783d14003061044400d8400c9000041d01c41c070111581100c100900c00380244007040400240c0910510b40840c140e108070725007114038205018075030403110640000303406403a2007459034036405429040100c4841d44100c4440700c032100c0b01128070400ca49408089800c903105101803a80e0700421100620b8041030010842d000d10014031224842e0881d00800d05002031040e040c00046403d206c4501804410079210300c0c8240c0c95240c0100c3c2c1404192032040450708000c40d0b901c29031950342020710032951000c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 796952446 1250 796951196 796951217
    0x91a10050607020303090d080910020d021f09060c030f0c0305060306060904031107080706030e0606010e132018030a0f020108040804030b0f07080a0e10020a0c02061606110307 77
    0x20072501501141c2d00040540303017010744200201d1040404180104d40545c00010f0080e5640741c0320044003141c09c800d20003440b0300c1e5190800a9500c10904a00d0a00c00303054140440b0f0b0201a0342144040592009082c0040f00c03c0c800c019001d0a036105101c0d6900b81000c1c01e00038101c0c800d10900e4401c01000300140a140c403401d05114102c3e202a000351304004825081810f4808204000402460580e006001c19490000d0041c1183c0e001c4900364920b401410a026491703a2004141604420490b0640a68241f51424800405a0902e6450141c0300200b000e03088507000b20113055500364013061410400001000c143c5c4444105200404416040c541c24026510071058143c0c41441a01694a081d84a03141c2404402c1d0031103241c10780c1d0100740d0410408640c0076190503004110184203120582203181c2c01612004449801000690f01181c980400c512408410001c0d82c2c0162103695288184c1580391110011040162034450408807400c2c480b00501046a00c60081651030101c100e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 796953696 1250 796952446 796952449
    0x608030c070b0706110f090102072403110d060609090609060b19020c09160e030c010f1416351206010210020408010b0a080a08030f07120f091a1005 65
    0x143c2140006540c4560350f0803050b054a20300c6001410f01c00700805c101600c60b017424000a14000d083e070000d031100490004c1c8190003132043c0300140310011040c10085000c0407090b44061190091600c1c1e6000903050450015155130015090010390303034030306030078400c0719120300083c6c0a0780d245204500301020100450001c00030080755140005a0310700c199101264810001180400142d03450560304c0c3d040c4c1041d084d095003082080941c00c0d000c0e80030380602c40b0309100284c42c8550038403883c01030080c000346040c0182d09010454441068821005100748031070304000d0400040c07000c1c107800159104140c07900c4252502c10204009500810f0325117001059256079880c0c10001d0511410351180c96000306039511540042d001400c5800c0001512040702020018000125440341c0d445070803c2d80d00801003203d00080320761003d00c60250542548800a088440d00034103e002c0031484e24069010310309035040e4001034100e038040d01501d00031440e01d824096010500b40c9a10440412030319041001d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 796954946 1250 796953696 796953719
    0x5160e150a051e0910091d031b190302030c1603050c010516020a2702030c0d090c0e0907050906040209090106080604091a0103060c110a11310608030c07 67
    0x28480441d10400102428045454a4130544225a003149182d00900140c42070b4401c0703080144c401040d008180741030564450b1684101c6142445041400c8100341402c0c00421404910310000c84284400d0f03003560500075100e0700305445d00702e21402051078010151100b82100c0c01982e402401a00c141003e2600569031644003d840c00d10b0705003265400c40c09039031405080d41c018800181e0102440341c078956002c40f2020038460348811903105009207c05500040c054400c40b80a02c0c00c0010011958101b14403c071507260b04c011401c050010030880041c8000c030381c03102140c90035a190204c90f200c050801c030a07400b400440a804c0315842d0f0041052034807604a942d0820000b40c00001d0244160301c03000060000740d100c900f480c02e40e400040041080a03c0707450341c07024040c940303140391070340f1070a1103601c0703001030700001c0c2c0031700e581112411441d5140c008050074056a100340d4080041004d5200861003d070300e0244440b94a07052000074a103c000c0100c40c1112045006025800e040c481030424 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 796956196 1250 796954946 796954969
    0x1606051609151805130e0c01050403080313050a020d03030b210d1d03100b0307050a03020a0b0906120f040317090d05070c0b03010b0304060509010c05180d05160e150a05 74
    0x310b02c0c003c00c5000500742c41c3c051240c08080100100480c0c0140c2101c185450b002100480d9030411808000030030200d580c401c00d5076002003c1501c01c00d010152414000d00e81080f03000003950104002c0841d404051f0158060070055109071080d00c1000b0010490070f080d810204041c080c180c0000c0c40104c0741c0c0341316120f1a034101d211304400303a4241e210640840e1078003c01ca02400c90055842c1420103003885c040107024000c103000c413440604207041d503011568480c10b5125904805601156011095580c40d0a03580300c1980294614001e2600d04291400107000ba94240d0208010301c20503641110800700c15881101074078010322114140040844440d03001c00703004e5454020880020440d00c404000440c001c3c003084080300e03160b007014203004c0110b0701c016040ca03407a0f130f01d4843c0e0321103401e401000b42c90303901071400184105040030002144120041500040540c0651040a0381e0803109543d1001070f620854604034065403403c00f42d82030f01b20743d1300205d9030041840408011b5403a0121100a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 796957446 1250 796956196 796956227
    0x7051603052d0d06410d0c0302040f0504020f0d0212010905034605070501060b03011802040305071403070e13140a0314030606160605160915 62
    0x1600107000350b1001180030360512100c10329080000e080c6100b40c1141c000c0e04060040c1240401072111003250142c5145160b00a2600350b4409550016001210300c241c0034103640d0103000310300d651101c1d2034078201041c03943c00100d00c944d281410b16016144030f0701c1400d11031640500440922048402000081110600300b2a800040c50aa034544084d00380515401503205400450f192921803404212414000a00d41308010705602c162204041c0c0011400240703181c2e20440d41d45900c410001c0303e0710b216070f8402600643c03d040000844484000046040b15482940b1501d20100c00c0d56080a900c2688006403603a0b2150344203008009840704410b00c61200101141d4441c2d0b41c0c0e01c107950003500e044030103910b42800e4142c004244603441c4a00304060755803801901c024403003660060084030303001e080c404410401100044183e1200d404490b0382000007906200e1164851401d240070304012a804580d8452240c284c680b40c90181c8a4241a00d20280541401c5401150100d85d401d0014070a507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 796958696 1250 796957446 796957477
    0x3060402040b0705030307030513050616050d180312110720031902030709050103240e0a0f02120d0503010e06040605121627180b0c120705160305 64
    0x2c0240d401c0700207010b11441030001d96100d2130844000743c202c81c801008031250100340c641803c001140400c01e2907000d81203216180b564081a5011101d43c01041c0b80d03401f800d440c0900c00c0842c070030a8881c0c0c0344824401da039100d4030804010354910503a4401c03601c0f41c04912003804118001280e8180b00510110204001030189640c8400249003216001c41010b0102040304001c0543c01d040c00b140703020306040f400a0046525607903c01c6104601c81d02c0d001c52800400c50702e1b084030f80c001d03041492540d95160454041000e207043c00b41000c0b6460030103e00c40c00d2001d15131120b0070004208681d2002c4580c44079070440e0f1901282179400395000784201d510981d1420702141960790a0107641d56041114014421559141104841d030856a0010030110124803c00486120031003c1c0510a203440400401c0c2c0c600d103241c84602d44154650700030403030303004c4400b000b40082c4248094400c4004040344080300351100541500c15200783d10030510b400111210f8000824042d40050041008031040c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 796959946 1250 796958696 796958699
    0x1030c0f1103130f140f0d32071e320306010b0a12050912090315070c0201120504081602060705071403010b01030605060a081801062403200306040204 66
    0x3c0300050740b150011840c00c80510000d0101c0b109050290041d407405070b4441411054240008510000e2070a00401d4030304c240407039040c1401c080710342c0e444200940c09840c01c0100801502c680f108076a001d1441940441c50320020410b030703421003803012100d4001071181d0455a0308810f088141e043c0c48100c9103e02c03024040903880d00c08010b400d00a00d031000200d504c9400300c180c01411242c2c000500b0000904240c103000c2c070400c002c5004601f40e002d081e6a25aa11284004a800c060301c00703500c4410118000c041001c031130303080301c140c2444074800d0781c480248000c00d11841d0700716001994007810b030020621400304040d0080c5100d0051b039000800250420000750780f40c9281c0302e883d40000d40800700500d1000824142405040c000880c2401c0500c07130360b070501000c202e0a001e100f01040412503840d0100710b0031141c0006d224500c0015800a205242d22004090403006844a0740e070f0203180540b410344112131003480f400200c480d1400112501d00f00090f0055281d80010b0425544240d08100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 796961196 1250 796959946 796959967
    0xc030a080d380109050603090d0806180108061e07090b030403140d060306050109092604050a030813090203010e0a0b060c0a0c03120305160c0c050604081b01030c0f1103 74
    0x250040c0411501c02e42c0c0c19598010000144400c01030313840b03903005000500502c807110303c010442003284041403a095900d51340d210000f84075001c54245030f202d04800d0300004642403c0100d0f85e5442405624568107082486440e0100c003400201e4410700060802c61040c400310040500940d0824003a14000e0a000008200b60030f640c2d01040c403035804a0380d2106c0030010421140900c074010041c9800800010b90240c0700c003084480141c1c00703410b42c0004691810307c0b61511b0001c1e070f00a000040c000c51a00c1d9220f01d461107a907482014500300d050031a80340026001030790300803241603900202080b445078848510400240804000499103c03406004404210340102300040ca668003d100b100ca45501c0c60410039030040c1400e5042c0704144c02d1a0420800c901d24289003c2558803e16220091441138200100d841406d900f02640c090300001c0d0015815030006140c10301c2140600c2c018a49404440054040700c03031044403840070901e40c40040791043d009003003010402d40c079501920703c0c0146c40c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 796962446 1250 796961196 796961261
    0x1d150903040906060f2d1b170a140304021f0c0b2a09030c120c060d0507020607030b090a09080f0a0314010906050105030406020304140d030e0c030a080d 67
    0x4124500040d07000b042d03001e4080d44000b44080810180126416207540d000034881101b0b802400481401048a221404e1441407002e1000e8a50070036440c050105c60001e001070f01d90300c400700400020300101c0a000440e0301c61001c59010f142d000b00340f548104000314442c1d203100c0010300c0540920142c040c5940100d158031903070318481c003115020052241d50002050912040d068805e0b000b4040030311400d41140c500080c9558000e81c00c4921056034018403502c14034146441c0c420b160440808202d08000c04010b400c1a0f0103104550281c0c1d0b450741d03c1d000214205c031002d00e011035002d0b100744085000250385070302080b58180191900d03440c08503c192096203546c000c0240200099955051259a0061400c81c0d80035202030322050042502d441c0c0000c00c5404003400180210760f000001c00c040044003942c0c503500300560f0061300d4515095010180c02441c8480c4c00c4400e900a20140e646980303000704070040d1745640484c0440c148036980516100601060301301c85007580305458040c64004051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 796963696 1250 796962446 796962449
    0x20a0801060807170d051605030f070b0105030d14090112110706062103120e060a0f061505121314240426040b070b0405011d150903040906 61
    0x90004100145454100391038801d05900662101540100404000303401080740043c5000d280f40064580503200340c1c0c0c66031200005402072407840000796010350005254060851180200c01200c3c40384c0e619800c0c1070b1507442d840c0900000034100c04058210059210207080e800006140104082024103030840444404c1d001c0486002c03000f0640d54104101406002e000d003400fa050300c5c0d48222002c440443c0d07540c05020007801d020305400b000009a0040e80115040d44601c011034065043c040f6503040140b07410b4000b04112801e1642c0800c04002446070242d010249942c0c2c0da24124261a030b0000040002e007178451010301c03683c111808600d162076241d1010722200050600468564040560801c1da0485164408292030401021038040115080803040102421141803291501001188035607040407a000e100440c15509004283c4000303071150303100d50000c000c4800c0d951075501020040503044041030380031032003c040711808040c00980003070603001100e0400d500c039645001510501e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 796964946 1250 796963696 796963709
    0x10e100c0c080304270212070503090111030a0203070306061d0127030506090105010f050f0d0312020a0306081b061b0f1f0506010810090b0d120302071b080a02011b020a 74
    0x981030080d41d001030882c01c2205417032081021450300344d143c0042d4540b820001d0141003400b42c0880091385212080d08015820340c9025081030b81d13460540d80c118025081520103400107481c0c9000821401e000b040f40f0340c041404ca90152144004d44401103034010000c110181204403024400c419218603042440080c40c400d2001d80305610f00500d03410b08580c0140c0c410560741000b800d040005854500540e07014a8017900c803074088400d54207054411002c0c0d42d0b450324915200040923043c2035856401501983c00000998a03001c0d20300c40f0f00300c0c4440c4a4010640d03c804d082100000920501c006507588800000955840b0581c4e043c51504128042c0e048101d04510444990100076651150039400a02428610310904112703004000034207842c0100a843e6503242c1c42c01d180ba80d5043c8007041394903400703043c035a0024400722000b030107508800c401f215101c80c50b503c1040d48007442041081901c175620020440700c1d00702d400440b00009880d01350f280319000d5400701000b50300c030300001d032001d4402c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 796966196 1250 796964946 796964969
    0x50924030c0a14070b011a070f0b0901060b03060f041503060603080d0b09091e0a052b020d0c060b010c02120105010305060912030a0c051216080105010e100c0c080304 73
    0x62000003d00b000044055803514040100000800035000149150542e0315100c2c0701100f40b240f05010304054411482d0141203070009141d42820054680c016500c1428100024407040d56a414140c1c0b0a00003501c00a6000b90301082c41c48a505003544228003950b600700c1040c0d011a0340ea15882c007200c0b96a0403d465080700020083d040c3c031040d002c1c1003050002a41c0113230041c03421301c01082c1c0700c05200e203501c030340110414850b4000c060100004140b05402405036941007051a1179142280c0e4141c401403450081d0b2980d03544410b0011400381c0742c0800c0f81d2241010a01a5134440006007918401c16040c0801703084c0c0e03000542c8424080001c0c0c000f03504000580c550540c2000d52909030000c1601c04581d0054101d4250340c0101d1060b250000c008060104000c003002c1001d4950340246c4401d103501214a604118104895000540c1c04030314680f20800316980f24001100e00d02f040080e181d42191506200c0c82c98140b040811074990b03401016020420364480d001e66045a01c41c0e03021009240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 796967446 1250 796966196 796966207
    0x81207090305011401060e0d17221a04032a08010b13050c1b190506042919060503070602070f0f0e0402120a08030103140d02010c050924030c 62
    0x80134800d00345140c1218564298642c5072450050035100600c45281c000c3c013007040c00e0300401104a40b00c203c0b2110082c080c9072181c0c0d8040f03559203403001c0130000b203c841c0da0b04040003030f1000307a42010b950700e401d1204009181c68150b0b10b80015400103448000c071042c1c1122005409206208500000352041c0c1b000880d04450380c04c208950094004030142c0d0481c9420103201e00030039000121581403813034003942c0048291580703070642418856104540041c0905240070100000468018851885100f00d01070410031440f62018903501298941038480901010032030748071405070820001000848042407040c1c07a03e01090800a155000e100560f10640e000d000c05c13000c40e130410002d0070030300070201d504505d8100281d110700000751010303010b180e44042407044668244085800107070860304071966540d481c58140300c12000e195000346280900c0300d81c2c140591060080e0b80c12075070f5650740c4605215200741004105102d00c075020310240401c26071600141d0748000903520800c0c55010075030b181d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 796968696 1250 796967446 796967453
    0x1504051e030f0706020601170a02100c0c0602010209010c0b0628140103021c02071505090327010206014b0f0303090315060b1605010b010306030f0803040812070903 72
    0x4140a0250401d82c1c104800c1845000d50011728035044078091855084008d680a0800e400c10300d003910043e401c0701041d2601c2e115a604500b40808152044514464050f80e8043c00c0b801c07400340c0d180aa0010f50618004004907069080107900400d00034a2401401502c2c601c014881442d903821000441900c4000c100082131740c3c640c1c941190087c00d065140541d0010300910191580740d000c1e2503035170702180400c03d02c0141a44011044080e4808021906100000554a8200990000c2030345c40382c0100c0d62001e80c510f40c0c003480e09001030b0020401a402d00d540710390604010700310071044e000b0b5000c844840100981680c0b940c0d1000d140e00071801d1010260f442280502d0344c00c040761095034944d00b0400654490703008012650000c082d5a070000044103c400903094aa00000d000c28001c215210b0201c03d50340c00da100b0b284100c0080110821007001501504c001d44006403164050800715004265140006c1d54070074800c0c43d69501c2d0034840d5942101c91202984d00f4000100341100a1040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 796969946 1250 796968696 796968703
    0x220e1006060c080708070c15050903070b040e16051e04050f0603010b1b0c0a0342090809030f0f0c030604080a030c030902040e0c1512061504051e03 65
    0x6452140b520040381c16150700d603c0014803a0340030040a61000091140034400140201405400942c0040300c0f0341c20560300041c9590800140740c0e01c6409403541c0040c2d02d15090045404903034411310110340391342e16140b01e84070010710306120800b405030803c4442d03514080c1c6401e240040002c40751068545040006010141c01550b54082c081c0000b04010f0185805940641c0c070038100154079102e42d0001000c0c51410070303415100094010303042034408010003a14646410032680460003183c00680700ca221000c0350020308003500c40c195000000301c80c80302125003088032072030b020b80c00d80da180c29100380c0401d10b45800d5200031042a00000b140c86080038040c003c401c0220000c4000300301a06141d142d44000340700f405102d0003450360f40c0079210380701030003600421169038006001f08001d949181143d9181e601200b041d92141c0b40700009210401181800d03124511080c01c80c1d03a6075541d441c0b041c04005030ba00000142c0c003820a1100240654408240710b4403032002c1c41c1000c850041c2c0c642810302c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 796971196 1250 796969946 796969949
    0x204090b04091a0403091d04260414190e0103020909030c0c01110f06040503130602071211010908030d09110f03060f071709030301051815220e1006 65
    0x1246041c1080b42c80441e0200d200301c021044540a840e43c1d0352610b00e002c1c1d40140301035001c000d040d4500304101c200302036185889841140940307811211260030425070380506100700900458505c0c10700090241509071f002c840d9801501400841011341c0d1b40d452001c40d8a01940f1036128001a94014000c5042661042d0b070080c10000c011030908610805550703e4080c500c407944e04000c000c3c610040c0500041080c8000002d000c002c1c1c0e5030505041c20600c1e1298040c2c00c1100b6025415000024100d1000171003200310b40d0302151503ca0206255a000701081c0c3c0103241038100700c034403030700071a10400174001852185401c1100054003100f5103411740c40b1003203c0500510840003480d100866032804550940d1080b541c440d00c40c095600e0f0340003030701c004070788455044003d0395007400c004140900200960603903a0032034000c11b07800c02c101d18140c225a02102c010b211000c41100112107802c00c2600300d4816064070420303801104440c000c00302212002c9564041c40c1e404071440711f0900c20603114060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 796972446 1250 796971196 796971199
    0x15090304180917070b010b09010c0605040f170901091403010b100f0e04020c2d0d1716051c110703021006080714090c1b060a05090d0c0303020a020c0a090204090b 71
    0x1401c04e040307500d902400700014896003a164600141c9442282c0c46400500c61459001c141041141800d05005205021100088410b104610800840014824103075030f04280143c0d90803200740d04220998000405012002d0341640d210361200700310756505100c2c044441d1a6555030b20035030080d10320040c5440440a201070040d841003110072203201d408561444040000f030b031150782c101740780748140c0804142001c0d111401d0141a40545229612010700c8074200d07480c102c40b00c1691600b20304088400310035040e95010503000c02101400303034110b51070035106912100f800600c4294018045205900811041713005802211a0255200e007130322030100a0100000104607841c01c00c0f40c401d00b00142c501031340d0b01c01d151103400038400100d55000c0700c140d60214212044201c00100304180c3c0d604040c1d40300f549290402c000a00040000039032180550720070f036505c03011f550590b10154003e62107060707003408501a1072086155034031900c0c140002042c91410059440d403814100e0b60440f0324840d18207 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 796973696 1250 796972446 796972493
    0x210c03020a0b0c06070807090b0703020a060204120302010e030309030723073309060c080d020c06061005070201020c0f06121528170f06012411150903041809 69
    0x90541d4231000340c406072035000140c01e689441608041c0c5c030b0042500c400600003400024041100c1d49206000d151042c882e0300240301d42c4020006168403800221003c481d9a0300521001d00401c03038214000b66421000298251250244410281021101c0d0000b14030400c541200380185071020b000516958002c250016464002d05001001865584100c004103e05008024148003c4408540d007440050004650301e581c1c0903c117903100c0d40203c48141c4652045c0c011000901d000d082100d115550580c050841e030601c03001000700b05550240907030380060040c0100c21041581d18001402945c009611401c43c8402d80c4c00c002c3c600c0c010f0340010b01d54148030403602c041840340900c02d60641d0101000701554070001501315180400b40d0f6000bd1440c03141000005030818030880510b01004c00c500641140040d44000303803049a02c1011904a5900281b08290307103864071000702c0e811860120549141940c0c811000300220082c5491000c0c050b80c2c0c1d204102003000c4c0320911003100e1500c0225 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 796974946 1250 796973696 796973701
    0x3120c070f1101021e061e01030f080a051603110c0a0b180301140c040501030b060f0a030f060815090d080919030903120507020f0406210c03020a0b0c060708 69
    0x8048a0201000004142c0c10800b0b041d807081e42c2c0284620b1003a001d8110407a0764441814444540c1c4241c00d9581c103012004015a041c101505101d031681039a03080700014160112580d64203030a540442c402c1c2040000c14440f404071580c1c00c0002a9a19000313540c0d200e14544005419070800e2070845070207100703d5900c5410010504070405440c602404404000080c0b0703000c1003c2400f4005440c1b40c481045010307820400340b03a0481d07004d40300359802070707131704002c45e07100001070000c684200341d82002442801e100c290000d03446900b1002600802010101d0200e5a40329000e160010a40410072600d82c40800c020b0302a104000d14070080d801c0d8500409281441c4000a80301c201e000480e55a44400000700c1c01458010030011004551141400030010302d08840206a50820302049104503040752108400b8606401a142078440b61072410140350742400d4030384048510f41e0411130300d14410307040020150355000ea07000e0082241401c9a590340c0b1819031a141072800082200c0c0074098100113 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 796976196 1250 796974946 796974953
    0x12a15021201051210050903090904030207080c01020102041202040b0d080f0405130605090103080a0309050706090303020c04110f160b0f0601020f010c050909070e19060323040f0f0f0503120c07 85
    0x45030815080030105c00a03040c0c88010400f806c40c418032151070b82100211050200b01503000a4081c11180c0032000e81d040c269202d00124213074840e62051030200070002102102600d0a50300c45041050001c058150390b07002c50392031034001d4101000100e0308410119003000320b804c01500303216015144007810040c1504143c00109080c5041c00040c0084101041c4540306d54041c1c0d00650301a40c0120882d4600c6a984030001e11114140c00114014001c00001c1c4285c0c3c24203004411040003c02c2903a030800380d1400710365580350840c0d420300c054070380030311030100104659040c1c1c0e81c0100880e0410195502d0b110001a10341984088084c1c0542c1c504250800701c1740d4010103032035010300100d410720300d10b1705c2d088070444482204521585c0d000035820944420002e00c80c1c01ca908844041c1ca0500c5210000109c524861103a4410840b004100030000380c0002e0001100e412024030030427001d0100f24003601c5100405002103c100c03610f51002074258031022081100e0340d400355800d4a401d142030982c3c2d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 796977446 1250 796976196 796976203
    0x1e050f0d060504081c05061512180c0402070605041712060919141008030405091303033e040501020c090a06080a050307060507030605012a150212010512 67
    0x403015201c96034460200d4108520742c02194100c3d580c00e0209a003504140c41150010a42505c01d9031041041d80703a0703c0452180c10050711f01103041c0e0000007c041d81d80060060420707020072481e42c4107001e03000e44101c1e141d41c0e62000c0c01809010b450300117824a0280f802079107030b030440d01c1101c100c0102409030100080800b5901544820140c5401d03285071036103025400701c0343c05c07050a03060030b50030300038180ea404d0b2a114000c0d00c104601c80e20384400c00d81c2c510032a038403441940a00b5800c803412000003100a010801203100b039a201c0d103800601c025104452000700d02d0903680843c101c0ca100050700551441480022444003000d0250601d0710340b4100020350342ea00c1c00300e4511301070b070010000503c082c01031380c5c01100103007015000d6440340d001c0751030600c3e1640e106810854034940b510300440c0c50340d4800c0c0700b000207039441a110b00b580f0005410068103034808010900304c3c014004400a40001c240100407608070000042c0036803074400c10104c0141d1030105801440c0500d803001e450030152240003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 796978696 1250 796977446 796977469
    0x4030506010303270608090610050a05010813080a0503090c0915040b0a03150e060f0103020901060c05030412210c0206090f210303071e080103121101061e050f 70
    0x1803e015074204440b07440114005036202018143c80481c013000a400c1d41c00c800c1d0b4500c41c21420b010345410f643d90303d0600c5100c1e01e00f0b01038141c0003003801e9030910547d40500c680a0f00608918179030001d176150f603920040994400e41c1c0400001c0d0010003400140c04080000d00540300302260f081441d890480d08200c080c08654a82d0b03446144c980b502c4889948894502c0b40c0a0740d0007440031101c0746a41180380703000d000d20840c4019039118040014254041c1d09003c2410380f0740c010541402a40303040310840d0640303c00401581d1500042000044120b80c00d1031303d5001c1441203288818240c0c020100ea042d10108000407014000c0080b10040140e5a0f901141c828807021039043d0f0b4800c0940300451070380003081400b13105203048540754015802001001c0c40c0720b40716554901c408904450302c2100030071040e07240040803440000041c4001b8910910a00c1d0340605441e1000f2090182010982502c2e1507034413080050341e19614080d02074400340f00d4640544000d50303194850358000700c00b150503040789 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 796979946 1250 796978696 796978703
    0x12140304180902010507060c02070f05090405060714190903020109090506031c17010b04050f0a3002090703050106020f0102071709040b0a0e0603011d0a17090a030b160203040305060103 81
    0xb00e400010842e80034805542505410000070021216544806981c0b160f26000384030f0030183c0e5000014282c90b11307602c2c03d48200d50000c0a803440d07444403c01910000141c03a100440d16000344094800a628900384a144420948e01c840c401d510758000075080102982201511070700384400c000c4075440019090740c0b040c2c03903103030080091000100c0440d0030000315041c0c3d00c4191400c5000181d10403452000e4802e440f0b08446010058800344104072810b1b010f40310785038810001c4084c4181740704000b1189180e4050100294454503460b60028180c04800c59015001c80d9640303005000c6c0d99270400c421010001c03072000851030104a40c465000440c1100ba01c4003001ba00040c880c0301984072600004005540a00700038500c60321415207000d068002c8498034000c1d1310f040036554280800c2c000120301e402105010b00922141074940300c0c1303070440c114040b2074500c10810040c8111b8071028222402980074403108001410302d4403414122160710040b01045510500c014800700e24081a240e045030762 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 796981196 1250 796979946 796979951
    0x30f0a141603061502010f060b03060a140619020d20030f0309070f032117010506030421030b0307050a05060f0d0608030a0f02060a05150607020f0603011214030418 72
    0x8007400114041c1a490304080b20380c04420a41248154054011802c4801071300400e00c4600e440b0010214180821128a548807081d01d230100301032405055000708511000e44040d291044014021000d0301045840d0f1005a10042c0c020813400c0c1d01a14501c841008651025074504084580c103650717004545103d8002d0000002003044680100302e0880242400521000d04941d070f41008804645941c6911a01c0001c1e0318910721310718450042c030000056500c0c44000d241e42080144031098100510803100c41e5042515008102798105101084c1c038200e9802042320800c0c0302c145800c04841b0782c4903a001da40c829900340804d41d2000180c0d45443c1d014003c40740c4680d4102c0017034010f003020b503200702d0381d034080003039081213042d4080d184e090414216005c44031540c540300c8506080300d4085402c0400c0e084052103031022403610f00c0081401074002400041d0000a240c0065400e0707201307910190003008500209410000c0341540361500c804900040c50403d0301d040e00e42003011414000341d045056 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 796982446 1250 796981196 796981231
    0x9060a090b010e10091d0106080106260f010f0e0412050a090f08030706051602100216060e010b0405180706030b060712031a0d020325031403030f0a14 66
    0x900c01d92000140b494003c0c078282c400c1c00b10080180c417940460154440480d440c0220015000e00c015070641203641542d071700c40040c1e283c86801c0300c502400c0e220b003035690302d0310501c16260401001a690702070700ca80c4c00c8040784c81d490b080341c10009214030303803203080712003a11410840800d642400c600ba860071182081070b90798840c48400c540b81c400301c0d00070700d20b084101c010120340ca041c000058200d09104180030406921160342c0c510140003012040070040e4030075582e407640c2c14020f4000c2c1003003540503d205e0030618915070300c64064455003140103500c0ea564040d8801945418000c49030404142d0883c60341240b8144d81302c5031030728214003e0606258903854140e405031240d104441e8410341148044041e5014054018040c0400d00040e0b404013100801ca525103161201f2404c0c80350368000e00401001e00c850b14500c41042c80151004900b41c4d090380c1c00400701c0d04602d0b00e0228410070740c1c003440d90b034900071800700e50244000c3c00c00518540b030700c84c056141d6071518191640110540400a0310389 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 796983696 1250 796982446 796982449
    0x30f0309120a050319030f050405060402010f0e10110d0c02130b1804060507020c011e08060303040801060821040b181518121c08090f1203011409060a090b 68
    0x10b510703290018014400007441e480021741c40e1114503121070761076506200007421483e0100a9682c2038601915075040980800c005600a0382c440d000d404860074210145a444000604902a500401804104a06031040d5a81001e000c10000e40c105820981d01d00b0382d0a4011401792480103800d001c01c10780d500c4400603c0e6a40c1c05c10340b00b00a400e14154040c1d8035052a000e409420255007400252007880f0300d4018640c095501e45441c0e1821001c0103000b2424000300b107620200203000c0c503030140002c00021864500a00406000c0e103000e04c02040c00c071420500c0409500400f0400054502080c081480020490b50880340f921401d081000000e40340d4200054a1002d14080e0070f040c42c90001d252084c0c88030800c1300c2c4c0c00294048500c11807004a080b00310761a400b41030b000080000c0c102c481180064041c16000c1e130080010740807078288800c501007486c5080155486003d00c0a00840100480c03250f140c90488624010745003030364282410030210340e9020a83c059402c0302500c0b014040d129 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 796984946 1250 796983696 796983703
    0x2004020a05300115033905040b0d2c0d1b05060f0916030302030a03050403050d2c01050f0105121c0320070309180906060b09011815081306022205030f030912 69
    0x25004c0444400c2e13039042d200c1c0b030840060507080640e4100820340c0c2c0d110090300b04807016007804070580d00068133105607804070403138103010000510340200441812403000700380c00300007aa21071a82200c4050b45030400f80c2c0303802c0c40c0081d0f403582c4c0100da1801604c14000264080107503201c41d51281804175050f1240d05c0c007914240070302000102c140340f41401041c504000f0703d42c03a07400f92202e225000d80c1c0c40c0035192102d081e95022a503a445100012004200c00d00b4105444d02092200c1d80a4581544650710114103501c603c800c004d001948502e045c2c003001c1c01ca80c203034248408805150714a0700310643d801910300403083c0f0881c0c0d004403800c80001c000300381507080320400507030050741044600c1c1c071001e0400d460b03003240014a00089100d00c00124500070130703030300506807074800500311140c01a02c2001c0760660741c020040c1d86600e6802c004070000510300d00107069086c0100074000314408030040c0d074955000c3d240e48024440d90125012500030301020003200d0079000291590f030301e081d0a8058076441d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 796986196 1250 796984946 796984949
    0x60207030e0d0f02010305130206041e0b0f0301030b060a050d0b07120603140709060f030b070c060603140f06011805060a03020d2004020a0530011503390504 69
    0x802150454500b42040b041c0c5181d070200130b100b620100219100d412581c0101d07160600c2c025040341d400c100c14011503500c030404c015514190240c0e201e0036916507540d8003c40c1c0152030200c074401b00200c01801000110100d06900800c1074500c1007072203180100240076a4450003001d89401c5411000c1003125114400e0b061005031407000500003a6940d18041344100c0303014006980324050b150020070018060f0140e0300032103585410701d070b1590303080da15042009034000d4090400d0200c0409148001629805100e00542c003440c415201c0c00ca11018080c08c02c0da0f0410046855005140140090056141c60684000f0031380030009881d40c1d9800810b40d2030005803c082d520034004002a0100300d40c00b10307101e810383c0e07920356032041c07041019085c40240c0c02851151804510240181d0710781d000d281010240340480107010038101080c0f031400403020002070308000340d44081c01840c034000700d03014010054801460880155400c0c1c43c203454000c05481113590400109445031500d044030f00c40c000743c90 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 796987446 1250 796986196 796986199
    0xd03030608121c0e1e01020412080901261f09020c010516050c03090112180606080c01050c0c0d0305190207030606050919240905090c100c060207030e 66
    0x20115505041464095009031102559107a25001004542d85aa000f07200e0546000c1004014410b001700c050010b511a881700d4107200d660a0100290300d603054040107030304a01074004503540300358440004141c030655800d0080d00e00142d1001030000340d00450034a82c8402c110411a0403031010f1010030090291399801200141e00205241c1035160066101c0c0e409090000382d1588904841c031030a8480703000d4950500e00070340060201c00002d5008403201d01007400c00c00800541205800781442c2d00112800d01581d0403a5940c0c0180000f0b1010881d550342c2040034244182851148400b003542c62050140450103811104800030426000c2c2082c0c411050288600c5c248208080000039a58150b6110640786141040c1c0000307581c1c00c240341054052208041600c015299581e00301003d070a0541d009901c402c000107011001d900d40d9030038900540b21035400807c85045c102107641c64802084501d62140001d00e07840084d107900000c1040c0220790041c000b40c0c50710100c1c20281c075901032060755507 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 796988696 1250 796987446 796987453
    0x20306030328020f0f060c03060d0f030e100e0a0b070f080c210c03122e0f0f0807060e190b07020406080102030c091c23071a090d03030608 61
    0x486010440d01ea07002c801c041a821070340080d2401c1034440d03131a10f2140d03c43e0200e81025010900402d520002164005409400030a04000903902c1da00c900320481d0041c0c0010b15260131890091038500c405110080d2645400c00d0801c8042c0b000400f0120140315040c1102070000305031040020601c065482590084207042e182c484000c6c200d910380303040c1008860074802d90680c0c0008010440180c4d40000c6c440f40c000c43c00c203040380b6031150640c00082e0001c045200d1201c404c2e01111b440010180070285076440c0e511000d032a102d50f460244540e504009940d0006d1030040c0140000015000221001480d081d00b1100c040408140308040da105407069441140341c022800c03000c01401080101d00c01d903410480142d8581d0326508038002941c08180c9007404001203c0d0700d140c01c80e6846141598610380c000305007980d0b640d00e00580080751010040c10850b07132014004400900c0110000e100c401100a295288500000194850140e50ae07200380303841c50800007894131a61001e4040d00f29501107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 796989946 1250 796988696 796988737
    0x50904081e0c10241203030c020a08090f03100c091e03030f080a0b04020304060504030e010e030d0e011403100f090504031b05100f020306030708150109021b01050a1d0a0f060203060303 81
    0x4080c85c0d4a1082c07020740101e41060010080f036840054a00d5819800c640001d00b040080740030070801014444c006a8107202d045104c0420607042e2003480d20310f014648480c2c01092078520301c0030b5081441040e84090040b29141000480e8002050500340e40151814070480e503a8621450018a0600403658000d0320210400041120992210340154001d86900c8521825100115243c1d615102800e8158000a0300f0101ca140615050921410141001d04110344106000d04143c1c0080300c1c00e4204100c08142041060b404103130b04005801101d20500091a29450250052040164400741c60081c03040f400c003400f409020b4141c0502c0c0071a400d10500c504484600b010f900160b800b507100340200d4000094080c03000591501541c100e407020200c0d6842c00d00142c00139003180c0340c40da0104100320030a2640c030b071080c410b5070b1190059000002d0141a07014408120615079004205075610400701d1174081200101c0920754070750b000f800035030f4940d144004a81140141940364517452501c1c0c12 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 796991196 1250 796989946 796989959
    0x306020c0105070912050c120f0609060105101d06130302030609010c0305090c0a12031e020a06051b1602010e04090303050a11120c0d06050904081e0c1024 68
    0x200b8081c3c0040c0d82e60000351510f0344043c66150b8100400104154040204004941024070260028000c040701740e5011a200880160609500301c811136103e4101c140107206a2500c00c0200c0c10001213072800307020003c9c09800040041e481c0c0d0540e01d21805020803503186444060825501940d8054181e03191800c01842c407034046c000441820010a00340000100d0080e800030b038001c0c04180082901045602d09074000c04034000c661000d0301003040d1500c6c00c400590351503910039030a00311a80108029041403c1c40800c03200090b10403540d5180241a0440079605001a10084998551140c0040c4001c1c401a1100380c0d141c25540d82190030860074a0606802d980180c1c0303d48103124090005241810901c8141c2c1709040d6051a0b9041201c041b54241d00e045015090b01c40700da0784001551500d5000181e11742c203041300c0807101d1000000c0c0c0c1040700801c5903081c0c80d0302e98405808a041000346802c19807108800b4403001c0c0c41d02c0d55544810040c07951245e0304e560014082400030269a01c410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 796992446 1250 796991196 796991201
    0x121b0405180610050906070b15040504030f0e010306050f01080a090c0b1309090201081810090b1e04021c0c0e01081c020606061603020a23010c02240606040306020c01 73
    0x4800b00e118602c09040006014058801c0b20103458000b0b00091511219550700c01517418090101e036a420940360060030951218400c00e03018a00175140d905c0003514901c80141004404c010160425080400420132070f120f030704410500640c242000c0d107640d0f0f25404404011700f041031020f0000d0300c141301c001602a11840042c030410514a40340c4000a0702c0703031034000603078202d41c0d030007400507504000140d0124900d01000c24000c1ca004141c0341082d001c10103002c1921580f48040d1040c400c8a0244204078403001c000794500e0300021948095032425800050050301103040825002c4e4241d1034183c02c011100407005c014018001000d40b441d43c40d900425a203004a562240700042c18050000c4081e0001505a1040d1030090406282203a402000c40c002c3c43c032040d080f0158400c0d1030006002445240d860000794860124804403072098040440c04c3d80d101003070241c01d5400c201e220900301c1880303a10360900c02906000642441d119000442c0715449280d03c09003043e440462844d10031581034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 796993696 1250 796992446 796992451
    0x20c032401091d250504150e070504080d120f14070e0a030501240e090a02010f110d081506120c031b0703080103061a010c02090601090f120c0803121b040518 69
    0x1c1021113444c0e490341e041c401210380045081604180750401040f1000002041076480042450041d00342907a4004151504a540304408046516080000c1042c41e40d440340340c01d0781c11000000c1c48110705c44200c10183d42c0000d0034400c10480403000781002a11111042d4005540c04002005261101104411100510b00c1c4034074540d000c000c0c4c0003e0510303080c4503541c080e0000d03a015042d40c0840d6801521800004a80380c01400030269800300340550602c400c1300700540e00d4950f1301e407170303c1c08031447d140c115190040c0512078602804a044048e90174460268042c0c0100617547e5240c07075442a07550844494404801c00c500b000841c3d004040c0e00c1404c0504991040206001000f0400055144116500c0c4a240050840010303000545040c0b09180d80010040c10800221500e4500f075414101c0c45800003010b1100142c583d030100044110701400800d280000b4500b45180f03030009c0c002c0d052018100c4d01b0204540d00f4107212641c06141180d00608000b003022100346210981d03000b5a8108 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 796994946 1250 796993696 796993753
    0x71d0307081b01020705031f0603151d0607020c0d060b0d031e0c0308040b19050a0218040c05030c070c0e07030603210807120e0d020c032401091d 64
    0x14400b0b82c00e01940002611000c0e2500280507180f0340720a1159001c2d42001c0c00d0030301c003010781c4a800c0040440d500741284012031003564804030302c90140c002d820f0f0f01e040c1440056185948100e0404c0030843c3e0105005080110848150341c01c1c2d9201c0c02c0140140c44125581684550710244007020903802c0103d0001008240d4800b00000701c42103411f0351a540c200a0140200d40e02c240054002200351071100d500400300b05d0400152580040390718100e6004545184611b031b400a814003c1e580404070150f460f081c100d40078030801d108070b48010038500014143c81c0114801182500410214500c0790002d0f01d10b5040d8a6464030300250b00601400d49840700b80c038103188001f2411098620901a80e401310420345403090651150711084803195a04401d007295955176541256000d50140031501d010401a0300601079504810200340c10314407000f1901d00042001807458440704d14503500c3c40d0440320140c0c400a000102070781c5455441c2c8202e285443c0c0c90180c2c42c0b803c1701e010880904842100c22 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 796996196 1250 796994946 796994983
    0xb03100b0c06040605090f2e05010b09040e0307060c050301150f08040803090a0c0b03040308072a020d0b1311011d120a020901080106090c0507030503071d030708 71
    0xd45a24180c040e220300045950319801c45000100410015002180c12150742421101c20000f50302c821420160303110b2062000e405000900300f80a40d03072150a280c200181501000254074098000300188034014020303004d039132501c0b05a400300001340242c440f51038210905010401c05564010700d154001d0094104100141143c005c90620502100c02c41c501c2c80c0d00d41031140c2d01c0c0c0e901c6441194000807c8503a40d4441d150b4010006240c0749e091500a14546150584038100303031401900e4100022705840400c20051125401d025001c0c008104950085410704201c802600119159100c140c00107400c0428010070300046e0151562641c0610f4091042c002c0c0e2541d44500458080400808480e0310785081e11110025183c01c5003208217910742e0384c0848003034003510f502052550009901242d496599041c040005030102e004070044100c042c50110720300039007a074000c0d10074040505410208001d6621481c460000100340251755100101202d01139651a203505907503507a0004030028808 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 796997446 1250 796996196 796996199
    0x3051c0f05030408070303050c090307080a0b0a0e100f060b03150a05010e0d1704030b0708010602060705030613020928030501061410120207060f0902190f050609030f070b0310 77
    0xa1007001030301e0043d5405401c291411806032000c0300944406492552400c00810000c402651308104c0d9000508241e0040d08800716039060000b4007410080c5600c507894100780c0604c03041807000c6802e441010049034005a003c13220200c040050030150030030802c0c45000000d1224907414040c0c2800d84078011903a85101c1e0385c5440044400b507001c1b001081d04200b20310720080001d00c05888501c810010f4003045803e01e82e4a48030303e04070348030907203900004c0f6042c880144880d541c1401290342c403d5660800c140355080c200081420054120341c900419a40800d22602c60b1380c800384222800034078040840100000a100c240c4200740c01c0c842294103610744000040c494104042280074003200900c1202c1190070400251003200c008038445000c0c5500f00440300002e10144640840c800d40070304001140340c11031061241071076044010302071302030380942c04000e2402c05c91000b030b081e140183c1d4041e8840d50b8000200e40b401032080300c201a140620007000c00e40305032040c09103105007802c1140c40d0826 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 796998696 1250 796997446 796997477
    0xa0e0109200301260105040317010b090f0402070618061e0e0c10020a060504150b040902030d0e060d33080303041101110f0708100c2703051c 62
    0x44038030700111140440500041203201451907180c100d004a0300d0110b0110090a20010b00711101124100c0c0032079600305620100100341120340c0d014142044c09079140c01c40590001d401c0305140c907906803066400255481c10804aa04050816040d1612400714441d50f450100083c048900c405544003400b040102d00b00b540034000c00c0040450301000e415200058018803196904040d41c2d030b010361013440c0f11000020032a104007403040c1e004115615402d508845800c040d1403200a540f071090342000400c2c4007590380800c01281c221340d5810705510181803400485c80c28092002c4200407a45040d00b80c003007880d44c20145c501c0b10032442c080048081c2c2c0900e40d1441d4603040340a0000e16a2042c00001c002821003e0040c1d80103034141071450480b100d01c100e5518000c0c0c80724100b0b030150810403041000c0303482001418004a030904060103184440c1000038aa0b5400040d13040704c030080504640400428134400d10051a000b006480c002480c00c10140000061100c4640020340c2d06810341901c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 796999946 1250 796998696 796998731
    0xa030903031524020f0a0813060305041104090c1206060306050c0c0307060506211614030309060d11130f0915060f090b030a0b04050604060303020d08090a020a0e0109 73
    0x960f8003020841c1c0040411100950402e84280a0349081d441500c02092807010108203240c403217445003150558a00f030101c01c40056907203d80c080001c0c1420701e024400065441d04046010134410b4400140120044c2800c440588055211003c090010b604403818000b85801c0241030740d008003800d010030748440403051014410615002e003160003d00517540003d0303d13a00095040341c40100704100120360805400030000410b0441241c6078000702125021514801950006003100f130700810f009505003002ca5164401e440c46284110000194000349040c0e96002e010120a2441d0b111340700c0323050b6a41c04501035114000d010960013140b00009060340d6074014610483c1c109150701c0c1036a4500101034940c1c600c0c010f0040c0a100b40c60f040402c0102450340590b1040e012013a01007440002c3c5000d1008403000502a207004a040c040c051012a8002442000c065080d01c2e150180740c0d07500c3c03505420500d620340c00a40c00955098000b4000f188160054182d9070440420031508228120f010403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 797001196 1250 796999946 796999949
    0x100b0717042d03030f12110a05121302130f090602040914150607060b0d020915041109150715180209060d170903120c0601150804030804170c01020a0309030315 70
    0x4080314000b11000c6d100c4c00b01c0f128200c011135004240108070003da00c1e4280c0040c82d242000a01c04103001554a85c01801c054225140c0c404008046c60f058000c50f80105010b4041500141c0310103903907101c0b42c80d5a111200e800d070010303011904c036601e0384240d80c040c0100d85600c0e01e9100d00c10000c200c00c1c0b0902c1d081c2c2d0703c9440000700542c1c81c0c00da1503907400000e445c06d01413040d80184c03e030310341001507114410a5441001d1040a450b8010000420030085440070269000001800d01240700e454503069115106203140c0c40702152070b04102e01d040707400780d8018160340300c046090100d0410f48109031105264080e01c2254440c9523665884103004552690a2015200c08a00c0c241096400ca600700108000d02015081e0f0707566401b01028581142d00900c2900007540c80340004103d484005802140e60345803a00e000351081c1060f40f401171a40e9005040a0000e0605028452030420148100c03903200a081c0000c2d902c0700e92640c1c2c09030013409404410340c00b090600c1945103903001500c043c0300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 797002446 1250 797001196 797001203
    0x91c0801061706010903020619021e15060a0b0c030a030c030b0d060b01110312100609030302030d1a2206080304051c110a0b030106090806100b0717042d03 68
    0xc4980101c442c81d65000050b1403035060200d51403020000d0781703944c40144100d64040d120b00c91803042044009140c400a110070811b1000d10301215140014049400860114072216080c029141e210010300d001485502c030b00f91305100019100903808010000d4510700f05162400c100358000d01d00c0c2a0700790b138624a00250300080e000500c100140c0c190744039040129041c034080b603500700c0c515945803469200211244440805d0b070100440d264a40515901134100d515080030b0981c03840e58043d650340650b18440081c00d440d6502c481182c524030800142401d401020080e0800c01c035500d0840356860828595680da080c0a0b01090194002080301c04651010300342d425500600100c01220b00300e03c00084941c1c9198150801455489011641c080d0003d8540a0760300c0d4500640074015503956403100a203608441c1c01c015800462181140445070302d08103c03079a40420345070064418042034034201d80d0a00101d0b000c40c10710f40c0c03030150214207600c1d90140320810041100c40c1e00200002e20005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 797003696 1250 797002446 797002457
    0x60e070623090a0b0705011113230604030212030c0106090c08070908061308070b0109141f03030c050124080d05130605090a0306090605070f110a081b06091c080106 72
    0x800a2400504c014003000d4040c000000381d400402c040c500507540440341070100600342100610030b45092101440c2c04200a085000740700b080c000125916008900c0b000c0d119003001d80c0e0880c8000d03c140100c590b1071050034006c205241d181c1902c00c0007046810080c0f00007810f84c0f00001d00301806801c8060a0740c00d4031006002683e00c01c0b0041e01103a11103142100c0e2464280811400a141040141c0c080c0c21040004036084800307102921559038010080528044001e1707404031806290003035001901c2e0589041503004500f820702d680035110058000c00140c00102c0051b40050885000c2c1c0162032150082d210b2491048d0f00071603640c010680b44054403000401c042040d04d000382e0062050700d1024105401c240d640380c840740c08451b046401075400640354020402d940c0c4d40032070164460881c40c184020400302801c40c15079190318110005150040005041c4da04460f03c000751101499503004031103942c501000c00940fa100c000790341840c45c00c40714105113030b0b207405002090b06861403a80d40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 797004946 1250 797003696 797003699
    0x30c0507051b0f06041805070c120c0f080726040b03010b070201020a020a030f170a050a1202220518060319110d20060903030d0504060e070623090a 65
    0x2400150b15124a007940d0090208103400040d4840c54041c100406149031840c1d040d000b03040304c64007601c1d0000c240c00100304010f03c42c080090b0b400038803405091490718128111f80c0c0580341a070002e61381e4010241c181400420850100200701403c0700c0c040911a0342440e203205030784064000c5010b5800784407140078081c0014880c02e10900007500500f17005104884030011140c0205100c40f0307441c0c0003514440d00d0f44101030203009980f40c0c500c02d4846003020355450100051801801da0084c15030312000c001403461207000000c280d4050300d000083d28201d00c16088064070302e802030642184615405031407074960141c80c0c0305e032031301800b881440082c0140c2280a0f81004036000f41002c0d8908461124007180702c00d0386503c8000e40141340621070000035405400d401102e00d940520080014885e80040109042c0381e02e0101c251000b4120b00da00c08206078070307a4540750001e41210000c2e04607500c25454000307803840c1e00c528010300d44040118505070a803509504002c0e02d2180420350781e00510f00150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 797006196 1250 797004946 797004973
    0x7060e1b032404022404090b0607110f04060e0106090509100503060c0310030602040e0a18030914040603060c0519080702071205030c0d0e0f0306060916050d020304060c030c050705 79
    0x4a456010384024800c0508107042e00004040409445e004552200d0104050104034103034860300141c00002c441aa0428403156038003040c50071030a0103540901d100d10101503098445400502c003400300b91140300210740e190000208015134a10901d4843d024280202c1d052140003d40c040542d031002e40608025521014a0b190a5002511454a00904060010214039144081e20240045030300c08402800e101401c0415180001840d9a07a1100d40481c1400a80c00c81402012640301c0f81e260303445220b660b40040d005040c1a84050402070401c40720188095001c0e0040282140d4900089001051420304440c4884111000700241e40a00700c107000a54640d451103591a2084040740e2a00860060722803c0c0301c1c417540500c010890303036941e01d035071031418020701e1080100c207500501c40303840c21384000b94011001601d051100c07848074800c0f80e08103215408a401201e203105083d503980c141442e00b0001420741c040041d0000f86000d4102900a21036821503c055400c4030052110121240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 797007446 1250 797006196 797006263
    0x50a03020d022d010906080f060f060f031603060803040308120c0c01180c090c0e1c1b141008150a050a030302101b09140607060e1b03 59
    0x30030680c0d0007042c3c0352450b01411401140030035000e10f2410442c21440110b0000340040c41c45170000b02c24898103a00700001d551588101c10b1784040101c0c1d60110000d42035010540600c20241c1d8031010b804008200010319616080c88030821030a554200a095522940c003130700c034010f9000c001c104500070400200844498003c45803c01d90400740540340c9114441c00303c1c00c66900ea18817500718480505200c0510643c000303040b004005560781441074003d08074005015450380851188200f07504410940c44000c901101010f656022981003951001400c22803180209807040c2015140c0141c45441242800300c0030320b180706050785420903152a2520942d12049000034041e4120790503071000121980ca14208000460098011f410340c0101c081604058038121240c1210307200c0001440071109602003070210865030400756108044072010001559480380c5840a0141400c0c60051107245c40007040400c140250569850511441c0d042450f458080300b030240d1072528000b0b0a0300f500f243d020b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 797008696 1250 797007446 797007469
    0xd03030c05040906091d0102131a0712080a0c0c020901030b04050a061d0f060f06220903050d051b18010302070218040327090c05090a031b060306050a0302 68
    0x80c2440d5060540b0b8001c1030f01194400d41c4510b140341d0300c44886814010429071048221044c440c025464602c001e01c140c4000030081c46400e015240f0881c00b50502c1ea00038084e40c1480e9441144030021491501005240210a880309412945007d40f02003c80d40150100c0c090541d0241009620b0381c0703907481d5098413117401070047e54103001d507410081c0004d83e0341c8545c04095170000c140040301141009058a00a0113403020759080d80154140b003240d00c11146441d40c0200216940c02d00366903100059005440154880351280d4205140c51040640000c0541140c0c1280e03101044aa5600d40034400c0641c000400c5c403504c4002041403281c00480d01c020b03480c0c038040605000d843c088240c0e0200e8405001da18413081340c400d81c17105010806a03c000c1801410129102c103800c1e5540c01c03501510600014400d00d800c09039696082215a409101500e0292800400e8210b405175281413100e030b504034035000e1020750110020b0114289000703106400135034102900c4901c9460840e4244403403441e10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 797009946 1250 797008696 797008721
    0x6060909010f0507020607091710020a022e050a05100504021e030a0b1f05271807110f03090d0c050a031103100b060a0807201c030b0d0303 61
    0xe0b00b80b01044802140039560240c80940c2c0145400e1418100003089043c940d007050031003048911020300486d100040c180300601d50308000582c0c5200c10101a454112441111030068804120b00c400c82454800075442403844000e0900c01540d0b050001402c840e0102d41200301513006200a00903814981d001c3c05e0300712000e040604418030480c00c0074090380c2040701c11000c0f02d51281d501d1703011410140e40c40c0030b4880318061210420000ca400241050107a00c040e403021460000c03002d09800e200c5900000715a0f00601400803081a0000c406401142100c224007c1440d00200d0621140c1c00103d502084114802440c14444079404104101c8020b007815944030203000808603e0740c0c0d035094128001c500c2038950603c241c0101041c0340c10024000c0400814a00e005241441511210b0485030305001e5480d1802803991440000d41e0301c00d8408410401c8086400b41c000904180001c40000c41c00040d041440d020892140450603104d20341032054000104c1400c1c900003034040c4c1c00040c2496035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 797011196 1250 797009946 797009951
    0x10e0d0311100f09060c03020f040b09190603021206010206010f0302130b0a1502010b0604030305040302041e180c08030c030703111c0801090b0117220206031e01060c03020606090901 80
    0x1030303501e042c00075900002820340d070160b600c048100800c161481401807550706802d0650408603841451070040c00b40e1b01c144052140c1c0011015059a11800301c501049065020b0740601a10390074021700070f40104900c03500074004400803408541c000108241210705070414152000d0850b400d03c03521060b0000265141501c40b40d101050b80d4901c00e0100180260304541a84c43e40e8400b00242520440c00360540240c10811080c400310340c6c810102d405a0b9010b41d0041500c101c04401c61408280c108100d00d501490a2030030101090305066448040d80a01c8a8a6a0580743c640c0d0f2502c0e44a50030302d81120760320400050000070300404868042000c0c40c42500c2508588113090b080c1508aa11064005660399005114000140c410810f07240020300c1c01045036400641d119000e03900c05003040c1d560040c2c403c5540d054504000c88070140550180c43c1075140e05140d010002107d4080e0702d1554554003007000490828410491076014a40660052665031104804c0c0f01d0348a10242c4001010b54 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 797012446 1250 797011196 797011213
    0x60306060e06090a0506010518120a0c150302030c0703030b03150907030c060518040f0b040906050403090b0c0303010608070e0d050705330f0c06070206010311010e0d0311 75
    0x402500c6500000e01404100000d140740c41c8040000e104402414054114944001e20040c0c2e644007058413a100703000340710303522689007040024008281c06140c00849200320a61082080b01242106040700c0f000d81d40b4900400c40d02c001074040e400106c0302440420401d0040c0c1c0c0110703100e60440f070200034016043ea0080c03400813150030400d45003140c513110709a1060600b04100480010383c40020201c1d450080d0034042c00f04040c0000c20048040c0500c25134a60341a491058171550002100c2c070001401002041c441c1d140004c050314080790140c0c0410201f05002542e805008100ca40d0640041c0255140d40c1c00d21009603850341000d003a81040100c0c3c041d1f80fa038961100c400410410780604020302c4140d01e04001c01c00311552080b0300d102050354986084008030100b07481c0c04130240c41110f07141e450321031404048009001c3c5042c4040140b1400d010310884c9034000c241141078070301490060604810741d000565040048800c03a94002e02c50080384c60100744200c8121001c00115029243c1e0310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 797013696 1250 797012446 797012453
    0xf0f040f110703030b1903031e05040801150e01060f0c0b0910020307020a020301050105061303140309041401060f0e09061c08031509130302061911070c031b03150207060603 76
    0x3500070041c00c0f030200350f0300e10b40d030100b074501100045000c3c16009010840e19003590380c02002c24401c0055841c80c00302c10900032030040d000360b065034041c03c1d5801c000c100c40d1080d801a0300d514045441052056000c00001040b498811034201490300d1207600d1701040a0225074540710b0500b8000d003c5c0d801801105980b41c00c00c0f0b06400214001c0c82254001c0111040a004041c215181a4040f61080108101e00c42c2c0000010309580e040342d8020b200d000c260902403210070700f140f14030409a0741c4a0700d441c1503080000800c10345241680c0f825a0b41602190590701d056407100c481c500010f40c01240790001801510b000103410703c101c13517190614081c02d21640c0c0d8024207a08143d80c0c0c0c1000f50401490514642452440c240d40300c0714420035018480d00715203001e52109005002881080c0003c5042c85611215400000310214180d03441da60340c0440d414000f0454482c3c1c042251024000030784044002000440c01c01038a41083c540c0340f0300400889040c00961002d03a040300d8050300c428000020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 797014946 1250 797013696 797013731
    0x70305160b06030c040b0f040c020a050d1e030c0e040e0312010e07021b0901030b1806010e100801140601081b132c0f042d05010b0f0f040f 61
    0x1024441c40032030803182040b070101800c20400c1654a030150349403440d42c1d0151b82d66050124410001a1000180c21034900000c83c20400190300c003407c40d20801d90749010840c1e100015200203900015180281c3c814860101c06866244504c00001040d001c084040340c5051751000e440740c1a80b03000c50349031000c04041000c0801d000d0b404904000d081c4010460b1a036014400a258902c030346c0d8400083d014611300080d072498060002600d4801c0200000e5200c50181c298142c500e41c0c440121000f40d81e440c2c2c00b10304140c038101c4018011903400d03130001a013840b05000b90019045558251103103591000011245860000c040100c0c0b50101c04840035404c41420091543c0c01c03102541c2c001280c2003940600400100c403201306005030014120711048040c4502036500070702015008109a200d80c20080e4103210312402c0002d40f03034041c140907409c0350440490703400340c28031540007403084041d154200030940540e2820303036821600c904001c000c82c0c5420303440144504030072030300026000302d6101c42600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 797016196 1250 797014946 797014987
    0x5040509070f0e03070e0117031611190e04110303090d06020301091503020a09110f0c1c0206090717031b0a03030b09040f080924070303051b030705070305 68
    0x464540c1a902d106a0f90140e83c0c00d0308502c080c1c0003420380c103140940c1071841520510a10030311a0b0007202c01c1011080500840c1c1240d207460402055441e81401d040b4500c24078610300d14403c4500317a10705003194000c0c0720203404031243e00080d5003040c0d480b41c48015642550521450f81408104541d68641e901c0c001004002402040c005882e581000480811034041ca103a028102c0c82e201000c000680d254a03442c019110031100200d20018440b1510f03d40d8020321314002078000c0d02094407500c00000141600e82c034900702c1401030f041000040244e84a000a640005035500650014040192030504195041881900711703483d0014102c8010711411180000c81c1990f04990314090516915025510b184102140c11504a051030303554242d0200f403810006003a40b001040c41c00740e5988041401814201203070f43c0c40e000043d603442e060559808550102d012a14007008590300194001000700a100c0108000c0c1c5151285081039a050704501e0045041080800a0014216501100c0304 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 797017446 1250 797016196 797016211
    0xe28022209060e0601030c03140336040e1c090b0f090a140d02091f08060621070b13090608030307091e0501051602030109050c010912080d0c05040509 66
    0x58602140d20300b1100f40d40c1d480c990b000d02c03580700328014808100c030300701441d048a610085032480c102c11a054076085000b010481c1813104502e035441d03103882607070041d2100031545111190056622000402003161118103000d84180d001d490800c1d1542e4684001e040007962030305042d1001941c410440e11b0f10f5200d000c00c944410400704000f00c460402c4014440a00242000c8041035000340c00403405075000304001038413658122010444055444518041c401c0c1d003024821691500c0d036070025640c540669506002d40400b50894000009101403422180301a2014201203840c21100c03942c242c109045414800740c120800044950591280c02c000f80252000346480e80741560019103550006d80c4101c00980c2800c1d100340d03d100c2268120390079120242880c0c0e0b180d1a008400040e81c4155800003501903203005800024030800080c060900c54090341e40090160b150180b410320b0701284035000b0010750050105950b80340c2c0a40201e01c400405141175414941e40c1c200140080c8020385409 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 797018696 1250 797017446 797017451
    0x10150c0807140c03030a0c0b10031407151d1219030c0c0609080c01181d04020a1d0c031f06080403080f06011b0819120e280222 56
    0x1504041c00c14003403055100c3c411401340d401c0c84403204000e0455028440002c0116118000141e110b800e0350704400301039074000003085603045d8401c500c16a00c030450301a071810750b800c500400c00c0c014070840f2000ca070100396525240b085110b0f8010301c030b00e044d0711410703003000d42c001c4a50420407001e00606040900c0d000e0394504240748070900b0805aa200e56030060340c20881a200f00b0f001c2c03527200250309040d080b4207181040089907440c3d21101c002c2c40c03d4000b13054802c3c200c00c00c070400c1d034641d10340c0d24001e80c0215000c4620f030307540c3c82604040c80304504004203c00a1100007030384603100c0002544d840020450140c14840c00303d00304a00c0020703180c11000100750390380184028554010213155200120f44462807090078002d001a02281e00d00000c1e503c203440d004402410043c4020544414168801e0701d0b038491400120090b14404a410307000a44924000c8041c004550010341d4000001500300e520326420760030460416080c03c0441d090740c00c01821100c100501c001a050f5811500041000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 797019946 1250 797018696 797018723
    0xb0f03041e0f0c0b07030c02090414102009090601050d0204030b010f030605072a03090f08010c1205040b151917010c090806070804140a030504050f0910150c0807 71
    0x16040905284d0841d5844080034440707240004c0d00a4425440c2940448003030105942e00d00c0e01e508414499000f82d941c5000340ca80c640c103042030320340040e040e910001144414402c1010701140c070320300440030701550003507902021820550081d00146891311f02040050328140c0c41e0780307490b804a0000e034801504440c100c0420001d001c100d04c91141c1290162519030070b03a40100c1c03440010a04a00003204400a500c10440c00301802408040001c1040c10f1800144e541c1d030708082d50003130040f000b0050106100040c503c47c2800184100381c0705941c4486100f005d611005000081c80610180c1030360401c5401c2144844030b0403510380b55004040e50a007141004158003481d40c01c0d5080c01c4025014800d840341c080c4803015010a40c5988030842d450f0181c6283d0f918144681c01e0362401420f140c4500840140405042c0e0000040054801c1510030480c601002d8082c080408404c41d1a00d0310102085030034420701180b490714040150441c6000e806044240d120480c2c15413040302d08840706202140e5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 797021196 1250 797019946 797019953
    0x2030603031b07051c0b070e031005090c12062e0504090c061404050f090705130b2a030a0e03100c1e140a050901090b1b1005010b0f03041e0f 62
    0x100030706070b6540c5e00080018000c035650420035200c00783c804014048046040401e40e2803c101c0c958803840440c80a01c03d030304020390619210041e000440d8042c8801d2540c18125200000e480d42c010381c0401c402c0c0800081084c02c602080100c00003090042201d10400141d50f80d56005010038103006102c00680d5525000740900050800c02c02c0c0b041341d40003800108a9640c90340d000b0a4501c10030364a61145984025044841780300ba4001a5503180b404000824003403d000094200064071410039540c80c00000c1c00080d0320100d1000c0600c2e17682c41080380a0380940b05446043d00c004000d0100c460400303400ea00b410030390390300a0424002440300c00701d0000c0e6005610520300454082d0804860720300b12601086680e00c01e00e148182404000100200c49034070074040c40c1d008182c4031844a44404070380000010b8080310043c04080c510072070440c0c1450036081c2c03080904946240c0c040070300e880c01d04511002e05800007041954501500c4a004414091404060344503074800c2108003000925443d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 797022446 1250 797021196 797021209
    0x12020105091b0103090809150c010c020105133c030e041107020d0807060501060e0906013b03010f150602190209090c1504050f0f0a060302030603031b0705 68
    0x4009000d40e0b400070204040081000c8009407041d2403c0c030340031a42e29080c0c01c3c45507091056203d141c0d0803000701080820101080c00150020040c01c00081c0449040002c2c1242614415134251448143c003520741000500c0034508402246101e00d20f080c03200e8000306601040e446030064a90300c488480094404140e403041e81907400e440100ca0801c44410301c070303000c1a2103000760b00c0700138051403c03101c3c5030050140c610203840715941e0001003800690f864074001003c4080566072140203803c0c1d00c0c04241d2070343c0a0114440128031580203084003078141c40d214052000e1640198408003103690800ca4691001e0003011380d1703141e8903000403510410181c988400619217a0221045401401d030451b81006d44803448108103404a43c80041600c03a14401801c020f80d40d101280d02c82090444070348141d82040140040300d40c100e49680f51030084d407050041000300c159600d036001401702e03001c1c070109020354003a5400400c0501242d04050102d902c04c2c00d0031aa100c80000b182e440340004000c10301e0f242 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 797023696 1250 797022446 797022451
    0x90504020d1a18030705070506070c08030c010207060e0105040f0b0711070f080d0809120711060a0905030c12031c0603050a050601090617101e020d091709060403060b010e0d12020105 80
    0x100c029807400b02183c86c0c10342c880c1a40d009440c80780400040c54014011800c00030300107400c850065036624022620507038001d44c0b101c0012200c0b0350400e40078140464041c410349118640001c00e074013000d582642d403441040340003844842481161518812844010000f02c0040c01c49040c015840e41d0801c16601e24081901d00b6400400a0000c10400c1011000c01c680c2c5042c612141d03080d8942503645020303150208030b1081d194000d800810541d1a01e6400b15401c0103e9405a040e80d50b003101210610201038000c1a03c0c0d6110b034010002c00d6000b00480444400490a00c4c10004501e6242c1c0c0c1c4641c00c0101d80ea4003621281d00c45030052080292031301c61800105040030141c1c8001b42b402c070031140c40311542d003101d440c615038408144e00c1840d10482e11b92308001500c40110b50701d04c280a45000181040710041d10019250900c000c1c0c1700c0d900404603401c0308001086182020300c0d40d0f60700405800d0300e0780300c181040003901031034286895034070744103083d0b502c01c2d10403099440c41c004000b821107000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 797024946 1250 797023696 797023741
    0x308191b030221070c110607080f0304232508150a050702010605011b23030d050903040b1b0709181109010510050d09020d030509090a020310090504020d1a 68
    0x103003c0c443d884d03400103c1c2d503982d950b2040c44000480490000a0000d000b1414003030301c5108001401d000349803140c0300951169206a50003403105240c4442002480000c0508a032154480c5821201542848040c21201922044400c52142d1916541c5060084403080e821040341a00180244080d25006076a8400c0b0f240c0300802c5a00d1601000a003118094042c0034140d1214440d44000d100c8006c1c0c601010414151000504840910045d6a25031220001342c800c03c0c64400490b44223240441103500b04c0c0c2c800f070b4003141000404001e07040030001102030020184030382000002d96801c240107075800c141546051004040a50510300000610024840d2103504541c0040c4040c4d50b641c80118006c0d8090f28150340c82d81030300030440c0d0090004c3c0b8000ba61084241848104041e4400c4c0100b0060ba410307100403000d0b488103400c600a900080d1045041450f540e00306102c2801640c0c403182e0f01600040102c0300b101c3c49522044901c0d4020510f5610b458200410441c010080c94803210152a5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 797026196 1250 797024946 797025007
    0x80303070914010f11010e011a190807060e030a0c0605180303030f151c060f0c110a080a1b0b06030c03190b040c051504080105130308191b0302 63
    0x150600001c00c0c481382c180041081c01100303000b0841301e4409601c044021074901000b00039640e03c00841d110f4105060324124031030402d40710100141c00c2c0c032118000449110f207000b051014145182500c44054941d89a5014840c8101101c0030400b1a07003141c0086c240754480b5556411201d000300100401001d00741d01aa104000f4400002d102c55030070390b400148c400103c04e450201d81c00150440710840e11450848448070b400b0028402c0c16403000007456121203003000818203050b000e48a0315203a40d06c00301942c01018407032001c01c4400340180320004103450128208c04071140d810300818812402624881100c00400c01c0d43e003800c2107650000702c4118000e092503800845840c02100051100908101c00b500200e020864107120800103030070000c1038a156903200d43c02c40c01c450f800a21812172503608090114203c049083c422035112a0160359180f41c1b907841d19400e08605a2103411142c7c4c2c15580c4403206441003840e1601046400180c0d40982c0d5000c03080c0c002111401d141d0308400e03d692 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 797027446 1250 797026196 797026229
    0x81801023c0c0d0e190e10080c0102030316020c060c010c02071a2a010207050f070501050306280308210a06080309010c060b033c0c1e06040803030709 66
    0xc400203141c240030031403403602d04000380f050404125070108101d03407140c0c1c0c1c003d0f000010801e20098540c944c07107047c5030410171140c503a640f000150b40d803044601503805030b00100080b071604180c1c03000e0075012100c42d0040350361004404001c01e80c0d40c1c0c070046032000c03141d5481c0c000e00d62441c1c0c1881000010140d1520130109101b0704030359040e144c414807200f2102404802502c010403260310724204001c1c1c03d81c2008544030002c0b82455500c8510720700b5000c0042c0110600403c0c1903000c0e0003a03900a90001c4c1c0701000c4405129902180494600101c214201ca40d40d0000000b03240700e8020890840268407401190300019661802404043c01105140c0d003080801d0044078400070564807500d000f4a0a42c0e00d40025080030780003012522410f0b6003600075030301105c0d4401450421520070280e40707400d00d0601c2d1400c08800404090710904641c5d00d41101d08122a10700d403403140c29003644410200314030102c1c3e2000000300c690348998013800c4541c1020040084194202024400070030700110306035031a4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 797028696 1250 797027446 797027467
    0x11061e01060302091c080304020910182a03020c10020f1806071407030209070201020909040215040b0714010c02070f0504050a0e19020f01030c081801023c 68
    0x20014092207003010b9021407032240a40e00c0b14211110400c150041c40e901c14220305080c00903500440d4127a004104020100d4400301108007040c085036100700e401343c610030411300c600b4090601c608450b0f104d0b94100d0240d40c0c900a02c0c20040d546201c168600580d00e100d082d0b00c5a08020306c814002e072201e4811300c0848207014541044524510811400321024020f200018015009102000d85841c0b071200803140701e0940082e5100559008644480c81c555910108030700340e20aa540050b00425050003240050514041d2200d84903c64030b520381c02c1544503034145000d40c100c03150540340844044010f8036040c0f402e00c01c07085218001d2029203904c504041c00842180d0242c89484d0040d0340d508002005d00e5026801281e2100000c01500c2601c440b803d03075080c4000d650030b000d80c8161109002d0306490f41c0244609880d0900359114101075550311591401c01c0d4900c220341440f29502004800d00c0b80b82c0d45500c0b440364040d60a90700f581410315100760040840d11003020b4401090812481301e10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 797029946 1250 797028696 797028751
    0x50a05040c1502060c0c15010b0a0215040f14030405030d02010b0a0503070e16121b0207050a0f0b03090c060304050703330c02010605030304230324070e0307061106 72
    0x30410b589002a80d40d90022121854014501c1e10400781d0207d000010688a01d070f0300040248a14550172205007480d003260580304c4100075100103019050803226200052a040040d2500c4080e85d019681082e603518042803c1898103419000141d40d00c80b0154001d1810045110242000742c0081030480d0801c0154401d0150107040f05080c248250449a24030b4031034443e01004803203000c828808105000c1014005604880350800076004118000c501c45c00e0101d01c80013201e100100700a0000c0c070342541c02880e0b9001400000c1140122541d804903601c0b010011809148160010100c4610314108061f141d4440c6000c01d1128420ba82501440b450703620a0b034031000090440013034200402a0180e005108562080f60140008103000a4005840d00405a20100b07448540395042680040646909e45180396501c10546818520f5843c00300d141c405600c6101e03401d19000e0309a991000030f01d0503105074000c20010700b1301c04000e951b4070007d200302c036042400c045c0d07501d0800d4240d0021002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 797031196 1250 797029946 797029951
    0xf011d190308040b090c060a080f0f07050f07030201091b0512010507020c120a12020124180902060f0f0d0b010f020c090c07060e070906061e03021b01050a05040c150206 74
    0x640d05404c007007580490103201d0611600700c0104860780e0707035000c20000780010b01e0840d00c400700e1203000c200251008280e06c4903503100b50f20540c4c99524100c642460024030f0b4003d04010f070b0466580d503180c08001682e1807a020854403204209548480c81c100422621581100340d42003a64104010320041a8002411544054048032094481070381004290315004828030064010b0204841d50ba03203640c0c044d80000c004081c803012010340d0042014940300f0341d01c007601c910105501100700710007102c0001d61280529910052035030b441c0c01c584c0c640c5544190030603034501041c1d03000094028401c0104d0f2003490401d4500f0700703144046c0300b44103c02940340c0c50180861030144001c48000766084041d40100c2c1c0440d5404042040181030000106a40781600d00030801e40d240382100201710240a201c0414242d4161580249040d80754a4100d01a4000d4a050350303880c01c150300040040802030051070b104206042d00020103251600300ba104603400ca070700075000b024000140c0300d102c070b50100d05a40d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 797032446 1250 797031196 797031203
    0x50601050711130b0d060b0406082b0e1207050316050607170c010e01060509011208250b01030f03080a05070207051504050a060503040302060a110405120f011d19030804 74
    0x801500c8414203d6015240740074407140d00810f41c0c0c1e0303503008100165107c050348030320541d0108041c98942c0042c0b5914684400404a0329407890352100e207040c011449008089014504580301d02aa00d02040c0c0104424800413660780200e04213010303030b040410250400f000306406040107185040040b440c1c0b4880d5000250200320a01c42c0e0101d00b032415022a1954801c184c000c0040720f4a80c0c103041d0003070500307008080c40340c5030640001403441c210003c1c0c5451503401040c001d103081c0c0ca088007903240601a8980c5000074980340c40c4000842c8460242e28001e5010700846100295a8600284150b100802c4000b03030501d014144814242d0000f500419140181e5810044007042200030141d40141c1d405181d00040400001c584150301602840c080c1e48640c080b200541c803003069610a0341c54441843c41c00e54400e22040041c0d00c0d10202d0482100c2110702540c1c085031030030b061035007507503040ea162440070f00d401d294117690141d08102110202c00c251803809410070090741c004104100140015 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 797033696 1250 797032446 797032459
    0xc0a02010b0a230f060c070e06040e190c09230916060e0a08010e01020c15040b37020903070617010b07080f0a0f031b02120c0c06070606030501050601050711 69
    0xb010b094490b840d820000b00030050017161130750158007815030746403418011250507420000c04154503041c07601034602c1140b40d2002501440708404020700150b4038001c81640c4505040a000583c00320314800d020b01c040310203c3c45907076008a80b2f801c202014001d420440142d000c40c110b81603034010318100314191031880c074003e03260030104000103065403280e80141440b5460701d9040c103005a01540244240f503500d8003510380c500340084400100d1081210060a28a010340016030107804840d4103540c0005103100d80c101080d20100b0000c4004580d0842542c03030b540c00141c041a5182c10000d0701c3c000c28192400207802c42c0d50701d440329242da406108074421720340c008c110041080b1403d0240c070040c0c80c40c400d2054444013503070002003401610303800b0f113400700789051100030300124010241e900582c2c4940041c0500c0c218551101c205078842c0078102268054650304d1703d8580d407030500902456001d4000441c00b14118241039003114800303008541408010483c02c400170701c1d50488a001c0b0502101c01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 797034946 1250 797033696 797033759
    0xa030207170106231009030c031104020f0a0201090b06040207031215080a0803010e160206190f0c0e1512190626010c0e03030d05040f0b0c0a02010b0a 66
    0x1c0707025002a401030640008814112807070100e60750020951180100c5810802d42a01041514290100d00025145520f0081c052011410070070005600f40ea015100601d008180108800960018030300d10005035100c1c03c0c52414010800c08050b080714040310114a00744c01540d02400d80340e040062000003a8580b00c0002c1c1410b515007444000345078a02c166a444200c2e880d2619895000340104d4910345003110108880300b030080e149015251240d0001e1405403100d00900c030f00f14070703d07140100040341c868001c41c1010030340c0d0003050004803250304c800502e0340c481410081c100034240f0740302d610084240180c054800f41c100400350010307031845201c214082c518840700d0180c52550447d42d644481440803548541001124803840c0014030000c011440015104448001405480c641e1541c403d000020320a101c55000c0d41c1c000703104852411409009980740400e0000407201095880c0300070403003611a54080c003501c1701500b002c030380194016080c4210450300d81c202c2c10380c030255500b04a04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 797036196 1250 797034946 797034989
    0x903030c020a030203011d190c060e040e0106090e010e0609191703070f11071811040f0905090d020f210d0e1c080c03040803040f0f0807060501080a030207 68
    0x1110243d0b4026009015441c401ca4113003500d105110700780312003842160303482c00007600000034140d02580d2002d00750594901d050011034290080425003a441940c03032007100c2c3c0f0f14509100d10401800c0344900841e071440c900c0c0000c0d0844078009003000c0140c00260400c10500b40c007080c4018880001d0070000c003050402e080020840070086014420381c82c00200344100c007034110031141c60b502c2d255541e000081c0b12841d0115212261031140c40e81d80c200c414103110028010b038100601110f6100c2c0c4250401c0d6072600c5007014901c1c20380c0711010b199540c01c01c2c0300c0201000d2100702180702c3c060004144480c3c070a04007a03a80c4e141c0d034810504600c03074050440402c0300700800301c40102c000304c0414003002d1040341c074654862294441e02d9840c242506e510700107a9000d8206680f0035800c43c45e00c03500b15500c54032030411580c401813080b00d001e401c2e5a01071000956803101c548569000b001a2511061246000021103006800c22110365021020341e90010317600050280554842100d1601c10042010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 797037446 1250 797036196 797036209
    0x40b0109051f030f150915021b06010e0601090b041a090a26060a0e0703061a0310060e01120506070f0e031e01050a02130603110421020102100c0903030c02 68
    0x9410203040b0300b44000040c0809a912240c004d8004d2107038420940d40c2c0003442e000c55076010340007008070b85040301c03500140c0c402c1e034007600030000c00c7c84001e021528115034650a0800980244201d1050038007070043e1941c1c000c61080140c03458003075540c9051308001081c0c25004030390b000e07102e5150b030005031525180c5031400c80c4401418020900a001041c0c4040e81040d6020185660502d00c10351000410190040c00380c0001410108003074030b5601d0464450744060701240d140e0700154014104922416281005030500d1003503450b4001400d00c0c14449510745602041c6c0c490001101d207040c2410100307e0114960380c00400c0c41c01e00305401c0a02071419078054030044e010316414092105050203180881c6114485001c0d140002c006076070b280c5629000300c1c00b07600020010380b05917510a204003401383d8004060345c1c6000b107040d0305051740c0301243c0c62041c04c15001c01d0b5284030074208290440d60100304092a00011480502c00c0e580c905100514400d56480050108043c6010540c10341d240c02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 797038696 1250 797037446 797037481
    0x403150212010303120b06041d0a110a08011514030a091b060c06060905010b1c18030504081614060d09080c150f0103050601031101032301050a0b03040b010905 70
    0x492440300710b40e07403400c0c050164031071005204400382c1420507501d15454010110b605039038100710610401c0300b80c40840c40d01e03410000c01c480c102e160303a140f0b1314845075900c401030200b80103160386403411036041500a000688401c10080140040100306a08411503041940e90102107030b4000501c1d119141000d081c4507901c84540303004050344141c0425040e0340302070403803015806688280800ea98a02003201103a009208004c825078060240b00c4004106c0c100000c000d069204001c034941640303060b00100413803c480f044010550003e020840b0030020301000e5214940c40c01c40310403103480d003100382000c0380181801910680000489210340c24040d4082d0041c1c9401a007165200c01c0c0300c1140781d135185080f80c004141a2007410010b03400014503584141601d078014040e103480c0c3d1a507640c00e8030008071352407440e05050303c0e03a06c803040701d07204094040d00100d48055a968107525000c00d01024a1040d0443c00c050321003041004007058080030414116200d00c0c10004850ba100c1d04108414241d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 797039946 1250 797038696 797038717
    0x30412061401140a0806040b0403030c020f16030c091b260f0609240d060b0319030305150d020d0c05181b1204030c030e12071406090604031502 63
    0x19400850208803c007408442e5290075681c41e500c07580c4800d07034166121422100145244003d000180001c0d101303810000e801c0703001d40111040160061209030800250350341008403108020410400d00c400701caa580d00500d5499010402c0da10600b56202081040c1d54205041c00444031500c1212030301700708006ca40010a2031001428202501a001404c200b03545c1c16118004003808180c1040003124040d030000381801000424091010030720900807041d6806580e215524a5031007502e49040c0300300c0ca84c103250036500c844103400d54500502110740c0640a401d41c20a03501070f82d041a01c5294a109074141c046031080041c0c209480c21000002c1c035500403581000300002a030f03140148a010b040d005a03158540401040407804000090380141d42000820b11010004180800e000d00183c54140b4068075002c94044d080d5400b1502614441e900c6000aa2280c2c408001d11030480d8621350040c00216111880c00d41a0310025400380914040500701182102d54004880e18030790455811844 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 797041196 1250 797039946 797039981
    0x31e04150c05090307080102040501090915050d0b040605090c010509010320130920030402060c0703080f0d051f27140402040b0a05060d09061103040f05120c03041206 73
    0x680080080c069080010f03200d009100300d01c800300340d41c60180280e0302940c1c0c041c0d4511040600e026994009000e84940041c41007080c0701004c00c5645030f00006911450281c504068a8209032900c00101e0300010f02c0720616030099506401f96a910001321410380d0401d2901107602030f0301c0715480c1c000704c11401030309941000000342c5400ca000d00010b010300702d4459020401c03100342115000990000021070f183c80441302000040c00619002010b04031a0300050100c0d0041c0e6101d640712401c80c0d0004401080e01e1002041c99814000c42d4041c4075481071070701290310107140b04000703018800b00c014050a04030308060502083c41d114a1140364a1103501c00109002c050a4480042d00140041e81c060b030007503040ca60255041d00b40f01b099034046400c0a8502131800341c2002e0b98100070940f10800310b403516200c0e1101c40c0507021090155000b18014a9840d04400503450301621303101c0c0810018903020018440107240b00c0010040e20100d404c20302d04890194280d1400b48000c00044045618028 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 797042446 1250 797041196 797041211
    0x30301060e0a15111209010906050d1814010b06091e01140d020339030a020706110903010b090702030706110702041a12010204030c05190e010605071502031e0415 71
    0x4d5100c1d0080060759103020951348642d80000f400c450500c03501c0181b80c08500c80c880108080c51007003005103a0310345000760002e090328204024012185d030800068401c3c1c200d00343c1e001e209640c00e10440840071000c445041c0307096441c0780441c07288122a800340700c00d02d41a401c031006503409003407212101d459001c140b43e618001c007241900290820f0384c006200302c1074441070034a40a16401c22440c40c0008054141c05461034603500191584018000b1500035000d11050000031154000d0486403c08955280d44506800d02458215035160320198400d07c50355040c0503099030048102c1d422550446004518810403110030907944c400c212000703410174078201100e004015040303816010302400b12008810900c1c0030308054241c0c0118000500282804607003001540340589006e8502440c207801070302642d80da11314510248100341d0004010a400050341010030240d810040318025a0340401c49c20340c20111803030380800d588106640212580800402c0500620300d41003c0c82c1480080c0501160 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 797043696 1250 797042446 797042489
    0x41103070210050703050601080412020708071202120604020603010b0901030b10030509061b0d05092812050316110a02090a06030203060f36012c0708030301060e0a 72
    0x3a004103584810032031401001c600c106201b4000c26001c3d407016034580030b854503076880f8480800307000b081c84020741c8074400340001c07400810b011244c020311250301010b0010310180148200d50082c1c00c00105e06800c0070f01004016a9118142c074103650715041d02a44074101d5900580c002c00c88400111f500111042c0c010180c20740c5074112510941d080d030240c0708551582151890091802c020011007240b080c0484040d51110303604c4958003d000c94100e07030035034141040e421144130358500441c1c141f04800004c0f10074480c06d90071385851710074145004c51651418a60489801c03504510391410005101038103002c03070f40d0070409a42c00b17a0300100903884e1403d000c1c0d102030060545220490090090800065040e07124041c024410b2490200c4400402110040300142d25226490b03488400781080c41c4030701d0791409100300d0582c003290a00d00c80035004040059600d015228072104031036482141d05011190300030080d00d044500504003070142078000d800044003500242c00c411a03c0064981c901c040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 797044946 1250 797043696 797043703
    0xc1c020304080702130e03160309120c081605181306060e060307050d080a08040f051002030601030b0f2805041401061103040e010509060406031e0303061d0f04020411030702 76
    0x14548215000403005c0c0c228410f1009448840c130705126030790401c1c84000318844000c040c50301c809104c1d02d01448a2a226091490110304440f000c0d03508051120080c44481c81c20440ea00f4440d0705000d80c00d00301b03403030040010101483c180c030f95480e5030b4880010904074081086c641e09001d620107020b20078192a0540c00a00020880f215442880388010020343d505051100b0044507400030011403500819941c240c0703808002500c00c176110300030f501520002c200c0c2400704a40111100c400580d60382040c1000600f600c00b14090a84034101c0c031524030240e6501c0c1c01c0d0950b05c03540241d00450b4a07008801d0401c0308900f02c1e80c0415040740c20100556000d0040c010b94505071142d80d120411b040c0c482004080d941d010764022035151041000040c072540c0307002c030b14650f80300c40004c002084131a101c0d900c91149000c0d0708411581034001001140c100364150141c200980441d00004005030320a2403c1c01481001808c840750b0800000003080c15503d6a070404408411050f1003a562070901c1d0000035035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 797046196 1250 797044946 797044957
    0x2070c090c02010c140f1204050712030203030109150b03041716080702040f0605060f030603030714011a030d1d04020c0601121109040f1e050706020705010206090c090c1c02030408 79
    0x20703440040403a49507110384c280c91b0030581352007900d0b003000402c603001807100c00043d01c2516580304921001400d43c006410021038588280c1c09143c4a5240c80d01910903158140c03900300340000492010300209454400742c0307078099003012a08180e405401951034040c441c54206964071001c1c00c4240081c00204030081001500c00d85081010040005c41c04007207891030b00803168426010000710f4508a03182e4040c40d0000001000e49144c1042541d414400d644c0011694101d070751103521101030f04c00480385050340440b00380d0181224003071100005201072003075005905917001c0458407203001d454941c1034a03c0c065842c400c071461561581c00070300e0301080990307085481020b440c0c1c0c10656030610501d454020781d840b418400c03034980596501090341c0f842c1019082c11030300410351000480d0303040011000412040e000b0703001d00c5081000080c10010010700824556100305813008041d1a94000d00f644800000c90325034035820b04140b5400c40150901c484440d680c000310900061000e00e100624 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 797047446 1250 797046196 797046221
    0xb0a09030207050f101202041806090b01020606090a0e1903030506151602010e04020904090b060f0402040807051207090c0e0f1c020f030a050307060903030b090c03010902070c090c0201 81
    0x4492558a80c20044c0180c000e0500743d4000c920012444425401994801c074004910640541810784550b441d4030381f0360606024403c0e4644408041000428034030804085440c01c0c406003c292030102e02054103000084d002920040d515aa1660000414400f88908640c0d4031540100c500e205c0c24001d020b08001e4a07002d00ca18080600c120452001100f203070b0040e409040c4081b422140d5400559100d0f06000384682c10039000c00010166644500c070b106d851a108508030b002d036082040902c2000c0c101c4100b032501485c81080b050041d0440083c400003141c008481c2c0504180314030a016041030b01e141d000810241c180003c87c0740150b0001e800d1502c03140250360030040004401c04110411115003065060032002c100c90202505104c00d2642c041c0d01d01034100c07944140660b407001c1ca990700c4650103460310781d80c1e03072624410180e06016000840100311005581c41c101001e1408284c801032250000c42e5600148010402035408903038001440580d4082100c03154420b40039000c2d04501c00c2c180c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 797048696 1250 797047446 797047453
    0x1020d0204150c05070e0a23070e010e060301180207020319110a0b1b010209270f0106050a050c0c040e0d0908030a0c030c05122106040b06030708070c0b0a090302 71
    0x41110303e22035200f03942c141d0b80081c02082003520380401c02d41c6895003e414030750300a4407851003850703803100070b0920541036064071084c5070b040c43c051710020f00c0120800f8101e4100f0804ea00030106640c0e64400380c0e410360309030703141c7c071040c604070402074000034410350704025054050000900381e43e64801d0690709115008005501c080741100c000c12a4512060141b0f4100280500c03550b5510005c204c50b000c0a2000800014078000341c43e0b00050801d2406650040d81c0701c10507005945803000440c07010b81101282807200c1603035041c000082d1031801100e02501c04c0040105030300f009114100401151400e010b00200440601000c01a482d8081c58080e0004207030242030010704c40362700000302e5124105564030300c0c40040c0c640c3d408072602004400151142d1191003000510005420700600f506183c80001515403040c0341d0444242c4440203020500c260301d0078103460141c0d114507003102c1c1d2208840c68a0820380d55284015182d203440e106020309451003103420002c0c20300180e42b001001a0180d001c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 797049946 1250 797048696 797048729
    0x5030a080a020306100e010207081f0b0402070b040803070c0c0f0e10030b061309170309240117031e0c0f0106080c010311040b0c16050f01230c01020d0204 68
    0x16034060f0300c401d852568015036524038001c0094480d450008512205105585440f40e0b1820481c0c40c1c01c0b0152042c101803464060014914003862051094501088e0341c15410f00c0034507142c15004400042024041150000c0068210341c8901e0600c1c85050340f255903588115154403044042c04e14070b020b10300013504002c0128642c1c145201111040702c0d40281d40e83c03002c0ea110800d110384d075038000c42e0510703802e6125215000000c100b84841d510000d920a600340e02c0b4507294142500e421f0091188154060b01c0c900d020502c441d18008076419202d81d440c041e80403502c03d0060514500c551191480485541140621756100d52002850310b01607000848842ca00403181250803100c1074400c0c8200c507130002d11b60061035402074004425045c0e06d151024100b66072079500b51516841601c0da0b602c642c000f4030b900d811042010424101620301560344048104030701d00084c2640c42d81135840400d40d8030b4220000076480c0300c402203440744060240250744030406c4000303001c080d4203e80524103160025021 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 797051196 1250 797049946 797049961
    0xa0c180f180b030c040c02030d090f0c05010c11010507030e03030d14061507060b01050403020d0b190c0804060e0c030a080414010503130f0c0f0e1506090a0303050306030a060905030a08 81
    0x30b00c80103290000d01070180c24401400708001808590510425400300303114000c040e038180d1203130802d264003801454280700c416207840100303001c2c0d64000314144580d4180c5103021410380f04a5840c481803c0c00c0c01c50744c07030030340d810140e030b081c0d20114110307516100001c2c50080c9010b40781c2100740c1100c6100115145500c5100400050200f201c0d00f03604d03841e2080c00b941000c500103800005401c42c060500d280352070303241e40101d010078240030701c140e500c46200700c00e10411040323824154904500c251020004241e03652002015104054400340034644c41307481d800b8907081305008c5018820300040c1107840844040c6080325243c4c009100d8016001d03982d400b20b2406500503c01c4030302c10410403190424080465030341d0b5041054440c1d00355200702454801054201901d070001d405400c520300e1200b100e14258014250040000ba03105001d114103100900080d281d0340002e00589500d4109942c50b951144042803030101004805004a42031139a0700050001c080003c1050b101d1594882c0c0f4160b99010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 797052446 1250 797051196 797051201
    0x9080d021809010f1a0315091815010f050d0c0906080a020a080109030e1311030124030c2c1005090109081f02070501020c161706040b0a0c180f18 64
    0x480ca03219520110441721040c8800c0008560001d284500f191041609401113007000200311a82a0b80309145507200000503c1001005074210304035041e40755940c18851500c0c04000355200303160041c81003034481410402441400070180140f590100020ba0b40d401b1107d0396800344e420141d0040110314404107140c2d1060150584841e05921000c205d0940701043c803e0510b060250b0310650350fa1200f151500d1030302c1c10000c0d8020f1445a42038100c42c0c8141503410229084103080d41c1c145864094078944054000f45114100350541c5840100c0e003941c00c5c2d4405c15900034043d0141c0c449103100780c5200407a0481c2c05440e6903074080e03a172000d005480e282c0d40b50faa0030012981035449040c0345044454000c80360020005240314800150920321322141031480c00c0c14a0011580e51a2680024482459002c07a41d0f0220590000142402d0410740c0303d110345aa0082c080c21013654030794400049450056407e44011641d0605240d0510f0f42c407051820f4210007070054a008070584840003030307030140d82d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 797053696 1250 797052446 797052449
    0x140102070305060c071e11091e06010f03090501140403020106210602090105071a150d080304110307050a03030504062c042f0301030c0806091009080d021809010f 71
    0x20008000350703101c038130128580750002c6201b1540c1c0c1605008194501c511401c0c200701c2c1d80e205940c860b011038460030030054404c074001d1040514003003610134500c448840c0001150803203403c2c00c5c22035000000000860107000480006080342d801c003462044090382c80030b00c0310310030307402640204a00b0380c03180d031014031304c140040c0740c402401c90864490000c910154020900c490f0141011441d2540c20b87d50b002100101c00c1d4a001114029010020040c2082c401c80c550800201e440302c0d00741c8e40f540d4502406000c06880a803810b14401c10103101d60700e00300301060150400400720075050750b0740d04d4000e0440e401781c0280e0740000e40c2202c1da00825800403c41213198481620090090028201070200600d20b01c0305d0010940590b802e2452041414200a001c61003800200303039a83d030440c01c3c040499200c66101084a13440002000b0124601243d052000728803003201041e100c0e650705040d5494042d841400030414030001e9007044001181c0600208182c0684070700700c50742e9941d4402e04c8000e11a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 797054946 1250 797053696 797053703
    0x90c030708011a07140f1b0307141c0f1b0b0306060a1404060309060506061e0a09080d0818060609072a0c030c12260c0105040506011401020703 63
    0x84400500c85586412042204240c0b1606003500305566905c1d940b980d00311150801005410030020100b41280c24070108603ca0b030440b04103e8400000404203965002d28403c4d0440d90f07048903c0c2c2086a6030b10030070300b425400c80110180c2d146455052000c58200091001c4448461012500d0000700c6a216800c00f21001030340705031b085030b950005204282c3c1c000b14028007040307406d94200242c0000540907102400b916500018074a140d490140111000034001c1480f4401c04d0002d0683c0d0a450b509005081c01c0106886071030f03d25002054440b2074848d000404c250046040028455038040f080a105600704101d000241d201e484416456803c1520400d421408860002d00f6260240510064130b07500720a06428100012540d10a03550411900300c6000d80400d4040081c02a00030048026200140321010041d1680d603904130304011001d20506040014410340304102c400340155004c080114000f070100d8901840d0050310703070b0400d01807988582011294204c840d440040d403c0c05503030340b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 797056196 1250 797054946 797054957
    0x10e0103170f0702190812040807031b0b0d0b1003090f030f0c1e03030b0a060512040f0f0c150509210f030a090f051806010c02010e1c02090c0307 64
    0x2594192501d03584018001e00002004000d01c000603100e0700c0460022450f512501c84682c0e00700008203041810710945007008020600c0180303c075450204220f42161b9124010101400f013001c0d59805009482d808022001d4001c9000003a55044c0c2e0820a0290f03021103203d06000702411003941105c56061016282075554648000080d00907100da9002c030680d4100b04c550f0002681d20300c2c248009102d20f140c1c0c0c00742150300b46020141c2600a804c41600b040f24000d60142c20080300419501810084c00b17141c480e0b00d408a000c1c080310780042c10600350415080c40b40288079040c80d140b4250588981c85030070141802e22451148036070207030352000c00000c02c221612425900b00450103000d20b00d010600340250043e0020191042000701561200358407100403503494102c00f05607a584550105000d5402c00d4469104480081101948800c00742030101c008200e03800102c5501c58902113507500b1901c0c0180140340459586c40340300d802c900c22100e10304d00d5940e0781200c2a240c08213480b00c4000c01c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 797057446 1250 797056196 797056223
    0x207050a110321070506060906010221300c09010e040905070504151a0703080403050a0c02211b030c012106090e0d0c030e100201021303030215010e0103 67
    0x40700c210052000000003002c0798041d50120b02c04072075408054880c8258102c000542d002003000a1001d541c0c00041150070441c1c0e464800c0020f500c0300c500034200030f02c504420b0103401807010800c050b02c92800301e11b2800480071030841512000c0b884901d480b03c82d07046991000491035882c2a084031000036040e03480c180140301d004203100203401c1c0501c0480d414000c400300812251100c0c0b00708035440e0441419031600c180340142c4400003840503072803034031100020400c0354082904009416042603140c50500c2e5a002910400c4075100103201e4001c2d800700c510140c500c001c03c03543c40095440800c106c01d03540360b101c5056032010038030506246190140c01032203803442c0560103802591a0614124889001010312034003050445031725030441c205459480c008500c07402810800c800c0100c0c0d0608045a0b8400c0645001d01a05030351807102d407007161903502c1e240e00c0f50b1007901500c1d00b110700780c44000b02d01e580b2894042d49448200103054181c001c501d0000075402050014a4101ea030460800d903a0340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 797058696 1250 797057446 797057453
    0x5120a200a1103030a0504120e0906060702040e06070306080d0203070210080402060403140706030c02061e060d242012041a1501020c04090201021507030e03180307090207050a 77
    0x70742140c540320091001c0391046000c112020700040d44542c061103070010b40c41c0383c5480d00000404d00d8046038810452506e43c02c5030340d515084500d5401c9001195403940307444083c40098050b015010200701ca0740681414800e03140e0701500721005032070324501560b16144030810201c4e9640506c140103540040c82164441000c0d0142c100c4030340040c0060440c505c0d081c2c0f2a10740090442d1540100c06840d8801c000401c600380d0f141c4250725810465201400b10742c14007049182110b00100801c1c41c41c10301d6200400c14503a00d02001444056101002540326003072a1000130407850f012a54840d640d080030046240141680c0145000345c107001042e0342040c000e00c0300c10b22507400042c412105641c00340c40c02c3c040032018090303061250a14825100b400e110b504002414a009a0b070180e0050b4101a81500144c2e000f00d091813001d903849070b440785103980d00d40d41103000e071a64564006050200040d0320760620b50008603000203440960480d4010b950324003854049105010700503203180c01260000001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 797059946 1250 797058696 797058761
    0xe040f0920011803140f0d0e0102060f060d0b0606190206010e130f032304080303060117060307030311010914060907050d110f13020a031505150301060c0c120305120a 73
    0x1941140310848050503c01b00400d0324021309003001c28040303140c040c440111580d0400849030303c20f02c0340e0300c40501801d0490118415011246009190480d03c4c0700040c4140c1383c46040e954415003d0b2a803c0d00c00400000107522030000b80104152100d07102c0004a03189124020720803400da000038414030031304a6880c105c51265203602c03001944481f08165071181d001c8a405480a07000010246079281050000580026419400d09500c115558204807542ea40422090100ca416017400c11079001010040380c010060343c00010800607800702040340100001800c0d5108401a0048614494486040001869002c100284205110040d810180c107003600341040580010708400d114941c003606500a80c0c001c81c0ba07020000b641d401d40912142e01c0ca4981da0014041510300703518905026511910500c01401648144841800c0c24403c01c031000480c0e0f40141611034595804148c13516009000d9440f80c015802c04c880c0306000325620104030312074000016145100701d07512900701202040c0c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 797061196 1250 797059946 797059973
    0x9020a30050a261c1404050309120c120a0b01080f0a031b06050901050603071a1207050d1103010321091403031b01020307230304030e040f0920011803 66
    0xc40a000107280600c3d0000da201a004c1c0030486145241c1182c81c61000e40c0803103944001581030840d01905000100e2804800c56446580c283c030400ca1a4020329501450000502125500410008540e60690002140d00c49030280705140c1c071001a41c0c0d50804030b80c2c80c29400003e0200b50098400d40c0300107030183c40c47c04d036a502d4401d00d652500c1c5082d01c588040310012150028941d45510030800307541340901074036016095154140f02da0340c6443d0005c210600501034204001040a00072880081c003400c2a60502ca038080f00c284845520b0110105517a0000e2004a54100b0340c411038214a8180c3c02120070744001079601c00c103030b6074500003140015410964580760180410041c4103000c082148000390b0200c4a44005652030810765002054a2044c400d000c0c030340074190300c00c2c0752010318003070031071390055014606403995a200a00003001441c204000624403444d101c8000b003000b401c1e19407288a641c00d1448954060040c50056680001058080340845260602803000030802002c109 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 797062446 1250 797061196 797061233
    0x40504051008060403090f121709010201060807031506061403070c170c070e06040c05030a0e0106090e0a0c050402090d02040e2515051c020d09020a30050a 68
    0x207500c103a4a800082c200502a01d09500041d503640003401030048005c0198010000c54030b58050444c00d50300d03980c0d80e510400d0305d11180d03550b0003c0c40e090b0300da100750801c5020b0403c48040c0c2d140540da80c5044448802c07211140b01b205802c201c40014103d0040c2040001490300d114910710b50f58403003034121101c041014007226071075030145c40b10301142d1079840074040301484070300180001410701c41030491841000b44414032440c100f00001d400e03280d0003800d80c0c1e003000d2006400309424001c03010486c050403850700080b201c90f16012218140200001d005a220b5001b824924821525401400103a200303075040036403c2101600e90a00608140d400414030790310300002c0c1e604001520121080b41c400c0440c0d0f107000b01a9013070b014008150540d540004101042c14014901840e218800e0328035200c284203891800e50105900840504c076800c07070a2056401402003181c81d486841b2a2001c101e0302c151103000c0105c5010000d041035458500080b001d4000c8018002c004003540c500c1221901040f662 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 797063696 1250 797062446 797062471
    0x9030a110f1c030f06360e070306050901020c07150207030b0717070c0b19060e010e01051f020c100c06060b03090d0306080312090a0605240103090f08030c04050319020301140c04050405 81
    0x8060260300e80c450000d4603031041f0302a0502a10f50300740341d4103403140a040d060141c3d104001e809102c01e400601e84c0304940200071a90740301032403440c0c00d904201041e40080c02c003c00d08e00c1004040d682c0040c0b01040003249401c03178040d0351100790b821140140b070b07210005c0841c0c0c1c0000c01b08504c0d4a0300c1c80780c2801412989408a030b100d49a543c40c2800920a074800b40b002c00f61540180710a140851155100300b180d00d0b15020704844001e402581c40343c500da11b0a024414074a00c00c81c540348151440c0e0b0a9507082001440400c0c0d0321040342009900440d501541c130700801807811002c81c440c0c00782000326843c0b00011800c0c080c2018580710b9401002c0e00340403552040c003410300000f500a0007070512900e0580052070494184c00c264641d417950b00786419040515001c810700007e80c04a14200c0e0050300620000d41300d948581e8040b0041c4115080b00d581803003050380300c0f8141c1055290109040b4401d4000b40300c200d0b2482c2908071820420780d2032860588040c0401d2041d0b040551101d54802d5809501 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 797064946 1250 797063696 797063789
    0x150c1403040b180913110d0f0f030f0f051309020f041d0121120f12060b03090106320105090607060506090702030309030a110f1c030f06 60
    0xd004182c0c1c46042058081c810f40c9201c10840c0c0ba01c9209075510218034490030300c2e06849641d40103426810075540a01c2451060200404e2240e0801d032400f245a1010411080580d9802c016000e074680000031000a00d000c0d40544144d4410001e80710202c008070748201800782844521000394024111001e0003030424440081c040c4108070000e4090b40800c000007030654140080c4100505680f00e910445a80e007124603000a00d4650154145240c0c6280811000c01410030458038151040120003180b41015000b081c07601d240c80045010b042035000820160b99241d880404a4607820251001040d0b0204019149030310700200c0100564140340143c6032041c1c5c280069211f412040c402d641c00355861042021038180030b000b01d904030300c91380000c500354036002415594a11440b441c0350204204bc0e913040046100c10012072459042c114140c5210024801c5e0035058905400d220100203401c0c8084883d000303040388110002d035125060404482c07042030036404103039903882054964044c1c210f0b65 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 797066196 1250 797064946 797064959
    0xc0d0f080a090f05060901080a02031003062904060e0403050c12030c1903060503061b0c010606180603060617041509060c03060902040f0e060307030803090115150c140304 75
    0xa2801e02141e0300c0c0c41e10381504112106000c80c060350005070250404000903502680c10030000c0b54020b003c50720248e0350f41d803210080740700d0100f5a4001800a0708000c1c208006003041c070b14203e2102c607441f500740400400c00e400c1000b41c0780b05e84a0004070102c0070000c140403e01c035000801101d0381ca1400c907118855a05c1501005900c2207801168103800801c2a040035032070040c00d43c400242e02d281c01d1016500f8080040d40b21385000e0001c10548500300c40c20140341010f88107681102d0540c500803c8510341e940d80150046444d00c0e801031003c1c0a00c1d03000304409001c0d22508043d15101d60700d44151000081c41c5008003130b40039102340e401c500f0b14040340129088500500382c88074407941300400c0342426440040c040d10302c44c0d08400f03d00c44c0103110900c6180c80c0201e50204445d680742031486140c03200d4002c281001c0361500003521001e000400c110941e03205404c001981000c01d40303d0980076035218400041004410316120000320160302070380110303500c1e090401c00b5150900551f49820350312b44 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 797067446 1250 797066196 797066213
    0xc0c0b0a05070b090604020906010206040b1f03020a12020405060312090f012a0203101103060d2103020712030203010602100c031803020f060f06010207060c0c050607050f07050f01020c0d0f 83
    0x111182c2e04c0703910050800c801c601786003024a402c424217000500007801c0c260f03160008560010400058a03406501c028800500c40c000c5000a44d005400c4500172a00d850f90080603014000044e4011820f000200b1024200003984c2c00c000c810340d1003114100074002040010440b841408181004148031094407051442081160243c80c0c0045c50300307401c0300506c14582071454190160b60300d14903107039a0304449408401102d5001c00100c82c20b148a203400d14001e09032034120800480801018031741e00b056580c0540c020a101030040d64802d04056041004030180d11003400351800503013090100d080d0640840e0001c1000c0360040c00d01080320340d50071000c11780d07401c0991800c0c0c00503413000940c031511300010700140381c1125600b40e4054851034007c001030754460f0284242010000324980001c1806980444a4050100282516642c4503103040a60b510801c000a8010318010302c800002d4a150034100c00705841d4045e0050100502480204003008000c02c4c401d89080000703c101d040080d6251 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 797068696 1250 797067446 797067451
    0x3060d02040501062003041d09071d01031104020901090902070f0b0a020d0f050c0a08070e0a0303050403110a0e0a090203010b030a03020a03110726010b1003050a0c0c0c0b0a05070b 79
    0xd44e40c0301940410320b00c0c000003d505c2903803c880282c000b0402071041001c0c0c400e000025460702048050543c542c2d062207464220298050f078030410300c91075101d4550407031200717281c1240d0180c0300f0000b410cd44d00d000c1004a1041075038190109801c003404006d030f19903503005084518058442d0400042058481d40c4141004a844425044e03001424228a81c464828000340b0120928108a246000228085184030b2010310905102708040024141d038400c80300d0028082c006050404010741d03924024001c0d8106000840d40501c04140700c02c00c0c0d041c0254485c00321810f181542d1a00d80707800b03240500406070228166091354170b0318001c5203951001c003e0384118605c81d038001d05c6941d003182801030016401180060454006803000c205805a5014802c1d9000580170601e100c030901c40080360040290695860704001111201e590301c2e41c155120f1803041c200d03504203010800c1108c000b00d46a64054400905160040c107060110390200f8004c0c4c8412511400c1403854443c082c0c44055175403804 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 797069946 1250 797068696 797068709
    0x3190e0a060510140f0d1b06020c01030c0314182a1f020a030f11060421050901090902070309030b010e0901140603030a030c0504120804080607020f060c03060d02040501 74
    0x9030b2042c0800b00b05940c08641c0100704580c40780b0f00400346080044e00c0032801d151100e100304c40032410102806042d10090300354141052061482c90744d00c0d04042e45880c42154110302092900080c440c446009000340710051a002d140d001140c0d80380c441020952424546400403031044081c0c002151480308400d02ca61050540d10302e40080204041010000240007003448503120065000c100c2d6400003803400c12640c1c5801c0220030240e64420494041e1140040c40e0000e101b50300c244400d02c807040e22115080c108003120380000782d414101c00e80392131181c0307010140011404c100c10482d40340181e010302441d6110307150511000c0e40e662540c4601903001e0700400141c90100b82072002083c0248a170fa100600c108a111505161010000e0f49174060100070009050315042c410b10309030b1199003160040d204003261401704a499061071101078015000e07001da140b240030045512540001440a86010b600303008003200d943c0c84035294500d81010740241d805c20b034600395505c01655a1b0180c24083c100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 797071196 1250 797069946 797069951
    0x7050c011a03010608070803070821070305090c01090812031e042307180e0106030605100806060904051e0a021503090c09060915030f030301030b06100503010b03190e0a06 75
    0x80c070000305421a102980480c08070f500c888000c01001c0c1c2e01000350f840d03194003c0400358440c09071950f91003090284840b02d4288a0180c801c0240711900f40e803040d805811294122000020300c6070066903040d849000b1482e40358014030200c1402e1a0610007554024418000c00321000880d104144031008295421206582c980903102160f00c0c101001440010107403006007800381c5014641c0d00103034078001100311695240c0d503030300350156425042100210b9004004100600d0040e40c48a8005224041e41a80e2702501c40440c00502d0580b1140380920f410801070103e40c0e82006561801d0310750b6200100040c0980220000580d840380264410805034007540c650300d246c01210f040c01d00d203601003402d1080c075015041c80841d40310b402c1d40a0f40b05400f002c0c44903069038080000303481e0091200241c015880000300103c00c010280c1d059600458064030030000700140080d040d11a40400d000d90b21003c3e03018000120300b09155008044183d84401d00042c0c0102082980c038103000d0341107016588680c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 797072446 1250 797071196 797071241
    0xf1e030d180603090f050a0809040c09053312011a03040507060e030316110906060c0c24070b01050f0a0302090a020a1709010f050a0b100807050c01 65
    0x1014400c410031440c0300e24004442601d0900c1c0350224001501550303040503a166264010003600c190740741072540d0004101c0f441d41d112860002d1495012121540c0101c0c280b16204405071f0140c9a0f0509a03a4020a800413540c0c081c2c85401c00b04000c144148400c0084030b03000e8110b019039100800e070054140c0d01d0508558189114105412440c81d0041c28542e0108200800728101095003401d490203407905040000c0040d0000c1e155004011000a00c6028040504200826505c0d810754560090b20003c5e507542e5114200072160059601e0070380e4a40190182201e00d03d002044030711241030082c2c048410282d9504801d00d1500460402c0b00c5260500f0018410351914150b841c907200c80481c0c1d0052042e04643c049101c541014001006203a0003041c00c0301114042c4040012002d420405130020346003030704416010748041e0000241652401010400610607801802034003000070b0007142080c01d44003400c03a8010701c000c1c0340c070701009400c0c071002c60194020f000d00c3c0c9540034501d4603841c294 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 797073696 1250 797072446 797072449
    0x30313050109120f021b2d0301020a11060f010609090908071e0203120418020309030c0f0a03080a060b030c07150f0b150a090513110a0c03201b0f1e 65
    0x1491094012007051445c07000c81e0555645031030354440711021010300c0c1601341049141460b0b80c110987e01d40e905500205132403540550081e20103505020443c129441038035a5010340b1082c090a00400000541542c8144000c00c41a00036114181c0714005003803400c00c0a440c1c0400d00034051000c2c002d00c410002d42201946002c1100c0340301401040800b03407404c1e01d068a45a04540c20340110800ea80d004000238000100610a0390301052209042e100c00344100c1040300c0d11303010b12074802c03404a180c2e10041001660540304400c1074400f15042e80d850350b11000c0c0125495000702d401240e031064a4032659864101070700860316400e900b9000840c0c6811711400b00104140d480700700ca030040c50180188010598882c1030b600460720f0540e000f03200b008845e100c5402a0110042c0419000c100040240c1042d520052130f9510314041c0c3e4a100c1d0080c114554500281600710181555501000c08200c0706d401d1070781c146000d0440100440c4d00745050b140451050200c402c00300160240c0c14001c3d000f035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 797074946 1250 797073696 797073703
    0x1020c100e1008150a060e0d06060506070308041a0108100b0319060614030303150409020d06060f15020c0a05100302120a05160f020a030c2405060a06050a02030313050109120f02 78
    0x38060417280e1341006410003000500c01179500d000540309070509640001030010f540e0000024040c040d1000d9669011ba00700507042140c2907504481c8884071928641d0840315900195068a0f80a8003400c00450601505400340501842480c0d0500401c0706818014403152680340d0420b200b9a00410482e00c0c00b03050154001621802034040e8200300304204455040c3c101035820504200c900140300401800415001140e50b2001401580b820501040c40003400d082e010866030074500c0d4440740b48440600300d07140c42100c2080354000491880901841c0b504402100c45081e21b40307801130810841000801132040162212000c141e03841090115100c03d003c081414190281440200f5003c8143c0082d582c205400c8003400f04854480d25404105550511854100f080705010364100c0602c65800c004040603501d05104110301c401c00200c0c540200103440d070000c2c1c0c81c4c01560440e035030b8140034084808200301c1103d0035583c42b1948000035000e0201c01d9110191591944031144e05820041e14 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 797076196 1250 797074946 797074981
    0xd0323160f0c110d210306031e050d211e0b04020c06070c03050913050708060103051501031109060307050a030501050a03200a08010518071401020c100e1008 69
    0x100b202c050750803030101c0c049410300c0c41d4800054030843d1302c0b64420304005901d158001e881e25150080e05100e038a00f681c0c10b03008101524004c000c2e202011003221200d90030341d1900140103040741c212000c070713405250044070044401c002900d0000c1c0c0501a071048401154981205010030000d080804400044580300c0c00d800c03041c040d03d003141380540d01603196940da0b4004020000b000382c05d00c0c05500700b52140042e25201c2e14050076444408402000b400007904040304c4400c0050810800030b402588280692402405604000c0c11018002001180a481242c0c03040d503074520100910380d03141e103c030300056120740040c0c0e5680341c488006120040590b030040c0e001510564801d0000d0000c02c9070903404280d01d030112844041a8a034400100717203407030420b50240714107511781010004420360746c07107020030b2101c00c2a007501c0200703803600c01c0010707021030300309682d40103a11140c1c1480080c242134103c018140c0c41401d05903180c0b1034080024030b139000c00000000008032414203225103030040004000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 797077446 1250 797076196 797076227
    0x40603021e09011707030b0604030809100206042f06120702071e051020030a201213091109010f031a041d060108010c1b03020d032316 59
    0x602c2d100c0c1100000b44104024610110404030b0346021401540c0298408100c0400183c050b039204c2e80e032401c0826490f041803840b64000d13100030426041d414800305015205507803110894007034034141542014500c40c4c49180946400418651450035075600000d81294650344480203102c3c904803c00901b080500e1f03100101c0c0300b0454440b500d03102189089401131b0f5000791090141c1c424844801c46d4a0600e240400704010140d03030702c2c600143c030044020300d10445291070726018001000300d4048501e444174003102058000d42011a014903004008160410850081c3c80f81580ca075201d80040b541c0360a001080c1807000603505016503040b0b10028207511090500300910f50950038003071905882100340d24450350343e07000200c3c0b14030740740c1c0300c01c406102019084a915685964585e8020544120b00b040030070907034100d0a12104046510404195042e8081c0000c550742d2041075000d0034a41480328800d412600400719219111040c4504c10f511030102403221031b10403d806001c40c0a03180510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 797078696 1250 797077446 797077507
    0x10812030415020307050d14150d0b06040209030c1008041a010602191b030b18010506100809071205030a08010605090604030201140d05040c080f0c0d0b0601020f0304060302 76
    0x4004103001d8403900d80e00031032000000da40d917a40c0040c1141d4601c141d281c2c50320864a01960380700c00e020b000c0c110381d125600f5031040d11055180c6070100855804c22040041c43d1f0700750540011042c0c20113801418141e000901150604044c3e030000800d030b548205441400030745207070200001c0c06541140c8403031131100c0d45559011355041441c025100e82c075103190201e01c40940100c030300800078504111651400c0e0004031503007a686074036009990400c255115001c024101440508860042c8651030180000424003412005190000d40e50104c0082502030540960500005d00b1003401200413610351103a0f000d076030364200400c4c0141c041001038101c1c1d003c205c4240841c009035110311040b14242d03a02403c2210003100c03103146480c3c00f40304d00d84403400010304100138401003140c000e18050581d4002ca0913142103080100ea00c0303a036415500170030f6030300c01e5002c5050b6011800945001d0b40151040c419a054010400c0031145150301c943d10610009600240805441090325903942e0f81c1050301112 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 797079946 1250 797078696 797078701
    0x15010608040b0414070506040f090b120a021003091703010914101a041502030403020310053309090c1206040b040201030c0915050d060503012a20010501081203 70
    0x2440c544003801000284441c00420f02c0503140070041100c45c1c0185001060b0750b542e00c0d02c0d642c49504041c85803260044d15800c4c5590b00e03141e132030880719413010b1841000003032103601259020005580d04d001000b0701455500c0c4914804280e40d10340701d0032445038125a90381c1e40d502d499011001c071040311059901d805006c10070711803200c2c441100c107000c8a03081450141000045000c121081c881e079413103142030716100400403121503008070140003224003c40580d544610100b1840c41034680407121000c04100700d1043c070303021a580c00050442072401e010606808042000801c4c014202500e12070402c0d40890150001c51074242e61b9054010801d90103402d03103080c6a81c03490408040070300009d041c035450b03413600c101c1248241a144c0041c2009612101c20125841e00684660300041c0e9441108d400e1440118441c241406100c83c1400090f0382e200c2c0214061502d075030710302928108141048580031003081d1108900e0305110500b2001c5000103525450079441c0c030301d065642c6103440c9210304207008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 797081196 1250 797079946 797079953
    0xb0403080711061512060a150506031b0a030204080a05100f090305090d061404030509030d0806090a0c050f04090617010c02191a040b04050606090115050903070302121501060804 78
    0x40f0903820a82c03080140080070f00010010b5081c42e150500070f0319600c40c200404c00c000c3c0f5160004117a00c403940445145a5031100d080c04038621007155100c0361280e21103000c40c00030324204010041c00b4020b00e001818651a1900182800c2c1140403d49180e84408010304c894800c61203400c140384500ca00810200c486a603011b4a680242d0507420302c03804507201070800b404000d8000015504001c822060207140500d00a002508410300d00c5010703210b40c450004115002c3c082c1c5c84d003d420000e04442d116590000810050901031600004100051015480a205400140000c2c3c0038803440400d0007400c041200304140300c41040300000e44e0400140290540e0089803091f41c1e450b1680e001c1c0404401e07818280501828401984500d2109004000038080004100c0e40510721420550f441a1140d40c03c11098540038042d080411400c00c030003440e5280244002c1000c188040c013a2605d1943c0c0b9000180c850340414007030750b6182c108401c106805000096042e01401e50b600303080c0c4507828a600c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 797082446 1250 797081196 797081203
    0x207060e01030b120304060203030f0705070b0414010e0105090318060a05030c07050c060d0f0506010807020709090311010603081902010917030a0209041a0102071215180f0b0403080711 81
    0xc2030103041c5603035020181c0c126103401018020b0854101c00b02c80d0b95036500c8000940c3c0780d0007281d540500980074030201c2d0005219000b00ca08660300284095510345803529004848604030341031140566131b41d07188240e240828001d403403041e42041d02a45e00c40f8214a03861481c0704030700403028070031002045040f07007150b00401a00c0e013048070256411f4030754040b4502075252201e40880590310420204003030b00f145687d90807800e02c010405200f4040e80e104d4000558000d0b400782e503400e016800245040c0035901942c0e10043c0d419001e85030030344004012640d80340c00c5420581040e60030600c0060003080000c4050340e000b40050003803000704009401c5032100c00b8000d4545140100f000000000300c6c0c0c0590703054043c0d8003c900000c0080194110003400072100106e85407009015003e0b140000624440e5600e5054060b504038081a62040320362a140000309443c030b03c0070410700005900031005c10503020801283e64480d801c03070822401c003800c02921103c001080542042202a14842d401c903010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 797083696 1250 797082446 797082467
    0x1d0109052e06020f071805070c050601081f0b030a1e0b18060c030c1e040b030a0504140a05030906090103060b04060215101d04060b0d0605150906100807020a06061d07020706 76
    0x151000030b0548c50385c200407101801e408c113000e809846060004030700b00b0004036056140c0c04070803000d001d001040395a0a07041d01c0383c0940203945900500f800c4000304010b07082240d9103107694035060100045640c1d41110241003982c400315542000e00c4444a0683c08000280e0032040103401c450035454004900443c034480c0d181444071700c03a0903844005035895100107030307006485001011901da00e441c030001d40041c801101e069441450b10f8210200c54000030400003032480d00f140185140c03c0c074800a0020aa1045101a04169481200080a058460250001d0800340c1d0182c150203a100480c5022000050080218105c10000030030805c00301a5803200e1b2031041d00084495580c0d1420324030000d1200700020382d00805105402ea08100c115480144240301c030201e00304802c0400400c1c8910b0307030001c840a503040710f425135042c8a05400b40b02c2c1c01e0b86c8208284103c0388500b40994525094454580c00b99400240c0300c0340d200b440000c01c0b00019405141813004010103490540010200e5940 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 797084946 1250 797083696 797083739
    0x6050a0e0102040317131a07020a0e07050414060c01050705120f0105060406080907090213060224011e03050a1103010c181e0f0602161d0109052e06020f07 68
    0x6e00081d07100c010321100c3c0007007031280c1c00c9541c6c220b041c121010056129070000c070320440d929840401c0042d48054464001d00301c9581d441d0a003403c18201c03403140440f07400003035400b490520104045e09002d000e0345120b5946c650343c130354071603e028030314001c1048044c1c4695400c1310042c00502c180c5d140c940a550032201545055401c3c0d88640c213800f414900140c02c0a0782d142e0001030200c43c10f07034071040e00d40204e0303001d5401c071a00100f4614032580c0f01446103610121100243c03004101c10220801c42c6885850300309070b107445480d07403a540c492901c5010f1a04a41c0000105495181890f00b803044d0098031035141040c8000c0003815000030140d862a02503d03c00050418240401072034055030710001c2c28900003020480c9440e104040e40c0c800c49141d400221034000369001c9125100c0504180c2646a045990801c80c2d0a000145000c0c0c0401000000007004240455034102c0e20094980001440321410f400310350b050013002400c0031031030440302c0e00e0f90780300b400100500c245420115049410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 797086196 1250 797084946 797084993
    0x50909101d0c2710050405012a0201030902010909020703030b09130f080a0311160b01120c0902092205090106050319060b0d02030604080405030c010c1214041206050a0e01020403 78
    0x80c4030f00f543e20700001e5800980c2000b140d815080d00c0316000030040043d14002d80702d12a01151152003460310095510461004c005d450328401b006501941101008920504100524503242d248003800c80c1c100f5081503000a0b1104001101400d280350015080004180300795000300c041d80398100e6030741d0061801041c8100c002a07025055120fa8000e0b81e8000000700355940d00c1e210304000322240314103071074280e0b2501c0042000180313018400c6242902d29078010720540070145007540b0000290003800d00660001c01804084000c0c680b805100e031b406040322180005c580c1419500b003800c4444603004ac2e4040e80c400c0c29041c10a110551141006507400240845c801400f031010800d003000103900250148504e105000c10002c40c2c10160040e19000c0e812240600124801141c0c1540c988a0103056499405615003e41d442142112110f05022544910740350b030324504034480d044140c5080e61410b1b540c0060254094407400b6035000325506800035800d090964407a040541000c165007603180c907 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 797087446 1250 797086196 797086237
    0x3110a0f110c1005030a14040b16030b0418140705060f0f0403021503010e1006050307080a0e0f030903060a0501051503150d0c0e071701090c050909101d0c 68
    0x160410204008990141c8100f611030000d060103462900140e42504000c0d042c4401110142000c590491140b0340254820070035480f00d8048003218031959180008040d200c03841070180e9144e5019403056002d0054030b0040703c281ea03051480140d4545002e410a03500110300030022583c885041c1c1c2c040e0105d088a155a859404010541c2445254402034008102061103468039942c03001850407540d41032560f01050b914900c81008850090103200045035050000ca40703682c0c03040340510790081c8082400280c0001880d8810b280c85401481c007140c503840001e000356075090038030120350020301c288414001541000d000688949040181e2a1100f60201c00101c103a000380d0409a26903e02914000900c1e10b030382082c00484440c2d000e08440b008080303012580507032190004c01c0001385030000c01c81035a420101134002038a08103003110100002440800306643c0d41441481c0140d02e5120032001061902400d400501da01c2d12006440303000d80c3e41002000348491007251101c0700d02d04807810824 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 797088696 1250 797087446 797087477
    0x10515012a06050103050d02070b12060418061e1506030207051e01091e02012312010b040f061103030121061e0b03012904020c0d090603110a0f 63
    0x100e01407042001045001c002035018450207903c842c1c1aa801001600e1200e9601c0c0400d9030794540c1441400050344040005410004820700500d8020000a0010807403440780f01c030400540d920040c1c141d41c21583d4031510f41d443c04040c400141101c1e083d00052007426003030070340d2002030001c034401c0100303168000401d0820848180181120035240101410721500d076001014002d280d129000c580890014042c08180410308052013113040d4140e5402c2010462503680307000c08115842560518002400000701c0c0030b594203d034901902845e5982c90f02d031890b10406c402c01595030b0340003000340044899030000105000c42102c0c107613410140e0030f0b40180c1040ba1982c41c0d40046044c0508032900d02405414124020440b04c104103500800a20460705040d00309401ca031a00540340040e002c42c00000100da4500f01d074440031480000b0401170505514408090400c81c2c1c441821002441419051082680522411900c104819200ba04220780d040015100300d0000c100d540501011980c01401c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 797089946 1250 797088696 797088737
    0x908010e0a0825050106062a060c05040902070f0501060f0302030a0605070504050402070602090406170a060b0310020301030f03171b2212150c08060613240f0201051501 74
    0x10115185603042c03c00c0c10b581045802843c0d00d018a07000250020341c0d10111180b01c0c40f02c181d002c442c600340c008046040e5640c0c8001065500d8048050110a02000400742618030280048600580004002415518140742100c0d1107400881c510041d010081c4056240055011012640000006459121034405441e107020b030350f20582d402400012800d0401c84250080c1218036070640d0184485a2540d44414000380312144401c1c49601401419000c500160400c805000018060304c18800380f01300e04000303a170b009820540341c04514003818401c150340100c002c0e005003004200c031801c0741848002c0d801c0c0918040029225803002046505490390701e0307900343c0c0b49000c01420340c0000ca03680300c1d8041c00300792080301c05541c1c82c000a410242016200d000350070307140d040f85c0d5071040c103a0740b0076040000a800241401254265400c1c0100c0c08046503003100c0c1030b869040c1810b004030408110001c1055001103024011641440c0070f101050424180d01a8018401d0a041c1c260100030782c1e40020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 797091196 1250 797089946 797089987
    0x6210f020306010b0d0b030109020303400303090b0c03030708150405091b0301020705070501051c0c0818030c0715030207060203180f0a0b0601230304050d0908010e0a08 74
    0x107042c041e00000151220440008110034440704400f408403090b10400c060807200e4440c8041d4060b041002001003241180004800550520b000c12011a80183ca00f00e01a4a00da4500c00e07400d0010806109050b001a108001042a60241c03482c11249111881c0c99000c0a0a070406110400c0c002c140c0c100c8080507a8851603601800070065071070404402035468001e02c03640c8010400b24858444942018022205030a0300000104816841c04004650326804240c0020782a1036a4030030301680b040134001c0c0903050071a036880c00e8007401d152000400030251700c0844103080d4070800c2038411109020601c14100d52200f01002500b18880c2d170b046c0c0103441201c000030000c0b840002008000611031000b00707517a50b462422101c50442c0210381aa40e00d00018015244864a070000741c01580b10342c0d07828250907440d4520b40705400401c2d5603440590420f44049505070040c0d42ca008100d94440d04080c0100000c0000b4001c0c005460034140d110482075001401440300085c00c0350310380c0c007986074840 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 797092446 1250 797091196 797091199
    0x20609120a0f020103051e0f090a02180f0703090f0b1f0306050f06091909020a1208091504120b09011b0801090c0519120e060c09030106050406210f02 66
    0x1900000c242c40c00c480792000541c02280072910300000300345a80c105110b49425400100d0410070141c55403000322041e0480100189014400c00c0041c40c0140c4a179220003000359880740a080d090304002d214482030402c0146810200340c07906c850030020501c0c0c5201c240380e55403c50122841512a140890030f050400114070f2460a03a80d8030020400c803490740020b2281c0280c5022280c903031921005c101c510542a10500011181504e840c00327280c5195014801c80e520082c006520705580d0308482400601910080d15501c40100702e0307920314200022015000d14888104c249070030700740103000780041e1421001901c009290310004001e11401d61008d810550400000c01b81c490244000800001003400f510781810708015240715154024001d031401c20b000c0c4003007895a400340381780480340c3d036420700760302000207444502d81c0213201024007020703001c4c04641e82c13010f554a44100c185803d54002d5803007140102d02e00700c4108250345425402030300c00c0701c0c003000a489250403030801e0300c00f4800c2e03440040e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 797093696 1250 797092446 797092453
    0x1503040302071a070303061502070e090705031e06070c0302071503091e1505011d07120f0b191203200105090607121b050307030e010906020d0e07060c02060912 70
    0x400b41001101d004d01380881c03080da014042c954075482503107032110343d080c00400903070301c92007040c0111a030700d003681580301c09404202e0b18415541e1000034a07140d4800c08101c0b0f01c03e050100000e00080c148019a4442c0c03a0f828901d1b04650b260350002c3d91040b43d48a4844102c0380018400d034900c1c840d80007510203980180300a058220b0415070941d08032000e400c1240c0c02c0821001c889840200d42c042c1c981203d44607200902d000700410700d030075511000100305c10100031640103248072041c45031246030a01040074000281041401040c0045020901d40702030703091003043c20030090140306102203c2c3e0703070b03030f00d07140c00300c9003540b028040708002403012840300344e039420007040003031152002803424070444056072200200b884a000f46000c8420810b0507082400c45130240031080c90084005542000451030f001501e80350154440c1d003140c00030344d0200ca60603000200300703a11100300d02031001108524070150020b2441c001010b0955040078100034018080400c4142c5036541e103c2c41c00d6030a20340c110a6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 797094946 1250 797093696 797093729
    0x714030a111908060d0f0f1703040609020307061d040e0102070803011805060901082d010e150705120a0b01020703060c03020c1b101815110d0e150304030207 69
    0x403500c4181c00840c0b0500001c01c1000014424038200c200d916501c0d820454007001d160050b01c03107040f03034100d07400e09a407400f5004074000808070341c4400941c03040340500f00000b40841e05204050030b1403143d40c82001041500c81500703089854810040e00d002900b00c5001548030ba088801c18064012450702902116000c17000041d000d600c3d05460032440c01c000720400c031075035628040011020080c01004a2540650440c01c0b20300f001400a0801110103070440a50242911915013580c0b400c480d4200690004004042030a81805100f074100b00c09040150915011981b540d10841000709902c900c140c40f83c10440040c0d00911003103001d1034001d1028808184002d00203000f0b54054445035056102d2801031000c000e82210303030400007000044ca10034032024001000c0342c1d10005200100c0320007900c0b01c0c00046180101150b00c5403c81941c580a141e541000c0b0504e0a100da02d0301428203120894060b401665546002e209500000420700d944946483c01d04a140c05043d8100702d1625403004078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 797096196 1250 797094946 797094967
    0x20f090f0a0923011e0e070c0c120212030903151009020a0c02031603030e041d0d0215070c05070501080c09030d090f0b040f0b070f1703010504050f0714030a11 70
    0x1010a000d500c0c0b2001054145d91342c0c801440802550140c0358104454680c040c0310b4600448111070b0000014900502a5026901d44940014443c1d0103060142680e2103200b0450800040c1507106102c1c40300514100510080800d89941c4810940c50401e01080e0009980b13506840c0840c1c003031300400030b046407200c0912002800c12442c11405a110303109011211041020158001c020703243c2c583e862500e110707508820b0002801c5084084071000d00c030b894030317941161810083c481e00b21810390300a200c42001c0e00300710b01065602404020070008486682e81c0494000101441142e10a107490211503460490001c2c59000c0c001c0c8140d8580116004d558040b1b60100007002074511904800c3d0081d40e40304195441d6220b80e00c00c084040030000c008214078900800901407250040303a084e032181a580d0b4a8110407a00200c01c0300001c1004801480581454440d1035071140d442d4076900f8030750600c0d00002d844801c07100607042c1250070000029a02013003a400a89980d01c0d03030000c403500c0ea10070780b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 797097446 1250 797096196 797096231
    0x61c061401050619030e010e120403021206091b120d0c0203010e0c090a0209060c0601031a06040209030a120e18010305190312020702010302090a090506040f020f090f0a09 75
    0x400a5911100d10000031030146412400c494403205803206040400f0784458050f0040e00280380301102c69561400b00403101c110520103016440c0d0001e44c803030340e620305520402c038540d1203500c4500c10ba42e12030030402c40c0d200d07030008801d0b4040c108020302503000805070002900030309507201402200d004039031810b03060580000c2c070b1901480c802c034002c1c881440100b03c0e80341c0e1043d185086642c0128000c004c00c0b00241c80b40e00900724240b0103072a1a00c0c04500480f241c1c9802c000b0713841103500564620102400c200c01489c50f54105000b220158908014403000a940d100d000320041c00d4240c40c1381300120014001d90a440018102400f1982140c5241944a4103100240b000380d0384c038040c04000100e45212840103106007581502c51011270b100c40c000860094020000c12414154204500c072030b940d5440c11f03420018003200174089031615040d0280010355051200c0c0e64a02da0040c401e9a80c0914244207940070307401c00752210f50301b00c03201070000303030f0300c152140e010b00f442500e813038154407015400c02c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 797098696 1250 797097446 797097461
    0xe0d060624020102090a030b1801020c1c050f030103021e13090c1208120702070812040312082e09020d0b100c08030103140f070e011d0f010905061c06 66
    0x91588010807088407000ea00f40e11500000640c000f4111100f8000694102c0c060303508040c251289400c2c443c00d2a01035401caa00c4a800d255a55000900c2c000761920080c07580c03980050b40785811800c148070542040034600040c00000d119500d020101c0620404501180e00c5904e0020300e103501ea0078848103000001e000c0c0c48003e4034402151840451001088402201c0300c540c0304200e1841c2c40c4507030800e03000207000a0901411401080b80c0041c100300b0402c030100200e02203000d090b50325441c1d483c0810140e100320002405000a410801c05031030055903005928280b2031071326104e440c282d0084a507008001d904081e903002c0c0b0200303a110760204c655000c02c12400b0181e881032010400b80c0019155103240c224001c08041d001c200620020300212850921303240c1c00c2048817000d0400c0c4003d0342c10f088043e0001d505500324071004200c9281e134106803404c140106800c02c141760600c00c20301c031104401401001d440035210700c045901c07520f500e10790100903d5101040c903e045030600e060006131510 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 797099946 1250 797098696 797098739
    0xf05010906061106061318050a052b0f1110060906290703052526040b0706050601050f0d020408060114030a0b0403050f0f0309070902040b03070e0d0606 67
    0xa41c124804080300004c1540c0a210010403e03c894840c4034000b034098400b001c00e07002c0224040c1000d0001074005c2001465103480307180501403550348080e2070300759120a0401c818002a4002c01c0034007003900058a0781c1d201c6d4981c54007102082c80e001800e0702d0700608100b9207040d18a004800207001040340e11600550b40c0790343d40e4075408a07142c68082d550000d242d22403109502c0421502c0d0019000b2401814003586c1841e41c407001607d012105055101c0c000c20540d24020060040311102080501a00c03480343c0c2c1540090801e0304084115140e270084480041c05a43d4490100d080385e0301400a54211482c5601201d035502400e02000d0041c1d0407a115411081c451107001081c0440b4400081003940c001070000c108841c07964035466007004000d0420382c10700504101501c4070380100c00091050119034103080d50b6a0a00c01c60180c0703084002d1784600c114600c1400240035440610084980008181c80d0103001e94000400140c0c41552a100c0202141c2c070702200016a041c0090414049111 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 797101196 1250 797099946 797099957
    0x12020111162006120910020d0c021621060609090305120105090c071514160813321501050316050a09020a021c020c031c0813020102010f0501090606 65
    0x3000031960b030303001c2d180107a15030312040c00d1081c002d808211310744296001c0e040200f100d01d03c1ca01030212408a80c068100c51844507210b0b15280e040c0d6404011320480954110680b1103554a03013501c004842ca443d0a01c103403550315981c4100180301e0039403c490060024903d0401090790300d0310f00034089a1040e5000382009080b0800050f1a25006442c070b4450810381481c04c0c50840c1a982e80100da44003140464020355441407500f5603e45071001e42c030321030400403216403d00c1c50000380103400740c0130040035007182e40903400c00e1800003080c00011041090302c00390310402c40b682c10030300800110800d0349505640d20540c80c0003152410380101140c101d030310070b5080d580c000700031912044000d0894081c164000c040c500c42000840d52075402806120f50502c10b69001601d801c2d4114185c650b8425600016030110f06030407007615003031050310f0001001d201c00e00080da09150000d04803800040c403124050034075010480659000303400c007074bd2001c009076040000f583c40381c040b24005c00f0140902000210b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 797102446 1250 797101196 797101223
    0xf01031a0c041502100f0e15061c0302070b0f03150108070207031e0602280513120c0b1317010e0604020607030c1a0601030f0b0d1202011116 62
    0x35031101610302450350306822520300b5042990200812240440d060114410310307810100d4040ca5100d00304d90a40889004640c82500f031401503c0e0001868140f103503640c84400303000840e5200d410011508005082c3d4075035070003403070070140d0034000d0a91001c0391944001440f40310000c0c48100851060704000e024148110850004642000f000c98500001d40e000c0a4280080303148842d0308000216450440c15141a1550340d401c1603170026603280e502c94855154041c549055206025002a040c1c0b600a003030101d01c20120181c1101481020180380c1c600d402c840510456070b80c00d9001c0e1501c0c42e040d075540e00b04c0307000c210351506441c4540c1043c01c80d0940e01c281c070b0002c103010f9a00c0d40c014074001440552a0354007080000e130300100c0118248403580715002d000940b900840150307640e044c7c03d52500d0385004800942600c04108a0082c00e92810042c48049d64681680c2c0e01d0b09a002034410840942d0640241c1c010002540098510200429448241e07aa245852111944601c04505e450b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 797103696 1250 797102446 797102483
    0x20f031b0901120201170c0c0d0207051c031e051b030304024f18030206060405040f060207020414090c01090909050303060616150204031e080414040906050f0103 71
    0x2043c61100007800185081c0074001d17414040362004c1e81010f002130800b440e1000407050f0a00e051860034001001d40c005043c200281c2c80c2a40c0805038400300620800e4904d8100c1d41d00801403a06040141082e664882d5100440b42c42203080d030307040744001a054002014003a840503500d41084400300d1084000040120f60f200811100115030304285d4186210080c0600f0301e4040c26440e0790300109040c40707802e00c40102c0c2441e03001d1040b542e02501603404008040703040081c14410010309aa010301d040c803091100040e0760224000441c0e4100c6001a110080c5100090103400e000d00707040102c80c150000d20052010200360b650745c2c101c0988400b4201959000300e1030036540c61440243c0726800601c000b4590341040c90062140001010b6007400419103a03a0360303000442480380c0c0391815580840d050081060307041102700c0320000206200305010f04c955808405100e0707400348440a6031146090000c0f0f0312160002c01d050b90780401c0a01117171514405100343c000d0244000e0b510754207050880c080c1c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 797104946 1250 797103696 797103719
    0xa0f080702131406010e180a02040807060203030402030c01320301090f0e070504090507121a0c0c1f0e0f0109030f08040b01030206030402060f03073216020f031b0901 73
    0x801070f40303100c0d000ea0703d41c0c00540310400407001141d0402401115020411501601240b003506040c40050311581008246483c1450903041041554410420700c0056500084c00300390648091034020b121040710301e50300b0741c80c1860782d01080c100f0f2013030b920700d40010445d40050b5042e07801402c41005505100380308001507038809014804c0c142c1169009010608064002a42080c001c4e0115018195940c054080c614486501510007481c02132900c590300c99000382054000c14054a103031b0400400088868a40710b001c0d10302e05410300030a04d1034007151100d4002890100e442c400792461038190744103243c084c01d80040d0480c0022107800c03403449183e005210441c06190000260718090b0b08541c207000b600d40c006031061340d00130020302124099113003020003148a1002039980a80540b40c03445001c00300d11a024100b83c42c480e00d841a02c003000000070903604e001040041560072001d4038004109210700500006425005046000801203040e00e00101061000c1e60b054034240c2e82c9131818078a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 797106196 1250 797104946 797104961
    0x90a050d0221090616030216150f0e0f040914010c09032102100606021f02180f0f1009140609100f0e09100501020f060f180a0f08070213 60
    0x812920400c0c03010b224240040604892107010300b04070b142a07890305821407065011182100184e00001e0100c1e8100040701c2c0550080004a540d00c55501d0240f4000d030201000c04400c2c2c0030440301e121810308559480001e021000d0024000b08072460f101d00303003070710040601110901d256003880107050f190382c4903020450861f9000040e4048d80002c034120039180540e6444400e0851040c000241e240010920642d001010745800074144180510000341107442405c0506407650b00c18070010381b40c0c0f5a180710b0380d400110304070b8004001c9840321000130f06019124000c9a04268404103440000350015181c406483c070404003d11061603641c100440c0380f03e0690001d401078560100e01407064000c00203144040e945040c1060340b410b240000c14811507003114144401d641150b803c0183e0b580500251404581400c05040359182c0070b4103d06918402601503100e01d01681d6403002c0a000500c500251030303911030b00907201d0480340d042592a54120741e000703910458000048121700c42c800d02c25802c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 797107446 1250 797106196 797106223
    0x2006041106071a0a1a0108220311010203271207030f03020d0905010609180506070e0a03150504020f01020a0507051201090c080d020c030708070b1e03090a050d02 71
    0x221600c04540c248041600070501c100c50085880510b480c103140164201482980a0a000a40030940e00344070941d0640a10440b030601481106004045c04090701d0321000990342d21800178000c540c0d1a0858002d1110030301403920b5440881031104288191030152401d43c3d02d840c5124424034409510303074881615080380c01503410b04000d5000024010350000c0c00c28221428018200b20740302e4289003d071402103c0444d40c03079658001c1808440319034840c0c1403610701050800070f04203465170f60340e41e540c03840600441c06001500f40c41e081981c2d916a205005150302025008900940c0c1000d40c2c098601610224440c4008080d0940d0315403000450304203098000005201c040d14105c14800d45101c4601d61100f29500e0b5002c510100340f01180356001000448014a20b11901280081c10401083d19003442500200303020441c0f54000100401a44e2018500b29958440d02c481c0e041c80d042e80c00300c80d0303001020200c10002201004142180032900580035030302d4840c4032001c100d0b11064403a8a00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 797108696 1250 797107446 797107463
    0x3060c020d02030307120207050319030f060b0403110303071b0609120506060907021e060a0f020403170d0209100203090a0f2d03020a0f090c0c02010f0f020a0b0106200604 75
    0x4130f08911900d4051b0310756001c03072030041ca04440d5480d00360666011802440312505107107440c0807450351600c1900e84501c54010b04000441c2064144078141c415448082c0c102040440c0182c0c4958003801240c203c998032200d000c40d1a5448007294103841c043d8400d08000c0b9942160000d00d10780c2094100202e9684034000d007465550b074408018110b003000d040031085120395256801d49034440500d4040090710000146160319100445006940294950212482c0184020000901040400b144041c13440340f103243c07201007003890300c0d000380071f00050950f112a030101c15000700c0c3d40100c020800300c0c6040d1400343c09561500030044004404c0d10035600702c04030002c5c0151540f81aa90407100d0581b58546d80b0700e8540d62a0000f44032460a6085829166a0704104100c1c03540c04e40705644580c402d82c144501501031039000603040c42d030b04500c2e10041c4900c2c290081815842405030030115940000c809070346507100c00c0c00910100300342d560048200c0880c800281c04403400242c0c01d00c80ca1303100008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 797109946 1250 797108696 797108701
    0x160b0426040608250203120112020d030c0f080f0715200702060d060b0405010f0e0a050105030a1b030507090801050f042402030a0b0406050409020109092c060103060c020d020303 78
    0x407180700714001e1030340e0502816480c002901484044d50480650503076030055440741c00c0040c0000b48070340107a100c07054060f80030682c2c000503210342c01030b5095560142060303003040130b43c0d040c000444c0c040b07520010060803000501100303009914015022150103001941c0609903006503d03811180181c2458102c002c1c1a0f91146244003920014008a0700c003074100350614580002a03029502c10340c000c0e0109982c007040600075540e0084030740900e91002c0c0f800031141c020042c04660000003e014090410200000081a01c1ca082d004500420440d0182034070145509800030f00820342624554005040c0c401c0010300010140030b080c2c02401e078071116994548032070341c6400c0b450400e0069404d041210740b4107559132919078400385118086200b40840c1620040f070402080b40e6098002c640320f02e26048080300503076840441502500d40f806c600080c503068040c500f0048951020410300454000300d0110303003611001c22228120f034400e076010b0100344034101081e0384801c040c500150040c2d005000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 797111196 1250 797109946 797109959
    0x1170a06050603100513030e0a0312050d020909090a031e140304021f050418110a030e0304051023030f0703021312120206060306090a0201110102160b042604 69
    0x29504a28010221000e2804c0d000800d010313200116008011011101030813018503801115604091508a40001d8144d0440e0f481002540110411804114001c100320b48140b000da03040781e0714190000c0202c4003c4c9010103103a035503050041402c800080b80b241041104c02102d0000c0e50643c0465103400e8001c01004034407c0f0306802c0100180da010f40f03020701840d14043da840001d41e1f00007950351b0300c1c1d5449080400c3e1100760040068203110740351610b0003001ca811050310541e0703220810340c9404914460134850040c51750189402c401d503c002c1c0e5040800a058101201070400c2c900a030810310807014451001049001c00c6031306000c400000380015010503c65401010400966420802c1d10703070300e883c49011081c84100c1c1c11500d07000c02c4910040702130303010404990304c140300710020150b0349011901507840d424801c000a05100307008000c01400d100030f4040e550380307162542e1b01c00d90702501403c101c100c01109890075510b5909045810701442545040548581c850b080d0740c1c2c0c2303050714204 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 797112446 1250 797111196 797111201
    0x306111b0d121e0515040207050a200906060a0c0605010b0a0e100e1c0602040611061807050111150a0204030c0605160b06242208100e030c0d0305070801170a06 70
    0xc0c445d44265851504941c00c6039540e02c064039206009100511b512009881d2182a0f40d0310312030240308201c0642401c2410756181508141c0c00310701036408940b6455001c03025217504040395402000141000700220310100a100507200071001035450151040c180070900c62007a4501140000203a5210000030f0142000d9491081d908001d540280c907a8449407525402c03a0885d8000c400080d001d03a00c00320b01120300304011604010401d8400004152000006540d50001c4c81580e062000520404400342024421400c440d0007001514080307183c00d40c3c5820080d802030200700c8400d0800b40011032230910074401d86400d01a0b007169000b41099544642140d410001c1c83d444d0710154024507120021f20380480e100b0721212600b01c2c036488400b00e607a00a070885644007945c3d03078617200410402100c1e43c0062105544002c50700300213180030030f01e9a100c2c11845440c420a080b441158041d80490354594095889006035659190385c0b83d0325400180031070544022105659803012020f54041050741d07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 797113696 1250 797112446 797112451
    0xa120e120c0405100e040f02120c01080402040e030423031c0207060c0c0302040903080a050a02091f02250914011215060513051e040209010306111b0d121e05 69
    0x4040c684c5905948075000c4900340300440c1d04640311030000e0105421410941c202000c079003c0c92010344010115800001d042d00c41c010030103482140ca03800402a100820302c21035026101071042400a41c1d841000b40d84601002290340f8000c0c801e80d0380410804600788540300d1007a51a902030003c0c0b516001045809048000f003d40760b0480d000300c0017005980d188a19914607209445004032450082c0c48401155001440d48134418010007121300389503076000510810280705550303500c000c07031302941c00c900c2c140c5840b08140c0c5441100c443e203802740000c022800e0440740b100300144140c0010144001c3d84101c00c0c41b410740448404440140001c80f001c140c10f01c04007082070009203481e50b90000030300443c1c104002c0000c0f06e6480c001d002c1e6249030350300b400b052103012180c8a0a80d06013a40450404034051102418042e5508004600181e00d101207030151048072640110a1008500d0143c48040303010000300401e001050569400415010b044d042144041d04107110154018202c005005d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 797114946 1250 797113696 797113711
    0xd090e070c1a1f1e0b0f0705030418050907060507030809150a0905060906040f0b15132403020603220c030503130617061c050a120e120c0405 62
    0x8000c1110304400b42941035807145155101d01d12880c3e020300440c404015031034008000d0240b680480d6401088003148040c1164100220b03a035a5500344e0a11620900545000900031301001030001225410f0740d8540002d4640e21030200020340340d04000e03980c0c400c3c051003900301040d000d110103008240503034520350740422074500744c500403a030252484a01c0c0108840040075a13981d00148828414104800b0307500c046003400800d10790505884c1c06001004020000700510303c05270016118001c0215080724500000e45085100d07020010490050041e00502602c07006151f120046c500c960800030401322500038100600d1506c03115900203100340c1d90b9580319000e000011005002075003040c003038402107000d64041c580701c50501c00c58019414065102804100e10542003100a800c10840c9582011040351720075100700926940002011185d0400341880c003905043d1030622540010039616910b00355582400c0c07503801002c103d0044001c80c481c0c1c0841e40a03554141c55402c203070f40140d8001c0305 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 797116196 1250 797114946 797114963
    0x828030e0d14010504150608011109040905030d0c091d06010e0f0f0306010807031b060509040c1709010903031803020a1b0302120706140c03030a09080c1006080d090e070c 75
    0x124000b1181c2034500c240c900700c81a501c101059041c141c818880c600140c00b03040024000c15002448032000d40c020300c4da505110315694096a401c01c00708201303c40003002011418000c00d2485007010340b01c204184690300342c0001d00307010170b0119804030295a2042d40140c5441100c81c1c810014800c1da42206200c44ea0801d8072280c032401030396810840c41d8000c01e201030081600c9419850700d0b003a641c1285020980c2c40c035540ca03052000d940c0000a0b9644518261400926103c201c00300711120040012090324194444003800501001900516020741c000d8400780194140e0680365903084039004030180050b00414051400184964241c1490140c3c09000c4003402d1380300d4000501507082150141d40c5a400128100039254000e8401d031f044d1070381078604070b09141004000d15140d2000401c5034800c0f9513142c155004028000040e2004243c1c020700b180c0d203d040229459000f4113080c0160761a6101381855424120f109252440c10344244a504c040d031a01c5024040e10768000c0c0043c102d03120309 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 797117446 1250 797116196 797116223
    0x50c040812031f0509190219030e0d09300602460e150c030705010605060c03090108130501090b0105180c04060f03060801060828030e0d 60
    0x3141040409008140e8540441c0d0740d00f401c0402c0305000c030b002112040310450625081215a131012a240c1e40014000d0b86500035501c9442114000d20a41c2e807160004001601e04c6520690300d0351200340c0c9032440301c046403c0707030000c281d007030b940918213100f008100c01c0090020303124802c0c2d404441051080b0310b6481080c4980981e500416a000042e81601e01800c860b00382501204596001d40003040c03c010a010200703590000b05030300321107030b1840400c0c002801d001c1c1120345ca07210b5a40c8500000e1541050710b82440d810350319182d03448140c080d55290300301030011400c0c0c506402110041c1d0080b8005500d094246001914107003c02081610044625425480031030310a000319820740c0d105000400740e5605080421030750010f0080004030a01c07040003007110381c140004c11101038420a0815419840052400b140130f40700d150010101c81d424032070001124803000a25100c81c25201201420003040c0503101c0741d49015008024000500c02c9080843c01d080012406107918080d81803042c400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 797118696 1250 797117446 797117459
    0x609060a03021e0c030d0506030f0a0b0a0b031c030b060409050c0403030801080f071403070f08030d0b011107050d033b06090a030b340f050705060a050c04 68
    0x150403520300300011070340014050120710400040300920040510a40b820003d9040c5055900d000d00c0940320344055540380812078036a41004801c11040c0c00030221010071007c1e107040c0f02d0b11300080d90901215824101242120701d000f24070110b498030a079200713600ca8607020f03500318040c21044d44940e400c884100008640440c080c0140f9100c1c03030351014002ea445142d0300d00241a1b010581c00301c403954004004070010700f40041002d8003110300502d041304100c02a81c0009091200c60780c41a0348100f00c1000005640501002409607403d40300c601b0403481441e00c1c01560703040c1002600d8085500b0a00c414011031130044100300129009243c154440c40c0041298000040482000f400da45d010325180800307040001021102c885003a200b0300d00300740c24480415501e446a0000030002c52052000400c07440d00300c2860510703c400c2210360070044400c5030440410315440107a89001494070701000102c5806074084030340b4107502c1401851070781d8604110304000c00c005000c0b45003460f0200300001c0e14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 797119946 1250 797118696 797118709
    0x20a020f0603100f06111005071205151e0f0604052229130219080408301f0605090a15031a0913121b0b011d160e0609 52
    0x501510b4840c4004600c4261b2194034018448807110451030800d02000200c0c0e50110302100c0e0801c1d0f440001c00c20b500c1c1c92802c0c0c103100c1000791005811401060702e400c684041112000e82c17520042e0360f040b58581054040c00198840c038014030741c000000c070305820508045e0040b13000b00036400368000900030400c50300c6141c59119441c200504800700030f1094241d071400340e040720951000e0050071072406d515100c41c01800307000c4a44170410300c01c21000160034400400d0840301c0c0c200c0202c84c89003406500a4031102603046078034442d8000c210140c000f03802d014a000080c168804c9a0300714403099854090b084501e5804880099080740c00e0300d800141c841544001c40d884983c0030746021801d16034544c1060040e0a10081c03180c0329803801c0003032222054084911003038058000c2d9841c0d035912030b80041901c141402195584405c80300400380410301c0b80702c4c4580da050301c4a0324490b071081e030380c0c068203008030a9013510710b00322820141c184290024010321b160340c1c9403a4090406410304600d0b0002448 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 797121196 1250 797119946 797119949
    0x705070f0906060f030510120f3f0804020f06090907030b01030b150429030403090513051501120e031b0106170303010e0a090f140706020a020f0603100f 67
    0x61140c8845090128907084484c0d100f01507018603007004107150130401024565401e105112a010041d036145003031020705440c4041030340c6c011402c603548001101c5e2031860401e102c0c4400803094440c01946240d01041c0e0031050040349583d94074807450300d5035002c100c0b4403103041c10041e600c070000700302006031a261450020303c00c07a00d90f10001600081d01d0b00140c00d139203506c1c00f094412401e60a101c4108506a41039130190765010144100d10000444c51558214006a01c000c803584044208410150300c0042007081d0f172001e03078612040d11680c1e07601c1800d988080d1030660701d1100029840d00903511400350741000b4141c600000c42c2c2c417103418000c20308691040c60b00a02000804003403485948007400b4260050040c18100e40382610101983c9407240410b0244140080a01004c12100a07054020800e1943c0004240d5030340c1c1080d1405101c2080d500070703114000e001c3c01e103000442074002f1035145900c0b900680f05040074502d04040115561005080042035410848089440e0071121003c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 797122302 1106 797121196 797121209
    0x3030406050a1d010207060c1115070212130f17030d05060409120c0b01090e031e132607060c230d050405090a0219050705070f 56
    0x406451030f1141c6a609030803020300702603c408194000e0421078401c034000c120300c483e207180070f40b05240e1114400240e03400400340f00100003500c0314003c3e4001281e00c19104480b00002000c0b009410001c90768007079002c10711041c0414114410200301030300c1c5502c51a242190f81e030751610340e00d100e02c0c1d2480340a41e8031b0b03a001c00c14540351904900012580149480d401200080c0024064031b5102c1c07040e40c018200c0740001034020050303c110a151264140518600003152440e104070105c40c4a242c1c5100008105281c9200f44251840019000390300821844140707080103481e040141e2400020f803a040917000300038440c0c10000c00c0000350350260b007a51188044940541905825021a100c00d018540b40000700c0742e400b40c020010303191304941c5840305441c3e46603014124020b03507040d180016607078100d00416078082c2001c2c0194900c01c4044807101070b100c1600c22002d000303990180 = true := by decide +kernel

theorem cover : BRFrame.Cov 796942446 797122302 := by
  have h0 := BRFrame.cov_init 796942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 796942446 ≤ n) (h2 : n < 797122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
