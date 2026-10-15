-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5206
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:05:34.696455+00:00
-- url     : https://prove2.me/submissions/5e98c705-8bf7-409a-9f57-30153f4fe781

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 936151079 ≤ n < 936330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 936152329 1250 936151079 936151103
    0xf0604020a02011515112e06030206031504051303020309040906062112090311010f09090f1401060f0c030e0f150a080604150e1503190b0a020403120804030c 69
    0x445085d035100b40841a01e521340100b90403160801c242c403102070090903103201c240342001031012800b1980c9004a00100c100002d910345c0c41ba000aa2943c1045031400408025000012181d09140c05155045480c031b54a40320500640e58003c1e41b81d0251001650085540d90140c60901a01d501300000500c0207201207038488d0300e81003440d04240516401641c1c0c0f2a0049000c1c45a14803072503200040380d400c50744601c030901001f07004581c03400015a04404014074076002050488a5120768505480c0380c6e4000200c40c20421440c11700312030142e0204051150000303a840e24160001c1000c9506981468030346c2150b5400d034002004611a001115000308000d90705100f070031014401000c0740041e0340c484c103029998040402080d1038004a2400344420904c0003000f0800400c05059046022684040044604040441c0c50318420b0504038042a250600343c0c0c09000c0540c032100e030004080c51003580f802d4119158000c400005403500010405a00001018180300e141101d07506a4008603031200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 936153579 1250 936152329 936152339
    0x3032125320a020307060c021501120c05120c0f062508040e0705090f0f012a020301020c0d120501080a020d080d0c081b21040c03060f0603060605090f0604020a020115 73
    0x1130390704890740c11520185044151000c03070f0700004116015944c0c1080c690403d80c20703c845900032a004903070844095000b0040070460341da86407090210382c1c0c20003000700001e004240c10440c8800c4000c41d80c5014450421182914400a83c09207945c10000280441c0c000d03814548070416204640c014090900400e003404010355014000f000c00704400c84894200000c6182044100c1850f9460f80d0b002c140c5040144c5550040d03014800c031154942c0048040800140d004030307099910000e0f00081c0c0d500030030146000944c200350741f61100c0b034100d4820480c2d581002c0c115035890200a03c0a4440c0b91b02c8213540c010010743c00b0440c0d0b000032421000b80021002c0590140c0346440548480b08404407629291260540c041d0950329801441c10707a003103103002d0242c103140c841d1401500030b80f0022034958012001c03401c6400744014101d685440010040c0c40c0d42130590481d00180c00807440b03200f00d10184040c0f00c40554103180c122200302c0b80140da444542030b0030b17030050540c1c14400d00c06104204000070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 936154829 1250 936153579 936153583
    0x8030d02030f07210b180f1f08191502070b09070501020114041205040e0c03010e060a121209090f050603060a0e190203032125320a02 59
    0x200441c0140408901078441a0050340c54803d01c503144e581c180002c50710024550015005070b4031142d0040c207804041115042c110302c42d81402c0380c0d10301520203a0820f102d880d50079200c01b031300b10058116045c1007183c1070801e60b40d180d9400480c1c01c414085001703440303c00d000307a00e009811030500c610300031543c43d556481d090b81d04030b400310350003a941d0186c035000007010350041c0034403440842030084d507243c2c65445030380d00541850140303002c0d0104235040c007005c01c507005405c201e0f5000f43c0000032410b85940c58075410200c0704234010301d03050151601c2a0304000d00a003140840c030a540d07004204001c21425000308075030040f8070f44d001e510f00e9424442205c1072000701c3d07403010340581d9040e8183c59681c1e403001c1465058950409200083c2d81c469061000c80c44115a0508010741c40241a245400c00c03201da4000d140e80d200d0441d44807040428103001d07a0507824618889402c0b4680100b031180c2c0402e24001d04540c0c2940c2e0100c59101341c41a050648548d9260055400c00003145e0142e210320503004002c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 936156079 1250 936154829 936154831
    0x1609091a221101080a02032206060323010501271d100b040f0902090612010905030a090512160b0c01110c0106030b010b0306090105102c1e0d021908030d0203 69
    0x250100e07000901092002005e4002c0f01d00c18081043c2c0c0c43e200c07000065101d401c0040362001501c400d03a543c2000310000d0038054100105034103009400d44241e044c1d100c840d0861320181e00003582c0f0b41c048c0f00042c102d00c05514105443e10b650070000247c5101e002e1003003010309101c4a44040c14000c102084040785400c0e80244d202c55000d840801c840641c040c00c203c00c4a001801c0030754020b05034070000d500b9207080c10100ca01c401c200c00c0046101070f561342d1170300d2840e000782c0701500100d40c000070240510304101d4081990b4094400040c5100c0b90750420003501005103020f0b13104d01d820009844003240009401c480480e00d2548115a5502c0844003005e0090280b80000c48181e200180009540c19045082e0303805800006c00c0b40101d41d2810040110305c1c00740d8421802401205086540503058006d062075103940444d0801e001c0c130700140c00300581c1401203892482c0400f210700c694091900e43c042d84034201a4180d074406c21802c4141010fa90350318060b80070b03800070300c00016021034a6829030091 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 936157329 1250 936156079 936156113
    0xb03072d0c061a031606090b0c0a140a060204030503090f100c1209030512180303070b06040f09120f02010c1115070c0b010b040f09060b070314090a06021609091a22 72
    0x7010541d030702c401e00d0a4051150317480c0340d189d82d4800e901ca103011501500503d9505803a80c0101c0d4030a501940d1200d059820590054401d500701141c00040c41c142a9a1801c1d000303006c8801c200c40d202e417074a0103494070581c210085c105c5a07000700c000300d4a500850a450140d070300f09013120610707129106900301c954000813115001c017a8000480c10760b82400419200565880800400a0b582d03000070320008064211090300d07026103034000c03100842c203181e219a0010100c1c3da80e6560245000c03001a0a584908401004020a410404080340310200e0007600b0300304a00012505522130741c504445070004e0800c0a0710740800300000140426071b5130000c1c230445003502c020003441551444020100e0300144100c1c10034030780c01c02c641c100207071259070399220b030b10343d07014090703080c01421008541c500c2c0c1c954125002682c048180380b114143d003407080c03500611a544040c4940f000c103959032024090211840c100114034580032656a01c1c140341c40101c1d903013049d08110909441c6040c1444400200d40388 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 936158579 1250 936157329 936157337
    0x7030b0f1e06121905070806071e0e04020a0c03021204081b030312240301051e0a1104060c03080c0405010f08090708060c120f0702060606130b03072d0c061a031606 72
    0x4547c080400c4240c4689841c1d00c80c40c1c0640681d02e56000649200309200f0104420360318146015540c5101801c1c031400c041d981c4012003015850040d01d00003640071003020080d0117000400c0b14203000504245030600d001e43d410804003440740071a10714020400415074042258080040c0940892185009420b0010002d2202c1c2c0c0c107103050508030b41060381c0b500509851442102950345050300c1c110341004503c0c50019020352034a10034030449d00140c00c28400a0f205100b003009043c1c0c842022500f1141201255240c98504400070705580910108a82800760700c0c2e0025251481c1400264014880c034001e48001c3d140505001d21103600628034010100325540104540980707268501e4410100d0340c004102903100d034401c104564020003046200d0b24001e410100381000041d0283d4080c1019803646855580e039200074000070841421001d0001c03540f01c0e40c822440b607201c08a542c906422120024065100d510303014869107480360b00f507404d4403810942035120b40c0b5561000d82110707860340d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 936159829 1250 936158579 936158593
    0x30d0f02030906010603110912030912010c09091e0506060d023006093d0504290120060f1005031f02180a0807030b0f1e06121905 57
    0x382039003210520a44102e0f400300608c02072034641004100c0040e08100003080700d04040e01d0a00044281401480e055020b0351036000000c0c2c900e801403550704c09404100317410300c0300c18820004501e41f040c05040883c40c1c291100c0108130940c6966084886c000101c407001d550310b401400e08003800c61111400c084d82da0011042441c010307140240c845008410080c842c11a54032146820f145c0140c0c0e0a0050840010003981078140200311182140881d84400380e01400760701e0301c001c00c82151664520803c550b6150a0501240c04611000e042c003074001342441c85080740a04100300c100308030054203400c50b01c00c5006200d40b00103000e0b035035481840c00d03a19028600c0c0d111800d05032100f004d8403c0e240d10054916808150607034070340152010742281090441080c0d010b00000e400a400e03a4016003aa420850080c0706002c2d52044c070980c84001c81c948004141045800180c2160203039174000107841c90f420100f142a07444100b03040c00c9071300034000c44504000d003000b09a014010300004842030b01c1051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 936161079 1250 936159829 936159839
    0x70803061804021e041803020609160305151003080403061a030d02030706090206070231140604090633140105070201081509010902040303271403030d0f0203090601 72
    0x31600c92042c1da010b4205415a0007080c03003150b261401d82c0066910035204d0040c03031200701c0214000c00c6018001e43c014112810003030701890400c100c420b48100c0700204882c051000c81d90002c0c0b0782440c0c01e4400d1000e0340b203554494400102c21816040100b400790b00080000600046801c286611107c80d0a00d820b554029810140d695a0307841711000540c10510141c00411034581c889030500b03002800303980c07411400d58009452900c01030010404030f010390416048071810100410404044000700b004400540c80a2146a040041440c0c3c4a01e4a0b40d070701c242000b1080d04011342d143ca00b840c0301d244002042c0b4000c03010710b52140c814000e0f808280d900194000100c3c2003070b40c020f00e068644500d0f2000319001113032020801401c0900307103e402007400340345840300f2003028001c004c0070400580351030075881d0042400c81c0c0440c4c1d44450144502d142d82d030034500744604404071550300746110050308104011a05500409070045e100e139185c81d103005040c2c0030640082d4850507800d010b4a11580e207034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 936162329 1250 936161079 936161119
    0x16030e190807050f060c0a08040810060302150c030d0609060911070b040308090712051c0f09050112060509041101143a0203101e0803030a020f07050307080306 70
    0x2882140303600c1d405a4403c114905040c200e0040502015103131a02c0e210a04100a02c1d0064400080710650800241004500010b0141d036038480d20501c01882081d14540000d020000400d00325041c07070000056025585030100111580902c100a00f485a181da840504000f0031440c4540e18440b420000880380820840301203070100e9500000024030f40d101d03900c1c1140e140340001c0445029200d140b20120b03941103649030f4031f001144900c00929406800d0a443e1690700141c2c0c805030141b1441005044541e600241800142c13942841d0400c83c541c101002440a46282e1b4021a0800e0301c890a11081c080e80c0f1559a900f00020b03200d09905540300400120240309110400205c004070034400740304900c9081340006800c8038403441e1500c0e0081948644100e07407007900e03444101c5010403c1001100507014031441101c488114506800340f5089506480740300081001820990004140c040c084020b4117480b102508003040707a80b101c0c001d00e01007919500c259030b8280b0403c02940480210144 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 936163579 1250 936162329 936162379
    0x6040f021f0519050705070e010609050604050609040f0609091128030f020102010b0a18050610020a032f071d060d020d24022106011b03020316030e 65
    0xa1940ca062403d182210301c042c01200c80e903c44000c200040003400080b43d03040001f40c01400c100c4d00500d00365450601d01404a4005c0d511003801030360213100c20045a84c4204c19192209800c1d00c000c19024000d02c401d00c0101056007091401340d2920104506200d000702000d05400020348541d008040c41b260040c183e14030b4074507845000220aa814400501d0040c419520548180008a8070051000005910003940e8000b07513a00104c00c003184810b4145406001c3c0c03c1507003541c80210380d040684000703446401c81040a018031034a880c080490720881c0580900c510348402c00300481407402c0035466207449441c460901800700092520b81d040c034012802c0c0d40224030041400380b49103119400d2001c1c0c14010384040d01c141303180203006003680440686145240c0f0381300c400180e4440f040707030f0380d50480007460110403086031180040041c241d8104981070303048080011603605020301450201c1c80c5100d0102102100302152118004043c0c0001400c261002c2c1210f8840c03810320600c0080c1c031000c1c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 936164829 1250 936163579 936163639
    0x1c020306010303051e0d050405010f050c0406030e0c0d05030918090a142e0e190204051003050d030209120d14030c0d110304060c1d0f01030e06040f02 66
    0x3120004000082c01103005008602412034502c03410400c1d1007140190781c2008120551054803807003003004001c2e003880303415009407811108001c00d0410340500c0762140114040e24052565642c031074040120100614494020002d00e11030340a07030f1615156440b500001e0380c1c41d01401020001310b600e0b03044940c0052040e07148600070480780c00030340c50740100a03110048030b100e1030142102104604803584d440d10804982c030102c45034040c40c2c1d800c1446c01c60306d1012802229800c4000f441018440b1034a003210b650790122170225a40e2038410a4080098080e48010464449c58610000c801c2e0581c01034203410000300c81c00c0c500e00c160981d00031740700c844181d40827000505510403140c8c616030b5074026541007a101103000c2d08142480211108461285018a800113070220030070042005501a0800c41c1c0443d1408402007540112030508100f081c0c0b108a22807004028500da599110b540074080351504001250910704050a0a128140c80303441c0907400f60220146074007404560f168140b510300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 936166079 1250 936164829 936164833
    0x20d0e0604080d0213211209140f062b140114211005100b0c0d0c151d0c01030c0c020111100c080906090c0a180e1b1c0203 54
    0x44075078502c0f400079406960ba1040900c0151804108150703a0304414401c03140034100104040d0250420000c84825040d1110812110f4501801000004071201424110a6503041e62030059140055854003800102426842c651402078564512021500d0300031403959408112070401e0800d110302040b130902801c0312158080fa4007242604101c040080e120031058036100d410030001c0060380c02d080a0002031011a516001170110280350100d001d40180130000c0700d80e240031507152070030744c031090340680780018400b034100715009000540c0109848071161290400509159510407601951b8140040802c0c0c0b1409007581c07007030b50091107025101d219580303940e5400c0f07009900441d0b0200406101c100b4a000340c280c01c8081003501d002d4600c85d4034031031b00e86c9941464403180141c640503000300010700a070310580d800406500ca106d80300d8291034811001c3c42403111000c81039005408550416402441038121625a524034280c440940c0300c1d0031182e544234821840e40d102c1c07015558907000383d030507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 936167329 1250 936166079 936166087
    0x8360102190321050a090c120b06010c030210052509260a02030a061b0c020a0608090a12030204050109090e060c0304032c01090905241909020d0e060408 67
    0x820b01a41c0c020b990740c0301201d60340c0c0d0039000a801c03203c2039801c192228007070703c3c4e203400d4070400700106800e2100282804a245002282181d25500c1c2c2d5a0f40140c00b40f41840381200440050601c00d1005208941540c20103218506003081001e0340941c0e8959a0348901c20302c031414aa07520720a01308581251300414000102400408280d0300b01c840c1150700d035503030303100b654411001600c007131268441c014003400002440000100d85020f00d41c001d03040700400c03c035800d4039000042e82c600f040842070350001c0c03501d01a01d6585000862a00c031aa04c1c2c01f030001c000b1030b8199030310903500d07800510558000380e175041c42803039481134000c041d552040350094103600501c00040c0e1030001e000107558864040d1828507007500102c6054848002d030740c0304001e9102c030b8007103409a180d40c00c03e440354003c000d241c000700201d141c40c0e6110100c0c580d14500300c2c4e0580700d070203403202c050759030b4103240020312203203012505601942d80010713900a6108100c0d181800e0b0501100c02a0903901007159842030750070000040c0f030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 936168579 1250 936167329 936167333
    0x201030e0c0901031218090506090105150304120e06120108010b12030d150f0b03010906120b0402011d120102030a0615050f07060f06090b031204140d0836010219 71
    0x1d05d0783c2501010108028518040c6101c0c09210401d070090607641e00000310760a00000b40521200160085802004045808140c086100086940c819040501d088004241110450703002d45600d4026902240100341441d6850003a4181c5040324940d0f0020480504180148220201c9000099015820510600ca0404441c0d000b600c0c0396012841c40040150700c9440d018a540c0c2c65400c07984003104044014001c0500f07511070600134215452248101000540d203581c40d40d2401400281080101201048840c1e44062009241c65008000002c1601c01d814528000c0d0000c44101c00d200c0d052600c0094080e40d81ca000341b500502e55914503107401d00c1611030040c03c2e48044002c0740c84580d00d02884541001610940d005044d901c000441e104841d00105880e0804a80e080641a2020401004907101555200001d010180ca45500716a01c9041c42d188a008071a6096554501074800c100c4109110f0f40188a500d41150256111202903004aa407041d002c1d40f210310b6443d5240d180c0380 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 936169829 1250 936168579 936168593
    0x607020c1311070807050106140f101101020c030a030b1009030311120d02030f0f0606090d0302011803091a04031703091f050714090f0d051603030c0201030e0c090103 73
    0x1e5444940540030809500720311000125610224050700c49000c00705c0c070300c01042028000e80000305001401079504800f03e200081c0c1268194500f94810000b11006c807500c0342c0148100d0340e111505800031915039442954807038032a4007514001000078680000384a1610301440504220741e0b1a0362031810300e80c01c607607042e01c449100400c0d8811a100d5043c00c8403111b0300c100b0003418500001c000260b2203040910001c5103c2501401304c0f200ca1401104000c81d6868070002d4520f40c410480715200002c2907418103078010a0821303800609400c0284604007419040380d600d904613000c2d41d0684500a002c841c0031a520300840c0001402c900d0104001020296124003840e0041c900c4003d031070858418518110300c05801032280002d59071038404000b00b40b9000300e100c00e191165804035034a004503030000900c003940c007079644074880c2281c2c4d5160707401d1110803c01c00d044100c01c540072415440e102d04000c0c140c1c1e5451071040740040d00308100001c824a0104424041d800040e00303110b100d90855076504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 936171079 1250 936169829 936169849
    0xd080d110415200619110c0a030f090e0a05151e010f090503010c120b04140402100e0928020c0c131e1b050f040b0d0b1f08090607020c 59
    0x2443c06054040c440d070404006014250003980301c100c6100c05100e1052006054a044a6518940c4102072004030081c01000c14907181c655491700c3d040d00a1700e104402581c4006454025800d40382e17031a0304000744400313164080c1d4041d402d6107002c3e000c0b03401001c08021210403581ca00301c08485501d0042500c55001d0310f009a5245030a003043d40a00e5103810203e402c48440012020009010100d4026000c400788a642c0d1440070941d401c0c8001d807040e041422036043d02074002070003200159200d034100c9204180c003c040c402c00415802c180c0c01c00e5040f090201410724408040d4a580748441201e101c0a40308403151416240d01074038032040c24400b08070307110717541e94190f00c0f66985840400c40083d09003e1900700d03904280c00c0008100240d03507240c1c841e040825543d9024000c040010b410119124030944086030312800800350b6030788240115401400c0c004100a4001c0000f0014002046614008240c1e0711015960500c0c155210a021a81c451050341e0b1400560402d45504da89410548200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 936172329 1250 936171079 936171107
    0x50409200d1a04020720150a1808011407270605030604090b01080a17040605040509130506012606040309150c051c020607031104050d020f0d080d110415 67
    0x550901c18100b0208099031301450302143d601c4003103000071190b0002e0030143c01c1010070958902440d600714070442c80c402d05c00d1140d40c0c410b0040008038000c805100e00c08580281580d04000d00110b007034602032000c000c1082d40d0300d4010072a407111492645e008843c400d03036001c420300c01c03045c070841c80c014050700e0b16400640100c0e000350700c0b0024203001c182c3c0746108034001c00c4c45c04002c0084400500700f10324840a800c40540862404000c100b050b82d5000c020703903041e80d10440e0040c4e00c94492022507140415440346c024294043c580000480e180880d5440e5201005042444030080d0080310154031504c00300d03801804505010f5050100c61000405940009500e040c051400d803055141d5519121b0b510f80b030f0360315101804803000282030741406481e400100c241818480c070346840400310068011401458002c42d4086440d400b5907407030700d49100324070030081c001001c07516603030914a2003036201104041700c0d603041208459090f80c599088801b1078018001e1490310401403201211942007400305 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 936173579 1250 936172329 936172361
    0x12080f090d0518090f060103200301300b1b090a0e070306170309100203071a06040915060807050f0f0405040809060a08070f0c050307060903021c050409200d 69
    0x50801d0715290030413542e006611101110941e454050001002d954402202d032241d00f00303019050a8801c19001501e0545000441c0c5551038081000c030103010302c6201440800032000c00e800d901c1403007841140b50f80111130a85860749a500c41c070700788a00c98802c03412143d8000015400422850b040d644000d500b107001841e000c074035141c6e90054190014140384015649800c001100001b525080390003801c0a5010300186050104544600301250a41901c1c00405001070000070b841c1e503500c1d07000d215507c1c2e0015420303882e841c5041404000380054003556916104801f000710b814038001006000d01407009200400c1c1d01c1d07a4106110103040007820444035400240401c51240d940c010180c0800b210b40d544480c050b02c0d09040c0113000c401111030311000e01080d520a580403410100c00c0752030407900542c001c00d80d04142d1600720301e842e9094040520900c0481d20400742140d02800600860b105100240300c03185081440324031076a045c034091401440c00b0080ca214105581e004090311a1b0002c403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 936174829 1250 936173579 936173617
    0x319110901230f0c0309030d080f070f0e1206090d030e0c040b06040302270a0c081528081b03031905090301020a091805090c040f0608030712080f090d05 67
    0x21007100e45800005282d204c50f00080b40088141c2401c00904034200303040d103440d42240c188921420589800030f804041000707500000380a11601603c400042c0c0304c006480611800d00451085031510001d960445280c09642e01044019110b0b00514004501c003402400207880711504010080541c40c0049402000c14007002000d0380d1000f00000005040460354041003603203038005005070100500d0481500e00d00408400f465074045645507020008560a12845160000150b154103200741800703112000b254021506500c0e01055600b104c104004440303650549030740f10003c2e0404155026055407041c801c070750a2071202d203984007401459085c15032401112001182c260b034090700d1424082440b000d810043c0b0340000641c0441034482c1c401c104030a06104900507211114400307a103128544943c601c020308030f05940500000c0c40c000b412655110802e14080102049104410020034400d800083c142c507040b08165120701d035084042c20b0302c21040c0c581502e403030704801d0b0720b0600064042 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 936176079 1250 936174829 936174847
    0xd033c0509060702060711070308090f0d0c05010f050909160519021e240a0b030f1c0908070501030207150207060e0f011401030b070311031911090123 66
    0x441858041d07801000544414544241c010f4500000030b440001006400e64000e07444487c0800e052042d0b95102360323a0ba80c0c4000d20b5001a0380390b1859403666500441e0048400304000c02c881c000d07011914281c035072440e48040040305451900a800c20a900301c2c50b000d0004503c40d0f1002c7d40c802e4081c00f035080141c200040c80042c030092107800c1901101507405183c5080b03c403030412500003c006020b2008211028802e22500e810440000054041c684c068003c41c04841060300710100c917a4026007121003540956024a6640c0513000d07900003902c400005c0031030420302c03e40d45d4005441042c001004401d05e0840110002d6202c12401d4440040c010840c04a20100340000d00099010b040c01145400d451080c842c01e082c3d01c01c060310401d80c500070a208201101821060440303400c08101051540e07009000e4000d0302c4d01c2540e43c0b00030382000040007016040d0002c801c00617041e81d17404018041e19668072050a21413110300f24041047c104103200414000a20405c0244041850608060921f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 936177329 1250 936176079 936176081
    0x30b120c1c05030a03060612022d25020a05040b01090b07030203280305090d02100b040f18060b0a0e0406021e0f040303030e060610120209061305030d033c 68
    0x4c1c11110300094540004004460303203e180c030005646569400c62420800807220718858004040c0c030002c05010207090300c1e80309200c1c8161041480c006010040d01041c0c000075100314180344108a204080840011030141020300c00c80f055400706071100312a5a0902610001640000c081142103104c00c208081088000d418a0540403010856250b401404140090290382000f01070304800d50001d42107003451a8000b42d41000c0303d00440c1d0004542d078003107000c0750140c031030b51208a42039401c02061943e914141000440c0942c01040c00301f1116048030f003040406c411a2080441d40b460180204001c9151940104100c9182d54408601e81c0c8665619800b41e4000ca1425411100086000c200345a014095200c500c003940300981410701c0c0c1740740016080360009803d4800c006c41c11071410000e0300e580d4112810701c1001080140c560500101000c0c3c841468020300340a401103041d0304080034068011840c2c0060ba0384000c6008004000601706841c03170074a0805941c0400c1d080840740c4002c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 936178579 1250 936177329 936177337
    0x10213031b0812030402120607210615020601031406070530180c0d12050c0f06042009040312020913180303050108161e0b0d06030201030b120c1c0503 66
    0x30f15a010f0b100e1400d40100410400d4800482089400005c20054410350040782e112169400300c494400b4a01d1040c40320008100507046140e0310080701d0f013400101d54000035068122882015842c1e07480c0b00c0b070034016480c0ca0040d112640400e10520030703591a1a081c22000940500d03840d00010344440180b50b16100b001e09903003078841f12005c0008440d0b00300c018806140207000c15150b00b40da503204c503698001c107001e00120041c104440407400e0004040140002500380a50f01c0c100c4005047c1400e141c944402428822985c02141c80002c030407a040001d919482190192240b01a540c112242032020354800354050354031a410390100d40d6110110b210324600d0440500394242e16035041c0c41c01034120ba4040e04010f969900010948181c1000d00380549d0a541c40e82e28019510100050000000c50403500707c096009004a41c080c01c2142c04d50104084a000741d9080c4800303800075013484905519055407000e2380e04030312000c80d42e07411f01220148004041c0c240d5150318420a407500c5055401c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 936179829 1250 936178579 936178603
    0x81902071a0a0c02070506071a1503010c030516030e12041e0b041a13120807030905010e030c040513020a030b04060b100c3306090e010213031b08 64
    0x1450404514140e801076000552096044608110742003040c44042e60714040c5100e054031403c80081c400c020402c881003000d100541d02c0b182200542000c6581c0e00c060402020380358081c0d8603001c03505000c0c610034081c80740502500d05440a00b442e4100d8200c0182c0701018035450a417044211a82043c0c407110002c0004004550f05070101c0c115885c11001001c1d00f40d401030b59900c00a1209100c01003c0406500416495149055440180e500d9001d0446200d5000301c2814204e4441c0c030b02440b1485d4001c1035079074480e036a0328481945400043d00c82c0035044950903050380c002d004070725860401307500c43c1d0341080124607044c600780d0302039000401d400201c0d08100d41d641c60340c0c0180410400780d030150400000e001c0b01d600c23081c04d4602c10010b01c4c1100019002c2c04418840341c100e0ba04480092a04400c8480420400e150000001124026081c54400c50140342d151841010007180c040c42500c185660810241540c20f1860301e0361034007401c40c6c4542c4121660b0b02e100001e001c000c104001e00e1440703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 936181079 1250 936179829 936179843
    0xc02010e12030c031305030309090105060d20090424060311120414070b0906030a020703050d150807080a02130b06040b13091d0703080f0c01050a060314031908190207 73
    0x14481c510001c181207146d011600952090204030070b01d036605a01a8191941610442c0d15a01c00011b51005411101c44030b22174064020402951076204000034400c052065a09100a00c0f072000031050341c507005a21000c19103c143c0c820300c1424826004541000c03039041a850401c032442040048060090701c0c21100800e200c81c8603031040300c0611801c0d0080c00502e100ca400e20100700040b48191000402d02440303154000f40c1d80c0704050040064414050003107601f0000d1400000915403001d14901600481344101d041c0040d08901c0011510600d40e070250821600860000c10140905906002154000303418840481c22010b491301a000c2526182c04408969150100c2d402c212400c0221403003100f00c001d84030900c1c10400150a0381180d43c4071624983d25403040d6502052400394041c0f004142d404c1c0014001f08051541055041d2405001403000c5d8445000d0709960383d110701c0010342c1d1f81c01b40d0583c0786082035000c0c3c25510350201e003074141141a10305040500049a0000808882d04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 936182329 1250 936181079 936181087
    0x70e1206160f05040b0706090614040212030705030712030608030c06010311040b01021c03110c0f0c03030909070804051501080607032f1308030c061f03030c02010e12030c03 76
    0x15181c03050074054a80c9440c28840c0d100d4a40d8a801020751145014008000c100001d0800400170554021182141c10030001c01294245003180440050141d40a034401c9804000d04001408080f04507056641d002d8015850020f5075510b0300c8440ca442a403401c1072590756034000604080074401004100001c0b4085c104540c11860651403d001445010b0300403450201841041c0c1d8000071071103554803088588012824030700800302c010b0001d290494884000100b0400800b100010f1600160515001a81c1c048000303502495600c0c010401002c1d030050034030b0040741080340100e401d00d4010b400340e8140c419140d440682ca000000080c2d100e55500c1d030141d0308101200b503051045503c20880d8200010301d45d100d480f000003540510490305000c7d02c20000b00105900c850a141c840140810005d50f52a1400c4a00198a40c8022100013552030149400c1e00c16402c10b0031785280640313625407a940c04a804680044a4944200c3c02691f007011907280c061504030300c1003000d01007148498008590b5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 936183579 1250 936182329 936182341
    0x4050c0901030305070b130b1906171f05132411040503060708040c27060f0f06091214030c060f1509012105031e030609061c0308070e1206 61
    0x440b060081407112581d13207500c0200001110240001d4014000270b4038403400740c1c412403410000302a641e000400311200307404014109800414840055032040b4072000070000d0a03080041a00c1c0116042042c200c0d00354000d60015501c0915034000240e2024001111094091b2880855401482450000c00b0105d0204454074042150300da0200d018075100c8260305281c0e40300f8002010714000d400f000d001402641c5000f03980311440901c4591004c8050003515680e0100b05a20a0680070b0107260001344840400e00b14000c540c1c4a0890700808040c1c104003803151104201c540309410b032922035001c204800080164100300c00ba02038264002c051b215410310a041c841c41004040d20342e030240c8041b50040251100b0101400c0002ca00c000d101840d1000c03034613000f0305600c11400409440f44001c242e006c94008104007a503c50a03056400c144140c55a00800c1401640c401d03c50450f42c440381c1558002078458491031ba00300d462400c24516441000340000c4020060700d1480089a12190070490 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 936184829 1250 936183579 936183593
    0xa02063f090c01021c0c080d050103030f080c040320040207060b1216031403090a0303030e0712050a0213021c1e06051c1a0a0504020f19090504050c090103030507 71
    0xa00540c1000041040c030002c000084c1d2541080e10030301070300902e05030401c0c58142c014410690413640c060300503035855841400341e80c01048280400e80c0007910560641c0012030003205c4040c06070b44030760b10312410140346a64408140940b41c444003001080340e014028a03484e180041c05c3d41a11a04010412034490320500c00c070f40401c1c0c00c03a03140b0f0741d0001e03101400e50240c0f80554030a6a40110006850110702040c0c1480c62040e02121900454100400004e1540c15440702080083d460306270341040703503145000c0b0000400780201a0164001407400b01c01450b1008084482504450003d400c0140300c0700c85445c841c08d0710401c02410b64899205e10708400c03150000300070340d01070107504100c00350411001c621084121840008a10480301c0c000080c048542c01c1081c0100c3d03034070010081441c000030440050002600c0c202c0c0500303c3c401105180745031100002c01101121403008264a2416032101d000c0c100150082d2114041c810040c580e54850109444c06940a601c03156070b903c1e01483c0103a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 936186079 1250 936184829 936184831
    0x703020d0b04050c0f0f040302031f1406060f09010c0623010e040b061309020406150210060b0904090f0203010c17010f05030a020108070215011e0806090a02063f 71
    0x600c2246000100401392800d0b078140c604003030f03001c50400d886444651805034581300d1504040d40c507100707840c0c15440c9103455900c10811000082c409000d0714400c41d61a0900381002d483e100d92000051111040d0700111102030a0405c40514000d03603003e08640340c10048a15107003102c0d003041038004151041c604c00b10b26850040182401c1d1081038a415140c00c0091007001d4041c0d881808801841c0325150460b410402000da0024403c01c0070968640342c0d00e06c001c1480c20220007601800c0709074070766024641305040031180410b90052a04460904002c0203107000746084401c68507c171060400341c1c809220b082c100c18919111010400e074110041c2a07003840580c400c01c10394a929000303000c075403008644c45610701d90a082c501110b444580c1c041c7c0c2010720f120404c2007458000400002e064039100c0c240145c03075a100210610941d190610345842d000101c0c4d103010541e1000700b00c030740181459401010703026404040c804880546900014505c0302488441210720441481c3c035134048007491401d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 936187329 1250 936186079 936186101
    0xc130203150a150507081b0705040e03030420120f0124080d033c0b0d0c050f040204030c080f0c041b1101061706090607030c081305030d050703020d 65
    0x190141910b003c2407440790700c10f8101d0030300c108140031400700d040040110954071450003264550020342d07454009030380d4a42042c40703018032031030800d0555290f840000c01100d010f00c0e01302010000c56028110340c9164034809010307058001d10440c1504448603000d120101c503030202d02b00049440460b03001110360072611400310003429813683c1d000300441907000500c54015481750501003140c1c0400c1c0c0c1c988415124510591807200c3d11840c01843c90407080851a1006420120801109030100140001748441c010020950780b04040c00380030030700d00710b2024960020010f001600c0e298582e61420444000c0d940904469440300c8251030148906100300403034903c05407030410241d5000380d180d4404e280c0c40e8011406100450341c030190240c400b900020f003e80641090043d10b80c003610302e02591000304a175005594021400881c410f91f200b40640c4125519036616064281c403500ba20300038040a000c41150703188002c1204070044861402882c9c0f0501d04c42e01e00680383d20303a10200b002528400740300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 936188579 1250 936187329 936187339
    0x906060e010f050d03110304150206040308010b190e0609030f0d0f0810060302070c0503010615030501090b061e1303150c2c0102012309070608040f030c0201020c13020315 75
    0x9011036101d45400084142c0c062502151030a01c4800700387c04c500c10b6030041020100c44040d000784864001605c2c0340618880d5440181a80c3d984050843c140030b0f00961140942400720348031034447c401e4440f0001c0410041c03010b0700d84001100028030b44015800250074940015140000007500b1241006181c038050030040f03500e18054100f4061560980030707020505902240810a01030b280020b40c000e004050001c02c02541c40b208111500e0341308001000010781498000325040c40280580464154003905a0703041118119034113149084c00b02900c3c6807038209101819240200a1902000314000c3e964202004a104d20502c2512550340400c000d04c4003050079007030807002d806001c441580c903a8285111010080c0d004078003602000040c10303143c0f1400808980c1a202c42140c5a002d85104000c44100c641e55500c10788890b0805c50b40a030142d01001440804640280d40701c0070928030510580301c4c0d4840174400280400e1404c03c0c0145000e80c04000c1058014030040800e10f01c0c44100c170 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 936189829 1250 936188579 936188609
    0xf030b15030312070c0c03061b17130212150105010311090904020907030f021b010c0f0e090c0c010203180706020a02090109110c030c1f141609090906060e01 69
    0x101c0e50300d20400c06091a007440600c005500782d80b04800a440f1168082d0341070740041d55908100e0040d240f5000d2204518103a00b0f03035880b404e4011904182c2c8640010804540c1c0d640360181000701880080c003da0704211700040944805800707004001c1c1482c0c004881e18039550600c400103086401186144050007001c1103901e9540e80e4128040d42d100d91304a418244951394444102d0242114582c04044680041501945540444aa1021059124020070040c0c1c0ca01c03000300c480e041c490340a10041580348640300d0f0582486012240e12581200c11145070403054020142281e00886903c400022421031444460105024032002048984014111580c1039000200d07010410f00c107214400d6961100070101c041d030803003030311201c04e10b4000b6a0344808100d070220380c460f1038150465102d40b000c8044402d9295141c400ea20302c904030303031520040594642c0c802a0b09101c2050400051003201440007880041502074038003100c0c0314500100301c1618144800040d05810f03040b4045200d1650 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 936191079 1250 936189829 936189871
    0x603020307030f121409040e1c031407081009090302030f0a0807030605090c0f130503120a18060522210605090a0b0402060706092907020a03051e12010f030b 69
    0x142c11b84060f180704540021300c003207092402c90700e00601d4032440403548030041d00d100741054140c1c0c000d030305070105103500304240ea6455804903441901264040e610300c001174420f00065281750701c1407240d1440390048910f4560201e0760311241780c00040c0c40600094801c41002000f681c940900310091a0503900c140d0f0504118078450824041c04103501103103240450798005120030b01c4140c10041901605a40007200300f1080000303158042000400030454011211910710300b406010422140243d035460704045402550540c8500d083c2e40d018031008012501160b42da5051710300300d0b80c2400c000c1c4080b842d043c0f030707140c20002d40f00020315224640d00700e11402c00115150b2115241d1099044441c0fa40d11411868101c006100310300e80a01228031005818031000c100030700c1c088150781e00310309170394840d40c0340003040f41e40e008480b030000c0000c2c10a10448400e020310300000000c0c4040140c0440c00c0486d650000720744486c0c241d00010210380207034400c209024040700e06070303000303186800700405180f10b01d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 936192329 1250 936191079 936191117
    0x9010b1803210a09120b010302120a030813080d050a0c030606080402060a0c0c0905130606170c04110d0f0c0e0306010b070818120a02092211040603020307030f12 71
    0x50b40e4060b004007070024020b41c06a100d126008080c08200c4c44036000104542031513210384e00d003400101d00a02c2c0041040720070200c0001c004030101c2e41542e5008566a5602084040b454245001c0328104414040075000410501500e4840d1840030300000d0140b20152006080d500c040c0c1c001018080304009110150304d59074220b49044049051501008203c1c0c03a04046205503580f08030a420b1400060000e26004482c604402030f000c0e0b1000e015640c1c80d40c025540b14180d140a008190780003a04030f4400d41000d4028034001491100c00600f4059504400d200366200782d010b001916640d8107802d95006d41142006840303040a400034400c66042c940020725034450750002602c0c0c0c02012400e600c0c80c0d40c4070038403108034002c00351000b8502849100e54955980a401c0102d22814003c4009850350126060750310300302c040749010882100306a02d40e11a294060400300750030948980c408009603e08008110055114104000344600300e070410540c01c084444050b000c000c0c2da042180204902 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 936193579 1250 936192329 936192373
    0x2070f150e0c1e091e07051804050108031606061a070204050c0a140d290901091a0d11030d050a02010c020c0a031520041d070215040f0209010b1803 65
    0x1068402c0302c1c04c0d4451120f44e62040c1e021348018074080c004641000758869103c009401c0740c03114922404540c2140344100415a0f10034011071906034001d208110340011302d602d0400c50716004441c000303034032521452200d004c2c04200b0414000443c00086010450506109041d8051038901e0641c0c20040841d00041c00c404d1410032a003407034500410686c0c400c29055020380c8002e2903100e08101120b4062080e4a065031180e55260322030720342d10000040b060400d0060b031504802c56104003080c2d0a0303000410000542144040d0380710300428107140700300c1e2420000750504005d41d46075107856540350500282544c020351030700d00c00c64002c8080140e07181c40e406a090241c0c3c0e4010103144032100c4144625000704800403800304c0d44000310b5440c08010304d14100600c00e4a103400d030381042a01c1c0301c44c043d12088100340c81100040e0f110300d541d042d401d9120072005400500c80e0030410000481500015817508003a004036518400c00181460014001740815480c02e900b0b8000c1c0230390390500c0e401c5036040d440f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 936194829 1250 936193579 936193639
    0x10f03110301020a0f0c170406031b080108031c06080d03020306030f0a02010c0b0406021201090209040e010207080301030f0201050f0c15161205090309030a0c080606010c0b0402010302070f150e0c 86
    0x3040c04003110400404a005008841c500790307e0703c0c2c5039643e0f40c038010090004c40940d2108411507003131151000f840348405034182c0d1702130401076281c040c01d0f09482040801c0c4140040304076a0790303078021400303510a11031207680c090542d0b000760b100e04003c1c0400d81044d01040500d4855800044408010f03600204980e078410740180004480b99100d081074000303403041011581005091038000704030a0250750280c403003590141c034100440106028030908034810060045c1403c08144010000991381040c880b148a01c1032501c80d0824600306036800b950b411400050805401401940c480d400c442642154004848407a42e01d90080585000d070201814501c00c051654584001400c2c0c0e410410850b0f20f03520000d003c94640707002905000c424422103008e040c0da2030181001140003913200c0c9442948031030b00000d00c5100c070744445d4015002035221540803501000b41d00500c4020840b056641e803401d05458501103041c40700d0000031030a000c0704a40862180850b03486d46c4028026003111054220 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 936196079 1250 936194829 936194837
    0xe01170a0c0b1c05090f0106060f02030d0c03060f0f2301120c020c101d04150608060102010612050f0d050f0909130507260706171806010f03110301020a0f 68
    0x48500c20f0840c0d884060703150048080e0303003442c0a12070099800101401940110b000800249884e400200d0b080f810540121005074814044085400d101e980302c030080700c019060000f41c0740d0f607586c403d41e2034510a0b40322455a8001c80c03c200240c014480c01080300c44042d0303421400c5681100000791501d49110390003442c1c80d98420700010514001c02130552032032002498140c2566481800070240c80c80440550a080e1511424000d581440e0251400d4541d078007103a00c408500701041140ea24600402c110f0466484401c002843d1410b800501102c60050b00541688290030403da0324140c40055088108201080000e145601c2d04e4103a8003003110490304080d0716111407029900e40c0440002c00f408a00400b040002d008603e0b405c080c44d00100409983d4605a0002c01c140e103032076652140e107000c81c3e03040e04000551100c02c010541d101e21107589035404039180d00400d926080b402d070444810030742015410301c10300c42100c1c5d645003103160480080d4500f0030206001020b000b914411f8800b40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 936197329 1250 936196079 936196087
    0x90a0801110a020111090d11030c12010905104d070302060708510306011e03032d051c0b0a030f14010504050604030e0301090c05060f130e01170a0c0b 66
    0x69800380402d41180d0b0340146800bc65038445045103000300401c6804031540e1103103190407a042da03514054a400300506605041038803c4500c520100d1200c0d0715040c0c00c0502d000c520881c0ba480050707000c0e8410524804109440b034030700b0b2401920740760300a8204001d0100741001c010198001041c500030040207512101522400d8012104000105504e1070750400c941801100c806160420b0120b00ca2400f102280e04c540da854200d4278860080700301c00108203015540030700119018428010103904002e41040701910380305148001c042c03181101c0b10020ba000140401d042460004200885000312410040002081c0015050603150300c070040401d900d4031003c0051181e58250303051a419004001d20080c45c00e07140c016215101103800700c01150303084604400b10f007414807401041c2d41d44003002c07240301400c000070030006400014100281c25010809601c640403c02400303002055641214195075061400748201020450103200e1707039a01401586020031100c0302501d0031241007005807556 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 936198579 1250 936197329 936197363
    0xe0d0e0105070b0118061d221a0a1104060c0f1e1a2217090a0303020705030f241f180506010906090b090a0801110a020111090d 56
    0x290082002c05449103a5010001580022004820340c1d104039141d400c2141c19100c07900c42d9440301782610180d40342440007001480d140d1180744885000c0000150380c001d98041c507510b01c0c040b0034094140000e08a404428815001858051205022151029142050f04100740100349010b0b84401601602001c03200c001400721440e0384004a032201241c1e480d02007401d00707140e084400c0650500e8000c9814400144c1401480560b03841c030300c0c0b50380000381c18441d503c1d1136041e804004c3c4081c03954107a40812058041d0fa65003c0d074400190300c40c3e000f404030103161070100740c1403034445212801150001480010790301400c50100340da1143c02c1c0040d41440d103800041921068014201020a0049100100e4030600c80150035090034074440082c8016070312800111501c252900c0f400c13011030300c4624288012254800076140503c07000c5c250680984e9100c0c415400d40e101c3c2001d09880d08400209110080d50a0040d0004201c00030341461400010001058104000c200040d18101200c0c4034102 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 936199829 1250 936198579 936198587
    0x90a06091106071b0501020d12020a09090c0c05060c19050f0c0328141605010f180c080109030f030902042d06120b040b10031b180e0d0e01 61
    0x240c0140098041d03030f1103a06a140841c0c458441d0b181c480c0d15003a09a400080c1507100050014044171b8076690741c00491006078022010b03420910b00c0c00c007400001c80300401e65541a00c0303442c1d1081050340c1d50641d40302e082e0070328600381900502181c40040741003000d01800d00503c1c881c041d003801c99244c020f903607020391440101c0d1402480c080601c9801700080d0940c40006801410381050002c0600080fa1400343c0810380d212a504d030508168050240074002600100742072550006000d02c001080d040851080d6004446846040314181c1540b0f15104090103a69103426000c3c0050f10000c120f0583c0540340500b0300b0707904402200c10980c075944044115107868108c10100103041008458805100b030300c880252014620344901c044c80c1000014114079036400020107140c0002000d0f00ca40c44a48034074088103001000e00e1000314040038008001610030f114260180b02c0c91900b44101820401d501c1d1001c903000128038016030038481c00440c800e00108004d10f580340d5078140007030b1b04126803005079 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 936201079 1250 936199829 936199853
    0x111c02120c0a021501081f0e1005150409050d09050d0507090b0d080a031a030d0c0f021c05060402031b100f031b0207080d022e06090c02030a0215090a0609 68
    0x4004c0e0a0800001001c0c180041d0f14950504601d2200301e417a604100304600315084000c0340d0300c2035401003000c80b0080e0f400c0c2d80102e400c80b582d200c0000301400c070000402c064903140d01085449900001c801020907500840300c0000d80802c4440d28228912921403070380d1460140107140e60140d41e003000300c20036520181c1c00d101d41a404811291110200c2501034000c1110001070015003802da490204070b880d000c9200003040e8600c0e1070b821201850364903540b03010f00001f03d0032600718a44540403110520fa000303561a03200c0c4200014000c625143c0706140c03d01a0070107000300424941c1d07441c41f1300f590715881400407250445c0360400c80c10b265102e046001c0d0001044850710240e810700b288007110f034007007042421349800004890b0040e80514040742c0d61140c12041e0404804405142c0c0481c8100141152904121900c0404c03003940368109042150f0046210328056440003c442d060140c050021700c00a89890b00f1400030391516205160300c85180c0400240050b41d182d2018041000c042da0350 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 936202329 1250 936201079 936201103
    0x100f0905031204050f0d020d0b06031c0c0209251b080721030911090a0b19031e03140c030c0d030c20071205011d0609120405010e01030e0a06111c02120c0a02 69
    0x900cc2c105c12080000c1c0202521103416402800100d002030b00c445c0c801c0d000c0d000100078940200482c90100d200072550380d20380e100701c08076084141c070708030000c92502405004024080c800c02c02c2d401c840030446581c001c07054141e08041c0341c100250040441c0c17469440c2030b10a03805980b21500c40c1c2e00c1910b14801013890440a540c032200c4100003a0200e181d02e8001d41c00e8038410b01c95103032092901e5114482e07180303c40d1802070000702d442041030200320f0240040d015043c4030780e0440b41481c02d02d11100341005ca6030000240000c0d5508420f8010a43c070654201d5044021100c03c102c0c66040300510381c99104900a031394101003181c90304020044254484c3c00540f031480c040001c0c4440d50920144c84c0c20040da80c2002a00c035959020514a441e00c1c01c071403c940058441c0f0800c040141c005601030091180c0c20f5030035010311700000e0042401d5014100346a8001449a130303482d80303c3c41201c94003401110030b030400c1c40c2c8184043d002172503048001d42d0f081100c2e484026100c1141c007001b28034040c050001d0b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 936203579 1250 936202329 936202363
    0x501090609120e18041106070c090b0a050d05060c033123061302060d14180102090109090f0e070603090605070e100f0905031204050f0d020d0b0603 65
    0x380800d0204a60302e19614080310703a01c8100e40c3e401c850810102d090f8462402d040e4021810100d400104801a01415010058003150501e0b030251911a9209960350008518035143c111007580740c0303002c02580010b00011a04010001c849490b85580c411000b0081c9185090000c08100400750783c0c0201d5601070385416544e079682c0004113110b50309490300c00341280c0102182007201c00d031541c000d00f02151142c0c0301c8005c007101d40e5440652280e203181e03680141e0300000c6c20452000706d00300034019a07500d2306680000e2525401e000e24091423181041c80c0e0f1002a034414001a0840d0b0b0341304031000111105000003103034600320341e46080000c0071001100352082c0b00e0440c0000f500b0b90180c0054490a0082d10308000d07650300c020060754186804803100ba80480201171390030583d401882c3c0302a1074249440c00c3d03241d0589803408a440c0001d1046a20b0702502d01044c00c00c810f00d0b0144001b00c010f50103490001d42180c030303a07010400b002892003000b80852521400503e5589042101d0036016400e410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 936204829 1250 936203579 936203591
    0xc0b1204240207051506040525120504060e060f0c0a0327030206040c0f0506030402060c07090518100b01090b0f12070e030d08010503030a260f010602191e05010906 72
    0x181541d542d00d01c2500c0d503c10017100d14005081890640700d0b080c40b0b1008103034040001c03550200741c419007603480a00e20f0140011200c10760f0340c8a410f8801d8a1145108a00001d00620100c013500c0c646880141400c1c100c0084604010403030405070b0990310807100506001c00c0703601e00d081e040040307a4601c5601015920001c44c06500b07240d80000c0c0107000b540100220400641c0b14100c0c241450514081e8503042802000410700504081000703010134201b174410785900d42e80311042402501c0d000e403003aa01c028284c20208030407600510030102c0303156066000700411001000040d20070030b00c0303105400240d84041410141301040c2c20031074290601c51007840e0743c01d2070210300c080d01d40d5040756540c0d40039102e264280d400050107030343d0305416650014021810020646000c0b02c1807420500510840c00c01c82c0c6460710003185807400c040c01003401a40220240d030500f00c00900e0080350b8a40c0500303640b8041760210110705031605041001c241003034124841c0c9414181180585115200288802c3c40c0903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 936206079 1250 936204829 936204833
    0x100609020c1e071e1806050a090b0f010f0c060507021b010207050a03080306030a1a0a0c0f020709051306050f04050c1c080a171e060d030801140315070c0c0b1204240207 74
    0x9400306e0252001101c060105a80310052002107a4442c00d240b50003204002c034010380c96009081002401c50f00386010040f041c0103a9412069130300c15200c0c0c0c009a44032804803a04424100c82600c8080030a200400c00c0a10b032200144e41043c0b03a203c0030303210040000202c0c1094406202001c02640c100f0088003501e4504e1031041f02007442100c00e41d1190780b03005160170038584a0a46a143c900d40c40e40203104d0303a420b141c07418000b000e010700078400401c410324403140041d5160061078400c042c680c8080c1e46524180c00c000c1e04000c10004110b11561031480240a8480c4000411fa280c42d00042029202d5800103c2a00c1410742c41e006030144090141c100410040180800c031030300404811f01ca039541e01d6050501003400c100050040c0418070560062010403d446064074050b80d004080314220300e441d049100c0d000f0360a81c0c2042c00903048050260034404207a00060003801ca0b00c0c05a4035140001000210010b00600004e02292078440c1032800701071850803800b031031094110110741e10302e43c034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 936207329 1250 936206079 936206081
    0x8031e0c0a0225120807150c120902041404080703110d0f11190b04050f1209090601110316140601080309060c100609020c1e071e18 58
    0x512814a8005640400600120310a5041e00c9400ca8660000e01d9030303034038916500701e0882180704024440d640310300303000403c4600390107186042402036010681e40c982d107051008101c04401c80f280a0b2605142c01d0582c9285d018010b000a50415007001030907000c1c40c40010054a2100d1041c00420105014001403090160080c001288280c0b10500500c00300081c81e078950760703e00d000c4804a8407140b402044540101504075100c1d000c0000d80310040d5006003040104240e461095550704110003c0000304042040b5805500b080c101c02000c045c894515400c61610507036046a0042040c800406c0e0180d0040c0396410190361181c00341da89aa10f086103100c0c0d1120301c1903041e00d007422442d40c5c0420702d203400305015050341d082c00091440c010143c014414a5400407648180e1072041c0624a040c0070101c0c0728103000751280341d04c09aa03c000b656103080c5092400da40e14610111030f07540600c902040040c66104844052402d08410715140d0610010b1400c143c1c4201c0856540401c21740410841b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 936208579 1250 936207329 936207361
    0x30c19110406151b031d0a0b0f040f080601140f03031303031d0d0c050d0c1806061d0108041e0501020723070f090209040905010920011d0d0602070803 66
    0x10366511392420000025030040044120300503011a102440f00005d282c0c0a25824040500103030071411200d40d100c10488007684030005072005032078041010720010000c1010500200804001013240f541000e031254803403003041601e9071103150040100c00712602c1c10b10680c1e60034907030a1014981e42e0796908000d80103a1501a003c00d031500c203d0215429860070740900c010964104494003c403034200801d20140c00040d107000e503404ac54a00002885490388003036405000b440312004a80a4030f0008045c08814035018038842a5481e0024011166448103602d40c6c0140c01c20301942e00c4204203558003100038a064000781c21540001420b109000915200884d0501956903c81200900008864840703006004014068000344810811010f40b078014005014009000007002005565101d0846900c0e80c0121031488590443c102801c007a00c0741108070b0700c07080c2000085140b80841c0401f4020f0514801441010710040000600040e80c1c15240015800348070b4656908003042548803000d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 936209829 1250 936208579 936208619
    0xc120d0b092406040303021b041b2c0907030b12030d060f0503010b01020d0503100b03041406010e07050d050c0d14040b06040b010507110112020f0c010e030c19110406 73
    0x1aa030000c5080b50414034201e07002c4a4043d03014084072031480d1920407050328219a043d07842a02e901c09035001d0028610031f0840703030070151901c0b9100803240280b00d00034003000030100c510329580c070064011034440020075540034036185400200800003100041400c1da280000c4006031202081c80241c001c81588000b0039965a22101c950003540d07201090701366454400e886006800c8624140840e50040c0060f54029a1240e000c038441a103c6840302c600f5081102c0c141d940b4a07281c0388500c040f00c418000c031030140c407404452201134030b01440e01a0003071080c803440c01381030303a035447c0024404c0341c120007a60740000d999003051256092440750300000000a440c2030717030344001a1000c1034051a051254208995068617500e05098064031149104020400807a045c018070203200340c10b00720288001c10407464071410407034071049a1070b452400c490210242e400e0507072040107805140c100010341401a14100500810309040743e2403c07149a804090300e86e0380060400740c0114a200301c4003164001d140d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 936211079 1250 936209829 936209881
    0x50a06050a05040501031e080f030f0f10030305030106050a1e020c0a0f03200103020717030709050d081e160f0b0c16030806152205060c120d0b09 64
    0x40c2d00d80c4208001c40f202031000400602c92442c40d5440407015414101240d030103002d45074180b103625401015941d200701c44901c00140804100400c1d0307182e203000d00b0340004440c0c20b16450b90b030560383c000d803d52106006040910401103003002c0c0c614843d2003620050500020b40210349200500b0203507a400101c1185031081c4100760300415025556401c0c542146c0d040051200202c49501010500d4105c03109054101340d020040318001c1046a100d42603461880c50f22959a4a41300000901c013040c1038110501c540420200007003c50030a0041c0d6100614401e080b10b603104944009030003a03c110170120101c10b4454495000b03100070340c02d00b05885406181030b102e06580b4030482e0302091003451000c901c444081a91003010034400d81501e070f0f105074003a0100c80b01c85440446c04521350408403180c40e00f00144965654071541100d0b400d0010101550340a041c000007516058981001c40341030880f1410104426440140d030380c12586d17a40101511000c258240845014044045481019407613 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 936212329 1250 936211079 936211099
    0x8181f080f0907031226040501050a020906120a090f051c0807120b0616080304140a080a03050c09150c070501051603050f0c120a020c0102011404080d06030501050a0605 74
    0x1090322442070521842010b000303004407034215610810103681401c0c0e960200203100014245601038040311607514644020110818545450050b003540c0700108640d110078018460003200c2e859042c1900c45040044a1102c0c0725624a8142002011309000103000c2c5401c2a0758481481408a807000840d00900140001c00507581c00c26100b844040c0d412900141f00c0c0c0d0200541400c1c2540800704030107008080b0f40c070b00008240800001498000c007a02e14200c00010322042207224407082204401510107410821403a0310346500038040d0b04040e006140e11100042d500d10003c4040b01d013020002002d841d02c244a8040c0380d15a0b41140030382840520960401203065030154007a50b0b144c2c407200785a4480034605560071103032504081007140003004144100c09941c9007d104169801009403820360306e0f21400e640c0246007202e0580c200b41036901d00510a0702c860a0b40c419951b109821405403540c0c0d804505089000344465400030700154a400c040c445140300c00d401800c126030048614483c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 936213579 1250 936212329 936212341
    0xf0606140d030309060e030c0304060207050f0d02090a0b19050f300307080a0507031404050603160521010503150f07081f18052208181f08 61
    0x4558544001036001e0580d110320000644603800c010780c15032142038080340102080102610f107800600416426810110341800f030b250f41080f40c50020b0200710303100c184003c10b05002c61410041d13074802070300803041000050801002c1da0040c2849a41c041d01107420901c850000c0800c248150140e1480350011100c9c0640a2400c0301401a500c1440c80c000188180383d036102c03014601c02c50806501501060042c90007080c001030103000c6e182500d449041c1c0e200001d2070010710030644200c000e00b03d10000d0000740515128102960ba000000c51342c00070810401120079542401001c1544405410300d880140070160b0f1114001c0c12a00c1c02d80880d0f06609000c00e111a051804644d110340220920700001d002e10f00c2f840c0c40c2a041880d280f10509450351031003201c0c0e02c00c001c51b00480d02001414030841d031009194407465071f1024807160f4440507403a140050052111200d031000c4c001c1200402d400b01724503507000210307180703280c0105420001b03046e00f4008000007440c103052001080385000002c035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 936214829 1250 936213579 936213599
    0x504030b0a20030a060e01030606030c320a03080d150602010b0d0f1b0e07120603080306090601091205010b130b03120a02070b030108061503010605130b03190f0606 72
    0x4030b84100c0c5010700300084800c494040306410060512180b592905000281d40c42d203100c0850203103010303070f0300403a20b039086044c003a010785029407298064061120300081000450700e44000039440d00304400182420860005100c2c3e15660805440100d0010b800e000084150740485a07004040c40e445e03c4075652124144d080721894414a9005a150802e240010b110402c20046040c0704842440038075140c8402c1000107030250b0032140074070501109025580790002c182c0c882c04401c035681441080d042d5941c2014a01010701628010b440b20400320780c160780102d9142d0007820249048501903003290820740d01030700b02c1e415401e0156807511040d40802c081ca010303244114801400034680e003407607010846199884400004214014004049045c88090008600a000000040c00f0b01c0c00c054051542d00b04450030074501c40c0e0f140050821a0317403a004070f40020320780c61100c0011100c0c0048040b0b0b09140d10480b04c4004c5c0801c2500040810948038034440005020340401c001143c2c861124032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 936216079 1250 936214829 936214841
    0xc2b0e0114070204020708040905100608090303011208030604110c010f110906030f0a0912080702100501061e11161a040303020a02120a06090c0501021002090d060c1e0504030b0a 78
    0x800075040402c040c1d009418150002e00800d8400c40146140a83c0e501c51601215000e0313502064440403007900304891030303008041d250002d40c0d00004d10320310b5140418130001007030080001450580084005501651958407124200b04881c0101d0360300e0010708029402021010040d0402c503181241c0d20107400030140c240c0b1101c0c2ca02804461440d142c10000748440c1d00000c01d4a46203d03258000040011070400f40480ca28580e511880c4039401d250740c01034104424000880812858900100030362a0320651030580c42c884101d1510340b07500a00801c5540ca001a16400c01910420200384a00982c12800d4000c0320b00030b01c541c46103900c03030448043c440d20440c40080e00607404289440094504140120300348000344084800148580e80d0715020366440c0c0100b600d00b035031208401c0209580522040103080c021903021403800034920000703a100742c100d0740e0140c8100c1d0307140c6100c003100307000382000c4a03115180d80c0b10710301c4407640200081651384035001c01c407440702600010401200c8540504 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 936217329 1250 936216079 936216107
    0x4061101062105190614010509070c020118081507111f1508012a020a05071406040305030f0705011a18040c050604120605010e07020706050c2b0e01 65
    0xc0744125901c0b007003001d001030300c1a00f80c8041c0200001240380044290f07059910510075007000c00e800c0e1014820907501d00701640468003030f20136042000f80e020ba124411000d52642400c0000c1c0d03548540c1155244111345800c603004500c00c1c2450080c00c0240030201030720650056903030304500d0340030000301500c600040042c2c083c08009200c000381201519000b80c110320742400f10101c0f00344d6403484200e080d078241010010900011090503c14010341034104031030f6850500080042014650b9015607aa61510a00c3c100d00c0040210040503520300c0f00f1a001150400104c82d260000541040d0059010080484c0c8641c600a003498120354804c00c01401510000c003480d0104040c00c442480d6000300410894000c8600b03100400c6913614000a0405805c4403046030007a440d00d03140c498121401a0028606082010100002a54005401c5041e42c80c18501180c8400b000440545018410b050382000c200008001010040006485104480060780c0d0498507520850040d540705036581e0711 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 936218579 1250 936217329 936217349
    0x15061b16050919110f130501080c0d02090d0206070308090d031104060810050301060f1d090c01120603020d0f021f0203031f080106090e1606050a08090a0b0106050406110106 76
    0x1825078142010f0308078204403108020659a151070410205548140020010008042040b01203118202824000380c0801e0038008864180080b40318480e01070090f0031030300d013030700011442240d4a4207003001840c0da0340030304a16122001741c50050440b003021030740030001d8841c8100c003000c0345d0310034007a21504a200d004624505800c1281c115480140103102e40780d21030080000042546013403040e0002442c06140d1146079900380450f91020840008001a5585044007808420380d4007050101801c036007420012602c08401c01a00041c0682c0d81c8042c2d4001c10701176000e403d2199008528112901c201c40d0100d05448012160b44a04d2b01007105000692080c000175a14101b10510960b07401d0040c0030460240340d0341d10b10582034601c1c0d900000c800c01d0b01c500e10545e0981e0100850f41c80480801c620540241c01d0445c024068011a40c005040181103004504000c40c14048840110382054a01d01e0642e15101d01418070f0703101c2d00c00c100000e81c11096802c001d820620030780e826a501000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 936219829 1250 936218579 936218581
    0x16140c0906011103130b030a11042102190602060f070203161211060a0b0a2315070f030e130e03120403021f1e05010b030a0515061b160509 61
    0x110f44a00790540388000601c0104480c4543e4000e24040500400004218503540c2ca0602410310035035074126070f40001070600384400d0106d50942034501a0b20b03501496000d81c00041070000521082100b04008090020034102191880d404101c1911911403100c245600d5190f900e800c0744d41e403050706030940e200480c100765600018040000c00c0c00c541010700e029040054040802c6050002c16240c0b0300e0368a64540700c0020505100104400070100c101f10080340170425140c0c1c6a05a600d0700c1610301c40c0c24040c2142c20380f28a66000c0c0d60500d50000d0507100b140b501845c0207064481c4a0910700e00c0795000702e812051a2017a40102c0843d288000095410412900d5a28041c0c0602400860540c0030b0008101c20b8441070040003804e00014500c0400d0740841c402d00310f0748010040f43c0c0701e1001406d00c0300601c038641142c0e0481c1d801010000300001d031503855848001c3c4030b91940d98070300e03409000000c000411341e01112243d4040c810000030b44409482c101c0000010360664450305410100b010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 936221079 1250 936219829 936219841
    0x618080c1225030b06060427060b0403050105190b0f010c06020c3a1b1103120903060604020304053a030c08060102010506012a0816140c09 61
    0x2084101514621040756100c2e4840001d04094072080614408429140d080400038000d0720403c098100c0350659200d86131504000c0710880442074090300c1c0c807510340107444132226000e080d4132650043c905888503585490310ba141039800391109580c03400b040480026a0103260650307201c0c058001c04000c102c0030400d110700c0015142140c4c0e21405840c17555080c040c5480950051100464920900900c0480b00080d14090f0a1000c900210042106010400c940c0703996044400640801102040f07600214101d02e840d41125881003020b40e010b0080e0341440c414240c0410241007503200440a4603a00c2d9108010312040b4002214090304c9a4070058181c98a508000d81c208001c800c2c209000005003284c204425540304000e0038000000d41e10020b0907040c5a0040c1c6050b00407600340b00030301490802c400001c054480c88401e11300c001c5280d06580501e02c201c0c0051840107a0b01032091030b10f4008554205c12800302000050f510709040d80c200c5100342e0400300b02c100c07040c0741c028040c40c0c046d1220 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 936222329 1250 936221079 936221089
    0x1508060a0e13081b010504051e0a022e0e030d022409160e04060518070306020a030b0a15090803070f110111030d2f030408160f0305040618080c 63
    0x40000c0da6420700402910004c0c8804844135000203144200104050615150003454090352a132195503401c6141c110660540002c64452502d5404071003851a400340701040c8402c00d040b8110421048140d040c0021210b60404081008220b041742622031402d040360742680c0b1440700310902d404050404000c1c450b070b0401c0d0a282900a000001210f010195440301034401c804030703800010700749036081c040108101c010301542d03a120450100c400404400342280c2c1b6275401d024040108041e8010403901c189030300c681d12411940800a14680d86c89564220742c0280d0100300c0e0412002450400010488bc1c00000465907420790200d42914400256103034802ca5548600c441c0d410030142110200c040380081003d45074070705440340300080c00207a6089001e050380074240c10030034241200c50110000721010055035031150b0403000440e501c2410362045504c400c3c1000300181030800c070001501c00d141c1c3c400090825942203840c1d6080a5150540303d65030102103109e000da440d8000c074a407246504203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 936223579 1250 936222329 936222361
    0x90703020a120903051204050a020418030509091906030804030209010f08030a232101050a05010f0c02030c09100e06091005010c0c05150901091e150c0c1508060a0e 72
    0x82c034100c0e040c58058000446e00c044203603815502c5521000e00c040c19440c1604c00e6901000600182c030b0720003030080d540540749001d14440d55201d840d202d00020004162442c59a00c0d0088c02034080202d03980344e141c20300041e0000d010a80c028848000046054440b00c904002900c000c0c40081d8100b4000000407212040d203212110211580c0006051400325008090b1000f02000480b41188842005500300c48007416402244031b051503610400569170041d80d115480031903850007212040e51400442c4ca0100b13640030168100940000704049440540910020340e041c80815500d1a11100300b0040c8201c4181e0300003260040060303041007590300900d0f00c1c0d0440c611a103051403071565100300140d4085419500d1880ea5500010803c400d0341e03000f41250041d100600032540ca400b051030000504001d107008011400c4940c4414050443c0104041c00c2e40c1c9901940c1c408509858600a04000708042c08040200c0c174000041f460345c0c50281c806005480b690104003370035540b8082000e1070003103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 936224829 1250 936223579 936223583
    0x70e060328050601031503020f150405060f07020a120308181603060209011103031312020708100903030b030a0b0a0f0605041505091e01060807120f0902090703020a1209 74
    0x18a01200c00c1c0c0300041090300c10707010561040e00041620307002001400b50307589180760308010f1040f1a41480140e48a540d080d51640040c1c4803c0c400d42c94050f80720205118980045520140c0800c6282d8025004002003900900c02d8070101d1500b03035540029621071001e10320042c045601c2c040091031080742455400e1034004283d007107071202d8072540d100058510058009582080c0c0006500d880340d41c0000800c40c00e0750070385c00214603619150a100d8290310000c8c000422000b2403c0104584038401c209410203011a501a641d65811415031030006201c0c055045011030709140a1b140c080ca001310b245032500350040210741c03a40d55100460402080007106e95a034040d40d655002c12a62207030b2250541403200c029880344142e05100402c1a134141c001c0c2005200499041312000c08814514100e044a015080500040c2c58980c410f41e202d89840c1d4500150a2a25040904180d60f54100b50301ca20b0007507038811307540d0b00e80c180e044041e8412408007001103a43c1150550f04000281e1101c030740c844c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 936226079 1250 936224829 936224851
    0x607020409050a1b082104150809010b0604060e010f021c0207170a081206030c090c280c0f0f02040e101b0c0b040309150c0b0f070e0603 60
    0x10156900280c12a024400103a959078018180c1c60100140345400310319a80200210151903450a154590342d00c1c1640f981100f0081e40d880300d03109180000003540c025100e80c0041c0a1000c800c01e800030603907a41101c1812240d800c2c01d040c0c2c020750406408484c107035909556252034000d07142c00150380310303d0544000c104521501180011b5a01c0d0288003500c091090360141c1001860201c000706114400342c3c500505800242001002695040c00c8a084107801080d865a5a40d420002810b2684201d50982c1005001042050030381000d0010b00401d041d82c0d0034461803402c6074400c2c0814001ca508401c1c0441c8260019101085988964805041c42803004c80030204180d40814241d59150344030b000d15610000c0107080b10702a50141e203904900591050f40c0345035030803400500b002d4108902500011b0f041c00490141445000b8820103071250a00c151492086080010031034100744c6410b48281c2a60004100314909981d441401142241c0c1c80001c14017003002004459400070349588030031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 936227329 1250 936226079 936226087
    0x30c081308091f20120301120c0b0d0b01020d020c1c051f05071d030a03030e19030504151701030b3d270e0703060e0d0306080604080306060906 63
    0x790b003e880011510b0009540c3d4000782d132050807007018608541000003072081d080f00b41c1041150000ca416a41110769060166035032401d1814042c20b1000d243e005018401c0b80000c1c00f80c0c20340d8558004803000c0000b0390031600600341c094000c07a255681e0000720340d4002e0307400f034105411180800f00b8240080c040e0054440510691096400c0c1346840ca01c40010292108200500e42d0380141140015400e00420030341e003804e841c8002a01c40b052000010309040c2d03996001200300700d0800404000d40b40081c060041c000490401400642080c41502200f02161820340e01031481610b014654007104000c84107143d0844e03403841d80e03070030009009982d201e00c0c48401d04d80c2c0280d1700c60007421400428040031f0445104d0783d0000015030040d0020030b0050300c000030800b9200e00001c400c07800329410020000304c00c0c1c1c10f0f0880c942845410f81c009403030b40d4188070302203e41c101c002c40c0c45404001e080d2010800e0554a6031315645070302040b2400f401251041c00021910f0a0500c0180701000005003d50b00e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 936228579 1250 936227329 936227359
    0x406050405010e0609010515160c15030e160311040e0102090a1701060b0a05030708100503150604060609050919020f0d02070b150a060e060705010516030c08130809 72
    0x201c85003640010440300d4890240303e80d41c102407001502504068500e01c0083d0884298000548501500000420892400703682403010305107201005e4400a0460425107030b0054000b0f014000d02d01200229019100c20395070400b0038212a407048a900803805520101c09208200041240100302c0a15540800c00e1100c2c50b560702140d14043d0902003403101105000702c40d240e0031503200350072081c4c410004105241c2d06075005003c0d2039018941c0c0c6031011181d941d0440b28061041c065001540510071054450819003010b001d07941300740001d0703c003000010364810040720311038010320682d0b0b00f10081001083d219224111014910041408050f00c1c041c0200e000c040d16901000d0310003113003540414075204220160341c00703940144840910311442800f110000e03c0c40c1641d88034400030700002400202c0c00b9261442501c880540010080002c1d140486803400c50b040d04840d40f0340001e00c4c11742c3c040c0c030441c021a01d131800391018106040190031166601e03180744d4408408240d00400403200148 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 936229829 1250 936228579 936228581
    0x50307051c0e04112206080703060b07020d330506090721020415090503160806070323070f090911031305100929010503030711010c171c2904060504 65
    0xa42210034222900749241b400d0001081c2801c0545400c2c01c05040c800c1c1044090306c442c040d41c035041c1d0126100001c0b402d403850103d21011000c0c410b820b50700300c0020081c00d81c0310626103444002c18208070600c10390360f40d001040311070403085944a0204e0755080400d0303c242c0c86010241244002d1600040c5042d845002c0800c402015107a4400000c01e40d40c0203100a05052100807450b101c4400e011040504044031705440700c0004201e0780070565a0048425540c1854000841e00000c01811010908200c00000c042c1d02008007541d01240c0782e42c60010f900400c601c00c00400e21200a0000e0071601c034400009201441c3ca00181c94600ca00074640c1c1c80c030380f20f41c41040d89980c440d18001c403140c0005222044004684218403000e001028010000b5840c04421112415801a050460400420b005031100700b00c159003e8000d840008941020400b52002017145000b6030310b0791a4103242c25003942042c4e4040c038054104002c1c60580b5080c80c490700340c6088a030302c10b000f0000b1564607114000f00b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 936231079 1250 936229829 936229867
    0xc0301060302181317070c08060412030c020a020901080c01031409072303060f01060e030309030a08070822081009020d0b0403031b02060105040e060f07120906020304050307051c0e0411 81
    0x35038108000107006c810040f200ca407040c010800c01c40940180e11f0725445035842030081031282c0090580710926000a03500c00d01484420303541c020004c3e0f495584602c210703560b0f1410041c0d010f000c43d2170080002070910000d802c0a104004600040c04080d082801e2129804250482d102c01108001150b03000d980d0144000c0303110741c480a00c0300b1020f602d8104020040403003c0100c0340290010070418983e510040740010f00b650b001480150b46003450301d003003242c0f03106584c0c0240c40181d440b260410024201d117a0f41c8100c0c3c1c042c0c8115611000c1040f40c40048505854001703500c81c2031041c41e640041e004500b0298003030b001381400102108412900d107210355000082200603044100180901d240c54880c0700b104040e1a8014411850100381c0c841c01c4040151501c07092041200c0e003030300c10708642d811040c917069100000f507440c0d040c03601d04150389403c818001c40f1507014100f00480030807002800d1043c0c0700560340d103c40200481c20b040c4801800500040008124100300302125000f07000291 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 936232329 1250 936231079 936231113
    0x3070806010201060e092d070b0a090608060901180f0e0c01180b0306280e190b150d0f061212030c080403110a060609020c0c03010603021813 62
    0x1902145000c600080c21946240c21000305510030a0520010301e0001442a8400240d042c3c3d20982408144140a41407041200b031410b0b440761761400314020f5901c0002d41004206511100651501c40d8000c0d10b08120071120030380c2003c0c03104010050783c4c440750152509031002c203500040300c2845030b01d00400e44410710484005c65000702d000a000396405410f10241011110b1120f01c0c1905009051456210107030444e4072500303040110760a5400101c84844c6241440e41c41081310545d00d070014620040c0854800300fa0385821040c48490329114010b00c0000725004000481402c9490000025138000805070068150380b07411008080600e4401d00c00a444c1e2085a0004c40d4403501e0506126001f012000c41018142501034440c01e80201c07100782c02982c1810b04485203d50401d20a15041681201401c4d541c204040001c1005030783e1f00800d800c1d00c8180a0354441d0000006050030b0310700900c0020b40100083c22264030003c11001000d070044503030141101d82c40001d0b2101201c4084031005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 936233579 1250 936232329 936232337
    0x20a200d21170c0405040c051b0c040605010318080310030209090604020f010c030e01050d02070b10091b08010e180318180610030e070503030a05070510060e1302060d020307 76
    0x3181c69160008038203400005005400b18240ca445908512280078901ca558055a1a003200c032030180d005506803a5001088580242540c640030509907840c1003811090b0700607882c108003c503545d4400d020b04c10441d1514181c0018112407603a412146602c020840048122581000300050351010111070040d18008014015401c2c207004200b020004440450b05019266507418002a00081b00c8290b14100f401c0035600c81c0e0001902d00080c0c4600500100200a2081001804070f00324001703c0540b9003041c4104581d5280740000300f503a00017401110b000c510300380010801d482c0e0755910182d005c2c04490303025211300440e0400500c0c40d0001a8a0480c84841044c000002d051070352446006c050307044840c0840f4201500859440c441a050283c101038603042107a0401d0700400a6000900018044950740d011800004140390080b030000c0369030b030044644138901312480780208410342c0c0055003951041e45801c03045054010701c3c1102284c01540c02d005e5131450aa0074405144240200d4403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 936234829 1250 936233579 936233633
    0x3191e0501090b0a0810051e070c0b06010311040b280203040e0a060e040b0a1d151b040521030703030b040b01030603170a020705120d020d020a200d 65
    0x2a60710280c82c8160f4202e8001c0311310020400000c000014910030b2800e0441c8000742d035403600035102d03400b10308034803c2141c40b01da864203126405a022000d01811809070101405640700c88004600b81c44802030707002c0750010140000e00c8000030140042c10f80d08a2038880300a000807102c074126001203d00038040250b0004603041042074510203441346d006010180400407a8200081c414032180040d00c040e0100e120540021804a00c550203140e50040760100c00b5400e032103072048075170358606816100b00803007295004515005d021048503e81554080402420b25080c03200303101441c1e05003800a64656291481406441c000703100500000d40259000f08003001800144010f5540d0704040e14101b40ca0510100085031890001c00c0c4c24070b0040c4a1143c1c2c1d00c440700c40c01c038503005a03608000c0e40b24148002403892501c000589074100003441e0242d640141144000b6038a0f15507001016184c0c1c69052200e1b1085251741b2165070103101c0082a02845880d1900c424405982941d0f007462180a81c1c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 936236079 1250 936234829 936234839
    0xa0f06030510150503040f060f0509071e140d0f0c0b0a030b030a02130b13050a020304020319080d09030512150a080a1a060a0e0c04060311030c03191e0501 68
    0x68024014200b000f620aa04000700c040051841c03100800182491807000402d004001e543e82120480c207020300c60502045c240032400ca5100d41c0703a4490200c0c6050200740b210a1030100e4004081140c2c034110f25184842030341400d2043c440c0114608455054032088680300081120b115007000c0c03c00c880045031030303001d07001c0f014080782c8450006503c640c0c840b0880200580d100d03400140402c8030504041103840c0c0e1440407070391200004050030401401e02007008601202c650103140300314000c034200d40182c003000c2100401c812540074088d15408040000c1c0b0410009038200d00c424520a1924a1411544244c15040303680107880d00d005010300c05000140500d040720042001d040d484014200022299403202e4517040c0300ca0245400e484001c00041a60b03980d40ea00d580104400e046d13420261034201c504111541c400c1c0140404a403405d40300074240c10030075094034440d41401e0300d00d40ca10748503c0800d60040c3c00c2e0760440c0480c80d84421a494035078218480046d48401030f404e01180742e505003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 936237329 1250 936236079 936236101
    0x305010504030e120606040e01110a0e0901120804060507021c080c0d09060507060902030c211204050d1b0b13030c08010903090b0a090f030b0105010806030a050303150a0f060305 78
    0xf80c03a5948504040c41005002074800300e0310316005001201c00058001110f610b25006d0110722500300001840802c40d0f09051341c10401101c03010302e0841d0041010ba8a582d1944001180200701602481050000307200c110b00800090a280380010f0020030340580e4a020b4400812041c03404440541000c5122540c18400700b001d00001503690a2840c045401e1039801031003401440710281516481c0c10081041d52014030070754084800c0903240c940014000b4840140610781c0c440d07850b00340d1044000050020500718252030590f03070300401081e12003200781c0301d14603851000d5084400403c0c00c0b0324006440b0400f180105140901c0300c4501036018a182091507028089501200041e4141500a400a0343c041c0048050710744181c5003a884a4000b8030448040b0066017020428078031246002c0140075003180c51a0407504240d90704026951103105043c5c4039100170000810035803062012403002c9004929801800101503c04000c55540b824425400c00155000e400426075840a2141d5065a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 936238579 1250 936237329 936237347
    0x10020406030c0e0f0d02130f0507020d1e030b1807030f0f0501030b0c1b030703050d0b060a12020c030f031008190b011a09031f0612020f06030718030501050403 70
    0x2c0740c01d00c2c800303000e080c40100749201910040300744224402e104207004c40da900b0841c600510980c0e0303c10811503400724807040c000d290698540700980300303c44240400d80c0c410484807086080c09421001060300c0340d601580641900804030368000184880c22000000c00a0034500c201c9440c6d50108080c2a0401c0400803035103980f00031089141081c2c010f101080441c8000350300302040861543d501c940e00c0b22607001401120120b01d125010004601090550010203042d00344000b5004000b0030b10b15004220300b511546983c81d000ca610281c2205003c401035000d0714140801c2000d40785401111201e01c485507204680040050200b45406e110800381044100014012400c40071031180250b00c5054440c40c0520611610b00e0028207203800014008040c0c50244030050102c507020903080c0020480a0342240040324014035143c000140c44c1e5002c9456403100d50080c2041c2c489140f10814011960320040c035800034440e45505c02c1501142c030703500c0c2000039401880001102c1c1000e01c0e0040c402c6031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 936239829 1250 936238579 936238601
    0x4020a08010e120a09030b0c0712110c100908011103090708070b070b0a090b010e0405060601050a14070606030b010329040b0105010c0f080a05040611030c030304150207051002040603 80
    0xc50182d0486507078030300041e100410640c05400c01c2d100c0240140481301d0350102d0b04010608080a81405442c6022001401d5407510541410359004445c41c0e0450b242c0505420480803a4020060404541081d54810300385844c5490300c0004a5100c09440c0d080d030704596000105d15000000300801c03080227128040141c4100000b40c11650300d0040800703c240a00500130700f00b0880d81b008661941c880d07501103520950311401d21340b290340c0d43c1c00c07080324014004c5a0940d087e00402c03002822a621440490b050a18a522030300c0d605100e0001c0b01420b50440c880849040e903031040701102040b40c18100c98000c521413800b9810907800100f840039200c0301a0071062500c2c200e80140b00c000340c05c40761201c1c19a1001e10b004240c451a904040c00850140d080140481d0400100040e8051744540100b01350342e01610f641a28001a011860b03491040381250781c041d4005201240000e03144240200000741d045001500b401655102d5030f007415484425404410740c00981006815054020612415 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 936241079 1250 936239829 936239831
    0x110901020c040b10120e06070f110721150f150b030402090c070201120903080619030807080a020708100204092301031127060918031903021c0504020a0801 68
    0x168410002c610403204ca2024001840f00c404170022200400b540411030281300082112514240104040c6c10502010250400180030206656070303c100015140c041341e034400210704d204000d810303c103100614103a070101c42e002d031600b10081000c0403a006a80c4510017003180001c0a94140b01042403079801c66011404900081c010003015036260091154490410000c04e603494801e48012615020b8500040e018145001d0102c0181540032070f10764821038040d1200c4231203030031242908900c45140e00c0300405e00b05d0304020080000708590041d03c9400a28011a0003e80e102c88206044c100450340c0342c401c4d1a40850304225a892a000e416801c10720b50040c44403104000b80c41c9080300e03005000c06402840741003c3c45d1515101c00420028003081c0801940c02c070229401200c08004ac1035440c0d0348120740a4000c1403c0e10b4901101409180000c40114600018110500e9040314241068004d05609008007208005500002c29125803205d030001005c0c41c0030302c1046000e44051300050020303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 936242329 1250 936241079 936241091
    0x4060e0703050f07141305131401060201090b060607020409021309060605120a020f13020d091401110301060f0c0f14010c050f220506070c14040c0f0e03010f110901020c04 75
    0x1500b1610610341c0084103503106540e09207a01b013840d040c4035a580840d13041481414200003c000a82c0001c0320000600b880702c00e0303a40e07030b070382c08034260340088030301603e2210345030301149041c6007140040144a02c0680042061055038000400d55080401d80350112621141d0000c100a207a1082c400070b40411240d440461310880e886995a84001c000240140350301aa422903558402c5600480c09050605c2990b8540c0d140421002a148003a003c64034034072980d064540c440410b01640e948941190026803d581ca030400448103140045070420130b1080c2c0c0b101c50004a10280c00700322a2500030100c00c9000e84032258003d00f10f0300da0031240c2c410050240210000c1c030109030b04603a50b1070f4064210940040c8072032030401e1200030b2684906d1744452f00058080410001500700012155403200107400e41300d40a0500055076219880e800010740d01d00c243c50744140c02441100c0000c040a40005410810b1000d07440c22614048641c0308000001700f8440c04a44e030400410102d40c40582d000d002c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 936243579 1250 936242329 936242341
    0x1090305030a0c0909050726060603160e0913021f05030714041205010605010f0305040c05010c03030e060403020619090507050427030e0117270c04060e0703050f 71
    0x294040544000b0015446000c900c008900c2240b4a402034038000c0c4040050b418845005081041c0c2200f441038201c002041025992680190180c450600900810328590b00c04000720544c0c030702040701c2828040403040c00d40040d00d030080107a05c80c001d0202404403040d1a40100503802c410202c040d410342105078503594249030700a0640fa004003050030060b40680c144207945445000e5900640313200050380f4012024402c0540100044410a0325422102a2060801c90596008580141c4a42e40c924410030165118800740c080303190281c5000612016106251810050191415401030f80504184500d0080190401801c828111800c1000b100703d81c0d20103880e0760b09071042e28416540d80514030658a5070f0000640c0c4101075030f80d0315031030507202d06d005440c1c0008040c115002490400394175200340b954240281c012244c03103c1003203104200746201446201d070700041c1d0381c00e8082d000e102c0c1c60030388450103200c000e81214801080745180000c0000c046036402007510103035502c42414000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 936244829 1250 936243579 936243587
    0x403210504050a201f0806061905070201121b020106140d12020a02030f1b040c0c060b010905030109080322030c1205130e160801080304060521010b030405010509010903 74
    0x31400d58031072403a0b14240011049243c40000700c04c030068100c1c3c820000c0d62041024825980c034a0790040c0c95044e00d0b41c841c00d0900c042401254030158102188128180c1d0440c0503401403c01503105142c40034040e4020200002504c45c0c40c07007203426103030304089401c041640a005100240000d42031890703070240320200040203900100805007205900b0020041c400303100717000c0015460740140440744d4402030b0700000d0b42c2d5248414020340e0b400c01c0c110301d01900703440c0a003d000904a00c642d03a0058031a026224074000340a40f202c040d06000d00c640c4c001885840a000e0351080300e0083c41225201e240500c0c1e01c00d081c4008403e04d042580b156140d03135000940010a001c0d0341c0b45c2080c07010203000414402511588104900c48026441855000845e982e9903a0140c0c0300e00110758100818101011040c0c80d07414003805200c00540042c003080c030540d4841c1001d0500c200c071032070310b12203580914000010444800c0e00044690200001004107205090044d03030b0700f28501c88020040881d1a440c018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 936246079 1250 936244829 936244843
    0x20c031605060714010c050c06130812060a050406090f050a020705120703032301031a01080304090b01140a030b011814060711030105100501020d080606030c0c1203040321050405 78
    0x6100c1e00b80403071020140080d03034401c00601a49100200700315143c49802503c2c0350400d181524030703441124006050f902040d1110703c41154081d1141e41400c40d0700103088070340c01008025a402030074919001400f5640c500400000f0072020600040384e0210700c1900301660700007080080304500412032346e4001500020226400055104d01c070307880340207e260480c040e000c0313440302c2d03d40f82241c00e0000e01c201410b9120141207034840c0030702c80380304c2a69a400050b1100c091080750016041440100700811440e0403149000750145410240c0c84a804800b00c00c030f405c0300c7c502600090347d60904401c0d55810071280c0e03c450000140f0351018600c0c0507080010121044211401800c3c04500c0c1c00c104601d41001c000f5410f0010024044d900d802041c0c40006003451042074018403549004584050150211a01601d40a030a641c134540d111740c00d9500641c0040c102c0c2e1004d20404170340031481180800658081c5204c0e03501d0350101c2103d03020201c90103010ba49603030051480d00382800002440000e83ca = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 936247329 1250 936246079 936246089
    0x605030a180c03110a0b0c011b0f020604170c0609070f0515041203050d0905010b090a0207050703141e03030702102d15080a0606060201050105060f0304110d12020c0316 74
    0x2440f042d0341c0d00001c90000c03900d07a07119034080207001c210070401f810117411903414a0071015200b080c400070980e080350b400c0c89141400b40960031160205004c41c800d8030314090041411100355240c440c0000407146040c80032100341c02c035500040340902141c508640082c00612085036150180201650003461501c40c91161007841e0324012151010140214141c0d116200311100c1003119402d5402d10901030300300003490501c640c0e182400110003131304510964424541020040c180c40d42103949140c800041a10300c03143c54802d28031201d03410100740c0016214400340c2c402650b101d050508001e0315040108190350b800c5801d00403000d098011242003103c051002c070841c15a0544914034035230003000f00c01c45040400084000200e007400d00000d54400103442180d040103015a9080700700d080307030760030b00134294071020400c106071303415165101031904603000e1039007a0303840e40c10744002490081c41080100c4074210030306a8000515014001070300c00c88825005042841c00301800b1a880c081e0318012 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 936248579 1250 936247329 936247343
    0x302160b120a020c0a1509030e092202060d020304200901060e0d020f0306070c0201080f040b0420090709030302011a011e030f1109120a0b07031d070605030a180c03 72
    0x41000382e00c4d003004240c0d40f2580256010300714072014441d22001c0c0458640a0b004568411802c0c0e50600308005034500c41c2c54401d800d03154003800b0001d50041d412240f0420390384424103014039058030906200850240b8850508106ca00c406110422241c8002242c03140c41091b540c03004201580e0400d0074500614000c54212090004038400240c0c120024000c8540511800e000c0210041d0480a1400958002d0b00c42040ca50b8484654102c048400c072030080880102300d000c10001090328007900800d0740003080c1d0442100381880030800304041103134407100240b81c0c0304081041c140c080c0304900003911b540030b446868003036074000039081b50403001a600b40d4000030700300c5081052080c0c3c8181000c1441305014000b501c446039a0f0b41a903041200c00500c00c50001c11755803075184002411002a80d031249078001b465544070720960040c0f2840506581ca066120440415024148642806030540d51109034490404c0d07042070044400c2524100c805501840031000403505214400302240c1c2e01070b00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 936249829 1250 936248579 936248587
    0xc0d02220501080d0216031101230307021506090f070f0210020f1b0d0c110a0302060c0105041b51120908160804050303070302160b120a02 61
    0x4118080c0310303101010002515000000c114501c01041c1040005285c1d804c440341556080c4501904080e50b2200800c01121103988400300d5000705094040700140c050210352610a0b0607035421268400c032401401600801000150f111803503031521f81008041c0c684075180c0c58440305482c44694080c2104092200c0404c1c4004118402c01106182c02d488203001c3d034423402114118038a51704007100b04c0c000f4848054bc1d11200460000700300d11002816607e030044240b00c0d446113200d84400985080e00000503140c0400075031915030060003042003c0c4000100d528180c144140c941584911903000d186070304508011041d14108100e4125000c1551441a104020301c2d05103e1800307510404c1c42c0f00e689807154900c2daa0380d9450311a81703902139150400940c000b4074a0104a4403031090050040b01c2c10b021100f12510290072400506100740140d034038154603080001d18541009038100c0060f403041c0c040c0801220002c640d2001424030141d010b09203041000548103104008111000641d03001c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 936251079 1250 936249829 936249859
    0xd050408090d031d010f0504061b06061206050a1e020d0204080a0f05150f130501090503160606170c063001240927020c030c06090c0d02 60
    0x3030840d0104100107011441c0d40e5002c0c60003030f00625100030700d0a0703501c920b90014503244d401741601c1c01a0742440d81c2c807285014100181954400f01044241314042101801c88002611034130802c0050030004039401810b20081c50315605030b0342c2c011310050080d800c015041c1981c05460740d4001e54992001005a2103806103010500240a240c2c02a4400d100c5c81c0e1014052240210364410103500410075540c41107100305008502c0712040c1c6201801d4019440014990441400d220003180e20400011030f8820850b19002d107943c014a166840560098110400700620ba10031207005040d20321a8503905001c9041d00ca44801c451785925000c0d0f5400030b4032251206d051407c0d14548090110388204051500b0300c0d000880300c090192940303038a410501680412000200582d800c1b07216034540c40d81d43c1c10404800e0b41e4a81400181c10402c86008030300c180146503001910a4400030710055413540f9141c090390340350240241a811442d0080c100707006083d1940d4001e00b403200d405a13000c0180c3e921003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 936252329 1250 936251079 936251093
    0xa090807080d09140c100509011107060f02010b1503010608180303040f0209180a0210020709110703080c18040b011716081b040e070c05100509100504080d0504 70
    0x1810090107200001401c0000d401c1c55808846007a006910103034449240040c41130707450900102065128510041648425210300d0042028090603d0002c8450300c0900030b6030315228551700480f02198001d1400a840341c0c6c24810505920402c690444046206800e0b4010610041c0914000c102d0050005644c80c95205901c0c0740c010108011070b9903d190605014181882400040703202d5008540801d00030640000c1141c03500510001078084491503600704202d9500744006101507000748840040d01c00480e100328622458403126641e540c440c13524005041100040032246401d07800c0c00104040c5401000d0030120381c80541d40026030818640050390420300805110b0304064a0808124400e8900f40088840b074241c0d0301d5141c0305450b20742c4980c101c8520288200c400150a1104102942c0d10b111002e0700118681415058510b86840b1681080002c8250210050711a0180b010306503041000600440203218200582d040a5403802e03072030300c0392500090900da2514041410b0200d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 936253579 1250 936252329 936252337
    0x20070812040614041a1501120b1306141503250306231f140d09140703120309020604150e270114100c050708100203010512150a0908 58
    0x144043c0303802c0b1031506290202142c0032920301000b100740030002280304070060300d90410040005860300c8181d100780003080402080322815182d40f001c5044a000c1d2250b84501c40e03980582005e01d20000391100b4070050003407030318459010038401d4604104000c644d03085800000700c1c881104440c000d14105142c0b08078080c00c041d80010402c490803280c1e4110000c04072180e1b10301c10000703481e8824086a0b610717899602c0c880700d085070004503104c00480703400010482e0041208104006000030003413a141c9900d22203020b0b400701c00415600131a002d0041c030540000002e00d01d00360345400c0c0b180442c0c030f6010a80500582c40340f1300c100c0b40b03043c44a00b0003600401d001d020b9100003410541345802d1103c03180144d07414400c0e00c2c0d484880c2600010910201e601281c004c150400340920800c07001521084400d10f100314401e075901c0c004e24801180c120780c00d001030480c0804903100580c59506010411891241140c43d440d03043e8089081544449403c21080307500058041000034054840e00f040251441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 936254829 1250 936253579 936253601
    0x4051002040609031209030510090f120509010219020d06052e0f290a051207050304020901081606080903090a1814090705060d1b03200708120406 64
    0x1001060100d141d0f0f9026000004036400340003110701004000c0c00c2501c41481c00d00019096421074201c807916003605422841d02c0c0e922580b044285080720740c1315003103100e40320300008002410005610280f581e040200c0794082410410200000105a0000d207141d241c100009002e103440e034001804c40220f07030320783c2c2030380c7c40070b814400c800480c05065041c5254424064020405144000030031101101e48031401045031441500b070900e101a00310f100c03180c000741c04900030130074200304000d5442c1c0442000ba004840a44841e9201d04040c0304101a01c44140c2044640e0b500840450010619035a550000c5400ca401c1103503142e100d8084040c11485000c80351600002d00450020760640c454040010041207000c0800c110515211140d00015040e600da5100d5031080006018034684032004018628003401d00095812104150030031500300308102e0001300c0c2e0381d022005c5c80301e4014014580c819074444070f002d18140c0c250361400c00398019040b46401c124090380020b000c022543e0701c1014504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 936256079 1250 936254829 936254831
    0xf06040e100312030e031e19050c100e100902040b060c0609010b040905071809150509120313030305040503120c040f060519030506180c090f060918040510 68
    0x460001030418800200d0302c0201ca112100c0500c00b4161446841400320000149016610309002210240100c6400070441100b885d000c026180b0f441701e116058050000c007a89409440e04e038104030b140e040000c0140801c0341c0da8180100062911004940c0019200540d14000743e410401e001103801810118540d9030001c3c0001541c0b10180d4000070418030400b8158000d1014492007810710081e5407074860024200e40c4900750500c004160707084948c0d6140e1000100040c204102d8030b6035002c001440c1c084046c81903480d414031414074424804514803140701203000c2e186081883c1e0005104d4407121001e41016581e40110341005014002c455825802d00f56408050804014204503036000d485914034440d0900c20002d0b10500030030543e0310a030f21104000d1461002c44000340c01800c4010072055210360851000c12500000410aa0158400300c1c9510785480e4900140010190010f1216100b0302c401d0104e1106940ea0144140700402020b0385280c041d19180750807407410442c4a2103003142 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 936257329 1250 936256079 936256081
    0x3180d0e310c050c01061401050306010518100f0f030623061b060106090f0b040b1b010e060601031d0a030c1b0e0f01050405091c11060f04031701060e0f06040e 70
    0x164010084e109402d503682c000c120341503642c45501d1920000810060120f0010320014540350300a4001c1c20243d2400440c1030988546540042c0041070303a40100c0000c1241581468031a5900c02c0515072120018101000f0240c01c1c1040700000c2081d80c481080350380c100f0f80c1140301c29203951040d80ca1000f61468204540701f11002c8254440c5000d0082c1c500003008030100080110024400000311421031100318901414201070458662011603120740c5102821500c908144d824421901800c0500c0f0242040d4200040014107a0303080e50182c3d0324049109882c107141d440c0205030300c00301544c14244038401c02030f1860034411a0841081d076070b4000e1403800c0f000a038003071014080392044d800c0010468241c8e07241d1040004481090351941d081d58171500c140c2007811684042448079080c10700340061680c1e903590086180202c112626000c090342407050008250b0480134402402d010314140b48819810980010100c040401d8a44d01c11041c40c0418691522441c0c00c03a00030300307440b003401045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 936258579 1250 936257329 936257351
    0x7080301030804080c0d08071506032405060307061205040f150e06071b0f110a14040501080d0512060402070b07200115120206040b03180d0e31 63
    0x700d40181c4070b444c885000f80b244407000780c03804002040200d6030000459003090007a8071441a0010809440d4012995030400440481c0700480183c204150040031110341c0c0343c00c0604803082d201c0182c11035000e6408400c0c01c4c0002508001110240346141c88005803580c0d0700e04001ca03d132002020068603100064014018040840d0000c05076540440e0484000b03842c0c3e080f00300ca0359008000309042d44201b211140c0009550400540201801200e43c807200032000c40005103649103d60100a04000c04040b1024a081a0140c4e50040c0041c401914201002880c05000703440307040c401e01514003100c4002046584d4540c1a00c10745900215000800d140448001c0c10001045581407003500a80c0106488008140124407000801e6002d61003102d19185801c80748054040080383e01a04c14003010502c2076284c1e01451155040d030389010208540160107600740030300d41c4810b50412200e070100780d10300c4d00c4104140b030080c50b50558072030002e980601c00d1408070200240244600b401e01640e15a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 936259829 1250 936258579 936258593
    0xf021b0a0b090a1505040311010509010c03060b0c1e0f101e050c0d0b010e100905010f0203070c0b090609040f24050d0f1e0b0109050108160513020708030103 69
    0x6031640c46070164540750380ba40103a4a640f410035103030080c02000314036081c1d00800304903007000341c01034403908080141d050ba0000d5142550001c0700c42d050669504c82d041c0c0200395241c0980401071950149003454202c030a07840d01c0c3c503008000440745013407007906910300b0303440410088940c89420440a42d4101c483c00c0100d00060024036550300c28455401d030103042001a0b40c41414040c0500d030303104900e44000d0f8020107020704040c10525040c0320302803103408032545600c0c0c20300c0c80b40074490b551418190305090000d004080001158002c41d802401380d100061281d00713210095030099000142c544004000295580c8035504100c0e8212b404e14a019050301d180e50070804030f442085d02d1070545141280c0c0c0b0300461000e14483c9030340c84031054502c50003203102c02240e20318081c0124080c5a40056001520290041c1041c0c2200e944802e24010030189406105590141c401003001e400604102544040107070103a004544c4a4503102040090ba42d0596040781c080c19400112140c881da501d04041d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 936261079 1250 936259829 936259843
    0xb0103060c03050702100c09090207050d0305130807020f0d02030109050d02010615090911040b0f04050316061709070f06020a020414061c11042c120d0f021b 69
    0x498503410141c20380d440902a0003000d203d00311320740c02000c40e50a800691000f9000d078520f80414000e4600d0b0210356500740f0300052840601410003450300c151180310003403c942000344400f090240e0701d111400000c00c0d18044030180c58040300c03401e1200802c0c10006071003824880c0000d605601e0030004208111000c07031207607001152500204400396a0b101b011484004450080c2e00007a2039030814494040c0507488040120001381602c0d04040d21801c00020355071001c1981400c3d408041000c2043e45000c003c40e011510b000c01c0c1e020300041c81c240300a0001d2056801140402101600160000c5010418140101501c03003001e056143d403044003139220740c1084030607170065003054596030081c1c091002c2d031400f0b00c0c006001418550034401030340900c050302c0079080703d150034104400b0130382d0341d0b80e13000b0164110303e0102404048115500004c21100782c00302c01c072519070002c4060010301c10008003541e0640700402d0780801c2c1c026030b14003144020702c6113141a14840a2391000101c29442c005856 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 936262329 1250 936261079 936261083
    0xa02010f14060f1012111b03250c06050d0902100c0b010e2e0f03230d020738030103140c0901050418050106140a06080f0a021b0303040b0103 62
    0x34000254584140076403040040200808207405510305010560282d2140c402c1510400f06c1c2420083c0030780c02da600303820300c3c0d400184d0f040d8400300b500040c036019442c035a41680307084440303021024160303502c43c071084003e40300359810721602050740c546201a641040103d964020010b5034034203841d41d0050b043c1e1035205c07001d0f10f00d0880c5400102ea104d031804449030080d0380a2402c81050f20078005000e14400356080c050719004040c0000080a0320980c810342c01070351184130110700784400b5101d0f06288003201c3d1503152141d030014103050b02d2141c01040c8441900c640007407446460740c40502c600d41500401d01e03881040321801c10a011001401000365050f070b0312400c0500040d503000314950740d682c2c41a42c54560700030741d2580100302504c0c082c2c0c0b241c0790304070345000903141c075042d107464035130840d07005500400311108203283c980b04d540382007400f0001501180c01e203072903030b070030a90314040303006000610400400c3c0e80002c10b085010001000211100b80308803c40e40e0700d241516055250f10000e00c41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 936263579 1250 936262329 936262339
    0x6070f0b07030c0e0f040c1e0503180d0905040c1b0b04140708060f0a060b0a02160602010204080327090702011514010c060f0b0607030504032a0b0a02010f1406 70
    0x300341c20392203155031800780749000704650045031001007080001c003852100e1f40c003880000b501001901221445a155224190311650303200d02c0c1c8190b100894001003441d00c6101d800c145280c12025401400000954078180c1e0700050001002000751424101110000c5040701f255048600f0082d540c010f541c8554801c0480481c41d0111040707070740e545c0c11540203002c00c58008900003400c804101034100e910442074100070540340e030388895028056005400c100d005030401030300c41c521700b03440c00519401410070748001c604e030a16181c0103640320b0180c208000d4080c4507003144000c072000c0740b19120b480b80c14010208078281c01c103a01c3c040e00802c840c01074120354403810440060031003103540d07404041003010b0311801000a41c950344d00d030040c51040b5400618640c0c80c1000489500d03410060122140b20352905690f8a0a42c205102d484e40d0b0300400c02010f814600c8541c03d11200d0703004141c12210422040b549410311481c050b07001d0110880c002003640d180a001c5100000340c0c00d5014050001550 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 936264829 1250 936263579 936263591
    0x114010c051507030216030e090c030720070e0c0a0908010603020a030b04210f02011b14070c080a031d37080d0203040e070201050714070206070f0b0703 67
    0x401540c0c110103128010749190022101d041a0301040c19080d41d01c111107140c0145070200b0039646642d084a1074500b6000551491044d100d0303070a05011030754000a089042c85d0035482c051a00404046c280c10100d000c0c44000d40703501e4404003040211034003821513212440381e04d10300000c1d0074140d5003081e0704030300000e1099140082d03601010b01c0340c0d07405e40b03802408101a843c1981c030342c1303001f0303040c050002c99080c44100c442e0368805000752000c1c00900c080c4d5442000085034504024252000040114424000408043c2d4007079004a144001844980c0005496500b5410030168144182c1d001200c0c42c0218103071801056840402e000c0348015000668000c00083d03000c1c0103080c4601000852a0840f1280000b80045007003110b2500c8403014104070b4040d621410403608000001d02200d01590021405200c4081c481c01000e41c0218148020415842c0190f0300400940c1011001c10003e2400281c000c00d5440e100119004560000501d210000041c90b0a04140070110303454400203107415 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 936266079 1250 936264829 936264869
    0x901141204210507032f0f060a0c08090c091e011401030e0c09010905090a082106030f06010b0703050909131104021c02030a1b020703030f0c120e2701 66
    0x206035150640c241e501c90304011a51001b400291106100e05050324512131401994404204006a85501c00360b015120504054400000b07031200d14140009201c408800c0000c5448005020681d4038400c65001c54a40c03110441d5003494101008031105082010740046280148800e8640c141c140130781c1c0070000142034145481e150f0000143c40c079840002c20004121210040e0441d07504900a10140c43d0b076158156107100e0b071540507180448040740c00d00030380704200c0114502c41c4d17401603064016001c9801509140e64a0305030500480040120103c1c0000074544540d055a01602c1d01902c04a480c0c02c0c07559822884040811049518000d1900303a207051341003d00aa030601959030710801341f044c3c850401fa20103034000800149100da0ba9103020f1382080c10720140d9100610041e00900000ea08608008201d9005400329006220660454000142c40c2507407482110380e0301c3c9010901c980340b0600155070100503000454001003804521580b110f4010b00d0103049803040748000042542903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 936267329 1250 936266079 936266087
    0x60609070c030f080606090a0e06090105060901050a1d041e0f06050d060915290604050f0402160b1e0108160314070b1b010b0102060c090114120421 65
    0x4090014005000b48020043c00c1e401340d40450b812410040070641400b0f5094003055034400594000701d0010081c1d130a11480d424040f00c19805414141d91852414609200183c9580311790f456a01c00c00c0a21a0308a023540210710303540c0c0950740010310030702017003ca0010100c1c20340406041481500d2800310800d20130051f0b07100740c1c411901c010780080c43e803143c01e8580c00002d221400058038110104044614820708511864247d8003041c5109c0464101031540b84641066881c001801004200b005100554450b040f4245c5050110360142e40ca204914898030240080d9000030a05400c41d4180034150114143c000700041145052030a2682d0b078003221581ea9a0103100d08400003641ca60900c08640c074102e41c0c04ca075001c1c1c202142c88061f65059110001d41c03180d0601100f0ac100c11002000c101c41c00e025000244100344010000c0703040550400e0703294450280300c0c60500c00c15541000c4582004bc017076541e20080200401744510f040d0920421003030f850881544075031040c03d030603441c031809 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 936268579 1250 936267329 936267347
    0x1d0a1b0f030c09051008071a04030501020a080405150705033601020c0c04110307030e07080d0e010908062503091a0406050906090a060b0406080a14161d0a020c060906060907 76
    0x460310081955914090175018901500c6c1102380c15583e0801010010a2003400104130b1517500da55070003510721341400c0403810403c003012030450140000c4107200c5080d5010069036089001da140401240b00041c602064020070a06c280460b0861040030800300e000641c0a0015200140e054a8106044a04200c100c0d0000480f03240c840e03e080c800b02d0011442a80211074107102c0c04111070703c103a1a00720746480c0c210900b800780e00056480d502002d165034400c17140e000801411000707060317905098590b4180e0310320304510100011401d05650000c103100ba0401c081464100510301c0300075917918509107a050003210151545414100490400c42002511520030007a40006d416241061754803000075000c000c070002c0d800b5850300380c007292000050041240841c4540804003030481d005004031705100041d00e12071844030080c00104403041024054250fa440180751f8200a55038400b21800240200301c4189140d1040d80101300c20600c3c0090400e0144000712400303120360740c5501c4100d4403031307070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 936269829 1250 936268579 936268589
    0x63603010c1709190c03051002270105040906030b0907080601150e010201201308030f0a05092407060f0504030e04050403021510091d0a1b0f030c090510 67
    0x32041040c1050a48107000b0207401031086016201d0300d540028244540039400e0b0419191a6804101001000010055800c1101c0000e205505128111000101c107441c0e900000b0030092266860b520b403070784104129030107065940800c024080d20b9041c44030442c80c04480c2814a88030740003011404000000d1828100c60804e024442c64082e920422500800071090481c1550740b51041d00283c3c1028a004040320481d0701549034072030300345450000e903034204c6a02c0443e407600100100965100030340102c9070201c10314103051761359001c2e0701c020806407401d02c44030000c0c08003050b00d407540a80051009044c4140104000e100d00d8440c0c0c070401c4100d660a40c0c2c001d0205d84052040c107907500703140c0c10107980280240181c601c04051018403803d000c804a4102c05444d00b010018000400a07218100c1011300302e2118440d03180300c0b80b07500c41d031324402d1042c0a400075070b0301c81e01800003002d98071003030300a0405200b40c0d90100e0754a00e4100c0350f4810900034056000d052000190701141c00c4003205045038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 936271079 1250 936269829 936269837
    0x1090b0405091801060504060b0c0c040501030b071d12070f0803090108130f0212010c0306060c08030a150b0c01020301031e050d0503060d020a03111f080c09063603010c 74
    0x5100e843d5201443c9410841c032410a548500c1e00054a540701d00c1084020030b001e8088580d1101c90701c0096040040c4100c24901c900c0c640001072000c60b24045000788c1c03108440c1003118920390356551a8400e0140352000d242d04c001c80b00c0c0368200c44180820003104507400140040a1240c40d1189541c49009040e1038a002071040000120030748010010052018000c807045201c1d40e42daa0046901e4183c100741000e02a9194a4a150903660501ca407000800c12880d00c02208001507841149501c4050000f040c104c0d1244190b0041d9090102d040b4003c0c00c52100041c0e80703030807495003a4040e41091000b6030703510321252409454204000880b20065610070040c08844101030010b690a0b0006022250045403c880b2640142c540c441d0100185000d4081e650001c00c0315030801000c441c030030400c1d1080504120040740c0140d0001040c0360002e0200000319204c5040d05d0200d51580190400e810a03141d2a248003502d00113150340110300e031818401c0400340354a0440c1410300743c500d4800070b10300003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 936272329 1250 936271079 936271081
    0x140f12042612071a100e060301020a0c0206090a1d07020c040c2c19091a01090905041a010e07020607090503070506070c030b0c03160f1b030c060c020a0201090b040509 73
    0x40c10034000200186481044140034011350155420001401119100520300da100b509202e9000c82c01d40341035003c10100d0080d454210410001440b4005011000713014a00101d12a07080d60746401c2001d01401005280c3c0e00c1d540216900c00000e00c41c1500c4c01d1025000310480c4003100d007054007401c04242841e440300380c60540b040445020040f061280003903556502c0080784401e64902040481c110480d070501d41e44241041c10303041c102c602c01d03200d410b02c0c030f4140b260030300c0340340d07001001c0004460048400050741d5517142480c00748030580b5403400c480c92124800106429401c40c108500500c107130741c2110320a640d1030b038068132a2002d501907150b041c1d00904040080c0e1411100610440703103d881882e08155503030b920041e404105a4a1090341c44021081080b40380c042c41035401070b12003c0c6441d9480305c4541030b000d044159044003c4150701844c1c1001d100b49405585c01000180e1b1140c01000205680304009480c2c003407400c0102c0c005061024002250817a1380259015140010030040803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 936273579 1250 936272329 936272353
    0x601050304140f07090e060c0306011e030609020f04060f0806150a020f010e2a0d02120a0c0303090501020f1212071215050f0d0b0103140f120426 64
    0x419420b54400500b511842e064403511a5091009400410082001254607032141074014104400105410070200f410700402c501c50f079020303c038881211103804110b905c039001200114050b01441c3c0000000e00c0c000a0340a200340c036a48000c104032010fa541e100703402400c0643c02c4540b41016201d8990102c0c00e0740d0f000703070401048401806140503c1c0101c1c0c40402500040c24290340c50004510f0030780d00080f65004c160340a01d900c00c03180c05410b07006c003c13110103540001800f0501410002e4025240800380801e24081000913a400036084080c0d40507031580c1c0d18004180004500a65005010314001200d09031000070708001d0103841c000c0b50a01700006001c1600401c00024243d00820901034200340c1000c0d030503c1600e4640d140755020114150400c411300001042c6440c88038007424056181101081ca0b80f105a415a0b51201e076154485070041d0b80d0743c0c5070104001d0040d02d035004548c0f0500c0310340e040c0780c014800c4400d00320861040000c0c5261000c40402101508042c81d08106c0d5008a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 936274829 1250 936273579 936273593
    0x1902060403020a022107030c1403030c070e10050d0b07030b011115041a010803190905010e131d03070515091b1f02010b031213060e0301090506040f1a0601050304 71
    0x101d2503842d508440c805e98400c81e05a217062020740c026203842034246410701c0040703040c0c48032000072041940214500301000c07503450b82d1840d05104d44519225031034041840c100c4400449802050000d0045c03032064410704156103c100140c60140100c0c3c03400340c03206419400340d0308408212500002810000703404008000380c1c0303580100100d5000c05400e5450b01d550119400c40b902030030920b03009640f05c10310150540761505289682c0780521100c80c0c02007250340c1e400311000ca01c1c6e100c25a00785100c480030b101d000c000b60140d19801a24440b00e854201e010006c0003014040c0d290080045418114803000c881d080100107403140031840d044100103166005c800c008081101c04080d120101d000d0541c2071112103c424500c01c4070050751144080e6001d4601000721038240903204210340c2c07501c3c000361458440c2d050b007880380c14180621401c056071281e03000e5001d4004d0f84d4028090300e2540c5402e1415488401000008480c142c4070b042a28288001500109201e44410307140c07545582c440b9140c00c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 936276079 1250 936274829 936274849
    0x60e010609170304150915080c04140a030c0b0d0510030f080c0a0b181e07050f061204030305040c09140403050c10090804050a09020310051908030a051902060403020a02 74
    0x200a0f44010000040c0554000b400001c5910080e654840203034141801041c50540c0f404080301088010300a02001084140448045410380141d00c034414011002280c0034941c25807000e80306650090b80000c98010100c020180620002d44c1040199a0300c00980b8203134132540809010b030440140f400000a03010030081030707141d100c2800c4410141c010303035624078005000ca035001941c1e071511a40040c50740c0100f080c3d4107030504c070700d45088488140303280e40d640da0038141c0714551080244400008880d180c440407103408114610039003a0302d20f030608015010307100a440446041118280009544000b4410f22031036030110000c03110303070391180e4900b11090f420517200ca01c3d06000d40d18500075409418410103560521951b10103484070324280802501081c940d001e2030200340100104021021100440b4040d20404c540c1030551070055000001c800070300b6000303804507120020391210347e1a0010050f00b0b41400026032506902d2a8680498a908094400074050f0340603040b10401460494501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 936277329 1250 936276079 936276119
    0x230a170901120e070518160e01090509040b0601091a0a03050c0d0213050f120a0f0501150608100f18050a0b061803100b06040b0f04050607120201060e010609 69
    0x2d2144048102508200c91100255420310350000703904128509124071600460465582031440503d8040ca48011480d1008140c000b00445580030818682c003030404d84028250203001e071001460107203401c20304440e050b038045001c140070140c00158080081884841c0e00341404d109424030021140990240c6400b0b0712018040400340300880740c28883e0310250140c8548030f03022143c003914000c10b11400c1000d001e400c500810701c0007001c191380c010006400061a07400114080001d076281810780c014109032a40303209080b440c0c0d2001600c65400240701e8000c03c0c022540e1040f060b681c116148031680c0e644030740c007100c0010316000711101115500c6164410000c43c0003084008500340010403962141707a01c2810102a051252403609080004407098416100100a00f04503140010142e00441c450301c1124a00090824404d0b2110408da07001001c02808641d201c80e180d00e0155103510350320115100561a04400150746060012024102c5a06896203c4504c0c2800c10a82c1e00781a5100c203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 936278579 1250 936277329 936277337
    0x6050c01110a051306300b040204061d10080c07110a0f030c0e0c0f070303060f0f05090f0621010204031b1d040210081e04230a170901 59
    0x541d0032030704211000380000700d01c50342c0381d0b80e840c0b00f0141000c400b00e030b07590002800c2003009140240c20411001203801c0400c00015940840182440b502d001b405500064541113030010500290840e00b03c58020410402a10305260001d80300c828810000ca4442d0500001a58980460881c1d800d2800502c4280c1c05907a032500900c540134003045541c8078076480000d10360000c40c0c0c10028030011009110140c4081680c400060030300103040c1e0384600072025140545640051010109030281c2e01440c01080401c6c052420f5541e1000841c0c0000c849100e4180030b428424005001041458891403192178001c001032410507408800d000460b0f000722a0054941d0700b04004004540103058021010b612000c0781c500603414000042c200051180c205800702150070284001079803800e41240450215103081600c1d55079907004c601500c684000921920003080c0c0521003400308510200500704601800c007060400a0900581c0d110a140c40180551580c16003a8201d084da1200401e00b08005240c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 936279829 1250 936278579 936278591
    0x30a0b06090d0c0f1d06040c0504030501050405010501030201030f0b010918200307030c090b07110d0819022a040518031b01060b040e0a0b061b0102030a050c04030c06050c01 76
    0x720b01d141d403045030306903046500c101c07042280c860070031420b001820b40c0c0074401049070032007034101e80500c03405045580f05a48840c01300c062180301d901a80c0c002c5400000038451410039040c03842c001c000a00060340000d04201070540040b14a004022001c041a034903420740514041c000e241c051200c07a10703845019200c1c0044042179088104c0350b081ca0301c051020b00c0e6130b03090002028003110f811050401c01c9c4641000d0801501c00140243d400e80d80e0441c048010342240e0000140318400319100c000d01c40200880c3d40c0003071500200d548034840065808031540141d60340d03025241c2c080d42d6840004060042c103c40d0740c1c0c1c1d0034540c02c25600202541400e501c481c01151000b42560490004000340032285410f2a403400001d000b408003c0200b08413440c500b5007032282c01c000e40b08008020009958980c28100ca143d2500700403200f009581990010114114981ca24041d51042e102c0040581c10940407035080141c030421201107030790000e400c0c60594504881994680c000c1068250380b03540e614 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 936281079 1250 936279829 936279847
    0xc040b030f0a03030b03370c0e1f08010501054e06010902090a060c02011e1808030f0a082e03051902030d0e220905071a030a0b06 57
    0x42030600c114400e880c00300c2c11440b88414103103003000f0582c4c89107260340525601111603100302d5130070072210203201a24101003000e081c01c00e221423645d070103100c10250a01c1081400c0004401680e030000c41c020b003041125588031400341c241c400038001c4607800b152043d080b105511813900040c40041c51425403140350302c2c446010f1001c07042c0700c1058071111480460064500c2e4000c2c4101ca000d880c030000114100060000854544201070250b40240070b43d0004c001d0540e800340002c000c41d1541080300d60005d00042c10024100c0b503405c006c5940b86020041c0200d01940044166000c101107048000c4c10a00400d40490f001ca01c042c01004017050094014a00c00d8444140b48400100c00c1c0400003d940c65454182c3c68842d04440401d0070f1000c0041e00401664085403080b805030462400c105150b140400040c852004000540d84041c1c0d02a14801c84e0005c3c1d0b00960107060003002907909403595204801c404421300c0c41180e401c1ea6040000408a40f078640c00608201009041c69042108d01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 936282329 1250 936281079 936281083
    0xc0c080601060e01180806130203012c1203010e0c071716150c14030c250308072a111822170c0307050706050a0e0906030c040b030f 58
    0xe0b042000015158540c1c2c0009580200d031454004034544185a0030300c1c130303108000b61200400b0f05010640700c0030420807400d568017504200d0722aa504050100300030a041e560f02000d42229111f4400e0f03004180d0202d502001c510180ea040f03c41c07011403801380d603844111200150340903a0040b90038400b51100b0154a00c0804090040405071100000b2107581c0c2d0706203d000b0025013040e03034101c28104070401410382d40c4004d4507801a800c80140b10f460307031284008500140a001a03411109000c05140312a1035006412900c3d40c03030007030b114103a0507150004115a0100f003014a624079078103020041d0f101400c0700d180396190a000b81c0410340c401c0400780001e030540f030410100d001c990003a0030034010240075030048072034041d2202e0000c83c3d042c440e43c0c1c1c032078a01c4130f10040002542c100104400c44c0c01c810602c211a0803681c448203664a960301c0e42c00160507074229001400c0010380c260741380685030070f10414050264400400a098041c9840701f0000036201c242e1400b0741600a45030f460743c00a00c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 936283579 1250 936282329 936282331
    0x71a0408160b010603060f050609010806031903080f0901110f07020604050a0e161b060504170703110d1b0204051b16140d0f0f1403040311100b030309010c0c0806 71
    0x200b52070044041d4900380c401410f031241600100c20040e002c00080041d07035156000c0341c000c807070203007490b07030700c0f0380d55480040c2c01d01418600011484d400159105e080645c01125540308910030202c6249503140e140740c1508a404c440d42035840311104100c0241c01c0300c0d4001c058503885100810f00303481c03d40c640d0041514001c2c1a48150130b0100075006200c038409070841141604440d030b01d000c0e2101c00c030301c400510141060440c050055070344c480c081014401c00741c005036140b00d4201ca00e103640e240780f85002400d031514a07028003154094441c0c04060240305505030f85014002e404548950307a0b803034007040010301d0054089201c448030440f0740c41c140003000000d4015030503982490010b009076411b1404400b10300035440c400c2d0390445013500d0382c0c41303422034003802c600d0035207141541a1403403a01d0191110207000061101d01c03000441000304042d48100c0c40d20701c0f0601070701566010a4840081001d440584105a41c5600203101c0091036500c14016030306c225000c1c0040a414507079030701c81c40307082c084 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 936284829 1250 936283579 936283583
    0x1060b040311010305091905011b0503180f060a0e1501060509030d020705090f0c04030515072d030f020f0d050603061803040303080a0b03010e060108070605071a040816 74
    0x4089410420300407522044a8403030b40c282424403d81c6060325002e9219803500c054100507034210180e03241840801d6200c80740d080141b0040800d0145468009011501b08641d000500e4040465200c221000400c1c0360b403801041c00000c003410b1f102c003019038010f0104e0341240a40c91180c0c81c03800920701d0386401030030b009140039143d05030756003920f009160030005501518000c0d5480100304001d0340d191521602d0340902c20b03052500c02074070707403141c1c3e0a0315200325400908a40f00d00c3d501a403a0003e1184818000d000949850042c066050300c01c0064018406400c3d8143d40d900300700320703041806500310150340603141000610b400c80102c030055070744e008440052540c69aa600700b003141d003410880e5a42004041405610342c106e1642c42e03594a12071404010204941c000c04148085d0180d0080808080e0080003805509880f58009940304da00340301d4164540300b421400100e0034003032800c584140350810002e6512010b007009400101344040c00c00c50384c1d21810407401d01840158103400e002d5074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 936286079 1250 936284829 936284849
    0x12d091a0a09050f040219080921070b060a0b124006110d0207061a0109090e07030212100b06122206020d0605210706110307050106 58
    0x40e003800d51400800151151000c0141010004880318a4010781c004040b260101d03082c40c94003c20f000441c1c042c0c00b810155040504500c15040c20890300200450721500c100400c40d10700d80260f440c50640078544513441c44503180308110080100301c0740420680d02c103001606140c6066500da0503e103440d40408022a001c414020a0040c0002c81444d24038046100e2585444006888400d9019801900e6105552483d01400541c02c01c865908100181c0e82071000707180e128626550140040d50010604580c200d140625000b4100940ba400350030090f01a0b50b5402d0781030a00700508010903d184642c00d040c402c1c000004016035421314109100202080904507c050600d020000d841107a6a11403194005010f1800c01400301d005040c0c0c071516000c0d41480035080b9034042420550f1890700034001a0001500403424101034000808491041d00c0c40241542c001070840094a00008910000d40044208001c2c5520070071030141040c03030400a8174503010243c0e40d018219565940660303000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 936287329 1250 936286079 936286097
    0xf040608060a0e01051303090e041109070e120d120e0109140106170d1e0e0d0c1e03232833020a050f030c07021f0e012d 53
    0x30b50001c5c041c031904044c45080e0303900081c225a0b800360400c1c070340d4060810008458070008003482003103100c01c83e240202510f90092030400c00d90007059006001d80d528050030907580e11000500c1c0000d02c030803031b200c6241d4600303903c4040c8556034009003080c940c0b071310265902c0e141c40e1004142d2800b94142a140f104000007403051a00c0d040003d14000f440b4060880e03000301c015039a0341c0750800d4035449480f001840c10325019190710300030f59040c0f00384a0300c41d401c0b09211803a4010486241d520314140c030400d042214040026590512001907203002c01446420720b01c10a81c0c14420120254150003204010342d040010942e80001e614400074296101c0751404581c1c0006003c03102d0001c580714954010400c0d000c1e13003c04417903c20110b03410240b2880b40d5001940079801480380043d01d41020080d1100c81c1e4031f0401e04c0c40c460858000c240141e200d00c0310110340070034002c041d60510740802c6d600c0d00c40c0707084009400019240c806905070f8a5a046148240f1441c144000200726240da001a445904031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 936288579 1250 936287329 936287351
    0xd06051513050102060f040609032a060608030c071703070b0a060306050a020306100c080405041a030111130603050c090901030f060c0e010e060f221403030403030e0f040608060a 78
    0x744012984180c1c1590408814440c07200d9a40104070b038002d410910124903c8094641140e00e00003c8048110b04941140e9484608621200c1141c00c0ea0145030140000d03070320307004200d841e403180c2071101c0041d90101008002c1c20b9030070502c500300b8041c0401035034200300a079120034100c41c500b1621400405d942d8841802080f500c0e201d8a500712001c1d020443c214501500410400c4070072410f0385050108544094040100305402c0790007816000d40244020040038170045046543c2d52503d522035401c0c0592203110014a0080c2e82c0e210801800e135240350b80ca8100c0c00c0c1d0061101030316450352540e08001041441d1034600049008510900c44060450100c0c18148129240c00482100704160000c0d00080303a80c4c403001c1c10125841c101c40c1c940d603c034000e170340300815071007000d0080c81c104141c01d90780950f003030b1400c680381c0848501003640348419011008243d1207106500000f0b0201d0760319406401207003090496600002c80c0034000055050700c0740c2d0302030b2030244206e1ba4100300305e40310029060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 936289829 1250 936288579 936288607
    0x408010c090f0e010f0506092808121905030718032a080615040b0a0314070b0c070b18090c1c0b0a05090910061511031804020d060515 59
    0xb840f02e520564104d5041541854034400e0504c500d81c400ca82c04200728000ea0344d20070411080580c0301a9501100810500c1e9a0b940304062084c2c00480c018403400c500e0725485141140d02c440c030380c140d03241130054000000b524503800103004441003090280303242c0a5101002c40d9100918040c942c181000f00ba00c03524040e041c03480f480c4240826180781c1e03003000700100014056802070300945058010780d01700e2020800901e0103480065011204407000400e003d80795860191404900080d9401030f6201d04920041388204000320100340e00039101009811380800c0581b005044070320164040340174000000380040303016202003149000020b0b141e00100c40012494480f0b8500480038004031880a00150b0120300a00c200c0780110120700018150f281d06001901c5c1800d1490b03030400256842d2010082418541e49507040415905c00c500001010000240c07241c00d40c118140b060311511400c280006504105611144680c03210000700d070075a50f040b000a688a1501503e43c0c90328071000081d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 936291079 1250 936289829 936289859
    0x10020c060901052107030212060f0a170c0d080702100c0317061305160306080106120209041b060e0108070512061002031e07050d03060602030d051302151308160e0c0408010c09 77
    0x240305045e0852212b40c603484070a10312048586418200012038070b8191041c1c2460800c0001e2540127030142251805c214015018100c89802075420f45002440c021081c2c0348103980c0040603011454644214030720b038008001d010380c0010050207080c07502141030420001e423242030382d001070081c0014451041d00c96140c460140140211002480303020b1402c405c1e1040308081002c0603000e9840740e400207040c00000740d800d021820442c085020700c140c0d00c1500402105440c150700c0d000800c0e0390042804288144151114030b500b051136513a080d01c5000c03c0019281c0419407503401c1d4082400118046d9210452411206c4220241141d50312954903000c0d09000c0056140700c01e25241030005d100060340002510800710614030005140d461306510700c0c50002c0c0c0c00c1c800951101300c10408080b80ca03444c00140c402c800310440c0805074140c613840c05544400c0310300e500d4060000085020080c2c000041c54040d004051403601614054844424a095580e02c40e508004215250380402000300045051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 936292329 1250 936291079 936291091
    0x4150e100f050f090a0815010609050a050f041a121e010908040614040e100504231b0408060408090306070509090109020a2c10020c060901052107030212 67
    0x724041441c6003502078118003482100c201c4508001c541c201c019205d403114a005490600200d4822280e41c1082c0703424040300b401020300142c5180000122405d000c601350083da000285400c00fa000c5010901c0b0080c403200001c00340c8802600c080c45044c1d100e6219203100c548034840505203140c2d80b5007441084103011102c141d002e178034090080001c01e1129040e0381c1958500e250a45000752051400f45960189070400b4203014100814030040c404211015011240140ca0034448408520310303411800303044a1002c0a60444540064480781308064064a103004240115041980300c1854902e00302040382c0494403008000340010070751500f0000f5035406107891810b02d240a108501041076601c1c103219600c4040e40114581c0a6980074400c0302c00008034000800d091403803108080d0080599151040707010300c4070500c0c41020741f44041050501660007400e1249030402c1c0200469540d03000859100310b40c0e081e01031070130b04028011046401034074155405130b110140c00300e08568101002d811 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 936293579 1250 936292329 936292337
    0xb150d02030303060103110d02030109050115021b042409050a1d0a020609041d0c01030f0b010c140a080c1b0a05030604020d03050417101103010501120c020304150e10 73
    0x10010307500041201e910000070320b8003007000343d15117490104a01072181c030b41c03558500102c00424481d1035a8482c0741207a859180420085400000c2aa11481c40b0b02614660840c0c03071801e500582804d800109c801d590050042c440c0d00d0481445080308846a04540c5c1d40130713102e00500440c1500e034020207086880300c840d90180d041713070000041d941c2c10182d48024080c9201140c0200c2d1643e9a52102e420888508141e40c2410310400d91161240108804140820700d00301500c90031300d290388124008060107031540c510a101940755030f201030051443c0746205105240300304001403129000741141030b44520052035206442d0a00040600c2d6070413580b401031280480421503a0307400100190000d4040d80c3c0d180d49500c15090440f55481603400c000040014401018142d050020700ca420803928103004200031401c5000f10392540c4801e01c12180001c0c1c46503040661100264055104106180102c80c90710383d442d61000941081d151000001c24001e0514158504007403010680d180c4483c40c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 936294829 1250 936293579 936293599
    0x50a03050f061b0d0b0d02060d051603060b0901050708040b0703080109051f1202010c051603020103050a0c0804030f050405040c080612060405190201020a0506040819020d020d0305220b15 82
    0xa8040c0981c0280d060410102d5200c0d8002605501d1b10110201443d802512a0b0341d2020051300701030141c0030503140400c144544c0d5507040e030307183d201e031141d00240c607200c3c0e42c03207440c00300c2d19001105c2a400074107096400c602e0030080040e0501c01c1d40c0080c181544a0b80361002c10750b1605c0c498004490f4010540f400f145401503482c1c161000c04480c4000380d4000c0c00c08240040b0150004a812101000009102e172058a04501141188004242c01c40b8800d903010700c2079640315541a000e440c0000c1c074120200300d40b40042000207001c3d4400c2d40d031015043c9030445c14941d4810006040e41c400e42d42c0300002c10340e4142030001c1d90500d44032035011145d41070000e0245050543d0740c1652482e2109290b804048182c503240210fa01c02c0c04000d2440e0f801400f160030506003404d040e69154410001c500a007590700310b50900306800842c03c2c010511458019052400c6039000c00d41c041d11000b0100002c0310045041c0c006080740c9100410301041c0180b030803c40524041c818498020000c04100e032049291103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 936296079 1250 936294829 936294871
    0x1e0a03140a18080615040b0f010c031112031009050f04032102040914090a11090a0612030215060607170a020304030b0412021608061b04050a03050f06 66
    0x300340080882141052941d81d80c00000200d81c002c480c400741040000b040c1d80b00050140000921500420041c1040701042c292041080100c4841c02070031600010005100c480a42c01800050200c2e0701030b0501c0d01d609400d803101c01c0c0c00c0114600390100070420200511080c025844030000203070049030001c00c1a410884030124016400a100604110b8035000580c501c8001d01c0e40c04000c2c1028880640d100c544400400005d41440840c0c984030203031407000500750780c1000a07a481c1d41c0d600325030200110603042e400d00220b500001d12002116441d140c3c001098405144a0140035000f40c0c054001c2030400c08407600d000801800c1c16125140071310070748002ca00a510b83c001170542d03e00c25982d50380200842030b4158019548060410302d010030400060201c80b44000c281981d0917801c0e01c84a0202c00c01003403808403140140020350b4460400611030084240407045503c9082030305900703042d82c4400017602c0b590507820440d407a03040749458515a000400800d07800c161a40f0100c0c0c0121052 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 936297329 1250 936296079 936296087
    0xc1b060206060a06170a0b040c030518070b040905130b180618071e08160e0a05040b0a1a1009090501080307020f0d0f0606230316150504080d021e0a03 66
    0x1a240303260031640c0f005c010a820803040e5100940c4102c01810070b12040c100000040c000702002c440141c5110141020703190480d0300401d04034107641c0b5050110f8201401c0c0040786008000003040600c00c1c0a51642c0342000c6030b0f904400b076103e03400c2010340d40c10f42103d1010b4141070a4014054569081070390840c0704d0b00110119800043c4d54081802c44400504009440881c085541c0010741c03500134011030540c4241d03003001c2e400c240e8420b0b15a809250325a22444800c903201190003505043d251000310b10444041e801c00303440e030002002480c082405040000f40c2e2191008107010216040000800c940b50071401517a0040400d00095401c14500f6008106095484030321a4854500005c80400b0010000e11001006810500404c0a00e496400d1340002114030104007058082001c071220080c540001e00b007800500003940d050000b49401d42d00c0d80300e03c59180b2064248501030001007801041001700c1c03400c0038842c1c0e00500f02c0044109052001000c48021406507400681200d00485c2e00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 936298579 1250 936297329 936297347
    0xa0e010f21021c0c021e03070b130b010608060418120f020709060f0f0b1e090d17070b09070609290703020a060b0604030c050405070c1b060206060a06 66
    0x100d01c940360a0180d203115a03000b4802c400700f4083c4114041c03140e01a000d5039038400d0b5007162903a0200c81d45c00d8072a01b50580a61140400310440754002c1010f031000400c0c115120307801a4017035065001e8880f5580e81e001070014260004000030311030408110071803a0034004c842c0e2102000700c4c000c0f41c00c80d1503103410082603541c00102c800d1100c0503102440720340c401c000f80001860101c03020001c40d612084094a12a034501c2487c0c42480c22103404140750003410b080305e0100c40210401070100b5182e0802c40740d150822940e041c1d10400601c486800328120044d4108450070071282259180782529201c2c1017107802604030442a4040c0c0c00c1480055003004000341070300c1400c01c0096072510941d1408100c2d07004105405810540403a10800b0181c00280384090548a030360184010700c13040041c00078a000385e20002e4502c0c1da08100401440c18143d2150780c200203103140c514010000e5465030003c03000e030000036254810049c0d604001d91581407003c5a081881210328064003850b00c4402071014072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 936299829 1250 936298579 936298607
    0x1f0b040207120306230d0f1209050a0611030a030f2304120903030512090a0212031215060706020f0d02120417091008330301150308041a0903060109020a0e010f 70
    0x2c0c90080041803081b8219441030f5070ba403090130203010548080008103801503500c41e01b8054bc03210303800810702901a0f03004c0c0d00c00d5404600150300704807160408802a090780d501d003403042a925034181d60701800b4001003c8280406614038a4a41440c1c030f00702480c2510140303c6801c00c0507480701400001e86c81411951038001c1241014010f403241940603003040c6000000940c406074100c070800c00201d02002800440d092407100e9243d1f039591807030441c078045c3d061190a034062001c0000800281d4140c2c05444400550f146140c1801c400b990b4903012640540c1c01b14807829051410401000801108021800c0301002c40504180d0108003041410715213440c1c00d070901c407003000020602c88020380b4038414820400070480848000c07903100c1403c40c86000b90390340a5402d0840c0c01380c61034816070401048030b030301c010b40d00d00d0145070048050341100501c03800085070703c04006040350760740e04010440c064030a4000050380e03030101c5c02001d0070391000c0890707541c14054101192a24160801e22208070740f2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 936301079 1250 936299829 936299839
    0x3070201050705190b0702010b1504050d23070e0903070b0f0601050c0a0308010f0f080709050603030705070914150901062003120f0f04051f0b04020712030623 70
    0x70009240c03213400c01001c02c11400545502c40c00d0031040c0700075500344501580390380d0001c1111142103414410442c165103145d06010004200c01c0006042080c038503c4072500a00c1107040220000000c00a004883e0a6044440d03109a03828800480722030b03560790300584a0702c000d61811055031395122190744000d090314800c500500c00903004d0303401803049442c641d598a00303580350410140780c0035009010a02800e200c40f03081c2440030916024039079000c0709942040f8020700c2401d01d4001c5040107410002c1080d45c0601040c4034903800507008020140141058502c003041d00404c0d039141c142d00100040c00c40111040302c07480403606031034020500341500c2c0d8620f000c4120354030540c0c07121801c500e407249a0541d48000070b51030030000c0c1100000c0703004d00c8804800c00f540d40c42b04141003800c20b4055030003800b0340c0c0100e1142a006078244e0110900860b07001d40100f21448080000780480e00b00ae001620018950b1308031000c060b60500c240c4001c4c0180020500603950611650f400c810300000d4110300030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 936302329 1250 936301079 936301087
    0x30c0d0203121f051012050604060602100218060c0d08070c08071203060b070b18010c020339011a030715050702041b02030a0e030a1e0c0b180f09090307020105 70
    0x711607400303e0780041d202c090a06554481500030041031001c61385c9200fa03c151612001c501c8a252078010340c822602a540100442e091507581d800c000c1d4404241341003c1200003a0805550b100d180207040e2014021020300100c050040000c1c080706e00041c00041000010035030303c800038100505444d80140c01040401a420541074150010a80d039003000750105008201207003001081849184100d4445d5954110070f128028114240c0b004400c038000582c00600002c500c205040c500c114501d01810b20f20050005402c01002c055002c1c500351003110b9448050103035048491a4018100e040244c004020407458a860407400095040b901c0c0c042200015103c0709554840d0003c48603140b03a003603000d100d140034000182d07a80d4402810007022030482ca00c0700809140c0031507000c1d05190407a0581b2401e80c40b80600803007294014000b240c011144040220340c14080070007400d46e03100054581110607000808002c60007241c00005445408080100142e0660200a42e0b0b030307182d82800e1858403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 936303579 1250 936302329 936302371
    0xc0b07030f1802041a0109150e10050309010e070f1a04030c0b04030c0e0c070201212c0610090c020f0d0903110402120f090f0a05030c0d020312 63
    0x58040d0a440812040c00c15240626aa4504484402e014401c5504000f44020481c0354508041070380501d50219001040c100981c05002c036071100d00c5501460903520a41e603001c0010400c00341c1c03080c454002140402040704125091240c6960b1200210061600c50f05e0a200380f02440c18074041d910b050f428507d98400f4030420070017a24041d541c080710058045441b9120035055412610050790350f0f1000440001c0e81c1040010500d01900d42815440d1800c005500103503031614210188900d810044d00e0000c00f40b080c540301c1e000c00c0000d031440ca04407000c00d440182007a4030102d104411141c000000f03011f208070013050300b082110f07140c0001040d00038401d8416800c02203100040110350089980141c070482c1d2111122090f41d100c0c8500800b00c000d20020310049005000320048120404d138041500805481c02d91544829481c045906602c21141a113080044540c0d00321855400031442442d010400c0c04980504c0d000d9100450070003070a030181a08003900a4403005540a02046800c1d07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 936304829 1250 936303579 936303581
    0x510050f06090d15180803251e0e04090b06040e030c062406030103080909130206372a021c0201032009041109010e090a14010e070906020d0c0b0703 65
    0x250340d100701d00030f4040e00e90882c01d00641d29071045541d144e00c0e80003400210101150700750101d00d00c400740e5545000b49002c0c0c10181020404602c2180c090021074502e82810717556501330b484070540304002d06100d9081c50340500040d5a00cc0c0c04c00070303054105120a0a141800007090355001c2c0000e055100907424141e4000c4441903640c00680d0007410000c004018400c0580040c1030b203640c01d03240005640da07446100340025031040e80007548444100070702c0344004040c1c070b04000881141c105802c10300030300b1200040302c4041c00385100c2c0480d60b400a80500e565010fa40f00c84400c19003403060541a0340340d40010f07001e2a54242d5202084c81403510a002e5912130b80c401032341c480c1d0240a0400c1c0c007548204d0740341c0340d13004018168801c80c1018007440000e01080180c615030300060b180c008910f01868200200000010210034084e5a650500311a44000c010740d07a00911800a620402d41401040200912aa90003c9040d0340c446c0b41c281c2e40e003075440f4003191242da82000c02d400c074940b20260114 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 936306079 1250 936304829 936304841
    0xb07021504050405070206040c0f0f0315110a02340614070b01060309020306061e0d110301060b1b0a05030405010c020105120103080903010606080907170a060510050f06090d15 77
    0x3a0f0031900d45400c0100c12500016600d000300c3c0034007060301c21159160742c500081d104074011801060a0b0141c1000000d509100e081141d40b1118808110500060b208a01942082c185800140d2000b00d0703920740c101c4202c0a040c0c02e0480070242d0030700800544100007044400b842030300100f060040c24506450120f801f03884010b035004447d1040d039651010001e01810b500003080e4400c0c054040481c07681d2a11464440d14090309000c0d03517908080007001c021501860110903601c03020482d2a03680d00741d40030311641014240c410112500c031400c03a48500c994003e4944110802e903c803040190109a00100741d404035102460482218001840122160f010700102c41c0d180c1d4440ca4008003c000c40ba401420b803901d8103600800605540300e00c116448502510840c0d10b40c0c00440c014419803030350044400c841100c0741c4c1100c526001b02e036100c0007228400c40320042c00c0c0309140d0003031010749003500040100d6002280c080d41040f8800380000c0200724410002032100014188442c0035605540040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 936307329 1250 936306079 936306089
    0x1050c03071719020c0a05010e031603050322081005060604031209080c010f0801121406011203170411190b040e060901050108090a080c0c040609020a0f02070b07021504 74
    0x612050b80c200300c009540d00480d602c001d100800b442c801128620005214089a0005100329034007850000195208005101c2041d09405420000d41021203000c4605c8000d500c140000c41d59400800c0008804005500d544040000303190010040b030440025520004110101c000400780c48483c00100c2c10303c135030380c0000c08042241d01c0e0a110507401040300740449440a042d9000b030359a1100440d1082072235561440440c144000610100259403680b4403001d00c240500001404403610f2a40b500c4000d0b8441d4001c0142c000c00e800402d944564088506164108800c0325410296960240e000306081d003940600603410340085070310f130341400050042c036052260540d82d03503c3d4403200e52188ad04540460241075501c000140d2948114600c40c402e010020103401802c21a544000c541e500640b803440d1b0781c2c40f0b091040e000c030380e07214850308004100507c0c0050769500652000b9158a10300c0c4500c2c001c0d900010b40801440d0aa4002c440c240e5604540c803c4d514122024030610303070302a90b003107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 936308579 1250 936307329 936307343
    0xa020c0a0204110a02070902190c06090c0f0602120f0301140117150f0306040c030215040915031202120307050f0f0706092d02090901093c0c0501050c0307 68
    0xda580f03021426030080c4280042e95003514541921010f03c50103030f00c5203040e0005030b120300408124065104100c110764542c850311001c10741c02d4858030340d0b9580c2007032504100c46a0340944020810f89404000c600f03d84500c0c90031050811850081180c1c0d0342c00144a81001d000b000745003002e1507032007a058469014602d6604401604014810040c0148c981c85421b00404940340c05a10038a030000b0708900c615407020b00c0c200b12509690a00514007842c041d0b10b4100c0b80709000c04281d80d10a4040d42c02e0303489002042811440c558149060701806416203101590041e0481800c121803003030407a90f0060380b9007801c0e541c80e4040510491a4400d08080381c0c104540031404004010340c40d04160700b828010070130313041907038030030912070040c410524401a04d40140310140801410121500c50348040d40e4000065900b4040c0c4480c0303210004109480c500d40d4500404190071900988040b00d8140001d200d185076201c00c3e0784180500c0e141e406000e050020104d68481700140c20000c8400843d44100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 936309829 1250 936308579 936308591
    0x8180601050d03023406030b030d140c0a0302060714070b010302090601020f030c100b0a0b031b0405090708100911030c03042406050906060306061206150703020307061803080a020c0a0204 82
    0xc21750074a182030300b04070344031000301000942c091081c0192141c005c0002c01529a0610b240710590340c0b50704190000206080030b0015542100d07003840005442801707600508150f01e000d440050400000000807003c1000500060300070406034141c55054913419200304046480b040c0050745011580301c1580200c0c070002916180030000071440c103550180a910500084141c03104101180e01d880c019041100800e10001b04050704000344441c8011160704ca09180c10b403102c000ca06c3d641c0046030044042524030f0144001001c03108900300c01401925010082c1461201141740d8511003d4000441e03214048003003014040c00f2255101c0c401043c04507078510b044615010300149c0801e110f0244a02c00c00f1000402d1401d1400807280701d1280200729900e0b1642e100ca82007190100900744c6504541040c96410000035171030001d14440c1e000360021034554840d450a10103035a05036062803060901080d05d08002a00220200e03013000c01c8990150300d4040304103100d8502101c02c08080c0d8000d05041c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 936311079 1250 936309829 936309883
    0x210309240c2a0e010522050a0b0402190809062716120b010e150d030306050a09091403070b160e0a0e0106020607300207140d08180601050d0302 63
    0x1d070b00c000c03c4495490741c0215980c0ea0b6030801040210000d01c030034003070700907142c0208a50120391000d940200d140900180070203052020400b01d81001c41841075260544078a1003146400507a0300b03900c1105070004201034548902501607500d20b6151041c1e4060325410a8145080e05212156404225900000348140c1d03603004059040001002951340541040001c1a001c0c03218017294404c40c00c0d994400f0b038042e8064188103c0000c0700030140c040683d50380003c981c0da075802002000425030614041200e01103400c000310900301101c030700340d141e40c4108480300024040092141d407182020380d0030000102e00007401e4603110f110310202540701d80d10f040c010601c0c2d86052111416141640d08480e0150f588a03025164660700c032261954800c0152409840104c00300743d0441516481d02015040100603915110003035040b81781440703070b600151603c1d4040343d80b04031080c1d8004945421410840315108a59446203018010940110100303418a010f050082150520303a054a011001c1c21091117 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 936312329 1250 936311079 936311153
    0xd1d130c0c1e1a070c12020c03010b0306060906060702031903170609070806150405030615091308090d06090807060609060501141b0106210309240c 65
    0xc29003103038046000c450340210300d541d207007420385003d0f0f015661142080c6000782140b00004014100000c110a0120100000b400001d806001d00c03030036001000e01d820803000709400c3d52414902d03a4000d60141d400c01c8055030300c00400070741201d801d032981a0b0364541400824100306580d035401e896801401890420598481d011003044044a00038040503102d043c20840010410303940300c000201a030000c140355103000da42d104003040860b42a10302d800d94550209090910440300c6007150b4100e08119182e038108040c42030b078000010720510108102c2c80e92201d00324010b04440d0381c011550030b000641000820b60110303107002d4001345055140c0c1031038900200a48150301a140d0b050f400c150740001c0302d5014a07520034210a49900c80d5040c19060390b24820036214008510281e9903c5040c0005c02c03c14108040114012076400c540000351541406041070419501003200c8980d40000f0000302008006030b54121481480c00702e0a180c00c0d8103042d4800c12007554042e070040d800202910040100c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 936313579 1250 936312329 936312347
    0x120603121801081305100c1e0503040606060e010804030f170c0702032109040b0301090f0c030309050a060c0305071a100303021002090d0b070c050706030e06090d1d130c 74
    0xb6a580301841d6a210000913407040080c400030b140d0703841a92807241ea20300e10b07048000344603107a2801d17480441c1209406207580c0740b010840404a08000103100a2118074001c0c00050581401c1020414000310002403000c00000d0002e8100001d03414018030003441100c402401c0344800040b42c6050906d074103e00465449248124480d200d141102c29000c850440002404500000c0090030300700305500f03000103000160301e80e80d8595170f951140c1c0d00080e081d802c8415900e004a90520a4500318500500510103c0c1c02141c40303021144820080d465000d54000e0100f83e05240164560110f0300e001000e9540941040c591722544c1e5042001d00ca03c542c0c07240f4100c1e400381d0308441140401c40d44200807445210745541d00080c00507594004590080240c680100c40ca140c400f00c0e00400e52030700c90515096400280001c1d49890b080350710701100704812604569500007134407124451100c06014180071001d40c0c41e070002d0601c49245541d6541c1114050810510414000b0400c41c0d0801000084 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 936314829 1250 936313579 936313627
    0x507030219140409180218161e0c060e0706030b030114040f0b18120306040c110a0b0c0409020d0b0102070e10062f1c021212060312 58
    0x900740c10a5031002c0c80b85000200c109640000a40382908208141e40580050a000005030b0440300040d401a02c8202e03aa09607202c03441503154040c14072010034548030307514840000810908217008800117268445400072480e0074102000030b25914503180001d0083c1050070130050181d2480050025015000011a820224020051420048801590003e09890162079460100000800600c4020f151b94001608030008025008041d200510b13158900b10310a00000c4007105000701401d150051828412030340c14080c1040070800360300340c0c2e150816640608106041000306000034914001c1b40c01901c0790620642d903c00141c130351880540128000c1500503ca04c1000050510f078806220307000307040b0140f401070282d07e44401212400c50207145907801d03078002c3c11800d0240558415035951a900e510140160020002c0410b944041416294082d5001039074684440c0502c0002c8810090f001010800141c07501008246480c8900c000710342020310006d51480081604040400c2d0070b5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 936316079 1250 936314829 936314857
    0xe15090412030e1f02130810020c06070c120c0219030303051803030613021e040305060403091a120c16140105090114010603090609020603150f100206060603090a050105070302 77
    0x1850110702136803074144035000c0484403254111031502c402076030010301070501c0c002c00a24446445022260510058550500700103500040c85454103406220442d481440c80c03e0500c1a24507607201d801d201000118200100311244c40340b10215901c00e150303451142072195207002c0060301c92402400502c0187ca140d05100300091102c904600f001003280e21551b40a02601490b000c4010710101942110303a6000b03044070b141c000c0c45040603581c1c02820086008400038509410607040c0130701350340c03842d4000d03140700c0b816034802c0545a84048116181c089225454200654400204601c00d014240302190030688825030170080c8030b0005074400c801a0200000c0020b615014806030885800d4a030b8402e103000000300400050f07010b9801880d110b801035501003014203640e40021565442200c0005801d03110035081d2066090846c01011145015141c2e035100b0903054074060340d2460010701c0c40307110f0240000001d69000d401d01c18400d110b60b1000080c403850a204001402035000000004440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 936317329 1250 936316079 936316091
    0xe030c1b030601060f110106081c0e0405010b04051201090503030709061b0c03060b010507061b0f05040305190f050703060b1824030a0203060a1a03060c040e1509041203 74
    0x3a2078007094082c100c5203030b0789038801c101890325800d03641441500040b454556031142c002031001d50900025078608140c0740681440380894202070b140ca043c0400080c0500d18100040c80807010700710456050710011241513000c040c4601c074031405040f03520300c020020700021050000098002030403c0c159000c5403200982804c400c15403500040590201401d00c0e10000801c001080e0300358420a04c040040c5843c80c44c003900340c1c450400b0340707370302c0140780301c0100e003030304030381080e16488941c43c203125040385440e40c5401d14640310150340d210400b18504420521580541c01c101410f200e4031015a40202070320035940d9070b401c2440003001040d15160140c2031140040890b000755a8000340b00e510010444030099041004004004c14007440e000c0d018422034046d43c01590301008020300c10980380c1c1c408075000c0204010b8444401c0d10f0121ba070300a07844401441121401d9005035019101180d90320300007541c03030b100c3d1120702e40403880700c8a8000c4464414070042c0040010045544800c84d1010700030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 936318579 1250 936317329 936317383
    0xd09062a110d1b1a0a050d0f09080a020a0312150e06010314010b03010f0510080f0411060f03100b0403030203030f040c03020d060218030c031b041112010312050702010509040f0e030c 80
    0x6501c215410300001500c10400300b007100e602c7e0f43c4609031040c40c1c48000030321000c81d5500e082160780310308140c0b005a846010300700b0426601140004254540407010f2085000b100d001803403a0105004034204031004900041e8540d1090744044102c080260542c5002d503901e203507a01c1300364802e0060200c0d04001100c0491b560402d8039602c40d10303554642d03820005607214003a0703003a2240c010f03004a4401d200c040500440f5501d240c003a085a41c0303486c241caa07a031304190301c1d0b02c54030a00990010031070103c01c7c041000401e401000752a88031403038080c02c032000d903211700c0c0c01c45001c9240d80001703520101c03030b142c9001401030719400340c40907498036000e002250185204040c0c1c1c508000d40e0721340d45030b0301c00700040c0341d0342d92196071401d0341c03d5000d03002007030319407040709000042d401035914a01c008501e40010000d109800200c600610380c5810014540149500000c0092181d0300109000350f03281d80061191042a43c000c403840c18042c0f050320b44607108001c2c566212407030b0985520201440a80c0c0c0d80c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 936319829 1250 936318579 936318629
    0xc032a0d02061b0d0605190602010614031c03021c0b0103150f0b0708090904030807080a110909090f160518010f260d09062a110d1b 58
    0x4014a002e03010a0000c03034507034440b06020b5100c04d8a844a03903855040c0054141c80d032800b01c020118054191100b0076080500c001d00b16503a0b54480c8100ba80800702e60030040c1c40100d0b0300c00c02c25203d08110002c051f450441900640302e02500085d10190100c0030b818866056440f10348804000d0380e0502402020282116100ba1507004042019200140030020710008030001c0080902c603080c0f007030030482040c2c000740d0044d0702120301b43c0100c0e44030380c10010102d034172841140d880b1980781d46c2040307040c404903802c0486008200311903001c2d608860114485076000c0000840f0328201e00121440112491141c0c440340f0b0007445194040c868010744a025140140312482c16941e50ac40109002441c016071541c078000e103001200895102a00e40729003810050080c600802d02c50740303441ca0000d00e09400201170300c90100140c0c2034541c44003013010035500a0215643d2040d04044841c00c1d181d1007200182d226000c519006060011119800c207910b940f55207603808507000d2003103c0041242c1411203031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 936321079 1250 936319829 936319831
    0x50f0102100c02011404050a1e03021b13091208060a08060c130513020307080a02070203150601112a0910120804031e15200c032a0d0206 60
    0x9015800081100100d154994401c509a02d528030000c035003111078502e00401e8003400c0c0c1e0f06486c10341000c21800306100c071940d14081c00101403100c0c803240340b8036524000e480304c6020f1420100c2c0046002140d130340380d40d0241c0110010b8110b0404000011842c6400021007061148143c00b0801e8800003494500c0d013800100111841324001e08400d07503520000304503540c4a24150021403080e828041800c3e15544d079440c11130f04022a0050366400c0900d80680400d0005044000701030041242c1c17401607c01080d2040c190b414580d02440944508006a68816490345184502c0c46580000780d0101c183c1412050742900c5001c4140760115a40244000905c0c100d400303130500e0b85a0030040001d020b006d180c04a00b140189a0103007465200d52340c401c0a642c100c202c0340210322100e1500001d0010090b844610050306983c10080d500c040b20309121368220422a800010700c1c08130382041220010310031202211850795041d402ca141a402483c561014510241d007244101c0342b1b981a41400001c400e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 936322329 1250 936321079 936321109
    0xf0601080f1006270e0106020709060302130b040f020c0d0909060b160c0503011e050a06050f0f0a031208010e071103160201110d120b011722081c0605 66
    0x1002d031083c1440401d64006812440044080c2810906080c880000c007141310040c024140003140d2075403405500914101403600b010500c94074004013000182d94800b80d1000248440c44042a00d5600900182c01050424072942c543d9000007545800780c10041101e4480f00416180d99103456182c0d440724046a02e14011050005001c101c0e054040b101241d20041e418460387e21061034940350700111b030944814401742403006401142d80f940c80c0a15021381c80c4c0c0001c00300401c00c40c8518040000d03da0111589070300340144404480b101450301c60900d40c001858010082c076074132940841c1c0082c007000d800d1154648585505003c500701c5440b8084040e50540058000c50400d400721151000380030070a901207061003881c0042401c0d43c0c1044c0f00071140d1041c140c84010303020080384400400e4883d40030b031403070400c000300b902c42c54107030b650703c1585403c1810070091328403850706107112080e8140102400380c841c070804a4441a40c01400b03542c0701d005460010b0520000d6503078014001c030507948040c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 936323579 1250 936322329 936322351
    0x30216030e030a050a0b0a05090a050c0603070e031e0c0607030c08032701050907080a0309030809061b01150e162703080909010b03040f290f0601080f 66
    0x20004a44038403400c0c0e824038401001c2c0c510000aa42c1d40742c0c90311110250456010030f200082100108180c030415a002e071010002c0c20036000d0581d103142e150112008002e00c200e8010012501d624406c402c043d41400c0068225500b400842a01c2d0b000c068902c0070f03180692082a50b2044103080110070761b0318695140e20340c42c0c07a0009903030710a8001d0700000c01d10001003124060002c0f019006c10000ca0303160459000000e0282000c0d141e50b414409250441c488560050007050b0010341d001c418030040f030ba0486001600d0341d000302c00180c11845941c0d0342c0c44035030154902c000042c41c1d0640c41054040304511180d01c0c400e0382c40038000304140003103540950581d4080000a180c1d8018030003045014410440300d500f04060f135000c0c035a4500705410503100c1040206100320720341001480c02d400762a28010107402c600e02541ca01040d50182403004005403101a40c1ea05000ba401000510f262070040440600c1c1ca403400e03108074008001c55200e0300041e0500f011400444e43c2c81d8069014000c0d900c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 936324829 1250 936323579 936323617
    0x30e130605030312190516020705010809100e01060902040f090e0703120f02010605031204180605151806030a0f0b180a0b1c05011506050315040b060d0504140d0302 72
    0x1d82c003584d00402041e115090345034141207035038032250344500c0c0d11540008606003045281f07408020f01d0308c14150030441c1072050300f40a0215000002030300d0522503180c41804110100d000500d02c0c013502c6a5031006503a5400454003240104081c00c903c800c0e07469925040110043c400e101940e54031040c400903007c8684d81803003c00084c403031100c1d05c803108114000800c1c810703a5131001c40c4c5844815910700c04440310204080c018040c0d01c0030035040745004d40300e0a000c80703400c100000d030b40f8004051503000101c400281004110070074a15100c030703000008003130341e0b1039142808000020b0010043d01441030351500b080c0c8021480d00d608022038500d01d5044030040c1d9684e20941c98001c1150406280e4001c1e900c8101c81190010428030a4140b44548004140029401400010b41070190041b00c140701040c401c00080c60030003200c071242c030301e012240071542a0140003c14294413a90100c10117a40c10442000b060141c01c00202610a4103001200d003007503200d100c00c500f24081c20403007102c3c00d29090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 936326079 1250 936324829 936324847
    0x21030c030c1a0108010506010e010503100501230301090603060c0c0c031b09020316021e0a060f0e01180c0501090509060603040503210109060e0606270d030e1306050303 74
    0x15024080c8544148a2808200c2e002c4102090240c0260f2001040d07030344034010080c440d40e020101c44075040c001c0c01d0280c01c500306041108684e00d0203004060410610145900c0200003094140154041101d407255a03540c4401204000d400d072400240c0d00d25003441c0c45048010b00c00d40502030602e4004a82d0010b003821541c174140303020040038041003d01010800071130221828402176004000807060035010003055507000e403c00100989004640f00d0005070005050404600001019800b01002600a8107080342e0750041c2081d6107408400c0d03103083c034180d407044032007154500322602078032240e070306996200011500c0e402c0500800d45c00000c0d80c0086603607820710301e025541083c490070640f41002501c0d10403855544481c0110041e0000a0340108003200e0a80b01d0701e4054851041401142c3c500800400d00920607044107003140703402c8410360b10700340450201c1041b0388100101210f2030752006040003800c4005805030607118810413044818411410301c1a0710440c0c070098085d6040881701 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 936327329 1250 936326079 936326087
    0x60c0504030c05090601140d270818120f010b0f040203070512221a010b03091b040204050d08040906060f211104082506020d2303010906080c04152304020f0421030c03 73
    0x18115040e0084ccc20380159901d5290248080e601200700b450001485611000c05c00850301c00039080f0f2070140d44108184152143e10030101ca50004880118104c0c03900e9580c1d000c0404e0f10300ca1806191000000c0c0c0311300801038249941d000c10303110f5486c89580b40c1d803655140038035841b06944005041d03215581c0000040d01c0d030804171244c0b1000800c01800c003039841011a00c42c52490380100d0300f8140005007070219005501c140c2000d40200d150559260802080280011600000039010601c1000102c0b8029000341c00000c2c550b800300316070644403030f0388014103550348080b05106104204994440140c00020300e1010080f104554020501001000b40549908103803890f03000598918a0824030198445001107008180d6508000f4903d4a08002d40d401c4c00b031a000d503544205e0510788400c2d0104441059101030303880c05100144440743d242c09540010000d8050150054000b05484070551451030250003202c5c014940300309511181070091f05514001e00c0001d022507001003114010a1103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 936328579 1250 936327329 936327367
    0x40c020d30060801020915090108010306020d1509020c07080609030d021c02040303020d110303060904110a080a0c0302040507140301030602090a03050f0a060c0504030c05090601140d2708 82
    0x1140c0000d054003a11072a0640a0740c18a8002000580d0001489038203814130141c606c0310181080c400320706040c6240002002518180300251600e500802c1c141d0640c00720394000a541c640510710b4200c03441d5540313003040c00703500240c8180040340114a8001064a00451040e20485440c00034500d4910107a200740000d40003030403500c0c3c480c0180c019041d500c00c042d100038006540240c000304180882240000c20031000114042040d40052050010f5600c0300503400c0c1d00268172010f2400300228030000b081c0840840d520003012480b48490400c140300c59005d000041e20300035039080c08680e41e0154180c81e5a061021a4003890382c0400042020849907400389c03241c80301c0100010283da6403038a51914100c00c80c101500d481e00072034408410401c0703034420f500000c041030404900f0613244d030b1186401522a0b02c9064040d40e1040c00241880e0f00c102100ca407031380240720f062929050900800c038001d042201081a420000d003c42c44114003540721081c82c5030f42d0140391685844d28a410100384c500f1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 936329829 1250 936328579 936328637
    0x403030e1003090c0605030108010c030e2a03071205010b0f03060411040605090106021606090501090303030209031207050706090839060a02030c0715020303040803100f14040c020d 79
    0x50307220000e0f40051800c5045500a000c01d660740d94480d41411000b608403408460741d03006240c500000da06415001050020403a8090410092008504130008035400302031080381c4c2d8135000310440800c403218506003070f2104901a00003000713500b401c082400301a40300c0c9411a0348c1a40b00c4000140007840b09008000344090107400890a0356450000c9190b4103020703004080942c12100780d40c40441d08119210004100307a2501044041c038220001c2d0003025240009030405030002046100f03501c0411485803084021701e907480d03442c055070403e2511480039008020000e104140006001000042c011250010640075040540c20101c2d11850b105d0301b1380c95048003240310003c04c40d1181e5419010705a012444e4001d55170f51410b544100f400c1600f40c5d04003116455403e500741c1212580001603d5000340e22088140d600d848203a20712440100c2e13a84280c00c2c050b8820740c0803a100042d061441c403080016903013070000d40c001c1f80003a6180c401c150000381c00500d0921110310b0400c507034200b134070b03d41c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 936330935 1106 936329829 936329831
    0xf06020f1b0105010509010909050304080a0f020901080106061e0318060f180c030b070504082b0e1f050f040e071b121d090703090c08030403030e1003 66
    0x6c0041c020810708945c1c1d500e0b0501007101c00c108442c05170078000c0883e00c02c0c0015250012408001d41000c86c014941c0900004000350140140d400f40c410b02d88400c60341a0404c0d410004a601c041c1a02042507291450804202003141e42c07258814041c3c00701140518541002ca025103020640d40728040c66200924404100002d00c3d5030192035002c20035078a2a101d0f0310381100c0386d009603000a584c83c0641b0b0b80c2060941c080b92051505030410711085540f00b16130f04015590132070280c00c0b440d0450a00c124110ac1e000752040c003600392510605215051216810202c07106030055040986c41071105401d11640d143c01120688440e100444003884201301d9a89480700040140034200501201050814651007906043d5001c000c000d4040e00240c540700c10003e02130700c4640c00c04e4a5111807000c02041c4401c0c0802181c00381c940580310416018500d0040c04009825101d08100301 = true := by decide +kernel

theorem cover : BRFrame.Cov 936151079 936330935 := by
  have h0 := BRFrame.cov_init 936151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 936151079 ≤ n) (h2 : n < 936330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
