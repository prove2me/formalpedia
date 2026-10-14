-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3693
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:24:15.745161+00:00
-- url     : https://prove2.me/submissions/de663a1c-c9e8-418c-bd13-fc66a0e7b180

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 664028776 ≤ n < 664208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 664030026 1250 664028776 664028779
    0x1401030c0608040f08030f0a0b04090b06090901060905150a0605160204020d06050907020706020f03040b0d0f020408031914070f02010c020619091a030907060804030504120318050f 79
    0x100910885100c0c010741a4410700c1410388060081444d101e061950700125015980c1020006c01c000c5110fa40e030068032700c161025641401070210b1581c401c40700b2503000b400240103802000c00248252400d400c044000c0c01034075020030281c140800c05c50511590410745600840300d4001c0040e09510650484000e031003040c40e403a01e9034007181c1c204000303903000c1ca200d40d58540c0c4507080890240c1d01d200740a4040d8900f0380003803040524002000e41009900c02c2e0343d4007070b600180010400c1c40944030840d01050804680080c8a01c0e55030780d500c00038012600507141d10702c408900034003805042aa04080281a5144c1405050182d200790803079106040303000b45154039604000006502036680c4d0745071144000e003007a04080703140032007075600204212408002084110700b00b00082407a8079000f40c000c00c0c441c6085c40c51419a001d10b83c2c1e402c0d0303031007510108124000000c05051103841070b00c01a00301041c0c0c501d0500214100240055200b900380d0008088410001900d46070a404403d4110700 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 664031276 1250 664030026 664030043
    0x311160e040807020303040906140306150f240a09061206050a090e0c1903020a0b0f04150e03060f0601030e2802150705030a0206070203131a0d0f06060201140103 71
    0x40750b80c2c410515030058001241c052200317000118140710703140038040140c0b042a074200400c0700058105031400c9000380c158100c1c4a04200303510070b15100d9100071107903172005135108502c040300041c6030380003104660107128a881e00829140e40f12940003200c00c04480c02503603041d0080b418456004200c849a12600758018407203101004003c000750412004600b520090b140030b00c031910b0101d0b015603c08848c180000d420460705104618044003030380007521183c002207041020004003c1810b10a6006404c036005213607540f10300d914810079000321b500350040d0540307510b4101203003281c11566041d5480340c0420706118801c01a40f00c001200b00d05110440d80c407c81d0041c84240790924002040c8050341c225014034000d40ea8441c0c0040100304192103203004680c1ca0380403d40080c140f8401510302800c6410401612100e142e10007491401d0f100000c1c0e0311340e8403040307045c0c2558840c480c1201600d40942004007000c105401a44141c00b01c0d14036400a01143c50000b00d00b90801130240002092202c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 664032526 1250 664031276 664031281
    0xb04171506061608130f1701090b15270402090c07030f140c070e010519150e0619021e280203120d020901170705030a090302190311160e 60
    0x79074011207450f070340d00a041444ca40100c6842000380c002440e0018844042d00c00c80800c407040482c26551142c40881d0000c00080350281c1d201d5104140141075100520f040c0c0c000a000c560360500c801c0108207220013801c3e41e801c070081004040500071202a84205500320000e1081c40002d000c9509155142d6100d100803c0c0005040d1031840b003060740c15410603014488641c0303035082081041d0190a00c406008540d6252604000c44400240c8051108030341c084010018001c960240000760b800c1410400d80d07407110340c0c0105a26004800408210000d140072107a07040b5004559035104904178074030002501c41500e04155a288682c0700380040c40701a59000520903640c640c00e454582c0300034181c0e8000740d0141d07640c1060750019051800c0803980002c05000542e040f0000904003458481c001e0706070324101c04040c00a0100514400882d91a071800c58101807080c000b5140e20700038104032040d454601e050049c8021034000000210340301d698003009001d40354810440407101888020303034096 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 664033776 1250 664032526 664032547
    0x16020406090603210e030a050a1103030a0912111e0a05090624040503030408030d060f0302130c1211040e090109020a060f03140703090210080606030604150b0417150606 74
    0x48403001341c10400c0000c01000d1588650f0700303109894029005400501c021061810140300d85c20101014611a900070042a250300b50043c07a0101107941145503980f500c501420511a0380d1400c6010744c2d4080da0b41d40f10b103026900e090940c2c8142400540306c40b100d050300c0344244603040100b5114594411141c51462040a001c0c07000315415054000701d40307007066603c0e030203c1d1458025810240207500003107280e1800d0b0ce41803141e43d0090034540c54092044d42f440d0003142c1950154603c020380b00d0346850321046194000d0b40b101c1000e04a0400402c203903543c074800702c1c06541003402420340e010488004206116014000e161040307030005c01c80c50f9030030701c2e00710161910040c0c0007828082c5600c03200f40e4818200e06400785445600d00b901d0108203020144104507225804001e07420134408200d05103c1c2c240c40303031008d580d8400303010344000960680d15201d281c0300300880c0d80290100c0c10700103004100000c03800b0009880020b400c04841d00844080c0d8126040941100d040c0d810900a0082018a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 664035026 1250 664033776 664033823
    0x150705030c090109090c2a0f113706110d0e1305091525030e10050103050c210606040c0306050904030f08010b040f030809120316020406090603 63
    0x3581c070506013030101960702e4032007000b6a0305020824000c10150300c52080c03070300c844118461406145000035001d5010903590395070001c0030b1440c09410680746031048102d54032024402002440102d040b0384d6443d10300318071010a0b4003054a03601c3e9a0f4078903440080d40602950056891075100340c0641510310380f25504a034800e4203544c4041d072180c00e83c0200141442140300d17243c095080200580021009504200e001802c00f9044810300c04900c0680c10002464050800c83d01d074240c500450000a490030042c40c06c10100000d1003c6481d00c0b0000041120010381002c04060644014426580e070703440000080801921110168101382d0010300180340c03c0c0c2c00981c01c200342e400c00082c0725480e080803600d60b1400b21000c8021601c4e07003002c0d12520741c006d00040e0040c001c0304032103884c1904264100c1e0f000f1046110081913000c001c19640780da42e580101d140c600548841c1100c0d19101c00c00d0540510400c4084243d000da4070b0907a0100d0007440302d001d54000e0700e4000c0e150f00541400040c99449 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 664036276 1250 664035026 664035037
    0x8070b0703090b0706060305120f071b0f060806090703020702011d01030603082110050a030b09010f1e1a090f060d05010509010209040501090605090112080f04030f05150705030c 78
    0x10002d031100003041e905000030181240380d0007135000066050a5180586c130f04071169040340c042010034004000c10390390140403160b047d80d200216146440380407084412615030b9030442101a144042c0200c3c4807a03110700303840c1c4640f004840884240d122104150103d00c41d640300179001130f034180c000d0803a0401c1d044122035000c0043c0340001b00c040e41d030303122a040c03500030421003040f02000340e12180310820301c807108507003211010024070740d014544030006019030241d00c8000c00c0e8684210008003901e9003076201741103016081c0d4041c48150b030030400728408a03444251080d0054078240d00e0b00b124501d40c40841002d144054410300c500d490b07000f245070003040c1c010512680502c41c82d9409000400a01405000300304901c00942c0310800001000155034058100c0d28600c1d1030301008104590310307151890b0440d048109403004004581c10700c00590301c219540c00351141400038001080101000324110002d000b50192076201c040b0b60705500e400b220a461407030000c0e00500100c0c10b41c415001c010300c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 664037526 1250 664036276 664036283
    0x80c040b12150301060e090618031c1401080a12020607020c040f0905070311040b03030903122203050a060c03180219030605010902041d010308120a0603020904230708070b07 76
    0x52910b03074a1001034295603080d00701003608841c080910a00d140e04000d8140c102200140400350301440c0000d80381c0c2c900900380440141a00b91660101b1104243d0000000030002c040d040e03400d40e11984450342e42c840d182f2044981c8242161503102903840400c400d4001e13145540544801d0b181d0f11b040002500401210704020f503551a40c01001401c03c01481c170007507204a0850356017404900400080391984c03d80709004e034104005071040d5036008114540303c41460f249464a4070300484003c001c0080380300d10311807038989145000c820720100040c640c03541c074407030b0340c00f441500da003814100c040d244070055405484c003410407080d0061814030110326100329010850442561780340c541c001a01c400380e224000e601e0380010284213080c4800680300ba18803041d80304241075451559246458445c0c01c0f60441c3c04803030000415039134501e03500020700071900288620490b04140c1401c0d00444a03585000c20003128084028000741e00c0030909104862042018204081c034000d130105259001540c00c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 664038776 1250 664037526 664037551
    0x1608370f11100e0708012315030a0c0305120405010e15130e01080d14040306021e0d0c08070f09030b04050c0d050a1e0c090b041b0f080c040b12 63
    0x5000500300320501107100c940b000800c1e155214607115042c107040d50085440c903418540d5184045845072080700801003032540c401020394072440b159005400407040c0030361500400c086075003402044072803031058a0043d000e035010000300c250310002612940c41440c0c080f03050301c02c081e802480c000b10020a964603002c1c240307103040181c02001c040303e00d4640001c0d04404e40080140700f014400c1001002c8030f04a814038016452140c01c81c61706c24011844024540c13600014418030b40d00c5a107142036222000c002415072200e0610481c1d10190624254010010341010006400c49100785162030707a450f526240e105000d400d5407a101d241ca44010000d40e05440b648488442e075840b034254051005001e50080d0804115500e040d140d9000050303071562030591140303181808a62541c1400d070449800b103100040042c0c1040105000d007960209509654480e510350240ca6900100c11908200d000e680385420390791414030741360780750203a4040e03107280341c20502c007001510a032500d00682000021541 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 664040026 1250 664038776 664038797
    0xa02060f0c0403120323070306081e03120903090a0909110907050f0901020313120507060e01120e101a100903081605070b040308040312051e0307051608370f 69
    0x1c00c0007402c10347d0140000303070381c0304410003019005211501c1640895078603680c050100078003c5907640220310300980000280b001080f40d10408100310745c01380c40080e2004500c1c50f59885202c00418090300e0644026451600d1005185050103106228140e0340d107965007021800b645d120380c030390442c14425040d0b110030090364002031040c401c400b005041c2c401803501000310740d2038014103008032540000140112081982c1d900d0b030304100040951202802c0025809140340101c524281c410044442c1161602c403904c00140c0b581e410705c091042d0300b6203030800041c01c1400101c41354262840064002c400601002005c141820110188140980125600d07243c5640702d03003a09074000e074411070fa0120006001c104100c8010700b00c02503456a424071901340200c07060304922130b42c550925148580800000038003c3c41c0240296400c0c000c6c40c3c00c2032a24280f1514203500780703a00040c00904101610311040304005075030340403110001e0a840c070110f09120615029501c0c084220002c4092201241c103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 664041276 1250 664040026 664040081
    0x150201151212050913091119060804030c032604030e061201030f1b080309030705180601030c20032206050f0d020f030a0b330d060b0a02060f0c04031203 67
    0xe02c6d02c13054091003501100380c0c0150b0400c0304c0201442146d004c11400c00200308011034026507540c1d4810b0705410001c2300c42c8138a103000c1b0313810f401c0c82c5c0070f1180002c211004440328807180111944242c1c0f01c1e4a503298070280e00420031680740145640e034500a60100300500000d8203680e141811144125140e55a00110384000e03c0102215088201994400300d0700810b03a180c1080100c000b00f0080d18030710700a86035505204481c54004049a0515480c2e995031250705105100b1a0441c02c400d180194000c1000401c1c030fa2203034880c1c002201e410f42801c000b20241340c0c0a00700181100d40d66259186818810702d4880c1c41ca400c09101d40e00c85035428850b803039480b4114402140306401808000035640b804400304400054a208482d001d0003100c4401c0c2c002c8203c500b0035030003413080450066220050352425802801868210360018803011410074901c82c2c00069150242400450702040c035039443c0002075090142e8440a029042c0c07020402403014003a6100850300301c54810800d82500d401003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 664042526 1250 664041276 664041281
    0x2b050c0307050d08100909080403080702210a06060801050f01030201140909070903140105070f0e030c0604090e10020f190c0f050330040605060604150201151212050913 74
    0x510840c08213082804000400300014000c002600000c2800c220790302041d142c4070b2050041c0d0000030204900007501200755601c00002d8854116021411200c40f40c0ca080a0390b00d95400c42c1c2c085a03101d040c03003c04940302d6018040c2510074200c1c48901c4043d03030b1035a00115280b00c2c8001d00400d40110800c00c00180e501d41d9aa120711582003903c500a18615500d40040c2c0124104507800c6541d142200340314030b040d4030140c0004801150714103003a0204062000030f040003108c01e1f00a5010100007000542e40d40c0e546c210f21002040380040e00ca1100c8142008010ba10402849c240b8a001c20000c01c0074054405416401250301440c1c1207100d0061560b41412603060000280d5203644081145840082a694401c040720a0700320380f070a50740c1002c010204020b0006e84000c11440d1114002030f420303150141a5801000c44139481880398440b020060300800b0306010700c0104450610011031a1001420700c514000c0d40302e800030ba2540590203080324035401001c150740d030041043c41280300c0880c44d130 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 664043776 1250 664042526 664042543
    0x1b050106090912080601080105040506030712050a050124090504060b040c02211e0c1203040309030b010e0402130b010315030c0816050312090f060403030309052b050c030705 76
    0x81c03000902c0100a08107401504880c101460402070703180c04010341640c1c400e454504560090b903001c00d0755140d0500090400110340c1160400042680c841424084002000c1e2205030055008005000c480c1c01d43c407000314074511030132020f00b82d07880e01004403040c190701c95a4090700403000003841a6003040000d080d1039103c540c4d00700503404413025210419507a42c041c1d805910120381c7c0ea103030200d2404400340c280c09030740712030710138500104440000f46000d0150b112041d04554001f40e6070718242c0340152201406001c2034601c0d081490001c102c46d2205079407240125002041502d107030304d000200030f002c1c041c444805410183c940c00c3c12030059124148001c0030358450380840129508250040d403405008103000a00380b49611070401013902c0c00700341c410000090740900b40e80c5103084170125002c9140c020081c0d800800c00140003040c180d1681c0050b8a4074456815107201070501e0029403580e8002d41442c0d0080b4100c401c2c0310001c0c50198000b065505504020b030380c2090216126203041c401903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 664045026 1250 664043776 664043789
    0x3071104270c090204060e060d1803110d0e0919060305191401060605070b1e0f06100807080612101103010e07020307030203070b150a1401030e0303090d1b050106 71
    0x21040000420044140d030b0405041c42590031410706241c04001880e10203503841d22070142c0e0001880b0400c00c0c0711900301007410090004071040d40030742481c00400c0c090010802ca2540d006200030800f000748182881100c8400080c0100802e0720382c00500c40890094031a100324940c0c0c0e4180001c0064000d028084001111104000440d545030a120854408043d07045006034980b04060100c250460103a6810a8100180356a0f9940ba6105e010b410701d9054a00503400b5510410003c2022410242c01d10a560540d40701100c271310000c1003510400c1003a203144003c10055400100a804c140400030603c4d04424200d070000c102c418013490072115130011001040e10000010b00101030025212034104490707100651825a83c7e840c025141d001d8450001c20000800011828410241000002c01100200100c2c8040d546000d00103201640244840c04213080c64400c811280020040c0d0348103c5000c40130b80030340744c5001c0b0100c502c01441e0105040300c20000290a010030024403610002c0d000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 664046276 1250 664045026 664045091
    0x601081e0a0b0c03041b0305030406120507091a1c06050901122a080d120f090b0a0902060f0c1b040207050d140f0c03120105040e03071104 61
    0x54030a0808155200d00900d8501a03001d22285000908000c0c290355002d03400d644010785940340c901c1c002080b890104e07004c0a0400d0f080e00c01106200c0040003c100322041d41e00d4040806c0d2020b40b215050720022a0307044c1c0816503070b500c100001d2100d1155000c0c0210083d40743e51902150340c0c2d1203034901c8510f01120700000d5540609202c242441c40415000d89240b58241880340c215580780c9011024002c0c5442080000c1c9100440c440041c4690402521282c07003a0391948988440040220f007500220004c03036818003d050a024a01d48a100803658202c0c1e51112a60707981c140342e8000d03206812040742c201c0020001d001408070458044d2040888a0000d002506903207451561000e00700521540706a104010940000b14001522030490316541060922101801e00c1009540110700b101c0086e09000240000c0d00d810100080c690000c021004101913605c44050000f102d0054118410660040040d60f002c5258601c2011203014000e001084a1402c00c09604034040d11810302c24a564 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 664047526 1250 664046276 664046293
    0x706080108060a0c020c1c0c05040b130c030908030c1909050a030620070b010608091f090311010c020d030e0c0d0b0c04080a030c020112052a07060203010e06031506060403020f040e060108 82
    0x8e00a05540e0041004640500c0840903000008460510388001050720a5550310800c240340e0103a00121040c42c1c003c000305441b442d0140910200ea8040501510002c0314910500052809055034100b9140c0240c0035080050940d034400d801400c1c0c2c06500703034801640a250580604410703006103c420700c2980070742c1e425450454058429030b00605040c8880c0c011030944040d0001c0044504108443e086c0003084104c0141010380700013200100142d0039500300f8110000454001402c208041240d6600300a42c02c3c0e180e10f015110a550101c8a900401c41d00308880410154450540c102c1480107041d03140070f0f52820300c03502c0c003003140c04120040383c80144414250f44e0801c00c2404111505c0c0e5090140f803408101c3c800809240c080d400140004600304110b010564406681d80d4543c4545c085540c1c4d615030483c151951800c0b0341680c071034816288040240a62040c100d03005000c0545100c0c00c1c07070704640c20003400f0a51100c001d60001da8410071034444050400040d8000c240140140104d80c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 664048776 1250 664047526 664047533
    0x230901090b010807121e0b090309030c010c0807030e150a03150918030807021002040306050405060907080c101e08060f0a26030c0f0304080706080108060a0c020c1c 72
    0x10340168449251500b00c0d03c4d08210b141290350b20b104a07a46c0c400201071079006003161352200b540360948042c4c68030550750200802110000004e0070540c0c4210200c07111203548600440e0b00e402400c030000c0600005005c5d0100090046c0c4034800c480a004018840d490468000020705800080991700042c0c0c58a1500c2c0c0e241c9902a074001c0903220000060110000c8003120106611400306d00508000c2070f00c3c00294090f2080c0420300703500402020955845a490500002800094a00b900c0a00440c13011820000d0001545802c603002c40000d8040119880d04200e4504a4904108103029144140400c4038100d40e4003000303204841d44400032079090550503c00344410107821a0300560f40408c041c014054042c01071440320a002084100701242e521206007940655400302c1854801e0980401e06500c01101030020303512404d04649a85a5800084604902c01c2c0b01e2400d10750044c0f408500152400c1d00a1340503405940101c412030f47e05031011988003070111510280104015602e6400c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 664050026 1250 664048776 664048793
    0x100317030109050a0504050c010804061d0114070c03082409010b0d06090204060509041107020604080304031a040c0302010c1a070e040b030304060219050c04061211010306061223090109 81
    0x130085103810082881c2c180d82d2113650b1580300c032a1905100e1100001004c0002d0340d00020340d503141c140e501c503909100e03692455019210040006064802ea400000c0c0c00520034076031803001a40540ea01c030710a4840c402d03240820040403107204141d401d01020070400f40c036441a81c900070180349000709c3d5103c00504650080307600b02d810111005004220400009511009550f0740540c1140d0014405406411220761489034580080d081403011070001840030000c000b0f0402c49000310700c13022040342d01c040c1c51b2411039004c480041901900344014809944240c90710704450744203c10300c0421486000101280030001c6803000c0004081c01c040901c542803d01480003285400c0c0c004500f45405c1c4040a0340382c0601c100b0040e01184500e60610038403000308220030408502400130028540c866007207440c4242c0700101a075000d000c1c00b1406566510274418481251019903550400c000e904039040702038603031081e104010b03407480305e07040d10b01c946007080c550301070219500002065241031411100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 664051276 1250 664050026 664050031
    0x4020a090801390c051926190203070507080106061404150309020619031d0a0c060503090c030105010810140907030807060204081006080c030f0307080310031703010905 74
    0x84045a560019400b14651110703e016200d4000a900c805820b11004495000080c200078000b4401d82154905c00c0741d4100551b10500d0144190303450343d0f1200303450541c412002191007400d14004019419945070411652540c000c80c2d1303c1a01e24045180c0c0b546807600c2216088401b150355144020843c00e0780210741c1e5000c110b40315041c0c0d8141490300e1121410344900100c014141911401071000315910f032000c85000a146640c10400814150030003001000040020030a82c090144030354040c040009512010030b900410584415040040850f5203410191608840d803045101601e02c607a4203000e10340c0a421200c005024440d1005501d038180ea03040491010308801c050240250f10101141d4038060301d4001c10410364030001032a04c80c0091003564010440c501030381c04c1042c0841c2098000d031003107c2e0100101c449021a041c101030b140c0440981d0187d42e40e204111200024079603001440d0702c50304400e011172209503251034080d030405510300b100400a00c00801488108844c3c811b864 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 664052526 1250 664051276 664051301
    0x9050406093f080a0e03210f0a06030506151504080a0213020301032006070b011502010f05060f01110a08030112060c0914061c0204140f0f06031f0504020a090801 71
    0xa82684800b4003070904407001c3d0010240c940c0350142680c1d072a00410407500e000e048440e80349142003245a4940d040c15040e0340c205119100310000c01d141129a00070324040d01d4000026000c0c41c1c61303507041c101d042c400d00441141c100c0040c403203254950480d80040c01c01800c4050203010b84100610400400004917122584614414030050011035404100078680ca070b550b804c41c4030071120920000d68103000da0000280310b550504008140e082403080c0846110455130002d1000300d910f884880180ca02c100c0f200c68000340b4481e5003024a61040a1078054001000142e5850141c60b4170b55400c0c5074026040080c0141e200b009420422080c0c0c49204e04403501854003000301410801541d51040d481422688036900108122803010300c100358801c0442a103020456442e0307030302d5105421a00407016903c0c8141405e00c0c0001043c10044004a460807008000341d03d140c0c2c4900d9a41d400c040d40080d4021074080751200031441ea03e07180300030306485084d900c0e411182c0c3c0c0b41990341425105180c0856 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 664053776 1250 664052526 664052633
    0x2130606141801050c151501230a0f030b090a05180a0312110c0615131103041e051002030f0106030e1e0a0b0408040e0f040c0905040609 60
    0x6202039803040144420070b100074a0303c01e40e20362500c0050f0f840c006014200c00c41a0005100384480d01c25495a8040d01003002e072901e00e03007a08080803103501030b40c484402c02004501004265440b500c83d03070080521251a00b000a084c41aa001268025008449130243e0070350300d00622880400c40d000d004030300e941070f60041800300c64994000704100004919000b600c0c0e11a40718181040602055a0388510440f045500901c1c1001a0248855107109047d000b10312820481e91114540c1c003c0d18041300c0c00780c00c2245181c407aa601c0d089050388290004552036250345503e000030b5024428840c1c8003850318805a01c9007044003650402007010390100081c18545602251000d101080040d1901d8800e0410490141014035a40c02c0c600102e0006001800c0702040108209240000c0e0050700c1226521a64581d19889504803c420030b0710041c01400000308100a00c03a0150044c5a00c103100c0d10021400269540d81c960301d110388000b4203d0072403010001c4642c2400051382507190b42024140c81c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 664055026 1250 664053776 664053787
    0xe010f050d0314030c04030f111903031403040314040902180f0102192306100e04030c200402071103010c021212060409080f04030309080705060a0503130213060614 72
    0x2c3c2c20150121603102d81d107000480007500c0a0404000d603401984c020090f0310305150140f401c0a841400290103c2c4140382000c1c0d1184240456900c2c1415a03604d6200c0640e00400a07070050044e41004004600300044125813401c44690b59007e000201071000c405a00c5500078911380450348101c02c14076016020010b200c00c110380c1d001803007145003030a20420041c40181c500340982d0b100342c90a0b07000f840c15400043d19013a0780000508a2081140701100f564940d2030b0701e00c003d0300484c1602c024000620403858400031400074100c0314121000031215a031205020310201d001e0b0780001038255021050f091030b02035107007002c3c0100c41406045201920b81a0750300c4d4180606070190403080b0020a1000001031025100c80d0701200340365030132005054032104180e0700c102896019000c101c001506a03200003039111000030b03844041c0ca6004081500f4509428011a06500300800000000030580007030000750703e41a01c20940c0300050300b000b140712801e1031070150031061005403400c6e404508112 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 664056276 1250 664055026 664055033
    0x112020d11210613110618100c0b01080321100306141807051f0c02060f0304051c02060408160b09010633080717090d0801050909070911130e010f050d 66
    0x3000c04d04d82104503a100d807948400f034000002c0191f01140282c200c1e06000d01c15031190b4002c1d620340a0140304d81c1c500c043c41e84c0ca801030140c40380660340300e40c040302045004500303001601c074820fa0344c084801d11141442c20717500d446607415204814100ca44100d20780f0107019041009460008030115901c00400c1d410385414040789501d03900369403440a245400080e1402c691080885c6000d0780d07001006103850700451040c184499000361000c45440c0303d0082031080c521391030320703100d004031006801810b256a41c988500345181d206004840386c80c0d03518141000040c41070a5814010b10302140000384840c02c288608022141030011040650800922681140305024407185004d10502c8c00b442e9645800d4004d544050103140034080710102e141c100030456200085000c407007101c0360b0710000c00b642d1725810301813a06029200951140c12000c018000b08201d9005070806d180858501464052803903104016141103410425001356110b0040290640110300c42014041c11110410400e80d50354 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 664057526 1250 664056276 664056293
    0x1101030b010c12090f0807150809030405091b18040c0201060b16050102090d050309090f010303080615210108060903161203021c020d140112020d11210613 68
    0x8402441003000c0e101c0f02604900c1500c5410060940407241a04192200001902c80b8080c1c003e40001d103030445014241548100306844c01040c0c117801451402c2e040c0800d02c45190002407492070958841001802000724200091803076124010060019850540420060714081d9005404581c107003c001d00a42039000200d808003200c811951803909520302e00706002e40a0300c031196500c00038985504041c09030220041c81c554138112464100ba5a50600350b4495241c2030001131700042c0d2002c0003540e00e040101c00c1c4619003607042d1000c0e0030a0344045008a001c0e2070fa40b03101100444260041200407020480b42c0d03084800c2201542c00c0410010740401584410340e400352100c9001e446038110340f802076045404140011301d54020685a07010154082d5004084140e007071403400058980b040300c0105028141d4841d6858078245004503000c0000e41c10545100307807011090f40882e014655917004100c80350606010a40c48589641d0a44600303240000703000703a42046200c1c807800001007585 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 664058776 1250 664057526 664057547
    0x605220b030309131e18050f160b16120c020f030d05070f06180c0e0708071407030e04020409140a0b090105120a0b090606030d03090b0114012a1101030b01 68
    0x1034000400c0d070121800005c5407201645a4000c0d40c1c50010050303100d44118143c42c1026005900300d0703000c9007104400e590395011051841c0c3c0c0c18016620f0074080740306140002e00510100385501304081c46030b83c940c1172440486005075400702c3c2c02c6404003400c604180f2041c0c10030312400c9000d440340e0166640050140d114071400148900c480220340400c03c0103581c04a5041d90500551200c1200c2d20320340080e0341c480901032440a0b07207410700000c90340e51150040a10414042d9180d00c0358060140030800d10f0340000d04110140b04984040c96000d8407144041d1006040d02c0c00d0201d08230202d42401003400001905100c141414945510055103a0007201d13811940d050701c9914400e106c10105d9404d0400c11a0b00810340c0c8420400c1c002548800100c950082e00c040b82a82c00a80d80110250115900814010314116041004002c600c00f0030510410500040c141900c043c2c840742034a48a0f170002c0704040d0842208400d421092060780d0030f1303c2d50400c0c42030070100107041c0d840002a1584210 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 664060026 1250 664058776 664058809
    0x9010e0a05030f0c030417060a05060904030212030a02040e0a150b070f020603130605150f12120a020f0a15180b150301020f0a02150703020f120a0605220b030309 71
    0x10113501e090340800844005040b10316030900005010146a62101001d0b5542c400c640c1c03d21002c1205854424001c5001d1540740d00208801d1014103800b41c41500004c00d0090690350a02c03000401d0403450343d1041c440c0c1004000000c3c009006140380d0001803941d00a0301602c002408140c000031707290300030806a10b40480340c40c1d0710303996519140480e02c454000001c1140d070400b02403080c900b4499440112004080f41e00076880c400610510510010402c0c0d5108298405065204044420300050412021354410703116850b005020052501810003000c6540020300e82c000b08000c5041c1c400c0c4003015158103c03080f440420b5480344602110b0241c500144880703105120107a0740c1d400d504031106249800c01290301d45801080c040e49408403041c54a100c2d20102d00040c820301d2080c8203e40b01000314041103800d0030020a1301c03c100710030040161021a6440034041103a41d10b480d00d118000c1214105004d40c62518080882034802d0f002019020b60b00030b009140c1165100750001c034620301c0c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 664061276 1250 664060026 664060057
    0xf07020a03060c0c0b010806160c1403030f04031407021807090e0c0409050a0522151a030f150604020d1103010909021903030c080a0315090509010e0a0503 68
    0x114000a1414449039100401d510b14040030300102e50380013080c42c0b03009401440c1c1001287e0361450340d180c944500300c81501c514503003c01480055401759454820f014010200512a904602009071440c2d009840c144900035469081008040d03000451307090405404030b555003040c0d415804540381c1d08014000209040380e00c1c0014800314803c14507400188050045480b0390300388405034002c594807a00600c481e039810800050380341505802150702441881c410301d060010300c1600c2c2d04c441c21106008880702041070345040c0300d0310103d000f0007813201c5054440021250300002094941498042c204660f604201d45600b4682410441183e10000980d0003681e6540c071000400000c201d50304c0c403800402404000071a604100b82d0000138418801c0d1a07000101001400365800241c2074407004001030b89030303020b9000044a0001414102d4980c2c01e0100c0c03101041060390305a600343d0b42100c1e144913615010003e11540900404501d070341060040c01c02c501480d1902c1c0d4891241d40c03000c0d6000c42 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 664062526 1250 664061276 664061287
    0x100309051221010b0c190c09090201110a080d141006050d0605031c032a12180501050402190602031b0c09070203031b031603090303020d15050306010b0405060f 70
    0x75480c900034820b5030401e9411150396031510701900403600b091002a005104001c011189104042c502c1090715801c144150b9100d40761185420250032050000c9041100c45602c031821003004104046129120350200c07902c8000844c2c07200211050b424482d07111001ea142441220110140c52000f91001460000e5403181c0744210381c00a0a01c03944866010710881c2c903030700c04412581425160510895505108601014120200304403400c401c001500001501069080b80102c4e80038580c0c099052002c108464400c40c0079201c01181d100c02e6507142d4640003000218601040718200082c101405034110380d04000c0c00035500c1c0a80c0303400158210704801c84000c0100208034240800300000d0013000f407480c00e6038000f51a604162950b030262141d0003403030400c4000d1403040d644680c191803c0d000e10000310380b008070090070781d0800603410302d41d00b007194131000c9895009031407400f0542c070b410b4800c080c5000b050500c0c15030141e00401040c40103100611140d03485800321075030b4003000040b0940f1034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 664063776 1250 664062526 664062547
    0x32d030903020316060f0324060504080c061908060339100f030509150c0a12020403020108041209170a110405060d02101806091401030615030213050a0308091003090512 74
    0x40c094401d5140c8c0c085c0b0906030000300d10380e00c64003c0054400d51403d031428081c030142440014011084000100d0341142c1d2601051031240c1030071540020000d00f11007054408400c0304c5c001c030000e00e0740003140b100f220040c3c1c0b92100b811a80c500d403d40c0c056400005603d680c600040c80c4271800175205080688400118001110401180242d070410380b0000a02d030034056003010040e80b00b042d03076002240c801c0402c480300f414a07100f6602143d8041e16407650b66600c0340e607100c49140b5010701c01c10a104900d074020800120b1101011520744440d00107180303039911424418100503640429a10540c282420420a510740c1c1c1c2000400d260b05840f00092485148410784019004402070090f05041e12030000e01c0300d600402c5201201e072042803180542c450b45004406072800382c020394140200b80e04049070790a20079402416070200b0003443e402a00c1d1900000b5400a4255001703075413003e03001c148034005240c038007602c0c444170266080c00c1021204941c0c0f069111a200c154400343c9060201da05000f1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 664065026 1250 664063776 664063811
    0x61410090902041d070512060606040312110a030203040501123614070e01080d0206240603010b1312170d320718032d030903020316060f03 61
    0x2503020300c60491800d0b2542d606070b5184011b01c03d0f5840350b906400e40d00e12aa80120311035002d96000340c40300c0e1416003103865803902c082105414100300502d079051043c1034402030041c00340c1c1130f1203035000d999600d01e08400104128044003081c4c6240c1d1814001d0f90801050320f00840034065070b003000070480e40c2c101c4002c5416608a900c080e0800300c03c03003001d00f4007580204400f0240c440c100c000c248103907200c18041c4d980b070182c0c0c0700d8500940d1010011071804c00b90620710111642643c000c04141070403101c0070071505d42080c0c1c0300b07010f0020041b4641c00c00000303c0c0400781c040c00702810b98961082e4291111850303982c8413052012042c000040fa000614116004170300790340300c100c600c46142c00c00724544400140e141d40c41c0a40c102e110b0360101c4c003540c3c45039868a080080d000144442d00d421521000c10640d4203000000c403c280030740c541d404803034000b00030841160180c0c50704011345155006050801c1d14003000110400f00c401d8061100d0b9400c800265a04c090514000508401c0c0c454940b10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 664066276 1250 664065026 664065041
    0x30608071406192304050a06050f0306240406110118080f0304060b0402030103080702100f17360c09041208100506041e051008130c09020f0706141009090204 69
    0x644c40c1541400264125a40051088441c00d40e20070207520390f14101114140200b280e801a200340400202c0c4035442e0030400d84421100c1c0c2558025140003443c52010740d0351082c0c2c0f04c1808900c000c2e15207402210284200c1c03c03190030303945000d014540b156940c80164414140180c003407072000300100c0d00b8801580e0010801c00b401620840d66035840b800c00da401600031001c00c07845031002c0e00307006d541d6904c80c0d003014003024889e841e480202401300c500d000107407034020030104900b04046414140c4e202d2005c2101103020000ca519680f5445107415031342400c1007098064000e459460502000409096556a0b402c0c490301d0f11002c0764555200607003d01041c3d50100d0b50020303001c9030214004201d0b40070041300f0f9100d400304190716603072041400446d100002d184070206981000140000703042e04074070760304240f09800302c01044e41c0700c010140c1281c002d00141c0c040890045024400c10055100300303c12869031103207500c03080c80c1070411008101ca040c000c48030340b1910b400441045480d00d422600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 664067526 1250 664066276 664066307
    0xa080c010213030309140414070507050a02040f1b0906050a08041401050c04170c0d1103190305040e011403100e01091523010b030a0c0e1003060807140619 68
    0x81401c0c0d90303418000c00d401aa401414016022180c000b0502c0c0341071b00c04c44200c000280c8c007004003070b928035034152016000f0390026a001e004520302030006940e41d100700c180c5685810340000c0d456400d50b010501038206507026034284030301d5110a014158203c420390751000000e19140b1078594452400441d140d030141c4407440e1a41c00c003814000604a110094020382c2c2804c982c0701d4050680d0801c3e1a40e03108100b182c1a000720207140307d0004030b0118080c40c050031101800f02e4003840456001042072282c152800d900058021600303200e03880210036110f0052544101540c1c3c031070454030000c0d4948441884040d0102c0c1c0d90382002078100000c0d0010340c04030790001c40d202e40c3c6840304150f420242c80d0080111115010300c690030a0f051480004450507240d00d05086410355031201440e034000d20352000000203009010fa14084a6501e50710810114402c0b40e802086091801e502030340345c02e030280c22034050303005158495015a26030105603020404079148003c080c1c041c000381a50f8000181101c070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 664068776 1250 664067526 664067557
    0x1205070201020d06031a0c13361d0732030f010606020d110d08040c0b0a1e020d050313020a030b0106020a0614070f031a1c0b0603070b0d020912060916170a080c0102 72
    0xb210080d827a50b100044440071050081d80c0100c2c0d18100030340f1041c0d14083c044e4a480300c94241d030801d50307900e01009050341c402c4000c07400f028010b41c006464046400300d812466911007006104040d414000c0d003491030b2040c14404900c0480141c0c550b1900c1900d9001010010000005000e020322500e103c3e009104d514a0241d50310390007a4000d0443c0c0c2c080f00310341c11020b0b414071403c421a100040302e100f44c00c2c855803164290349510703080700c1394501200000d82e0700000b03001d8040003103010087c0080c02401a50000c111900441ca083c506540820500c0400700010204000c2100d810050413103802240e80f40010310405540000c032000f15103124000d4210743c0c140c00c40c00c800300360070000c019094040c9900d50b8050355070b0b40405564002602502c204050180014801c0078041d0700606050203004102d01c40240400711418580b80d0100c40b008036a40c0440038400103203090a42c0304000d0100c900d0075181c0450310300420303980c038110314000070002c05001403006a440800e5050381c6019450b100f04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 664070026 1250 664068776 664068869
    0x181e020c061509150607020d02130b09010e1e09030706020414040510030302030a0f090f1d010b0a0c060b010c050d03061a0f091c08030103050a0b090a02011205070201020d06031a0c13 80
    0x2800000c0c540c00b82140c1c0643309400012614001c149080e030705c2140316541039120100460448000941c019010029510040c41550002809170015001414940b0700c04009440540d04020541d400504401c02e1311b032043d00c05002107980072003240d80c5001241050728412009030400c565402c019070184070a0000c06401041c004101031009003911942c0c801d001a40e602d40d81d40322554400c20029801269140e0303418000140d040d00300c0c1c0c02403030050410000d503000300c0c0c60344d604090f10b1110303010000ea5512028000c1c13040d6200d405c2000d55141c42640c0c00d100c4543c4940385603200c1c80e08604d20811a4560301f281441003102d50000d6164410504e07604c035652403400d1a0355686502080b118240105d00090310980c0c00940da400c1d0a070141e4a1154030700741303d07440000801703001e080281155020843d0580362501d9004440c0214851801020046c1c011302e00c2e034905500140018040c14000c100880c03e4814244210080c0c42c4888209150381d400d0a0b0381d507460030162072118004450410300c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 664071276 1250 664070026 664070059
    0xa03240e07091a040806060604120b040f060e0c0103110702010507020f120a060b0a0608090a020d050c031f05060406180203060d020d0303050601030b0a181e020c061509150607020d02 80
    0xc0c000f1285114100c1b580d40d1206010070102d80614040c010510310740180390f070046035001441c9034200340501484000014030f92178820a813101058140021341c8600320006da41e50740f51255804c2c551030060300905192090340020180d00c00d0301030280c0f02c0d2101c0140c0074401e542c4c180a810011014004071800c80f0031a00d80305014280091400e446a180311100154840c0502c2482d03100355220000b428401106500304101210028001da40f18402d115032465103403010810300174030030480a01d5205801c8614500c0382690070003040e090089041c0181040303a01c04008041e410104021400360700c136611580410300071060700901940c490440c0000e01c040c0f41e091b5004602810302a40e05008001e80344060240404c0180b29078224040d06d461840d50b25041a0b0011100c1100305c902a402044000d50840c141d07044461235030100d03080a4280112110340c50420a08140b0550350302000b0f19140c02d0208080d50000304c2e050056000061510465072a00da01000e095070090605000c50710014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 664072526 1250 664071276 664071329
    0x4020313060b09010312050a020a2310020f0403020d1703040c080c0301090809040209030109020907020d0f030e030d020c010212040506160513030318030b0106050a03240e0709 77
    0x16007900d400d0700c1c1ca5040350b058101526064180ca810144031980b000a1050855040d0300400100c01103000d512500c2000035491507c4441845c02982219510b40060304d03181c2c1080a00f101442076144100443c50100c540003040d03d040b60340440320050890024140b803003450121005a00407403000001300010440c1d00c440741c1c41514000c000721000c441c901c40170f1600322858a207001d4064003007441168510301c2e0580003064400030190012031003482950101e124544265500c0001d0780080124501496002c8a0120404024601440340c0c0c9a58502d20303880e8030070202801c00d566000240340032892003d4044850148149401000303904d01410821b0300d80c041030710740c04180750030402812030892085c800d8810004802c401c00e0502c0d45103039000d5400200307030501c4040f0040c0d8070b036000010400f6144054020022616121313540c5102c540018219540340010390b4a0800c6060309030034104412030440107a800c665980303212a112400c003600c00c1a0958004244c4501c0300610465800720790b03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 664073776 1250 664072526 664072561
    0x6011202040e01140f010909020c0c090103080d0513030c03030f14040c0608070203040303080c030a0608030a020124080604060c270906050a03050d030c05120f091236040203 76
    0x1901400d0046041340c00b00001c60450164950010320104030510000e0400da00416407400e90600325802102d01c0c6011480740c240907070041d2922500810095202451405810f43c0030302c5404d03608154a0860f60041c0c10031707000407400380c00c15950710b1050b06030365400d6100c05902c100b06c40203185585001d02c0e02400358502030085a0000351504040381c0302c03500020954007074903410380300c00d182030790341d902e66150301e80009010205c1c0d941c44090002e1620010701c014560800c1e03a03400030406c114040141c400c046020420f0005885030500200310380903000c03c48035007041d4000ba01181c0340013000804c1300e102c0d000011000503481d5613101d103444085482102e5007120390954081c01290b595508225200c000380c131010f031141e00302400703211540d4800e03802404284d81c0e500700282842d40f00c007105000340c0e20440c4c041e001c0b610b03040c0a118142c1030401c620b003d6100c1000c8094a000d0300000d041e507000c0742c0e000850501d0a08881d2202029203204440000c001c07025104541328a4408074400c800800b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 664075026 1250 664073776 664073789
    0x9020a21050708031611040b220612020904020f2202040305012708031b07120201392328020309060d02090907030f11041a0306011202040e01 62
    0x2c05200088101002c0103445904509401c3c4848001c0240ca81000002c0e010180076070140d502c26080105680d101e9a40c9a090804040304001d079824035480381c100c40322078001d82c2c030300d0303498001a03401070780d801840c03541c0f1960603240c116503244151b000c20341400c6110002d124a105450300140705140c1580584101c0b40250024031040502840080c000e1a0006210034400d4001c040c240c0496138080c000d5411900180c0700d5800c01c030894032580380580005504072031066443c4501152651b0901a0300500001a6500108811100300560350701510b02d419424648003120b481d40b210b4051810428401d4019405050261070b0032000c00c0319a000c0380c40840f03242c4c0c40e08080ea550b2041c40a1b0305c0005112600118500341110707041020366001110216215502080b20025680f00c62801c2c6014010030380340410018030502002003513454000c181406140107100402030306034210281404008242c0501d5540c0e00d5450040391041c442c072400d84107035800010000b4400c17107a0000207040301e0f40c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 664076276 1250 664075026 664075033
    0x80c0a060305090c1908070f050928410c0705100b060705011409011a0603220507170705010305010b0307080601260f01120507060309020a2105 63
    0x21a45000e8040310410b9a400301070381c1c00480420f80c6410160490452018406040c2d00d0706031b981e8142514100d0283c005110300c1180c000d042213942454400e0035001100c01c51034040042c0c1906000d03905500510a44000980b2141c140401c00b505c0014503900300788184803000e0b03c600820a1440840300c031204410358140ca0341c002880d40380c107c41596141a8090302610742c2040d45160400580f40480003103600083c200040000a8000d1042445c09403446122503046d15000304107500b100e0b040340307400c24000300e8074441098658a00048076400700c806003d0700c055070181c82743c013550003200940091882c0304079240840c10740d40d416405034084800ca0100d810310350700c3c6c1d8011002d8030320a100706200d01c1c100703002048645018188a943c00300303042c5811328250080c20800c804071007101da0300d80d041480360814410980080704c1280d0140400d03040090600e07201c1c0e603a460b9500c015200d0740341055500d04040b02190f031280b034100001c144180562092201e503500c46000c0006981c400c40f460320 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 664077526 1250 664076276 664076279
    0x50702030c040b061b0106170105040b0708011202150d050420060a0504060c14030a1716020703081605031c05060103091e08070b070203041814240a080c0a 68
    0x645402a1004114003902c41c40c200043e04180b80c900c00d9040310302c038410f55200d031f80c0030841210540400469548800002c100350900d406c003140c00c25000342c0b1101c10000c5a2740184030004559000c03046941e8140e64040c64008103240014050040304030f107005881c20001030109000265480359030841940c42d00c20210f410f0303201045100e00c505c6000c3c5010440901c4100000d034010030345c0030a4a0300403040700c501800780d424402e08550100c0d540c580414030802c03900c2401c29141c5d60f8281e01c854001056202800c12020113036541407075120040000c200003920311107074022100c1c0d112401e0341c01000c89485090300101c0070010032107005c00c400c80901d404005055507102e0301030300c7c6040f6080455001070381c2c0c2040091010b05100b820941d0b17202020000300300040e416130056881818140d01440c1c4aa0030070030401c2c0c03610304205130a10800d08001c8080c4040009021254006441c848012500c81da81c10b0301b02c03164110045080c0d400003083e40700003403030324003c0303001c401030b0404603400d03401d15 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 664078776 1250 664077526 664077529
    0x19020106080d02190809010509130e0c1c0b060312070b040201080c0712270801052203050d05060a080a050a15140a1109030717100e0d21060303050702030c 68
    0x914580c0d00550194100ea00312130b0100c0c4420f402801780020601d441460a1103070b50100e03e800e03c202c034402001c25039074108030860080610034042c00389000c413032054424440e0040c4070002d500304400038000304030010220354507580400095008190b030684058555500b41003076103804004823410b0f4041241d103400a11110158000c480159a22510443c0e41525960040b40e01111140c6d43c403410b80b10703c0990944500300c80d14071230010308140c40003095903c0d1400c2c01a00680c0d882d418481c0d0700400e10707001d50000c2d4010094424511036681d0001e555542c25000031032030a000e621131b0b001806103005840a00c8008500243c2c403d0180d1122200c3c00400030400b8201c8605c40c90884403001490003003040e18803e07401418603003010050003424000c2d0200000d00b054000c0d84001e8008160124218050b40d00388a4808012071a0004104241841d003080380c0b0b56203d003406100704900b40140c04901c1c0b644005c00f40c4440c01001013000080d4917840c02401941c0503450980c800d200700d0180d404030307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 664080026 1250 664078776 664078783
    0x803091006031a1009060e1602060f0708090a080309010c090803191b050d0206010602160501080610200106060e0406030804030b13171804060b04180219020106080d02 73
    0x100c2c2c0e0300140c03651144480140d140310841020303094090282c0041400240701c1090b000b8680580640c1118110038242908429030300003000900c1401e540121301008250039188a40c1644031348203042010b07031a42c0e03911070927052060621004000c140040306000c1c00840540c403007151880c4075212754400d20f0311944102d54034022191047c004400060503009080d1248806804090500140020404035580d500b03080940d8400d407400181e000000400039507a040115204405002c1408905242003200080665270010036560007000001e000c1c1042a00c12480851b10010140307071403108141c610200da001c0c08140c803440b0001100c8100709542c41c64544500402c40e039000c201e80d8034207455903540c804040d500502c00c001c04d00c180310980002c1522aa8a8500c0d182c01e0b0f03000580d40e18041400f181d48544000486018131302e009000d1040c420001e081f1000d44504184907590520841c01d0400a0f11681c0b000d4a00f1390b0707007000d104014580541018003965000c1c3d0a9803010128904101c1e503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 664081276 1250 664080026 664080029
    0x14040b15090a0e010f0218010f1e0813061b0908160509040503130303180905040510050901090512190215151507030e04050105010f14090103180803091006 68
    0x34400051008140c2d00c10b000d40c40024407104040010543c0c0560000c40000c0780c00004000040c01e8218001e0100e940c0e00c180402c000e45828280ad2115100032010b00004e1715041c0c400300144043e03030010502c00c2c404400c440b8500c952103d400d0064070903140d41c100d0400e802550101c0410400d080228809402240c510313008150313000491b140a01d0681082007a9002038003d03903090104003e42c6030130000d003940703590107035010b510ba4150380c0b400400404000d08540d8048840a8904000e0000080c0049140d1a2002c00c04901142c1910b4295506004102c5200c00030846e00c075484021048407030b00740280506004040444050519585050740c403148030f12a0402c21031202000509101c654910901c988640680402c04094030600d440006a010036000e0700814000c01c41c01040c0e1400b80174040c0505420301c0d02c0012103400800143c104007071070340840c0c0c0e1003c022400854607440b03070384451000a845200c07641c2e03d070325a0030a643c00d03602c1510381501500810b15101c081c1c160791f004c0c540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 664082526 1250 664081276 664081279
    0x801020a080f0621390f010909150e090606011707050d020313050d18090207060f051e150609090a0f0c11070f060e1009080114040b15 59
    0x46503580c4003400001c0404000340a03a900140c481d0b403140c0c00400f0307141c0901618413160024188220500c000903000d40c4801041000307211840c404121144018106102e0b60340f040d501518030724002e20043e9500c846c035401001001e840d10030050303a0000024424001c96a4440c2c80161a4130341002050311080c0845030300e4041401d2841200301c88002d4a400b03640040107140c0107003082c18821307072003040c1d0b03009a4410010210006c2c0d4801030081c103004100d08044282414030001c20302025203060b03c3e225100d681c180d15808a84c010501c00e9035041010b550581c2c48081001e0705c0c20404200454511804c9600196600c0d000203654440080780d221650000610a07410500e070708080103402c0303070300400300380030745489002c4c5508000944c0038002c40741403603032030741741c031282c40c1c40a11460086994402c004100d20300d001003007502e401c9180600c52103030684031140310010031a8241c601403055400203030650720700070f030100350840c004140c40e005502c0395905600396112400c00b0000134080440e081e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 664083776 1250 664082526 664082537
    0x16021503100302060703140412110a0f09020706110c160803120a020d0f0e030306010311090d020d0302210d05070c02010e10030605060715050108070f090b06121602070801020a 77
    0x6001500d820809171540034460b1611124040001c182d1500036007203540160a040010600e034401c1102d191690a2005000d0701d120610620b010303c19500700009214080441d41e00284110911000ba002054407200c185000d42c2d403040b051510940d180c081c1f180c007420728503d010b00071400c04000b000f00c5501d1110044403030015261817103003500a521812900070790303035074581c0701c0c0c8000c40c100c2c090300f850004000040c54880c50310600141c15544401ca65030049042000002ca5030765440d826000c0380c68048c1d900410507906407406034681000030311005025890004034424034501c0740000c01078200d06e0300d000c1c407080e111b81d80181c41a0289002c000c0c003050340703189000c10302c0c18502c91010700c05040381f4001c1403265654000c1550381d803104105a1708262010b00d59280c0303040a005d8240113125a02c014010585030190840c81d440c040d010304e506072622032507042c3d010740c2c495041d42c0498038803a218081c00d09041d49116042c0004c003100f1009800703841d200080b0001d041c402d0704d03903901c00764551 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 664085026 1250 664083776 664083779
    0xf0503040b07050c101b050703090b0d020f0d0b130e1b1516140a02030a0605040602120a0207020306061c021201021207080a061203050a120902061602150310 69
    0x2281c00e040c4004210324100101441811940c0b40100701d90300031045611000600c0c040d02ea10341c0644880d0a402d83e01c01e01c4010001c10300043c0c0e016148108031911884400d444104620301c0b20043d118141703900105210102e4076240300c00d0780b90b0010070801003c40b03000010282640806c0b0907508034405892498000c0121302010360710381100d813204c4a40040890540070001403620b20190031a074485a5128001c0b0424400c22100741814403030172036810024401c0030101d03400607035100301c108402414a42c81c0e82c0840c00f00025a0150344641c0841c0100348424541810f01800039040000b06a100340f14160104469040c51031000041c00794180500080028035000d020040d0194140d08015660030071807081c200104940c00d9020300c1d207590341c004440c10160f265101355074040d00041c6540b4140c0c80c084000a400000312405101c0501b40800680321421503030008002c0c0400107500150001407281c1e80440721902c81c0c0c0010304c01c80313030b0200c001c0c0080d000910901044440340d0800345608030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 664086276 1250 664085026 664085033
    0x402151939020f030f0304050f0612040f141c08180d050a0e19030c23090916060203031b030103020f010c260319050601170c04090e070602010c0f050304 67
    0x201d2002680054082d450340e00307440b404646403003000c240080c800c0e003021a0900c09890441c90407845840110b51050130203004072240300d070560000c0c200070b207988080c0141d0420060f01088111074110380c0710903950001000b80c080e0b29601300c60146040044c86c0c0000080002d007800681d48500561400141a01e45441000341c1e002e6100b814007106002032403000760a03075900c414200810307480303001c5552034151451502580984454000c9880c540001d01d0b0403140940d9800404d81d19a01111230720502c0d02c030b82841c2c90502c981400c40300501c00c41c81401040700d680000003180500082e030386c0c034055440d41512800c400e00007800020740c8140040c5454501d50b2044104004090182801c50004400c6071080108080740c6a400c2240000100800041d4155491000d03284d14940c0400d00452400e100000c2456010300180e502c10b00d00a40401c00071030307402050310098034010300300f001250140c100d4103542d40c810313120380c9005600b04066011628450843d201c5c4040490b100c290840e144ca68 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 664087526 1250 664086276 664086377
    0x20d08070e0d0501050114011701060c260c060402130603020a050409031403040f06110301032a05060c060a0e070e1503010207150c081803040e04021519 67
    0x36031190740b00d03007030382035a40114a007032084034002d00401a00203d614040d200151803000310b4450b1078856078001c0300402c901500302c05041142c40c3e10141d2149040340a0000701140c256a202c03901041c038000c07e91004101c0c0c0040d540c3c6c0280d0088079a241495942c035110400da03811408001d40100c202d4004000c2820303d07030802204035119040043c00c0740e07080380340d2041a42040301c080d40c00c0e4260f04d20740313030600c0000d10a040031300414042c0c1c1d910355819500c40e40e94041503244180900b101c000324200c019181b2510000140400810007640e444c070f180301aa513503035002e581020f505c4d0320f05921090006000101c81c070032a5403d03520066103a4070404d1038101c080c041c400554140d5000c000e05030020782d000c0641f588070501032000040c6055081001004604020503020003010000010b9168140010036501114440c0503a604a5921403003c285c607405008503032034945402251451206c0e8030341c07402d580307901041d580300113032000359514590502c2c94050040c0308540c0c2c05005840c03500d42c0030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 664088776 1250 664087526 664087547
    0x501081902060711032523010513050312180f0d150b060706050a0c0c0c1401051e1c0902010c12051201090e1204031101030c0c0506100e07020d0807 65
    0x103400f0b8402c44070340300b800719040c41d02000e220740c0c030880b2411550032900000c0342030308068503012640101822020741c10f60208041501f82d5418000e0100b08900a4240a400140034100203001c2d140307082c0603c0410351450f045a4034503020321400900021090812031600092103034000d00d0301c2036617480c50311641d8942034085e00034912182c68043d80e14080d210032008080e5103101e004005442d02d03050034100100e5400d15448c10411468038058404210078004c0d140c01d131603920318020700442c0d2150040e61503206401c980010070b11000c010454103c0094080e0244490707007a2000348058401409808030307900717800000d011075001a006400309109001078071100c00c40d402c02d20300e044410402116543c8007640000a81074480304440c0b000351040c4840b418074002401804e0070039055540d4845045229140307036042543e540d55003501c040c45003a02c220b409800c0810fa40c841d040c100f46d0783e24043d02d140550b03409019203401058540e440018a2410030383c06940d50351040e121840c0454086194 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 664090026 1250 664088776 664088783
    0x5010302090d1b03050a0506040c0806090706030e070915080c010f0512040804030b1603060501052d090a030b0906070518012f0109230601090506030a12020a020405010819020607 78
    0x229040800080c03002c0012206c8540654000c02d52403403c7c0c40c00d41d00d03000c219040b6440a8000800b48560a48001070000540d0b5903828082000209050301628113106903120018203410110071051044c442c214400a6070b42020a44940e01044001501d01517004498a800524108466080044d40c080d1032a04948070b46e24407850581c1e262501c84009006403404000036440511403200d203034042c40b03880010002070a000341403110303095003a0a004007d0000c40f62412041c4029000d0b4850300c0f00b10752000c480100380e00c000b540c032400d004a01110807122645184103000218204a000d00b00780c44580e5200500041007071003031001110714161001c1e40e10100787c0012403220101d401801050500c210840001410741d089040418061500d100440c074a52100104080109004110340d070549900820114068403000c01107841d085100c0c502030003450f0700d0420741d14031030350200d5503009460088906200340d90725a82c038980c33a084420040f1b19020b544210500c01414000007030300b4030350300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 664091276 1250 664090026 664090073
    0x1060912020d0b0f063a02041b02160f050a051009050a1401120b010e1c08071103060601110607031104031a06010809010e060114041d031305010302090d 67
    0x1d095990310b0003103109807600416204003404021030346c2814214240c0f00d000005102c0e81c0c0203418004a00e09100b41d00c100407029401101013829901e4a820946148454014049100b107034208002c1d00c0c1d201c4001c1c40c059205184400064501000c0840d005503040100000e90344e40c03038001004414a166040002807043d068400522a0b940d031400070018440c0c1208a00046038140005140b6071013407905400d81c0b45010210123259038020606101000151007080c010714010360035030040056494014808500010b005080028090002451071000d07011950a9210107005581e24400c520410715144d00000c00601c080340701c1c0d004001a2a40030318500d2800b5141d85580410000c508480c000f41c052200511800f0b592080780e90350300c03060b060000c0154111589010740c5451061007a64040180441d0a005650351580002c1092410700d040281242861350303026220342001c8820302c14044030280000f072650080c0211030401c0350042c1103014891107030380c0314108029041420700a080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 664092526 1250 664091276 664091299
    0x13140907050d1b090611190f05030d0e1501060c1a060d0c1409370b060d0c0f050403031416050607090f0515091318030c0204060902030106091202 64
    0x16503c41403a80c640003590384280d420390500c2c40c06001139642410301d413841e6112510b4102c61403210394451075095440304a4442110081c2051442c0d070080f0300300762841516000000c425507400180d40d450440c49082d5102c2c00340c1e44c03803100787e030600903100c3d014101c441c4106011440c0440c07104055404440208024a621056280c40003a03200503044514050200c0740346101501d024000c4030742c0700c00660541480c2440c84900c505c602603984608402c0601c1500e01c1940c211882e8000c000d844001030030803034403001e400044002138440c0420316004035000413481d4080c0c6100b1030480b400e80390503460b80300390b800d280d00d00307071803180d11516540d2a1184450342c14800550203004290040e12944d444500300e50900461048003500c0f81d000901c100400045031902544c180c2c140c8004030170440d4071083d1a5440031491010f82408035680c2080619080b517103003019048001c0c9040c8074020b41e02000a0303602e404103001248400e00815020556034a0200602a18400400841440034045c5076060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 664093776 1250 664092526 664092551
    0x403030b120f03040e060a05011b031b080a033b03040b03011e09060e010b07060b0901080706080a0c09030212150a0207020f0a05010e0d051c0513140907050d 69
    0x30b0120085000c10b5003001404000001c042039403030f60803100031542c0c280361500d84000a0505241254101c1840501106a00a040c09080720b00b06140c552540d1140c500c00718a03108603a5031101d01108046498104911440c1d150030040b2204554030000030140000f101051030003803440c804e41030140b132004200110703c09000f83c000e98001c082c10140140f0680b20076006002c56510742e0807032106203151050400401d681120054111144414400c0c0e40d565141801c8001d025002d0b200354100c0f424600004907180d00154203000c41e08503503602c12142d210201180300b500c900c0a44400014480c07881071015190080c9d486010f00030300001c80d00102e03011320280d000e91004640000340d5a60114200040d82020b80c0d0100845508450203c91507050000283c030302ca01a0110758000e800d40b180400400a0402607510b60221910040d01002c41d5420300074640d07440301c10031001070619100d0015103c1a11a00740aa0000050005040c0d80d00d40d40100c40035000341445008541d2a070b031000c000c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 664095026 1250 664093776 664093783
    0x20c0a05060f1f0306110904090c05030d0804020a14030a0606060e090a05190209010c0b0c070c150e01050d06090e07030b180604060213030203060109020304060606170403030b12 78
    0x10603114030080c01040c5000441501140c00007410718100500b61203c086880c00b83c103880000b542e500800010301d102e029400c1c0c50080c001c10300c406800503d00701010042c040d0030b036400421118118100c0b80040c4403d1012102d014054500940164010a0a0001c060309540101800c5005012a25048010b445c2d4405413681584128049180b0050504c020304000080c5613105810b11400c0c8020308244d40c00041000349011071b5200c0039804500880140e126403441c8920300d4000c640300c0030f0f909107084503401035400044111000031054200141c05090700c00303841d18075402034440c1400801034000543c0d10390303c0030080855141c0d441d0008030b2141c4091045406002164005141035419440c100300f581601402040321141c81d41007001c5840c0d00080d00c2a801a4890b50258aa01190004007034044043d04002d40c14011a0000f14071156954003851103240030700d8003400410b5446031f054912000001d9040c800700f80103000940802d00a070001315850b0006880082480c0c10241002d08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 664096276 1250 664095026 664095043
    0xa02130b03040506060d11100e0a0b040503061501120218041406100503010807140d14030309011b0905040e0705090c0a02010b0406060c12170a0212070309030819020c 73
    0x300c40c040140000d00108200c8140c0c800d105540139030f0a2802d58540c145018080103031248103404004da1a19243d100e205c0500d207041d0082c048654854030b0781d51241e425081030081c41d0092003000001280010b128041600171034042e15906440000c80f020900650303c06040c80c0300d1303ca40d441c1600c015455910800300c0345001150404070504200c0c0811078078065202d00712003004400c1c40103228501d00812540100d403080448815401c81c80004100225061907014051440740390401411040101c01140700d42001c00081040303d80c001e00c0707003003210610500080000d8030918288041d0170f056200d181a07000360bc084500c016541c04c001840300c10100c6a81446c68400f080c9140d01c41c3c2c09000317040c240d841c101d5051010314140f010042240390201405400340710031401024215004180f20311000309080c2c1400301600d041c0b00424003941c01030305001c0000e0000000144030b1442072082007842649665a244982c0391140106034070b044500480c01c0540e802c102c8001201e000308681e06 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 664097526 1250 664096276 664096289
    0x3050a05030a0e37080406030902031c090e130c060809010b040908090103060509013b04210f08011703040e040b01050907050c0d121b080a0e0d12050a0213 68
    0x1c4051483d005140720301422846044034200c4c01c07620300020005001c2c1c03800e40713070145000a5007000600009180010742c1c1e08100d0300d0111803600d021107aa02c1055034040c0c1e54440300841c80350310b521140000c640d201c0d06019000740702040003805110703c00e580300d03134004801d41e00102c0d01c80400400074045884003001200d000000141d0140c3c00d581501800700100710403107032404950301d802d079080c0c1900760f0229540240115040503024982c2d404c2044510014000800341c514580380c0780008a142c0034480050103066599900030440b80320721074203c2040420307982c850030360340307404102c0d44400f51886440c4e980340001d00001c20180c3c8040401d03403046009440200301549880c06001c42c41c140074003c0010000700700306860f444400040d1628a0000a00d400c031050104001518018140701e0317013141503648600200b48500b580016100d0041c0010101000024285d00344039585620380c05520001c11550304501c1d03646880c59024a41c4010706403809464080d8107071211000d803240780c1144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 664098776 1250 664097526 664097563
    0x41b080d03050610030608190c150e090f04022107171608030403050d120f020406050c010509010506030a151b02033a0e0114090f060c040303050a05030a0e 68
    0x120306890000c4126a603449031303007030400c50141020107107030725205608150b00021216200800402c541d12011000920039041c40c00c2d0001c0342c014ac010b0030782c0b060784541845440c0200c00328250080c10842140a1640204095040d002c0c5000f06406802030b0301d51410540184c0300c000807044102801700440d05600e0000c3d0903154101c44041c407404070b464101c410f01c0d900910090001031400180142c10b01024100b031a00344610158050140540d054020410380c00070400081103a04070f8003500c1c042c0464402070000b0b0ba50b46c0300407400c075542103416982c1907204803e10030200304d1071a0510020080440c3c08075001c14907000502d00d09601e4400c071001603000003030007490389204289181c4045464204280312104010150b00c0c00c0ca108002414400c1d13990007402000e540960003040064415902c010702c0e8500021801d85550403403051230310038096000041c40c9258a00c007128280ca43c183c035414100142c80004072010340000701488100b035031b9404c040c030059104204841c0007801e01c1509 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 664100026 1250 664098776 664098781
    0x13020415030c0b03040305120a060503030403030c02010e120c1e090f1803090a17030d15181b08040c12060207120f021002091503040b04020301050717041b080d0305 72
    0x50300364107442e0380100344450f014000d1100103948201202d00005010ba400e640c95160000a5002007110b9400a54144400280003081580050310508058003d88030355110a90741d405200c43c0070404020958190408440c1c0c0e0058603290f0711100030801020003624a035048600801d002c44030507240d4200b541c00d900100107042031a480e50305407582032003020b141848a6800455a0410140201800c4c1424103181c4a1043d40400c240c0b0071500c00351344144103440d154602c0004c00300140c018000c0f514800d42d540c001d000710710300501d0341a8541c11401c09500b00c460204480c03040c0c015208684403000f1100010303c18105034103080f4483c0c003607080141d5442d11840e00c003410b2800640040c05102010800304181d640128885584030101c500160340c1d400103100081041c400600c06107100d0a010041c0004c2c001020707034143c4074910950080160791542141500c1d034000100301e41c800c84030f40e000010002242001c0c1c6d41d5060400006407110280c03195102ca00b8800900c0c010000641e583e400c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 664101276 1250 664100026 664100033
    0x204020403210903112116180605010c15090503030a050a06060f0203030601030515030f0307060501050402070b01030f02150a0c030e0f010c1e080c0a05010507080c0a081302041503 79
    0x10900c042040c18003c580e50710b15070742d0001c00041a007400c0d00c161a1001424030b20001140c8400e400c031008000d840c102006407403008200c40c018062400d0300000a0a90040c42d04d40b80f05501c19500142c5514245c42d0582c1e59135940c041e00b150415000a071100400000aa010030186008001401d008a03561030f10000d207008443c207a0380441c1c00c100362206c4514801c0c2c0c011044036008502840e001c00c03030351ba0314180710301c0d407080344140281c26110f51001034190040200203400128440d1406210a0340e0b520200016230084072401351404007400d00400000d00e82035000140c0c2840986030481c807a240c2c0140e42100e8000c1038041d004102003200d01810542d101c0181340c0c004404544003038109210100007030044a032b02000401250b1051090401051040501c4000307a41c081012562040301c54076250f1550700040c0c0445940d801c080215001e5402074190314800e4003929841401c115a4010840e00342038007920b00b500d004940500c410168407603001c0e44540c0103188113000c2c40300e8918503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 664102526 1250 664101276 664101323
    0x206030103240605060703030c0207031e050601090b0a050d060612200907020c010e0a1203030e06010b0901020a0b060117090319140915130305060a0b011d040203130204020403 77
    0x4804070b41c1103160031814481a5034107429544c0300c1d605032038000345041550344107a240845d9a040548000380403500c0000c0251014020810300d0300c0b5005031100340c0d81c0c41c40024181d0701c0c004503107644101e00c82e00502c0603003800682c01142d6400b4a501080c0280d07165074822121584503000d403582071080355003090380b81610304250390145080c1c54910350f928280c1002500c51200000050400c4000b04650b000c45c1e07035517240030b0080e24001203191029145460301038010036904400e1401c90103603c00001c1c0440e600805d0710944241a00a040c0d80ba085550b4444001002070415050041c40000074079400805a00746100b8040309004540d5514807a0004044035608210241000f00719081e0f0044503807044151034840d113042c0c40744c2e400034902c50b03030107109802824024500c6403140c1c0382c00024090005103040c0202d1011008221903050746004441080c2802080020751400001c883d80c142010380c000c41d071103504500b10800c42003c0e94001000e81c2c1c8154001c2e01c020546400307042c00c401c0c408 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 664103776 1250 664102526 664102583
    0x1f171003110909070b1602041103040302160f060f030e1e07080d1e0314040308010603270311070801060e060310060f121523060306091213030206030103 67
    0x2c0301c94020501d80459004d43d5012103010365010182c1c041503000001045900e0821010340c0100107000e9500c0d03501441007107030812581900140f0604800000c45090a114071060f40d00019441880906004007600d40301c280c0381441080540d07544e46544c00190600c00c0000c210101102030f03006842c9029140d18100316608a0300c1c60390004042400e03841c1d04240341e00503813a041c0140c505050b5202100760010aa070000d4001c25602040c104001c15920119090580e90503450400241c1c082405100c8000940610400c00e5842d440815010031f020700c1d090210f0700501c1d811542e0b0540c030303243c8060a40f8070b1640085084400380d000d00116280901400307c00950340c0100b044094038141c803114a03070302c0a105d5524a01e0101004000348030300d02200c411041025031007404030b480c2c0b0405d80707400301d00020721a40705200355070046840d51401007178040c001d06801c1700401c3e40150070030300140130741d02021207400d110000c032034008016107588020758000c502400301c90301e844030004807403902d80785070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 664105026 1250 664103776 664103779
    0x90a03030c0302180112020705011812030207150518030d020703030b03031303080c120f03010905090f1c09030b0907080d051306080c0d050c0c100204051f17100311 72
    0x180501c00c81900d540003d0b1913586402d01e0880001602c41c000c4400910030034002600d554208010400c94000c81d1201d81c0c035852040c2d41c80008415030783c5088049020711080140318603400a02c04084c03000d103400c11500080c001b4209940808481441c1e403840e1f00c0411000c0826130040782400c140b640510500d2002c0c18190302440ca400046205410010210300008160101c0070509456084040040341c10072032821007600d43da280c6210f441034189d0000d01c21800c003182000e000454958000c21186800c514040c014081200d800c1c2504180c1a5082d03082410008110700c0000401e01400d801801201c1810140920505290416044c20485c0114a0500004001e4880c0910701e03a04e11008035650761030070904030b85841d40038110030711a000110b11380c04c0c14641404a0160901700802500602d40201c619884080407a0800c1e03014a1150981c841440007074106101e005074101141c00d00b041c540043e02841e2011004c00d2508150b50744100050428018800c000300b003690b9920f080720 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 664106276 1250 664105026 664105031
    0x405010806010308070c0f09020706051e0f1902160308070c200a03061d010f060302300d020105090d1e0e040e100506091305032709090a03030c03 64
    0x405032a1030391080c0600c4000d21010000840c0801d20991040440160040c0c044810600c3c1da54a0344c02c029403c004000d40315140307064042104501480461200c1c0f00200d04040d07042c0d9502c50507d00002c6e40148402c0d40b25000f54468841c03004140b0042031400018038071161222800d080040040400824440601c4010030301d21001c140170100300c003d0880d00541c08480302c0c20860114540300c21652008210724240380b082015070381100360b00008903610000070001000700ca0f030717140b0541d104c61102942040e000090280701036030303c030915554045501c842e00340b04a1f1400a45107024020f040500050355900184644040140800058070781c0c6490310350300007035080002c8011241c03038000744414440320a400c014140c649030003c00403241e540d030a584000c1c1302819100050f0000302c0f001c41c03003280410300140c0b0801c5800104004107402400450400d108000c04440030308100b00d08050341c42c00d048100403a42d0741c42109e03620500005014107501c25880c60040c0a80b12070320030320810f150 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 664107526 1250 664106276 664106279
    0x240603020d14071b030c0210080a0e1902060705071d040618021e190b09040e0307260712030204090b030a110d0c03080a080105130e0618030c0a051b040501 68
    0xc3c1d004418040d07030181152030340301341041481e0690b03103d102c4100003900b10b152030102141d590341003505148915031000c01400070442404c0b155459060200380d003e5142c00f19030030100076091a00240c217405120304200c44c041500c81500c0340e0f49040300c0c81072142895a0703004001c200000ca000f108605c90b80e0307121140d044841c0307900060640e5030811080d400400308049060240d80c540688004c6003013481000c410072910340d410414140d105800c3d0764000e42c109046458404c20002c11130344a140c00035503000d440352507400b03514440c0c4a00050f42c05031440500c04940807a41c5142e4050741e5213619100103aa42c1c2c030301121101035a145e10072162198010821200c0401c094511114103440d0852300366403242e01d9407404548112040d0000b0341282c230045941c00c010b41c2c22000d01c07410390300202c505910710081c203508001610180c1e030341d1001940240003c40c100c00c1c080040d0400d8070450606072820480032141e03007890842e003003000340c4440e404082d5854182614114404c00c1007000c4c0d509101c150f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 664108776 1250 664107526 664107541
    0x1113020f030606030c090d05070504060e19020c03041d070807170c03190e0105101203050a0c11090f0a05011e03120903050d080105010f1e03240603020d14 68
    0x1400020050b5001c0d020020009045d10014801c40d8071262000302144032015490404a0f40c80a05000385806586010000300d1b407002910302c0c1c10301c12601800b00c03500000c442e81e1040c001e9004410081c105100c24800410115481c0c202c0140a00342404212005d180c64540180524805070940081c01445565542903290300c6046550040000031642e641c0d031115104448500b4007403841040180c03800307203800f14248045d080035018210354001004120707142d4440114618503c41c00401140003000381d0450a07020300803c5184500a407400e2a00340442c00110780c80c01401ca4005014290302000c00544010621800307001d045da189103001004c1007101040c9510078940006848080914402c103c1144140009409980d111041c1c94030603542d0303007001d05071340b40a000c1e060101d5074505907824494450610080070f81068145a01701e0400e2590641c0208000076080e2014401010102d0400b481100038000500541e0b4006a482c01100d80f5601225500b20a052450a55000b8405030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 664110026 1250 664108776 664108807
    0x10909050a0611040f0308030108100b0a210606080d0909060b180a080106260d09030809030f01020a09031b0803071506050a06121d1e19111302 63
    0xa5079403002e400a4100e0050b4000b1905000e00c1e132200d200e0380c0b81c42001200f00724204015504a400c10001c5520078440207140b1415280c2d8142902d8204006200800c001c20594004c01c40544908071404110300140d11a0820b855180c1c0044410340c0c8453341551340c1990146084008140b91201080038078200034001c40784c0d00c100c00d9200803000412038501000d580c1c0e030b4641001808040b008006150355a0210036000f0060b8481420030398400c2c0403000d16040110316070b21707200007990341d032006130f801c651301c00e00c10341c01c00243c85816102c0c089541e0080c4038244002c2034a40324603103d9500c0c1c03a01d540b80252040c0048864102c003085101802c006007000001561401940960014403441c80022400c00405156100d298082d1420200003009a000060300101a02c0083d0511850131504180b00007104090b01c0441241e1122401c1030f00b51401007585080d0a178200160303045c085503101e411039400c10604090300c5035000d00c0096201c900d42100e0300e00074407001c4e110039410400c0317050080c4c45 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 664111276 1250 664110026 664110043
    0xa1d070e0a0c022a010f110703060e0316031806030e0613050a050a060203010518060a05010503150406140307151e120f05040605060301021c0f1503061401090905 71
    0x480d40e01c0b0341c0300c60601c034001e205034000d940344040c499041d8080e03c503d401c2e54084180d4602e0100713406210751842e06204100b90f403d124005001800c4461966880c44000e002035110a560340c0800d11800c090440071b03080b0307090540c0c045d9403014820341c00d140180c41c42c140240c0c450000d040c90050209412040460b411f41e00800c00120041c42e240da0f070800e60700340006401c0041450203004140010810144c2c06503060700e1090b01c00944060103074213040b420b0541642c00c17690101101034104079543c03007100215030000040100074407054606001c18191021900405825072a02103000460300341005184d004020400c10036000410301d010203001c40c4c04003043c00000c250120116180140075134180603105452020801c525903100f01560001c000c150b508441080c20007001c00e441785030500035121008802c00c10301410101000e00080100104182d036100715495006e24020041e6803108270004500960700400c0c644408106102d82c2101600400c00a600e460551404034600090300007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 664112526 1250 664111276 664111291
    0x703240e15060307080708060a06080a0f1512290115050f0a0c05010b0a0501020d050c0f061e0601021204180e030a050c060c070305120c0903060a1d070e 67
    0x10344544075504403419400c440c040701c03a0481000800e021485a000c61400e00c950f605913501d00090300c980c82081001c40d440d01c01c82000901b04008100b900c10b07641c0c030101c4050b003100d0000480e18404490b4000041e89540110080010840301d0b0003808156036035041d001e105124095412281c42d101d010180a06004031290032000030207410f0894080d60441d162040111740550310742104440003004500002ca040302d00e94200346604072281001c428800980748142c01074410580c0590045409410000507086a40706503800034025080c1030101c03501403024009085090a6100c8655001500180c80141154480322000858081171019101503030440142c0c0055151410200c1c1c01074103903243c050020303000015031080c205030000014a800080317078043c0c6d4880d5035031800410032030140040160205a0404c2904140714151f55588d80c010356010740f40d0304003c0c800010900e01502111100030080d543c8000c16100001e50100c2c19a0502c0100101451410540c0c01c00782e1040c040e2000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 664113776 1250 664112526 664112549
    0xd02160f0e0115050d060f0510022109060702040c0e091b04030209060d020a0e0106121803110f07030813080a02131a060304201912031b0506070324 65
    0x459900d203e20201c44810094820600c0865280c030b00510040c9040d10a540c851042c007010809c1d01c03400420782c080d80e008420942c842c0c610200910310100d5225081540d4003074410058600142e442d80b1400748032a0292750784007000d000d807200b445400e80004d0a42c00160b244480300100c0599580205da060b60390548140314182c0300c02002c142c0748025402d009621000100c000b04600c02c0b10300300c039412110980d803000811020b001c40d8100b25240320640a940e502c0d1009003130003090261800b10000c1d9a03003000c460780b0140b102c20090620300140c104950742400003d05c280301c9154646640041c241a038050120901d941e070001340c645507281105000281ca40c04610406200c2c0c1d52490240040504039583d24542458004010000d84641030090390f00d982c440d080324100a403094601044881c030341101039003021170101743c1c0300ca40e0504500700b0038062030084e14a82c23203228400560b0b00c00c0f00140954180f047e0701030282d9910a5408000c01d088051012700055015901400c650805181 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 664115026 1250 664113776 664113809
    0x504080616030204031a04060b06090904080a1e021606030e0d030504050705061209010e01140c0c070b04060309020f0306073c090911030402090f06010c050d02160f0e01 74
    0x64010b0b000e95400030f406c4215811032910503141610a00d03105500c2803030100020f0501c4001c0203518020700c41115040b160a50000700000d0381c0c0c5000740080d010324100300201754001204040103180d040c80960060b00b0640c0b1680105801402c2c0384068601d5040502c01641085600b654540c4240d1a11041503140c002060030f00c10244100d4024201c05000c16664070b154002c1e0300340d10345081c0d42c40c411940ca07141c1c42c4c51240c2c83c18456000c031118038a100544030b868915080050760003001e060f990f02d00a06600185e40d00140c402840145007548002c244040c240c010090016203403101075020790001410082d407580e0028110a110036030b4842c6403d0040c4212414004002505a027480d00f10440416080c243d0044a118101c0d400c440b42440003401905903014540000c0c0c030025040400c40000c6100127100c0c20f60940d02100c1890a141305a110380c44040c5041100d24100340580c000b14406807111a400405402404400c1100e1140300d01c0e2004503074141c1014880c442064107003540c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 664116276 1250 664115026 664115071
    0xe010b040203130507060819200d0b1201060609050915100806100806220902030109030917030a1e02190c090617030d020f0403060213050f1906030e07050315070201060605040806 78
    0x411508070407800c00c2c000d8440e181508198001e2041c0140c4611450b133030000b96040c100140103610076502d41e076442500311441d29042c001d407080043e2803e00041142040c100340ca80360000445498400c50b9110300307440c140384061019240c0141d040508015240b410440b40d5151643c245a000705501d0003d000f500d04043c3d410014204484020351650800c0581c605041e0720074214816281c40c041a05410050011496901c0c4a10b001010128580c02d601c01610032694088a440d07003900d0064480c1d105485003805008010b040301240c08148040060002d40b82500c16103024280b0410480031a1154024a40e0749004410344c0c0052207030000b95119440b2018800d49006551240040d0b4441c1a0b0105d803185205182c084c06d4020608890001070600e0111071240320209054801040c050410030210058403001402c14024400c500000495841c200000c0c52180254036904540f030508140003030a54886030b0007801084000c1c0000d11900d00b0104205400c040c03584105901c0350740100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 664117526 1250 664116276 664116311
    0x9060f0201020714010506040e061306051b0a02060f0106031401090213080d091d192007050304031704050120190b06100801180e010b040203130507060819 68
    0x710300400d440311660303504c8005901508003501031042110103100f0040030410169480300100d9401030444060307000c1c140400c0b40e80d0702568010419840150078800320031040303078281c0e001500110040e8007a00c100241e9445088126004d0980740c03a0610150340740c005142090081030182101140e400141000404000c02401d0000c01810040c1c403d007492086010700800c540b031080650034000030407141682c5e030701c0511030b52088800e00d04410010308942c030400000c109030201d00c903220800c4022400544082805410b041e84904011a5520305602e0121100b10309044040c0c1561024801800183e8000050703942111000d280c103d50700ca00303031081a29100e40c5e01441c03807041e11316100c40d60a0144000080c0e00c02c2c201556441d940115694085804003000d00c00c00811200078404c4034040c0620350000a291444500081140d50320100011b040744c2c800e94000c5030404800401c4020810140311407001895242414104c900c1c0c41001c01b210600c10f0704255a002d80e864820006c615101c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 664118776 1250 664117526 664117537
    0x901090506030c280815010b0412110f030313091112040b0403021606170f09030a03150f0801060e0a0b060a080408190e040609060803070209060a090203151f09060f020102 75
    0x81300c890389400c1e611310000307071555a50b02c1811031001500780049150185041100c080310b00740c1c2130000d6000e10035100c00900e50341c0a405140d0180b01200c00700d0807a45e00300017801e4032b103130240391007050742d45410808811918500401d6941c2401800303030303030014030b0709140c200c0d4016003007415030034903036a5850105d06094000b403103806054000d00700450055070005034054503449aa0313088203e078036450145000c010048480c10340c1c6a008101881d46548690000d0340c13039500f11800201c0c07031501c40c92800307280e041035084450260340d1044100300e600b100240598000d0310100301008000d60300e00100c0c40d6841013240c0b00081c0300000c07003c202000701440413640000c3c50349484c2441c084080e100101400d5000f000d6038411401d120cc0821074814921071141101e081c0c0c0000c502d4030342036074240803014400502e0a50701c103c48000006002a16000662261750204c4040500460200402c4101203010840c03443c9035003100030210800e50400106400e0302c008d41402040d10040341800c17406881034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 664120026 1250 664118776 664118839
    0x5010204060e090106081504020c0c0d05010c080708040f0b04030e090f070f02070b03190e07062606180910020703091d07021207050118110901090506030c 68
    0x10380054220b500c18200c05118408690f99030140c5da0750b510840e050071044e2540e10022585110f8000f9614095000f001203031200400e507005564250300007011885c20350020b585594582c680003402590002c41242c0c000083d0403e0801410a80c981c16445804240000d041b541d0000c003040516008009400c0c402d80010b2143c4914504403028030f04c480c5040d100c2c04082400311041d14142c1b070000c50100c0c00e5405800b845401c5a0341c0e1070ec0d03042c800c0ca0b00141d85c000b0565448807036001c0d03a001d100c6c2c80301070526030301e84118803034480b89128001c4020400503092521a2401d0103070b281d49081c400d0b001c248001c0e5011405d5111074002e0b904005042c4580e60803240b001500004058100c03007a18111500d900c6405010f1690320f482e101108400c403441001170f0040c50100110081000c058090382c0d000e0000001d000249003000710080c60364440540302c001d11030b0081d480c50b2130400c0d00207014020424081c03040341410400309075100d102d402c119228207000c1c07100905042000b00d00d100c00001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 664121276 1250 664120026 664120031
    0x41b050d11161a070207081b0d120504060e040528112d030f061207080d05190c0521120a0c20060f0601020a0b150111010608030f03040507030501 64
    0x40342c68440f41c1e001143d1510500a12004009501d103800030500408a5441e071000c5e2680f02c1d004814001c512800103100e580c024021420640410a05c142084421aa540b036442d45c1d142800406802900005144c038416800c2008000b40142411554002d412086c00c10042c40000aa06a009401c082d039464003030400104100c1722070b800752031101d040152000041030030503e0ba10030f81e2009100407510881401c0031900403803107038144110103e07811034000c000e40340680c1c1c41e03442180c104004084580d0010300003040392402c410180b200b8031085110b50600701c42a003520360741c41e5183d068100303003581810010400e4600716071651044914400200004035103925012030018020b00702407011000151b00c94800c142c07170380804030f5401581c4000303030000e00e02e41d91150505403003654024030490441c026100800e001415601d08240225040706203140600c000c6400100101204103035000d15070f040031010801080302004454a8a640d0480250340f5910ba00b05103107007800a82c402006580b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 664122526 1250 664121276 664121317
    0x10f11061915030209180f01020a020304030605090a03080103032012030912030c0d090609141e070f0902090a03020a0f140d0203061501020f1209041b050d11 69
    0x42100000030001555808001180610b628001000300d40e01000303402c10811307808030f14509480c80c900302032102c0c030608884101050038042800c8e0b030011505d890160388017003414401c01c006030103610780c400303010702c0203184445c0d041c1c80081611206100140500ca40c0701404110100c0f504003104c442d004c00000c649081000415000c0c45034021640214240075600319140081c48200c100e9001d0216541e986040c40d0300440100b005200d141e0040b203481d503540ca00303000080c1c1c001491403181e8045501a0548200c071040e144004c6444010010040d00440d00920501e45046101c1c001c3e0395130b1040060321180044042881c0039200c3e00080c0d8003003907623200012050744191180702590350300fa03003c82c0745d00318000601007a9804048000d52541100e00010030300141040342c074003134000c1441121003010200030014101705003558050403420001440f0141c1d410319025801d100340361040c0c1c0c42e4405170540300c0141240100400d60aa10741c8a2000400e04607010069840c1e45a011003002440c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 664123776 1250 664122526 664122541
    0xf0209280b0a1d010f0c030807051b0a170c030a14090301020304080d06150c08090f12030c0c090108070e1f0b19080609011a040f0b1201080a11010f1106 67
    0x2010241c8080c41d0300f0b15040701810b540d481840040305a51080c1c4805048821079642511110030045c03a01007082001d114008841e6070b0031001d101544a94400340441400c542440c07501005081051010002c0c00c014000313072048000102c42a43c00b29280450080100050481d460700c2600c408591640c0044107001c24800307100300030b08140082e501c0821815554601036034019081c400302101140d10004100302084041000b1300f07170710780e0040440303240960f82c02c00541c2040306444032809070b62012031185601c907000c004003181040e0456000c03802d98034210f840e50b03450400380950000c18282c0c50200c0c1a522011b902d0703c14541070600c0c003100460701c501c4c031458190411803402802e40101403889030303d1806000441c1c0108005408600142c1c201420745544400004030500d4040040100041c0d0b82021840a0007805141a603d6030311100250320751514401a04094100d40101022500103181c1a68100c203040e000c1c00d103001c0543e83ea02c000d44200d1480e481601b00c40c0078080030850203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 664125026 1250 664123776 664123787
    0x9030a1a0106140403060e01020c0106180c1106070c1403070506191406100908100203042d020114040905090c1f081504021303080301090f0209280b0a 66
    0x4030a80d551046a0340c4030702c11108070ba40c0c05200c4910352010401800401e8160b002603031200c046000140c0740c00a030609150850f000c44e84a682c010340300c01d07031015000d08207000b100c1501500e4072300702c00040c1000795041d8075000090002d0f010700c01303618022000c0040044040c0e11034603400040e42d48a003110b00b00030352180c0f41241d95960345400403102c5182c1d03001070f1040c18241c08150803c0940e541d920010303c281c51000362805418804285400103419508018004c040c0515150150300c03410245000c50f0212522070b58982100701e80c42c2ca64082282c04100380c0c0c001a024a0f010300d98402e540d41c90307142031140782c1000d64254100001c0218401d80025031502203041901c1c640f00d6147c0c5144954440c06030045a5000209291701140c00d01c07400c03900440207204000c000514124103040405642c4906078011510248084010049a2064405d90b8801001804194030308141d40c800200d642504900c007030360751242e0242038003070120100f84140c050240318103500d0342c0300c440c0c100182c030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 664126276 1250 664125026 664125053
    0x90705060f04050a1d0610021f0b0a08010b030a080708090901060c231518011d07050a030b010b071b26010605100c1113140603010b060d0b040209030a 66
    0x342000010004030f400c0307141d0403204a00c502c00c40285e05916151b0401181c0c440c1c8500180071885216000d4468004590030612800d01030940080c07521611030621002850b10f9001c0d42540e4501170403c00c040d100483c40d17200080e4496a016038441071494600000e0180c2c148843d0404c06c07010000c07650503042000c11803c00d003d410840404002c0341c800700110342c180d40d482002c903000003048691501000c030019412911140285844400e0f070321040d800c40d60800140d4002c1291806000082182400000c3c003a01c1c0030f4914020180c2588c40764a5261010310520500c4400000d0000c18000d00c2c024081c1943d05040840030f075241c0d41c4c400100301e95605101c1c0b40c0000c507903590071452070405120fa1401c0f2140070303140c40503401200d00240c5007074102c05420781e242c409600b0820400d9451107800c113040d61014400040c0716030070041c0090010b0f001003009000c0d0380b41c1512540c1954520090b15803090400101140a00c0d43e2804500039001d0389403281e404d031107100c02c48010840c4154083d003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 664127526 1250 664126276 664126279
    0x70b0106020c0a050a1a0d0c0305040c171f14070306050a230904030203070f08130b0315120a2418150c0e0d06050108070803070812090705060f0405 65
    0x3a00a0080700c100300c00f00e003a902c01c1d0791340084424070810600c030720f01340d00c41c13420b20444442c0e6040c10007800caa10142c6004d100118000707a6070300200303c1044120800800a0120911418010801c400040383e640c0311b00c2105138140040004a81c4d0351014a41101e252100021440003240c1072074000078020301030b01e0141510076148090045a40c20b00703405104202c2c0c00b03290507200980320f690140b03d58031001030020350031800208443d83c0400c10a00031225031a10803182c1907550b540e4003c03140c180e008540c1158958101c20010b1048039101c24807584200d050407115086600307584400149408a98040141002910707404004400e50400e0380d8402d0000720703402808030000704092906a42e5008400038400354040b48043c00c920599032086420846609110b0030f071500310000103e10001d02c0b94111501c2d1307142d070010310094600340108170092a4001c0194200441c590762090070780940c0101d100d40e03820242c005100200100706072001000d0250860390345403605154459154003500030f07207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 664128776 1250 664127526 664127533
    0x60c0f15070516080315100816050316111e0307020a080d1b050c0d1118100506030a06090903090e0c0412080315030610080f07290f070b010602 63
    0x450381e50050b001c69101d41401030000d407000301c2e00e580d101404c0d00003502e40001c0b1466080080007a4860b00c1d00c3c14440b2465446504803844c2503040e42c001ca0440d07028120030000140140b06401d16620100300300c06c01c007401c207004c0100c4d855115624200743d00400c4885404111080b44110030080300401ca040c2c0252000d200c11070f00e44904541e100d0b020000b01000841407400440e401c94018074015020b03110700cac00d955000c1254400150805143e04050b030307585140810540082c078224800342900070341203240203910300c0c001c040c1c0803190500f486914001c04000000a003079104641c0808060146800100101e400c40d050041601c0094021f048141c41008040364040014030f090f54122069200c1d0a4002002661001038a40001d0716a090324007120000745010b80d8140140c52094016071403070604185042c0c0c3c01c03850803900000c0090107800c006e205211014840c01c600b5150001e00d90b00040c030349615098030300207106100e41c0350340850010170f0b5101040811010b26040750440d5088 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 664130026 1250 664128776 664128781
    0x90b0d0822140f0d1a0c19091706060619030b0901080607090b0f030612031219180f0605070915030c140306130f1104090903020d050c0a030c02060c0f15 67
    0x611560ba0701d040001780c880324416450300c0d141c0720701c040b1955110303580c600b00a040c180100642441404400380c010081128030710103100b24108540c0300f43c00124184001c00345400c03d0404a01144034a40b80800708036075040385d0f9001c03a030090700b001d010800040d111800f250fa40c0e2544507162102952107000090301d145c7e0001705c44e0003407402c0c0d54410501458480c0f654407074104000071613540098440040c0400d001c08200c45034044212072040050006040f0208000d17840d000c1162109000b4480c40300807043c0302e0000c10021888400b4260380b0241c00126a160584152484d40f05603008490310101c0324260b15030340f9072640015515049545865100d4004c50806841c2d9010840311140c002104601c07042c14410142c2050440c1e00035800002104000070340c00500660207500308002c095241e4031404101039040010f041c0e80f070018504141000410144281c96a03114200a01002090140e0b00190359035102120078280c0c07104210b07120305041b800e615480c0d0b41c40b010402425200c0d00b00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 664131276 1250 664130026 664130029
    0x1030c090e06150108042a05040c030c080c09031504050c030c04061d04060b0613140f0112110d02071202070b030105030d180801061707090b0d0822140f 67
    0x84850190312015221400c0e00c041030011a41e0b0345c0d0050082c2d13444000528403181040a461140c0c1c401c01c4180850700728142040144001e5940700c03000003003018074082d83e1200380c40c1d02080568000c0c0650307290750340e40d40034500064941120942016600411b810600041102c002011724000f00c040d81945c0c0b0310b00d0b607113007004201d0300e4920400032070f00318002d00d0000e4040c2408080e0782c03003840f030100003900390755440218203250814840c0310700308607a5801c1402598a85000c1c0d09102c2c0702141d031a40f001c048500001c0441c03050301845031241da182d145101030f440d0341d0000d448004001c0501103441d04854101103010340b510000b59409400b03800740c08211840050202c9060b508003030003c0c0940e6107182c03801c84105111000301003011030b0344030010883e08028003442000303101408018074540b00030407a0b2400d0050a910001c241c40c40e025031082c4a44030000e82c0c10764950400455a15000143e041d00b81024414503445c42e0310410640210b50303a0a50304505c09817100503a41300310380788110320 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 664132526 1250 664131276 664131283
    0x1707170a0206040f062d0305311406131205041a1b0105010b09060918040803041a04110f0409060e06420607080a0302030a110a080c03060f0901030c090e 67
    0x440003804ca005025500700e40d10f0194102e1500030520402c9407a01c4442c28880249c04440c801514a01c014440c205805108001003450b0415281602904c15802c018858a400541020f8010040d6580f800c084c1c2c5254022021380340100700315140045010315000040304240d10501443c54080d0354034840c012603550500c2443d040c1d5450082b0b41d498504104100302c059017005001d01d9000f0a021581c0d2016a1250000342c041d922440c0150f842e81400d241007403101401b88403207424006031008000c0440c144c000e0140803c038058428168007030b0304c403020a0290240328005007a560500d08070b5000080000740325445401904140c1240d00c00196442c5010010006108000200500105007481c104020f0032492440100003a03c1c04003103030340b40e4620740c005100c03030030100b0360100410944a1181c004d00d403512008004c1c042c5040186100980b4584010300840f01554000c00081c05648030b0030303034000e803041005080710032a694a03c1c00856404103402256002402d00d044011050f1000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 664133776 1250 664132526 664132577
    0x203070906110601142e0e030d02060703020a110d020a030908030a1d061b03070b0708010503030d1a03010608071e0e01030b0c070803090d091707170a0206040f06 71
    0x4040c0c489a403a01d03024031200b007520b420455008070b00c2200000300c00c1c098224405c0c901c0c2040c1b02c3c02d822a00c10715001d40384d26007042d641c0d402134100064007402e00b035011400650007100c0d41001038445010003011610350418406480080c4100b03908400060b40000c0c00345c55492081d562610042d48813429a511380c0030383c030706e07550225441c0f42214544408801d28011088000b41146040c40b0085a0007006d4058041106a5036040007600d4014040c000c03444650180d282e052001840d450500880d60300d1055100c80d50440303507104110701c0ca00d4440c82c1c2c00010280020002d00c40d80780c4a412441d03c07203c851190038215000c0540d0300490303540c07401c1c80808544050100040c0c5a10f0b42d1180030b00b05800030010030b50203208003e04400175201d0350295002e030301c0c203900810782180c0600c4007170a00407258100d402110341d43c8000345020500081c904007500c25401c62920b2460a40488a1800c0c0e44020001e502400102d004513a802142074074030201c0f105961401080c0079150149030303000c10788 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 664135026 1250 664133776 664133807
    0x90405180705040e0a0b0f0a0b150304020d0f080c0f1c09060f0c15060302030d0c2a0302130506130b0303040902070212120d0e030909040f1401020d0203070906 70
    0x10807001c00c603074079041d88290400000f040c19070700400c010b65100a51140d0441d415080301d907010050245500b6984a5840558026188500d21a100c01000a0302d0702004000034440e5000214260801084040644155500c070500303d4840c401c114425403500c50040034416280f05a9a001801c080240407050750640c41c0e8584c04991410700a0458800c4841c40640e000e024080740e031000059449400f0485e00103c000c4002800c604510416090141ca40e00740c030308100e07001d18180c000c51408440581404886890400030080c102e101c460082c0c4580d201960100a081c0d0001c16013070340da0442031180008656400300801200005012918074210481c1c05a00034001400380c1d8005070f00900e001d074002042c4201c24610b040c0b42130300e440c1d07008500d507200c5600401d103011020312500480f41e000780060301a5080003100000f00e91032410003400504032840d4074900000740509000e0380154490800000d540c3d40c84503000c103001a50003650510001040c042001a0081c80b883e002007030402d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 664136276 1250 664135026 664135033
    0x7150e06190b1512041a01030804030204050105030d21140a0b100f170612031918080a1514040c031b0608150103270212010c0c0b041104090809040518 66
    0xb18000c0c0c09050005c2c002c86d4103a40c0d1039000d1004800c80d040e5a4025441002e00c26680e030b040d8414403050b6a010303400b03207020380d11400d0f0114046800018113040606800c18010b180300d0440c810001520380554a030240041000038007001d5020741c2c000c5805030200ba01c0491080719400b00450341c00ba203803e0407000040072500c030781ca1520884a0502c2e04482d0040ca505501007602c0c18050841e8402ca14500040413800c0d211034401d600070140c4c910100c203800081e2800c034074040704680c84583c0381400409082c003c82c50b00700a15003651000306080e40e0a600c04e07a0900c2c1c5454a444441230310700050307404896030101d03004600c0c106481c0c441510000d0399141a01d8503400041c40075882c84145007410f054803000039481c5859041e01202c00c9500404400b0703a82c1d034035801845902d1007601c00c0c0d0f8602da41000240c124140e008044c603e0040e62042c011100c0d681c1d03509043d0503150844150f10362060610301400207002d00e0360003a0500c1102142c00b001192211142596450b1000c4000c03544c0d600b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 664137526 1250 664136276 664136287
    0x1202042018040c09081e0a17030f0105030105060f0d020a0e13030908060c2703120405120c010c021c0609080d0b0406031e0606030503040611070b0c0307150e06190b15 73
    0x981443c4403078801000301c003140e15603245640c07100c4400e020012192001d1070301100700982c12601c00cac402e5004290a42c0200094100301c07000c14824004c680801d80a41c441106520031511014001c8008140d200c030340110504100070070f118007014900c8150300103400c0d0000492102004141c07540030321803a0900525209850120300300306140d0420050340e2070400380c2032410b82d48040c448a080303100d268030000c0c2ea0703030b04010400200c00d46002803420b543d4081a51010707140d030441015000142c0442d1388981448600068220000c250b010007007211742000ca554080091203000341c0345000041505100011800d810300045030f1851102500e0346440a07403043c1401130710a130b645032090040300080749207500c9490311451350b800343e8003183c0003803484075881e10028024031028000d00b0840100610345071651100942c1e9024030000602458201003204c0010009544214034071840c48060720640e1900e621101800d120022031103210600742100e07406a440e000340003e8a028180c0c1c0c2c06400c01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 664138776 1250 664137526 664137553
    0x10c051204020f0d0b09070b1c2a030203040b150a0e091212101e061812030f080901090f06020a0504050a08070f0e011202042018040c0908 61
    0x20a0003500c243c0c1c112100c0040030700359480e00754042600b81d020344200009400c02d00c0c0701b00d01e401c0795944040000d080c02e01c1b001c10f00100c4840e840c3d00401013a800410417101900d45a914146203502604c410501c3c0d03203c5c0d03d002501134006e14465406400c2e01d0010313039a144000070000c1d0050209640c025405502408440315006407181c001503c02c0440c0c1800e0340750f18000605900c031710411445200b40c10708124100700d900c040030010b0034604a0000301c1c0311883e404900940700902410003401f820580c1d100d070f00076112203441c000b8105a20845500300c1c3c2424054980c141c1c0c2800b0400040b1070900040000d03505026a000701c0358005141c9507000301d01e44604d8003e421071400c0504119040200140c41d80e0340e540313a640500603220161403d01d18201d550280d900d000e500180c1c1007442c610041101e907400310030101c0b0446d01510040b8444229480300d0440c2e407140350020070b001d207000c550200c2c48100590740b43d02010050300d0070003a0700318585040d0b41d03001b0725101d409220342c8070400d04801d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 664140026 1250 664138776 664138807
    0x207052e0207080c0d05090a0303030513020907110f07050d061104030209040c090b101407050709020d0b18010f23040906022218110d02180909010c05 66
    0x3240d545880d80c40004120500010580c1e00c04038056035080e10215405001d508180640000e4417281d040c11441c0138086004904594231920000c3c090568680014446000300c00307072200842c0c0c6c020b000ba000c5180c1000d015120b007190f004240410b115030320074002441380000707401003a2074000704841c41d008155a10307078000c0e00c03403501c0360341d5014414400080183c841d882002d0140740300e9940000f40703a081c2040c0f0f10440712a404260701c02c211000000105a0700304440411040340340300c48954071070040c101545070105980c4214280d900c001141c45001c10b96a000384181c8400311070800d070391401d040351541d2087d000e00a190010000040401c90701500003140c0c1007401400200f2200b919000000500b2600c2c02181599050380004c0c15002c80110703a0003480800c940f41c00e85881c0103040403202a0502001410b904085603590403c680a000d4081560080070303941e2410366070346619503000071800060080035800785185101003661040180240d0700710238240d5903034070b05140900c14015007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 664141276 1250 664140026 664140073
    0x21c02212503060b070b07170103020a060e041407020c0a0824041401020c0c130c02070509070c0f21080f0c070c03060f060e07020f0c041a0a0e010315020705 69
    0x5269807490001154881a000313850058010792054211f8035141e140685441410782e01807426188040042c0010380d2070a0b0b1980660751640f4101380301c51480404a00103040390102c000408480d4020407040550005042d40d5801059813044032059580180300c1d950b010b00c50b00da290209010b0540b04da100b01040300c0c654485d00420b40c0b0740d410f11040364110b007281d020b6040039169401c40c1c003106440d0b08019120079810100484108001d02036207130000d4641c0601d0141c0b500c204604404901c02e503100314412803209412038410003e08503640b808074200700103000c40d903034038144200c0d95241460207a04401d10411490207095011b503a900c50441c150f510420044039200c000e14030103c0800e80318414044103101c01c100c00a1102d04024880140400c0106208111f41c004070703080c040d0f481c0124000070840000d440104c1e20040100000c0740207120f2220560300440c440c3d80c00502c00306a03525943c100c80c00303a24a400d10010a800c3c080030380c461060050143d500c1804000d9039440e0b031010504 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 664142526 1250 664141276 664141351
    0x506010f1205060a41011406030a09080c030d051906030c06140d0c020105060f040507050f16140d031505060f0309070e010f050306150a0513021c0221 66
    0x20b03c60b40032010104000c150318540030003801c0704428011000c1c44000c6005024000700190044d07d50030000001c0d10900c401018140e01c2c61704c40343d20b001040320320800d0703070107200700f28090720b460305001e0ac502e87c01044100c2d0318654103891000100e4200c400c610aa40c02d0b40e800801d640e400c5401d1580c19202c1380386050303131180309450402004251304c04600c0b9400c10b111050b0300101c1c04d403c1810400400e100c4c1d500b1400d02c10f038601030078400000e800100700d0703200254110101d502d0321204c0712800701d5014405006401c0c141c402c100140119070100d91012032640c940c5041003402001e004801000d80180a1180c00500400c4143c0e103141103030019542c4014804102c0d0740880e2a00412003401c0000e03841a080040c034013509003c140350030b000145c0c2c131540c44281062a2170404000a02100c102d00c00c0b1801a01e100112070815911b035011034010001c020b01080b01c81c0c05c03d020620003540b2100002640f501c2c417a441e407810110000342c0500840704004540503442c0f1440d500da286200000c5c088 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 664143776 1250 664142526 664142561
    0x218042a110d092405030121050a030906090b040506030109020c0f0f3003150117040b01140916030c031419141b09010e06070506010f1205060a 63
    0x50030030707040420416200908590301c00940601c0c0441820150500b2203403071100209400340d2804559020341503e0460700003014243d4244020780030001007902c01d1001030054020b0840c20000e1681018440c1c0c100ea2869482004da83da0b64491000c0e140180c4c007583d039012004000400804100d50064001001034506507003224901c400e0413440c0c001038400040441c0c000440111078014031890011004950821140e00c040d40e040102801c1d03c0b000301159002003112a5000b4107034420319501d2850031414400c49014245414581d0909900344100c40000140040d012454140740c074615000e0490640c4e00c6006480c030b0b5405402400d903028000c0101590340c1c0c84042c0d141c5e0b42c821454000e8015050943c00398013000c4001d403c1d2441c41406440140b5164144240040c1450070108045034000701941c039182d9980040b43c0e0400784100e0240e20520200c5d1880030b00401250b560f04031420341c0030451003a6038860031500c5480d03a2030310182494200c903001400c1e052040d0800d08098420410300c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 664145026 1250 664143776 664143797
    0x702010e060405130b0f0f030a020913080d29030307141c0c0b06030c060712031401090e1c0e040e0c060703050301080c011418040e100218042a 63
    0xc95041d041e40501d461555885088510281c10050306c24001c1c4201034444002c901080008666520319541009024410ac2e00c0010103140e00413074050042075102c100c00d0f5803600f58501c0c1300c001e810341001c4404000151a05111043c0d90b640c180d0b010b400d00540950300705608e5407107151b07080781c1c40c0d400300e00300d4003941803c00243c003d204880c0004030010345491885103940d041c4800718400060460b8025800840c84250540d144802e50b00d82d654015078010043c07603000c030220042c0c9400410400030800e41400803c66520540020240c0303600101150b08101d03a424214030940304040005020034020800e280c903d00341500507005488240d002ca980040455000c42e11a03840424250009031000c4014010071030b082c086030520220904e44404940c0c0c20024070800c1e0300c04c04009441c15201d00c0c065140c0703038032142c011520420322203041c0c404a40409548038040d40c0410007010340c2920303075071a09200c0d103040d100700440d85180304140030003c44401d400d04094400f4803000003d1285650343d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 664146276 1250 664145026 664145029
    0x2e0213060e0123040905060901030b011703090301060311010201050f1501052503210608060708040f0b10090e0106030519020d14010f0509241f090624050702010e060405 74
    0xf9201c500200d002d0095699031402200f4000c5610203400c992080c006000100701082c410503929064400c1d02c0210f08620628030045861441110f8141d0703019400e00d10000140000d0088106071a242a00280420b45e5010b54912b00204216032200c40b0240c025045150f65200358098000494500c2c03140b0f6060054488080b03200c1081d41c0d044000840480354150b06100403104d80001d0504a04103110329820300400300d48500c001414002001040000182400304e160085e0550300e4000c04000c1103800c00c0c3d15030614055443c01126a041d0500078581401a014400c081c201e0303801c88003400315800d03c43d03e40c190300c8151044c241c0c0d04c081018001004182c0001c030000d60403400f1000014118000c031003020641e00b00500c40700fa250000071140c02c40f901510041044d0407820190314544d95196080214000e04ca0382180710010300061000c01c00181c00d0344940c042d126070318601e149484803a01c005403052031003c070240000d241400040010b5003c4c6501692408000380143e06140c3c5460 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 664147526 1250 664146276 664146317
    0xc0a030f020d060f0f0305070b090d02040212040c1a03060d03090b0a0914011d0405040204110f1e0c030f03090a0f050c01080109021608030603010902032e0213060e01 73
    0x2c0000181a40d101010004542403101000040160000012129145849040e280c0c6080c0c410714000324400280c14075603948201006070301d5a0300a00c11501c5110300f00720802c00d140101c40450f48018001c0010501902e8991101c40c882e00b101c1d0f400c4d24558801040c03249000c0c0c000c1c1c0c00c5003840305041c00498030750701038000b601e1091550342e2600041d0380b91510401c1d090403801d40d894103200c10017281403400c486071a08281031060984002c00e6035100c51003c1001021060800760703d00d040030490010031650749009118400802c0f02c850702618900000440360f103c1d07280c6070030f2130354410403010202140e440090b5038071a1010090b2600400d0303d49404101c0c1034180000c0780c1d00d42150039002c0c607035038014418a0246c48088401c60500900340746820300d40c804a040504605404000a281c2d680c0940001c2151036002e0280ca10326103080ba1650622100c071803504034020b20850340000462140d03c26600b01c02ca54818000303206140c550103035030048040e240181042900c8078100141031104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 664148776 1250 664147526 664147537
    0x90c2a030d0912090f062c0a061809060b190c05071d13050c0d110a0e060a0e040f0b070e03011505031002091f09081615170c0a030f02 59
    0x31603c4040a800c207607001042d0058981010b911000081c1050006540c00754111400c5810040c060018145080c54095034035420032035294028250b80c3e01080440d80000b8524200202c40e00c42060356032210030520603202c080c090392030b2004050000e00302220380c4041c00584c040144c2055540c40e096030310303446d00f40042c5422805802c4142d4014030300e101c40711046150310400000640c2009806580c0329600d404034240c0c054828951074001000b8015084240fa41000d0014004da0009940d001c4181001c94100d070784622034148200f0004001804480d00c80c41958030014003481116142e448008040b0701030090002c00441c0030910500ba10240700f140030700288400520442460b26007014542030300341d01a40760080c014442d5010b20780b2403a048030564800c0080f00741c404920018100c83c1e10000b503118601038030a0780c130139201000c58110030000303460344003a42000312201c0840980e140500080140d59010780d050005140c1480407014102c581c4051802003894000002d2070310076604007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 664150026 1250 664148776 664148783
    0x102912060a0207020a060c0312050c040b0c010f0c02030304030c02040207060e0a0c080105011d011a13170d0318060b060d0614030d020616030b030a0c030809090c2a030d09 75
    0x30790f04254035100460000401d120310b820550b2240a5034001d18214243c184040f60301d407034a01042040407414155000360203208078030754a0303007084a2100c0c0641070041070720280a01d0103401600142c4007100702d0344200e0b0592164000300702c550303003032000070350010b00259000e41c0c3e00c5400d250101b0050041e4540310340201c0c00448141c0c1403140c03a600710794060340080c0400c000c00d40d2501c100b40b00c03455420704551445560494050003200300d900c061084030304541c0d51394070582010500030030840c80d81201d00141000c41d01005072001c400d03021504000e072000304603034000c582c1100144064020200c06400a00820b04060940400100f0341d90a504124416242d0842079511030038100426140b01c803c520084c13685081401e8607100e070900c010700344010140c59982d11110340d1401c00400c001c1560080850144030303540d040000c0190007040000c2e1040d00000c0114882d1f00020080e115515402c04402e0717041950f040080c400202c9981e407021f0716000a02c08105a02c0c00e621442820900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 664151276 1250 664150026 664150031
    0x605060f0705010b0102010b010e061602030a0f03030b060412080706060e1e0f041e080c030703030506090a09110f152110080d050306120d0201060602102912060a 71
    0x29403602c1d5094030f682c000454110383c50b0010342c1400340ea00c04680c08540809a604c0782d510844c0c015030300074519000c407019400d032003407004560400010304424903916000c0d941c100000103080d02004268401c501c503d00c884001000e4100210380c0f21402403103a180b10f618002541030781c1d000c101810344004c071078001c16420901d24401e221034a4030811030740441030603080c070a503180c11b0307440ca4991400000400028100441a10100414101100c0c0100301100032a51548024607008000c1d0800702c1d54540103984c00e4002c01c00306009401882d003c503a102e00c0300d0110f40e41a405202003060350300b9580303501c030078071200740c03464800d51a00070407526022400070640c1d12480d48003180706280c082c103800d00341c1082c5c6504015254010070081c030307110a50300e440d03a500d440700400038194901c0c0c011044268050400c0c50900280c0560080c01219110340030f071500b5040e0703000c051040303c2c00d040c2c14450812420008208070340e540410b80318002c00003000c480381500c503854080c0ca0b1460072030b4890300007075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 664152526 1250 664151276 664151287
    0xa09060501120908040b0306010c05060a2702090703020d020d06080601150503130b070302090414090706050a1d011803060504060f02070201020c19050d03091d091f0605060f 76
    0x160322400421100490050501c81680c0700c2c1d44c3d01900e44290300c196100c460000c0007166044c1e2082c030405401c0c41e001000c5802608000c0060001005103202c0c5500c1c4950f5091025904a001c80080d405d46800805411080e5034444058001e503010074903c0f00002d40c20040f01200600603c1407002400d8000e00038070156040011042844051700340c4882400402e200b040040c0301d80c2d600304113400742e006103580e40e0380d102c0c40300541c0a80500d900040e030007803c10b00800c000d50708000200c1e10402800c01181e213102e589460641e028440c1a640e0320001d07424070044814859101c502c00c0310010103241c440e5280b00c2142e050038103400c03070ba0021103503035850781c060105205003809000c0f20312031000c43c1140f83c500c0d1755001035a22503042001c1c50003400c0314840d00c1507280295408a0080c04003410761070000446240080c01460a40100c07501040d081e104131042c508110000c1d407166903a000103001051104031010b0200140e01045039031661504000314481d00e4000c09010403402000300b46484a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 664153776 1250 664152526 664152529
    0x20f030f1e060408041a0f07080a02010b19170c0901031a060612041118090c0925050705100f020a02010b0111030904361a0402060403200a090605 64
    0x40030901052601c5901c29814440410314481c1182c0c21140905075012098244061034040e41c000e4403800710240c1d00c007060100070b100750070f4000d000000d00ea5008110f640c0c5007000f00040e414441d01030003c04d030300e8044140040315044811100c42d91301801110002052407002840b800426041118290004400d108039204104003464100c001255100d04184c0ea085a08241105c0200007405a4019013240c1005442c1c84c046000780506003038080301d4a281c50400c403a030300c1d0101c90b01640030703500a00015405006e1203141161118542103140c004405001d4103c030960400700c0242ea40340035042440020030002e00c20260328131a0100c0250319101e11601c082d0071034125013482810311800420282242e03401200311101407000301c40016000c1000007001107180e18a00c030701d901c1c03c5100b012000080104203500800c561090551090f2008041d4000c405a43c003500c2c001c4d000b2400384000e00c0003c1e040028101407900e00701d040407070407400b00f0000301604116400005e4080d91240c0c02e0046 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 664155026 1250 664153776 664153813
    0xf04020318160302030607031d0a080c0d0302090d022103040f15030504030e1002070803030c04030c08070609030f020f031c1101021303060b01030b0613051f0c0b04020f030f 76
    0x5210700c1c0d5000402c645581c0119403100030060102c8101640e9280c81d07c400711a0010030410318001d1001c503542485030307240c204026030007038645890714071605540e944564428000c8600c0c2400191922514405603403d01681901c2035190388011141c280c20507031404401c20140c001072800c0c046203403d00d0308d0030b2104200710645004c17043c00c2504240c01c01c00403076006590924a081d0070f403411085015070010813070821400e03070004103c1e4000003091100000a800c080e10642c0d00548006c28903580d07034140c00380d42c0c1c0b6180c410070703011034100c1c0000c001050100c100c4c0c1c050f05002401100742901840d000906007030300c10f0410040b400d41003564004659001c0d00801c0b4840c0b40d075000f1454113004032071402808919110051069072200301d100002d92203508103498107035018002c00d4851166003446108803041e030107154051220758241000030301405000a082c0085900d41400314002900d440000d1000180700740d0b000350610050000d5500c00b00040404401e1b51000380c0899550040b00501 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 664156276 1250 664155026 664155043
    0x82101090f050601050915090d030801050a080d0816090f061d030705150c031b0f010f05040b060f0406050a090c1b0302030919090f1d06010e010b090f04020318 70
    0x42030703860702c0d04000ca0742e41c000e02240c140e0201140c840790580b240a200c040140305080080c5d81040d007240c1c0c10010140c2068065040c1c500c1210040c0c0056192181c00d542e0f2010610700c00f002420380e80c049003c0103d2061009284491441c100c65010b84030b121201400505a000500044070340b040c0720061481c021200c4510403003117000c2c0003007525101c0000c001c0c00760407403007048440d000103a880080d0b0081080b52480d03581004a10b00d5900385c040c005440b80780000000105500b070480310200e80541e031187d5031049510680303c40130350300c41006020034005c07405506a00559a8a404207082d43e98401c00c00007040001404034020740a100001c2004102201440c0b00160351400c18000030780110035900310000c05d584511462402d5054031000c0091503000c4144545059070807500d0603c40c1c0c001020103410482800144c4548501040c1e075900c0911030071841c07047c02801801444001802468400d40c000d0519810381d0140000a040744c0c416212200c048100710404001840280f00c800f1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 664157526 1250 664156276 664156301
    0x180804030302160513021813140a05040309120f0204050c0901090b0702061b070f06120c0203091f02030d321306020a030603050a030804260904050408210109 69
    0xd031443e00000c940441740f00c1d098003207116004941c10124901c1015000e40d0f100c00140300c0202d18818140c07034001005849400d030400b0316104000b490340051800b40c280a15030542d9401ea005152078180300202c202d511040352a4002049884050395071805014020b1400340c1c2c0b52036446c000301002500f10101a8007119800d5018810100540d03616425142051000c070440c5e50591400c0710360302c0c24034506800180c00b01413806400314845900c000038041041d642d550070461f6004006060381c0e00e00401d030038a6800311301a0f0706181c0034650707c1f490841c0d0241c5801144d0400982917448400e40b0901707500203078604000040c403803801c454800d0020512401d86140c11460401c80c0e0101c00c01002d11001501d11500010007201c80d40c46680060021500301041d141d04c00c017a0f140080105100303072000c0c2e8000c10ba4075034600f0f0b002c10312950f40740c40c070140d20351407447c04a12a091001809001304143ca030701c4c00034040d0b01002d03030042e501e06040540b440c0c1c491099605208040c8100e500640004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 664158776 1250 664157526 664157563
    0x30e0a060212040b0a030902100f1701050319082704060b04081e030f1908061f0c080910021f111c111c2715180804030302 54
    0x2d04082c0b80b003080310305880081e101c09036a0303030340b042096014084510009420010310342c0c48411603a4421100511074546540d1a604900f030344061100b844428062359a00d078100c1c1d140762176210115035000a00e2441038508508040401d4454540100d03001d4540100c83c04070b2441d903440d841c00d44031305070140040c2c4207050704141c00c052510340c0d110401005103003003074903401c0c460811240410913165510242c0e01c19a548000d5900c1100d075130754410b2408004038900390007194007850b110b541160443c1d01804501c0f540e10444800b102e00641000c41618850b8080110030000d40300c011008141400b80d0b00104159010103c0e6041002480b0300b800d204c039840e0014544101c83c4080880302030002c001040c1003128603d494a90051480308540c841c212000108111260444241181e8244620038208041110b03001d540c1505150b040d604561400c950301c422000030803540c03903045107010194002410300c8501100580c2c4400402c802e417a0800086010402c2550410500000f80d1044000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 664160026 1250 664158776 664158793
    0xd1409070803030c0f090306131407030302210d0615020f03040605030a020a030f06031b060c08070803040c0f0e10150903030e0d020414010504060b07030e010c150504030e0a0602 78
    0x110b40340c0c0409042c00f0a0083d00107803a070980346048040d20110a03004040ea135007030034180c0212503000a400c100b100d138080d60707010301c0000900c049504011690190040c203003461400052584241245d440742080710428000240e1180c128441d00020f003a090b9910002c1540480b8083e1800c4590540014140c0c030410040c0640d81c1e00c0f0f000e80e074100400340001750300e0f404500300540148c030301c581c41c4040842c0340000000c1401500101243c41d015618400b5031440d840e60710803509015003e5010b00780c540304004000008404d00001c5910a00609500d6001512040c00c1c100d0020907512841501034040c0501010344008007030074000700b1200301c500854640120707018141207203601c03001c0c1c240030201c0e0b0080001e45806d90805482540100100f10001070002c1e40e007069042230041c1e500175413420501080d0708441800300c44c0e0454158071000103c40c440001103542001c40441280c00d0a4075500c0032020302454000c55000354803940b40c04e80c1302d04d8400c00307220803190030b580030408540c0040c51 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 664161276 1250 664160026 664160039
    0xe0627090906041a0a0f05072d080f1b031e0601030903231909231c080912060402101e08150a1502070e0615070f06020d140907 56
    0x150f841c203030140c1a240c1007941c0d840c2c80040041c000c00040341c06107800c100408c814158030940012202405240a0031182001500745018000244422001ca00c51a000c2070082d20540800c0340c1c400c03204d050b202d00c400c0b840032810009030820350700722001324030b1a101c07034516080c40400c05500ca4820b203010801e18100d510000e200c0c880354004010210b00c581c0d01e00d4600401c2070120b0721030740700c69a402403000703040c264020b01d86800792090b0311501000b10385140301c0346200d0440e0801120b004004030429480000500c0b041603900c00121111030381044840d50a1304d03118214104543c056000d450146002d0041c01300748810000780c44100110b1039030004c2400b0801c010045410381600d81916070356220041f00c10505050150030394004021040042d100318403007031900b010003c40d400c0e201ea860b51a2400420200240d41142c0e000340f40701200503c9001141c05040714500600c0d4440c4000c055850700c504aa1003890f003101100c0e01d408406a0030074410b8040c07a0400703044801070848a14025 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 664162526 1250 664161276 664161293
    0x406080f06010c0f0302010912050c1b030a420b03070605030a0e010b0913031403090a060504020d0c080123040b0a0c0c24110c060105010e062709090604 67
    0x3d0010306800304031065406140c400d40c002040590700046121004e034002c00090806c0d00503003004a25407240320341c10240b140903c1d5003880f8081004c0d0081c0603103240c50fa11400c40b1605400210320ba40d00907000c2c80a50000304d5220308200d641107804441040b8903500d007100703907914262064020790003c00101702d6560b2200c116540005906070015500c1e41c0145070030701518041100e10b81c04040d000501c0010714a00c00400c0450f846030302c5000010400d4070b04014a404111202c04250b04007900d40380125401d50041d941c0184003c058074010141e907a40c5801600d80c1d0340105599a5450042038110009280000c03a00f40380310411411600e095510501c909400812245c2100e48851000c019103010308002440b07180d228035070040c2d059400404030040f262144031004850300b0100d002c10070a648034102c424905240c3c0103803e203a0300781801512000350903d01e043d0001c03000c0080c60010404034440c07084ca40b0240000554281902c010089801c0e4050200c3e4040c1d004031082c80006074441 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 664163776 1250 664162526 664162547
    0x15190e03210a020f040305060f100b07032006090706020115050603060d06060b030c070507061407030e030708030f0c0d031814150f100b0a020304120f080a050406080f0601 75
    0x216070080381c035607560305840040c2c040d90f18800c07460a400300740401040000b00e1307420710a440b0030a0151a665503419214440c1c661803041c6001e40100700320200111f403240d0300300c40d11000941c20091000d4201120103242c20011168a08a900b014000b409026828001d1091900e605c107030300036450341042e0000e4070522024200300c0c4a500035880010400005070444d900524501a00795120311300202580303080e501004084495000d10000400c01030302601111030245100c0d181903003400f9a03594156240c0d03a450a02a501d0b202e05040050401010002040c403030462072502611070720001141e6240c01081072f0750b44145414040c00480c25a10f40502d0501135412104e680904c480e17668400b41040074242815820344914810025400c0d10880d9581c0180c05d99402e41c00e102d50385941c08012070181802c4540140c104000c100aa030380700700d081454250040401014403101541c0700e0146030300c201d000b41e02043c000304040158503080f0f818075030301241640040c0441c0c604440020003c0f59030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 664165026 1250 664163776 664163827
    0x30b18070f0f0e041d060c0705070602061306050406090b01150e030304060507080d060f120b06090903041205150a0c1e020309062505100b0a1d04030215190e03 70
    0x5840b10210445e804040c030300c4221107090262201803c0aa4103640c0b0703940025001e581e40d1040c1c0344000740e9244000354552043c4c000180c4219230842c55a100d0000e4000500291845c0b1780310150700c004200f01014070f9000303282200d402c0300e0b203004441028042d400c040c45072a00c01d8009120402c24190801e044506496100c03811030741eaa410f403808040140800d400447d8404040200800c4894690b182c01d500c00340141002c0d2403a590f041b040140c2c01c042207a0342030302a0000c3c442008090442d00d88050303903a10400030360340e0402003407081020300a4115820307049291612007180009411030780b140c20b941c02c0c10142c0340c80c90300e04240180d6079102c1d894019020300300015207104070404071400321b0840507000b000403900b0041414201d51b190007040074940704a150004140140c80c141d000c10081b5080010400804001c01e01041c4d5048401802501980035418003076200800190320340380301d450b1098a800b5040c01e00701c01c21088441c8d10f0028585035000b005001031f5641c00500701c4241400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 664166276 1250 664165026 664165031
    0x30706050918160324031113020304020a0b09010306080f0c090702060405070b090607150c260c0c0c091008061308090d03050904090501051509010b0307030b01030b18070f0f0e04 78
    0x10813412801e07051074450030801170140d00002000300010f00b1030084106101725400c0030045c1095007884200e01c01038400940c8800508010000c98600383e02500c441c0e03505040008000307595020140c18102138201c001c4940d0030182c1c4003400c03031a0401c800c0341c0002241c40102010710b0550381f0650b0302c003450300801e41d980c800815035049035a41d46044a0329030381d00151001e01e4000d15255500030701441c0941d074022036200607105020a140408450a042084000c96950346815184200ca42d00075140701c1110300544401091079192000c1c02c500429164075143c40b03507460305a00605001010341014070070106062500013003400203058a8002c2d10413506200348042d9840d00740d9040c461140307059000f81c140422001402011760055200700a00c0c1460708203042c4001c00c0000705282400741c605205004c0c804034500c01c0c46a405045030700c0041c103000600c609003a0026011500030401c003210880c040007000318090b030204000d00e40554508021008910640c4040d14035400741d10034038015503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 664167526 1250 664166276 664166291
    0x14150d14010b0a03051005060603160302181504080d0f0c020f0307080609030c060c090901061416120210290406090c030203161707110109020307060509181603 70
    0x9080d0300c003059142d401000351000c00e80d21302d402516944032881d2508a0ba01d441c0c0094807a00307001e41180d100704242c07200300004105c0d2000a500940040c03c00c0250364181c400809c6454032810141c040c3e0315a0580850b0b100c40c5014907181c039015240d054076080212045000c0507480d001440d0000140c1c0c102c4042006c1140e01021903e403403030641c0308113914072540c030032f01135546004801408103000340004d42d4130036951035030180790324030404540300d80140c4850010000c1030706c03490024a410300241005482c06011003114084551403600540710b03200e02c50308074078907070303804001c014001e400001d0180445407a4084141400c1c1d075007240496101034481199246584a501590240484500400c49001c0411000340290000c44050252880000341c040140d801100e40304102007400c000840c2b00e94403903074201d403504007450550280e03649074014180180d80500c82e40000d80942d0365020b444040c20420020b044088440240c1803030300c40007d0000d0070940020340c000024047c01c000c18201c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 664168776 1250 664167526 664167563
    0x5061911010c080a0c02030309061b1b01020d0f0b0d0222050108010c111507030c0e06070b1009020a0203040e040206070210050403020306250f050d0603030314150d 72
    0x3030012104800d129440d003100d107034001da00840740318028100000c04000c01d44090800340e0707481c4030603140d40402d584440006141e80c0c1d01183e20744000505c1c007000d18140040741c40c00c16443c0007071808580440c2d40101d481c92102d032261240810400c0540c1083c4207a8440b003003c180420301d0110b0180c0100ca481c444604603480000031040d8031202400208aa0340c0d4400305640202030303440c103c000203040311001c1c104540d400210303060600030500e00b01e607a6480740b15040d4010021300300201e05014110f22012b0603070355098050b01b04a40605448c00452400360700d01681680b2942042400300c0c41072240b24007050b400010f4500b56000d00045107001d0310359000003905030040c801d00940c840018440358500395401030150044a1083d400c50700ba6840f00e44409403428001c403003c811070013801c0840303101e0521941c400580f00d01107080c814a400182c000040644003190010307404640c4030000b11040304907807807605601040c040f01e4440c10b8800880068060324000e2000b4100011418501c80107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 664170026 1250 664168776 664168787
    0x7050a0e1504090608010f020a080708040c03060608011b0311120a060314030c10020a1d0a0e010b0c0c030705091306022502030c12031b10090606050a06020106050619 73
    0x3011101ea800c60b84807640c0c0c468920240046008242640d42840c024540840143c001d0b81d9110149484040c400da4880e401210420b2004105591540d075500c0300001244042c4200c101515582c2c0001c90091a413103500c1340ca1f8400b9030614002c1624040345669104c1c543d006440d006952515800300c0d907241c1d4074851015040e1a00302504880348100c500e031050701d0000061840da044001900c100c001d6010112040f0700960b0604030102d40360a8504251006100c9802e2520704000e01507840c3d81c4e12404000070307204e02608210b0301060001040c400c4094108428003107680c00300e00a00c01c0c00d0a000c0032681505000d016142804189804002080b06a030192404030369002c0c038224605070f240002d080354401c0201e0070b030b0090258150301c081c5810300e100581502e0182c00025450000080e1007030380e15241420a0301c41d9801041d014110300012409182c680034020b48000c198981040100404d04840d68440025a89402002c000d03a2300c842040c4c940c0e841d9880000031066182a038161031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 664171276 1250 664170026 664170049
    0x1b0f0903030c0f030c150105031b01120e01060812030c0405040213080a0302060a0e06040f1e02031209040e030307320703081008030f1b0f0a03030c1707050a0e 70
    0x3400c2c0100c0030f241c041030b0000406001d109080d02c0c1255914295011050a498400c1c000ea6416030851544580c0410389002036240f880c40c18036101d19140c01111403031084841d6416a440142d442d0f07107080081403402c0102d082e40d088241a8680385081118400e0314030721403881400e000d01c3e000705080b003400059100001c000c01482081d959810303030510b4003d4075100100d841c0c010481c40c050341c450081100042c01d501c219442503c0111440c019150004140100c00d03044429142c40d004031030050701c2c1889030700d48150a007040c09403200344000400c03060790800003500e02140d1080c4200850b86a2103030340398418a250004111401081d104d400e01000254a5140d070120b600180d110101540086020311034003108400c040c2c0a0703100c2e007034207031284150003041c0101c003000e000c8040c0032106040c0071181d0449000454066492050b80305040c180015800d40101f079407030000c1240140c01a640b8000d8104400c8403403550300d00403501810034003880c4442010003000294102d11916031040c92207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 664172526 1250 664171276 664171297
    0x90718020909070e09040201140d110409230411010203040e0f04051002130e060604080f10050105010806060a05031806130201030b060304021f0306090906141b0f090303 74
    0x45125049605510281d808062100c1c0154000d8001a8803030340304a8544600300c01c001e000e18002d0f1542c1e0011600383c0c4912412090000c0c04100048180850b8402d6201910148101c2a1514508a1a002241c055945c502d05908070300e0358915240101c9900365510603030010b01c5146c0c80c00c0c240e004070302e1400785d80c00010a41d0743c1c040c1030115075082d400c42544200e1080017110384500c0340c10014010390044454115855009101c20700c090454a100c0c40c0c2c0c0042c000c2c01441c2015600c03124180340c9860b03060a001c0a8106d80070007d011007036030150700c2c09000203080070780d030508110010944d05d1042c6401c1800300140800400c00ca8000c8130318050642d2005002c42d54076043c13803c0b1340070032001c1061003240401d2074480441c00314184881503038411500200284441c1003280705c07014014020500300e0007016034904000c5203401d00e030702c204d01e0390500802c400120802181803107945070701c4c0503006455150f0300030200c0c07601da1001b03c02c0301c04244064a00644a030502c0300800e01d1402034480740c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 664173776 1250 664172526 664172549
    0x150501230d060e07170a0c050903031201030b0c0a020601050103020a0e030105040506060a0618120c0312051b0606090606090f21070e04080d090f0614072a0204050907 73
    0x140102940c40c0c004006541c80c07183d0190325611050010382d403580c0041d021140d06400e100005880010a6000d1010482d02d0b08081b441c0507480f9000038103603800911358a54800c8128010b20038070451401041d400034070242e00342d160100d11070000e99160350500c500c0e030405800081040003039200398003038101c035072014001f0311060800346441600c54804441050042c0303048103002611a1003481d40f000060380030051052858248042812130300c80001c0166082040c01e04004001224245000407079011641c0309602e03088001c9020400d4248a0105003441e402041132000c01c1d034410b8081c1e078100500b1249141c1c0c503a500b02c045000140394111599109028030482c1d860328450342c13840304401d407501040d0f840c916102d090301c0d04802c40985001d084e03000c09000020004040360700284000340035090a4400c18155074690050703d050400800c08140720900f80550107401c59240c14442c0c8801c40d44071160310624030008030103503100c034003e4841c3c2e8503030001c00d0280c441880250080c0c030602030341 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 664175026 1250 664173776 664173787
    0xc161a06010210020a0905210303010605041e0509060d0203010f020406030b1207031713090903030b040e01060b0f070f0b04050607110a032106180606021015050123 72
    0x1104004a085030410701500030030410000300c48252080700c07004116a201c1e0f482140c1040d044c0240c4d015000300784801c1c000c0c411100b550303c207010400345000f01043c0d80c40f603503254144654540400c00000946440000f03c80c1c05001c40d5032000d101c6603018400f9616510140c0103800084d014019081400c140280f000601080b0310b98550040c0e000f4000a4038444038244040e04280d65a07000c510000d0000f110075040b0401480c01203008000d080f44c1008042513240e03e40c4083c00072100101d0049001c0303a41c40354405060f04240c001c15075441c44000003040030b04e00d00649036100d80300d900c0d8411805500003586904000a0b07101c030f003171902d8100e05010308030b2901d803800655030041610658042a01010502e200f00c1d03002543c04c41c120382c95034498100704035011460044481005c01455010349801000c9841d5542214010546040f03000224640c0d1030140040e0070030001100d040e03400750a1501100004d9001490803044490130302e4010300d020140d0340101c504409a1100c4030060f1400640e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 664176276 1250 664175026 664175063
    0x3060e0c091e010c0f08220603050702060106020606060a050f03100e0a020333030d020d0e01020106080307030804030c0c0b0a030507110d030b01050c0f0106060e0111060c16 76
    0x5000301c0102a10701580312010082d088031890105100760f0b000a12040c0f401c80004e4141c014955100e1040400901742150800c0c2e0415484100c0d50044440d11000010400140e040c003d040c1c01011a00103000315504041000f5240d400051616004990024032400094815011a9410b001280140d80c803414050320021300700e0450310402162a600d080446e001c0c800c94401c1783c0c000c42c1e07449824140442401481c50621158822a4170460400c12002c00e50ba101030100b540044102d50107080140b2481d0307406401180340304001411a03140441c103008181001003100c20080d09810402c0315541c0781c0c5400c84140c2105200200b603182c400074000f030710b201b00b1b9014040800d0161014455070b9203500c401c0f2403011841c040b5214035408506602c2c145400382d0b000d440c90000602d80030307207085612240d2a1514900c0d11010305141e6507007204110465001d800c029183c202440c2c200c03050325004503c0c030780c0e803080944510b5034968005100034071021a0308424404650089942620040d15039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 664177526 1250 664176276 664176301
    0x50d050c0a1b0510050406050d0b0d1505061207050109230d0807020319030e133e070c061b1703060a09050603120304080c03040e101208040b070303060e 67
    0x2103154013800015140c802024060f100760b4040d0f50950351030500704000f244005010f4404840c1c000e8114108005a5012541003e208a00011040c4020409040030401c0c00f00c881c01001410103290450764017409140c0e070089507101162000e05050b24000180c904840040015281c0700b41d2101e030403440d013020406483c0140420034001c4003900c1001c07201d450060400401002c0040c0042c08401d50310300caa08d42100c507a0403012100400042e42c10714011786100d2028100e00844080840b5880a58200720480717001007155a40300700d1600f007000c203540b01820f483c4e0034000c0e042400540f18034220705030003400f410a583d40e004501c405c0d40030521740c4211051390051302c900740500034080e404540c6030054007599020341b1016000b003107240414401d0480c240c20140048600401c20040d4610095082025001a004048056806042403541c2d0010300c81c00781d0209600408018007600410b641000380c60031101021519640c2d0581c61030202c005040d01c0e00646400050703d000d021a509601 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 664178776 1250 664177526 664177529
    0x3011b0801031403090d0f030201090203010f021309091208090f10090308181b01170c0c0f0105160f020c0d0b090c011805040222060503041707050d050c0a1b 69
    0x11604003008104a03c00366031a480f80a08a03034010001001c00d0b40081d4401e036003a1b0009001c1e01c000145643d0b5a8006802c0d5001c00303a2568030180c0110b03500d00042c0f08003400d80000c10000c0d204000590a0355039505034010740b0040720f0240004e000024402c040144448070344404242c050312400c2c03000344460b41c01001400c10960019440e9070000e5503090303031034034108585178440004100c600c0310505003640c1d428420403041d04000c2c0001c0711b5100f00c041045050b000c0c3d00b08101290700c070810382074560720b41400e198241c04980e0510f0305200208100700700c2d80b80c00d17400c9031070f040800d080c08a030184c2c81c00c4e1485541c2600074116280c19814482c20400035801105110180c030340d0101d9401c01110072095940c040b86450001142c00c10082c0b405600400540911031141000020001042c500240e2140e2048011440000c200010081c42180c6c01e5110354000344018200344003601d420ba038500c605002c0c4402e0020004880c4460311041040f00202640038880c1c6140b06080d848900e01b0014a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 664180026 1250 664178776 664178783
    0x4090c0203130914010e0c0c010515121f0c0903080d050f06010509030721021809120f07030309080c010f150515030c030a09080d1e0c120b03011b080103 67
    0x190b44001c200080d042c042c03400150700b03c0f0070101007079003490584140e6803009403409100715002c00c00c2081c102401e018541c42111444408d451500c0c5d403601340155480e580941c4030f000d820a0841400c0c0088019815000482e1200c000504840a003802d50341a4890f80020b0240342c40440e000c0c5440e40d0b2904568031520200318200350b661140d100550755401443c14103030781a00010800c0c012a80b038094561075817805900c0074885000680c011890054505c0c6c08041c01ca42400c3c01c22202000811081144080d00007074546841c890185040c41d41c002d000d002010107440715180d0041c08805401e0300c41e0900c00304001c00104903408030310360003003103403c91003c21000005800a400e02e08910a5041c00e81180700031b520f546c3d24211100b8856100920280c19581e40f00007540100b038500340501400f02c0310210000304503025006106065585410110110b03007818864251f080e03100c4110391307160340110f80c08140b6554000c0009e0142c11042c03900caa040080d405011b1070700e50b02c426104c1c100ea00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 664181276 1250 664180026 664180057
    0x30a1e05040f1203023c16030807090315020c1e0a020909010e06010312110d05120619050d0c051f08070309050c0f011806030f1401080a02040207020604090c0203 71
    0x424503c20340680c05101119191420000400221040a401a0042c9107141c50001e07107800fa03d60440c10564008003001c1074518460004102016000813660760040f1076424030030710403840e5a66202c0d00c2640c50511104154000c1103400e083c98040100800012540ca6440c11527144840410f136074410760340c0113034414414500400d440200600c40c014401c40c0f074801410b910b13801c2d03460340000d81d035005090741c0811034811001d00304004c0501070000004015682c81e0703900c0500080240302d060018080510801c2c00b48a0f140407003940440d1202142c1c0e0a440c00035a41e00759003003280042100d5400550405074505811980100e2004098200003140c5c0780c4650783d46410004400b2035101c1080284140d0107504003907182c0c80c14240c54215410140b501c7d4203d40c400500003980803505501c1000803e807030f070342448121a690300408120304100b0b200383ca03031903140000301903503580d402c070002e405194000b07401000d544440e8201d0300500809041880310600d0824004e549a2100c0504100c028 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 664182526 1250 664181276 664181303
    0x102d0b100224010e0a05040f050a0b04120203120f060d021e090c040807050d06181101020607211a060301120c150c120203040f0305100c030e03030a1e05040f 69
    0x41020b000075042e079420402e0040a41c0d01c00801c07900400c03003d4010360790b030041c000010b400150100712843c1054805c4c3c43c10b81075410203180106000e02940101010354009112480340250102106903100542c002e103080c4688804002c80c0683c00f2102020350070404540b003c580740381441500b07202144054508002a980711002003216014a0140b80c41039003180340c04109501e0001141441140540c000041c07240f00d035251888441141c41c01210210280e10901d129036805110b4250b110059042c0100100340011481a10b0020035910714034032503440d01d0307030608508019000544c916014040c0c41d07a0b543c5401a8a80d080c2e881101200c440b090020b01041c0e85c1e104240541d0781895603129201c0403206503482c41c02d500c051018000841c070090000082e000c814100d0800118003078009010944441641c3d0803d13129544a910300f032606201401c7d000c21000811170f0b50007503040a000403010300d40d80c42101051503a0880201c128189818442801811800c03404114440e003041810706 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 664183776 1250 664182526 664182583
    0xa0b090c03100c0318060b040b04021c150506031009050105030304031a060f0a09090318080604030c0507080d0908150106020304180617030903102d0b1002 68
    0x6050891a141d0542c01c54204010002050741100e2242c0b10141004900028080101801c0b40f0319580b040e0b03682a214594200c8a0600707104116003a04155010343c5010314400d806150340d52000e40d60602540d0760b04c1860404408800001c5c0640b90081c16541d81c0e0030700e0780203418041082d0007030340c4400b4603040001400746400801c6408807030b44208174800059000246005050700280802c4c0c00040107030380f00529540b9101c6100207060038a600081103001420020070340c0072074507440390200314210303000c0c000036800003a8598090391516100d0364241c040d2510f02d0411415900a84181c41080061513201d90052258000c1d25240340807101c1d203000c6454102036000c0203106d8400540c00800c803d00c404200c0c0007030915151203480b03010880310740e10040b0680c0101010070846a0fa000800c0c030040500d420b00c518106000e52180c00c0c0610a0411181821612503030040c03010a03824805060b100325164003c2d145022001b06007284074580090040e45910303403030300501c0c0509010001ca4480 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 664185026 1250 664183776 664183783
    0x2060405190b0f151210140606032d04110f1806060a02070e100e2a03071e020601030204150b07080c0106150e0a0603020a0503061e10020a0b09 63
    0xc00360442c11820b603d40700c816401c80c00c41c5010304800031a441503103002c0d480344c0314440c946249070038620003041d66000d014480ca040343e0307030070807440d15480c054000e10005aa03603d00703580d08901e17140c00b041c00c080145aa801070380700b600541ca80305604a03e04000c00e10604070081c000340d0700192040310310310f20395800b000007048281007009140c00400011a0b2a41052000ba000460803030044850403601c4a030440c49901d402c031619811003c04d0981030110500420ba00e5030030241188058a420100c040420001c0c0c034484140710001c00c0200010703010501ca542d406451005d501041c620a0043c2e050080d20b40f20240800d038029410400711140c1080e1401403101146e40024203a03040c0307421583d54074050390029445c0c0b401503480c2c2901180c4004d25035007011b07144c001a00c8509400c0c80301c4c0240070180c985980100241343c8188510103c10350082d0440380d100c0d00031128001c0341822503141d109103801a00040c1d4120030301c00c11107280e1980000c4d951200c82c0c0200d521001c3e50f03680c4640c0c15a03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 664186276 1250 664185026 664185073
    0x80d0501060804120e0f060705330a0c090f03030e0414150d082116050301050114030a063c03170703030e060c07110315011403071502060405 62
    0x9205161340c850081684910032061801400400d51480d104011001030900d80110b502943c40d82c11043c0b07080d000c16046d002c00e40b500703014000201071160541d2400c08041000400302411540c403514494807891080d44400d01034901500541642912400d0050070107c64502d818080c0c0e00d4030390001480c1e40444a0340b4070610300072070401a600ca03100e0a1000d5266031407002c43d041a802e021607841c215000708000c0100d5000c0702100d80c145803190740c00404000504400d4203000c0100b0041c00765982c400d40c2084090801380e0621343e661524140040101820f50101c09010030200d25804081080740c5020300004a20b04280c00c0e0003081c50440d940035415200051100710710110008400448002601303a080c002d00700090a1250244401d00340b0804442145011000007651010003045074192003e858045d0f00420480008814000b501c60041c041c1e1164650102c802d0501a40c0400925004c1c200101000340c003d000c0300ea003e560703900160345c1110280222800851b104140305c10b000c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 664187526 1250 664186276 664186283
    0x40902070b0a241401031517390d0f06050a0e070b091011060f01050109090c020a060e01061223030703120b0d02100810060e0d120912080d0501060804 66
    0x10041ca02e0000c64503c003204142c0b1440c1450b0310f510850131910000b0007200000c10421808c001620008050036090180b04112000503140c030310385101c8090080c84100203030ba0440041d200c22406040000780c0c0310010510000c0c207500130280500700704542500300d140103121900d8288542d5007050384060316107400f030081c4100d6203024852124945462021803d041c1c0b4107060a0745501240f12820342064070440d4848024640c4030010885968424600e000500b9140300810014003107940094079045404409410303951140d0540c086814207501c175278010404c0000c1441d900d0030515021060744986501805080010303e0b089445020100032100c0c0c071030341a0b50328211500441c410200414041d00c82c40d03000840500c1d80d40c010b80351203024a1008403281c0703c014192a0114200c2900000398000c84100b00c102c0c1e410780041e48502c00e510f0b90580e44180c1010804991910460b507202a41e48200c412500c410300386001d11a8540007420f018480a00500580ea00c41005840d220341c103a4005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 664188776 1250 664187526 664187591
    0x2205090907030308040f03050910020c011205070c0b042909010c03060503070b28030b030c12030f0f0d110a02161d15062101120503040303080c040902070b0a 69
    0x100020001441d11061b02d2103414002c0c1081d140c0c0c004940500103c078605e1740503a000c02084802585c00c6440c030501500c2003c814411031901440c010402400d09a0040c59141c00c2000700b400c0210a0f091000d41613a900c0d46600c9400710000352212240064890600e9940703455107102000d4031900032481500c40240083c05400c0c80c01e40b011103941e01007800d151181601241c1344070080c1101e482241301c44625030303000c0742000442d000c0508100c0ca28080600c0b51301150070403007001d40040103888050b891005c1c560340307600d100000e1498910480c145400780701e1404401050401c00c6ca006003400c8807482d400c803408501c0040410040d04520700882c0e0f422036103c040301c001c400c07000200c00e510810708804001001100c3d00410099000038952419035200e074000b071031051201c1a001401814640c1100750100703010b4039035a4a80c0300360b000140410a0310300016a403948114111002442021402c6680b032015040c08a03c000045e10385000c1c903810300420101900340160b19041e513030142042d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 664190026 1250 664188776 664188781
    0x20d15050d030f0c05070b0a12140f01050d140f150a06120f02030c090a05090f1f0b03190303020703030b0402090a05040209030106180b120f19082205090907030308 72
    0x591300f42c1024039084481d486404004038402c1c000d40041d00c0c0503207681c1c881c02100c02840214900ba10300360341c0c0410504000100b001742180302080c1079811541d0a031903040398903640b42408040351000ca15400820b2007000d2030031400076000601344903007001031035a080e240d441d004540c0064514512801b42800001e4140c58049400c06540c60b031194402421641e100f940900070a100b0102114113902047c3d40d6401c101c4800c0013400003108800804004d0840c00182d115580b41c405600da0340f04000603652902c821140c0c5040107880c40450044110004084080c50010082d41c000f580c110300180c00d01880c0d80707841c1040d0017601c00c200d0004141001050070501404000c1d0408050154150f48a00c1c00080003001d00340c0003c0802645070313020480081910030700c0b8800340040108025540201d600308100500030030311416034103d000030910403c2031420505103600900c00d000c0d001c140c0d03100585c00d45581c03592220303048480c00d9a4442d89692641d8500c2d80340e8420344400340101300c42d00c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 664191276 1250 664190026 664190057
    0x21090302190905190e030f1c110f07050d080f040213020d020c0c03120307091206020d140609090c15130f0f0f14060a0c030210020d15050d03 62
    0x150301c100401454010422280d0320005501510030980743c049452030251001030340c144081c007440303000c840301c100150b1416408426016017889000019030800c01003a9041900000d15040350207210090040103441e04c20000c0600a5a48901011919441903211510320580207504061058140e4200c7c05100e54aa40a01090020351015404155820051940c1c00b2110384040c00c040100c41d0000c0c40507a079500e05043c58100c000700082041d84090040004140c1c0c0800e09100b554217103040103885c00d40740d00d00038019002e000c2031000114145a80e80407061154183c0601c140002c58046e01151035000c030f8552640c2d5000301031307a0401d40d5a80718001214490008010110000c032461039050341d01c00181a100142d6000004041080d1500300006401a400403008c0c00700021280c0c0c1604d5200001001d40c0b180220620500501c240c04009040c024040c4111025148100795560780444d034601004201110340d02e00000302150001c9982e00f0000c0344084095415141d11000703422428 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 664192526 1250 664191276 664191289
    0x715030203070e270903040b0406120902030709050411010305040b0705070201090e04030519050c0d0c0f02121e011e0b030a05011a0f1008160c0507030f21090302 71
    0x107001400b4403160303c000114948446568292801000b0345218003d400d00015200d03440b00074203841810741c0280014002400744600311411540c01c0d0610080d00020640010041c02c018400079605010300c5100050301446900118400d0340f10320b41e244d0110b0794100040d01241c1064030090806512407000a9505025200402c04240141040b205095aa6650100b100803c460440002d00080b03103110f447d140b0010300e00c261590a05100d400e0544c2e04411650310303c0c800003034004103c1d960604000380b0079640101480c5030f402500784002021424034195031001d943d2a5135110000c00070b00419682018451800e004100d000c201c1c1d1445000060f00300a040d000f9000303039160041d0012480080d9092060507801d1902c1a06803100c1c220346010400202180b140140c01041c60000002406500600c2507034001446080e0740d1a02c0c0306000c0440d00549504c0000304280b00b400404001d0014000c81302103028400da003456000171211500c0341414001c004004040740311401d0904c01850001e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 664193776 1250 664192526 664192531
    0x50708040809061315020601120f02091503010f0c08010f03080904020a09051c020306010509060117100f081605043e1b0606010201020c0d030b031014010f080715030203 74
    0x4240f01d060003040c1001042a00302c0d64054a00300a00c0000e8840068042c846540188402030081441151685600000384c000a000910500c070490000e503458400030040284044c010780200030300600c0c0c2e54a0802059501c200d4004a0b00080000594030748054200040d6940104103600f4440024240000b07500020800e4003071042110022509484401841d00000903020341c204400d146c2d80145400c0100c1a00030341e005503100e90400c0110303604490407401c04841070700314500a650f05000c002034002c0a40150600903450240020308010000e00c0142421062442e14042e0b6a100704200c200d8040121041c80ba01c81c5092030400b00605581440c140e40011400011110007040c18410b16840b400310300a001040c101900c1c048802042013546c82a000e000851a14a46c02000303907441407002d00c00410580c07541000201c5480270701074000d6034a42040203100f1000010501901e05100340542d00c1030540018001421400018400b811074400c41091032010f0300c4040300301c01a5200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 664195026 1250 664193776 664193779
    0x6010b0a030f0e0a1a0a1107030806010201240603060803031302060a0e041407031b120b06040801060303030506121203012d03050606011706031c02071e050f04050708040809 76
    0x1101d42c4801201001c4c440108041e100d15201c3ca11a110940c4401e2140300c041d0501c1c1d10035241500c98407849100700c088a04042d01418802d4113a0b450100403405841013003800011304110404401d1108048070a010a440081c1c4007800400e450f010502e03500e0004603042d810004003a04040d002d4202071008210b44142883c01c4100141000089010b40328071170b40441e40031004504001425501d07122744040c4083d0f118094158040343701c00240b02c914042c205110060b03031036560111a5072480c00700e5004010b4600244a0302d561303410042c3c01410304503900c501502e9414800d0201840116006001721021400d590440c0d0030014200c0b1000042c001006c0714240c40050b4080c03038040084103000940c40303039008011600d01140010050600400e1888036003140c9014800b1656010a003c40c40e032018210441340300903150360480c600700c2c95900110004040d4480d1400503103040300070300142e48042d0746c02c002031144038040c80107c0350100d503060002000f42c2c0114001412050040c07074104030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 664196276 1250 664195026 664195031
    0x21308120f07050f010c050a0305060904110603070e04050f042d260d06090c05130b090105090a06030903081b0a0305040203011d030d05060d0327032a0806010b0a030f 73
    0x103003401030713600f100d4490425101203034010442d0000903505004081c2d101000b507400c12002d048c281d07220719000701da0243d03803489004048001070000d4803c1e03c10211210005000f4030160500301181000c1903010b4805486045804a407800000300c46204505100b01252075004031210359110184511800c0c0183d240030500f10f00841408010341c2c01420380d180050030001031040c544103204046500c02821a0144403062101d05050702d59000420111035045030010340d03139455a00100e800e44a00400554868000700c0e000c16511750650152a02c0c038425204c2d200c450f180d81c080d04001140041d04c80540d921304010b5080424807a0f0040c1d504076102800208074410352501c8003070b501003624050b40c083da1011540c4049032469004407034100d00150781241c1040210345000381680c0e070028400503080b40a03c0c04414400c00030222500442d04055a4807145a202c510515581146e000020740c4040d00c2002092028010070403504803000d040340c0b80c0c5040725489054015203a04614142c1c241e6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 664197526 1250 664196276 664196293
    0x60109050d05062415090a17060f0105030c0603150102211206040603020a0e15030102070602040602160f15050c061513090309030f081c021308120f0705 67
    0x440d00c6481071546481503002d016985002591000c465004c1101c1221481c0501101941c980b1401c054183d0303050054102992110b452003c81e4401205500000545258604070b08408401290343da000e000c1c002141800c030390382e440c20503942d403441300c001560149080001c900b103446034800c0d0904015060058461501a03602d00d0705507a400c000b26481101400a00107074040c03a44000264455000c490411081e4215004204111a03901840030320945150104190203945503000040c0c00000f0001e65440c1d440e4030b09503020350464401c56015108000413040362040300c003054000d4600d00d6025200d003528094100121702e04100c03021040c41000c1045248181d401c0c00a18412042c1412030842400c10800707003c404e0000b800000c18440c80c01da142e40000760300c214030071304994020310560490249801d0130101d62280a1114403214180e02c06030080510540103420440030105d101489540e42d02c03611626035404c6600110403140800104800d0344024000d40380c880c0c05401210803c1c07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 664198776 1250 664197526 664197529
    0x20306010c0f0503041e081506150406021f05041106031503030301140a080607081626060112090b0402060f090a080a0203010c1d010c15060b090307060503070804030806010905 77
    0x34480003900f9902900000703000d00421030001840c5a4522000218500081c501b00c82aa141c801c601070b090032090784907010a41c80c0d942c8140d554072018041400075551541c070100a0b5584803808000d0105c103c02e03004c4002c22022034801c0c20710694101c03c81d0200ca801c02020820300ea1310061500c01307498803107003441d200b68038100701544c0642004071a440c4081462820840da4129541c0210b110b0f074000700401c808980d01c44c616640003400c42c0d03c4107c81924940703040e032700b0740611200c060505101100303410740c0d20b05400c1c40f907001d040d003a201c100300b80d0450480281552114003003c0c2041c0c5402000c14018207010001700b0103a002280e103542460b1042000492844943d8005400c9078044070905040d07240078840d841e410032090400c40c030b00c04504800b6075400603906111a0601514030151030038000420010568041100750800446131190315208264001a0380e0500a1142c2e040c0070a01d28061001caa02440007a180c142ca15541c3e0740d400c6075500401400a0f0400c82d14482c00070700c0307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 664200026 1250 664198776 664198793
    0xc180f0911090a11070803061305040c060f090b0a020c1009060c08030a0906150303180501090e090f0111070611040b09090c190f0210050c03010b1e07030903030212040f0504020306010c 81
    0x1c944151b40c03499903400e004c030412011502d064950100c140c40d000600000448446c00e4800310381180c20702e81c045041408050340c1c0c4a94503070100c0d20742d050000344a11401c0e40030800740740700b5008440070b05000420b16021030304c1000c54010320000c034164000c603001040428004e5079001c52030b01804604200a9a03c150642c1c00042c000c045600725a07030f0a008054101905015402c1101c2140c0c240070f00d0900000e003042c0700c2e48149542c1844807800325907126000d00c2004031440801e40244050001600051901c0d80721000580d6600d14221300107183c4000d01c021181122801180b103428040c0240800041000150440920708410000720805401100480700c68400a440e200b404001569000c0d0918000070400e00690b4a4101045030200b603102c2a40e043d2a4154100d43d21031503009210f101c000902e00e603115000790045499002c0540c0300c000c1205880c800c0d4240c4d2812480459421010b0103a809160030000055009010a045c1039003d11f904c51414503100d44504640d0700d40c03080b07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 664201276 1250 664200026 664200037
    0x606080a0203070909120e011107030c1a030f0a0e07090507021b040e0d0305070c050f06041a0f0a182f060c030319090c180f0911090a11 60
    0x4464000c28910001e40c90244500c000400712a1000d0004090359a0744188043c0284141c4041c0401c0c600c6c0d4003040c2e48104009207046000e130048505c1140c503400c0403246e0300403a2041d90021480c24201100308000c0205682c0103082c618401c84841e11583c907408040d040e04034000c6507078401c00320002070300300070b0303000d45070040045401610711080341300e011a801d14034281326140100e06007003840004c100c000882c0051040035107030004503600e400200311149124054050000d00c00c500c00320228140114005001d58031034810000748001070a1850321100007192110300700d0101c0c0c00001d00d014240e80048030010412030710000090000d548600e0400f00c40125030303203202855100c0540401b00f01001d542c0c0d06030110b605d9030500b40440703406660b034800101401c10804242d01c0c001524111500000c615036404101c030348055841c0d0341103803041501c41c01840703100c504008881c00e10388111301c01c1012040c1c00c1120b8080c448402c106005c00d8400160103184d400c1c1c0ea03401d40660900d8050007400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 664202526 1250 664201276 664201289
    0x11031609051501090806070311040f03060b0f010206060d0807030c08030108010f1d0a0602090a08010509030c0d1404063f050c0906191101110705010e0c012a0606 71
    0x481d0304016040da420301c01e24007182810300804c0001070140350f030009400c9520640e01e10700810983e225135030300c60f164000d80d400010201b40c0d0003404070410030740347c21140f420002a034128031104240070049070b03248000c2d11070329001004203402c50049200c541c01080703050f01034246120540c410740e0799488550300903800b116807a50b40b40c110b185040d03151701403041284c00d1560f64820500a020340d80361248840d01006098a42c0000c0100a03910741416010040038900002c102a242c1640d0340c0f070300c0e5401445c01d0003060182d00107480da41130207280000d03008040080360b242410304120096440d40840d2041d06d02c034891080c2148211000c2e1b007001c08030005100084601c0350801141c801c00c0c1c81d4040c00c400b88052007806441c010391140005e8130070101d6800c440410201c06a1400d03203c81019078104003607942000303400e05070014270303000414a061240000b001100115010f50351500d06c2c8031410790001d8511491104000010700030411024045400340c410044540d07290821604960f020b107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 664203776 1250 664202526 664202531
    0x14040b15030a0f1a09070512010f0507030c1b1104051909031229011b05030d05011403030306011e27030302070b0a2a061505090c0906030411031609 65
    0x101089181e08001c901c2c4c0c01e10030901c501c039040c0084c440307440346a94017809004196a6254000c520b1003500480001440940c0130041401c3c120002800f40c0380082c08003000c59840310800d0f0b503031608034a55a21858102c00c42c407814083c00b00800000c1c000103808bc40380c0291203c03c499054440b4481d007210079200751915001c00c45c0e0005104290303030340742c950b044016920b0300a068108100c1904010666000d10b0300c0e140502c2619081c40344449101405466848089403c80c81c0c40e119500a50582e00c07d0b4001a08031ba070076404141e944c1c4001c50700c043c00152001c503403548514a04021a4a40d1681d0500b0b0f4401c10b41c2c040341d000c0c0c4000410b568098540051001c209042d010b1100c03001900020340141c0c0f07095030042e0040d00b00704201000040f040210b0150b43c8a9a220341803030b9568503400442400075442111034803011809a0007528420410b00c00480c171081030325001c0318500040600524215981e03a00c400a000c0d842c020961303010b024815190800425850301314020345200c2d07000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 664205026 1250 664203776 664203803
    0x80f0109050f01060305150c04031403070302010f06030203100b03012712020a0206042309160f02060118110903030307050403290c090103110a0504140414040b15030a 73
    0x11454400010001241e0f0391401506102140d000328400c41c01a06441403001180c680c0020030015116990004e800717070304000d5001d6880c40000c00108005802a0b00034000800c20300c03401e10440d00d02d840003c1d07060388108490340d80680103400003242003100500001724032180b45e9282217030800400d050000da0007074030b2107601040509a41094141d103d4070081c41e0a036900d5020840c113202d28020b0704118014088070400c404074403000740ba00c405020b00850224107048050399000d004641c0c00310085480500d403003070460300c00500141207407044621804a6002d450004009100034140c04420394010081a682501c0400040d070242c013150350758994852441c24481e10740718602d200e01c00c2c403e00c00000303001c602c44100c203592b0704180c22000150f9034824102c01600103012414000380364404c003242940e40290804091310840710074650800150110303d0412044a8035016012200d05561010078042805108802d5108400d008044c0c071202d2003c1c0043d00e001d5120404884408040c0704 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 664206276 1250 664205026 664205033
    0x1409040f1704030b090f0d05030408070c170105180304060e0301060b0a051317030a030209120607030204080d090b0a1107030c030602190f1d0310060305010f051f120c080f0109 77
    0x200b1175106001710041d000340415583d00765100c2c02c82c00741c180d0030004080003147c24000c0c1d10382201c030403d03401070081c010725689088500d100c034095079000855502c0e000000e4a04c80108802000040d04800554038190800300c05441211440602c0b07a007641d41c0b0100030070840030310001820a240b040d1256522400b030032059003070b50000d9404c408000182002520f0240400105079402c03030340d071401c015072200340090200e409036000c4800d03a0a144551428010001d805130300074400d4400390f405444450302c80140c1541c180100d4800c0d80010141088400c9946200300d2003c980c04c042e1a00b0b6442042d40c1c0c0c0c5518027070020940081c0e407119400988010600444250543c40d5616814040d000e4414050040e01c005000c00c100454400ca031040101d69917000d000c1080c020364614020010a40c582c20101d0007000c89200960903e03181c40040f8520504203995443c40c140d2001180341902d04044122140085044003264a044c140b400866609803d0200b416520058800051645203d05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 664207526 1250 664206276 664206293
    0x53c0109051e0303040602091210151d01030602030a061211031c0c0b060301060b07030302030f0618010b0a03110a0f0311030105150c0a021f02060705041409040f170403 74
    0x401c00c4038400b011040c01c08001c0020098a500c281c20060040e241c0c503003180070810704402050314a455009a0410382da4014666000d00369800c0205100500c80c1d494842c00920340c1e01c0c41550000786140c0900420014000350000c607070200d4420030101c0c0c1550780306800b401040710500200c03000203c281d000c50b4103040c00c125647c01d11460760743c0005188600c21024240390b00d1003d000d0141d00c1c0050000d071a03602c2c250002002400403900080d0740762014140207000f50019907404844206980201d0340034540340d115828016021901c2d0b6409918001510705d207176202120b07a0052544501041480040610203061070114540300c5400382c10325010000d040780d801d583ca14007000018001401507846003075030301c0e600307a0741000003680d1051009001c03845c0c0b101c4464000d60003035021017030400c60080c3c0f48000900c8081c6808465140d1140182502c01c2d0089025401c4020001d1280b02d0761440c000301d1845c1c0041c0214040b04800195440380c814400e01020020341e034090000c1c0403c2045000c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 664208633 1107 664207526 664207543
    0x604030f170f0d0e03030402100c05070f0b1b010911060a09090e1c08090d210609150b0f0406080c0c1b040b010507053c010905 56
    0x4055914182d034002c1c010440c215044c011003425042c0000280d0b8061503004052075108103030140c1c1218034080d080740a41b80c80c410400f000509c6010403c1c01e001a04090013410b50707481c2d880e4080f0099040c0e041c400b10f0160324200720707040815003103024042480011140140d81d442d40b500100c440c030000d5085000b10310b251007030000d0811800941c11404401401c000000607520105c240e507410f100300c8208050350080c08002d41442d1082d080303a80400205200303e2020b8034003204e40c40856449030004204903603122035007003034007960310841d000030b200010600785000c204110350070035400f4500c56201844440c101040302c00c1c11031400c6d500403102100c1215402d0640c99003a840408801c2c021038012454001c0000e50f0b548030340101c1c0c02c1650007a004000c054044000c4498041c1003070f41c0d81d21005150200342031070b01d517260311407542a1803100011611624605186040032000d = true := by decide +kernel

theorem cover : BRFrame.Cov 664028776 664208633 := by
  have h0 := BRFrame.cov_init 664028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 664028776 ≤ n) (h2 : n < 664208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
