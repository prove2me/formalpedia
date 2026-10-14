-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1341
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:28:39.77898+00:00
-- url     : https://prove2.me/submissions/19ab8d21-7c59-421a-910c-76d5559f701a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 241007194 ≤ n < 241187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 241008444 1250 241007194 241007231
    0x1142a04090213050301060506090d0b0c0705071d060a05011205040c12030903050d1b061e0c12110c0d0e041b0f02060604140c0901120c170108010c0509090a 69
    0x2240e070f0f40141c3c5000070003c60400313001c2c0788010281210868106061503020400c0c10700b0301000140925442c0000480f600c400c0403e89010b20f81280460300300641b84d00c042c0040310b003003201a5a40d5000b000015950b460078179001d0003a1001a5204c04501e5051070300c3c2005400d01070400c540811550102080b1401120b02c0c0c280c1903070096a40010041c9141001c604000381405048208039005445600c84c1d0300f0110442c042c01d91001c400101e800b961600440c1045d5400030003003190303003441e000c080d01b00e600200c410f0a11494400c100316076038005565031400e2007279000800088c1c001240201c0941e0180b80350000c1e050016001080c00702c0c0e8101da1444021030800c81c1800710716003001001c40954100122070340200c050f18100051304840681d5803080200a206a400c0400065204020392003103003107030380800d2504018001034805800141c0305050004401076241c0c81c200000602a805020b011140c461701e0300e80900d0485c01d1414000c0480e0300510444100d030712521a80c810300b600b0072 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 241009694 1250 241008444 241008457
    0x80304050f1605190608010302010507050a0b0a0914060103030e040c111006031202070503030d0903030920101809050903040b0307020d0f02010b0108070503130605041401142a040902 80
    0x602096080e0b040504101d080f4441c4e52800324056104c4005001d56034000d41141e0540e5024200306851b44240d2a1440ca07100c2c080f800107184400c48020300001654582080f0615403003402c0c441806c0c0b615102c11651040309201c00b0b000078510010003080e41c1059845042480e00f649440158844100849440c1080013110031114603a5040104203000c2d5100f10541940e2080c0301400840d407034500040c1d6207000320140403a4a55462400e0700030140203520030440181c1c0070486802c410f5200b81c150544008010b2075a020303407941d20200f03035084c0c81070017a842e00c00c035403240420660b030a03c00e50100400c0001d2001070300f44000c204c04a0b1202605000c0d40c807514440c0c2c020316011780305940091448065412950541e1f040c602d10351120381c2c101304600c0c0e100302c1d14944541c50396501502d00070100b1000501030156403804041c40280b1003401e903800703198200d070802841090030303189102d41c5100e0121450213104441c4034110803105204141c0c0c030f02944038805103500f07103034645003484100d03403248 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 241010944 1250 241009694 241009723
    0x70b030a11273304120f290103062c010203010510050a020d120b15091503041502030417190207080f030d02160c03030f0315060c080304050f 62
    0x742580c01c00424030350071998007648281d40700c016001819000311000856401d0200f0b04455046001400292801c15035004112098002d041455103042030b05800140c2d26080c0c424070b0690300450029112003030f00c240360000e44400c0702041c0e8a1034075042c0080040c010000e0840029040072000701d1a510341d00320003041d4003800142e42c2e500d04401c0120244107170b150343e01480b0003404004043d64010034000c0c2880c00d2410700c80e9854800000d000010100700d803000343d01011811b62241c1c12084200603200c669410303154005c140000c098046042e003c1104c5c000e14800f2101100d00a046564001d182c005201c0c40e08240404115005000d640e00150150344103c0040000d00e840d9a90400000d1f0040a01c07802500303043c00702c2c940303103900d034810701c88102c00a82d00060031030903403007200041010b450340109907451030644915004040449075100240043c1c01d042c00301d0f110115101c2c0c0380d4101d0700c40751124850040c56503203980842c3c20040007070b905801041100300e441003050044003d0a41e10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 241012194 1250 241010944 241010977
    0x8090310020307200109020d0b070306050a1e080c030c060f070b0406020307031a090610020c06190f0908070603090f201206040c0308070c032001030606030e070b030a11 74
    0x607503014000e0f01850300302101c44c90b0b060258050150310360102c901103250300f016545c1c1d0700e070b980e2941c04e0703001d003865038880e980155203102e00040c0c0c41c0074607031280804500462440354450352020340f544d44a00a000340c0707905400c01c4c1c00780300103031404500600481180c40075a5080452030707241c000802904482c01d4034415000400c100c08150f140c030a401300c11200b59410a174801c184000b04041900003000203004034840c51120328014020400c81e01154030042115aa95583c00614443c03803542c0c0740040d001c2240e90880380d4078180100b1500703054840400017445103d03c2c080b0210058840040d06588084010140202103660454a82032154090300300410b001c41000c10b00c00f42a1000116143e19045003060000080c1001000c00842c0e8012080b00e803602814103200b19010b655502c000c242185907460100501d1000c1d00a5400000903201000041d40d210020307419684151040360164000c90310500c1008014030246030010880b010005032135498800205041e030041c070511000094 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 241013444 1250 241012194 241012217
    0x80a03030c02010513020906060d18020a0503030307050d180210112103010311012f07090504120c030306050d050c0a05060a0801031712180d020303070c08090310020307 74
    0x300350007600007036200c0748000c101504d00250a40024004040020b1081800c00040b84081d074400064500c03a01901c0c40c2000080210b041080d49000440702c00c900400074407030001090700e00030054a1182d82551182e40c070f0803856215080050004614845c000303090701d44802d0140e1146c0002030000d10554440c1000e0f0314803200120b18120005a0f102052881e0105041010480c0c00980b0304603075103d6191042801c1c0380f401a660a01030302c1460744446c0800c403100084000c084001e109040c40c1030180c40816854071695010386004a6018000002100c200204144500d50074002640280303000152140c9600002d182602d00d640199840d030f00c0300c041000360f032910013001c2c40202030841e0004d18044400c203001d01001014800607122520320126541000e104808a4070400031038510b80310a0b18003110000d0102601100203c4140f1034241070007050340c000000c8034010381e419141c001080f0b10558402c20f440d44054511609406407964050520009002860003451a500c41008550 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 241014694 1250 241013444 241013447
    0x2030a08031f08070807141309081c0c05030402010e0d020a06050c011a030622020301021201090e07030c18060911031e10050f0d0b010603150e3607080a03 68
    0x49840d003020500d40c010340b1080081c2031700040c0d0302d0112600e0f13807210b0b000c00381558000b8165501a845600b500c030706000b80581000b80400c003d06800004284803401d92901c0c100060807210441c289101080040000c80c0256004403414808103000409217444103919601007113442202e44e01c94004140081154080900280a56000020845070b40c10080e031070b1a00080e80d0b000302408003000c41450741d46140703210345c045018545064000e802550f07a146a48109a080b040900c0f40c1841180340c525400c0c01c5d4403000c5820700469400105517403c242c200458184881020280803540c0c0b40d4800f8005040085801a01c0540040341c000035142e151450307000510390b90200083c280c0380c0c082010050540001c9480c403059820036070f6100046c0070103a000c14014240e189015160820319000002e0b0703190315421414050310400051000c02d592100601c0708644143e071151001a00003400c004010f8507066076149102031300001d00c081c6680c0e440301509201054210399510f410010f4000c0505 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 241015944 1250 241014694 241014751
    0x14030c03100c090501051603050306011e0c020109090509070b030601020f010504050d020705010c1208060d0b090601060905031b0609010201060f06081e010608070f0504080d0804051002040e0f0402030a0803 90
    0x9110a00b0401d07c0c03c10318241c0c10300b00c08600b2500400f844404400f20b0116480355840100b0301c1150416009100b44000000c1c1440048010072400100404c001040c0c09180f406024044c00c110300c01080b0b1907061021a8035103420091085045100303208400003070400034002d0034001c902070805010b0305041100c1c001d007041441d4000c5414031100170280d00000f0a01e0040159010302071420403804e03104e900000709008158070001e000c00420070103001005402080c0c16049900c103860f00703800c0540e150b0034151920f0340d65480c1400c0034903c8084c9030310382c2070100c000c000c0144148000580c0030b0f00c0c2c0202d0210705807a0f0b04517400007000320080280c09040151000400540d14407107540946c03512000900602d802085001003100c04d4810591103400340c41079802501000c800ea8001104c1d048008000303080c00c8130140c03800d00c1400e808000d0305400c3d2084800350398410141403c9a6a80005030388000c4000d08204d030544203030f00d03585000c5442c0c0310281d03004e0004840004045011201800181d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 241017194 1250 241015944 241015949
    0x31407210509090a051b030403052205030a02090402150c031917061944060417070206030703020c151005010f170411031b010914030c03100c09 63
    0x1800420003a200041d9220b00743c07140e100321001c2c00410180e07507042a882d580580fa2007030001031100401400200340c0c00c8000f6040c404500311031001401500c0c039613164804103900c0f035281c068001200b80400f508201e403d09611900160500031540045c103c400c400764040740d21207450350004030310707801011003098404000501d5440c0c10800c5042e0f8481c0d030606040064010b906c01d00125aa01c00ba061151070503900402e407101c2e460101c02480c5221031000414040e07411180f8000c200b0310601a0400c0c09001500060030700200102d80e0f0b0765944500c18200c0c000386040310413042c0680001030b911a00110700c200544e9030091f1311034513503020051800d00c48070f481408107003132481003282c0c07101d440001c1c504440d001d103408030b10828000c1081d41c0718181c5902c00b0320102040300401042c409101484818620203404403540210200c0a0101c0f425000389403d0000d19040000c100011808035000034442c4010300b901e90716032101e000a0f01d0a0241c16041031100c1d11481517091007504091603200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 241018444 1250 241017194 241017197
    0x23030f060624030c07111008071b1505090a06090f0201120903020c100e0319051c0e1009090c1e110a08031b0304060e0c010302070201170403140721 65
    0x3030320b60b200030009406000003450132240b013101140c6a0203000002c03003c1c14100340c0141081213140c0c02d2030001401d6100884940300030a18140070030708200c440f0410b8001c1c15030042e01c001d00310b400d0b000e10360014110240812a80c0d20a00064a0225034603100700402e003032264004d100307c004540300140044120007900f0b442145403248040c08240c000c10000c0202c0c404a0301e040c6050038540303043c0c03101c07046100fa46405100e840761442440100c040c8803041e107800b41c0102e85810300c40d018942c500d80e083d0003600d000030342d51040040c09410010090b0080a40600700741882c50340fa100600119000251048002018454580c90900c8005c8890b884030a040c5003100007501c80c42c0a161340e031100c4c848000e128510000018000c40144502c0c045004801c81c04250350b0308007410a8809000ea5010b41c3e03ca40c0121305020201f58000c0c0700300e030300040c1c0c11384070319024203042c402902181c94000c00540501c41540011348908510304000d0088503c6070b489a42d490032105060182548800e44680 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 241019694 1250 241018444 241018489
    0xf05011b060506120a05010b0f1002120a05070b0c0702130c0e0d11031203070908150f07020f16080c0f0604170f011505240423030f0606 60
    0xc500e9031520a0040040d8201201152945911002c20251030183c01c440300e003030042e10130349000c110041d00501c0b80d00900b205c1c01d00b501c3c0d071303850300308501c40391002c0300280580d03c500400100700310008054898241c05013400c9080c140e031900d640b4002c410455107031110700b400140d00790440c03800c0651541480710a2808100d1070420a030046d211000104007644244407503800402007011100d40c1e86441d001c05800d50b60070421019a205058105940305004030305d031040d022580c00c400240a9000c42031142c800c42090315041c40300300c450070300500140118080d0300c2840181800c03c0000c41c103c0f100070b03900030000c2c616180c00c1030b05200c65095054420b00307481c40051810b42d81c1100750ba054071520241401e00c1c4085400f018070f01504031310309040c10b5080100e203800100040e214007046502c01c0c2c1d135588695056025094041d48902c010703480f51740c010300c02408610b81d01c101e544128084031016903402c402c00c2e40004d1801046003c40c020583c040810441941082c14842e02d05919a901c1070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 241020944 1250 241019694 241019717
    0x80a09080409091119170c10050a0516030905010201140c090f010908120304020a08370c0f0303031b0f080709090504051011070506040209090309030303100f0501 71
    0x103090a10440c03240d0501151a803400c0b00a10421030000b070113202000700800c1c03120b078217030440d1030780541c65100b0002808902c84106008000200342692081d000400344000c0a03a110810342e0a0b421504c102d2007000390602c42c00c22460401d100440050b402615440e40c3d00b403810000a0a598000d0054140d8408505c14044205c405c44241d41940030308492420400c8109030040b0790003660343d40b08018a2107500502c0300500d4000004500850003601c0c410540d50b154807100d035548150940b01092260304001980c08101d05481d2269450442281001c100710a40c48003907100c44540c10090105541e1a400c2080640500c510304c80c2d604c0881c2c0b178105411a450010f418103030381e10446000c0c45600c2c000201d8030707482000010068200040104568281400d1079a0707103030500303074029071054a02a901c601c5007004005843d641940070006003250741d80ca81c01e0007402600603003241c85900c0140706032103031581d0500195200700710111541c10040d140080300c0609a04a6200350706108850151 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 241022194 1250 241020944 241020953
    0x30d0c050a080a02031c050604182303160305030f010f1a030a021309090c0602011e0e0118030c06060e190c021006090f06141c0512041401080a09 64
    0x40381030468120002d02e07120240428140c3c2035114440302d52010900c4180341c2c400c0d5424a6201c44c3c09a0020b40381006400e40d22500d4a0100203003140141c159560f12801f00f848101d90020742126502c03d80603203080c08011810401c003140d4448044000c00d0b404820003d0120070a5020390043c02105580d510707540c50b010440c00c068242c0810403042341c1c00040003c040f0b81140c0c049448440d0065041081c0c1c0e49d5a20b9210003c10044e0341c01ca03500710380c064000a9081c814054141c030714a8005003c0700c1c54180c040e0590050100349900f000554880701d003005442c50003e1112282402503c070146c070600b45140c21021201141c000d603024400c400d06001682501f2002c518010300e442c240040c00c01e40b0f180059180c620b28900302c412039410000c001c2030a4a10340c001c01c001020b051002d20001e902c1d98011402242031003d01134106448180c45920020110f5803400c1e41800745007502d800811107210580300b81d103d40c112130340e83c5604204541881d42d0041502e64423030f030000801c2151264540d40c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 241023444 1250 241022194 241022203
    0x1104030b0a06051f021908040303020607030507022802030304091d0f0a111903030f030e0703150b061e030402010801170c010e13060801051015080c0703090b0c060105030d0c05 77
    0x922620b00001401d69013555000700000355034540403e100114101451900c032146511601044005029850114440a010380241d500411843d00070348030f4100f1050303038910448500c9880c200d10401d44107035400580c5051004201420107000c0115289482c016882800058020004182c3e40f0011124002e1030307020a455584d6940b180081c031150b03240d03200086090502c145100321401000000108041e0007810020022070345441c01c1c800b0407600349500317413200d0891001500b0424140c10003510110f440c1c0c050781e0002d034020b0130681000e0f2000e00d0347c42d80c103030140302002c0f883d14000248070030f540c1c10250590051602044804000200214a949a41002c81c1850602c040080c1020569a620302440b1003802040300802203e5a01c3c1c8910340a400152140c940781141c0410218041400f100e00032845282c50b01c0b1605940c49611407181241c4c0304420940800c0144d01c40440c52190b007000a1806101250003405994142420103007850200e10049061102540c45500013403808503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 241024694 1250 241023444 241023469
    0x5030702190b0a0c03020106080f060412180f051806060d050709081f0e0f12031302040609020d0501140a14060c07060807020f030307120b0d05011104030b0a0605 71
    0x4554001e0800d0100700340748104420b401c4071540c0030011407241800340d480340c00380711101d009600a000c2c996070340e0600e0f40c440065028002040d08500e0004021030741c280c90143c1d01816a14100195040e4003801e400040e49540110140741030b00c1c0c80c100034910b0107034203a8104032440e03d0340301e00c2c6090800008500b40314000c806440c0a48590018082078040c42884000300340e2001270b500410f16050140c200c2c0c1a00b5503c1240e404d103000c003800c104d000c4c00a501440103980000a16038451011782144480d0801881903150780741248000c001030b12540101d0b0f0003400866400358440d0b104010b18410340e041600320042c10301e010342c1b2103861079481d054210222101880d441d602c0605960208000d4400c0b18584085c500c10742d8000603c581e80300c01c020388a0800c42d42699529a00d04800c141c403440256200b800246214000765000c4066510201701428010700c00540c500c00ca94500d42942c2400d1020b01c0320980114041042c4880008001d40c050130100b01000441c2c1440b002982051413031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 241025944 1250 241024694 241024699
    0x50301050118031e0615060c0b15150a08150a060e1309110a24032408032710051b060f0a1404020d02060306010311030f011e0305030702 60
    0x950310040311251141c110245070400507007103e04c4d040c4007015481112580d02281c0d44e80c80d000c41d950b031000d1401803080690321030366504078100b181074032010040c14002e40030f40e0010140d403140035510b07034600c101040e03078868905a1903140d121002d00603007201001020803500d1020002502007551386c041c4841e017618840d04210800080e900081401e0901190403400d18501d40144401401601c0683c40500c0c10304a80f001c01550300c504804010004c600e02c0410b03150682000450010f00940103011408503401003c8a010f00816840701c40242a030706c14142e80d040040c0c00300380e241c41c801444e0800484207005600c04060700c00851007020410369048200400881c0500308103800444044020107407004448041c104130070300301d41d1024140d8514400324500f0910b0648000c42c4809a403040c2d40042640195119039001d001e40c41e40001c00480c1015900d1300d0303160311203070750801950141c7c1d804480b0111541c105000d1b0392070600c1003500350035522510001000060800400c68a03031b107906 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 241027194 1250 241025944 241025957
    0x8040c0312031e020417033a05040c0f380f0703030e060618041103100207060e10110d09030e1302120f150409081b0703061b0503010501 60
    0x41c00045009010f0702502d011071092a00d502c5048403500d4000e0700c180e51190b194829902c04441c5c500b50b50344584446044c61441c8541c0a0b1070b00304400c0c003051070f51404074480b2103ca914a001c004102e901c2201d04a5000700401d4050000c84410906800034003511101c0558071094134503d411204004411300b09030b00012003412074020a1307007044d547d030300302c0709844103840b260135150144c0501803d2075200c205105944c0050030703920f060403140c58100c80c1c00f0441c0c0b00c1a11562903ca0000d500d9294140e054071480c184580400c019200410002d070143c5800100fc181d440005400c004540704040115400c01c2d04ca43c440120f000304586580c0050400018010340a00e400d032501d070460140298024012801c45841e06500d0f00181146011901200501e540d00c0943c0e24264070152041c152072404028070348058141a0301c010011405188601d0410150500d166204002c1c10b010280a4216400070001c100841c0104500c010000c2084000c01941d010000c0c000c0c00144100e0307040000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 241028444 1250 241027194 241027223
    0x2502030703021002060919170d1e0b01020f0d0e09180105010b0315120706050d0b03010612170424231e090d021908070612060608040c03 60
    0x50030000c040041d5800b40003040030058078107010303440740b40440d403d50103401003a21110001c1031600400115a40c8004c454040c00101108140d50f508841070030700c8640c0e612580045600c2d401d0300354080008860401140d08802d2000083c03c04d01c105c0c00310700346030b848801c0c091152030300800011044001507c4810143c1e544151034080c003400300911600c95440e00c03001245030204071000b54411141d0780217000702142c0f2603003440180c1095203511101c030f070007070348043c400d4500c100000c0811028070f0718007040070b0103030718000303821182d031036010003078a8455144030f004115448298002c2c0c200a0000389042524000013040724081d442045171161404100ea4280342e40615442440b03800c9801c000104601e17003100016840d403007103a51140e03200001da18a03008903000d1007200e018880140c54510030034459400d00a0249008c2c0486840e1207001d100421610000c1208400070501c9076103203280f0f407002d000d510782141d0060300300c5800c00c0001340404c00843d042d130a9090441e40d228006510321300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 241029694 1250 241028444 241028449
    0x15060d05100207061413020a0b0306060408100b0f121009020111010c0201061a04030512030a02040e09010207030806120307110103060807120b090c0907110304030c0b0c060703022502 80
    0x3801d01c8148808a44003152072001c0c0a02c603070088840021070f019141c0c413511402c00e4424a040120310080d405842140c051103000b08443c0a103821400103040282405c1d00c038113085090602c00150740200e96510740f50281c1d1303407802c1c091009081006440541200090313080e0581c56162102d80c400b445500c810180e01164401c00000c400c883c42c40008204030135094400030301038803c0780f1603007401c14000c0440740c0d0201e00b5281104c04603548000103214040030710842b103000b0b0b003005148091f0b0b95800d01c4005000c03010184014032a800202c0010784c0d40305140b8001d040f4060280840d8010205000c071100d0020000089405442d0003c140048150394034004030058102c540095800c0d000300b500c0080d80c45415048502e8562050540d4002c85d039861710b4041d901c64102e269280e0182c000b01c046036405004500d901114425a000d0341c0c54607450f6100e101c01a052a4000300c0c10480024100740080e5041c420103070007007024070701986020580381546002d541c0c8200a00079071071070300e0758000c02c55 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 241030944 1250 241029694 241029703
    0x1b01020705060f0a020c01020303060a1a040801140108100612030513051c0302060a051b0d06030b0f0412030e060714040f0e0403020f0a050d03020d020d0f0b03010b0315060d05 77
    0x805006000940d01c00d5250f00c025501c0e0405200d15004d48039091105040f9070012040d6482510042c0c08255403910349610401e9840d41585405510b440820000c500218280500c42401246906200350f1794900040700c0d242c00324060340108544d01e0030300240440c0c0004040011501d40519050b80c485043c0e50011348180c3c0294040d0391300120741002d0b840c002411401c0c8101c1d55000c1d40035160191703249480001910381c225103070350740071000c8440300d80c540351200c01a20b0340d2404010000b076a9612580c50641d041c0c01a00d03401c4030002c51a00304000c11402819910b40d0f10f44d103103000d00402c030039840c24a5464070302414460600072000a2195504400ca040d0380007084c00180304501550b4817502c04080b04402e071070030784c01802415008514000300080d00c0c07408030741c4903005094024804000b24029044141444880d640070860750041d00302a0050701d4100b0016240019680e14820130142120032413a262802604440d40391400301141300d0a059004034203a904440c090042e14005050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 241032194 1250 241030944 241030949
    0x1208040b2a0d0b120c030139020f010507031d030a17090a0204020d02090f0303031b1b011b0f0906050d0207290609010b04032003010612150c03020306031b010207 71
    0x2031070305022160392810000300c017101488180c00800900f848503c250b065000345041800800c03136480d40099020317442008000c80241030744141c0d5207205100c40340600303488003500da0100083d260301c00c0b11083c0c0114500785140b00c500310003e6140660400002d8014180c207010401e90702e00500c00a000750b13005000c1050129402441195070740700c0b04250780000e4009901d41400cd0204012108460074000222405101400407848c40c2203400c540c0185141d101d44017140c2205180b20503091504024007400741e92038164030301a0110114050001c1c03c50203200e482c0c1041040c5900d0070020b0701e400004071070b1996690400980d8540e441d09000040450118a22096000c1c40008201c018001811140141c02c112040362986e6a0b80d003410703503207004030702018002c414110300240801f41040ba000c00d10003005000442c4996403411a602003015544054074034085281340c50a004c91140b05221041ca254107085045041503030100303580d49803c8060070664504014a00c030103a0007000403200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 241033444 1250 241032194 241032199
    0x304050d06021201080f0a2d030c0b060604051005131a0a030f11090103090c05040c030c080f0903030c030405030906040b0a02010f29010306031208040b2a0d0b 70
    0x50500040c07412200039440a50386400000c46040003188900f000b2441c0c041c4850268001c2140120302c0c0c6403040514050010702d01601000d544481d0448108011041c295000e62590000c00c1710340d003042d4048400060209211f00400c120130f200c0307583c803052400f42031121440c2c45503c0d54550812440c8110054200342c3ca0100b421085010428400c80140100001c2e541c09010f001c4d00e003107610303003915603490074250b0440041c001c0c11040e52281d80b014040c503015024914030302e65288007184c1203420501d00790300001d850f007248910890b04058059005030005001c000c8070714201038140d032240070107840e028101d0f0001001c1824084e0410a9500914006220b29551551660351344001d502119074000035500700320810b900380185108800c85040040e44a442d0203041864002648008481b07043c140741c0e81d14400300c0820b00b8428090b03188440c1d0b8503a00890f0409040c83e0880c0c0000a1424a0350703800110a41e4032260185040071022010090258450000c03820f040c3c09418100d0100d42c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 241034694 1250 241033444 241033459
    0x12060901090309170c040207051606090906080f06010909020d0b090303100b03100501030c02030d0203040809030705101403100302100305040b060301020703090510020102040302180906010b090d02040509030405 92
    0x18a01606500a08900d072090310340100640c0c1e54840980301e4003035010380140d41d82280c19041e809081c2a0010401c5c540b2034400e990100d260780c45100c001c904281c000d400014041c540a1003090030038400c0401505a5400808100c401a0802543d40c6014001c482d0155180e155140864a420050008580d4414089407803450410221566904110391300744009401d18000501d00e003280084a00403c09100c021603114180001540a0803107403121500310310040281980310342c9030b88051400307188615070090340c07101268200740c44c0c51550740141307115802c00903800410981210a41e0b11b400380d19103030b168990703941d40c075028204000c3d58406034008000c000c2c4c2091040e0705a02891040c4d101d4003d46000361505004d244c00c038006c2900050101da41284180b1051030a8180605000784901c005807a00792241d01040b80c01d1a9070003140912100d61040c803c42d10420300400d409800b01181460074a012080001c0040d040070102078010b550f9840400d041c540c00b03004035006008040d0002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 241035944 1250 241034694 241034701
    0x8061c02210a030c110d020d02090619092a02060109090204110307030b0109140109050909010e01110a080a0c0918090212030a0215060109061d100801060e090405100b1206 75
    0x601903008403101151840c0d4000c1d41d40c2200e21b801d114800d20560090300b1001800c40503401e0003a02c0c500503200d540d100380344061b4131800d82142c2200e0381c007425071120040303a00301481c0c202104c0044171110a901110501c0210a4019030014880d4110f407118200400da01481d400842c00408801c800700c2005c0100104011078107415411100c40c0c1607082c1da540d50b0860341d810410780f50104010060f40050f4071000d0401042c42d007000c070160840c03440d000020300c44903442c1e012130844901c0505d4401d844c070003060281c2281d401081c1c1690001c4d4450041c040c036280d040f0300038819000360107102c110301103101c001210802c00c0e500000400ea0b02410300304611009600d1190740350000b018110040c820926010102a11040994043d41c0181c480109407400c100f000d8403010601c006070700d1045000d60002c19580c0d60031503001001c4119456200c155410810000d0402000e0201c042c0220f8024040c03000294000070403541900c4e1114000403252800d40018100d01071851120640d031091000b030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 241037194 1250 241035944 241035947
    0x81506030115081803040512070509090f0d021c031a1009081614060901140a0c06060909170a0215040501020c0c030a050d0e150d050708061c02210a03 66
    0x30005030310707580f107a8005a54080401c40d00710006502807845420500041126040c50510300725008640c1e010f5600701c50301d46000c102095000ca4615406620a030040310031107000340320800c2d041d442032001c0e00d0585004000d0481c0341e950f00d07002104055441000450701c4103c42105c04512030020413038405880c440ac8000c10380841030040400c58010072204c0c110b49241080344408560012034840c0f41610755a00b0071036940c0007039810038140405108812030700081c0c50300500c2000c4080c0c44035001041c0e241411001c40311140c0100c01d080340780030485030201d244c050003800c1d6046147d801540d0751940307600803800c003d04481c40d40b00c5074404105100807c031040d00a4820400f0441c202c500b000e006804159075411540405065900002070300322680348602030510644d42d015004080503110003201010b00d520261080c40d100703986405000c201a84841c0060b002481200c0c0f4846512500702c084c01c0c0070082e42c00081c4a000c0d042081080103500c00c0c42d20709026880000e03500a1a0076060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 241038444 1250 241037194 241037219
    0x1903090b130311010f170a140109090c090606050712030b040f060e090a0c1a072108010b0f0f091906020f0c010912081b0d0903030206090307050d0815060301 69
    0x1224000564000c0078a42c4d480f41c100a916100310740d4801d100c019040d001c510094a010b0a0951104e449207000c4801004000e9078034001c00406200145c07218181c20034080340342d45500000d9000e4202482045507581c044c0a660101d90840c80300300382d141e07050f40140e006081d120105a0814241038042080b0000c07540300c03004461406041c0049a0354401180d03880f03080c80c807401444294a12403d001183c070030540b1420760142c95004030702d015556141c0c080503150000c0d11080083c0100115880c050703002e020207004092004415041038a5481202e03928001e8640f036147c001008a07044d03580b5500c11001440d19081d20511081d0592076800017510340d408a90240e800344501056210396521450b6642d045980320120301401240e269182c1c43c6551040c11280459000040d86002e01d4105020481c00d1300c003680c40307800400e491443d001c0c1c00c20f070000385241e8007074009101c103c000c5500440d54442c030032058540039805980340011a8409182c0c4182c4942008001c000412500d07601c20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 241039694 1250 241038444 241038449
    0x6060c021f02030304140708100b0f0927150405030408070e19090809180702071d07080405100f05100b091e060f0c25081903090b13 58
    0x1581c0c60004012010001968500c010300d0100603842000010302295500c40d100b0300144c822025514815a00c0c440e44e46004404d10100c441c850303941032502c240c2d1610307142598560406845004d440d00d82122481c051115506a8542c25800c40c0110300c0061010f004000c20800b504448860500b4a4205031303540e50464019151184601c420105000d0701c10070f100b501c91500b0015200d201b500f04608040544018030044608240071b200c410450742d1100c0c010420000c0301300d074503101858408002450300a4076030140c0851102c401c020b46580d480e031901c07140e200240b0b040c608580d40f01c0345851840e1492110200d41540c4c603010110300158101e4004d0350052072884041c01e0800e445103402030b02c6201c0d120380c0d164000c80c2e21038000510451241044503560700140440d080c941700605030406a405642c2907492504249000e40000c8529280761516140424002a01c18100324003242d48090101d0800c6003c1d4540070044205072245c140480501a103500c8142c90320104028940d0001990 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 241040944 1250 241039694 241039699
    0x30408151e09031c020c01180209240607030207120501050f0708280b060706090501060f032f040207110112110904050405030912030307230f030901060906060c02 71
    0x28080c81440701003400e458040c285410146160a410303420b41e04407001d1030440d00019540a101e58441e900c402e205040700d24120810200103940c2d00c0c8100498403c0040101c81071149580420607415040c065800d6445020b0341d10715075400c00381c14161719000d100d42c0056052070005410604010b0190410f501414106018802d41e0301c44200035203001c0411905d00d9030b0601a6600c040c64034040c1200d040c0030501a040018484040720045403040d4458031007680d4803034440b159601040700c00d1280c0700040c00328609265203d0f00b180e5070b15809200e500418001181106001d06c044c080c48500d07540220320044c01150b40d10303c240362480d980d041c80c0d44c00e240030031a8400e80d40b09906a03400745407002941d460701c4034a028006020400100400780042e116480b05200010150b16101c119880d0040c18000850720b92414800c010511203407000031240c200d20810344484030400c0034003604d01c00b529013808241c41c2e9982c0501e1600505180c0d01c2042210b0034944005212a04003003d044218000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 241042194 1250 241040944 241040971
    0x2040f0b0d081c020708030604020706060e0c18030a021005070302070e0a0507080a050601270306050a05160215040b040206071209090b0306090a0209040318060e01031b0c08030903040815 82
    0x2500d0b03c007012406030840190a220b030410004407949000d50041807007d20600000a4451303d0f403242d035000000c11220304003445000181200c034902c0500745101441c00440060200d00c001c0d50110303c0c090041500700040c0b010100b110810907009120b404041c11680008207001d150554241c800b521003540d48002049040010807480c01440c001d2520510043c3c54146c11520280001144c070300000c51469000744c02c94101000040c1c6901556001d8200941e0110b01800c04d0034045848500109118056600c0f02000142081c0222045036105400c0480342a1966980c004140e080c4241d80c1d0040c22904400b10000754250841c0269040d6803044a0400041c0ba01409041e0745020a0344d40c04111b622000340e02c8010b14100c0d4030160b005100c2e103810042407503501c01d9a081c04425070413203404115065921980c0c1c0d41c0c544a02141c61501d00075002c6070450800c000340240c2600c80028140700d40008c006401910200110350042803900304440d00d104001841a1060302d00707480243e9072100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 241043444 1250 241042194 241042237
    0x1003030e04200906310f061718030a08090c040902090f130803070309050d030207030503150303210f0109020301030c060c05071d0406050106050c0a02040f0b0d08 71
    0x5191060300d90900351418101d40c4601d90140d0422660040d03050fa44c3e11410802c20b1000c03020700389400c0c040444030820240800c031400314003418140c0d0b4603006254010394815081100c1540420000b0006d841c02d0640030150704c6582c45c07844008050140e42450340700000da815621030307008055511a10000065030306a002d008100002d55904050207540103290381c010449541e2402071003504100e0881c0e8041c48032800390349420345a041110300300046070781c0d151000207010040c03045041d0040c140ca011864070744103503009042408041e103000e940f06100e2060140d1034400308107c034240141000501c0890508840000d07400c142110305100100348c807400001c00d026640241c0381038aa00600780d810050400c003085429080301102034800b403182c0c0e0350000303e1400c3e04003d0310f9940c400c900189520f141c01e003480d10654030181e02c0a0701f00f2004012401000d00d0210b1511245a03044a0105620320441e10090280c00a040840e0303000b1002101c0d81c04000e04400204600b40413050048560702 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 241044694 1250 241043444 241043449
    0x1e061b2609030703030203060a05120708061e13050f12090a090606020c0105031f090c1d1f020a1205041a09090a05040204090f050610050a080304060c0c08061003030e 73
    0xc00540d24610558024040710303000a0081e000f40d80d00210103080984481d43e80c1c800558145500c0489400b0b5070040310040c420280c05002d45036000c9010241c4400c01d090602251030240c000400205450041f2107407107080040621030000301140d0f0344116403d600f038100442020f40c1c8408420340c8102403510001071400310f50f000e0035044640c15005000ca240c1d04d04015070f0203900040071a03445940c1801910502081880c8100140c6198880010300002c3c90f40d0181880d03400c2102c0d060740c1c80c00601214896595481400303861000c9260708e003103102d800703030007a0f14211001e200184403a8494082410103940100600101c42803061100c1c80404001014400c03407142c1110325400c5590100001c4c2083e03410381110360860301c080d00020b6900c8035030b2101e6003007860400702240d00b44c0102c0f09101e00c280c1003a0360310024001c1156040d864600d07101403a0740da481184114001e2026805011080c000c243c2e01400003004180148e801e5440c1c40741e82001f10060303c0c00708402146000d000c040860 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 241045944 1250 241044694 241044767
    0x90d0e180109021c09030224061f02100216020108070c05060a09020a0305010510030b09010b010e04330905010617061e06070f05010c0c1e061b 63
    0x6410314050098903420421450701a42c040302400b400780700740b0f00a120350070b4814440c0f11010342c00303075001c1c0c030001942518141a4a904400c032004400807a014040250790705a900b20120710900302d61a03055218460690400501c2c03461074060901c04210030000080b0600b1190382c16100740e885e07113910f40d19200140d6220459200c054500c1e0b1000c0000b0700ca004095211019081c00203054036182a0703a9a40d440c00e481089800f941a4030084004104120102d503a50760400190300003400001c5000000808250003500e6003441141c440e100707034140c01d090b40c40400078503210b8204508144d0041c00e0602c5007804510400451500d0000001041407240550b03019000d0400340c2041d00391903a4040114450740b00c184011103000c3c06080101c1e955442e0000c6c48a107200b01c049110700500382c01c0860850700b0001188003400980080800042c580900013242904c501422061031071141c100034004029100b50742c00c15002010141102c141c00104a080c645580601d080d01c1d8503c910320340700324 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 241047194 1250 241045944 241045969
    0x712140402040e01150e070c0f1101080601110a0204020d0b33090a0b090102070e0a320106120b060f0d0c0f02060a0f02130303050c10020405060301260105090d0e 71
    0x70f0360802403d01c026a2220b00c11b0360000c801e4641744400c0b01140d11480a41d0070304d0340c821203207500020a003d90300d582000101c0d500280900741210b030006600402a100c0c01c140340000e105a500140000082000741d112524829001d442031012081300350806800021003031001030b552289864004010141404894006c031010780706200d064946407174901c140c0c000180013030550003840300201e07417554180001486484629404544200841620404043c0001c203030f03d03050000044204610200045550465100740f6101100300c00510381300300100b030760542c5690b02c030400280d440f0311414090f01414410560740b50800c41002104400c0d10f100d41c650031850003503003209000400301559035000003414521128094604445440f040c010625946c2044000c00c0c0d003c82ca00c480030504124840040c2c1403d00114030305420307e40003c43c43d000510410303410003158400103074240003905010b410200791200a10160030146001d5460781d484401e880c1c00a1070503125501d0a151200d0703841c19 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 241048444 1250 241047194 241047221
    0x180f020f0a36050d063801090b0f09031204061211030f04020616050a0804080d0801060507020402070602160b090f0706080606030702190b010305151e0712140402040e01 74
    0x200b46141c5030610001c0c0b2200c0001359480c0d03680d542d10740d404450890070513a482c8080404607080001d00108600d0b00c00ca0003c55a040003600c403004d01508041d6000c40e0255201d800481d82c40d120140c000074600400901201640d0802203800034120740c100c4242c6661140752981400400741004040b09507020480c0e40045503031300030001c02d0260030502c005001000076402d2244107c00325450341c0d8640303200c00000b11807513140040c04002100051014020042c2607213884e906075454064000c203203005052020703120300e5000440804011003a0b049421440700c0c0444811940350504141d600c07540308498812007400307149100c40e4003010206400080d6890384d241e581881e11401e042c00b64582000b00164254070503c0350301b9107190004070021104601c44c210180c115815032400904040c1203880b03041d6400144403d2040001d01c05030012502c100f00030000e629965480b104840403103500c00800701e40761502d2420740c00c40e00c1013035849100f00e0017640d040c8080780d98210310500b00c80c0065198035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 241049694 1250 241048444 241048547
    0xc0601091b0c02011202070302060f0a060503070324050a0b1306051c0510020f1c0506100f03060f0f060905090609010b0a030b130903020607020601180f020f0a 70
    0x9032920300603000001d02da0b00601d48103030004d40611134001260b202c1ca03800d4000d80d0150003080458640c40c61055031064250900788405440c100100742d45100030700008214204d407102c4658500900a0310f65410004124140700c1801c103018488020300b0902402d070f0007031410004405030303100310703010f580b04603100580030b5410403903005109c0400d080e018000b12001c1c01500e407000e044984a0016162401c02564a0f9a0740c0d00d81401524945074042010412141824208441c41d540c01e66000110403c9080c6100002c400341c3e000c030024035554100d00d80714a0b000d00301081c0400c41e105904156146601c40880c0180c40d103080180d00b00c0d08486450b03100346140c0c014004000d148019040f040910f040224115040364000746414205441020200c0e90301c503d00300c04c3c59410884a0340204286c0060100340d41040d204207103131400c1081c4110103546560b030140c800c0180c0e904448280d0b000c041d0304c0d42c40e8410080c008104281c513443c0c00080c19501114202e00590510280103001c040c500141c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 241050944 1250 241049694 241049741
    0xb1306030c09020d150b0405180103050a030c050f0601030c06230a05090630160807200303010e070f02060106020304030b04030c080705070807060e031005090c030706050c060109 78
    0x207011350f0000300b6a0b190540c82d90001040c1103403a102e507602030305d407000c0e443d911182130a050009801345c01d400c26180580b11401000032030301c045030f68015150585443d5001341804d081a5103018062008840705100d038200001c14092054561806d4580c650744c3c402c001c04d8031302c024042010b007a0f10b8403414944100314444102d8003500041103240c41c082d04c42801c00340c0c81401c0c212078051b50000200246005550042844001c0c0b20041d48605c000900c007078020402000105044002001c036000d224036000c0040c02816015082011031404504580e580e41c1c60382242c501801041d04e40c41c000ca040c01c0b60314407085001003065410b0f036074181e00850410346152a03502540c14083c3c001e074140408100d291010407520301c02801003d002d40024441c003441c00721000d00c1d109465100c0f400700a071034094005655004030704078401c03808000707010850791035107000d81d0f041c4925440c0075981881195000124a0b8104c409007880c06210070a556885c0c0ea40e03c6940103441c04651031a10310003015100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 241052194 1250 241050944 241050959
    0x213050906010207170601031712180f070909060605030c010203030705130b04060f1211040909050f06100e15131d01060b121e0c0309010b060406030b1306030c 70
    0x1a07900c10414070456854980d541201c2c10403512039600d070882070b04080014803d10030515924401c107000340da44c0da4030b41542290340703102910001d84042c9441c88200045960200100090b510000aa40550310800d65501303031900204100f0348120b80b02c070302f0104009100e00c1c012031940da28050680107140b95a1703a07294200c4e810740c482c0801002080c401000415640c500b100600041d00e201d840e0714000030640b81c4040c20a0841070030180780c0c903007460b04a194140035041907904840d200040801e00303265503c0c280342010b40c03d1004100500c680360800c240d0f88907180d0343d0340c110b030030ba1100101c0719110458004415244c0d002450307007121201e20001c1c020aa0703548202c006864000c2c002c001310503480200c2d804d44e4015030011344a803038042004403080401640c100c0d00440c100c0d103c035414005100e681104e041d4010b1000a50700e90100005811b46001c1d00051041d100c000e0040d1340da80d844540250007000480c4001d400356044020f007000c810924071981e800d8a8210300c0030b401040c6009203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 241053444 1250 241052194 241052209
    0xa0323010f12140715031a0f130b090705090a0602010c08191e0f06060c0c0504050405122205010314060f03030906030411121504030e0d051f0f021305 66
    0x2e0840d0048410500c203450101c0910001014040c1402403039602442200700030152000845490f45c0c0d4030750740d4041c0c0819582e84c2d6105180c040c00b600c00d40c0d111980124524020320b4804444c82c0c0105131201007103401c5a000d0000c001503501100c1071440c464640c1c5080f070803180d4801c0040d000c00c01c5000403d1561804945606000e45900c40c045103012403007a0520b0700c1070441d0145100ca0703481d402c0c0c42d0702c5400a80225000360006160070785c800300641c2c440e104505001e2003024019503070307003012900307120041c804503410061140c01290f50b910700c010400400707208540c0075090143d03a15400f06144d0302c40e005949407100c0801c02041182c44841c20007410030041c11203c0d925100400250341c242c5c4549000d18480c90040c040310303078000740140500045000007034001c4100c0d04050326207000f10b00e42d442c1035a001601403610303c410500500c0800c286400c441805000c078412407580e503103484081000c000d2028044507090007001440f65007a0203070300034124003e4240f1510350b4140000e08021a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 241054694 1250 241053444 241053479
    0x2502030717101805030a0c02090a090b180705060403080c060105010f0e0907050c0f0f0d0521090304050409080304030905040e12031909050d090e070e010c05010609020a0323010f 78
    0x282c00c40e000c0c0d12503440d14607517400901c1c8000170640c640d0f00348056141c49c44440c0e600c0300d4403c2c000e10500c41180d680007a1f10324000c007410500741e10f540b04411180700c100171942c040d00d40500407540e52503c3e03040114854000120040e51032080000100e49075124603a4441240501c0e101c0030940d0490100b000014030000707000318200801402a620201c400300203003010100d038003010308150314007050420704119500c4064424000c08110300112485101c400049105c1071150250040d11034895407030661150351301041c0d1060404400c0814800101c0c01940120b00ca43c5486031096920404d002c2600c43c561b03102149900032480e04030039051b4403002181d104c0b51b140301007200c1e14071154004c0101d41d4055426210755014502643e4006e81003018000038080c500884262032500c41c1c0001c15220350340030f241c0d041001b1040b0b10802c00c02d00750410009041c0740c24081d91110040c150050007070184403284880e0003171060440502d41200c2000c107040c1c4480d000d1010540d13080c64a91014102140d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 241055944 1250 241054694 241054721
    0x4050f120f010507120608030c15040c050607060608151b0904090807080c070e10030303390201060501030e120a090f150e0f010e01080705250203071710 67
    0x202400301c03000784100c0d8891011038403030b0b400403002e82c0400c1003240c0d00c903000006541c1c0200005c055500e00010213005208150710919041c2e561841e012092072590784c02a03402c0305020503040304100c4242c000005031095402122911044d408000c060220141c0da007600303802150b803000180c0e03001c0000500742514060004030f10790040360f81700301e6146d00884d000e844840b008584044080700611902c4014841b040c00e403150342c28003c0e40c0c024241c0452000600381030740c51420b41000c507a035407070481e140c41095007082000c07068804c0729100b10342d00e201d40c0780c0103528140020481d9030107072003001c507268010001070103003c00d004400f6150781e009640243c1840713a4020001a9000c0100d031030000b901452a85440c411100200903005000c2c0840342c501c288003200c44035865991220301581669001d28041180782c0f40c0b0f4009540c1c0c0d20801208031483c014500d84142c45098005049011707a100741c00b00d400c0940c0c0c800300c3d4201c80d00411640d40585d0492802d40e00c0300c18241c0c100309001c1041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 241057194 1250 241055944 241055953
    0x108090309190311180c03270f06100308031503010e120903160509040f1704080601080c0307080d080c0f030123060406120f02070b0124020304050f12 66
    0x1003400158026407007200c1d0306200c0c081550107004001c650f614a60b004441510301401d03640904074582c0415000800c8000741010100c0042d0034140c84040380380702d41c401d140441094023803030b80100381c480244441c0c490180c0f1605010804a4040c0b086c0c2d40f00701c0340c1016545085458541164000110f0700089940c90340d01d881000e412000c0034001d44108402100f409541c1d0f910700000e160400d00d002c0c04400c20f50710011810001900c40e00329080d4050f43c0810482100e849030714041d802401011060002c0030f10100d404640ca0000065560507100c807081150392040c42c04040503a40d00c040c1c05007400716040803031210100c0e801090103940012a100205080ca00b541a100d04160001d070310049548503210701c2e420b40c1c000f1219a0180504090318094502400d01d00050620756100413134580041d60780386030a07460f21980d030588083c558050384828040d40c0d60303001410060050030780c000340c41c42c60103880c003207060000046408480024240140f46080c0c001041407040c824016400c50f03005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 241058444 1250 241057194 241057207
    0x4061b0c060b12030c060a05070806010c0204050613020c0307060e03030402100f090b0d0507030507030603030509060a18030b0403080c070c0314010f0c03052a040504020f0c030313120e0a0501080903 87
    0x10604c090003800790080000c1405181000d20042500c41c060300310b1051140040500501e0b903800450000d04980507075000c901078461001140150b18040b115125551021405900050000c00181141e42c0548000c0c41380100c1320407980e071648810f0b17500940c00110b14040c00d1100f4014011405400042d0500c403840540c3c1d12100d0fa0302e80d004118081c200c5580d1010494915014801c3d503070001b6142c40c04200041c03c60b40d02408c2445401d40d0340d4800c000c04030703141c0304180c49100c2c4032000305001a1041274a99403454000c500c1802a5812004112020005440000b012098034041d0741c01250210615240d80c0718100602c1c4040011a00c0395240c00c0e0064010f8054004c6081c0007000341e80025052520f26202844a1628003407900c061490b04800c1415005c80c006440513580704031401a9210209200300c1582d01c20b0829900391400040100a000c54141e440b081c0070342d0140708a51102c00820100710f40d0061302c851025071000307120509220b42e51142c20302680c13042815048904e03211 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 241059694 1250 241058444 241058479
    0x16210302030d0e0105010314030a200f01110309060708040f02010e04090f05061605070804050f040204050d060b150301240306120c031205130b0702030c060d0504061b0c060b 76
    0x402c0c9107403c89007a91100c0040041041e8040c11501040b6075201139400c210307807030000074042c1030b002c010403002c0311003c0c3c140c076428001402485540ba003504000c00140b81414600d4070190800c07101d001103405018001103d05028840d042e100380c1d440710107910519402d90055441085007000141c00558440c0d0a000040d0b8540c005886140102d00a280f58036100780012030401c070120500e41080400c2c003003100081c4012043e1002d0314000c4842c0481d403d0302c42c020030b009000f16840f0310340c014400d202a40501032640c0c4008146072050340c03588000b0f01e0f5441c200c07010344000c4c480d43c1562240074009080300c624142010004040e24500402c80c2c03903841840110180800380155001c01600c1c108100300b010320f90350281e5074012030400e5030815a580001e1401c920300e510810300c440c000050305600b19902070202c4d02c0000802000161900c402416a600070f02d0200c9049a003545082d00c01804926080b200b014407255581d1204400401555510060b1002c08501c2e608081204014040300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 241060944 1250 241059694 241059701
    0x30f1701030506091b100c08070b01060503150a030f08090a1503021b0d09120f062d0506060405040b06090402040909150903141c05041416210302030d 66
    0x7180a140107100d107080203202103007054a8011000ca044c001c00404016980382c01600c03c01200d8641006820540e040c1040c00d02131007030100081c003441e103031000440d602d5000b030003031406500003402c044c25080354442400381121040c0402f519580080f21034900040c0041c0080440942c0070303094200c03143da51080105024401060100401d402041000f50a40411071100c000d1801c040204514104454003521140250140709015050042c103030f41031050341002003080346e60000040000c0b40301c00c2088449040b4804c9604140402401000403800d000e000d498020b4000800080c60986090100802800d5480b405500094180300c8e84a51f5542c5202503c010f103140b10000c20b0f40001d80c508020741030004094281440e207098621000700e076009891050803101d01802c1565001003c80035540782070703140b038000b41d214100000c20041085444484800c100364008882725500110700d00300d94580e1500480c0d0725007403080f9080c1144099092041e1a803400b90060340d00d011401017101098 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 241062194 1250 241060944 241060949
    0xa09180b03120c010c08040c0501030509031c0b100c0b060f040b04050103230a03050d0203040807050f0c0306010f080307060b0f091305160e0a05270601031101020304030f030f1701 79
    0x2001c2c4040390384001d08000707020700491000710f841c0c1000c3c1850070340d848002140c910b0240c541055034940004221200403c01c031540102003d8010300360350841000940504480d1008500681a10002a582d24041c010742c00c80302d54090518091075072941c0a00191240d02588281c0c1b081c0c60300c1285040c2e8039a80319090185006c0c0503008001040461112080007000ca540141c5a00c640d0443c800b080d403190503101c03554003000001d65641c40d24149824130f4090042d0240003805a40001100e000000844881e018000d4042d0f4042d070380e071104804c150100f035100300012034004111080c0000c4940e40900d8000b0401811060b2001c01038001c15a0762908869807410f8000031aa00c4051140410180218810090059040c5420700210b2804180080c2c42c40d1106c9440c3d0021400900c1d081d2050511014400079501000903c481559a20708080c0703c10b40d150071000075084c4070381d403011040740d00f942d4000270f1400907190b40350b0301110412240c0072400700300b10000611203184001c0802c0a0b00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 241063444 1250 241062194 241062223
    0x705040e0616090e0c0a050d0203090309040e010501081e0109061401060306050906010f0e1f0f080603190b04030e030a0809040e1609020912030307021507050a09180b03 74
    0x725450a410780311004400b09482105002c0807480030401a0303402c02d20b082d8411182c0d4882d07a100c000c03041058640303000d009111701070035001000300084207200102814060030101d50900003541002030060072108207020710710075900451680c0a80b82200f103101d458415100d0000100283e00d07403180300803a15622006640d54010b0001000445c3c0d040c021000070705822642d60721641401c02c00a41600e166400382c0080c094603400c0701c1c0007980c85030340440c0310440c09032000740003a80e040c00c020440e005030071103040410601000320341582000101500113090300f90840490680507241d0807a0050001c10480810401d030b4010381c1e054030305120310400c56120b01100c58071440200c0801c000c2d1082c1100b0030f411940454854401b0044494109003101d4603000010f82c3d8041c032a010403001d0851420f034464a1000006115a46900140c203c4a02012030084003403500c4800e0100c5083c82071141e008001420640b0500200300303100c1520080c644400300c001101400d250100303081c402e4074501441d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 241064694 1250 241063444 241063453
    0x607021206010e1006080a0b031005010f051305040c05060c1612150507020703170c01140f070824010912050d09060f020316020105071515060e010e120705040e 70
    0x700104561043e550401042c03404600c0a5045c13010050002100404403c4025100c6412030003585092203104883c040c034a00a201c25a158411500400d56a22519020740d83c3c24040941046541c81198055584400d0f07000200345007508114071900140c0c0c400c000c5000d8250300d04031b850541d0380080300030044601c1064103d121814204c206006e002d80c1900300600f407004110780b80d0717070100d103131010740ea844032840a01c0102c02c0ba960056000d0010544404e42c07030b2604258070200001c104a105480041c08010350b0f6031030a034200d8444606440301d90040303c2804280c8800c88074140110b000d504189885441c00b599040c5610983d006079006458030342000000c407001d0399100c0d04c58000342029040020000c40e02d00c038003e65034400c2c0c5481444044041115004581c4940100ca003080d400c00ea2044a100c0f880025074014660801561401e000d203400c001013040c041c40c0c0b0244990b505855600c0403003040e800703108104070b0118440495018146000c5115035992158440c4244082c0081 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 241065944 1250 241064694 241064699
    0x60f1d0703020f04020c06070c05012c0c010c1a04050c04060605030603070e060d030c1109161d01080117100f0b1809031e040f0902030a140402100e060702120601 71
    0x10400f000840c48450146004001296110900080c96500000e107450440c190070340b981050b90040008109010700840800c40c404800d0712407030a00401074541e8015035a10320240001900d9600400d10001c0120883c070701c90b0f0401c0c600c81500d07141d025008a043d24100000040010111074090f005600130030800300030f01000741020004a0068203840e01d5010803803c0490015440071400d01000742000b0f03155103c139080240c1d10326800703440f1030007a08c40000c608180c81c0003012009100c0042c000100380d070f26040b10780005902410000001a1110503041e400c0c072041c5625a07c440c00f442000f1302c00c1007082c2c0340040061140c954015441100026802c0312141044140b0584000c04d42c10404410140101c1c18004012203404148802050141e240c0c4000f0240850140d41c1c031a40c002907000c0780000e54040c1d80d800031031041c0302a50040203001c0702041d503c81c419409640103500280c0f02d2003590704550056103d000d01881c01400641405555400038104140b41c0508072050f405c0b00004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 241067194 1250 241065944 241065949
    0x19020c012904090503030c0c0304150504150302180d050a0b0a0b1302030108100207021807030213270b130e1518030304030e061903060e010807060c060f1d070302 71
    0x100c070000c0112401c1c4203240c4103481d0160790380006420761420040001701c212003040d0800842e030082c2800307214007601c6507000102030040d40141c8212404660381e132048011184c1309100300c54403240b40d2070404c13020b07060385000c2c006400d20a0000700c42030b100d60201c07d070202e948807042511902800c1400b040011000701400004109400c082b0302560040c4014480044086069020003280e0b05006840d28040d000050b450382c0030304d03400818000103409000d82c556040d0020418440307602a06d9496a40d900c03103502c94150080842804a0b402800014600240c0d8000c4032060307031300500c0009000f488a088404440802120702042d5111103207980041105c41c600c0c42d4088491410381d01d01d1402114640d4503840000e100400b00015200010456517441096031120382c0281514546244100805402814240111a41070a9080002070394450014101d820388400c1d40c0c44481200c0d603030391840d000e04801d040008049032900c24882d448001c0c00c000d03410030250a0000c15200d0300d035006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 241068444 1250 241067194 241067261
    0xf0903030b0a030f0f02032a100e030c040c050c07080f0607030915050c120a020309060129030606041203050406090e0c03010605071505281419020c01 66
    0x81e418002ca040d642c042021503035940c01000210b03044808103401e005d080c0300007800d01c1e00000d03142030285a008400101c40200c140001500a02070300e14040c1440c0c01d100a4500c958000780340c9038140e020b944590500d042c682c1003680041654100071307080058008000741021356a030441d80150307000307440400d5009001c015080e000b00c2d060408000030000d81d20b41e01d078810f6959100342c4401c1d440e407001c83c40e4164841d04940c901c461410700003800b420040c2112020390b00c203132100c0e0f4051007203074000300340c4a10340d1f507201d12400c03001020400d806000800c040c1d80c40d04014203055200d1700c244000a101c1102c0485054158442d6441ca5622420507602615101e4a5008003e4030304404040250307850400ac100c905460322400c00d1501d403030a516101c01c180e031141c00031240681c10203061202007400b40c42d00004000044181e0110030502c1c580540880301c8519030440c40e200d034800881ca002c80442c20b0a10f00080248015107070100070205107003996070325a92b03100d410744c1c400341407800380d0407040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 241069694 1250 241068444 241068461
    0x2060a060605031609080a0c080d020606030d03090606080303010b19260910060b0d0627090f0507151b020907120207150f050709030b0c0f0d0f090303 66
    0x1042003014605284004010b030000402042107030f40e060b40302c20740b65809110800000c01c40142201c04001c03040c80e100340142c0b0144600b0625205100400c12042e002082e603e1280d44007030001c00b03070a1401c17079044010f42a00c40094802607520500400c1041c0103100640c040c2170304283c0d86648000e440301c40301c455403c0c00703220020003185103901c1c501c1c81080e201000e401c501100030503895884d101410350414040e4442a90f03110f19140c80000d164940c4005041105800da2007041050381e50b00070134502c0f10f44070391540c1c0065180d11588a043c01c480e406454000c0c00b452150398581003e030f684030714007402508071101c1c8080c940c8403820482c0d400700000c1d401709019441c458a11f035040e400300340c0a64002d0445024081500321000800700c00b903050314000780d00000c1c00c400b4120040024001490f4a03100781f841a400d080009814500668120048a500084040f480e56070140006c004d60054034100b1040c13181007085801001060044170045040680f0000708056240340c00b03012101c004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 241070944 1250 241069694 241069711
    0x50306220608100e06071b12030b0303030406150b07150203100b0c03030105030714010518040b1302070606060804050318010c02060c010c1101051e0402041805061b07020a0510020705040501080d0206 87
    0x1087c1100d511055414040119a4000d8501003170314003402c010b030080d120f0600e501c5d800d440302004100074490650400d1402c0b029003004215610703107c00c001d00b010b01c00e142e0060407409110003041002c2c00941d00541e0b000c2c1107000a0701d0426124038082c0995404444450103c1e130000c80180001d14041c40b00b00c0c010b01d044640c0650a00c680c0c070010380140900307030b0007004800903429010100d40f2290404200c0d01c400420524810702640d06e03500007504511720030742d12039250501c0072800a02510070103010303e070000000c41c00d000000c2d19510080441002c694104441c41070702c000141c80e108068070000d8180000030940075804400180a07040088401c0c505a0402d410b202c0154461050180c00c0c1011019401290756140003040180190420048050804072010f0301401008030301a8000e035400c640c0c0105400d000c0c0b0800c21107001c0d50743c000e50300c8840f50701d00304000e20784000c243c0d07a00141801a1052295903c00090841c1e200f40e220079503c0d0401d45481640a6041c01582d40c0130980 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 241072194 1250 241070944 241070957
    0x1030513020f0102151003051005010503120f040b0f0d0506031c0e0a1a0405010f0e011403070309120207050f0402032e03050303160906050306220608100e0607 70
    0x1405918031051503100e01030300a01c0741c070b00320526607442400403a040c007509050f005554107011880d024696028442902c1c01d02590344a20200c03200d6015050484000500402c20048a98072142807540700421180c1020070820000440302c49400c00341c500d08141c09059034842d030401002100795080146000d103c0c2c3c1200c141c0f4015200600d01071070402240d07241812081039420b01046c580341142e007020b0464031101341c4150070800488018000e4410070307a9400310b03c0c00c0392035003941e000c0d0040e607101d80480d58131001c900f0380d1580c10300030b503603c07001505e0089542511511121528260000c5070310050b00002401e201a0520301c040078540c1106460452540c9402c20091280c3c04000b181600d240d006580c0303421000072000d9042003e1500441a65640c0c1081c3e003003406202030715101e003c0862a8500000b603840d00680550344103401c0603280c040f8449842d01031000e030030000c040986200d5500e500220b0502d00c20043d140340203c050300002103000618843c1403824500908031010005c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 241073444 1250 241072194 241072201
    0xe0406020403020a0b090d14010902030604050d03230106120b0d051b061e07030c0515070e04060803090d030909020a081512100504030519020604020108010b040609030f0807020d03080a0b010305 85
    0x4840c0c800009041e0052300c1c1c441c2190034206502c0c0941070150300a545131080b0001e000600c100402c4ca814140d11684040060180c1616043d0344400b801e065524400c03095801001124041c00350815001080b140001c5e200400c040025544800700034182da49500c000301c005040b61400150700a45081140d465040c107440703060101c03800003c111030345000a404a0380204050083d089a801940e000c01aa030b050041d9036400705080508440b64400079410b074100c103c00342460b100d550152644c0201540c0303401c0270081805a9004001800c07010040c807098000348041c218405403a84401543d00c02e0364600384210300e12109001800c038180b0580000c410307940550740001e1591055804110f01090360f59550400f51040d005480700c58598101c0900102052039011030700e0361150340300345caa00441da601c421402e101e41c059401000d0200b41d881c3c2c03081c03004c501d105085030308031442410014a0100d4135400f0071901c48607180200c0c0440d400d04140b000c0f5100d1030259102c0c00310207107020415440c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 241074694 1250 241073444 241073449
    0xe010b0d0f38041d1207150b011112040503010609020a080118150608040501051302010f051617070c1706190209090c03070306050906090612070e0406020403020a0b09 73
    0x5103031410250301e010009000d0b002040100307000200028008004010302c01e40000301000c60b0004030b8a4607414004e8a00c502c881d00700e601c00740c9131490381000702420740944103000400140700b100e0104e414004044020b000d84201040384940d0003811003002a201e500c2c180034075003540e22542040340c10070b0040c482c0c1c512035544a040c890455203003c0203000c41c081050500002044103180d0810203916000021480716008251030303011b548500000c215541d02d4030102e440940207000001e0000300300c1c40c0b0307040e60284100094035200c84101100e44903406c1540d580d48903c030702c2031107102141c400031411a0620510140e52002000c102c0d12038443c4549407080b2036200d04000340381d0314008190180d4051038907103580c196000e607040036000e108281014502240386400807601240060300f4890003080368201141504c1c0035800142aa800d03a84a800c2004004402000b45081d5032040090019000c2c08040ea01400b46004944c0141c3c0c40c2c1c214014042042e81d603400801300340c80c4c204110300c0d098 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 241075944 1250 241074694 241074731
    0xa0e060a0f0b0f060327030f07030f180b0a1106010807080f030c030906070c09050f0a1d0709020a0c0c030c0608010f0506091207090204090f140105090408070204060e010b0d0f 77
    0x20280101e81c0c49040406c1283ca486002031000080d210320011484400d84a00c040003400da041c003940f1038407219213403608102d902a070b5506e030040b81c2031500001004050b40d4000500f0710461070b41002030012101100722032418800340c0c000308207a40600c0d4108400101404020b101c4a5610080c52428030159502543ca101c1c1c00c4846010f003000065050070305c503407040800054407041000f07110500308060801903040c0103644405050340f0301144031030403003001e04064810b0081a0054580c05d4a03000d0200001d4118640660610502c103500d80300084001c450080503505c1210019030440c20b214000b011400160000d0921010849045c02607541d07482c1600c0408004440611180b0280c080050810409900088115002082c04500e564598000e80c96002c00c0800401c015020403101902c401d00038440c0c0c0740c01c05400404607010515800c020810240040c10104000ea6201c0041c1c14040c000d80c03007419880d902158803a41402980110134005d125280184081c410900e460800d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 241077194 1250 241075944 241075951
    0x302060708060d02090406050708070203130504150302030601060203120604020313080c1c02100b04051506030406090210031407080403050417070503010603030201150b03070c0b0a0e060a0f0b0f0603 87
    0xa1081d24800201d0982d42ca4a2000d5030a80c05400c3d002ca41c1414078000005e04004d0f5190303804503a2940c005900c0900c0002070b110348500f40c4580d110114a05000c2c04000c101c1700d61074102c100700308a00031025031410003509008140a500440e41d5101c1440705241c280800b82406100364010401d1007075421000718200084c0b500719441c5036407070704400303882450041c15280041c801c1e080303d158407240f01d401040b44400b803c0179140c113100b00044c0504200c2219000c88114259031285118dc080d0b5003850000b55038403030310952000411000e181c000031100d02d149100c00b0002034036645c07121400d244d0100440d401080901b0a0301c490b0900c1e0b41c000e4001d000d507010360005da08244030340c01c1c004034003001228010b0001038000c002c8180c40c0d090081c0030309410019a56181c034000070010b1500d80003403c80e0302c030b440c1a82d03076489a0022540c0300d15450340060509140309403141e0110160210521040b800741610000005070480c42c1c41607442170355089405103100b408a00c0340e0200d1501d034041203da2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 241078444 1250 241077194 241077197
    0xf05010327140f030f041418040f020a090c12050c0d0612120f120c030207021c1203110d1d03030f010315060501020a0f2d12050703020607 61
    0x814a10941c07041c0000c2100d0000c0c2040490429074103020302501000300112074000e0010303a030340c4200f421900d940c0c0744160164060810030400c4100100824808244280c0000901402c1e4841d03104020f03209850090b60203036150080d44c44c41408500c0e042361908000c1048200c18402101840406407400300308140d000180c94035000000c174400c424000704d64032840c080320100811522100040180c2c2400c850849004000044038140ca80c09044240c40c440b000c0d41d504a49042c1c222101400f03042d510956405140d001e02140e80165941e5074150321000c07104031241401003803800e004040190007104402458a0070a09100d4807808404035080007080700b50104a8280c52081c10a1001c20009a401c82d40004002e0116010001a4080c100c0b8020300b2409001c1203585034210403140903104aa0150344042c10358400602015600c1c18071a0003042c101c0c00da0070440d2280004401508100d10000900c00c450318108502c560007064460902d2502600b056800c2c0e8000e90b0703409001d840e240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 241079694 1250 241078444 241078451
    0x250e0103020904090c03050c2e140c0c010f09060e1c061e1401120204050a061701020904180b01031403044101020d050c03070606060806090c03010f050103 68
    0x559000350111014540c2c0078200700114015030904820700d03d49400101c601d8029a440ea03246031800461190480080c0e01444511885031685036140b0003000e403055041c402110f90706c0108003610030181000e0140c14024001c0c0b5003081c800184180c03070280b04071080c4500c000c2d085c45880d41c403181c5928030090540720020711081c0c449605101003183d100040c10941414171040020b004103a210540c1d00d000c0d50280300b8046c0c56410790081600c240a60042c7c1c6955110201c00340ca8250012070b089030481c4000030b82c0548612154a07141d0300c2c1c05071000160b4001034130300b03414101489034440524454549401d44107607541ca0816949040c400a08140c04000b18001804400c1c411280100f90146040820b02510a80d0905801700c40643d008050b04601e40c4a1445603035040d20a60154140d014241c0c0c0c0d181e07520250750070341095072103110f01d1000f407180300002026803140c040034140d50340fa01e0505240c9041040952080285510201ca406000400100245030700320015140c003401c010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 241080944 1250 241079694 241079717
    0x80105040923070e0903070b0a0504080c0d0f091a07080a14031302092d0a060503070e18031602060d0902061303050616021504022e0825 60
    0x780e10121040040030324900c0b640c984a14155000078801d01180d43d64501d010307050f40c500c2846034490080c0400a82800302650020310711100d541d102c558801c0c41011a1401d006000f01c265145c00d140850700800300701c1c2003001080305034101100da0000d040c09110614122140d04c68010035008014000701100c00c0440d4810300e51340a0f02160f0a0131040403420f9443e40750443c0304c3c110001016100b6405402c03041d000c2000001c080d000205c19031200801e03000c0440d50402c2000f04208010074000001740c1d80e440100d40d5079014401c460041c10a160103041b1030909000e400c440c452614501d0f44158400c22000e044c24250f0542c080072690101d4113161184144007280c005807650308402540410002000c0580c94030040e92001035034003410841300d10790340e1412079240f44160344030082c0242e44940d201c4c05000341170040440c0d1061018100c01d45010300b0014100c08503220b400b0042d102c50701c003c8011030441d03010a070141d01449420510200f80c400c802c4e0038285000c07101c00c070004c002e900d0090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 241082194 1250 241080944 241080953
    0xa02060a20010b040c03020403030806091503010f05100807030b01060f210f151202060f0909180d020303010b03072f070608060607080324030303040b06010e100801050409 75
    0x106407504084804524414801521940c0240503070f0a0480c8190b05c0d00c900c603e000c2e0300ca4420380c2c1c1540c0e03050720f82c000180c5030401003203d1070800810350124803590703401d1509252003e00600e07800350403000c400306180c2089040700d221544660004105c541c000ca0042000c111100040e5044440360b0030306001035062501c0846040001c841c5003260b03100c0c1642c4802c108160355101e0800c88084100822100404441c0f40300c641c5e1441c401c070940b0004008001c0090f18002c1d000385843e080c4d59115920b807a16410214003841c0040b04d2090451850760f8070512074440501c00c1201c1420301e803001e9413640d0304180a01000b408040e00b03400c10000d421031300d41002c0d4106400383e140d0620080e400d502e100c00d18286a541c0f10300c1030050000080e60b075404a401d90030320340142d505456000f0046410b656410125171074864402111800c0002800c1a8a040d030f01c081c001940280d010b842480d8061801200151429a20040090045560000c0c0003810740c0e000020a0669030200c90110300c10200b03007003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 241083444 1250 241082194 241082207
    0x62c04060e1615080601020d12020706060e0103020909120d020703210203270c0f03030706090804090515012007090204081605030706080103062a0201090308090f0a02060a 75
    0x1014903042c4116525440c0d650048000304003101c1030180c0040140fa02c41d48119030000e000c1e564a400745e48841e45500c0031600816240f00c403008521001800d0400e140c81c0c1c2801e560707060f030045485d10725a400610545c24620742c02c039405800701001780000401c508001c10b5034802c2e2420b6400265011800000701482112103524050340e0070001142041810a606c00a60060381c02c2e80264521f003062082e40c0141d00c841d0001c003800c0b80050001010b5840601c28074041c3d24490f603516003c00c021500000701c3c28820440e94034000c242d0300d0b44807414442c1807821100007900240c00511505540d9001c1d0703074480700442c02403030b000461044111012280c6031800903070380c0044540600204000c01e00d00d20008481613036030103a0819004031607943c4141070312111076000d002d00007403c44006002044198001c010b18446211000107030580c0c07110b0150352800d10090002c01070351170b195100d0034151301c40e10b40307034206400b071000e00040c1c0d01c0c88039100d580d0501144001e000c2d64020800300d80c0c1900891 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 241084694 1250 241083444 241083461
    0x61d060409060b0402220503010c0e040e03040b0d0f0c0305130213020d11090a0506031e090a08070311060c04081f020708070b01171c08060307030c090609062c0406 72
    0x910171741d10380c0790640544989800141c00f10104586440d0001010324050083c0340300d5800c5515060f680030f40907002c5c000500030001d900c0c80c003440f04000010b00402400000c0076424007903040002d108100c005d5602c00d69110480607030800d42004240256007035090003151619a04952480700129010700c00006801814216020a0b150405020804140d41300600c4031a00486621158945030300401c41c1d98013040c0d80d0060036000300c598644060410ba03c0858010340d51108440b801c1005507035200c41e580c007402c0104c000411040c03080051362420445140c00034030a0340c000381803e052940e50b40c2e651103440b582810030f419070032955099001c1c43e41150101070f0040a02c40ea100c00c00c0c10000c2c0324010038801e80444032094014046800b50216061490a0748019003a149400d108800c407500c2c0005800c595042c044c8550000000c3c052026100003024511004209145890b001c0b40c12907038a507010600355401c51081000300754109100042d060400d1500c0480e646803418144001e12500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 241085944 1250 241084694 241084699
    0xd0f030c11100e070f080d120605090403120c0c02010f03020906040b0408061608070503061e040c030f0b061303121101020a020606040c0f08010b0f0705071404061d060409060b 77
    0x840b10a110030a4015056504540c0212504907580e1414484500228807541500d500040341c1081c410384030b0312001601c0d41100c900440c020f40c8890020b00601c000343d80407000301d240200b480b14825014000e0443c138202ea801c080d9280c10b101d4001900090460110350101a03001401e000c0d41d980e45002e403409449280142c3c0d88903a10345c0e03007143d503074031041c2d601c0361903140d00700590040f113807241450034403488844c0d46440c21502c50009200e191500303a01d1450035407409055405550700d03288140a510720160741c001c1440b44540403004202c6041d045100e006480c10012a44e01001d41130f0141e041381c6e13100380018072140700504d0445036403400404131130321540000340b0340b8401d99000454a020f1001128100120100a102a5505258002681d0100b000c10380104065030701e0310f01420452030f007a46d08a00c2c102e020754440b400c000c6160000c5941c1090200340d5146400d00d44960000f03060240100c8844400362412007048640061072188116140d950200401c242a005183c400d40003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 241087194 1250 241085944 241085953
    0x41505090f010203012306040b070206070311030a1d0d03091815090c18050d030804110409030903050c180a020901020c0d05011d060709060305041112030c07080d0f030c11 75
    0x440c6076040c4500c50144041026100e580001b910302d1030450308960844032030f000250f1820407035600307204090b0000c00c4140c0500410590066480300c040c001450b450300d256441c03511580c1c88018125800203903d9030940540740c0d860722600000c1d04a10703400203843c1c086810b540d03035102ca4820440034013103074000e869600005c06400600342e0000c2d04503031003000c0e03907840d641600c84907803100b1142410203108803540142041d40307180100c0c0c003030320100da0420b0054100002580380305011070103071010044200e0000b442007030200240402404006d0803410b085440c2c07202c1c0d13488400c0303a26880001608504500764001000c540e241c2c001c0103004100c075030203011041c1490160820a0003009076a49181d0b111044d088400380b903003408203c051244d040c503156200c166082007000c4006040c002d0044a21042030198080180d8400b4104d00500b40452700460b5101c00800140b420304000c0c0c1e00880c240d5101c8034102058940120112411882ca45400038810070752210444840b880e150514000e0b024 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 241088444 1250 241087194 241087199
    0x1110f16020d050706090803030c0f0a0e09011214030f1909051008090c0307050a12020d020d0b0429191b110705030c0d0602071433041505090f01020301 67
    0x401003044c0044807490385803000055951400262240f104492442c05410104034401e2402d41c000041c21040c100c902d4192442180707000480e82400b02a0000e018003107501400c0020090a05002081800d00070044c5040c440840d8001072540500c510980810400e840ea000040707104880300b100400c4000c10401520a04040103800b803002918250701500507248000d0050400007400000c83d0006042c4001c0c0c145002e41c005a000da4000c8104da00144081c0d4000242e5035200c0d4a03507400e4060400720a00741400d10f00308482c0c2080960103108107400c001c020b41c442054000300c507401030180b1a180600c0320300040b2900103002040711080b12031003842c1d1884c10b140d0302030401c50158160314116003240d80c580c800c2590741c3d16241660359000b11000342400025226401034080e8900c200d1050041300103d00c071460030b05a000150f407083c5046c1c5103d03c80003048011202c1701c0c210881119810711305007915400040070141c040200140d885030045111510204a04012030038240000c540f1f070358 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 241089694 1250 241088444 241088453
    0xe060612070c0201082508131a01060f09030503031513090c050306010603140a0c0201021c020a08010f050306060118081209130e0709090609080a05031801110f16020d 73
    0x10048000342d00285c440400070b81d511408400321104100341650740c242410038404215043c94008001c148588548200315001a99013848100030396103101481002e581001c40042060003803051420402c168048100040f907000704c100c1c0e40104c1002860000304403220b0102d08909480c00351480c600c2d207005081c03c144a5480074803419180d044040da10b250b641c6007021401c0d02d01c0002d42c21039280010010a4001070304c0d41c0480c03180a103500000d4180414191940c02e112514045218500d0700020100005640030105031301512090260050f000c2c10180425076401303000b001181400301c02a4a01d4912001142c03405c01441c4520440d5a2542401030b03140d01034010380c00fa103000c2c188180404040540501941001d000e08500a102151800f031050018185282080c0c500f04d40ea9086c1102017075038100140850366054848541c0c07404d14561807601d0802c41e540040c0b0f00c2c1d26210034119501882d104030303522480441c10f12925000103060508005020810003584400b00d10458410030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 241090944 1250 241089694 241089707
    0x30201090807150e010e2e0603150f060605040323030414010e0a030f080708120703060302030c030c10030b060405120604150908070b0c16051c09030c0e06061207 71
    0x85036160130303c00e00c0b80002d0010b082c1e03816108410160740100d041400c0c0c0c009490030b42d104032074041c00b032610300040034104001140c07103c0e041510005a101c9243c0800401401070602c2e03d44102c4d01048011310385000140b00e80254000145020300750084026911080b084070352855010740142ca07075880d910340f1aa05169054182c450110b980d10301070200501d04480e40c001103036003101a80c04c94024503550794a443d070080108481c01982400304240000011041c0380c0710300100e880016550707055004041c5403500590f01c2c20320a6000083d00302c0c2c1030300c4681030f84141200d07500340440d51031403c90004020340215045140c0109a0050039401c06000040c410300480c065403500a0550072969148283d408492001d00280b0003004040c00003090303992010707885220110040d0809840c500e1081c45454400b50a8400c0e90144494031034680c002c070300171281140e0038100f01807800c1c44d41d96041c0d501140307449a00c00b170040104c00504191034040441d800070b00c014515944c207240981029140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 241092194 1250 241090944 241090973
    0x20102030603070b0403020604060f1803120e031b090a0b0409080a14030103110d0c0302040510090e010b1e040b090a0e0d05071a09010608030a05040e060303030c0f07030201090807 79
    0x41e20400c00f0020744205000100ca080e0303500070780043d02d890304080d81580e2010070341d44c48070200401d610402d40d0103c030105440b0051481010301031040c1d0441c1800410b030944022a4902c660010941c49900c08a09000032040000c1954148800d40e1808840700003000c1a0710007035002424030502008112484000b00078503022a140e1000c40210340005034120300090100400300450904006600d00c5c181c00f40c1d4175800d10460341440c0990310391380440c4c00d4510688103020550000e0005102096841c01841c04143c1c0e0800208043d84580001601c2000e1112000e20f050702c544503c1e001c1ca88640d04503080750400a04140d070b45007000d00801f401058800080c00a50080c801e283c0c842034031403000c40d900d6507000a950412903074030b02c08101c80d80d0405402d03403441350b41e1504001540030003840a80080121600c80341c0c1c9540c94120b00c038261640051080384a80c108008000417a016403080d200c10300c519044064640c0796901d1300fa8010004890007401071800402c100d42084002c0030750025 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 241093444 1250 241092194 241092199
    0x1403070c20040e010b0909010c050304150b0409120e0f010c02010e04111303120206070f030203090a0b012c060307030807171911060105061b24090d0206010f0b0912010c0201020306 79
    0x415517900047c40d080791405c0c503021002910820100f0f02091404001c1d1403600f1204500260700d030301c240c00040c01c07a90704010850741c51008070341c0d11285030742085a4903049017080e20320450340c030354020000300001000e5000a05021040e003001e98503441d140c0c0441c80c5007030780d400080c1d80c500c0d40000c0b841e15420b80d0322045440e40351040c0040303d120701c0441d500c2e024503080d407101d4010340c06005c0281d01a4000400081c02c5e44902c80055002c95076503800d080c008c0803404190752851005825042c0444c0d4100f60001e1007181c14810b1002e039880c0010346100f12500883c4498440450b80390500301d11685d040800c0c0c2194010442c889040482c0319180380100d625120584050461401c0d5600da440034401c40e680321074144a008103003d0f5080c4802c012091400548000c4030482c900d0000c460340c29030f110640700550004100c0d80070004c00801002c1340c07450004064a614104610444010354099503500c514080b445185503102d031904250403201e242c000b4400b84410b140004d00035002110080d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 241094694 1250 241093444 241093459
    0xd05250f08031e030606090a0e0109061208030403110715080a0606030506032a0402070f0b0c03130816050303090607031104210206090a030807031403070c20040e010b 73
    0x40d007800000403a40d0040060a001168205070a6000c51076000100015040300c400c00c9100d041e030740e0b504071020142003102c452001a5050200b02001c070ba80581043c0b601d03001e04800c50011076400c200781d80e40958546004202c041c905070300c0360704042c1d807944105030340c0030044260254240c100141320700ca007200020812039190b4440d01242030b01c40030340306a600b5410514521148060081410a43e44180107262a40459800220741284d10122059401c14400f0046504018915443c690400ea08042c0c260550070860440d0f0b90304040100c0043c01c040c80011400100280d50702c3c07007000240c006096940700d19220080c0e58945000711504c0c40041d26040809460b904a501910103035850340b1a4000c41200e5441c8541c440501e9030000d0303900020a204040b025661640d420b005144540c0c106038075079400c0d240280c201407070211341c002400800d004024041c0e41c000201020705030001014000c1c0030b00c841c121048400d07460000c60300070341008644480f841e01504103401200017a034505 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 241095944 1250 241094694 241094699
    0xd05060103050a0b18100b1c0b030c010818010f050103080c0d02060702100504050c091003030e04020a0c0f02040f020a170903090a1e05060a090e06010c02030c0d05250f 74
    0x8400702c4400410f216400805e440c0b44403660b0142c0d403080c503400f00c040e081100001da214400d0305550f0b000210645202800308940180711003043c040e0110b5044203030b00803c00c144040300041c1c0854401811a11100007210a8260700042504000400400030200f001956141e00307080b05c00f41e10210f410a82403080c0202020b607184000380c214450405503001d01103000102c1c0010001d010003901c10b40d4140328256400321107039114000140204007425003010994610f107000380140301980c0d04144175610510102c05040d40000c03d0034803880e444880c0181003422480003600401291b58002d014510201c0c15004154202e40c00c8605d80013411442e404603910325a08541d00d100e200c18858200c2a0148204000d40d1207404400c40503250ba900741c0c1c845515803010030415041510008002824440200107000b9600c0030b0a400c01c40a00c0d000052800d260042580c03141d08150701400341854044000600400303000c0b07034403030f140020100b550f980b840c0d4042c00400c01c0d540c001c1c07114101814400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 241097194 1250 241095944 241095961
    0x50a030f1b0b030a0c02030c011416020304060509010327080306040b030102190f170c0a0f0c031d030109081201090c1701050f0d0204020304140f030702030a0b1302060d0506010305 79
    0x1e460031203400440803442c40e50b48003102d03405000004007440561200340048168a40280206d00d02803580d02c2c480000c0b03240003071310f1740a884080141c1c1d40940d0800c00044c02840d6003c02240d100c1d010a080c0070501c006000d0945002c0300c61004449051950010040c00308210b82d4000d5000d0076040b81c0078085c00340d4042c1014200c2c81024024003952140d190180560b50207589800d6041803107003885110111030016524410804550218100000051000d0344c4d40d00000f0b031603252481c514001090940b03540d005411081c14050720401401c4101040901c0d5800750003002c0507a40c42200c0e151a50051a4003507180741080c0070b102c56007400c042c0d110105a104240703012103e20301203c07401043c1d280109000d146c403005a14103800112580400703001d40c607140025402076200310302c1211104e6101002d01c2c2456105180f20074a50000c11564015035000904001d1003500010700262588820f04131400e003126101c1c00039002107001c14030998036942c41d40020310070103080e24203101c11f6603400c01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 241098444 1250 241097194 241097243
    0xc0d03050405100608061f08060405010c0818211b0106081903080a0213030b0c0702010905151812010e0a031d100c031403010807140d08040509040c050a030f 69
    0xb204106d503c00d00001d040c98889900380d4540c8442c4002041416403296010390400354103c8043d80c03140e444d140d40f0050181d10034010307980a541404600c00c640c500618480c0c4072480d00c03284c1d81c01c0d0709a0081c8401c11030302c96012564015441c85801c20546040141c1c01e0281c0068400d000b007038000d000004100394000100c00459a5065842d00c0180da038441d5840002c1d00844021007000c215044040002078003800da1314003800d22407a900703441c0e4616100042c100b440540000d0301070295603400c074006180000c2078a5814074140d294103000c031400c50126440040f99100c07a40c3e9503090103640c640005010035841202c0c2d0003643c0f05038038001d05100c94003140f0700a080307642c0c0100c00440c040d0070081c801e075080002c49200b89000d0a0840e00502c002013030750001c0c3c2103000150001c0e0403c0006a6500040360281c001c2603c06080c800841e403204404c600880c425180103000c1d290000c1c040100c810403040140c10020884140c80b6101e00300040030f00e401010881e00c01e019004050b80f44980c00304d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 241099694 1250 241098444 241098449
    0x313030e10090911091f030b04090b04120207080c062d03070915020c01030f0f060f050f12031801020f030d0204060f0c0b0403030b01120525080f0f0403050c0d030504051006 76
    0x2080080000e1252028041c1003150f180d9000c10190362300400140341d5118002d8510072070280b626102d07641410706241ca01c1010140d01031081d175210507020003505c100401d11008201d811110355448001940b030708015044880c00c4407030750208c40f40303c04101c00c2c15980030b580110320b60b40e00c1c13080f05901d88411a030900f01c010801070142c0d10510102c051584280c100229881c030aa1001c5005004840042e01340c1e40e894020107141e41440d00c06001505100c66013000313542e0700b01c1d8091448200c2003451a224400d0520301d4802521032404040240d000f000b00e00e40e020303425001c40b0354500300384130303120001d400c54010500000c0301003408004080c402d58a607802c203500441068030a85955074290000c00b11140b0782c40c1404017030071384141e0081040c420280b156490000c0c100b081c003440920721350000d043c880b100050064890502003460603035080e51303500001e01003440046446a08044d0f401d80544403c4240a110700c2040c58117081c2d050300f2507402148035100301d41c042c07503da03072505091300c0c940d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 241100944 1250 241099694 241099699
    0x309140a0b012706030b100e0c1603030e10060305060705040f030206131d06040c0e0334060804020310110307080c0f030108011b031a0420070b04150501030201050313030e1009091109 80
    0x18020b0362b503112100340c05100214400e00f00004c0c0d44c00c00000c0390f800d206440498046190380d8207002c2080c00018003031342c2d41c041e0300d924100b0300c0c00c4d0801801a001940600002e8040c070404110f40d2a4501d10303017006030141400420400505c0d6144644c078910203801c4034031030300990500e040c004209000d150300c0342c1c480d10020b02401402070110303080d4a41d05492440421040d0070303804040082006044d000b005003105a680070384070b1616005051070300c6034040c12403455620740800304c0721807084c050039a50814407030319040005440d01c0c000784000b801030090540f180c8100000006d038020781580003a6017400000d10f094440c1d00320080940407a5401a5106003c17a840759440c21585015401804100aa1104c0001c0314244403500c906a0f0030200e0100c1c1d410000c0b03410310081c8965281c80012000041c0801e105c4d56045030b0008000340030143c64030300d8100c1801408030425029401d218280380011303000b5600740c01020300080490000744a200c200e1032901e0354044010729410100c883c401c801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 241102194 1250 241100944 241100947
    0xf180d0e0108271005100510080a0b090a0207020108071e0c080403050a0b061e1005030a020706110301060e09091b0a0807060309140a0b012706030b100e0c 68
    0x50400540390740d00b0042407042c112060550742c1e82c0003000d00d00b00480c0102020000d000e00d182c9070300f40c0811142c0181181c00132220b0100200481d5480c4d4101102805091030700d0080c0fa200c4058800191a2a440441d88080402d0411070108400e501400b1128000da9545559464112080d00c6001c1c1082c90511600020000d01c3e0845028900c0d411500c0d1192603c1460071744e883d01c40e14108101c02c00100c5202a051041c04184d02d4035480c0c20510b00c03403815036006403038041c070001001042e100380c3c820140080030000502c2002a603041c1c5424540003c2c0c1884400c00c4201c00c0302140d03000340541000f044c40c94030305100f02d0034081c00300742c850091000101042e00480c15010400e450303d9205681c03000f18003802284024007884020010300302a1404036101d600d9241001f50642080c1c0d040c151940124030460118841c410b80c0344c1185e00150743c415402158074040e00511444201c41d401e00ca007071110000802c202c3c0c5c40d85330300c5060403d20505c080343d05c51203483c4a4142c01d0f909200c90660 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 241103444 1250 241102194 241102217
    0x30913150b03070c0501020d2307020303071b08070f02040f0608070315020c0304060201051909031704030e10170606031312050409060b09040f020c03071103070e0f180d 74
    0xd000215080f0419040001001202ea5686400da0b803200781000000c60721034019110b031148002c005a0680312455031210a03140156009546e4007000380424100004400101803035000040d01ca5550b6401841036a5100c145003414200d404504004074001c80c600b010940b803840360b500c00d030390680d8810304c082c080c21441c41e00e40212442d010840e21803420ba0030080680910030400061008064035000881c4070b2904044000703500340c82c1c000c0001d929003400d6031140003e907c0440030b9009885900034140c240c5a0b403d049404400c4801301d00e400002e000440d004a50b0481c0f081940c4440c00070301594560b0b508010701829000c251750b225102041c0d008003900041000d6843c0c20310200380c0c5885404c055031030700031106443d540d0303102809503000000c1c214054100b50140590f40d441540c025491700b131071102a1503880c42101c6000c4c2110955090312920b940d018032200008018280140d08581000c1c2c1c01c40603035800c1a10001d81600000351f80c14000c1d031010030301c03034840b40d06a00ca04400c102c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 241104694 1250 241103444 241103459
    0x132102010c02031501080a060e06070f08070c2009090109030525050a11180103020321040b0a020715030c0e06031f030b071115131b03030203091315 65
    0x20300700c040fa8180a0803214440c0c280501c610340b0b000b042094001c10203034001d403c100084590406204400d40c000c00200145035800c60000500002030b850104a50b65032280201e43d045001d10009046007042c4007003030034851860b2001c21804208580403106610b83e26015402c80d01c6022008010590a002e041c8105462940020420000c03401c050140413055031458141844148101c60041002e6005011420b050500000543c0f500806c401c0f9541142c0000c2c0c5e482080800c3c00a4000b0408101801c00902c40140d400501d000c0f603803a17440782102ca8020307403110f1060249444030541d2004030000300d4800c0c0103031003504880b81c4501c2e0081c011a414043c01e40c3c0000e140310741c05a00e0030544000c4201da11050001580a03002003115820201c5005000070721000d44880c944d4000131542c982c0da681c2c18140ba810024009405194a0b00d074a44041d04203059070a2024850b00c0c008000145030300400284240d00080341c588410308040300d059001c94030231091461540e030107104281b0110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 241105944 1250 241104694 241104707
    0x10806040303110d021c0f021305040f2a0e01210902040615020106032310022802070509070f020d030911031002070209010608010303050a080a140a0213210201 70
    0x841c8608041c0c0e16080019100500360390200c04d6401c206c100308083c010452106100f034041c01044c507181903240046881c2116299446802414422982c41c0034810115006030b0203400c00900c001919440803400c0b090556010a10a00c1e00010881d40d0305228425849030310907000e07034101c8240c651080e01d0598035080c000c16214500300e0300140e580038046142d40a402e207443c45200c05a0005c10070310b0462074480ca0758040c00807044100d100c00401105000350101e4411002210704000507280c840c080076080002900c01c0541041045c080200c000340b03680410700000380e407070550b01062580c03103020088a0b0100940b20b03000040e00100c09400906200e0b400486902c1c0c0a0201101c0c0c1d0800140060b0425650340104025603600150001c00c504004600328018003240c00e0907039030356141d070b02c01a00340d00ca8180024100140c240008205121135031200000d5005014001e9140c0303008032510000f5800b8034503440304950f01920020f01c0d211020300402c581ca9850900303085c8801e19500550b2038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 241107194 1250 241105944 241105961
    0xe1e0c04030803041103071707090b0f06040602030c1603020a060806180c07060e0106120f14060a091a060604050120031810020a080f070812040c06031103010806040303 74
    0x106602000300101141840c0003850055004900c400da031001c00c4401c2502d08001680140c0341503044444e20f104005000c00c104c001c172006801c004c100c40d2032050014124020f16040190301403000300c0c0c00b140081d400030182000050380c0d8102c8a0544d040c15071303a004002e0f01c0c40000c3d0b00c1303c82a04103100c803a204240c0700b5040300000c0c103400016a0041404503404108031500d041d031500204102e8103101c1180215082c15035080001c211050030700c510350060b02c01d129805089946c2d501d0b01c000030007a9520050311603503503800070b4841c0d030300305034a02c4009042540001c2e074a41d660010005003402c12003011034010b2000801c07a52400740b5100055905203601c0308203a510180f5070408444000d0103000821040345241c070f11400300000c240400071310080c840e00034811540701030b070f07500f00003611041215a00002d400c0c1050702d9200602c0c050b82c085c4a00844ea001e202101c10a100c200702e0391030220000c0e211580c809019440101d00c04271207a0200340721700301103940a4404580801d00943c481c205 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 241108444 1250 241107194 241107211
    0x703030c020321070e010825120c050304020901091a2b050c090906010b040b0702062203200618041b08070e0f01020a03030e071d040c0e1e 61
    0xc02040030000c180b260346500d0400302c21000c034010000d1040d40242c0c09140040e007400c0880c4c2c03600700042165005640b5588004140e048c7e8000a08010b01407289442c0104910000307002c14003000c0c0e4000c040d5001500c04074004d191040010600c09024011500c401d1440e50082141c48214010010000c0c440c454105160303816003000b10712003a501180b40d0201e030040f801030101c440103d080c40394856005207110481d40040d001406080700d0315085030229420000306944401c00c03400050454800c04418803800041580c018403010a803640c08000c4900450628044869000c0803113421180f078005141e10000c10401405520a5080802d016000c054800a01c200181179140310a031281a03c00000c0f07880c0d50100045140e1121a0144c03001050300c0b204983d00d80000080d580e0741d0f043d50700900b8503886030b140f650400c50030404007004101070708421140c000032040030111403100340c4040c0e60031540e5440116514825405160144207180301c075a00440d03420b0f00110f000c1c080a0019038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 241109694 1250 241108444 241108447
    0x80604140708060126160203070b010b1e0307021608030307050405150c1e060604090c030b1503010609020d1109010c12020c1806010f0c0507150203040306020d06080714060703030c0203 81
    0x5162140d0001c164005c8800500e04124a0a0009204140c40c200d80c0c83ca4045600c10003c010000340c035410700e03504440e09080c200385c0302c00101400d81400303030040240707039110300000c4200f00c56691f0020b484450754000d10301c1c1200a60f2980d0102c2e071039110031141d40d030214204010411160030f10300d112081c600d010201690038400c4440070282890100844200040740c50114a0b1b030140082c000e55030001c404a4041104040301e50300d02c01c010240d40300261072528480d002804a0210b2489980d800b20011700802809071280b1505000390400c440c0c02c1c6840345000820100040444200c0307810b40381c161240c034186c0d074181d0354101e02503c901e0030b49001c60259003c00c0d001520341e0488580da150844100701c0c3c4502c1d04c00001000243c1d210080c500300510a001a00031500200340401510400901d00d001c540e01c070320013a4514480d544c401010544006694080d03c0100c4d40848142e07103801080d0b508190340c0d1a000c442d02a08210324039440001006440000b034041d500001403c0c200d0b0041e42e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 241110944 1250 241109694 241109717
    0x1209060c010207060c020c12060709060e120a150f05010f030602070c0e010e1918030518090906090705030a050c0913020402120901060602031c09050c061305010806041407080601 78
    0x80c13098410002e01003006da40207220a5001e0318101c244103d0b24440c0c980185907a107031540c07009280c1000c074890602400008003428205469201986c40350285c0002114400c640c10f10b4800440c60190400f03039400d5107413030345400880e1082e000f8507041f628152021907041d400c50b1600c02c025803092000f02d84030b052303070a40003c142000300134080c0200407901a007501441e08410942440031a10321a07002c15140143d002c280314509901e24985c20340520742951100d05035020050f81e08084556680e00000810421813924400038510f07121740303e10f50684004a82c0c0714249591003240c0080241260001510f00115041481c84654424001402e001544440d0340204049a0141500c1e01101180c802000840031090148800402081c0700552503c0d00c054545280c0d001c8001c00702c640c86848410310ba05000d420000ca480002e0010f1405035509000004000511114072620303010840c02e0300094940d28061044268000300c504601400395114802101c01d868010b0070681401610504c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 241112194 1250 241110944 241110953
    0x62a0c070f090509070603020405030a24090605160c0506040f05120c0f120421020f040c0c03020111030f040605062d040b040504081c090b100311031209060c010207 72
    0x280d41c01000440d0000500e4106038091909180e0301d9003146040c140104010080e50b180020710302d800030780181c80310480040d00c114004044280c0c00032064518100690b1009100040d0701450041c1a4820680b1191819503420303941000d200f00d01030065004400080c0c0412509a40010618072550548420f2500b00e080030b502500403081580d202c1c1c0c0f0001d00f0a0040c60200241c4c41c400001d411500d090600c2c0940b600011000c0301201e121401c90705100f10119220400c1c030589109000708207002000d0040070007002c1d260580b00540c010b600300f51800d18100da950341180e006400342d805001d80e9540c0e40c0c4442e03014102c0617000c0740e0000e990701d03c481000c0714100c81100041507109030300c4148142000812051395800098184610700d082c0900c400610004102c61602640388410441c44803000c00410080c400381e04007405e00900780d03042000154241038420240c0c5d02c100c911104199165040c1551513060b048141e4020100700242102071521001031b1001c2421034001601c0c109032541e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 241113444 1250 241112194 241112219
    0x12110901050c0c1e0108100e071103090306011202100507030804030f020f0d030203070909110904112b1406030606190302060f0903010606021f2003090c03062a0c07 72
    0x2004808041301c2502c403020360f0300654142d001039a090400a0003401d046071540481c00190a40c1c00b031207a05404650310384000e00130b450108000034256961581e42d040740740054540c1c07000032031055650380c4103481c6080c00381095400700c1c0c1d010b542c0d5400954030765030141e904480305136161041d80304403030341000101020004140a4143d5035000358032820585070180c150180f41e00316202c2c00c2e0501c1c2d105600c0075080810307160415021038005c15000314148210445100f4a10200702d0302c074050b50304015100080b400070b15400302c80a420007404103005c0c6201140ea0003a5617099154010348003041081c504080200f03040c83d00080f1503600140d0341d500203507181d400f240036008010070108806005240070f214940c010801800680060800b01101c25a4403910110703003c0103560701c3c4480241051490b0042d03d1901000b901c813070703803030034a8a08203a45040320b103e194442d12031a0b0001e07040446088424030407410b0350002c0c00e0315451006400781e5a400517100340590784a56000003601b00d41001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 241114694 1250 241113444 241113469
    0xf0c050705041806090f020102010c090509040b100f1215060308180f030109140606010c02060a050a051e030a05180706050702030a02040615080a02040b0405040f060f0602010c12110901050c0c 84
    0x1b03001e8181d40242c80060b0940d26030070441300c24014028400c00a940340e4619196000d580701600803010740d244000000e0038402d0390415803034416103500c042000240b030709400c0300c11070080701116180c0d4114071302c2c10140c4030103000003010f03140103100680703800203403403201101030f440205460058a540b101181c2100ca0455068404600d52a4a103200300818000640c0002c82072030148000740c6980c0201c0d20b0341c81000d140000f081000035500d224684124203031189184107044010400c0d400c48120282500251903c554051030100410900449000c3d2003407030400f01c8019101c0e8500d040c4045d01c154021800a0380c05028000403600107a8842c0b1507030020301403502c0008941402e107070000b001300070001c10045d40d20b441040b050000e80d0f0104281c0f0b040700c4040340d02040c21050665450064030081c1d10022448e54005000f00b613031501074100c08106121541c44103203190400c450001540e8040904c56400c440402000b003965119a0052449401540441d07050790140004181c0f81c15014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 241115944 1250 241114694 241114703
    0x140f090a14060405040f020111070b030a14060a0f0603200706022a06010905070c06050405030a020c040207020907030903051b0c04050c1206190f090c0f0c05070504180609 75
    0x40c150032800461140070160403060981d0208103d01d0940c0c1d8092003009911030180c1408112142982a00c1c810007440c3d016241c0f80ba20390f600c0e802d0803860030015140b034524980501e5042d00002c0c0090824030b000204558180140c0303085a0700c2c0a0080e401000c034003140ba0200d40700c0c82c600d0408400d5041c000e003105440344400603030303980c0461202c0d101c4400035502e040703d4103085e0413040b00d481c2000400d40d065440744c04001071140c0380c2031000d5a00380b00e1408000c0c10f00e4103240030007050010101c01303041c09144607005e4582100e1100100000c86c418194000e5011000c2804500c03c01e20075403062105900c01e0603c0f03442c08000c90344c0b41003a165400d00744113580c0c0c000ca079220140d0a1902071207030020504810141440203698098804460041000740203c05a019a03540003001020000040030546078042c01c0e26240e1b141d5401401424000314081480001a03000c014495048801510f401001412006040c1010400903100011646480c0c44201013817002040681c4169440640315 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 241117194 1250 241115944 241115951
    0x2121623220608060103030e040507050706091104060501020304180f06030c03050a0c090b06031303200106140a0b0a03090809130f050109020f0711060c060405071a030709140f090a 79
    0x1010084142d4165070000340407038110b00d00400000c1c0c1c00045820b01c43e20b00f1034000c1010354a400c4211803901910a01400e200c0c00e226030042400484e11981c1800d00e07040d40c00f8050507840703a00590340c0e0b207e140b1890782c4640c03110400100040595000208500e01d080000c900145d49444003170f5030540301c3e0001d49158201c104004104641816114000c010304202030003418421400500a400b009001c83d440d0b801426421040610400b003040031b121aa51810700b001c03001c1e40c5414000d020a00484441030340310801d81404d8034001080ca011a06d03001d501e1490410b5201c0304401070a8940342c01c84e040d07001840444865925104d212614030039005001940320107001d450800d071041a4018100d10744100445c0e213400c01904125254145c00c9216130f14401c440d0008a00345110704440039080e405000144001c0003000721b440002c440501e10030b1603505001d00038021080c401900c2500102d804c000c0f040010703d500c0da0714103401c0c036402409a2003402000b00440c0c91544102c1300301c03203010358 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 241118444 1250 241117194 241117249
    0x100b0a05030d090e10050604120501110d060e13050a121404140102100c05041e0801060306050f0a02040617180607030b01091406030121050f0a02121623 67
    0x800d00150f070f0b00417180310490440500c3c0802042070b0f071003603024071103803400d11243c048103003c0e0940001c1d12302c0c1006447c5a5840f221000c2403030003000c260003001800300c0c262020526100d1844030008006030020b0140c041c506c002e40d24045600e40c14014101400000541c641452000c0d0014000506c06a03461903010550a40024201202164036854152800313001c0090190300030143c030144d9401010000d100943c41030320081e0717507034198464540356090541c0402005a5504240e018200002d4140f20589034004c0c00703000e038091070156800140401610441d80b00c0b003010030711317040361000705004003000800d50140d007809011540a00460303241c08c02d001a80d41e0200d100c82c010001c2c42c105800080e00c3c0e4001544a00c010312030311000350088166102c2e602c45c5a250782c030413070b58014101c030f00980141300415280d000d0440203034420071080e2408901d00b02c000c00c0c000b0248903083c1c01d08103543d081c9107034141e00c450365850410060320b4001c240c10703a548403c82d00307941c0c8101c1066104480360 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 241119694 1250 241118444 241118459
    0xa1401140f0406031410170c030f0d020c0913020904021309030801081006081c0302040b0a08040c0f080c130b04090b0105122a01140703030b0a0504020a02100b0a05030d09 75
    0x10b4a02c404c1171700e46081c1d02c04200d02c024202480c1c509692580d9142c850307100d05192801e28001c040707550141c2c98010400407001081000801c85016811502501e880266010800c54100340858541400c6032005c2c4c0d4000042c9060704900340c0c8244001c1c0000202c2c80540f120804442e4140000c40115001e54014450881d0400015100c2801e1040502003541001c4883d900c0c0c05500300a807803090400d40e180b801a502a4046c0c4014040c00031459860740c00b040e00081c0350320805ea4082d20315200000c000308001c006580707054140c0e00310703d004200c40079404041c408651109042c08480580d00c1045980740d5559005108501b8003070310101e0040e5040130104241011900304e100110750040401d07103200c10185045501072504503450101c0d002c007050050b202d59440040c0c1210381c1078001295010160190700411103031000b540e02c003100d140c0b6172051000702d01c200427000016034032035580381c00c1d10142030304000d003021400f41141480680d50800f00b468181d890002d100410300d4440248000e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 241120944 1250 241119694 241119701
    0x4080307030608060712090c0b030405100e0102040b0307050a0903020619020f210a02070911030103150501140d0501090803090a15090f0b0901020912100e0c0a1401140f040603 77
    0x41090380d01600d01d5040c000b00142c51b2003004001c5103500e5856402810900ca080300203c002008640605603903885c240c50030644841c03c640d00c0744045441c0465084041e00c0510a403410341d40310090003131441c1c440540c1550207400104003181000150035001c00103031909030180c4481c191003110107811421b1076034043c0c18031100140603c0c095110a8180d49510700602e4202258256640100d40c0c51420b03181c102c0c02c160541e0000f207481070a020b040031003804c040c802141264040d5505800c1480b0400e80c80c01503038000e0bc1040209102100a405240740c2400710f04c12047c864400020340a06940e503140c0582c00403a506000e50300110303c03803428807171484e0b00e8944001009070100030300e405590702c01d9a00300081501508122400c2c0c00200241000d5040381c181c0000201404c20b80c000c0d0000141c0e031405207501600195050120840d10900c00043c6e482ca80c40004000007011424198074905101c28a001302d0704100594482042c000303038840c001d0104400e00500d81b83c0e102d05090015003030f07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 241122194 1250 241120944 241120949
    0x80d03051311060d09050a0b0a05100b090604030212062e0b0a0c05010e0c0a0609060503130201020c101d010c020f0925170108030f07030c0f0803040803070306 70
    0x9060a000411000a07048440c0c80300c226400086441c200c1a4800416868043d001810240340d19180c58501400000134042e400640704201040855449000791402ea136429202c1c3d0190104d00304c424001203040002406074602c020300140e040a5407600046c00d40c40e812030340344017079400900a01140e00f910206a49000808982032821064402e0024400344002d00c14800780d0036000c540828481c0c490090032002a03000b000078441222034800b16500c44100c00811480f960200d0130000e1501d0040c0035402c12074010351107441c00c40e5182c854070f480c25108603000b00d04602030542c1031076090b42c40d042d4a038540d8003030355259401c2c0a80c52056820b540b0803070f00818180b001d9081d80c000180d450302e0340a800a07901b0707a204025610f4000380351904907100d841041a10a0454182c070080383d1103103240308002003d0f283e4501c00d0746d854101b01d41b02d21581e802c40710286001c00030003000ca402008980d200900c01c0354181c100010300d498000282c1c04c2590205c0e074070a03000041c04034207503146c02040302 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 241123444 1250 241122194 241122197
    0x71101090804290409020703090e09030d0b040b0d140a050d020a060608060c040512010b130c020106051905060318010f020406081612091509050d11070f090e01180c080d 74
    0x161a85076502c200541d00641c440c081041b50001040c00405200701d0300c07c2c008004444010000707051100d40540c80c1e42185030481160381c0b81031000d51003407a02d801380040e00d480c06000e5018003d001e480782c1c0c0041200180d000424810f03841200001801041119040001c81d4058140c0e031016207803503c1600d0a96018403540da00071824015855100001c036011942c041301d00b00c108000102100703000d04985015a071303014607040c01e02d0041010070b8002e9103288415500800c41c4580728000c2140721101305403d058106002e090500140c10f08100554200240c403841a080d0720610b42c0032425100c040500e24030f0b8940100f410048150411366958110100c0308404043c0304007440000c3c001c1400031174401c0c949444807410010b211908620301101241c5490500c8a6285818660ba5400200c00e081c8001000c1503c2052303a000702142c000117441c0c1d03030706007444400e2406000c180070300f0020504500301d5582c1c030b40c2001406101404070416600c0340400c02c4e00c90740390001c0e050038201d01840000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 241124694 1250 241123444 241123499
    0x4030e01090b0c0c1215010b0901180b12040219030807120305070f12020c01240b03011404020a030e030c0a031407020f042313060501050607120305071101090804 71
    0x1546000f0110f21803003c91010780308841502a60043e451502007412103180700a0810000420a80402d900a000c1220700ba21040c0c5541c0c10003628580020703082c030442004a2013403082c10100d100200d81150801d00003490301c2c0e0100f00590440c00c070440b0b550b01c12210110000351000c1003115422105a50826500301008989403411000e840140c20740c6041040042c2c4c0d881048031f4103d0381d4140d0780c1c0358408000800980604c1a412030711581c0c07184003c0e0b0800310240300019007480c1101168180c40d04101c4142003c0c41103030500c070103034000c14100b400380741c0c403210041914141000a0005005000001c0440c00030506020701316982e10000c4480c0c0410411120000d40ca590b20400401a401d503000942c07200d28421140000c04003002030008290700130244604c444c00c00e0b205256a40c0101070811442c1d07070b150104a924480c0c00401480c103161080017070452b9019a111301e40c81211030034036000b40b0a41200441c00c542c3ca49004450300d502c081424000c5046540740001c1c402404810031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 241125944 1250 241124694 241124707
    0x306032906010c24020705010b033004050d0b040308160905061309110705061006090302060d140702010c09050f060301031e0507060801031109040b0c0703020c0904030e01090b 77
    0x3004000c0200441c2c10302c03284001640421504c16140e80183c985011050051040081c000001e90300c82d43d0f0035507641d030070f00010307844601d40800d0350310100a40901080706c01da07650510a903000e11941c2c40320740382002032100107521344403032440c10a55482000158064503003407401603c496405024001648050703032400032400e4100200205440b811501c00740c03030304001001d034003005645400503036110741424a01a98100403001a05d50148a2415505107076581c0140790744a07000f51048400040311504100003500b003c10060008076841c0c0f1022580029018401c1001c12082d1104401130307565000d002e000c01c2d0700240c490040d20080f1841c000649050b8001040307400b040c000038200c2d041540c0740c40100d183d820004503003980d114040d00e108555070075026111003001d100a45904e200b213482070601e03140c52114544a141d0100001d049501c0703414000f81d5a4000324030440541c4181d030942800d47da50494600e108030b00ca6a6003003291800f04000411110903507000030040c00e42440711 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 241127194 1250 241125944 241126013
    0xa020a080a050907170304091404140c0307031101030207060603030504090e07050d060b01090f0608070f03090c061b060204260f030a030c0512070f030501080a020901030206070f080406030603 84
    0x100215100d000342005c2000050302000e056110b15842148072a20f4130b506003400031140d8407480d129500a403900c164044c5144622604c4001c0003460030f40c180c0044000b40001a50300c103420b81c0080041c9030040c1400b0943d5a580200c0d50582c00070341c081b580100d001c03c41c041da1400f4180c442e015010191002910300301c0800c0e401580b00600400c100e03100c8a0a0409074030529078034004181001e00c00c942c01d955110007030541c00c0280d07030318030004924100200303256020380500200b82d50721003d640401403400c841100d40c4807002c000381c0064400c5a07610b401082e0b050024001510407141404200d034071820101500807803581d150b00b001e0308100c2d6070700e41890002c42528130001d158180030800c81482c240854043c0305803245000c0001042c800c2c002c225610600e800c1459903551801c0141c0d0340c0384c10138982e07603105c0c10000079030000340c2c8170042c0300604001c805040094800d540794205210035541d88911a0080d8101c02e00096907401c0c03c10034040144a884251911000c03994001c9100413103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 241128444 1250 241127194 241127203
    0xa0306180915110909040303020a030c14070f06063501090f1709120d0315050a0603020c01110a02060a0b06090f010509010c0818012d0c031101050a020a080a0509 71
    0x2c42c0d14030150349180c40882d03002a0011100b04000040003034256240903d800340081d004502154002440d0041d11400e4078004c022950504841c0403c80341483e4460ba13800e40c2e24407065004607941521100300040049a0288200304800c10341103a038a800928007444d20700c60740c00394503001168140f0036298042441c00b2640c04045801c80704401c01c00c0012421842e80e845840c0310503820850b5a54800a41040031070352010b04c2d07030035560a00c078501c1c40011014100065004082c0e01c00c1001e03508000f081d000c0c0e4020941e044c00b04001080c907081c51503502c0038540002184201607003065040000002c4544280984070000b11000b500700f06289010546135100840c40b2418000e0000b038028080e03000f01d02d03003141c550707102c0102a03451705402c850030b00380c0c141e201c134082c00300380030040e103801d5081714840c501010f258400031702854030788401c0300b12001f07052000c05405204500e00c481004280c01c0c00f601384501440344001d0703510089004010030303c0c0070040800000c02d107001c050002c030316000308 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 241129694 1250 241128444 241128473
    0x7030204151514090a0603020903010e0d1d0f10020303040b010b0a050f030c120c0417150402091e0702030a1b0c0302090c040803030f0702190f030c1401020a03061809 73
    0xe0009400b4039581ca68841038404d00c0c00c1d06500c0302c285c520004521758035800400203210103900074803082c032941403016503e41c0214100ca000c031780e19101c45407103480c04071142d07000420000c00200ca4100760001080303d84004030310800041c0c00020801003400341c0b0003182d6004249001525144c468251002031407805400324600c040034000020071a0038410105444200000600c4800b2604000340e0100c0f456104d4443c1311140c180301d18101201e200040b840707a02071400c2d0b41c0c075180150b80d60350030171400c00d00003800c0710300b441650004124a03003c041c08a82c401c800980007181c1d240c0c0c0541004e0b2a01d41d031082000d400342c200c0e00440000402a00341d110440382c1c1a54804065201c08440140d540600c0d0000b245074840482080404281e04501342d014408070303005e81e192044014608000c01c503125101900901405010344c0c0020701c144036010034140200318641c1d030035070b200035003d09a9100e100f40c0d1000030748442c01032158848502582900c0d00245400f0400f4980542d604580d800000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 241130944 1250 241129694 241129697
    0xc060706020c010f0c020c01030b010918020c030307080906010f0b07110f0607060207021816050702040b0a0303020a02030f06160c0212030a05070b0a06270f0509070302041515 77
    0x10502404011540e0141d4010001d020001c4c00b00d901c0300803103403004124441e59400140306500308100c255000c4d00c031304100503006035079095110b810180c400c0c22072441c409100f042d080d0308000941035404148082c40c0205c5c0903030b40e40001c1d030821074021803510006030802504ac6c9600c480810000b42450116070095500c801d6441c200c4008100080107c82a11480c0e0340050001900703c0820101d5801000520b200711143d010681c400750390b40c01e02d01404c4134010321405000003030f240d0240c0a100a04001da03c014408501c941c00c100100f4990401a4000c50140c0c1c40000442c0840c43c0c1400349038601c280304e40c01000149049040d078a04104a64980001c0c09408a48441551240f00c00c060039a80303204112036a80c041c40c8001840c983c070150041c0c1d0030010940215005900d41d00480c81228041454691007000d040001d880c034140c0030030000d00f11551040e806001081c82d010f035900c510070060190501e03e1560060009941c8250241c6080d00007010702400140e900701940701013034185 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 241132194 1250 241130944 241130947
    0x10c050a08060d0b090703061a010f080a021c05010620060105010c03120509030a14070506010b09040b03010c020c180108121303050610030c060c0f020105031e04050309040c110c06 79
    0x15800410319100c0185009000380c2007950400c08807005c000b48440417a0b22800c0308111034262540c1c000c5641c440b00485a0000708600e010711742603481510384a4000825000051424000103140440812025094509035445a00400200b03401140f80040e940c032101c0302c40d00e49600c503260706880e15414003440c2e050046404480301414890750141c1003010301e4000c00c11150070070110440e83d036089119550009a00c40c90045110201703981a84c0a83c0d600000030440b030307400d180740e9144a1300031400c02c40d0003a41d04c6200c5a05a542406058900a200e4003d480003809180c04e01451010050140ca10030482c0d07001000903d0700050640001c0b00c0c211112a103c0900410746000ca04c16640040c0c054411a400c0c080503103400c01000084a1040100360482a5100ea081e01c04941e01e80014103655400c0f00c84501650183c8019940210802c86140785604103e000b00d4080c5801d80b07068809900c080380d100000e040910030b003002241d842c00e08001c219140c10400703943d54152080203005020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 241133444 1250 241132194 241132201
    0x3110a170c070e04050303041202070608010b03130519020f1903060b04020c0f150106030e0618030c0709020d050c03040f06230c070b01090b0f01141e0301031103010c050a08 76
    0x1e062015401030301d110001c03900030b0f06150800507a60f82055405031080c0840704004003505000080344411903075682c070303404c0c6a68603046814595400040415144494080b0b83c1c1000410a00c001200c0303161b031905000c4010382900621031026403841c050350041d5000301c0049485540011603100300c85d8016004182107a140c4040741c0640203502409619200b0b400804104400c0418a05280c94075401c03000c8151382c0e158001c4081c3d420303c1d80315001c9500003a000c2150b07948503101da400d07400354040441c0d15152003000c078680f5000107036024622482e8040b03060003030961180583c540001000c0242421030070941c61b10348040708081d0000f07280c140d0b2a01c20100e6424680169061070380d02d100e070032029103461050345402d603114240884494801e44004200c0401b41c5c0300c2c0501141029161101c0c40344000015030b01c0d08584100302521900502401442d510201141c450101009040e40e071a545986803ea0120305500741940c86a41080c081e0020240c3c0311043e180401424500101a40c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 241134694 1250 241133444 241133467
    0x10b030102161502040b13060813080d0902150d020d0e0109050c1017040c050405090f1c0c060e0706090906150332070e030c0f060f04150c03110a17 65
    0x1704a510110a2010200d0038480c40d181022826046400740c1d1074044807903842500a0100340b03104d00008200100900800e07281e013241d075002d8042da42c0b02601c5940c3d01c40c0882a00025508000c01e10002d103600050301004501c0386005195280000200030b00551185030384064596a09500043c0143d2014400c412400d1081000140c4840104c4803080241000e05060008084070300a49005600707000101300381c00000038920b00001030030400380011240a512495400f401c2c8401202081601406403020900911905803c0c000c0140200b0507a0314101001d41001120340c440d805082ca011380400c400b040d031500054021103c0d15001441406c00c3c80d040c01002c0003201a081919031110401e0891105174144a000301b031107032105906c1c00c14140c10503603189910300c001c1e07802c241000d0300070300c3d141000005085008045075100f81085c2c1c4500ba07041941d4026100000041d201d28038080500d0380202e80050450380d2403004c6d0800b802141c8440c00c945110020368040800300203204d80000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 241135944 1250 241134694 241134697
    0x1090b191e031407080432010f05041704060503010b0a0309060c020601060909060b090904030c050604030e010f0e0f0f04020409060b040302150306010210020a03090c0b0c010b030102161502 83
    0x34261903007070401c2800c0d212002001003540001c6150241c2c0d12101191030140200c4030140f2036980010740381d1610940c01607003601404034411602121140017100f03214028280680c16035003c1619001036245080c0c03c2c4088800852400e1881710b80f405c2005100043c2c0c404c0449065070f0802e00900d6440540540440c01040b15003c081c15840c5003204001c1103e9007c1000c50403503016644240b0015142e0070b00104440706403241160781c50b01000300402d5400e1402c0142d50160003800d02c01c090040e5511b4072400d01e2400c84003200010445847c5289a68205001e049540100d01d05009a0001b440104483c0c0d5001c400340c0b032203800324a19a201959540d01150060f192241042c800207980300700c004025001800201e116150341c0500304410005941501c0c03090304d0590007040000105200341009501000c0401c0801da10340f81018046070442027458000c0c01c091200556613202c0305452800c64030044c003018400c3c0d0041058800809000c035400381300541000010540b8085550064001d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 241137194 1250 241135944 241135967
    0x11121b090403092309150102010b010311090103090602130303050706050c07020a18110a0905180f010302090414070e040605090f060c130e010605091008040b130f1703060a0501090b19 80
    0x10540708410018070201c2ea0246d0780241000780c009100d46c40c44007005500351034021118042011041c004000d90758407c2c3c00c0b107030303800340604001881e08071128010802140ca54109034041100021207034100103151050740d070700c100c4c0d401c0a41d051141550025451a040f441901e034880103d004603442c048035907010451403e448584159100d0035480d000c0c104210038840c15110348092195901209079026425100d50000e400d1a6901d80c216070800c4200c0d980600150780f401a0300c502c0c5071340c10700c0800c2b1480151101001c030401d18030b011314043e07080e00c40080803510960801d018210001d400010065085062814071a03110b10110701808201100f5238005c41c0b041d07140600001e251a0000000e0520030740c1501c85284881c070401d23043e19086015034000381000f88076000100c00784807007140282024450144400a0800c540b00d4000c03400e424030181c1c00000000007805000d03d071122a10780141020300707254041d81d203885484100c50082e4046000000c4041c0148455180700b5030a4040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 241138444 1250 241137194 241137199
    0x90a0509031612090806010e06040207051204090b0a151d12011104030605090f071406071a0f0108010b13020a0e1f02010507210911121b0904030923 65
    0x30b001c1d03080c10300c01c2c03034203030301195650200700c4049002c609050302092480c10388503003040c40c20302a101c0b542400300a6104000c02e5560340a144c180712902e11080c0014802400404400310390348500b841004002c0b0760700e5211689a81c44030143ca240c030b135000107500d42e40120004d07290314080311900209940e404403070f40030380340c5502e450303403400280245002800560b40580c00c02c21483c2d8410f0211a074490302d07601c50390b090b640115030812034401c40300008060b95002a2819007000180d68070030840800e148030b00152804040d08105000f080e03034108038014081c0c00024400340101f640031501e1041c80070b0404031007603000507517011014024600324030340b03074005044258254620130841c0651001d00d007200d001542040c5c0840c090a2141c7c1007000c0091021060403042d5104800f60310007056008000c07111440c501803481e401d039503885405442e50303da65000c0d08085901e2100b02d40d803109450810b40c85241c0e11810702021950140e2040151081140040c0070004406400c1c0d02c44030990424031b5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 241139694 1250 241138444 241138477
    0xc0213020406170612120c1c020303061216090b0a1203050c0d0801031a09070e180105011a030f040302010e030721210c050c10050115030b090a050903 66
    0x70b52280c1c80240b035481e20101900060341070320b496040000a0444000f4a0400e601c9000003042c03000850004002000040c821520b5104080c1405c029802c1c120b030040e005a08040100b0400b41003164034072030b4001e80d03d0080c0c003000302d000180c04901d60740da00584450542d20075150a594980020500103404040e00b40c0d200b000082c034008004d9840241240f40d43e0090000a0600d640100c407814141c1e03510440c858041c040c22900c2c0d560212000704107810300d00c1800c20008212880108060290040b803203444c2c2d080b944142c0c15400e4440607440a10f411300f50082800d00c540c042c030252a0045031054419840e80c8030383c2401c901504e01401505103900000401004004604590000d02030455000340401340031002c5c2580c5000380c1001d140c011200b0000f80c03094078481070b13104ae1100541418050308018220b13148916004442d41075204542d510030040c4044a11005561489c41041c50306010070140d8001040d52144060079201806441d4808928055010300c1600e100b010f0490f6100c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 241140944 1250 241139694 241139699
    0x15030b062104020111010b010819090b01060905040e0c030d0509063106021f050a1103010f060305010e040f02010819090b0f091204030b070e031c03180201020a030c02130204 76
    0x1c008100302520100c4c007040c4144884581a441806104c14071034051312503c4550b9034501000e40b2001e2490250b07d041c96036619200000b48007517107068040c2c162648ca240c5000d050800388000c98000406480059020500028213a0f80000341d440d5200b001e850035640b229200d10100340c0900a02200c244d40355420308940000c03890319003010400b1008801c200c00c666694007821b80e114100d50754500c40c4c0009400000c0c01c00c64640d0032550300800e040c080007503195001c41300038195820130380080c1050b00320311000304001c540c180282d0b4050001d0300b041a1483c1030503030f1760110f07100c0318040090501c200c40c0001050b1a10603001e485404010b00d10900484455117002401a030b000c0302d05a903000c4851011071202100011803040002040e0303155071810342580ca46c0304021500500010070400c0004140340d45403018004038404000e10f0110504080a24501605903a00c000501d0820301d80702a220f0017503a070010b0019402505400d00c04c6005800740040b400d0781e400342c040200d0ba2400013800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 241142194 1250 241140944 241140997
    0xc0304080604050106060c02060d090c080106080c100206070c0303090303021606090c0b0a0e0f0607050d050a0f05120f07021c0e15040506030615070203010f1d060115030b06 76
    0x6042c80742d40b00304004c01c241a00d81c0c03030983e03c00c102d02c0800703501f000c004c4c0616003110f44607601030398049002d258142c000c1692000c6007400e654180c0c00035011504020962080c42c2010b21701c0040c3c000c003600280a00d407030408402010009848005010140c45010307610526011b58110707400981c00d84d02c04108624207041540c098050300600305c403104d4061030001912402e42c4290780c020005540d414020359650420170072829000800180d00981c10450400010402c200100d06a0dc483e02c1b00d0303440b10341c0d0b1800941201c107800380040034460100b11140c00040e5010f92241e01014013a4488059200c0110480c9024442420b410280e0b00c60446011031980080c0c09030b01022044034030b1072150102c100d804805024510507541c00110500104401d8034058042c1c07a0481e81800c403190500302243c0001e800c0d240103c000300d5909980e01c0030754a4480c1c18443c07000c1d01604850007841ca9514042120310400d50700380740d90003090ba90700020001a62404c048030130411f2615062403142550044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 241143444 1250 241142194 241142203
    0x711030a080c100b0102060601053412170c030a1401080304080d0903020a0302040903270f05010e090106080c0403020910050301180302121c0c020606090603031602150c030408 77
    0xe50165100322256800f9608040c040c00c1d45115040c0d01411840e00e68100644a5801004105040781303603501c481a0400404012000c1c01d2482c40040d02841040781400c00020b20201e9980b0108220a1003c1c80c41c0d0002c0c0d1049500943c1d05202c0c1640c036555210004e0080c81440c8803000750048140000602c250f0000191007502e1500e13056400c0c0c030010f4103090b81c0400d20352100035003140703000ca4100051f2805900480086000b810080d540c000004891403020101244000404000520521000c003086180102401c020700300b913a100e10701c04000500306581407140004000ca901d001034618900b0400740d030b0003554060001c87c00d6003402855800c42c51414040c2c80d000303610b07100042200303184d4201b800f801e042e050340103411420080d4512030805e5101018400c2c1e0501e043c21101c8441c40d6500c20210664040e038090b10042c2401400c005540e04090300c0035210358818010929601b07400c03521588a17980c11218070340b00034501c141c03003507050207090031070840c0e4000454005040040402c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 241144694 1250 241143444 241143457
    0x4080702100f020d02010e1e010e0f0706170c09040b03190b061f14131a0d110c070501120e0601150212030f060d020409083103080307050711030a08 65
    0x3c0a841ca0184410012401c8a151040e80c2001d503100300310040130804c640c0c02902a1050000000c900580066580b0f1f00c4c04265000301966039000e20410450703151710689800311506920050a554200b481c18071045010f000c20403881256508620000c51354200b010902c0328074540f0009a03c0740d900d040c4480405000c55034180502e800f0070404d854440800f090920f5800d25449251000c2208110301c94160880851000c4070484020041079440741c2d0a90515181c607030044064ac0c407607801c80341038251905800204640b82c81030000d4140f8000103c0c2290580342e0a18141c02130605848056001e00311400795500c0c1c50140340008110711400d900c424010308240d03021140080f09600c074048442c0300c21101205c50b0f41100000c00c00505c0c00900e0005142d00081000c5001849500e84581d0742d40500307814024030209000700707100a02000303101400340d00c012040c00505403a40d203900c0054800141490100f0000180d92030070000304580c0c402c03030854068100c98031080140303802401c5620a5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 241145944 1250 241144694 241144697
    0xf0a2a0507080a1e0c21060b040603020a1208091c030801060c0f0b0408070611090a08070302030c060f0409020a02030a03050606091e0409061a0420090904080702100f 73
    0x7004209141c00003101c0d465075a02042000860005841c205940701110f10100c0c0d07000700c680000030f03842c03d0b07981a44a00071140c0d131001c03a41048620b008400c5a4407126081c1c0241d06181c2c04002503503490044000b2565140944003003040d40e407902c0b004500c90041550340c0482c1c101d030200d030040700c8408034000d407030f00c2a19298881c0e40c0741da50546000b440307081d008008156913014000007840001242e50010311070182241000c041c0d03518034003074640030f031282c901010340400c0b00c080514101c0040e2005004c0180035000b02c1c0c5c110b402281d00c84007881942c0e4001d100008402d1480c420034030888006101c800011500c03159104002500d907480509141d002a040030041000343c500041190260715000346500421000c1158081c002030f8a02d050f00da100381d880110b400880c1c0580554041144c0102d160f04180c01002d007000110340459082c0501441d500801106c0600e50504030b40070170701c0403188001e1607501ca02d82507e541c40303080c41c020341112004050240c0b1a8200d21290b018125a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 241147194 1250 241145944 241145953
    0x30f03120714090d02010903050d12051812030603160801150b0c060a0b01030e030a180609030302070b0c0a06140a050c0903070506070602041517010e0c0f0a2a05 71
    0x40040c12a21103151030030320b070380c40e510800011050b0320344400200002413040c105195103583da034840b20b040000030f40c1d540010440c103032101c1808900501c11903500c1540780250165a20a040f54255200104440e01e000524000b02052059804105030701c000380f02d20003207010380c03600e801445010300f290824141c2c42844a0401044201000b019038030b88505510040030742e0b07681c0400c0310000d000440015418180d90343c10020402c0c60900c000c0c0b122111b9502c9924880c1e0312040e90b448514440c2c1c0c01101008414442403001903800b06034230080300d04402e00d668407452603940b15801e01000003401003500d4500b0f0035070200c0e2156001c61500caa002d407041005075035a1607410944c90310403005241e51542000310709110500c3c1c00009002440d0082c0c400500707090320b40100c81d01c2e1801c0d5040c0140072403025a200c00440080c1c0f1051400343c101240710300e203241040499a10140585544407558a00205101020612410039803201004001484290045003d070b00200c00400f048186c40078002e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 241148444 1250 241147194 241147201
    0xf0a0e031b070509090a140a0f0609150e161505030f041b03030801090524010302180409030305060306070908070b1b10020a02010c051c0902060f0d0b12010c0c02040c0e030f0312 78
    0x40c04103100011070b4211512027114040d60b42c41c1c030000c14150341d0444051500703204102c80228180306c1c803204d0850f640700070000184e0115580e5142c0b410365001c44008900107010030100c59100c0140c90700a808882c2c0c1848a40729071815000090500700c0c40d886c176480b902000414141d200d845030b812140251420029a1110800350454a03407621820b0300710f5510b2a036040c41075110b40e00130510709141c26184011800300ca400281603484001c0f0540000361034106210b520704d018080c0c29003003281400c06088080c60110203d441d010700303209281c541c41001c500003411816864200383e014000350242c500030070100318900d009401402030b880c015880c00d8101d801460245048456000108201c0c861a104001440002d00f01c255400c0380c1080003409400040740d0010f01610311103d03609404a4146084002c0c41f0207040850811006681056070384001d0300c1e0002c10034820b098040d01c000c039200d00070110075200901421001a0503200e041c03d446601d1001001400d016044120400300a84 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 241149694 1250 241148444 241148483
    0xb07030c0e0312030613060801050f010b031317090306070c170c0309090c070f05210702010c021005090a030503030103020907020607050d15050a0b030f0a0e031b070509090a 76
    0x2044422000d0b09907005005030305040440d00040d6501ca076000341161b81c8683c0541001040c5c1d8207a80c0410030301c2e9110070a0280c0303207444440c40342c0548009040e40d800e600d020380010034040107907200a000102c903a03542a0301e4940b18011203c1c40d02018080b41c0700f60805140c02084810703070000a031490150412000b042442c5d200c2250745202002e002107050082c00c801f0841311803c00342240790000c1082201800007402d80c6400062107008202400144000f03201204903110b092020b001300304010400342005030b800c0790700d04c0945a015103403011000b9813010f0948091107450100303a400402500700000300300c0b0002c0214140c03482514901143d44641c40c0c1030b03a640d40d06031010804540c0920000d401c8080640c171602c1c9600503180300e000712690f110701041700440240c2061910341000010404200c2064507440e8101117000030400c01e1440c0c80e98001e03128000e2111100c40380d08080400340e0441c0d002c2101da0b0142c1001000c04940b0700300414015035030050740a084444644c1d846030803241c01c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 241150944 1250 241149694 241149707
    0xf0906091217150f0f0d0302060906071b03030207260414040c1709030d020f04050102010b0a0305061f08030409020c1b01050a050a1809150b1c180506040b07030c 71
    0x801841409500c42140300c810000d0b18900a500c05800c603c1c00183c4101a60f943c040c60506c4074020303006042c090401c1d1010134200700005240c002032000341c0d00c05880d402030b241500030107550075140c016182c0420b840d1013600b481c000042a0003c4554401002c00c00320828001d204880d00c009806103500c140505001c00d0782e0725408002d0108584a00300c000320a07800400311340c04500d510649152295a00240c412038200c0e100404e821080401c0a103c0c558091142c0c480c1110308940c0c0c1c4440c1450b55540c1030361940c000b01090301e102e81d2816480308101c0c503c4101c0014207a40c00940345c8842c0c50b040300b45d00039001b80101000318403a101c0e28886108103400700820100041e520300c3d10748480c40782c09a0f000e42c0945000300810406a11741060081c100764220301400d41c0c008089024081107803461140780c2c158010904100c820400703840c0a100c46200c3c000f0512100c0300101d8064284901d0180c104d000340d034090428081c0004000400504c030000750b109040503102001114000d2004550b034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 241152194 1250 241150944 241150951
    0x140709120803060108090f0a030c0b01050108041104020906090604140f1203120c041716150203030414030c0a11031b06071b1205060906010501050310090f0906091217 73
    0x401400c0012403e154030070b650761a0f000702c2e110704407448001c010456901d812484031051300000c4600b00d00f81d041000c0381c03841c00d0042c0803d21340000f05090507203d88115641300d946061089170300040190060f10b404003901c00c4c501c03004148546444c1d85e5013103a040750b42d060140c123100c0d19080d50358075018034004041320785440c4030b2401581400c0c4400c02031121404094221a20190180000540004281d0a00c1c607458808000781583c00c040310b00030b000144050f0800c81d0040c860006014005a00105695000c0c2c0c000c07150003178001080d00c81c07904500c0740003081981e9009000e081c4041c846078503c1100c0e00601501190407500c42c030007900c105904800900380d8400400c1041ca00803a00c1401c00b45010074070a080c0268641d41c9a030b078a4200c2c0325000080380c40b43c00c480d0820011b9a0240035183c0141001c0c20a0f500c1d5107014420a0004455400b0b0207050913038800c0802c2810b009940606d43c120b038400c804200006090404402d40541041144c0000300d440034802c4d06002103402c2c0501 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 241153444 1250 241152194 241152203
    0xc020c040c030209090606040f0e060402070b091e0615010e04060f0b1b03030402010516110307181503020918010608030304151802090c0706020d1b090f05010f0e0d0614070912 77
    0x74032801c0080881308900054400cd0380260240000c038013007507046900e6130003424480020025040d90012a5407060304103080004690007850400200c5000f2004540403940c00340303040e040000091000400502072a0004001407820400202d00d00d107170040109005164214840001d2880810140e920b20044034003c3c0016018461719001f09101c140c2000414410b944440340808c90a020a10780038a6a00941880c0c1208003040e40001943c86100100000e00202c0503002d820740e00429110070303020f0110b10040103451401c82d80c9546c03e40c0114054002d00060741e64a003850b04001e1080c84181101183c180d1520741042e581e1000420100400e039409480545203940d81c01d200300309a00004001d0320f48540030030444424202c6407140c40500908940310450f0301c00d080500134141803058010503074060464506106a82c1c1241e02c03003c582d02c0c10310b0014203a1030410302145201140d514010817043c2815051107564071000b00081c4205039550354103103000d654a079004c007030602d0000080c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 241154694 1250 241153444 241153469
    0xa0b03010305100506040b2d0603010e070503040507120b07030624050a0207080a0f2f0d0c0e0a05160c030c02121501090204050f0d0b0a0c020c040c03020909060604 72
    0x2800005103404c0380764003400c011300000314400c0d45001305140c0580d40c0300480380b415144e0081540035134011000c051191084d1040b900b07540c100b410b03003060010090518018802d01000048c00c0004c20441c600140c90f0995244400d511181b40c00b074a00541034070300b04003223400e101c0003162903104100c9401205648044103045110420400d462962190201e44211b0041180100b9003800800041400c18403503895095164602e0501c0e4441074188083c50104a0701c8410485041403189405203003080c00b02c4074081081c4441c60301c4000c82d06180d00803c55901140c00b040b41120780d9610040c446e45102c80114070b0310b449807000302d03045140c0c420002c010801210030000903082000303410440030020011541c0640340c0421710030981000341d00c2081b8080d000503050041d801c04642c1201d446406541c410507158403661015060b980007045651825a00c1207807040c3c052003000304032202031018000300548000010001c01a500c9448218016017a580115940c0d0402400726400c81d1400d034074a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 241155944 1250 241154694 241154713
    0x2030f0a0b010e151b0715050405010207030b090c090702010e1506030706080a0b040504050a06060b04121b0e070c0203152e0308040e150904080d09020118080c0a0b03010305 76
    0x484c4600c0f40c4081980007140c1804021000c2c08842902c03184000080010442d0900c1c165a508450034100c83c4001001418442081581d8000800c03100707507035005100c034103195541e2250342e1074030300c010300c900f94084410400d101d0116010760110921040e51425200c4140c44030501e103141100694003150168030103041000300300d10581020741c0003490305901048007440b80d00010207807032081d0313401ea50540000c1e4546041241d0340c0b08080c01000f0b450119401d2a02d8042c04010a0045410162001d04c40102500070b58050340108000351110706104046400d003c500200040038004049000c0d01c44d41038440c0c0490082c01c071491180700d010720503640140503805080303030052102010078031814001d10007000040d006009013010301003204c00b17284180380c002603850400a070881c800c0d002e410000d00340808078102c2ca003202c404060701a000314100d101d5200407141c842000d490b90151102601020034640700200395406420030481d0070130807290300c4080080d01ca110030b200051155001ca40170 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 241157194 1250 241155944 241155949
    0x70e150307120e0a08120a0507020307060b03010b030a080910080408220b0403030210140417030c07060501090c03060509250507080a0206070807020a08070206070215070602030f0a0b010e 82
    0x201e50402044480100307000c2c1c283d464452070844911001c43d038400d40806c02446d524011840540d100400b07400901903410204000b80d22032044040c0034085646940c0503c1c007507202500142c54400b006001c40d07681c2100c9040c28142500401c1000c1e00c54495141898840d0f44600030071405150004026031800c030036404000040d00207806841c170809080103001403a80e0700140904020740c000d401070103c0b540340034074090444001004c82240c046202c0c0900010820742c409001814000300005580d981780c1e10102d480502500b0002000d00c0d007440c00114000307a1030b8018515085403604d00313001c1d03242c40f80c0c10403188050444105207240d51143d2420724040c1c8500d6494028005414554501146c42c5c4414200d58842c01401e00582e0001050000c29644050016030002c1148082c006290003070b036543d820b611403120064413941313000c101082503503500d0a03505001144c0c0a0b03a565100c503036143c410040e400481c0e804c1030020100c00001d80b16000f41c041c40c042c6c054140c0d1080441041ca81c03c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 241158444 1250 241157194 241157207
    0x150c1b020612061906020105041b082e11070501050a18081602040207080a0216060c031809150e06010e210c04051305070b0a08010b0a020a0f0803070e150307 69
    0x820b42d0108041c50700201e52a1002d0744d540251034258004034043c0b0707082c01c1a0b010683e10505030440a001482d04000150001c6005c1d6100c0191070319040003001ca502c44144c2040320085075409a624100c8148090745585c402482803620401c02408076a907100c6102c01151520144121452a4000140d0009449070024400f1001100c0c200403e0842500070400f00e07007000360f041b21300c0c03070000400d10f01154041103105805168884044295400d07c00028803001112500a0a100c40d055448400c5004040424058042080100f010004008080c50007070910321400c40f081541c0804200c580d407203074200404215024003ca410140c14080d01b50070081354010418080c0500c202c80070407951140111801081e038000a05500289424641d0800909a000c0c0ea8212010060180c14a0700000c0d0a4110f03840c1032000c0e42c0b1041d003008241c0c20200950310040074502c1c500308800812403010301460045c1210b90703510078080f10b0042400010001e1449e81c01ca03c0e40e090000488041c441d54 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 241159694 1250 241158444 241158451
    0x118230c151e0d1404020609010507060b031009120f0c0f11040f020a030b09040203071505040b0f180402090a030b07090512010e0d050a08071803150c1b020612 70
    0x5500703440c08442e9000c1d5201c8a0440c01c040c102c44038002444110780040e402052040e060b003402100710b90500741d000810760302c81c50f02014144080400d560307090180c0342c0e020b07440540026094902d40000c16200000900e82d00508130740c20104555400d081030311401404c0800c00300b64540260410407a12403050720041c4400448424400183c1802e8584032801400304140e160100941c403050102c0c8042e05841d9000c10490103044070701e0411003d40d5002031000100c40121410080022002c2c600321030611554201c40c0f030b404e00000c0c00c294200252401030541342c0c0050204039071141180b0401099108180b0080c0c0c0c000140ca409001081350300390082c0d0448100c3c00d04290507030350303840802c0000403c184421503c0c0d5585081e405100018803241c041c201e00340c98076600c0c0c005405c4001c0c20600b40500031600b008420f5003c44140350707203a00c510b005035801039001ca5103010b02c01412030180004030003000010740002180001a07441e803840d0400e60750700400c00703800e2640d42c142c90043c100e0004e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 241160944 1250 241159694 241159729
    0x612063813020c03070606050109060e06030a0203041a1015050408060414071a09130603200310050103060b0f10091a0702090405100b0901030809010305070c02030118230c 75
    0x801030b0a02c0040304000a0178510700c2050042002c928200001d00960b40d03941c092010303c400304444202d1681d036481202d910020303043c401038481d207450411200b1186201e003011441002e02c4c0610110042a1840300b00304c0d407044402c15401c2800500443d5640103511981c0c0c159404040031800051040c040300f0260060307441100c400340d5440c0d10000048501106c403a83e1103800043c00074107410802c1e01c10011044200040c03201500c0c41d175400b14201c03d0f1103c0d1540c2110b04c0d0101c220710f540c081c0051440749601940600443d6101e091000c000c0131740918040c0300e00700008100c907ca041210002001281c65140e1907101c0d40350010500c505402c000359881440001c01c002d40040e501e204460f8000c50248000b005840362040004044032081d840803403040642c4001000001c100d84d00311504d4507401c4c6008070310b41c1c0311007a081d60b82164a410082d1b03d5420000d80005641041c0c80001c062401030074013610003d0b9104002d1001c1705181c040c1b15580c0c22800c1c05104d142080d111089441c41726 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 241162194 1250 241160944 241160947
    0x90f14010e030a0f09080d140a1215060305160e040e0a0209010b03011a04050609041e06090b040b040203250507120306150815040f061206381302 64
    0x5082080e080d0f61040c0d0620000c00c1da000c0c059450135a1001c080e40243c030030070005190704c00303441c0700142c8002d803413034048140c0960001e80040c0350380c4a9040500322a8182c1d01c01c0c02840041c01e1010700c0001c40d0b005190002e4644000a13042a908000c1089001c440352039800c118030f100000c2c0405042d40b0000007410f8804c481070f020040e103609050078000d001c4002000e842e5410030b480c0300031118440d0081d42c1003050500061002d652000220781c1e111404840024000341001100b84012103601d500841003032401000044903040c5030850103401c1022a03007001031103081420070041340404c1d1b440b81d4000084c031000c0c402c06005800c41d174140340c0c914109541000450307500c1c00303204460000b02d1030000c3e445040821582001c81c4084d42158000c0c1003132130441c541002c040b0703070040550f400c40c3e128586411400003400c4c01d43e4485005420300c9400d07918400e6a50404038060710402c00c8960105012001c0c42000700101c0c255914000010030000c010104440308121128841100c3c11084660 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 241163444 1250 241162194 241162211
    0x50411070506040b0709050604060f081008100c180f030213020c030c3d09020609030307050c0f030a171c1a03010507020105090d0c08070804031b0504090f1401 70
    0x80c20030503503116620132405168180790084006040b446154001d6000c0c06043c40300340500390300144c8411144140745000f02951f5100001e640d41e0306d00582c40b07080c050049507002e0704c01303d5450304038000710705490b1548105180f480401008414240c82000c41c60383c0b0840040c0014034044a04004c044010744000d0b04109481541c0d5046901225082c0001c1d40b20244401c01600500c4d81148600c00b048030411300303e881d8003007400c04a0702c41550300310010b5585400350215541d16080e51001c00002e401c81b41c0b20314030f07071501071395900740505881d108441110304244e43e40f5000070042607007944004030f032807254035080149034181c10210240190055480d00c03e00d0b144018800c420422880c03070f8840400c1030f00603040c1821180040e14540131a410700c0c041000360b40c400242407150045a02e81084007081d2810543c505019100c001001500d0005000061011900c401c00c00e2484200140f113829a4400400c0704680c0800700050040b400380510202242d18402c0042205139101c00210f00940b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 241164694 1250 241163444 241163453
    0x30f0c0d0f03020906070b07020a0b0901060806130812070909050408030619080c10020a050609030310090606020a02120f06040b07020c0a0e0c03040305160c090b1905041107 76
    0x82251581041039441031a242210503440416056200c009040c00c510708840750001c2000f900c01c4104c0904102c5c0c03074002217584e0034401c01040c5c12043d0090340e40300f4a4141040d446010300014419010030b40b250b600490080c032440c800381000c4130f40c4901105c1c40c0c5190a010a110b0110041400d41445070078440010103180314050700340300302e104400190f07480c98500e04110494608008802c030389002c4210600402d600055244021502102d12084842d0400c20881c900001c058008003a4003540062040195000000d14000d4080c0c0710f00408042c1c5544003242240c40c0c1c0e106040044e44405005000750402c61a60302a9100c0c810a0b03441500e842c11403d850a00141e9044a000207010100640d840d0705200d44101e40300200e4045ca0098030308160907090003405404402c0680c000004201090301400456403140305225503440030641d58201008014010703c90079011b0f42c00c0440e080502d1406056500300c1c1c4108001d84010306040c2414031009010100303140a800c0800c000840226 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 241165944 1250 241164694 241164697
    0x40e2503050a0c0c0c03080f0904020414030606061e1c05070e09150109210f050703020109090507050d0915090606170a050d03090f150207062a030905030f 68
    0x8540d180400c0609041d0b81c04001c40381810191010414000012030000390300c0042e02c01225003009610341c464042031a00007240c4500b0520035070051000800150010030710906128080c012816100325589a02c1401000d00c076401d0210b40c0707030483c9222101280c0c2d0050180c19148850898071007aa0a02d54007542200d009071170210124030700c101c18202501d4800c0c000340c0d01251404141a542202d18006440304c0118090184507440106041031003100c011402d110a0703400c008003440114860410036203501090005900061140c0c0c80807a0b13401c7c4c2070207403901400d826541d10340303404200c1c10218000c042d42082111040304640c820f40110311940591107119024081c009070182c6020b00c810303403e05420f90b944ca03285d00542c0e6180e0101e0004640d88840140c1420b01090a64803480c0004140380207580040c542c1403141c500c4c0c41140c080b54090034925110b8802006059204150880c0c2111726003c01d01c88c01c0a0211034542e280d02c00d402501605105408580c20030600c544001c12a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 241167194 1250 241165944 241166011
    0x70903081206100e06040902030c160b0403020d0305011215150807140307030f0206180406091e050f1807080618150c07020f0f1005090f011103040e 65
    0x4041da04801d0055070315002e400346122540e5400d00c50070180c003103400b089081c019841905140c2c0c1c1d0102c00904402100d60880e107160994041140b800320003817800760b1041d0000d0ba825401440b03000c04481503e8085d01c2100e050358140f13010120128141d666036030503442600354800000ea2a480c0f100242101d03c0f04280140040d03201428501e81043c0c10881c054001059030f034880d0b0301240041010030100860000c066806603095541c940301080d1415603402c0e0031600c242c0040c68120001341914030340d8440b8501440700440b0144041d00081c2d1881a17600565116405104c480c0101d10204842e0307030000429000a010f0b600390541d640241410b06004640c10300c800500800c07001012130051082c42401d0251078807440f80d0781400010032100c0d015078000240140d40250218074169203803c10909003c4d0004c00c092410302001d440281960810500e460042201c0c000e10391013580201810045da0a480d0000c4d0700b0145461048940c0140c0980103203c0481d0840d404840015481c020402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 241168444 1250 241167194 241167217
    0xd050a02130b0f031c14070b0f01050a0b072001030e01140103021f0c2301020a09140d0302060a0b010908030409140f0601020c10030f06030b060a090209030303010e07090308 76
    0xc2c0b80c038003041400841006151582d1007500300a0340304214001c0c020318403032600540d1030715100380b9400c2c41420380c59220710031018000340030400801c020b402005041c14182c1700203881d10705501d940c801480d40c65010b4503c000f0b00fa400304002c08a40140c180010623916801454041100c2600c442e9481c01c50361008840030b2107040c940014010742c240300700c076001995043d4103e4400146154001807624900000081c1074610301d50720740c96586420b004005425011200844d41e480c1581000391069806200f0140d0701c02680b10100708515140300c8900d40780ba0150041e10701c0ea902d00d845403000713200d021440c83c10300449040114014400700098400380501d201c00050711004000100d07600203000384a0350b0301c02c14000401c4074036680884c04030100c05041c1d40f019a02401c1c92415000351070042810314a03146000d00001c01d010030f001009009403801e41d55148280c1d1120100c0c0142c0c0f280c0e942458060b03000300010400007a101d0140f603403180041c80c00c800e40325200d07500c1071015072207040a02c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 241169694 1250 241168444 241168451
    0x5040f0b0702040c02030903060f040627030f08060a0303050d020c49180902030a1a030c09040b070525060b09060108180309030307080307090b13050d050a0213 70
    0x2107080920600c4c03e04a0705000550402e090b64000941c0d030640141441d2407e20444040790400c102038010a80c2c80221141e440c2c0b903044000080c90100300f804c00c3c26000a101350f040c8454103405400664018000a40120200c5007903440696142c1e02124034016243e41c2040b400303400800900c0701300308040218041041c0a103040d00224100d203103c9410210a40c0c030b02c503210902040841c407040c4014010304000040c0703070940d030050050490f40ea004800d900d00000400044203001c0d4007814002110480203180c00246005059039000c040d4031f515000030120340414081000c48290a42c464103615100d46065428501c1031111492030030508014001c0c3c00c07a44080008a000b00030318680144c5000d107103890180c00081003998064608040f24803542c0c01010361038402d100325650140050200d0341c4d21152454180550b52080360307030200260f404000440c008003050304a600c61080d0741c0c2c0c10b040b424141800c0200041c0c00b46c000f01d607284504036191005803201c4e14100001c840d1740384000f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 241170944 1250 241169694 241169707
    0x703060e0c0111030f03040609060902120c270622020708030a0b010e030622170a030e0f0a060b01030b090915011505120c040b07140706030608030a0f05040f0b 70
    0x340c001d51107990b0865598006200e1440585d040300c082d03e40c000c0d04241d021603c8040d03414000d0081001c601c000e50000301d4103424900c045000142680010030584d14038203120300e107030910600c80c005101e07800e42c00003c10001c20001e2501c0141da81c9112500551222420120b41c02a4101c0c2e0240d84122078026003c02048041070300761050305107030082820300c2c40c0f540c84e071500080d448030350041c00c50800c0084d07103003081c02c15510101203400700da81c011052044c1c58030b52007510005800060000d000203040642d49050740c02d0100c0c004e0180480e03c0000c2000000c25038612002c1c2102d420401d041640d41d940a481d6651410320b40ca0013918014050040344200c100098a401c005800458400e001141c1003650740e40c1c0b100c1124810a00701100c10f0040d15100d00300303482d81c41180e20450400c8004918101481411074100e5810100001121202940c2e1071094090340c07428410340b1140d40041c041c8100c298014005140300121034500f56141c5a22004c40300000542038200d26240718020400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 241172194 1250 241170944 241170947
    0x2120a0c051c0516150606020307060b010906140f13180506011814061e0301081b0603160c05030f0706110c030703110a0609060b030d140307050a020703060e0c01 71
    0x1040080001c00e07581c04a6081c100000d04244110104a112a07107402011030600032000c81307840b2141701c414800d1000c0ca03074440d0000c2d56078010f0201038542c3c07450980e24020355806103004904403060394440e0b20b00c05401c282401e40d150407582c02840301050070441010460b03c0c6c0940302c030142c150703003030f16542c0e0071410b4035140101c401c02480c0340e05204140000f03110030b21002040b00101d46e4041509101205643c000c0340441c02080402d08040594401145c10388000348090741c1039500ca90300304c6420074401c0400078000250002c44640020003000401c003003140c00050608051190f080080e41c1c03c0f0540d65240c03860780310007100ca0b100c60340482d5001c20801d40d0300984041a081550306810010f01c0c604281c4c6900c1100300c01400d01001d8000d0703e1403600e0600c1002d14481e003080b0704101c08030140c101480030300071080b481846402003402c9460304900500050240807108541d05081d556180420f403055408050b01c2020741c842c12a0000000c1c146009100c418542c4001038412034101400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 241173444 1250 241172194 241172203
    0x80a0b091501050918010b03010c0c14150f06040b03060103060c021e030901210609020a0e01020610170c0a0b1b0708150411090f0106020f0c09040b0702120a0c05 71
    0x100d4510820740380d0010032590303403688005500b159803541112080d002c109511030040c003564940d5a0194280035080c03900d180c200c40d5001141e0302a0b181c11030a40c03c08003035540c42e04283c002540008810402042100886030350042d4403141c00341c000540b41c0101c04c002f81c5022001d0380225040e0361204036002d00381e83e06200000a01c90290ba005100c8400c10010315100d00500b10100d0401685441c0c0141d00b5003c10076100340e000030008100302098844160340301950002c1d4403400810b098200c1e5698070351000508500c2204150b600c04806c5040010ba072400d081c0101d90268240309545e2045a180d50b0148010010116804010380d500b0081e0f900b45841403081680502c40c1e0002501000320384004129a0002c079a2090401c11650711031411004001d0506d08c0f141d0400e101c0f000300700700280c40d603c040f41617a5264088800c1407103160840d41e41c2e03d084140f81904003031900c01041c002028110340e10340182017401034600001c01030042c4440ca0300117102d01c800041c0504004400c0c00002d00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 241174694 1250 241173444 241173463
    0x30c0c010909060f1806051c020109050906090a092109170328180303050306031509190f02030a21090b030c0c0703060f0f0e010204060f0c0507080a0b09 67
    0x8005000880c54180d00390204c003060310503450340240e1500c261403201c0090b4000f101404005017030290210308400c0b040c0142560324030490216a80d07400100d200d01c1c2081d50140715480c020109039042d600c00c2e0380003001c2c150f00e180884a81b1b02d4a00d03410b65100c0c9401c070003040d0500d503903101c5142c00e1401c0d41d034120740c0f4001030f600c80c0300303800800540426810143e070030034400f003e503800460b5000800c50102c44401d10100040d802041d1102c001c030415500c10700171406401c0403000c4405540d040340c5203801507581a10122140d500c078507412000c0000044514000f80d0013581280c8021419401290814a801d00200d0b42c10410100c004200499800603445020061800301c00d01d90070b00e14914050f2001408c1c000300d02c080843c516441031803c00c4040050f66000341b0600102d40824100006400c0702070544580b03034188840d1107070030101407080e1802c4030000d0b52140700540541030103441d510102241a98940030303031500403990500412244142ca4442c4511080c02e03e85009240c0c00d000124 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 241175944 1250 241174694 241174709
    0x1060507050c0d020d030503180316050d09060912150504060608060c03090c09040206091f02010b01050c0c09060a090203070c02100c030e01050307030e06010b090414070804080f0903030c0c0109 85
    0x40b003010002d45ca41004a100c81d65160410540c1d9458000032040300c0401c0d030405803014070000403140800341892007120760701840751341107030034100506400340c840b404035014000000d00d07000c0040144146141942d14003038011813620702c0419606004106585040700e040c2c5030603813214000c2141400800040c1ea012684e10b91050031400c0004031140c4500c40d2059151003503100002040a6560708412200e4480e801800400500c05115070380d200681d50340c42c04c0c0055441d0041d14401c0d0750003402100c0211007404050700d5501081e104024030000003400307958004064120126003103035284015802442661106030150340c1500c10070103c1d41d01040005c041207041040000003a03000b11444008840c00d080a60301c0343c0d10080210003c0402985205251040303100000b90307410030070001d0a009801703442c11b00071000707641510544070704207440381c00029503640c000030040780e1100058461042c1125a1516150406000901e0340d00309161904280c0c0282140b8200c9603006200b210080001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 241177194 1250 241175944 241175959
    0xc080702060c030609040c05040518010e16090f09080703090306051803160303110a030911030619020d021309020d14070e09090304240f0203040f03080a02010b0301020301060507050c 80
    0x1002c00100d404050003a40c020000040414100064496040080c0c40080e0040040c2d16117620355010b140c87d071032205002940781c041840407454011540e0030901e10222070b8000c0b5586400c0c113020003006140b1218000030360303800c86c1200049205c402444094000d1ba94408040d0442c00c0031070848401802e40c04007882d85982000640d040030081c0d0741c90311074025000c1e030012000d0a06801a05500b104088101000108131514581580c0803030403460184078240ae5021228040c141da0304419102020503840d51002901000231a400608000044440260a02d0006034440b03500240581100c1445a0080b03664582ca84191180c8030038010308540c0c400413820036410240c903803402c03680000c1c042d03015680004c0c4010ac04204a43c000c0507003059410b00109084500020001c1d035010401c00030786101180d2000c141f00105440581c0c5020604001d014556980d01c02d059000d0340050342903540b075542090440e51300f880554000c102c2c580751039603140703c1413a01c54103084490240c00c0c401d042 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 241178444 1250 241177194 241177201
    0x70812030f130c030602030712061706090105070c021e04050106032702011b0311060103030c02030d09050315040f21140c0c010509060d090501021b1c03020a09090204090c08070206 79
    0xc615183c03000c691300004016540e44801c401203441c031380302d110b480b4410307410010000f4420090700a07c944060f6004240e0380346440720204c46081c5d0b5402d807907080000302040034200152a0030080004044500b11446281d40c08000218080d10400d91000c030102c1c0d070340c80300d619626070311815504101d01b0006604081c40c01a90010b05207410f034504187d2030740d5039200410101030052094160642151007100c0466a613803400400384000b40e00120b02034001d0301c0b4054a000d0003282405d041d5a0300801400000c000c81c01001d0720b05d000108107032012104d04c061080403500183c0c000a0300101030115012070034400c3e00c0500031084000d491000c0342d000b01304d02c44651b100412055540c003824031700a13540c0c07500396000401314000d082c2e0484680349050310741000c0150540c01802989807121080c80e110030803c2040340c59410761032000d0007000e440d095100e14036210b0b0340100189011414118045612501040b04981240d007084400c250380703881000855401a0300c5690002261004003181d01d0f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 241179694 1250 241178444 241178453
    0xc3003030504020418020102120c011d01060602191110050f070308011406120c1815040302090f0103030509040509100e0609010f02040521010f0c210b010215040203070812030f13 78
    0x42e050b4127070010050218090200c50003c0d006541c2ca24618000707000302565245c0c006000740040c3c440c08015100310f0004034030341c081e5200d400c1c101507080810b099007000320f4402d00141c60854000d46040200c10070034460003200e01e0026007010360183c0d40305103007036040400c4055031010b10b007400d505c03c010510080c1c8034122021781882e440890f000046e03880380c8100c075407160503002031496190302c0b1581c1520100000361090103003084900850300c0c8100c0380c03541200c80c410100c00b0302018002403010410b56005040c00e801032034001c11000c0c05c4595040340b00314030008403481d00c02100003641009051207600c00e004d001c4c02070042c03551442180f5144c81e107000142e50340e003400340c41c0005884104500074180001c0d40b19000f074807100342c81441194100391000b03106031100e50b40d24214260080800804d10402e1082e002c003120103800420b84d4503080d01d605045c10034000d00032645070cc54001c011900c0d1400b40860308513500d508410540300e007446d0000c501c00d10300c020800b01d54158089055000b14 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 241180944 1250 241179694 241179703
    0x901030f03030b0f0a030609050a0b090d08100e06010807140c010c02150609010303120f0203070e12010605011b060908040806040507120503030105060c160b1905070c3003030504020418020102 84
    0x1207900c164001200c007040d03d0b0441c00c120071541c0107402f1f030341c00c0000c0108034040402c06002c2c0c100d0699559a040e41d80c5a10800d4080e81c902030344c00c0307a501600001d94554000c0400300d40104080c10201d00060030412007080f60f501044070f0714040d94507a41e884841640420061442610144075040c0500d0030b0004991a140c0c1440041c0400c011541f6650042a00f6802552400800d080035581d134a0401c01c00340100402000c5240501810698000d0342c00d4180700320015074005a4802c2d0315404051000c0704010181d013000c1d035002d9a600314100000b094034008000402c0100052320f5280303441d00b8801d06001c080d5010401308590301c421f281c0000c60200840f03056510845456440b41034031800145005505149505a1a440c5601103001c501040c080c100301441c03040f08045c1d48002c0311045a207801440130007442c038042ca02042c04217842c011210118481819540c8031038000c00c8501c0701c15800c245c8403c1c5e012036030315003d100640c141406190700c003a08038100c07a00e10211990000f0b642c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 241182194 1250 241180944 241180949
    0x3040303020a14030106020601032306061e040213050a080303070e09040c081e0d0906021c05130603020c160518071e170a0519020c0a020901030f03030b0f0a 69
    0x1016800501d07140b819006101c40d0b00780071003c00351961690384504000e99946030a020650b21002064000d0700d110b529842098450300c0ca400140800791100420b011888821421000221610b00d0210025807107510180c00038522204007507001a140c0018001180301d65045051640c00800400c005c040d085044a10348100640e40119107070340e2814103581100d9640c000710710302d000e1039044151080c2895a01d1519590030819200e00195180c0162015099403140740050f820100c0350300300741e007141558103200c4062800c03c1c0e0700d0702080102d41c3c028030b0030640040d00402e502160448940308204620590794501035907560f071090400c00084d50810b0b1000d0f580380101200b80015003041d00c81e250800c448103031910710a10940d48014003030402c00f464034246100501000c0090148600ea000d201c3c0a11203801c1c079000390940d10b100d4403010390700141c3c45e01c81a104500d200c0c40140c41d4904c54a0083d0301445c403501072900d4918004007500c40e0310580700c1c0719501c0d00603844d80650300d8101b000304 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 241183444 1250 241182194 241182197
    0x5060408030711060412050f0d020304060e010c020301110c0604030207051e060c1c020a110907092d1d06190902160204020708070209130c030303180c03060c02070504090503030403 79
    0x1c4201c3c0c0c1002070030714032581e00807221a1092880300d00c10400d0001c1d8020070030242c003041e2001e404840004980d24002c40c442d00002810480801c2125401400914642c03400030f400418841c1038144001d0f56030b07000c1c0d031071404198882000c100c20b2543c140f0118003c5d060443d40024940900c5500b445426026582d0902c103880004103d00380d850100210111700f000e0b80711010640e0040400607481d160742102c15aa10000b04a560304e00f85849288180700d084284c0b10b51548909081149901e401040300101c0e11a110001200e00c900c4000a41c900400c16130f08005503030450040d6140303041c41d000d400c6500400f000e107039800c07540c11442c103204182c4404540042e12424198034003055440d4811010b9000b42c40061003400380000d10f001030007181d000303031a601107603200c40c200424000009500545a051105020720000744250010b048000358002c0719180300040b600c40d85200d007800c1c1c0c03040380c246588444100409805010840c01060121810448001181c82d200e0301d9110081c030060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 241184694 1250 241183444 241183463
    0x1030203071701080115080f060a0902030304081204090606030c02060613110d020c0d05190e0f03100f050603030c071401031805010902090c03040f0b150607080310050604080307 78
    0x84445110780b0303400000c04102415440256911414a4003c104010b020301508000358001b061401c000100301c0200960740c8014540e0b580c44049505c0104190b900c00c9a041c041004000f9486400300002c5d0b0724140311040080e0380b181b070500c880c801c0780c905500000a0600f858091007000d074000c581158080e0094a5000d050345a401c2080024080509141403540c0082840900301a41d0390260000e21055800c07034070251003c20040e90030780140e12020300300f8180440401603082c401d581050500502900036441d040c40c3c2c4002a003408120000c41d04941c3d55060003210482c081c1c09416000715090b0051450072812071882d41e120017060140c0100000c14a0b03280f942648207900c00140044880011304501441c0e290042c0600246c5a040c1d01c00d104a00110b060209040b003100d0117280d2001c0c480c09400d41ca039854020300a00140b900143c00010b650380c0e00070f43c03217960003007010910903084296a45040d5418586410154210a0040c80140024884031318008100d4038903640241446 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 241185944 1250 241184694 241184701
    0x1080705040803040803220e0403030e0c060706050a06050a181112011d07030606080f07031409010b03070b03040c18060503030d0207060b0111030d180503071113021801030203 77
    0x954140c820365002d00741a11000900044644021001e060750755012032083c2d0b9401d82042c4ca043d01c000282c0940e0302d4045113000860006030107684000f0141090005440c44e40d5030901c0041c102c1e402c4684142d0f800d6440d0b50401850020070301c501009048200c40d0152480d0900001081101c1415592440a991850a4113008041000391004125800c040405540c1c58140200800b0084503000c0e800c401e0700702c08215018040d004007400c0e60b501e0b98171014660b503200c005000750000544000d00781a60f90418115041c0011a064440c0a13524004141d8050340024945000080d81c05034001100510611001071000e0421000f12000e05401e5035242140381b40c0d0304020450381d0300966043c4000a1341c20521201c2e0b401510810740150010003844000e0001590941801204040c80390400c000a83c91040330340d110441441d441801901030042e2680c4003460b51b840810251a0044100507021040c503020401e4001122221401c0d4186402e031a010407802444010701d030306064010001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 241187050 1106 241185944 241185947
    0x1090819022d010c081201030c0510210938010504050601230f0d0203040203010b010c03120b060705010519110a020c0402071a18010b120c010807 64
    0x1d030740e80b2505400450f0001c0034050b040380c0381001070042c0c1000800f2004594042c500c18501680000d04000802161034a4101580100075020b941c0c40340701c141c2090106400c0e46c4161010550040c545049184410002041d130440c0750070041039504984500700701d5080c2c080b081d40042403640c90f10180002d80381c0455034030b400300b19039602c2880300f0850389030540c605440d05141c017402c1c940c0503013041500754011401000d845070040144015407600b1300c11a0301c40030090030181500e0311030b5500a08075070045500a4043d070b941c0d000c01d54181d00c840c02280c0c041d680c010003c120074504143d41d01c18105038078045603e220301e03160220200101c0e4004980c07101110350014850072006400f0800607610000086801d0400d0301b810310400c40c4e100002c00e00429104032140c15540d01d195402e42110101c084292169030581260110154042491b40169030203107031030b01c01d50392035200 = true := by decide +kernel

theorem cover : BRFrame.Cov 241007194 241187050 := by
  have h0 := BRFrame.cov_init 241007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 241007194 ≤ n) (h2 : n < 241187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
