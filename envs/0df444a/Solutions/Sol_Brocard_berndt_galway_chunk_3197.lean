-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3197
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:57:10.546882+00:00
-- url     : https://prove2.me/submissions/e48509c1-c822-4b66-9e30-f38549eec90b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 574820143 ≤ n < 575000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 574821393 1250 574820143 574820149
    0x3070b101a091c02010909020c1c050c0606031903050c010921080121021309120c02010207050409080912030c01090c090f050c03011809120504030302101404030f03090c090608100605 80
    0x461f03058220141e9074100100c681400c4c0f51010418512052440580841955114000d030011300c600c4400c44009407150403c0590318010003c1043c40c5800017070030b03800040e110b40080c1503004408000840c441c80c0c0d40d521a0000c0704005076100310401030440d2005942d900119a5004041200070380101c0d498103605209075404900d0064040d06500615101c1d11005038081d008150304071000789450805110011300b0700071401402d9006108020b4041642e103810712924a180e035204144510301f0141c01c080c00b202201c29610a08a40824403556240c54801e00840d502c41e403240070728241c206d0910000e103003280c05034502c03140c00b1441e20080190385002642103c0c156010a0402c0014609821503540901001840100b916807807031081141d854000b0040e205584c030a80070b4400780b00790444814229403070410200351240224000c18040790242005410742d420f1490007003100d516980f02c600901c1560f42c803084c0a1940d41c131003084203000502c80301107000950101800018686000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 574822643 1250 574821393 574821407
    0xb04120b0a1e0218040f060f050102030c19020117010e070f0f0c0308060a1e0e0609100323030a020c030d0e0306040b0a0b0d0303050a0501090e03070b101a091c0201 72
    0x3140b0002540001c14901c00414092403c00e1810020070500c0440080c8a080000d84494451241000103403480441d1542c0003009980190344428020700103403d05044000b0307a407031201d5059045c840c1c06144009100010086035000c2d004041c85800c0718103100c03400130b000e040718004a50800c151080381402550344240345000c019014030f041520740c2c4a90000030320740d0ba180e5200c201c4001904201c1440d41c1d800c99007001c11100b586849840d290340360428411141030448440782c0b65182248148000f880704896240409034140102d1207000b202080b1a156910882c204c1015a0114400850520741000129a2800300f46031019401d04000d020954481001c0c10080255035032500080c801038280d0b000e0f050841d00101500b140c03009506016000300f106480d40755005060100118040410b4054203141c40050801180f501c0125100c0100c0b04001411806500001c1000011081c0500c003420789800c4816100329a0f5096034400c1104030785d800c203000b5032001c03026054030300541c1e08580 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 574823893 1250 574822643 574822691
    0x70503011a1216110f0703020a09090f0311011104030f020f100203090906130603080a090b03040c0b0309100c0f18050108060607030e04050a1b1d13060b04120b0a 71
    0x10486401d6403104084e1200300c10310b41d080703809201d5102000000c0c140001c076107044034000c1e255028001c0d100c8003410b05480c3c0c1400c028103000c0e00e081c40e44002a200d40b2540031481007507c0009102400c20880d64500c0d40158005d44a088a9140326015843d00c3c0002010f04101101c2c00d0040a8100202a483c0c0c02400c41051107005064005426a120860420087d4100e55010004961240b402040d6030300f10014001c001540244045100555501180e0295800c891f8000c0b20303500e025400406036000811000c42c03401030404001c00c041260250b040301c105592100400b101c40801c2c0188200c2c107400d5a0074040400702010130842e6007290410b0b1700500c040d5201555001e50b428251a40b6540004d0035400c240b9100c100400d800340c40d400440da10020071007a001d0010b0040d002c030303100c0c410780b005000001c008c0d46c0448250300d0711501c403a403401410304000c0340c040c0d5140744074501c54002ea0700c10801e03807600b40320035802c00031520a175942c010007415040243c03040c0364585410030340c1071075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 574825143 1250 574823893 574823911
    0xa060302182d1803090d061508010c050d0221011401020114040f020d030c1b0911130b0309190b070f08010803040312120f0603060506030703020d0b0a0b09070503011a12 74
    0x1841c64004520910445416400150804081d46c0191414000030b001c00401c07031205010202c008508400180202c5000380c00720343d1602d0800c090341e200600203510517181324a201441c2880340186007090b6854900031700340f40103094a40c00400740003a003500d001c0e2403000c0303d00c0c68800402000400707039090140207a030140da5200e9441403600d01550f20102c0301c02c0c094010300d24820075036a081062210017060350090b0005000e55401918800a180503d1410001c07005002c403041c04000c1501d80078660102da24822920039010305c100210300e041003a801540c0d85401075040081107504038010313941d06421071920608942c54070400782e48034000c030302005041a5075080c2140300e40744908004e0403000103a05040026098a03500d880c003c000342c0c8012620941424002485858045903180880e9006460303078003103034040c3e0303211101900c00800385181d0741c0d80c03001c50f071080e80c80711394402d4443d1502d522844d9407075041000f02c4c130842e0400200481654010044e10380d85c060740041c0c1d26003109200e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 574826393 1250 574825143 574825171
    0x13152903070e030a0b090d0311030a0b150d06050901080703020a1a09040e0607120b010f12060b0a11070e0c07060f0b120318030f0d080a060302182d 65
    0x51007200c2c140210149181d02d445550728500c10300c807950070030a0094060710110361b0b0303012817000254240c9224408120750b80d1801d100040402410b50410100301100805042c6802f0002c0070480c415081000d08443d4590394a4052206042200000b4003514042004082051030359000904400f40341c002c403100c0150390344103690741c0b00d40742080e984400401032007072001c400c454032a03d03601c46c0304403040400502071130800907050707407a4400d0380c012103410f035201c4001c030310414400d440c1e40b400902ea40b00815502c840004142103690054089060740765107422003005007082171881c00003240c02c0b5158441c1c40d2800c0c0400c00504204072082d15520500c04034844401600400003031075044034a6801901c80011400d94507408001405c500321002c500640c0d00298505165403455011101801540310781c0100404038040c000803a4070040708000861656100e901244178100c0050b8485191000360f0309001001d040c162400040050300c0303011401220354254011041c0d400a0007040006040d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 574827643 1250 574826393 574826401
    0x81b030a0203031c06210302100b031209060c0115260703060b180705130905090c0607050f030c10060b2703010f0216030e091003080a0e13152903 64
    0x180e504100b004105404070354914610000504141c000c0e0188214010301030403270003101c003046a109050140700c019005090851211342440c1c1ca1794003913005142d010b10140301449008030240034071408808d421013020503d41c0781515801c2c1e2440d104150000c6815500d490642c40307000051540d0489400040c003050580424002c030b00070451803085c1201c50f4142c030b01000f51207038010300207201c03100303400103545a000d5459103500c0c1214400c0d00c0c0b0742e02540080070001840d2070b061001e1b00c4028028000d40360071042d1001c0d640c5c595071081a41203d582c10004821507040124400c1e20018241d650300607241c604801240d086003800d9840e10080300f0903030181c150894400354400220300740c1e0300c50215a11540c1070944640c3c0403103040c048002614a01d51348003207041814034503015500c0003009006260659685101c5604004004810442450580e580c1591000000c00e02034503c00e01c001201d60001d140ea5081d4000764001070381003410500b110042861580704446c10410b811803a07078898503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 574828893 1250 574827643 574827697
    0xb0108160b120c07020d02130902120c010503060d1e110a1401050d20040f050406080304120b06032b02010f11090603060607020406030503030109050a1a01180e01081b030a020303 78
    0x1c2e1446c0c00b94100c9901620b4100600e081c0e400841c1483c001c681c106d81c0304425261301543d8149604100b40000c1050022801e0b9007441d02e1401c440c070344100054841d0f144801d01652150030100d0301076070900c000c15490b4410381400040d68001e46025644030010030b03a0503001034198400e0f850b006940c02d40d290111500507400e02c5807003045a101804080d61155140c60714401100b003401818820f502e800c20024005400000312000c130b0f40714110614001c41551100030405500420064042c00340d4a9078044c1c54403100101601c0755038030f01c0c2c050b4065011311402400c441c150300343e003a001843c0c40d0149070f0310610b07842913480b2442d040325440c0da6039452002082860061080003500981041d0b0080100038003c0065816100080c508000d5550381d440030030281c81d48030380c43c100b02c1c5603840085400c6501c107810710001d03030b02e04007a860245e558a4200810b005400d901240c840c0d00b00b1610b00100703070035081100d21381517021002000200d2036a00003945030b11880d0085c001c1c5040d40003c80180c80c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 574830143 1250 574828893 574828909
    0x6041d06010c210201060e06030c1e101d011419050f0325170c0708070209091c1103030f10080a0506070e0d0b0708130b0108160b120c0702 61
    0xb64448020103d5a000d04a03400c11140c0300c09004000d5400c0c694045400d2100e8480381d44908030060042603901d441005103d40e00384441400b000c8800c070504919901e03140c101203100051201c0c0e8820700001c0079800341006c1d0311000e480090400240303c50462442119000741c1c0d01840d180342c0344006003101e011003660742c2d00c0340ca20300b01c0f003608010040101c080000c02c020101c142d0007403004c140e130445814040361440c00741c00750780c0c1c82842d220022074001ca22100c080c068040c40b80c900316180c908a80c00003824003100f2906100d50b070348402900c044000503402d46c0f01001c5100d060441c070001540900030344901004144404180031400004c14030481811390400030a5000c00b03503603070780720241011350312060120380c0b500108054001c0c40e42c1604000542141c0650031000419007500c68000c1154105000b8000614400d40340d40f002c404a111061118004c14440009000c11440d4040b5115000501d42c4540d82c038007400e00404607071004a40030103a100d95040c540c1c5a542c4103520008907a1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 574831393 1250 574830143 574830167
    0xc07060305070c0b04050a050d090e0408090a05131a03010c0206181509160e1324021303050613020105041205030715021209030c0712060605030102070f1106041d0601 73
    0x611140c0c240021b200d40850300c1f0001c240100c003034842d80c0c0d158050075140c3c008c851040300c0d400401c020014000c24070400c05041c404400914210541e581d071070020b140d160380301e05071262065551072603c0e407004403180310102c1e038181030f4008c2c4112142c034417001c1e4481c07800808511441200070780524031a07909000c1880c40c140084200d011724200748a5641e6100c4800d29000711200a03410701003452590303041c26600c201064400e40d99081c800e9681c0300904207040d03040551445d00d5668181c0e07240410b00240401002d5060b046801515504140f0314050010b010160101421220300c0090303640032007100c0a0303842000f1560424141864103c0c654031500d9000f030100c0303100a4401c0c5180070781d90007c204d060015401c08096480b6104c4468580c4502402d042c41a4410318041025041c0c0011306880140518000520340b90340c0d501107426603006a800311056101c080746c50040000009184201400560703620b81080d00346401d1140d480101c0c407134103c1083c040310004099a01c581208011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 574832643 1250 574831393 574831403
    0x3030901120e0601060c0c06023405030303070e03010506060f0304230d030509060f06100e010e0a080c211e030c010c030608101a040506011202040e01030b0a020c07060305070c 77
    0xf156039115030003401085200000c64805100700000503009100017800120039840d4200500a50881c2c445c1ca200d400d1400d5074460b41c00301065000440356400d0018600c81c1d0101d480c0e54004000300010503084400080000784551014000d91180036100130642c4d511503400f1026032000340203048981038400000b00b0010913442107203100d5888590580119028070108811038005842c0c0c800a480c0a0900303c66950b003080c03004e039030802000c0c800c3c0d845212940c418101004080380000c0420480d84460304110080e03806280482650700700a05021b01034143d2840c01c1a5484941c1c0c2c036203071502c2c01c02401d080c50a2401d850104490b1007030086803104181000204031310340d500d110286c06003010384200c0c40340b0300031904042c10011140c015000d56950b400300d0300c101044d034a01000000c03c400341000c3c1c1008101c14442c1200c003000e1001b0405060400b0340d200c0c103585145044855820000c01d00c00c2240c3c010321040118040000350701d41030319114280410f240d82d80c1c21003190744002000001d40303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 574833893 1250 574832643 574832653
    0x10212070609200f061317010501060207150e0108040c0506070b0702011107033501030b06100e010f030c0311040b0715090506013303150806010503030901120e 70
    0x100141c07a809031481e00e204191000801a040a0048221510600181e00200d0685030845031380f03043c1d0004c010710018202883c5000f500d45215030410440301d109135229039500c00062102580401c02b40b0300821503a0700d0906100014800207280e400c075000e03950b0500c60103001060030446100740107030140001824442d01c0c4c0700c1c6070070812401c0c4800c1d912040503520704007088000042c1c55048411564040e150149404002404080b803100085c5501d50115800750408211071100c07141c20f4029400b580300c004090603d0000c0080d0300a9041c0354034103200100c403c45440d07981240752100700601c94100020b00b8080c243e0190050841c85c4155602500d0004001c140802d4035000392140c203014500340b402d00c41903d80204210b921040340a07110358002c2004002d00000e501e103031044020540301440d8000000154010010700d14050f400c0840e0301c40980240d094041e80d1400b0003085918003c01c0654501800300380c480c4910290507040107070320104078010b060f4a4101650200f030402c1100c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 574835143 1250 574833893 574833907
    0x250308070302030f19030c021902060729070f080f0a1e06150306170c1513141815010509180709031506030201120207050a05010e030301051212040b09010212 69
    0x41340078210b0101740808070b407030014855209031000512129072000c00d0608041103021303030208030f045e070440e200440300100c103124010b95010080d2903410100d10b6018014042c1c0c05c0028020701840550080d81b02084000c80420443e407201d48041a0004100d11000a202860a1110100600a41440a40504185002807841344c51801401074007019038040140319225140002911a0590410219400b20803c2101ca203400340001c54860340440030289064242e00c0c80c50310000e0640d200089445243d40141860304001140c400c0c9011500385030001032502500422610700c006503101e0405c14041040c00954843c070f000c5d41400c10103401110b11502d0682c00040054070303180070407142454045480d01700b06180340100019030f83e05841e0030145001449d070341c0009400949003074030a84106d006800c0030031400c0c41850012001400034540d03a604060034801203c0085200d6165a030013003041c250000c28040555098800740b54000d940c407010000101c0c94003101c40079800841c90001603003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 574836393 1250 574835143 574835167
    0x807050901030504030c020315371518020d06050306090d0f0c02190f060c08030c071e060b090c040f0b030705040e090601060215010e1810020a02030c250308070302030f 74
    0x30b02c90b030071150021603410280480c02040803841113040070303c500d003036104482000480c1c0010300350f000300b41c03400412f059a41840406200a2450302055070b075002651a035107105a00034440505410303001000d5034100b0b070719201d075102d02a00c1920200010040b01c620454490076440e0344040d0001c3c002c1441c0e0045514050825450b4810612031550f00400021f40d00d0091107080907240c2c000328584e056903190001842d82da4000d84040b200320b04080a04800d01c81c03000b0b1100c441500507480003984480900a01045084c0a4005000c0c03100a2000300402c44003170f00c4070004d80341501c3d05240c5075150140d090b5158000e42d006000326610b06002c002468100140c2d981c100ca0041c0d0890b4810400300d100c0383c03021402070007000f140c0c0b502c49000030701b40500b030303946031a40301090030842e00b01940021803c41203811003d10f83c00142c000040d1a040312204001030600418248810390080b025685288041401c03484001c002800104010080c18001d1040d54290f41c1c8542c803195482c0b1401880e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 574837643 1250 574836393 574836433
    0x7030e0f0f0d02060903040b0901030902040905010b09010f0503070b18043303080d051003120c020108090706170c090a2d0b030604090f0c0b030f070807050901030504030c0203 77
    0x7807100d03481654101d000c2e1510004495000315400030145144c6400d02909004561180d8500d034185915940680d0050311580b103680504e602030400025002540404c0080009069112074041105500244001e584c041030032002c66103410100b507952004c031140f0743e00c244c0c0b122403644e6009141032142c4050340400b4001c545640d00f404000c000c0a64040034031100280b0a00018200351024802c141d240c1405130b11041d0000244240842925501d60302c0c00c0c8203004200e400800a80d42c104038400f1560044034064100380c100b006400030904118000b880390111904200c180030342c0c640402d66900c0c1050441c5d401400280031074100d0f544440e00301c1c1045195620203c1c450f4030a54900040340a030307460301c2d01500c030260b40382441d50b1030301801c00005c1d22031900240c642490380000c1c100003802e20b1210000500e03070100e03025120300d815105803800c40c1c0028802030511102c0ca040010380c50303001c0b0445070420403d0800080356107550078115520000c100e1700030f40501c039000004001200c1d2050b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 574838893 1250 574837643 574837663
    0x120f11040305060a022706072f0102010618050c070f080405090f06010e12010f1505030d1b0618060e160807140d05010b2805010c03120507030e0f 64
    0x100b2600e6584600d00c40104038420014001c0102202c8001042d0f403240c0f40408180e42c42001f4849420440584c070745908044d210f0008d4010042e2142c800b40f24070200601100200c4824002040f50754504810819409066168619460307134850006085040322010340302e403141c1010711440b43c011b152500e83d03544c3d441130050342e11130054100040d001845025515200d004d0603919060f140c0c56403401c1c0854207404820103001c40d5200c0841e642c03030301b0b01480351000000c440c2d01451522483e100505003040c0b0f184501d20100202c0229882412600c0b0000b1114641d0000c1c1c0014865031400101610261081d4001c0c229414803200e54034502c0c1c00184039190300400c040803a43d0039a00c100407942c0b00d01e02c3c42003c5d105101c11041c6401460885803049059005100124000d09414001660742c842c072040b5454042850303040a1540c2c1c00b4260000140100782030034174003103041d81c4010b0b1007000b01500011085840d40c001038045440f9400581c070f0740030344200f2501012014043d40da10344420742 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 574840143 1250 574838893 574838903
    0x40b0d09030e1c062d060e0a140f1005100309020f0a0513020c010204050307081c0206150d020102070801052e03031e03180c08010b09070e01120f110403 67
    0x144407660362074511240c032041d841440d040b080b080c0da1940d0f031303402910320f0910780024502c4103001307008049424007001c4001c1054120001e980c6051013000d000c00700c4044c100002171841c20051440301c40d45500c05c2c1d40c02103da206240d115550382c2981202084042e040260003030080b03502000e620f501a0022000d41d0300c21910040c0c070307116407024040307041c1d101e204e22580003c8015022803100c0340c0303038001e20340140c00a0000d40f030983c03900082803512155501c00c0001c1d60100c0540020003038422a01d95601030709102916007801c040d602e818601e0110b980e1700307204044120541045a0003000000c004182c2c42009014601e00461001c1044441e8580201e4485407a0320540c1d424803a08402e9064941c19210281150305155500036a1840b007020402419980d091410078520320740c0300d05411500c039801050540742403048403402d582617504a0307030241d51507070300307001131143c020801d0711a0030030a190000587d0074040301c0c100074000f442d4020707060f5446c0c00c00b07288a010505c0003e00035640a4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 574841393 1250 574840143 574840157
    0x110922140c01111f090203010507050a080a0212040b091c110f0c060403080f040f030602091c020906241c06050303030c0306150405031c08060109081b0105040b0d0903 73
    0x81001541c0c2c000340c0700d003606802c0e003119403041580d001c0b00030001008418090002117043c01075021a007155000d807410804100c0c00b00e00c1440e0300380d0001446074803180c1e80a06604021450032007008201c00030f0030040000c00124002030404408220701d64400c441c00346d400300248a1150b024240442c2d0580044807405101c0c0740340703d008000192b2450040010f401c03d071a0626580700c8107010f030045581c00c40304c0c0c0002c110015204190030110030113140640001642c0701c02d50001c201803010b00380c40030f60501800303241c49000b603034130700700f220f5070181c816034050f000000170100c40d450711900e01c80407002c0b00b5070100f03c0794000c4040288903020b14500c0f040804c6400d485400b05030340c900003100d001c054076000700700150180c240403042c4c0e074440307104d184882c0c141134980f40060b003406040780000d03064909145004c048207902c030b011207400c07a8084c203091070781d5424503610b2900e5801141070044c0307003460070301004000e900c204215002030201c400860b0300c560707a920091000d0b100d10300c400d9002440b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 574842643 1250 574841393 574841413
    0x114121003020a05060c101a0d06050a0510060815030304050a0608090706050c0a030309020d1502031e19090c0e040c18020f1801181409010801050411092214 69
    0x1417821600464143c0c40106500003101401101034102e054485840084009040c00307951124007010b143c0c1845204040303401d1501d4184141100c500034031081285e0100c0100b00800c940150002d60000e0001c00e01e022611340d404007113880d5100d15403119402c8130607880c0004075030740c1c0190b03154001d0aa040a41307441c50345c2e03407508650324001c18081400c560412802040060300a50040031503510262060030504429214200b0824410b885862055000000c000c42c900048a031220802c035107044500c410301707141040301000781c80c3c0140107184607500c003c94024400c60061940003009005803d050030301e0b285c640a024402d46200c3c0d007400c481150b295480d10402c83c000c5e1130080b080808502d040c40c16141c00e100c00d0811210055050000c0304940d0b110003c480912030000d45503604045050396241c0003404190034059102e9051645003100744000140c50401d487c6a50004480b25485900c0d01381400c0389080b02142810b1460112541840400250705550801010644103507660b2040d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 574843893 1250 574842643 574842649
    0x51302040e0c0d0609112104050d0e03010e030706090209070908191407030501060f0803120f18030a03051501051e0d0b03030706021201050114090114121003020a05 72
    0x49004440c28a1240e030300085054150304090070f40d80c410903001068a9503030300740002c1181c00b0300c01e94102007000000c503218041f8020400a45181144440740810325198550b19201c0308008503503810000e624168069a075002d420034511a05804250781e541c10262030100010102c0f01c804a003c1c00301000051080750103000c1410031510204041e10314102c6220010f0303081c1c08000030841c0d21040c1e100f1001000c0308200804000b4621440c00040e8041c2050360903244c6041c01d500080e1207603c00c10114240540740c0030180c3c0c00c107100d00da40704940d403101c1044841e032840001c01c4a100b440017140c205160b641c140c2040f4003c030604440da03007803001d040700111070034400c6000c0c480c82c103424001400c0455151070000d041408040400140c8044410002070860b4010041622101c0d008900441428612080741e8010282402c000104030701c08921902035000307545002d418040780240ba4107200300100221401440000d12040d450f103403000d0b8081d90313048207004c00d13801703100d4452001c20981 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 574845143 1250 574843893 574843897
    0x1a040f0e1510050409020f12130b1006051b07150e0901090209030303040b0603010b0d0503190e0a030b0c070b0103050109141b04090512040e010920070303020901200304051302 77
    0x200b030342e0b92141e103060b04000000000c3d42c0403070320742010007208102c40303001410340d002100c1c0101050101d541c1402d01d0750030b020101000180c11410307141006031040003803076080011100c041307400401e1038149401e103403640c2c0c0c20b103801130340302d40c8140026a51001205502100000c0151011901540680d0b01c5209200880c000c0c103003501e4041e4010000304011035420f003030180d800200103001160045441000c00c5101d80d4800e403c4a09900104420f190100559030441c43c0d01014a0314010801e0203c00007501e070441031002400d2502d40c000461000b40507581203a000980090154801d9656071410074000c00d00c00c082620103889044846000c4035010412101c0114042040300c082e40780030082000030312450504039010311070030103440b1021404001a100401c5c5103600c4022542c5069852400d403031403103402850100c1d008150000100810741603a1855070186001600c4106881c0182d401c4687c0342035101c041e01e0b4a1078031b101e18030b000200070001d43d58143e411001040400b01c64200f68 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 574846393 1250 574845143 574845169
    0xc2105010f0b180406170705100c03110f03030c09090a0506061c061701020a0f05070506150613080303160e03190206120f01062006011a040f0e15 64
    0x514884100300b0b0b819400050280038a0410400108100c80e00008086802552011001e0f07107030000d08064150b41400403400505060324080c02c3d68020180c000c004100b040001070901015443c10000080f04210044500c0302c9a41102ea030381c240350422842a41150102c24800c0e000c0000189c0c0c0c880044c090360307003d9032003e40600c7c149001500310b0180d00480c65039402d650381e61981c0004410720440600303020014018001070b40c0f4284100300502101202081394103101d410018a4001540002c540d64421100d070b80003804540c1040004100e4492076410441c11000303100302007480800400214000c050061040c2101c03c1c02d140e0030350f107500426000f581d058005603860300209860010086009100402d01441d0800980c0c401103454020b07148852111500401402a0354000c8501460144560b40c140c040f1030314105410ba0756441406002520001107201307020142c0c3c000d040c0d401030b04d070740c1c0b807074992003510742410030490402100c0465100308400400400f0b030804920f80a80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 574847643 1250 574846393 574846409
    0x608010302210c04021803030315090c03070f030c0c021315140105120a09080f0406030c0e0d020d0302070b0d24050a0902031e01170f03210405030408010c210501 71
    0x810f06030080200030340044844218409a542c0100000d5400384021403080c031840860181a06034407050040d9204000c0840c80c1c0c0d41010400d00c109550004203440300450f0381c2c60f022840d0811500111b0312145844c500a400c4802d1007450180d40100390495455034400454007440e041e6504405400c1508510003103000c500c04111000c000b81d490b8001c1644804e06031004104801507a03154031384d035070248400c0e041007400802c09010141e40350040c042d0300101807500c03043c40804c0c0d000142c6c03507051001e0020710604031290113504040c02400708400605902015030745800c4016203500140141c04091032115501002092854400500c0791080d54006007001d00a10304200d1420020350016041c0701c0380c00700610300f0741c60700c01a014413103029198035a100c0c10b03451483e0340c01d24a4040c02d06003480301c6030400d111000a0101c03844030b40c1c2c071495600486980c1c80c1c5650501904601c941d030171100643d42041e81c03c0a9054000e040c0f50241390035040c80c511158540050201161003e00810b48 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 574848893 1250 574847643 574847653
    0x60a0609031b24170c0913111809060604060504290d0605041808030c16020303180102070f03051b18041b0801360b01060801030221 58
    0x800d0b440c0c26524801d2540c1d1246500b069155000103400042c04400d054081040249401c4129400341d0346140900100c69020028207180502080c24011a14514011800b80080c0d9403000050b8100c0028043c2403d40169200c086c41c040389040441d080c0d1342d80c01540041702007404c41c00d003081110b045840d55a81c85040c035080529192360303a00c503c210b0440c03800011030b05805501d0150300605550358040c800003040e9203480280000d554119403403654400d40e40c801d001c0071801d45c1c000c0b00c1d800300c941401c807030341c4084040c000012581500c034041d416120206001c1c050141815051000759400d07021120101d5680e06032104001090000404541040e40b90340c07810307404401c41c446031910082c52132020450a03c101c061994040f00c0a5507200340040c1d01903500740b001c00c03180e070141041200034400c8454070201084cec02c00300100080640300d20350710400030b10301e111038041c5005070f44041c40c04900c4d6540e42d07000700b480b00e0a01042e482601e141002d0052a042c1a5100d0354410095000d4a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 574850143 1250 574848893 574848899
    0xf1107051509120d1a060702010e0127090203040302011d07030605060d0501020a090509100605090d0f020a08071412060f090f0706080a0b0607020d080d09150e06060a0609 75
    0x4420020098241902c521400f201c1a0351401900c1c09400503141d25400058124007000212881030501d00c24240601020411080541d03840b051491b18003030203003000a42c0c424180805028001c0340c0e284110000b918110109103102190010350103240281d0007403000f0f0740c0f4210b0071042e0008aa41c1451140e01a40d01040000c10a0700610f501400061450304003003501d8550a080e64010054003002030750290090046160100c4483e411001e0f0101511a49040c040040c00512a1101051051030414541e0703042280184080d40aa90b0240041b81c0302e40c2d443c0c03542c560303480c1c403805030b010403110003600380e422030a007103402885620441c0000c0c00b0940316082030325601d0030301070819600303401444103c0850603010042c4500404007580d4803031191405401d03140440f0700c0328041c03500c1010200000001f590342c82c411102070f41d8000194a554070407004003d40280343c0840011b10300c40f100449511a00fa00d40e110110034440382095400603a184010490b4200700c9028a1000c600e0080c814 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 574851393 1250 574850143 574850173
    0x1a060306011e030902090708100b040b0d050c0904020f0720100516051c120c051c020c01140a15030b1308090d261207030207081c0f110705 61
    0x42c0c00700340c05a041c0082c0500c0c580e00440c1c824481255200003054070340080c80019440020307488020507a9504442c1400c2c10450440e000313100740c0781c02d409540e84640108059941c41000c585034003000402c1150b5544480c1c041c981c5940007903509548840001c0300c0d041407501840c4012442030001041c0c4900c03078004400589840c0c00410700030440344685440100001c0c4c040100080d174002c0e030024086003d082a00080490485541ca5071660f81070143c42448990840103651007000800e4071006c4d01000c08150f071000f8061003109150f990b0800c40214030040c0700d256014020700e82c0080900c101d1041d1401013102508600c00107100003c110005002404c00844002c000c521410143d13280421017400a43c0c9641100002e46080c2e2801c0800f80358409110310403c040c0c85012040341c1881141c240a0f4400314006040d82e00380b540020b03401080008601c11580d07001c400004440409103c860707003800410070800394910325850000c5403440f22980f003050301c40c40c540c40741c02003440500d41000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 574852643 1250 574851393 574851437
    0x10c050307060509030405150f07032d0e09060f0a060e01110601141804050606010c0c0b1201050a0603110313020301090210020c3d140403061a06030601 67
    0x5840901050201c20700040c1c0d42c2c000d2030f0040c51008001e41d200c904107420048135020000c07103510348120800450085440c0325068520b841d0301400c040400c001c4070054500b4a20300d082101c6014140b900706400941d41010011068107000c2e41e61648540c0da00003403000e00e810500b800d80d4494490030041003101c0c45004110105901032600724600c281c90506c0c549088000e0300820300d4202d000a241510b420302c0c0480b420070861001c04c00d060350809032503e41c0c523060094007507410070001d102c140b0705000c03054080c18000c1110401499071545001c82c4002e84640a005161003040c11001c0040c0c1280300380962401c0000c5820f00c02c1c55501c420226898046070f2190480e015500c6507228030159503126090107200320141c014044a203412010080d6103400407a8801c100d00800c0010701001807180c0d0f10f004001505010301c10290903a050555212040540c1e50701c1114000030044200540d94201c000c2c080ca00e0750614980300301e440b04010940c0421140540096a01500d5002400800c94 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 574853893 1250 574852643 574852667
    0x303051506371e0e0603010303260a09021801061b110301020c0a03081e0a0e160617090105010608130f0807030804020321092106040501060312140901 66
    0xd0b03100000d51801d50404005140e004840700460505656084440984800100c4030806844d06040e10025280020410300041c0005402c04c140c00c0265200d6048a96000418406805040d296403401c1f9003090003030031091404034060b036255038080b5091003000e068603040e03400c1c0381c549020010000ea500351002d20001001d4803850b28078001079140d52820720081c071070315038950081d1881c21414140a801c51a024120014200f600255071002400c03040c40311b500400c02407004038655000020003072a2400602038500300501d0b24000040d01600705030020f450001020b103030b424554500001d1822038800b40307d5140895407107400038101580c02c1411192203441000c1e41030006040d5210010550064902140400d400300140025450108007910341c1c00c0503580c0d103081d0301c1c0250243d91624000c0c40000c0b4010642d240d0010300c05441c16400082d400c0d03051007100c28925213820a0340c00b81c540c80c4019a003006802407003450051280c91228404142e41042c6481c10b00c0100044070030030070f002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 574855143 1250 574853893 574853947
    0x1703011226190e12030c1606050f03070c021e1e18040c030b0916050909100f09061b0f020708060403140c0102132c010e06030c0603130303051506 64
    0x190728241503503036140c4500c044c0b210300c4000f0743d200c44003c10b40e14907110208111410a4800700002c10403150300400b1200141c030092801c0c0e46035240e244058400320503046000b507000f5882c9100c40003a4980b01c1700e20342c0c0544110384001003003d60300096090110198040c80d04456481007089440045d50304158000d40b05501e040250342c2c0d203460306c050340b000c2903400c02215004500030740c020360800034007440035003000ca881c02003074104444402d44d64003552515900180d2200042c021030307945a0700c8941c1464000d0320500c20601c0300b4607090a510341c08510180450529042c410242c0d20003c1c51105442e03010b001070600303881e00e4409035110240444d00803880c000400907110450800e0000c4c00003120010444aa03071410050b000c0807000d0341c00321f1110b00c5548613152240d034038a01140d05044420610000300184c0b14038000c00c0c100345684216035000a800403c0c0000700814189031610725000ea64104080d0302c07210f1854a00302400880540d0181c020300410240d01018490b008800c4100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 574856393 1250 574855143 574855157
    0x90e0f0903070b01080105040318081519020d060302040501080715030b030319020303070809010e030a110a0f0c0f060e0f1c0209010f0e0c040f03030c170301122619 72
    0xb5500d0840b0f0309401d0300028141c0c3d440e401170004043e0401945004042c1601507034a00f1801d0140542d50380b103e42407481d04030401540460242d041181c040021010716240641d6122882c0c460f03003024010503c0224002d61070400001140403001c5130036070039210032104401d94201c902600f2030190482401042c0d041c0803c00600b0000c4800c0304621100201c0c68005d1500c92810303040c050558507000f070014925905021100e410040d022040359120025414003100010003006840e00d0015583d01c000c003520388403000c0360b0602c40404030300c008451140c082800c0d80e40d00c402c0101c8542e2050784000350000841d1103644560b2500703504c85485003031414116103540c07510b6000299191401e90040444203442542448111183c1202507807241c6044411403525292446c121102c0400c0d21014040004c1c0071010400c11050081400e14000c103d04625242c1d40c542c17601106501258008a0300405618499695800d6812000c103c403040b07184214100001411000c2c0b0031501c0721010000c010701 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 574857643 1250 574856393 574856407
    0x30e041a0411040609172505091302090a061a0a0215130507090e030d0207022709010b0108040c060809211803060613020c01091502090a08030313121e0e0a06090e0f0903 74
    0x3c0d1066544504004c04ac140c0c813100090050003200500649200f004500301507061112414021018101c488040405507540706241c00803410201007804440f40b02c085034051068001c51141070900310760003101a00e0149503503501a07800c07199101451300d0613800c01e00c401e00760804d080e8090040e4a0000d000c2000e240240e59140707211044d202041814442500188a4060300034803030607450752030a080400d550300307050b00d40c91016030440c4a04402c000c40140060790b02035062010046180c110004000c00941200003842c05410010802403102c1e80d0300a01c040e1450005001405010080c00c1c0010074010b12820358040e52040000c1d412a640307414a150002d000c00c03505113694007441c640161200030200402900903481d91090b25140c2c0305100380260441590024601940c0c003482c1401c035841407031026a80341548511540c030208582c0d086c0f80d00b49410044c401e1490b6422502000c0351a1605001d64007a14135008072904c2c940d01d100001c0300100070140068000754584103d908040b2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 574858893 1250 574857643 574857649
    0x40c080109030f08060402090622030b04080705100218100e150c0705031c03091704180506011404030602160209010f0906050607030e041a0411040609172505 69
    0x1002003003100050800c0140c1d407100d503841104c0c181c01c60310856043d440c0c101e5020008540c0d0041c480e41c0f204550200c1d0320020b820103941780041c000d60b80403500500e01d19003424100030035000202d0603640382c060303544910701c0050640308480c561020803000b00c0520106105120141144050719018002001c1c480c6d0710b141d6400a50307017901c40d0303110007095450441826203801c00800341e110354000d40c0442184c092250011800740c40c3c5081c40d140001d6100420300780600076608282d09468504000140866031104a15110600b8440340c642405162190030044415400030300005502c610144401e200048140d0000c01400c0c5014001c0074003c402e54000607041042a48010366100f1480e90800400410f409404001c21040b5442814050282c03030181c40b1070081c5082d10301c20ba548086070ba0001000c942001007024010704104141d9a00395248a1554024010701b000308e94800700c0094200e12a40c0300644c424080c00240090400800040f2040d01c43d07208100b006041022010400352 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 574860143 1250 574858893 574858901
    0x31202040f06050304051e0703020f0a0602030708070c030b0c0304020103153210030204030209160504030206030c070b0702010e0c0d02061207020a050d090f120b060105091c1202070e1509040c0801 86
    0xb81c1b031f4010f411160301d188108100784070030212035801003501e51003c01c49590044162000c540e004884183c1e00d903041d142112105075a901300621103900d035402c0c0301a41302000061071285100307881c04c00a90b00703441e400e1402d00000348103085548600c0411031041410f0850132040066510a0b0032080e81d0754180091100d4003090410000030754003041c10230551805000701900300e081c1a0064070344014040d401401c6220f24007000e40101c03800008280da690503441110b40c1a60040da4526950801d040000d0281500e0301d0494001e2090100e40e0900303140001c0c0c000703001d5500070502490030710481c2440b1021314008007074601b5405842504800f00d013042c0804174040050b6603d00314510b0500b03c0a03611111071750012264100014a103800181e100c2c02040c0d0400c0c07007402c1260b115104900000c0c0010403500404801c0b100c0a00c940701004040d01070240440d0a5809840c409501e400c514035014200302d4028100038a9408040364500700790089a4215001e00846042c3c651205080744c01c2d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 574861393 1250 574860143 574860193
    0x408010e06090d14030112030c050624010e060313110a060206070f0507050a02090604060f1205010b101b03050d060303020c04050c040f051507120c031202040f0605030405 75
    0x90780240c42007148000092102c1c00381c0744501d00b4001c103081910400442a03010500035803440000811400040c54003d000d0740c625035a010003103c6c032500c0c1030008803900e04007021000300418a6100c2000d15580154114004040c001e450b603800c0d0754030720301d001d86031680301d000071368135160000c40c13248260b141d018100010f0a032503001032000341010720000780030392031400041c0d041060074001c800000310081640000705030100c40e80c00a0380c642d14002002404540d11031080035002c07035000150300c0340700b0400d04461130103480208422194413050101200c1c03001c401100042004414410703205103807500041d064000e140c09410861505e00c40c208039132180d00103a001d0f81c00704000048a241030b00030b41e40d21440c1d03100150300b010700c1c104a0300e81155482c0166841140403e00714413800c2c90540585001640164814251084481001d4804540110140c00141c0a50251103070b03141c15000f120121901064910000d514114041310203401c050003c0790307640200c010281044940312420401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 574862643 1250 574861393 574861421
    0x11070503030f07081302011709010e07080d110c090115050405100e040e0a020102060115111203060117010b0304080d0e2d0610050f0a080102161e120311040801 70
    0x110b8101000080c150311001000481a4050301c5d00190040c0da01071a00400c814900f0782000352611b459075100d000d00a045941c100301d1040b01c038002010710700081c2d802da080d90192034a42c0b021118645054803000320200c6140c0025910004101d014054078890362f00c2c443c81e242243c20703d611040001d0b0f040ea000401d8400060b1806040491031820384103110003400d0810007000c000c9280d500103511404144502d020001c80d91511400301401003140c40311061448080c1c8580c1010402c00282c0758006541d200e000409040c4c500b1b1420000c504001d050f144c1c0665a9404e658541c0c8e11404c2c55030098401306030558450880e1100300c40c04000b864802c40c4140740005c2c03010685810208150340c2d80020302180e5101031b0034812480503039400c10081e181d054920b005001251004101a14440d034450300f1998800204010507003a10501101d815100c0c188040f1000100c007044114803841042c0509542046907030034000074001c0c1c5c48126a42241c0c2020f81c01c0c031399540505800c641501500640e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 574863893 1250 574862643 574862671
    0x1502070b0f0a0207030f0e01030905100207060b01080103030e060307260a0c0e0a0e040f02090f010e0c040303080a2a03020306130c140306030109080c010f1a060d1107050303 76
    0x4414126140c81c40c1e4001101d03401141442c002d500c000b0405207100b002581400210340304500c0d164840d42081d41025000412100c503d8030114500780251300108056421034609542804950310440246040f0b0740c0581d07619049480460401c031295102401c05400e0101c280007401030700e0301c4806001a60760504a8a40207031801328850015600f1106c502010092000600303400382d682e8160031415910b0a4840602581d20340c9441a128002064041d51010101c0204210740c0d4264110f14141d9414110f404902c0c0c44e192485c0606004502008001c42d185070009808040d03640d10405015141c21044044410765040584159001040c6000020b400004015650900c20300f040c01c0c41c5003030f4000300445000d03424001c0a8031203203a1568030240000010540980d400d40028181d250080c0082e0790350300d00d45104900a09104100701209810404c0301c00b100310b030100703406140d950050302c020b00e4000e11050120007080c0c959103001003a00d041c0301007404035400f003026512581c82d1000d055 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 574865143 1250 574863893 574863901
    0x50a091202010203070c170c01051812090a1e090608030414060412140c031506130c120c02030c0703080405011b02130209040f050c1b1b0105071502070b 67
    0x3545160540048015a07004000707212805601148044c03181d904090030f01c082c0640c41c440f4100307901c61603107440c60541c204001e200214160304516000f01e401360003180c014140c079200007441c602461080c2e0f0360160b0035120070070145c00c1c0e00207107901410503c04480c085030303160041101140c8042d001451203a00103d001d0000f0000e1521420f200002120514101480c164015400c0c038100300c0014800003602100d080c180d1400c005024107a2001410b40d00d0700c14034a65003102003101252030b0781c840c9582c0140c05404141e41d208038a154881a0760382c4071b01d0103000101c080a00094042d0400310305c010461811103040030b0006402070741c80382812603940ca2038007000601a60142d413140d4002100b0300c01020059032004840c18841060b100090380300c030030060000e0000e101801d82c0120345400c1030f0030490f0320b00ea00b60042980103482044c40c2450380c14a16965070350300b02051039900d20031602c807101d4180d60180d0003400180780b0880755452010f8000403200c0c203070381166604580d00d8170840140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 574866393 1250 574865143 574865153
    0x3020301091406030c04020f0d020403151b09030b060f090103080a080c040e1303031b020a021201020c06192702100c0f02010c020411040e100906060f21050a09 70
    0x82c8035408007080644403402e250340002d45500001e0015403107182e00241c0102649002010790707141d940d907483c08548482c2d8be800c2c500c48400aaa0148540328030b0000c8072000041007404200e0100225038401d00c5050843c0e84120b07241c40044d02895100580302c01105079a561480858040d40c4100c20f80c07602c400710f0a01c090400c1c800585403460b0000705020501909105100680c3d00c5690380195141182003401c0540040c03101c54100500500c0c03c5880422054000950b400001e02c00d68039032280b8012010418200d00681100043e15004100860b42918503035400c3d00d6440501480050304241d0050b02e020b0110717400344004500c403560111302c03041d490800e1800c00e00c1d510701d0916a2011115503100175141803000030003418021044518015500c0b25030119801c503007408201c0d9a035a0302c40c00d00301c081742c808a440140704000d00e0b90103c0c0031000c6000e120115a000d0300c8488040e10f120344155013080c50045040c5407012010044500d80ca22801041d0003071265800006102c040b50500e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 574867643 1250 574866393 574866401
    0x306030c06020f0a03050313080a08090c040b1507081603110607080c0306060a170a200901020a021c1205030105090a150b0a0309082208120702120a020d030302030109 73
    0x440d01c00d6420418103a501e2450102d030002c0b4096151514035a60394407a0071142440d00c903030380b003c0c1c12020301007034420300741d40c1101d95580a86e00030307000c85444000e054200f0040e100c90464448c0c0040c201202c0010702c92148000c1e0041d103218074046410700c00c0303441c500a82070804070810750000b414421046610a0288240d42c1c010303006181c00006072078441c01c02e003001d10015059900440c0c00082c0700e04014031943c0f0700b841400d512803c240c10b5007410500c2ca80504540302c006a0403400071018068644895011144c1041060700a418000c90340e03001c11505984400d981510350740d0300c014950000e105100d0b002d0b101c01d0107448058480d41000c09002480780020034071a54141b0340545103da0b00080b442c440c08440c0050f0f60385980e4007620504602038809404010200038000c03030340320640d00f0000f0f1520011140307582481040340d80e94081c070f40c2c0c81b0001d00e490007826204100101c0541030914038050503010a5003290304427102640400ca03442440c600941c000796010006000246840c01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 574868893 1250 574867643 574867649
    0x20405100f060206060303070f02030a02040507090609050f131107170712020609122b0b1017010605090a03050d02010f0c0f120c1713060b150712050c030a0306030c 72
    0x10040c0098501400426501d215510b1301501035400c03032741c8020840d03808002d80100c8984c058428400b03400c18410160914186004103404aa40e5440c08512030038080f440e03602094004240442280308190107000902440d101845030b56420040b07000402d6084219180b4880807a849a81d10501401e000d500200c810300c0c0712003103402060034001503c01c0029400340b102c0710520718503a601d40c80803082d8004901c0d4484642540c1416203100420b4010384c0c4500303a0042c080d500880c240070a42000c44440d0342c400c103a011000480e000500840d8801c801400340114040e184c05816a160744a152a120b0a040c484005030744800f5101c94025090284900d48802d5041c0340200c40007a1002030100707415844840c0e5100c1c0c3d00c6102e51f10746486a5041e81c4071200d401841003a50030040815001c10848410941e084c50070a031040d220750a0210b142528244110815030070540d10b50b95000c101112180a1030070841e017406a000c03001d0f818030040c4040c240300c2e2400203880d407451a001c110005554 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 574870143 1250 574868893 574868897
    0x1401020c01030b090a33081e07150516050c04060b160b04110a030305070302071401120b040f020f0408010f06060816091a03340c0203030403020405100f06 68
    0x344002500341c03681c044254200e1a10500824100348008003e00c0a1a0349402c6c00080751100c2c4400f4050019800f804096407440c03005c0c1d134540502100a5100c240c0c44042a00740d507800810b0030070144210140f110b140c0e0941385841403504803041c20007000c055031a4020354140d0803c21140d8090f2800c2c3c4034034030041c040741b0707001c03400c010956070200c1e544c0101a0000d06400c40d82c000281c20440102209146800d00a00803c0c60580b2410010241d4005c900101c02610460601003007402c1c09258004e0041c0c8140e40c0d49004040140a902c041c02c0c0c1d0110558101e5203a0355014504901800908041900740d49829240c901d8121a1820759210405a1405600c0e281c814082154400d111603440301001000e040d200125030740131594420340c0d600c89050640f0340402c2c101e0046094005500412540c0404240b80c40f121490b039610700454426444c034088100c00300500a40640315100c940c0307000a080d02d041559a40114054070012074038011004030600d41480b1448a502c40d08000e0400b40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 574871393 1250 574870143 574870151
    0x4060e0a0513050309040c0e0303070f1a100312180b09010909060e0103060e1e01092d060c200705040c0206010e0c0d021b1513170f040803041401020c0103 68
    0xa070303d400ba2a071264007440c0f4080ca84482194108a0080b80d0014650074040d0444e03a4a103481c2c1440c031258a5071480803200303584c5d11051076100341290002140076000e95510340048600d190f4420000d0a10f10007130300d091090420184208101050b500c000804800310b03803c0d41c601030030000401d0306201c0c2c3c02c10f0407410f00e0400700380a81c140d064100e40c15241c0c803620014525002c0300c440c5242241031000e102c9a030412505103c141c1d80190084100c49115040110f510403030f60303003da210595091755440d07048000c0b6403000c010560f242c014003401c00c0c035401d0242c036602038410380e5007000c003845490340c5840d80300610401060a180c843c502e601c648610203400c8035410000e540458a00c0a42405045400400c0d01d0b4900f0845034122184800c41c0c586c0000140100d03030b19940c60b01c507505100060707a040140020300600b0300252064030b0903032080340c100805104102c0101c4d160480350400c4180901444041030b0000d040006101a10040c80c0a0707030f010b541b4030002803410050b82d940e41d04150038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 574872643 1250 574871393 574871431
    0x50303070506061309020d0507050f0d030503070c11100206160806240d050703140106020127050a080301030305040e060103060f140411180307050f0a0e130204060e0a05 74
    0xc41c4503030f0812400ca80521010f40d105001502809250102039440000f0103a00c108000000a01404984064504030303e00d0b0004003c100d560082c420f405004a4020000264128400c0d444074149a1081000702040108c1344081900250800380324400f581c05401800648040c192441c0004405403404540300d180c500f02144582c94030000c02c2c0c6e4a00801046204000320107015101c085509520412051404da00000c001d001d4840905000c4a001170010801f148103005d0141482d5a8070360581c0440c0d503000380e040070508030f010207580d18082e02c1c4040f030001c0c062100841c002c5010383c1c1c600b5201c50602c4c1345204070060107000e0505046c0f62035804c101c2c10001c3c1e0b006208079980c000600d60303c107141c507001c900a401406901d2441c3e110015009491b001080c0e000748510400341c00300c0310160384810500800c0d507031b50107829901404100d020000b200030302e10b0369540303c03407070703419405501409501082c10741d45145c101200402e204420006410701e507210359a402010103403d10340c2141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 574873893 1250 574872643 574872653
    0xb030307050a02060d0608010513230706140f0f0c06010f0e01120305090909071e05061b0f060a09020f180a0b011b06020901140403080328020304120905030307 70
    0x20b00c000c00a000b0b544c04502245c03100b40e00e03400f407002090005c000b03110f0341c42e2080d5034481c0210101011078401311084d048040e0385030405007500c1803e40b42c000510740c0508051095510700084006846810300030000003414540c02030240c11003801d40c22946440340c00076100c15040810580000898080f182810400b0880d41d00b02d541c1100c11098401401010500702119544191480303142c101501c0c8080c803000700c0b4002401c80c201c0344150140c105014044030541411540c52184692100d414860001c084440c51240d03405e10001d02e007150450364041781010b0070840c0071030303480030349030fa48400810a6003403840140f0510340d011100d58600c180d194102c0e040d05040a000a07811a03030340c0320910100d034001c0745155112501010702483c02c4d0014600307031029603c4101d81600040d86186483c1042e480a0142c2d4107503540301e0411070840e07480840d010030b02c5188001071260040c50f0310303401001e500300784001c0d40074a005200c09054903000407809041c079641c0354040c0d80203610402c09034010034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 574875143 1250 574873893 574873903
    0x60612070e012d020d051303060c03140406050f0f010302012111040b070c08060403210f060312020705100c0327060f0f030b010504060806180a0b03010b03030705 71
    0x100e8204242941c100d2401201d034404070444600c0009038011031101078001d20041d000030600240e0807110401c0b000c0000701c8950140d641c441e017440700704c0401800003c0b40340d0054408082c2500d00051409004180c0c03044917030f810f44068400aa580c81400600700400310f01540c0080150303000c02c890b526590000703007610806c0c40002c142500c0c030030a1200301c80c00303500100e07155218401400d032a203450700329031f103216030002c501190f01c7c1c1c0032040000380c0074802107401c0e0304c42c0c0d4140e105d42ca0100424800d01c080e9061b18005049890b641d02200c840300e000f0b0344540741c044c42c050184503040640044000e4544615500003d1250f062441d59005090b808440d025005034586000300e0914010480004645504140c00442041200c4040341242d803000e010b024010f00d96070752114200d40b1400542c100c0d100c4105190004004000031f001e0180107030320203508404e004e4031015180d4040134043d0440c5030141c41303c0c4a46c0d520f4164489580c50240164050f0080c114080c0d8505090790351103941d11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 574876393 1250 574875143 574875151
    0x70905010309260a020f150f0405010e0615090601170a0905073305040e1b091206100b03390a090e1e180307080d0f05060612 55
    0x1500e070200e4404022290181100a4801d40341181a044000c1103280c86600a400c1c130f40014841c01005010030b40300080d02c000645020f07a800b1100e52240b03c0402c2d00310000520a0b81c5543d206e140340c0c040403004101d41ca118140c07543c00782c454404d25a0412070703c81c6001e01064104a91214072640301c0040054264002c86219000200506c15181040c10460240e0000d0190307001c02c120146c03200364080b01c400404e8104242c0418250044805a0b850301450103011006075034540080c0320030094049080d03d1510107040a4100914440090003404000c00101c800303403c49014041d840d80d0b191000c0c400b61010041050440c070700f02c0203061110080d4040011b1000c00d2440e0030104840e00003003a482d1008985125903108585580a4100945403154441e4651510700045042c41c21641c507148014904001b40d003a0b80300c020040d62110940c2c0c0303816099000c20840c400008201c0001804500400100032070884400c0d44402d0440d00000c0c1030718000d0500300303c9218455140340e4201d40c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 574877643 1250 574876393 574876397
    0x1507020c01032a2709050f0106020304030f030e0d081615060518101703070b070e0d030c03090816050907110a0b100b0406020c040b011b0209040f081c0609020307090501 74
    0x6800c03500300d1240761811440741c40103950203030b04c00116103124107812041c0b08415440c03c0d4003640e40d840108aa5912980c440509080b9105601030300180c804c07100c200203010300800142c082c0b045901c0300340c540e500152010341d040e0364180345402046100b06001102c100d0202040005038a42000b10740344000030f4104884a00d82e400001d40101511017404c40a48039000e4440d40c2c000315194096500d5208580c241d808440040001c0c80643c0314070203490f01c0442c040c100c180b8030012503030281d405840c0007208800707001c0c9894000c10700000801015080007003c0c074240301030501c0d10060200800000e01340100300407461a10070b00320354000894a45007944218514261303652010028000c421540004845901c0001c00044190f800034984c202004200c40402400c04500300543d40809005500c0500026a0340b0200252803c0c41c0d102d0ba00c10300460b45101c10b100d00d9901c40151754042d0350748a84030340c007107120714401400d54032075a40609118101145107080544e0040d203081e4032489502c1c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 574878893 1250 574877643 574877657
    0xb1203120901240905010e1e09070801020a2606150c010e070e0601021b03060c090102010906052701061802030403051908310201030b031507020c01032a 67
    0x2008601c2548a12030346151442209405550200c075846012007600c1102111401c0c9400071500d118046151801125480c662003a1684000903003500404000c2011649024200000030110000c1c00108554282070380c81c049048000d0341e01601c0d00d0000c2d5600d6032410000f03010800b240e1180d5844520300400034120644440c49905050701510051800340a180036404000030215080464140a2502602960303410440c0604020070180b003c0c1d00701d54540d1003e004a41c03018403620080100d1503040c8000b04000c00c140c1c0368042941c10a4038020340d80e515052020410760b0481c078403814515030201c003d0240d5403a1400004131400c06092030342071181d00001080802d4020750440314110301c0e6000c40c204280020354042c0042d041100c000c81d6600b940c007100302a840c01c41d032103258240d5903200c00ca80135600c940c0044000b06421511a5094400c90821104c0030b030068a8847c400c4c0740c41e42c010106200f07800c00040c1078608000d1410511711080d540e0042c0201025003031051100d42d460030031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 574880143 1250 574878893 574878901
    0x90c03140706090e220804080706031815020c010207080c060103020909120909060117240406180c051c27330c020a1214030f060a05130902040b120312 66
    0x5e0051019090000d1007640005000140351401046c1801251043d07202000b1075046201100325001000c440201208036042030b12080b04c0c1560b003c1c10b61460002c000504081c2d00e40d4981580b90320035002c808850340501c0c0104118038107003400c00d40c402d103a04042d200da000095a440c2d1079004141d9154400c1d0311000020343ccd00e0340310303040c481480c20300700c0e04243d2582000501080441d03c15a1150180804290711440c0350605009a02c00c039440360190000d15861065030b6030042016940040030020201701c003840241403000b600107203110070035000802c543c03074411412210001c0c0e1800d260b0b4441c03010650012401810005400c0c84c102c13042001d114032400c0d0a160003000c0c142c02490b03a2860007081d180d4080e4001a8041c14dc0d02c1640340c000340140c89030066421544900500155000c200b000400d010300b020070140d0080805401c030303002a921200000c0801d10600b8100030201c0c0d50703200d1601949003034000c14551110540b00e10080341d8a4000f01c607283c0c03142a4024880b144980089 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 574881393 1250 574880143 574880191
    0x5030109050924090d0207060212031026010b04090803012603030114090901060e06120c0904111e060405101701030507060f02030306030303070c06090c03140706090e 73
    0x441c0f01c41c840d0800e503142d5007100040310614090151541e00c454070611080800c154000104101030b200540c004009407401803107400070b5980001c000c0030810003124800210400c40b42405100d403150401101840b15215240c40d0031180c1c9a003800d031040e0306120003035000c01d40c1442100d0640f01a0202060030300010b40c0c4401c10313a03203807100000c454400040001100124559104c407142c404841001c0319450b41620b8a0903211940120307541d020b4044041007051034030400c8110360301001c1c07080e240a4680f08000448011040310251740c000800c0c90007200c60700d01030b03105400300c0302c0000b40e1080320b01321440410018040c0b402407900031001c3c5900300242c907010b000e50318a01081030040b0b0038075603183d2401544522242c444d100108550860300e14440c0d0002c01500e01c030709000b070015400d5507121001101d8941400300e05803545c41d541c800d0740700400e003090001c4001d1802401e9000c200c0e001035a00e5843c118080d80a13404007e180e88050110b40f80615800f60429407101005103801c400c4610 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 574882643 1250 574881393 574881403
    0x702010f021504050304060e0103020c070e090f0a03020c0f01170f15041802040c082e0e16021207020931030c02040b0d080306090a150303030e1606050301090509 71
    0xb0000c1c03800d008030100402c0100020041c01a203842e076880c049140c1252005400768081c014004942e5006960103108407040d03603a20300e40c42a096000c5038402080b100e1440d04204c1d08060680050700156030503181414200c3c14107505d44800c0c604115a403880030401071074190003520011481c160341000c941248040344a0b41040c1030b001780200510745007041102502143c550b4102d008900700002d200e031241c0124080c0b44a006801c0700e0780d03084c1401e41d00002001d0100031044090317140b110008610b801c00118102c3c841c03040c0c3c031001288400b041d100a032400482c100080c0388a031040201c0710060b1551250550480c9011110081c80300c0f85200040c1440d0349230f07850380c00d9118588081c00c1410307400022111000d00036101004800004401c0c410604504400070380411030030000300b41182800c0e1345865020701c4001000445220018505182c00240d80c000d500080d1603080b01c0655140601c4411a403602c0095084204c0f07141c40c4000d0150f01052140302550790fa6100020800a03060003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 574883893 1250 574882643 574882663
    0x40311070b0406050306040c051201030b06060d02220b04140118080109120e060403030e06070c1e09150e1902070203011d0d0e0609040c020111030903041d06060702010f02 75
    0x307070302d4403503403078580007880340e001100c2c030398880e034202003040740c40901810445c0c200414600482040d6800e50311081d400781e601400c0941c21960030048010b54801070300c05007410301c0351070182108403805040c00090303282ca65005114290020030041086104210401c00e10070420700b03107601d00c0745c0100490240c803501c3e540803030555400d01d10103100f045155003600140c0e029984800003404030490a2000e1070140d1b010080110304540c020f5641d510704074003c1d21040d4483c00001c907440303403031f1400240c0c03030b440d0b0a8209580e0854a201030003c1c1e10a40642402c51210b6600030315194942210b000510f80040c011840040c1c140c044410000c0301901100d407a00e030068001c2c01164001d45041c0b9503941401c01c0d454050060f00291030b0824401c03011000b8804004114505000d91903080200404d0850581c84c1550340c2d4050b4034880e42d01c41c00240d03105c0e8074050050b58035946441d030001111400c100091960a5022080080c01d41d158015226113540a203404107050700100340c2603141c110490 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 574885143 1250 574883893 574883909
    0xf05070606080f0f03070c0b0711030d020106080f060f0408030606120705041a070209150612160e10020304030b04110d0f0606050418060c0c0b1602010515010804031107 74
    0x420200c0b8000351519101d0b40c540704440604007103541031a100c1c040d04a0040004881e000708204410642c005412158043e8240020000034100041e2800c2d11000015001d41d4552204008000003800448000c0c09400c02078922440c0c07442409403503c9004000906640007c070100e2901d40b10041a51041e40340c0d840c1c5070810b824405005841500580305400c000d442a007000002140d11200756040340d54040c00354511901d400c200001c1c1c7c184641410381c0c01040030b00030005090704009040703020341e40000700c1003030030032428200502084035071842c01c2c0100c0d00e8403000366050381c1c0001140c04503038110100c41c00c2610346241c907082d41c103101c0038455840004c0721001c3c0306010582c1401c0c0c42080c0308060800c281d42d683c1040c00160303000700143c1c40300d120f004c01e82980031444e507410550b43d104441c60310400300c00312a501c110f5207400a03204410415080c070041c07958076070241314203500155201882e41c4412950b0000030007210380100014200040012004a110020403405014042d18 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 574886393 1250 574885143 574885151
    0x11206110d0501050906040219030e010e07030c0311090108121303120e03010501081b0607050f010606120506010c1709041409030a1b1106070305070219090b0f0f010f050706 76
    0xc800c0d81d0010b040203005441c81030103904042080d030301e0503100b121495645820034084902200c54103400622164009007443e54841d16a0003500ba000e00c00d0002551080310712400e16030440c01d0404003035148004082c0902544401400301040001b0440412800f0852455640703007581e4200e0302d000e20680c00148004102c1c03000d01a4280c00600701d0304214002c1e4001c11490780c0c4c50040554424801c0c0e5450b02101c02803d01c004176052590080443c40d0148040300c0410340f1214805084642a50010b00054100725a100b00034a245c050650000024a40042c540700c05499226054840f0410b00c254011b002440000f942c503940c01039001c0d90100c000b40001d501d065032007a5103a40c81080c5c00400a40d104440310340c100c00b44c1c0450907a090f008120031100760480002d102595024000c03d9007440000e01c69800141c0d18203240e9103000300c4003131901202500d0080350600303480d01c2c880ec140c440c141da5403500d802d0f6201c000030821401400d2909001d6003146e90001d403440c0c49400310141446040c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 574887643 1250 574886393 574886407
    0x30504080709021c0627060e07031b08061c110a0e1005180a09030908010504030504030314120f0a0b1f08010f06080403030b0a270b0d0b01120611 64
    0x703543c060310103100503448000c00703500909000c0d42102c0c0940603040d1388684030503012655181010b240c01a580a002c0c0008102d61111a4409803000484a00d0006501c640608001305582c402c0301001c03111606252201d41400000181103118017a2030080842c2d4406803031041c00303020983e02042d0344d005014114850784030001040c281ca42141d8071500d0354510741c0c0015490a0810b1040314900902c580c820540d160052360314040d142010099040110f002408201c110007031142600a621035218295601e2942c5805020440c500c403084614000a020200d2160918120700798400310300804500a5624031241800411500191035001036000c403e0320040b00b100b514901341d54020b5220303106030740c1c0c0e1405171904603041c40c01503100181e60880881c000074005e40265141d0080140083d040d5507e5031041b1090038001c0c0d0201ca18031804640441c944502c921811000f600140e9410740b404850b03440d020781c0c03030030107204014a8240c5018008203108440c0d0015418092800010b541c0d410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 574888893 1250 574887643 574887659
    0x20d021b01050103020a080d0e0d05070f0b041e060503070e1c060207300c060b1c0b01051c080d060306150305060f0411011112040b0d050109020c12070305040807 71
    0x18013400308a0051421003800304117800001081510103115945041d0b00e01182c1c824408609545c9000710b40c0c1d4814803002190b070004600c1d090000e4040600b02946540c81c10041c04d614180c100341d081c440c1403d021042c030603981d22a0440707a0103205410b00c00803101001c80410542000c0d203498020194140040074100301d1142c0050003c98001c01d084420040005222990b0b44444900c0c1c403c40702c44481c003a070305240035000d2036100c0c0f80551800100e407111080401c01055401000d8000051000318642c1040b00110035180500340503078400e204505940c41c0701c4000c505e1703900080e09034200401c0d660340f0300307805030880000303035234809014003425824000c400d5503500d050001b12614080c0c1d1300010003052100301558402d03a04841c2080d0760014032001510070030100740c1138404c03d00409110f5503120322030800420040c28044002640c51003031006500481e181038016929613401002440301d0103200003052007030b000092000d10760700c00b010700d82030340c0c01e01c5241e00c064480d000c0c11500154102d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 574890143 1250 574888893 574888901
    0x603020706060503030a08011205030903010c030b01120b0603010501050d0b040e0d0225030821040c05041a030601030618061803081f0e06041409010c1103070c0603020d021b01 77
    0x352242034103020203503c4100b0182c03240503801800000a1203000108108200340300301c2d41c0d00d05c1c0940d00f0b5a01c0c06150001080c02d44440c0180280400c1e02c0d410111090350b44070b0070003c69070500c402c0030041c881e134050006604e07100600c81d50b0f042000c040766444000042d980907417009003000380200014a0b44240c49925001001d05070009402410564022032038214496002040d041d42e0507480c40b8150794800300140c000200c40d40766071a030440f100110b084091803203070245d8090784403411000c0c6813104202c2034603c83c415001e400300d00c0080c00302c82c54400062050569a1107200840e00141d40d2007038400702071250b00050040350400071400c1d402c4400310309600d8402d010b5921440d81e5030b00c0d656429410090200611300d030717080c1d8910030021030140000789600003800400100b0101d02ea9210209820810303603003c83c0f603940d1703140004405a0000c0010209180500240d17040c5aa40c0d11042c45003205840746c07009054000843c00c291410550403540d00300c1700c100c01c0901e101c440c026042d00030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 574891393 1250 574890143 574890157
    0x60e0f01151b0204150306140109110a1403070e0a06050a020c09071205281a09040302031207050d0903022a0f130f32060f061b07060302 60
    0x2201241c59514480c030300c1100701900c50002e8040000e00799880e5428000100501000f90440886188001c800642203010350b1109203800c29114455505241c0c40004541508c420b000c8138240412104d9620780e0084002e5540413990800251a82d48200007518503445040d00668003c66112010603466040006010f1b0885980d08542c0020352420a0001c030003810b5540a0104025132000d10803954181c0069900c0042d40d12144465490035a041c1e401c82a100302c1c2c2e0301c1c05c0d5160251b0080e40f032669046d1401c0f8003004ca03a03150580c203242c2c0703021b03444e4410200e10044244c5480300040041e4020b00849a04031244081000052214100252505060040703104440c00a001d881c4080807211050140c40900500c0d4480c182e0100c0d04000f101100300d0380030000f0580300c0c002c440071030600d44621800c0c0001c151b034040182851a222a0f181048a45809141785244040c010340d80c44140040541500a071601a52210006a840310740381d50b4525800316889141e0700480e400c2c3e03242d0064048 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 574892643 1250 574891393 574891409
    0x150509011805011d04150b040e01061e030803010e040c080d030b0301051f1e05120a1203060b07020d020f090108010c02070602031801200601030309030b010806130201080901060e0f01 80
    0x1082c2d072a0b131041c079a00c480e011405000300d0001c0c004100800d6640f400280581040c1400040c400b42020100d070a45040601c0c2e0101c0765914401004240c00410817000340d980c2c00a0080c030014213680c1c80484502044c01848883e40541c00000c04000c03e441c640300103004100c08480380610041d0000300038250610411303002c0d500307000101d4901041d07845040c100904071501c100c06642002d13040c844109540601c0003a0700840d420019807a281c50740784255030752707003030000d00081140341c2056842e030b12038441d4203010103180c124208090f403420320a41d0039140c0d04480c020030f07252450001a001820014019510605107000010110415030050944100d940c0a035030880e5510803080e40c5070f0160120001c0d21011400c1c0314100f541c81404040c0306c409000050321050120344055914080c001d8200310040b8070000300500501031258000d900500a06004019516224400c20081d02010070000d0603c030390000070415400b403e401c004090020000c2d40390003440c2103411034031380700400e1003001c007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 574893893 1250 574892643 574892651
    0x31c06050409031d01020c0a0b03040c171005060112020c0106050102190807110d170c010b04020415080c04120b3909010201021e030603070801020a02101505090118 72
    0x6964142805481041038054461818440c2151300c03201008403c82056411401400d5246045550b015491009040d80700c2906c0c1e1640b90500c0c003c3c40d84031290700710036010701802141074024240001d0324851220600320200f80d0b0344070000141d42210045d920419028004580400c48000c1540000101d0340700740d0840b03060040725401c03404004260340c5c0c0030702091010010b540210780a1b0700100041c02d0090010300e090016500c481c0c0000064051407080d501c80044d07a0200d40300c007405000100102141c0841c50701e49000762250125008280c80c1d0140202940018010214103050b0b03001417401e003100b400300c4d00080c5000907102000312207002c6800e0703103401d1f41020315600c101c1001d00098816140c00700c0003030780d1007849215041800c0700f50442d0740800038041080c1c1d480901401411a1101c0341e13449040c081c04040c200045508803404688c4103001c10f01445a0000c0e080c90444a14800050086000c8071494a0021a5003090740c01046040002030345043e650751240d81c40c41c00707000c104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 574895143 1250 574893893 574893899
    0x20c0607090b040b130504020715060e010513050a09081804140f1810061403060610090b090118060513090504030915050702180612071203030209030f031c06 69
    0xa58801e1480c000c07450741e100d05000034403502c101503008040607039400384011200c40d80c1d00c0001c0c0aa90060b10120f0f07400c86100c11102c9102000d00903600034180d600004c1c02c9660500c0701140401c0c00c2c1800d082e00c0c194588000c140e014070668807022550ba0000007a59540a2040e94060202c24050800b40160300e0030102c050340b9010300c01818003940c07044400f1a000e440e0744a4580804001a6040c030f01c81c01140f059030010495882040010000c640c401d44107400c0d0311003058180100141101c1c0502c10b00810034130308943c84094130094808051001f03032140030383c01c0125560202c0e91051000c115555a0106955801801410401140000c00d8400584030f43c02281502e2050f10018085848207030144241039079081d071034940c0b40b1280381c0581400c42d260001248062980305000038205100c0600c00f69007000b0300300105030f40c040401410f407146002c031895070348880303214040c0070141c1c0407901d40ac440e81c0a011055081c10207000b16034503586420701405840112840204800386884800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 574896393 1250 574895143 574895147
    0x9100627050105070503040b13030201030506061602041802040f020c0f071a1606090606030605090a0506040b1837150b04020d0c1e0918110409060603020c0607 70
    0x1140303010418240c0410349034500001955141c00c0201c048807607000510002c03a07001c0441000d400f404420300c184010007450341c0001b50403100050112802228100b16205407a201c1b4841c4102055040d03030006080000d0500c0c6140c4808402402540141000402d01207003e554014189103048070b000d840135404a541020380d50b131076600c10751000c50329941d01c00700c07456032442c06013a10ba0728034080350540d100790350344100484861004c00c484081c1c2d07901080c0288403140c8225507200c58824000d01c00c001207a105c0c5640c07118001c06c010401680a400190803510141c7c00315072034084032003103408507000782c05840000c2428014402504010780c0020000c200341c4118145071035000015400e181c803040d44000c1c080c0401c42d00441d0829001c2141c9840200c44d03100311400151641c0e146201451140410f0048201020a00c07013080703c00c840030b02840000301403180c09803a49036000150100d184c40018940d00903648003c420070314081c0002a1560550018070003c0303015019103066a0b103034401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 574897643 1250 574896393 574896437
    0xf090403020d120204030204060305030d060906270b12060106020616050a0c0f2a0803030f22050a030c0302150708011403010b190e0702010b010c02130b091006 70
    0x18005901444005000b940251400d0703103911100c10300945010f0b203903000329080d9030590b401240d15502c005601a901d82051140d140a403105c2c081c2070110910342010080c1c00080c050312036591601030000f1484043d19648204000d6801030300c4180b044042100042d256035003482071601602500c00029104151254240c0c200c4006c0c0d1580350500c400a00115030f0300042c1401165035410802102d001314144001b00b210354000d0b1039135001c81c1002072044d400800d460b940200c40c254014000c0c000e07504084043e0340c0d0b108202040071100c0313030141036001000c200c60003c082c069004110903c410b0561046036840450f02903004c0317404900c004110542d0452040342c0d0200059403c000501c80c00311180203c2c424983c0c018004101144c030400000c001d01e842900c1c1d51941018450101301c1c0006911500b90300080d103000801404c0792000006e8070a00781c01c10020320480108095048050065001c0105100080e1000c1020b1514031480e8155456501038400803425511005505c0341002d50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 574898893 1250 574897643 574897651
    0xa031a130914121b2a0a050a030b13021f080402040506100905122d0106080f060103020d0c2c090a17030c22030303061211210d020c0f09 60
    0xf040925206008859082e07850700381d007010000b0f016044140c0400c0c605013000c2841100014503841031a410b50007085080f200070741c01580a207900c09402c1004c2103c041c426980440011000341c080480c600c00903040c000e414294480c9070000603020f02006510212a61056200340d40400c41515000104104803480704d070001e0001f82e04900030b01c407034104035914111440c044012034051a0b00c0102d03002410040340b558040644036152884100d1001b4010710009019040c00341250b02d0107400b01c1031315000c0500003c0d003d45214080351041190361242140103200b5484c50085800c540360f10514804005500400c2c0d505c10940403074122500894100c15840d80440010405408400c03220720341d03040188111403c4100348580d0300346d2120410012045400c2500090819045250203012540c0c6d50700302100262846528000242121000c0310301518201c510b81d85151041c0383c4201d032602204c6182001d170043d103400c004407a80020300c041d8442c204070b03680202d50002a0500003981d504403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 574900143 1250 574898893 574898923
    0x60c0209060103090510020a0c050d030c0512060a0e010305060403030e0303070903030e0d06090503121b0f13150309110306070e010807180e070f0f050a031a130914 72
    0x8020441d1580203038008916140b0400c259000c82c48025445000c03604007400003408a030a82920008010080c0440c0340c0b000e00c0d40c00e0802c0f041603090070007490b5001e04100ca00582c0400e0012404a0b61800c00c03071401441120244422503841e403030219100d800039903048010a0030500c0c04049100040306a030b10490080c1e440c1d80c8032501d1600c1c1142c8080e41810b005821480002040000c1586806403050840c010380003182d40c0c81701d201040c2c40581d030007040039501c0945180d2010041306503c040315a1754080346541d94541c030702410320f11100c0401e0741c000310803800034203050090260940c00c6005800d00664810502095007414552070780d100700c4000000a0081c1d25403589503026103c125080900c0b86080c5422408a40b0142030b621219002080706940500802041c0d0f90b100c0210509071515251464500807410304c080c00d01d016200c0078005040c0c13204a164400480c14a503503081d01d400400c40e0700004030320001040240403401c001d40c2c1c6440d07220180d03030328030b000000c041c0340c0c0d02104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 574901393 1250 574900143 574900159
    0x50d0c1d040f0207020307151b02030c0105030a020c010e0c040b040501030209060d2414092418120403030306050603010b0d0515130f0e12030103140703051006050901060c02 76
    0x1001000000c0010141d0b2085843e801d1003e040941c900704032070710103440d1400c51296807801a20010f002200001c0b00341100411003444500140c8010506401741c4900f800c005d522504c41c40c0052001c0e0090318482c200541c41d01010161003080041c0039103035000c080d04c003001180c401200780401c0c0d0b0002d000c042c2d004041080421102d0402001c4082d80074020b407a048141a07400071803131030708500d60103600501520b8100b00945418009030b05904810148024401e08141c541c40c5100340d090b80f103d02001c0d2401c03200080903d80003182c400911070303400c4d0560b208040f070b82c1048040c98005020580000e0314188005c60242818811203040e5400c01e5603150501d5286400e120150600030050082e400d11404c0e0f01c0e515807500d0800b412680205c64002c01ea905401105004958520f5000d0350a1783c02410981c9140740343c8022281500d0300311402e0003850348041490791501c091a407004001d4810840c000d14450b601c0e42c440300640e00b00300c0758000340fa40e07500400c40d840d070780100c006503124402c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 574902643 1250 574901393 574901447
    0x120c21071404060b121506040503150c0c01060f0f0807050102100b04020415050702150423030703050303070503070311070818010216090905010b040c020c090403050c0303010303050d0c 81
    0x407659031000d10003403020801580ba41080310b0503401a105014040c4c00c2242400700c0712100542c440c003929000d40d00a81000c0c5080d0004c0d9480d41001246092180c096000c0f4841007000c404803918040b000c07000b40038540c1c0c0c8a9003440c0140d968418048810100f410101d60307028046846021100145c0c02456480c012165030801006455a840e80c071907400c000001c3e901900c1d00c0c0100c82702d180360b02ca0300d0301c0d41210b0060100d0564a10900d0004140401c801d0018503000354100041c40c8134022841c20300040b02c00403900c0c155250b0405403040c030022042251b070341e6206008501c207546955091000b030a4071143c0c800240240500200800418041041201440c1b0395030610700381c052041b9000c46459040005c181c01540d0081146103840304120b0080c00801d00a5240d54182550100042c041d88030b0001c2d2600c1c0c11700c10040c0315500b00700100e010f26100704281c2e009054131000b906e45c1e95a6928000d0003070b40c40340340903618075414201c822603058000c910a80001030f14100c01a89445 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 574903893 1250 574902643 574902659
    0x70201031401150f0315090615020f1905190605060a06080105030706050a0315090606020f06061f051902030307080906070c0b06011209050120040b0720120c2107 71
    0x40c8250b40420196031b001d0390003500c1413644400d0020040000002945410000010680b0704a88101e9007990301000390400c021200060360312026103c0483e200f010300480c0340250a01006044409c00c4840345a560000c1c00000d5101d5070240364101c0344448000c2c0e4442c030a0300ea052007482511303032541044200300300c0c80c0d000d800285103014483c940041e0004c159142c20200398066000610259600e46050010940402c0040f50124540004200c20300c0c003440040c010036186401d070566082c2030a4046000b034012001c1d81c03030040c0d0395000b00240d0001c012009503650000c40b0301e080021190300108810200100c0c070030340200d1981d660328003070001c82c0d11800c07280c0101900081c10490111640319504180f03104101040d48100008118405050000c1e41d0000ca0405c2c0102c960108100c200901c89047c0d0071202c0a55202a80f12188440b800741c203400c07000b00f000e00036000584559001c51480003c20081040740044a03203500c1000c5060406404030040005824698003052040c00710403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 574905143 1250 574903893 574903907
    0x200c12064002060c010e0d02160b03181203010311130e0303150307080304030501020403110102010519200d140c2a1905070806010501050f03060613081207020103140115 74
    0x140090030407803400c2800450340b4219000c0c030f845038140d901f003280d02c00070311903050202024104240110a0109042c41c40000300ca00c00038291140b840183c00805c10310074400d00c440c00d291082e0080117078803036030b60b41000c243c8404003840c02407040c10058082c8002100905c90f01c00c00715643c00007503045560b10803100c1001c910540100394036108a00000610440401c001c2000c0c501c100005615149107190400350700e2410b03c5041d0540e4100000c2000305000d98403d4200921003032000f007980410240400104c1d5905003d5032100100015003120746a4a0380140c1e94900314140088580d603100000a80107008240c51040708520329922100c0320340c0c0c82d038441d9141003000d400f038030701c60040ea0000001078800c80c0001c4889802070402001101001e0140ca40100000e0030110724040c2040014031007840300600551140601050005100e00500510406016650100c69421401c051440b003a078010f031070103d000a043c00640714211031119800c50495042e1071000c21806400201640c000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 574906393 1250 574905143 574905271
    0x12071a0f04021c060606030209090609090d080c160c060e0409170903030f030406050906100b0a111911040c030b03210c0d031401090c200c1206 63
    0x1d500c4503007240041a0b44e885000003d0401c0d850040c0d442280c281401035810f00200120703c20300e540810031515a5010407181684480c91800c10180e91300c41408007142e000f9100307041a43c205111200007040300c10605e000c19a60541c40b0700400903402c100704410745600d041d000b064090440e10303c140040d004005418007010040035a410007003038030f034510382c60303002220300340c5041c1d840e0001d001d10180c0a120f040d8101c1c004502a41e0000c2c1408030078041d5114920a03982000300c1380fa040c3e0000740003404107120b4008100e031039161100c5141410780306411221000c80c886c618240c40c0000070750280c4240098043d01502802120b1691200d20412a102070541e42182000300040100c402d400c0c040555020815140003c084c0441c0350000c4103402d05070059070aa0307142c0f901010640d078010f4208980481980079105007083c01c0101c09040113144d0b104181c1040b210b0103d500348943c042982407055420501090b00030403014503d00070440d8804400303d042d1820113220b40007003c01124982c113 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 574907643 1250 574906393 574906429
    0x923330105041a04090e061e0a0605030316110301020a09090f0b0a17010c1b060c051314102105130b0c09460812071a0f0402 55
    0x1401c3e9aa03042e07031030200024070034004003800010709200c2c118481c400d003104400440010909032070100552180d00e9200c0e031490050503842c0000036040c0000303410060140c40f02405598039415a1000090b0b0303a4022081118070328a80404926181414800e6480d4003002e42c0c0e039151038502d0001184010700c0c0740007048070156101c070102c400e030340c43e07512003240240014185550300c85c2c0e1810700b060031140c1d00100941080001948292000c5e030068482c00f003d070704a1000219040504400c2c1e0f614454050710708150500e00d00002031203039400e03986c04c0512405544110030a09201c0003140c0e10101c0d980b010010307079140c4000000030f8095074041c80c0d0000d8644101501422070361241e0030354080c00c0b1340760005002c0006005102d0305000413203110401041000d44032003548045100b5120f000650103134802e6030b101820001c201c840481d40f0004200d81000d0368440100240c88a500341d124400541b4002c02042241441003001412035110352002e490900458503683d003044119091400f8143d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 574908893 1250 574907643 574907647
    0x3050310050901082401060503010b03250302040311090412110a0602070b071d0609010309030c0206191b05030f0a0203071b1805010302090f04020a0923330105 70
    0x2425481d90990386020b418540010585c481010302c40c41020010300c0024500484500c0c010070039960440150307810748a1900e071890712030b1b0f1650f10003d501d0750480340b802c8500d0012492150721542507801882584d0040318201c000d07600d0724086c02100d6030282c2d00104000c82c2544000c14591260407500000100705007582d003041e4031516060b0036a0844400ad407005940355003401041a045207424012440040358501c144c000d170030018810340501c80095040c5074031201703070320f04152044150f120030755030041c54191290914084140c0030b644095031900802c09610451000694001c84a075010f6400002503280401c0c2c440c0000d074070741060200c0d005601c400d00c800c40000380090100616901a00301c803d80e039510b803001a10780703081d4214012084519003001480940c94140300c0301d0b03102220000b00340068540344081425240300c0d0b488811003900d02408600650522004412f9031800da11641145032110310a440c1d41c890411105010840c0c1e806010600000034240040c420304141041c0d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 574910143 1250 574908893 574908899
    0x1d031c0b0d1b090507030e0a061806060b040e0c0f040302220504030e15270d0b040302070816050d0f030201020c150901110a090902030a061508100603150303050310 72
    0x701070300b202c4050709144030189290038809001a441560b501041d103150510921a14600c00ba480e11070014000e044030341c594101200c105900280c0ea030156900620401c5082c2e6525a00b80030794002d03000b486481d804000105502c05c1403c3e041d43c0d12051240e0140307140c02d2030341e420090044900300790340e070f40a8900d61242c0e148040a20450307100f0390013516090003009009041003848007118500010340382c02885410615001c034500d091035000940c883d11003211800e0009000500c20f12402003410b9014000c100401d540860008c0481e8640c0c0101c6030f9110620a82103100303c0b6502481c0d81180d104403010000c03400450b0740c60840c0c0d000b40001484e041211912600749850310310a5030f1000342c04000d000d40d280e802d10401401d420380394201400c2070000d10340140544a18860041a2a0080003240c091000b9034001d50040112a074150143c2d50045006041a07034210350490032400401c0000450303d00901410440c56510301c0710440d8907080d03035000d4480390800b403d05405040000004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 574911393 1250 574910143 574910153
    0x1b0503190b0a0b01051902100903031a090c07110301180c0602011a1c1a0109060323070b1309090f0b10080709090309081501030516060c1401020c010f1d031c0b0d 71
    0x2c801c271900a680201c0c503010010030b03141c0340b20000803204d40907880c1c2008124900900c941030319401c0c0e0303006500d001c00d8444540002e002d412900c2820132080700c1a41040100000e603403503001151243d4000707004402c4201e000720f485034000241140c001c85180351100a20b40064901c0508511440c86d549929100070310085200501341c20155490f40d0b203031001e0051107804110520210026200707481c1580c2d003c8101600d8400398030400310382040100b030050215900c100141c000c1e00113000e041001481701e0a184000707014803007060360000c1c4a00081403044051006160944034000d0050214a2a10551070020712140506a040101540700400c20388418400b40707552003060300c14441c255041d4104107062101e0040240c41c510100c0c1402c0010360f8026490407003c98201c03031035005560b4000c0b0039a003e44540c100c404e8503540b810156000e8010700d64840158030104041c0d001d6840540e0a880e5070307a20400b000543c0c07141c541044084d404149400010048801078851106244207035a9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 574912643 1250 574911393 574911401
    0x60b120c0706050405030903070b031003120c080703030c080a18080a030e070803090102150103051906060b0c06040507060f02060c0906120f0403030513030c1b0503190b0a0b0105190210 81
    0x1003194170350070001e0401004e01d0b003045903a01500103000c0c2107165003083c1820503803002852000415421121290b00f035410b01680f003c042050704101c20694a01c0180782c004e0080c0400c8009002103030400002c900411010320950024007004218400e0000300c81e10703010055080245c004d010161210f00b08003850000348509001401c000c0019600d4182107000681048a070042e9030042500382401040402c50006600d41d0254694151740d00300142c0d4100074010706200d070007084172428002516000d03202c00045061045001c1c0080e41c400c2da480c0e0341b08031440070300b584a40d001603004501013203807501030780000c0a040000034982032502c0e0b0094a001c5030f00030111000b0030300401060811051540501070b0b540d01811040c40018040490340e0083d000705010303000a440e03560300e0a13140240910755070079a0083c1070014100c032185414101090398007140300408403240000d49010494400240c016003028040584509091010321002c3e01411040e414200046114280e0400110075852003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 574913893 1250 574912643 574912651
    0x6050c090d0f050c040b09011413020c0a030f0201150b090f040608070918150207020a03060608070303030e160b0c0a1a15091504020702030f030a0201020301030506010603060b120c070605 82
    0x42c1210950316810610b003803e9200741e2550096080ca03848107280c4c1d45081d08a81500c032009008044440c42d074000c074407450003001008210510025141425120000310315400310303c2030350b5440d91803207e440d04034280c409030f0b40c080300c117000714180c1880500000c4001e800300c4100a00444100140d810025003075034100c0e031084003160010141403144510034024600f04109144508540b041c00c1e80c0c804180214440038502c0c2c540e4003050720411581d504032000d00440d009013081c8a02c40d00c41a1454590312240310481c0800d00e0601c600c5045040487d8800500d0315040d06200500e05e0035505500640c003501038030300e07140500101c02c400554002211152907128640b04c81a03441c002ca903d048440300e60012034480c85030101003064044200040018000e41568056101c1e4641e10100f4a001d0f680c2d20513104500010400f00038080d81580518101c9004004032805660b03a04029000c4500c1c078000e406d6400e80400030000000200d00c1816000401580594a0401162107071411500d09603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 574915143 1250 574913893 574913903
    0xd0e0d0209181209010c030c0609021002071404060e0c07021f0c1203021207050c030c06010e151203030609280e07080d17070504080d080403090b03070c06050c090d 72
    0x407202540b08020840ea0380600c804040c0d20b490845000300203041400580c2c8000e04001508080004101094120001140d03000c0c2031001c0c84080b005020f034440c1c406000c0c1d1241c601641d0001121450303e40075140460340034088003042e40e1200a0483c602e6802010180d8003c900c0300441c0007080e0390058052059001a0b840c0700704ac4201d480c2a040800e01115044201401030211240381c134a183d44440c0c000d61281080e6a40d00c141c415914258010040041068065031380000350211032101c200388220456891214051800ca0810509041d08010030103542c2c8240009102802c201610356080345468134010411048906201608450a4050b508142d11154411000201001100050100c5501404010807003140040c24210301c54000c80c8125078940200d80072600030f0040360040e042e4141500c40041581c00003800c0b040c1e080c0c40460020706004000602c100c10381c0281e9018502d40d95801d50140096202c04001c0c110151204219403010003480405d66545035441c28024452 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 574916393 1250 574915143 574915171
    0xf190305010912090311121c02030d050a0608031917132102100906020403020d08030103111005030609041a09150901050403020a08030c090a0321020d020d0e0d0209 72
    0x640b40c10703c0c1c40c4000c80c070001e0500944034000c0c40001c02600c2e0407940001d0950391080c2039046062903500e0030700041902050781d080540411040355003c801880320f84901e500911264907010304070401c4420a10682003a900184214080030300042d8513020002c4943c505503410040380303010402000c50a0315040841c3d60110440c6040188014004516020310b606064030089074140c06920342000407800c0c211903580d081c080d41000700c6541510f01443e0045c08215004120f45001840743c1c0c0280000d403a070340c0c614a0301c4030407807034000520700c0407807c0f642e81c080c1942c0f0b400090004843c006042180d00d1100505c8107010308480c108090b1050006000900790303600386100b40c602e00342c00036203000070340e034149010480401d0b00000c0c44824164481e94881e600c0da245820507480f4003403802ca459105152003000010f203d91821050366996042400519107401e641080c0e90fa4030903d40e04bd40942c10034200013014a0007008440000c00c8042c000c0c008040076075000038000700b400c86c2c0403c0c6036014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 574917643 1250 574916393 574916411
    0x911090102010c0e01091a0708121801060614030c0d0f050610020a11150c060405031903020901080402041e09050607090f0f0905270a0308070e0d020f19030501 70
    0xc24040c41000d200581450300a01301c05000007005100c090040d2002001d040840c07494426105040710b40c0b49401c0280140c6546860354103142c2c0b4902034820544480042c2c0c1c0041402c141841988110741c0151a40304000302c842281d404160802040c1101410702801002a800051b01603150755501d00400054070b890500d0401c0146100c04403040300f190701c040750075800940e984044072411203081b60030780000d0543c032144694070f110b8092269014055507003030204011000001c0c00c1d4000740503100703c01c07031400190100e0490069a041600048142c80441d0143c106980900d050744c00d800507050001000100d41400d0f0b50f10607100700c900d684000200311000d41c0c408800e90141c5859042511241d1804007840c1801e0114060f01c181a41d40c2c0e4082000540709040300c16071801141c4c01800a0421703001e000d80c88502a000c1500450700300030011381e541d03109022600c1d80140061814003034141c1c80d0240700300401d10782d5034190010f00d8064105a550400c1d82076000a52180c0004101c2c007503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 574918893 1250 574917643 574917647
    0x30f0b01050a0f080c300d0906030209030c0112022104150905060a05061908031e031303030917040e0103030201061d0f090703020402043f080f0409110901 68
    0x581e81d8408070240310007520030704c1160341c04103500c603d101007141c040004040409014120412030380c002e64010701c0c5051000d0300c8003000300350b0300c20f8244151a1402d02c0c1f55a808150f00303912460600940c56000604800b4441d03020f4000040d40001c1541d0041c140b01c6240400e00940032000310b49000c4c410900200410411050712100c10020200024440694107a0310310341d8400d40900b003150307040c4e00e0300002421626212007801a10344918010000b031a503c0040707070307182e60241281c00c103060740d03e08035580c41a5074482264060102d0100c3c5c25170f260740d56281140180b40e810022108000690758804400c6d0b488030161001d80450b03880c10302c0315403440c50080e007119403d07070001c00c0200403210b02c051000d49842c0800ea00a10080f9090607a60b02c191000b42004a00e800c020360041c80800e01240c000090f070298000303d074601d81130140b0585c200381e08000f8038001c0c0618000720804803022100189401e00030b083c01702850680c82d814039450b51200003e44a4001c915080c000012510409035a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 574920143 1250 574918893 574918909
    0x7081b0a050a03021008091c08041a0402130c02070e04050d020d08071e030b0301141f0b1e0705100902040c0819021b160e01150e19030f0b0105 63
    0x5812201d007050070f031031136010a41390f0452144290500ca01000000c903014428410802052141c1f1121b507002840c0390000b0340400c80550381640e0101000010418401d0b02c0d094960066400401c2c1410700b444041480b805045128001b600b107009100700054500006044603000e244188040c08400010703d0b0000d01d01844594a1000c10071628203120b02680c001c030307103802c40058498401001072404201640603045060017640c0540c60858000000c150800402e8060f000102d003041d403250951342141e04e2010385010706c400001c0d04100380103100f50004445084e502c0004122420480d150300c4190602560682000c2e046440700701e01c00071881c00c1c0c031880146401724140700c851170815200300040280d0181c040500d003640010b0301c144420ba44451444428442c0080310000c401e40c100755074401410b481440c595285041c004900e2280c0218581c0b1169405d030340b00034070101504100000800c05420aa10004121a020000c60a8405a458894050000c5401c154900b01c00d0000710 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 574921393 1250 574920143 574920149
    0x305070b0a23040501050703050f390c060304050a15090b0f01140f03070b07080717210c070b0115180518060402090604060f030b030a030c0b0907081b0a 67
    0x965100c0c240000c00480310306070b500f6134500b031800c01e44802c20f62505640314442c40d50140070b19000030680702108403481c41e0070308913aa50201e0300c0c0443c0203411500e0b41400b035a160400007a4001c042e00c03a070a4200039000e5603000e801b8104466401025403212888040c004001c02d0303806446000074030070b2210718151550405075070036102103198908044900110900030030345108805c1240064036981d8100001c602034001401c081d982c40c480340c5400540b41d48000d004841d0360951060f00c40710540c0316400d8852019020500007024110003212402080004100c0c4a040c54240450300101d2511900203000e4102e8880c1801e010300d6140005d045154654504400c440030000f0900c0720352103c405400001c052400c400c50341d901c4040000d00a40140510a60051800b280001e40d450344001c0e503400b02a600e4034100100340c041c009140d100c0d100c100015001c01d00d00719000c0005800d000501c1e50043c000c00580c1c4c00b158946031a6030a2a03002201640920701c543d0b100b07030a41c41c1211540f001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 574922643 1250 574921393 574921427
    0xb041b0501140a030e030301080a021201180f0f150f050f090d0e010e0d1101080c090a0308071406160e041401090b0a080601030f030e031504060c03060305070b0a 71
    0x42600d4000020621007220030102424440840c402c2c2d10305000381c010782c602120380400e594a0b581c683c103030745070f6841c1e4900d02648100b41012491601840c1803041031558075030b140881000340303816100c24003480c0503d40121080080323b0141c1c0c01040d44017013038080194500c040480c046944080e480143c0e10040c004e161103d90714002d0009280d000100f60001300a5410324070540c01a400050398030700305000c017140d00408903043c00010807807004480ea00410090302c9409954590000c0700d0100d00500d5000354000850b0041800818641c80142070b00c1c40c03184010000940340450014203158068030b0703441c05c0c11004101e048400390030802c060801081030300c04008264076003220790b04811040c41012070f0075603142c4126089489110610002d4180801180c1d681c1d6920300e4501b043c218520420b4000400c00d0714440100d29001c01d402403110841a140d01190300c03a03440380001044000c0000303013819591400080014001e20490005090800e4000d80b14004110013400d0f4603000f4441c3c040f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 574923893 1250 574922643 574922693
    0x41e08040e04060c111b19080303250219111c0b01060c02060d0b01090b040f0905150f012001090f060b010503133c0201021005010b0405040509070e040b04 68
    0x8081d000811610706c0c007003510380c0c202d504501c0b00030404a40c0c141c00507405051840030302249000c00040254010345900384418030500c2c020760740041001d0105009070041c4c010000442e00507211a0300800b4807070061001c0990034040d580003d801f0440201c0708034010204100000500002c403400c0c90050180341000794184005500041140c403400c041c40030200c0d980c210101569218040e5500030300000c99007280d5440d11a060311a071560703103118807220241000009181d01005000c50310040d40040c00071003852138840015a042c0042d650203088202d814078a40010324401d00402421380c0c001c11542e000e0750032070300b4072805481070114040e052100c00c0013800344d64503032000740d006aa60005141d284019150600501260408601e09030280e0035881c01030003500e1103615038010034801d808460b207003051002000d0544a09204601984034140b104116074203240d00560381c081c02860a0ba039070180c403107521082030f1030140e5069850711141c40800040004240941998103103100d0928 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 574925143 1250 574923893 574923917
    0x1e090a02040c05090f1e090f370506030c0a09020c06010e130312020702060a2a0b150118120201090902030c040302010318141c05030c03041e08040e04060c 68
    0x2490341c0c042d0403107050041800f4208081003401b05041340417003d900074100c0e6000d0903c0700e98a10341d9801a0b0785215510100109a2103111103400070a4801d0300041404648074070f0006820000c0030000e044940500400c2504a80f81e56840040000f80c803000c2001a11000078916007440d00c0d105801030041d0081c00c00600c4104401d4510070102541d240c605039148213090240380c40a40030f160300080d0088000701e5046542500401240c0f005e000d00030b60503aa94900c012043d600300c441d03c07806046400c51002090351032120b0303000f505034401c2c10306142068012205501071030311000d9014890b85035441000200310b603030210400000b01424101542141000f58000e80140f25500c002070506544031040ea40d00740b0b0f107142d8191065001a0034004031100c0c102d115881d0746c0d1307181504407880045d0305032002c46402602a64051040d07081e00d1030540c1d03030303503500d8210591031018603c11050f51240b0400000d07141000030030107000d5140307081003e410240741500a58480c1d41a050501512030440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 574926393 1250 574925143 574925149
    0x31506051b012703051326010b09061e060d0f0b0a18021b0f100e0d0207051908160504110f0904050a02040b1809010801050106020607081e090a02040c0509 68
    0x3e515482040751120321129403030310f0709450754892882d00d82d071220b0103c071001520488200483c0001000c00000c80703240e01441c01c07414200e40d04807910940c8906004007145260138850501400785440c04101d0020255160000d80b003900841801c24141c1e445220429403200c0d54000c100840405a45614433542880c2003c0c259642034540328101c658086040c41c925012a0390004050302d0b9041950003140c0720503072042d203540c0036964a002582c00c000c0c0705410342800103900f403450b07072242d40541301d00c505141c10008050002c1c2c03c80610305c10840404624100c0c14000b075081a00d8180d081d418542c541010700040d550894410f180e804410721405a00917440b000300d420303008045038001003c3d610700c00307482e0090086030803026007800080707118000d401f508000d100c0805411035050f00310380c2c1c3e503444040c240d8909002d2200140c00c250081081e0a00400007650030080003c205020000040c0303001058202c11507404526900400010055042c10301c03843c00981002c1c81c19030314283c444004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 574927643 1250 574926393 574926431
    0xb06030c030f060406050d0b0a0b1c1e120f0e0108010e010513060e3103020304061b1a34050d09120512010b030405120a031506051b01 59
    0x200d0b1141e51107503400554980c1e103541c08031015140c01080c1c50004011410034440e51241110b4040700e942c60518003141d5860580da103d4080c4902d9010915480071680d207010300d2103107106a003d880c0600b5210240040c042d10080030f00441c855a0303200002c00b03035141c01058244c51000301414071142d1801031091500c841c1350030741500c4003039603201035060b4400501d00007440c3c10752010201c8400320003803202401c5540c6581021346500c030400c010f002940081c00c85270703041042005025900070001046540e024001c400c088034000011210000344a45503844c000c0c040902840705010104100708200c0441440c0c00c0f14800792003007002240403008056880b40c1c0300d65210030140b207004500a40072082c15003201000c160f01100254011240440251440c0c21240d001c000c00001e03e8000300c0c500c0c01d484103480c80780e60408024204040c5421241206920040480c0c08040e1201c407450844c50b103400b054402401195901c41d5203044580c50160240c804002c0502d103a410a10100c03074500312220 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 574928893 1250 574927643 574927651
    0x207090b010842010e0303090303030708060a0b0a12050f04050a02330306010e03030703210e030c0f0f070f030b07020c0a150210060e04320102030a0b06030c03 70
    0x46082106240395501d0f0b0018140015003c0320302c22101040d0b0351440d98412010b10110003030300d44014920b403010425450b800b031603000302d805510602c00101c0302d5106108250b001240900f5154503a9150341809070340c0c1e480050400041800742c94112540d0001c1d22800e54081c1025a00310074a0819945840d1151650341020744144c0c28102c109044003811041c40701005000311035032007480c50b07100da940325a0f00308070350702c41c003241c4c032000c11811600340841151420ba906583e46428610001140034a28140d82010824140e0701d01820a182d801000140541c00c0c1c0070005081200c081000d0514200e000e40c540f042079088a40704010034429002d400003900c1d80002610015518124102d14040d01c3c50609a400080e51000003100cc62148011120b04200e0707094900d8810002c203120161041e921900c6820041480081c1c042104051400310110306203820308502d00f00701c07507411a1003641044490081c1d40c004148400f903074151182012580b0103460b40d50451034504010282404018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 574930143 1250 574928893 574928911
    0x5120604060503061b0918090715020d0c030207030f0f060e07080c12011416081e0403050a0c0c090609050f04020d150e06041a06010e0a0b0c010f0e0a030207090b0108 73
    0x4d22001580a41c900303896034130308007800940c0624102c1c5021f941128060758012400e001b18600410280101004940c45010603001001280a4100d04890f0b09104420075011401040008000500a600b040440a0080000070000c0c012800c0074422142d24901c400b0303590703000b800c1c108800300c00403410810540d0202c41d52107051b44d851411034050f2091401d00c4950300d0b410000c01c030078078010020707041030780d0880d80d5800603031b603a002c030301140c03001e4030090b404100070344040090002480390b0700070420404a445c000755841700943d40d5001c55141d03030300300c00c03401d0341c59010a0222400b030340300d101c1d40100c000880003d1030130250089001142c4051010700f0034041007400d0300300002d05400080699100c881141c100b4500b0381004003000003116040c00140708548040f840d01c0d0301c02c00195121580c01800b060485181a6200c0b94940c000b0490741415501d551141c82040041e200d072100c00c0068030701034010740e03245240003803c102c0c070f0f5007220051070702e05604a903040e42d0142915a120b0003013 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 574931393 1250 574930143 574930171
    0xf0d1202090a180912030603110d0503070c06080a0b011e110f03030108030711030f060105100e04020d0b030c0603040c030204050703110c0f010c09032109030804060512060406050306 80
    0x820120300c1801054004914540c07101003800340300070b80d9a10244032680034006080c40c0c0121704d40f04070195040c500c0301910150410309022164038245452101007032040703046038a04a81c90f80c405410300000d0340700700c011500c08010455441c0d41c5001f200c1d121042482d0050701c000000c11b5409905a206c22914200022103d100c00e0215041002102404601048980320342e9a9007400e6900d50044004494183d03100c4c0c5e40303800d035080021300c1c80603440b030680190016a09003c140694158070040e101d080080700e01602445856500c028210158840404031741500391030140342c80d1410002e5918041d0008204000100c1c0011842e002960750480e4041036580b0f82c6c0000310040c2c2140c411300b20a00c10001031060b040580042c3c502a030002c004024842d840341c6520070380c0e0400301480040e0030040031841c107034090030301d45000d00c8a43d40f25003042410b81c0e81783c1d10380d0f804541080d049140481c80000b0488014003804e0069680f01604039000d00880c6e0801010035100c4101070a410074410301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 574932643 1250 574931393 574931407
    0xe06060f300106120501020904110f1c0b0a03050a230304033302030411091b070c0b0a08040516120605090a02060f0405090c0304030f110304031b080f0d1202 69
    0x1c2034006a00030480c03078245500d0041c8500700713203000790b010742040380c401d919042011800c80004000d9605c0c80e405101740c00e0401484d8820070b088180c11050704209250f03240760000d1665078441c0301001950003080100b04d20b51182c5000c0e001085081200c0d85104004640c4000e2560000111001c1c1c0340d200701003800100c80a020f02000c981c148100c81c82a80142c4c04054a4440301c2d805944290b00540007080d03031040d000148440c912003690b031070050b486809464002108001c1c002c100c40c40c49100c20342101941c402d900c1580307800c00c845113400220300c0c13021f11050000030011040a500c4c141c6605041030b01d4200581c2201d1519a0010300076038442d030010300c8900044c0100504160090034144e0340c4c1e41010486030040d801070003818402c42d801400308002090410540744100c2c0c0c1900d4980b01f64000ca64281c90300c0940c0203030680a072004010210000d2002d000428800700c480120224903400c3c0f101050804d550a5240c5070383c3c1d809802c2d06040c20f030740039017142c0064400d0600140d480324 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 574933893 1250 574932643 574932739
    0x6180207171b0d050c011d210405030a0602090a1508062e020d02010606030506130b030f03130e010501020a03140a050403060e030703030c090b0a210e06060f 69
    0x801a04600c07180c0290581c1c00c84064212004003004500c08000f0094071408008680303029008000c540101d074400c03000231366114440020030390781400c4505002e00300396031100040c0c54058803090496000c0c1e00070403190300e281000c0698602a18115034586030120480301c0061a40074000c2a40f48039a0140d160452a00421480c05840f54001c5034009484916544040d5842807641003041c01036207010000100d5521038030400d0700500b8000d00700c0c014500380b0a0b40001900b070b400d01c6a90306016080c01e5400d54802000140600c40750308003c1c5104602d070080410045030140e110f103055402c00e42c0c807280066030040c400440c00c0040301d07243e526580b05900854030b50040b40c1008002901e01580004100000006020309034441d541c280b00690a4240443e01c13000284940240000b0a2140c0072030580254592005900700c082146807204501c0783c054150345143e500c0000a40111040c4065070400424544140c6820354001a11108070401480034015910fa080c04641c040c0c139a202c2d800d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 574935143 1250 574933893 574933927
    0x4030305041103011b0f09060203070f1a011202030d0906050a3608010b1915031104150e030d02031b0c060427060303090e19050a0618020717 62
    0x82c01800030494413484203080c4140c4900080000b001c504c00944070242c0620403084001074941c10b0380510b0400303000303540d46445400104001c41e24491710802c800310041118015500800c9003120011130050240189400d0410f002180c004010380900103005d40c9401c842100d004141510f40245c0d95403a100035040e941500450015940c030b00d03403802c4500c000000c003000b07080c0c544200080080ba02d80d030040081100400a0360540c00f5100c03901001607800c0ea524400b8020420304010958a10540c112201e81c0e00c1b580103802065070441000050903400110515400010342c01046128034900c0080d5030f83c081c20040070120300d21001c0709039280d01e0600000d5910b0a0151500f074a07261182d50004e800e212070025480d0f518007100806020113070754003d010440b0f8050f19034402060410a4216440f0300c014121920345000120720035a02c00c070781c45082d1213030074100300006426082c0305000b920410310082404001e40140804c201040c841d0b1a90300009910a949541c0e44541000d031f0002a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 574936393 1250 574935143 574935173
    0xb090105010813060c2a021809030f0d0603050607030605090a0e0c1003090b09060705070b090a020a061e051806071707231609200c010c030b030a0b0403030504 70
    0x21420f0601808440703810001441d1807601c1d10307070013002840b0b0103038050f85582c0c03402c80041e501c07108e80c4800c0000101a10b440740e40041e95441640e01e030a0b10403402d444540c0c0104050204155240401c0060000c28040544c100e0341525051040601d800700044580401400d802d115070760303600b0004503141040140c441e003100b0261511310707041107100c1e0180003000f0b20390080c2ea000180200080342c0c82d0010610364450f14040d16080e04001044d01e500c0a09040205200b620348079240030407016a540e40b01140003015182d50380c0c0c040c851a09540803050041d40c10180a20405200400000e03c820b00c840031003401c2034904a41b03c04003403c1480b0071050810100c060400c00080c2e1809002c02c03002000d440901c5280f0200c6a03082d0030130150b0361824030409621107140118000d1003c1211500101d40700002c3c02c44003410b050100ca40e0641507404940d07511910307952503400c8800c030341d014091000d45e210128084d10b10303c103094681c04140c11004000904243d9690f0009040000e815000048 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 574937643 1250 574936393 574936403
    0x20c0718020904050a020c06013f0203030d09060e0c0a091a0607050c030705120c011d0406060503090705010509060712030207060203040f11040209150702240414040b090105010813 79
    0x141040c0072030703400a47c05030740c403490b903401880000708600a082c080354071488604030010300080340e2010fa10584031041480546010720351040d080160740c04002505400da01e450f40002d90240c40e2400390210380700403105e4011500501c0e180c4015a4800342c524003102c00c3c140300441c65590130a004400c50004480082d442980410310b0b0040c040c00040300c1c4611101a000c0365030f01174075030080000340042c16500d04041d9120201103560382d407281c4e2105003030681d1007131000006058540080d0a50b0165040b02000135070100400c02d08010401c01d681c0140003e0829901d0b082d80900031401501c50b2881c080c7c10008840b40c00c04143c4e202c0da0442d41c4042d080031086449042038600220310641d4000d003030300d5810f81c5282e007250b245054400c84501c158001c2c03071159540c100d003076018065044540141d0b4010350a40081880301d00d48806141c001800592140e80c481c00c010151101404000c0c00e140140e1030404170500f5030f10b07a1800507040d20801d080c000203503601e051800c2e0f1650202000100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 574938893 1250 574937643 574937651
    0x1116060507060605040605090c0a030605060a0203090306011e210606060c110117220206041d0106020d0806060c01231806060603010e040510050106090504050a020c0718020904 77
    0x500158004081d1080390310990040c00322907034030002c0000340c94460240039400020100410f50300b8000d075004101c294201c1c10003080c801d40d2031000a205401114204d005078000041600551400b4001c1d2409010405204d40c04100c08031110103a0307071410f00620b86038a5031020040251210a0214442d942c0e00200903c91280c48520050a048502108450b1070345c20401d00502c3d5030059110119422451440b045142d86000d0102c0c41d0504070a011900c020440102c000035855140c01400a0071074405c1c40c0d84e1850b0301c0c820021141d0300503405a021908002c45408419501920158000c5d43c115151031300c1c4e0410401d60b900400001c021300c0352403610344812802103000704904900c5645003c1011314280701160810fa00d550b0104c0360158403030401c10050000d41e0002e01440d4101d4003400c201c1e005607034440400c104a0354207800030004601181d408108900d464041c8683c08070302484254101445e030640b1507a1020b0314002c00074600301d00c401c480c40c0c1c81e42660580f200c681c0014400d01c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 574940143 1250 574938893 574938899
    0x405030904020a020a15020d05011202030d0e130e0d0809150a20130602010506060a090e0c070b090c130c0c020909160608060414070c0b060418151a101116 68
    0x1b90095000b032034070107a00c50422000044091070b090740110269006401b80011b103690380c408507900c0200c154021360140513440c880c00749503158401c01c14070343c1d54000204445231004c10041d1018400030042039150b030200180c44050458900d015411110365040803a0345090101c85101c8240b0129405040d5200031031104004280d49990600300c80944d0000c100c2902e0396820321070141700e4211000c0c042880b000341040001c2081c0304007507002c030404040908004480d40c4d4a003004009070f440000c5548a155403c1051a1100c1500c2d41d1115504040001a000c0c050140440c01030b201d0203031161001c1030001d80080c205106040c2072a00d5244412541c0da142c40c40900540c0d030580303003a40618903181c00024031601c1c1b01011809141161203c032802d408907980c508160f40003c00c01a006511004001d0342c3c0d4a141d01c00104043c8501006110000140002d00032503540b0581802c80810441005206803500b1268011000b42441c0c902c840d00f0030360120314500041c440011a039010842800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 574941393 1250 574940143 574940183
    0xa090504091a01211b03020607050f0106090209090601080720010c0801120305040b07030c05030a03061403062809020a0807060f030b0319060e011a15030405030904020a020a 76
    0x8a0014181d0407840c960590300c0d138010340702e1042901001c42e00b808040000300d0124008060824205022900908020f070310303a4041150723038100400c202c03280d511001c120007144000380685000f41c43c1a06046091040c044006045040080c0440f81031104039404541c40318402d1040000910301e03800c0159a044101d410340e80240a0031511100144401d000801e0f90a2440d10700b100c070b5901030380d03203504290929203984402d0f80030f200120188103a50fa08040024428070140c44500e4040d200051510301d410303403500c446000d0002c0c17948030760804010070000080c514020041207000340362484020020402c14401441403904c06075101d10031000000c1c05020000d208421b5443c10341c1c9210384614542020b4090b56402c3c08042c3d459000340710341c0e01020b038000c24840c10b214000d0701c000c51209020901c4a08481c0301207d070030b2007110003190720200c40c02c02070f840807141ca8500041e54954034040e1542511380c002c00414030302c116000206068014800c1208001c000d41100f454078402d40a1446 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 574942643 1250 574941393 574941413
    0x9050303060a0501052a0f060108031b030a120f0608010204030602360906130c080916180b060f0f07030e04090201050d0f02040b2b050613020a09050409 67
    0xc1480351000003070204040d446481aa10030f4070003481456200300021503200b0006c8020340170b000d080e00c1401e14565010004200b124000d0840340c011f903030344105070b0b1040c20b0301e11640000030102d5802002020240e0750310403145040381c50b078410001051340350022404050310003a07000c60701c04c5d0700100303011080c001e4540c000e10010954a201c0c4200400303502207e65071405403140f002040040324044040f6082c0001119404000140a020111185801c440840d20750b000400005a407450030020030540c00c1001c4801c0510b0100ca0307031805880c141d034441e01c2001481c0d0942a0b0742d111200002551640020340d9043c0410050260300c50305103030040025a00f04800560000301b40010b07008150034540f007403041098040e074400e1316014121071300030041c0c04081e81249003182e082000094401410015222180e0342801c134001c110340303914503000d8107071a03544117002c035500d0034060201075a00c00c241010031405c9040f01584548079101c003502d02040a41c42980c0160034018000c04020290300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 574943893 1250 574942643 574942651
    0x9010e1506040f082815020723010c080703050907051e09041a01090513020405090f0115030605090f03030106140408030304030801081b0105090111010e0a06090c0801051003111309050303 82
    0x31710100f41c0340402e1500c0f03400070840015081000f850003207540e100c0650010812140102d180318006c408080380783e900300c5407010702504240d41d81c052000e40c2641c070152443d00401d8600e824042c030309000b040303da02c40c6414400c440c884c01104001e4114150242c03260540c852004055003440d01e00b07401c1201009400c0482c43d005094420b0003c90080c0c0144582c5010301d00d400c802140c0c0c40b005609100007404090501c0609205101d50394100d0701c000d018030381607801c9600304908003e1440c5003110a840000c0c10610150700b080b40c0208030a840041540e044500c2c500e400785560030043e880d030403280b2035500700c041140000003c000501d0f070488a0b0034101c034411412241900404000954072400000c0d54500140e0104580707850366104041008030b00b4038200000940020a1407001d250003030920b011103415880354078130018401942c4404004003134070b9000307120f00c2c544040401d016440a00004100e02e00642ca210b10360b07100c0e022281b4142e03000980800508440b8105680e5070b400440d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 574945143 1250 574943893 574943923
    0x308030c090a091104090203070507060507020f12180f0a1a190e0f060c011e0e1501030503033706030c0501091d090f060f0105040b09010e1506040f08 66
    0x80000070003c020348036404071100c03000515420701c2e0070082d2800117580043c00100030481d0500145022603070920a441c0184902d130003c2c4019044511903d003001032088264132642e50a00070541e11506419030340341e21310b80c1112410603d0010a00181c00328019400c01d190743c1800c41c2803421110b8016000b010400c032400300c0311511030030041044850307059a052b4140c00071240d101309400340c144000540249100d21001150784100d1f1310b1039202428a6003291600343d52141980207007480c0c18020004a080655142c1c80fa642c115100c0d076036a0321024107202d9021403560002182c43c410300007000201280031308140c801c20922040d86c4040d002e1030100762564114290002141e600845401c2c0440f42d82a050085880003000034902d03114004140501a01441001220b12801402203e210f6000f40086805c0340d41040c0034001203034032600e80140a480e81c04018803200900b01100b5601c000404101c8c5034462620700031800c1070107036500c4000c00c4a2031401c0810400301c0401c0f0f51030402c14113 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 574946393 1250 574945143 574945159
    0x5061503100507171503010e100501050d020901030b071205040305120127110c0115090510060804080901020c030f01020a1e0c030c1a1e090d0f0f090308030c09 70
    0x1c4400542214019502d00c80440e080e00c41c1622a559101100703613024040c400798409841d10711003c00c0c2900c81410340300c0600d070041c401a1a488009114807800742406a501d40b003540d0150380403901200041c000904000e90305000681050300c590790500c4000804030050003a82454540500301c0d4003c0c100980032460b0f40b400200d040d08203200604101d0505c00b0708a8407018501031090014008142456041c030010044401004000d000e04d0721000310606200e1318151400d041c003c2210030140c02908400b011010810002e50322940480d0410380010f015036442c00c0040040c0d1030304002041c8103070580520300c03000d071b07044038107501500c0110825100c1894011f1030412002e904005240e00c80b004c60001190b103c040780c8948401c81046102e4042c0e6400038000301c8180b90900c90440e2091003890b88120000c51410505580f903030000d1100e401040c15060502000d00300c04441e440540401805201c050708285c0b091400c50300468210490950340e003000041c0c003000b0341c000b01019025441d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 574947643 1250 574946393 574946413
    0x60d0605190503010513030e150c0f0604150207020d0215090a1502100504022809090501020d0e03070f080c100f02130e0108100b0f030d030c12020f0904050603010905061503 76
    0x410441b00125560540e03424a84003410010000c4200380c1c00381103112241c0600424803607070b808000c54149045a80001c00c80c1c0d00e000e1804100a140580d50002442d0040c40840c0050b11404490a086681213039002c1c42035481c50003204203400703103040781b9900c07204004001540b402c00c03c0c0e6111202c4842da0907a0b4034001b03c0c216850130f80d0006c0d900250403c0003441d051000004411200d100008a2141c06d40c2e00380d030307924100066520550041d20a81d60000e000c0c2d19580c4140300301c41200d054000030b541094201d48440c0c0e6200345101000e0030300320001070241c203104010701907501e070348200083c02c00c101d42031020801f0080d000200c0c02e46841041c1280442c1241c0d2504805040369291801001c3c62a526030180b009412902401038020202800079000c0303030303410702c20f03040c2d46aa10382d000640000007120061900301c401c1018943c1510400040d0b0ba612050001c0310003a200690f0041413584650010900415008001504034002d0070280080c11002500c201c0c10303580110110350343380c21 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 574948893 1250 574947643 574947661
    0x91003050a150e0606030601091a04060816020a0615080304061d0402030c03181f0f0f060501171512060a060603020310031e0605010801240302010806060d06051905030105 75
    0x20583c01652400c580000005003507250110066034041010301d0b180044995179103854508202400101064660118003808199442440c4650001e48088a016000c0044802a4882c8410309015046a48441c03c22407a011002c4e0003000403c80041113031341d91562124010045d10415216206841d0104001001e80c9028029a801481c14a46032032071038903003442d440300803400c00158080301e002d0f401141a00070141030000100c002460340c041003171004000600200c03420031003404822445c1030700902c40c590380440c1407041d1030001c04034042503840b02d440c07601d02034243c2c540481d4880102d02d1301c2102d44002042c01402080d003c00b06102c0e0300d88034007058040c0d000c100c9481c0e0050b00000e00c01c102044108a4440560580e4152048582e246071a00429684243c1100141c0d079124486003801c544400c200010502c005200580b020342141d0009021500c0900030510491001c62203440d52201a4030440062000400c0020849400e0100c2070f4007018034403940788254600400561802 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 574950143 1250 574948893 574948931
    0xf030a0f120e121b0105040b19050c0406210905010204030b100302150a03290f1504032d0b0106080a090c1a070204090605090d050705061b091003050a 66
    0x402e81c50054003440070649a8020340d40c0100c07015003000c03503d050040c0c040d840c0a11515000314001c00d80e000c89490100024000510300c0340800441d54508420007a500841209a0b021741d00186440e8010461940c101041e40c00a207802a9075646400380110402005600800440c0d01c03c40160030359540310440310a040c501d5100103500000d02c000c21401c080900001401c1c00f4070311f0700300003546a0528440c1403128544108400740c402012508a843c0d241c4000313840300c441c9045601c0b030844078040141c00128001c07440b0040503003440509140181c640014a200c0b00c40c40b40b04036840c2146242041007100c0f00c04c0c4599804180420301003464184035018003030b0915003250030002e4081c50030400011a8070200c04420000030140020310050b80d40740140380d080d40c011580803405007000b800e40350510343c99040c50760600104029a034001800031688950000d140c2030038210041e04103402030182c0c0328040b58603501c1039409070410780c8150076600203809409098002c002c0010b540064903094 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 574951393 1250 574950143 574950161
    0x60e06091515060a0c080a0e0f04020403051e0708060a020d1103010605090d0c05280602030c0a031d280603060b0403110d0b0c0d0e010522050f030a0f12 67
    0x22405044580d402c40c00c24000a140340002c81c83c00c1644401c0c2d0703480760000c0b0782001000c00b00143c041c000c2c0c50344a1401c0c012101040000b00e030110300d07162035030340c07540d55613900c943c41d080d0b054030508107025140f2000d021840c0208441c1d0203480e520f28104165100a40c8001103070b50300f0f28940620034a1100510301901c1c1658250b40313a103031401d00884200485201403a408030f0702400384010200361034545451a13040b1094442449299a6002c5510440844203810280071507205201c1c209000b140056407080403509801d010085030140081c1c24411290203101c96048403044200030740c55030300c0c18113007050b100c00f800012004030b49800086065038036a204d98070844900344070500100303210301028101e0713042c014607050601c95903541b6034001c007038100d500000c584004107503050001c040c0d015440f014003031203000700654681091145440003020011640d000083d6076040104102000741011170b546080c2129100c071003120004084080000d00d4400185280740000302241e03d6000d02c0c541 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 574952643 1250 574951393 574951411
    0xc070510060b121504151a0901090e07050d0c0503180a120f030207020a030507050307240c050309030105100501090603050c030708100e070e0406290313060e060915 72
    0x1c3d0070748080368911071a40140801e030304100c0190000c4180c2d0340d40c3c41040c40c3c80d00012030100949160105800c10301072031441041440004101d0032145e41c0c3e00810a500b40c1d003050b80382c480e590b102e070f0700203c6260080d0540d00e09034030f10f0401d0714040640c10001031032080c402560f402983c103c1500183ea2140300702c0800038100e65140050070380b800c0c0101d0b4034110020780d030301d001401d1502680008440000a42c0140c6041e00140004c0c446800d0030b010031800307803c907880003141d0400c1c2a10f2078010440c2c1103c0100070046642441c804000d4144102c5154510090080c4401d08001140b0000c83c6072134402c0701d010030340000c1c0004445009004461007510302000c3d003030035540c034030006588454000342011034a0428a5000c034182c0c14020010340500303400e40c1d03580b1816004c00284011a8900d800400350000001481045c02605400f50f1441114604119840352100c0607140f040c5040c004008040505002003c03681c098000364051054517880304440c141d220100b2040c00011007903c0740c600d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 574953893 1250 574952643 574952647
    0x71b080c0d0303020a1b1b120302030a0309062307030612111011100605010216030f020f12070801050912090a1205032a010e16090506060706050c070510060b 69
    0x202103406903000c0d04101e4524140814106e0140e00004208418540101d41102402d490300400d0a06259010068400560348d40d100020300d171400780d60b078040e4920b00003c054803000c08008000080d00443e2071903001d0101c0c2c01e06940b100401802a00c82103030400002844c0010000345601c0d01c41c10044150f4203c044031b5119408a4140a0600f202c03444d90703030600000c941d0321034020900b0408a120000d0b602c10019030f00e03003880002420050f9030680f2503524003100a052021581030300754290400e078100c1d0203528124611001c07540d4140c5500003450540105140020b03510419001588561101c00654044c4004820050094011444800c0c1c00091243c0700f4440d5505c0c01b4503070703c40c090007001282c1c1804207421840006020000860a0740d07034245440c42c2c0c0401090147e816000202006406102c1040b802c5611109961240a0aa0b41c444010401c1900d800b01199503040c0c008006020fa4034043e014109580d1180100f10b070144100e11482e4900da00c1482401d042d0b98007a81c0d0300b4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 574955143 1250 574953893 574953919
    0x308060618060d14040c03050706020a0314031305010204060f140f1c090204020d0c0e01030e060a3201290304020906040b10020c0a06090f0306090c0308071b080c 71
    0x2035070480300381030f40015901e4074490602d52414440c01c0c070445c4540c580c0302040b0300f036241c164100021a03000000b0b65218000b00000a50003880d10640c282165542c0c039220790341c1d200b440006000300d110203070130340d4400100032400b6a84204103070400c05030754a03450032055183c070803a0020701c107981180f094801c05020314641944844800e2228240f01400455459480c1d000542241d011001c20700400b80e480c11035400007034000c00c5e050980e00c1c007424204010341d03840800316150800140807900d00c0343d42c0c007001d05080e000c083c0d09030400c294481d0303404c940301022124611442d80038000e5001005808070078010300c03203080c0f150703200c51003c00c0030541c03d58071290f09026480c6005001d59030700176200c405081d030341d454110800410b040135078010201030303140300188a058242138000c0c5081140350102030183d03000840740d10045940c40000000c140a50381403204840c1e000750070080071500001048800e002400d070700b20f01c0180e00b100c01c13140941d50300c01e00d455544406550407904042c0c80042c072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 574956393 1250 574955143 574955149
    0x1f11010b030a0c14011808030301051201020a020a06050c040f03080c0f0f0304030b10091b120b031b041e09060b040c020a11060c0a030203030a0c03050423070b0706090308060618 78
    0xc01d1184046c1004c915048070005080d4200c0ca564100c0c440310782c0048010001440c0c61503040c0c0e00051010001c6241250710b41c4003d44400f12a14041c20054442002c102c41a560908450003032084d248c81d4001c0c10345a203046c0318164403071200c010071446407141c030315144000401c4000c3d42c50782c3c9100445c50245541e0301c0700b108105c001d003065020350140700000340c900300a00400c100002541003c07202d803801c16102800c800fa01c0010340020318503004c03406000d6100050b07030300503250819002d050200020000036020305184081032243c1c02055000c8074400c030260700030b25140d9100380024000001c0d54014002143ca89040c0d140040c0d10802c0c82801141e0343c90002c88ca103c1c40544802d14210421144a01c2c00100c154100d0040e8000030412003034030814032030318000c200c00340340034000b80c1407503182c0c051801d03036104004101da0307507003416006006000c020a00090803008403407602c0b03001d541029001003134220804d0f8041020040060310f24500708040703422807221444092510f00030030080c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 574957643 1250 574956393 574956419
    0x3011412060123060a0c0c09020c07030b0a1104080706170408090d0507051c03080606070206040515160803040b1e011412070311031b060a08061f11010b030a0c 70
    0x15462260700f03d00820035140c07034080051030140c01d1910b50032030007501494503509000381d0741d022000d41031042c80b0785026508041580011a60007807201c1c8607580300c0301c04040003070400104aa00100b0002030009104001080030800c0701c03c65282c801003c030550300d0302c24000008039001441200b0402c003140c0c00e49010080004900e0180d401c5032510354aa001107100c02101000c4d01051800201c0044201a8824411a44440c0c10748005080007801d9002ca81c0901840c020349205981d0b00d2500f9141039200c1d001d40d002131040e462007103840c0310b0794107010703045038026142a2380a502210025429503a4121804a61105400801d01c241e10b0900701842c0310b11607101d0300341e00040f80d85603400c0140c02085150042d601442248100490540070503241c0072100781c042e0140c8940403c0038000d980c0e402e041d1007a2070a2800c2c002c419a03200c00005400200e40c02c204056400456040071455901164580705108684c0080200740200400c140c3e441c404a50010030b8806003500a00064981d804 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 574958893 1250 574957643 574957679
    0x60f070c0311100506240f07030c0506161707080610030204031b090b0306010b070f06060305100c09050f030709020703091a0a02100504031b030e1203030114120601 72
    0x904502c0d0302540445541c14282c91a400410715034031201444821714102c45007150305c00303041c00202d4000c51400e0303425a02d402861101c40b41e184010602c54181401001810500d55020050360910b00d40b20000a02504443c04054001210031580c00c1011180100c071500036405a2204911070340d42c90f0402c091004840184800c051702130000100003804c908104540c01c0301040740c01d9895080030001e074100c41c00b003c141d901c01d0748100c00401580300179504444505402804104855680341000806004c0d0303903000034041d2183c038200305d003018141d41c0f0451401c0099030710b1400380ca540c0c9081000c0072408901d220b0381500503000400c0103460b0340d4014140e07a80b113820200d914aa580042c0b01241020034401201c4040025146e610603506000301c1210800e8400e00f000030b0300780313910020310030001c900358a240e18030070f5640e09081c1409001840d80e00e441c010040172201100d450a203407240c0081c45200b684044a4014000c546415090181040c034503900511b5503a1a150b000705444655007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 574960143 1250 574958893 574958897
    0x2040311130b0604030606030b06030a08030109020a0203041d04140c010f0507051e030706230402010516081b1615050310051c050d080403051801020339060f070c03 72
    0x800b41c0e1090303c40b00007410045020f08000030f01b05286040c43c4100c1000284580e10a800c1808100f00103800e481c03d9a056500d14200140c64140c2d200090b851841260807001d2451480b04900744034040c1284928452885105a0200c004d131a208560303441d4080026640410f15142c048946680309802801440d40188101c3c0c400012001c80410200341c0d9016180403504001031003000c1c0800ca0151100662007103503000c00c1d0311440b12880d000d10b4005400203040040020b0000c44d4074281c03120402c05103400285181c0d072200b003a010000044509513042c0c0041c020884800c02c04124440e241c0200c40b04171f81142c2c4c94521586088a40790700c0100701516032645000080b0b480d80303c20b0440e4900200c0518154221181d90801a203000890511402000516801c000c0040d521400355440b00d545040540101486007005034118001c40315132a01a508540c48a0158500510603d0740c40d0108500e0454503610303050102c0e2951401c896007031140c0c0510011034400c0e0f20461908406500174 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 574961393 1250 574960143 574960151
    0x1020a032109080703090503240103140102131e06020c13020c03162d1203110f210105010c03090e1e07020109060e1f111b010203070e040204031113 65
    0xd41c1c2c1c510742134110700c505400007684900140700340d040c2080742100e62801008101413004440f107064100c1801400700410b0907482c40c2d41c0d0b0041440075010b0701c0082450b501d000901c0d6445414221a000c0e20b0443d203611580e07101d000003891400030445d41c20000014240c1041500722406030400380d40841c90400c00b41c402000b410b40364075010041c01d41a64490600741c41001e002c1d9640c08810303240c0c072224107400e00305c1c0c1c1001c01c0000e0a0007080c070714001d410300300840d0f6000090207001c2a030103010b80840d018080094080d6250007100b041010500d442c4020b02c2d903d0742c03070f40011214070000100c011301096070010288980030020110310b9010000410064010403008504d0350541c0c81a0340c040d0241c0c3d1955064403c00c00b0f1806110082041000103044100c20100301c504800c00444101c0714140d0b0b6040c1034031540c045201242c0d1100350000105194024000d5840c2c000c3d80121407510001d4240300b9403100070324060085404036a00084800c2c04030007018100000c000810f10b49a00340340c2d079 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 574962643 1250 574961393 574961411
    0x21606140f18030a0b07031112150a0801090f02090a0e0316021909051605031b18060f0a0807020601060512070c0213020702010e0405040203030304030c05070e2401020a0321 76
    0x10000952910b00c118170300002401d10341d401500f0703290b160400d103d01c26020300000e201d0743c582030451790340000140c1e581100e072076905001c21414001c0d0b80105c03d140d4200209502480345480590148a200f5510710702540e0b60000c1110031141a4450b80d001c98000308005410303480b585c100001001e0004240a10a049140359030341d0210719540801065a210707c200848441c0541c0c11854103081810064507501e00312014942d140a0440c40c0445100040b8007030011034180c0801a0210300081c00c02da41e2000901c00e17442040e00001300240c0080c1e920400160164400700e0390314104d8455441720b0341002541101c40403040c50042c5082d082100c0d16291002590364542c0e40401030042120041c0d071502c00d800018200f403c1021810300850500040c040161800030460b0390154052905140d83c01c82482d00c075040c051640d125904454041c01841852208071000100110349600700c000c0031480100107985510005c800907020a0f02d03084200c1e00c0c4820003d0b0380d00800c814141c00501242 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 574963893 1250 574962643 574962649
    0x3041e080c010f26010503210306060c0a0204060e060a0906030305070b07050d050106110c150d050c120405011a180703020c0a0503070614011e0302010f0c050d021606140f18 76
    0x2044c10031a810450384080104201d041c14000c500403c0180740b003e030081000107070000b800303103c041c0c0040c0c010000040e4461078000d0620816146590041080c02081d0350f905400c00540c00c2030703900b40d204e00441100027030100e90354410b0074120f03035041d112107080c5805031700c4109003000c00511040502c6410840c000d12046240300c3c15020740401d4807580495a03041c10a03e11300380d0103109142c0a00e007070500306550440503805407060008400008620341d0348100c4000c03418003d444c5101e17601c043c42c1c414402080010740010801600e0640302d01c00ca41544010081042c10032079482001c50309480200c1ca0080c403035001403000507628011143c0d4128107680b1249590300c61407042c0c03003c55541503e01c058140c5c0101190050400c0da140c02c0134075641c0d42c1c0101e84624184002414040d084018911040c000d03142d4040041c0c0100a54003002c110080203510b544054140f1001650000404140980541070364003003006d030350203403504118402d001c009180c0c2c0540032012541c83d008040b404155 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 574965143 1250 574963893 574963937
    0xc030f0e060117010c0818030403120e030c042a0e06040f0810050105030d0e04060f08010b0307060810050d020d0b0c0d05090a1e0303060b0c03041e080c010f 69
    0x103001401401198904140d803050f0983c0c102c4520710700c1e41401c10750403409078803200d001d4018020240d0014807641c26031040f869441681d00041110080c401008000f5400c5080c1c80ca41c1355094050300c0c1c451502c10100401c49082845009103048250110b400d10501c8802003490f841c1d207400c20595410500d00041c5058100b40c2c890381002480c201c00f400400c00500c50018202c00d020014401035060074006620703505445502002c00c4a0170f003c103146682d4680211004190341c0c1d036090316007611060798074060714094501b14000d1041c02d9001990521421a240c400c0c0401c588200440d4140f108000e0060400501aa400f56047d05210b000c52a1000450b028851000c41aa82c40400b15100720a948004107500340c25000f207025040400d4503c1400311103009620000c042d0f0142902d0300b50000c00a50b001600300b040c020a003031a01980000c014001d40e02d80203104000820f10702c0c900c5850207520b014031030b41034200088806c1554095902807003103c0c04c43c100070500d10820005031b0700d15 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 574966393 1250 574965143 574965161
    0x22060807180b120a0f0501022a06070f08060d020d02061801090b0a020319120c03020307030b091611330606030f070813020301020c03030103330c030f 66
    0x740c0c21210024040032092140300b0301c000e0161684000c40c0c5903801400c2d15040d10079005000589914890400c02c2000c1d811141c0c00101112140c0701c400141c07417801d40f003041d08500050742c0d10030325012802d040d0282c110008001c48076a2009990303074807132050022203008040100e03002000e00e107078400123a80d4540904508941d2014500310b0740d4080740010005d040e0b6511032201c80404004001d0740c81c1e404070407540784900c500c820303808601915408031060b940d0042e500075258500448800119410f400440c0141400d55090001d182d018003007002e5880103036061100c1080e502c103400c01300d0b40101c1250752104c8222082c1c0b240520920b03008075041c3d52200c6501ca180c4091a560403603400c0240500e03401030310542c0d80a055140a00540048540190415051042100004643e11070452100a8582e800780c000d54517203001540c22a40c0384c0003800211246001440208e0303c22044c11980c1284107000e07c1c2511a9080243c1303407400610f0058200d03010107803035016041c9000c034203028a00c20 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 574967643 1250 574966393 574966409
    0x933040b150c0105060603160f0c080304151a010507150204120b0106030c051801030504080904060f08060c0a21020f030c03091e0706052a0a1a040222060807 69
    0x10b200c184200e0301c2e08584c00201074a1061a00f4070900403c0c51414002205c2d0040e5403e10360008400e04006481c0d0841d1002c00421211000007000100701050071000142030b604442804008a00100c8144041c0c08a0401d40060801d02a10010440c0000c0c050700c0303100c0c6c0200042ca802e480d904c040c14141060030f001d4030049040001000803603498401e02e0100843d131f160180c2010720b0000c194114000d6605018109616800820300303011401c03045460051004204006440c4d0381c0041442880b99031044910030b0040c640024850144902245c01c2701185a43d100107000364012862019000c807074907040c0003903081c0001c210401c1d4500c000c5000b4030801d503491303481e443c2400d0b81070300e0200a20800d0195110b00c1d207180200c80310000721101603400d10b0800d15240c2c0d101810003a200d071020305010710402e94841c00580b00780f50100f400c2c403840d8001c0d080641e80c1948a046e0040b85501510000d4201040300100d070391102c001c2106401e2078400f80030105400d035541707210502c0d01c0740603041405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 574968893 1250 574967643 574967647
    0x101514040f1e0801020405130b0f1f170702060103150207080f0c063103120906061a030915070314010f0906050909030f0c07080d09050933040b15 64
    0x1110354500b840008002280081d0320b002d0504010503004882c941d1440388064480a40020680c0c512000c0c2e6540003001d000030b8060740701041c030558002c50340c40348507010542c450220520f111041648070f204400c1c5400624060346144c0d1201214400c101c406881150b00388a04c800103494140200b06402911440035140d01002207032a007461400b0b440b8030183c444000c4c1c030390600b240a41303506c14503003a0080c95008882f99820261045840ca00001000c5844c0134102001c10103268444010703070b58450901c1101a03448600c2151a1000b62101e442c50340c17202a4107903180410300e04281d07201d13030903180200d000c4026a0701149115020303040350103090206c18003800400141d10416000706011144481d9900700030062940324800e000095890300d00008481c0da51050410844004200810840741070f0307181707050024240341281c0281d0b8441c00c0c1c45404070300301482c0c000c0900165841e101501c1d0000480b845081031246000400c80c1e00a602d40203022891740d218500c0d2003800c405080342039 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 574970143 1250 574968893 574968929
    0x9120f030301260703020f0d0b0f100b03040b0103060504020a0504020711041b0516060b0603040302060a05060d05190320010501051302030c1c090b0915101514040f 72
    0x1203140701d0710058003002c00c20103c010750015000003500d001240d8041e5044400440b180d0003051084d0800b00010b070136210764109125481c2c0405100d50700c10000000b08544241e1a200903070b0442c40180d81c0074100ada0004014804200203900c01500688004c01e282c210559400120f426a0080901a03035411003051652109007000d018460031a928a0080604a030f08a08050141e014000c0021591040014041e04000b00c991042c102c0a000414103500d910346072500954601086608000b02400c00c0007113440c0e8189103650020b030541c020050942d042c920180b494079640240029010010b520395a600d8004080b104461418001030002c107403507041000f80b00c144003051400041d000c2c4100108070303884803e1416149000c00718072513400495122424070f4082c050480c005451803c01e034003030061400c030001740c00035802c03400442e07001036a0b00c4440c0d810030313a81c2d50321032001d9000269034200d800030321984100100510f84000b540c01c15495250403807101c905904460040130019000d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 574971393 1250 574970143 574970159
    0x61203051b070b040e06040b0612041a1b0901020c190807080303010f0b0715060603060611160b0c0f0a03091d060312091c030909061703070809120f030301 68
    0x1c24140d4801001018020300c2c003000808144a070780304441a1103403140119040b950740b5084483c40c290b000309065111280082d5020142d10280e03000c440c1304196041035020740c40440a400d20881e0003803040b00c407141e000d58078030010350722181d1303121b046004400b6000c110b55102401d00024150041d0100c10650400b8200c42c90078403030b0b80107100d490703206000401000a42d0144641950782c400c030300700d4942940d842c240340540050302c12800202e0802034003003044c9600d54441412920541e07a4400c4100490000ea41c540c10b40030040c1d481c0000800d41804031a80e501c0060a4032140e00c0d0486003105d10750084681000158041100090000c0c44104201c1124071203555401d07240490380d05241c1000c40c0029968802080e03070b200c12000c0031032450800c0d0b0740c2554061070001d51042d014440c0d0050700d00104000400e008101d86940340c0300c1d001c9407080f42c440c85034080071200b80007180760855645a1804130741050340c58592007010443c001c9440e15081c03050140c5a05040000c54482d4184044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 574972643 1250 574971393 574971427
    0x503031005030f030d090516140a0902070c051011070e011d07080f10181b030605150c03040f06030221090a0303050a0b0d0f060b030a0803150406120305 67
    0x1c1c41c800e51140707124410b0b5500c0803044031003aa00781400007503080d0161500d1342c1090281c5494404580e081ea03000100c0c0520103042e22284213048803800c0328292203803104000c0f4042c0e0540580b000000c00c80c10302090408201c00c0c0311442a81c100400141b50030401d0310720b0308001d03400113502440854010000480c1d005c6280c2800d0321114a0a100f61078544401000c10600910603c800042c210116188000c1030481802609015600400410b454060100505142d1419080340400b460b603849406101344501801e43d00000e1901d4110441511425019040001915074a000400c800186015820451002006203440160b1600810b0560900e80050a203548040d411072008000f480940442c08241440d41810001002d40741c2400d9040140f851003649034001842e041148140511f0b404003840b4a80b080c03805014004c0d0396018142c40e9556284000c10310700701480454040301c9107444048050a010384005902c0e0368030030303d2041400700c02605402145000403d5a00780e00c2682c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 574973893 1250 574972643 574972649
    0xd08071101090b0304031b0b01150e10020c130204050939190c0209073c0c0f05061e060111060c210c0c0d0801050a0902031504060305030310 62
    0x2040c41c240b5242036508a802d1100400040822901d00f030030740d4040e041003244022140d00815050300340d68481480c1284010210312030300c04945c4420301d0201e03501e440f502c040104101540a801ea00200c142030010030400108041c114580034840400c00d030302e030007000701d01c1401c00b942da03500c6000e04218160b00081424154650040788401051003210680b022541d03143c1080828244c1d04a4100f02215440c4011000030351154002060045050b44180b0010840042c203941c0041c10011450549454802c1020000711208450010706038501440c100c5032224010803012808825030b039a414108602240c002c140e0320b481e000380310006e10444050561212003130030169008001c0b019116540c00006100d103c0e0f1a80028417000310380707540303030841483c0750751401c82d42c071070f0b00b031280742b160454100c032510701020301c9000d12a071460340c410300d101d5040324009400c18914908004003580039500042c400441205803c0300315601c0e0702e59109001c01103008001544d141d0505411142001074564 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 574975143 1250 574973893 574973897
    0x5060712091101120905070315150503300a050a0e06030709030b06031203130302011524030612030f020d050f040e04051903030b012d110c0d08071101 66
    0x801440c00080d0010502d030300b00314090810388000400540e001c0064440c2000080c131500880b030001040101400c0c24001d10743c2001e900307002103c510509018252854800c0fa941688151412500c22034101e0443d40303501101d800c1d102c190212000741d0150742d400440e8081c00560001101034032242c1c040f4840c03280740303822500b1601e1400c00c1e83c1c00070700e064810301002e08101442c2011481d03c0d5420050f443c55174180c1c26520781c03a4030b4110640f00035100b0380b02c0180c02550811025240707556104480a00383c07080c2541e01c00354908012000510081581c0c0c1c4034050582d030701ea020640300c090084480c42580f01c0e0350351122025110354000e04100e8031820000c103020307041c0543d406200815003540c0a607080c6000b07090b82030f542c9051151500b0718404580c1400d00c1001c885000f4540c0c076400c203074482c0c0401e0321445c0c20600100c0340c003000d0a1849034001e0301c80c00c221600340500b41c402e4894081c0d007107581044640111b480c1000807400904844103c1d00514000350f030b0010000040380c40302500d6424 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 574976393 1250 574975143 574975151
    0x9030a110a1212080a020c070303180512120f25020103060605091e0607061e050108060f040f02010c0b0c04030303060b040305070501080405070306090c090b0f210c0d05060712 77
    0x160b0b03c1440345183d103c0184103001c054400101c011070702e5030583e410030303040b0011502c55603543c0c24050408040580c4c000c800d809044004180c5e402c14107111100090f4002c0105038010002802c0d002c1e0b40c0240c50b41c031201107403c10103c0b000301103000c122000c85040110f402c07200c045d240f001408484242e400001400020304c07a80c40e0701c1d52004100e42100d04002d07000c000c04650030340014a948100e250003132406240c21210501101007421046d1454059001013100380d880c0c801180c0c1d5094200c1c1c030941d8000103000000d0000303022041c405401c520604118418000740d0b030321030050f080c040390410582030f00400c08000385603041c06036034000c110502c4000e01d00703401e40d1103040e190241030283c141403103142e00100c1c04022080101900031138010008000c4200a40b81102c044403540c4202c503d81810301010b12640e16200b82c4441c100a0000d219100403140101c8081c010702c50444240050b00030034640703900c03607103503070700719068951144c005000302e4603001101034040391020304004002454 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 574977643 1250 574976393 574976429
    0x15030c12062304060e0708042303030403031e090501020c0706030e03030619090f090b011d01360e0d0503040b041104060302100206160e030a0209060609030a110a 71
    0x20000110b00000c0307404449401c42c0c1e42090106003c0c0403e5030020410480f0041000b81507903000340d0040c0201d20481401080e40c014442c06400c1c0000240286515001040440c0001e802a80510b040620041820700c0c1c00e0103a250507402c0f202c1c1a041900e650350001514801c10f60140444000b4003907504041010b043da1814013075aa00009100074080e417050701c003070308080c2c8403010404020700003c1c0040c04020384440d0a003000d004410700c1206d9a0035001d0010a1041d03814a1341601003000c03594403c00c9a290044408080403030200e080c0e0b030100e1304208015040d45400041181c000303088808111209042400ca1602030035030340d09030811400380203010004210b52200b41d00a6080641000c8100d86140010000d25903948001c0d417098191041c042c3e0347d030b000700782e0301e108072410300c3c81000e06000c28500755407100c040000c0c56815085114040014504070b07600d180c0103007014050f1800c00b42c00d02e01103440d01d043c0c94029100e0303131500c3d100442c0300c0c0740c101510405041a0101b80c1c0044403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 574978893 1250 574977643 574977659
    0x90c051203040308030a0207020307060c12050909161101090609020306012103230c1516091a070f08040f150c120e060a0302040602010b060f03160915030c1206 70
    0x29500004213254000008215040101c0e0151a41242c0003810780c2d82d81669031001402d02c10114104480700414491881801802030b810340752803e002408203246582c0710381d000741072100c101c0e00b0442441040c0d041002141c0e024401c00310304038451940040c0d024681e0041618111059110300c103501403101a01e00c009030b11030401e0103243d61600340100c1d08218003102100c9010120700b10b0f00224004507901203e1100011082520358002c2c2d0790a01c2e9884041030310200300398520010000c2024042e081054105c401502c07c0c01c416001c0d07202d401c2c5003031a61254a103001c9440b065590b01c00104003400001c5d40c407449000144200001a8074000c007451018140b0386035518058a0004141402b242090041c4416090080c004141c950345030110100640203400a0142030010741c6441004007090520342c0488002629580d121800c0d50b0394841c036000c0d244460000c4100f0441c40700c8002840e82c1a101140c812041580c4011449007003074013000704017040ca00307000404030b030401100b009024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 574980143 1250 574978893 574978897
    0x503030a020a18081504060b03150601030e120f0c1005010b0901110109020906040908070b040b0a060b03241f050403200d06051e1510050c07090c0e04020d090c051203 73
    0x3820b01701028030580d941c1c2462001062101c0d00c141e01030003640c1c0d80f00708512180341d580b03101324000d0b02c003000380f400032005060740c41d003004901d41416401005641e40b01d00d000c0001c5c09992002070115005404100180ba06442086e03000c1d10b0f11700d40c04035102209682000102d131214003101d000b0002241e6940000e40324010140500d03004980c3c0350001c0d0240f000243c12a46030b50740180e007140c0d03a03041c0b628013200c1c41801140c00f031152524052010410120700e10403240601503100c103443d0b186045442481d002101034003801c0c0e12246000419880081400030213030308909940f2426140c13481e42c100361145042240da40c0e8040100a07100c02d895a035602d00004d801d03500b0084c00100c665071250340034100184019142100320540042080004e0100344031100560140c030170995501403128203441a001e1124680c0c1a500080b4061040300486c5c1e005800140da585410101c5c081001e0111782280c1c4a554a001c1807511524007100b488100c01e03031440144001e4030035082c01855200703001d40728 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 574981393 1250 574980143 574980163
    0x30f060402131d040b0a140613140a050703050a0908121009090f12020c0618060706090605160915230c030a1103090109050f0d0503030a020a1808 64
    0x1855001c00c090141c501507041100240080f20201a071001080060700a800f100301c604135440c1000200040280610b4024140040e525104a41454070707a0b004102c003244a650024031890303564448840e0101420000c6802400024400a128105000c0c02425213000509000c4e01d90304159545001079050012503c240c2c5607060203a5890300d841c1e00040050400764070040c011810051018184001e0300c4240041c688260a060b071a00303c2000305030b8036001f2002185030702c02018000751609002003151803840c000c0040c840c52400f00c1980e2068100c407050041541c6007070381c03181080400b02940304c2142e84910725080404100d40f070002d9001400c00b4210b001001c202c0e8402201072415a480c0b03150460040394a10951a2400308184990b00c3d00b040d02a40700056034040340349160f20000c0111414090107a465040c003038102000c0c845003240d400c2107940c01920303004e140310210380240042c2d4050440e0917400340c0e0b0740c91640001401407440111182424030700f040304200c02100040c0190780 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 574982643 1250 574981393 574981399
    0x1c030b01210914010507091d010617090a0b040c1401020f071511032d03040c03020103090516030311070e091507050706020c010203040228090e070f180e03030f06 71
    0x180010034074180d90200703c40c2c0c080700419801c0070280945150001c64540681d800d80740f01c091110010480342c1402032081c41040c000c1102d4034403d101d15400440d019500000c03040444219000580d00c55032100c00803a02900c2c400052082404910300684944809071800d100809440740308441d0b0341d03245d00151048444000801c0480d50a150264100800030500b410a40b502d8480521302801d42c4c803518000c00d5604940040c444100281900549000e6500120066105400d503401900106001070040c0c55034443c0306034040d4a944490314140144d88203580c0c012000c4402da02e000c1c034010305074101003101500001007100124000a62000c1d4a09608a10000e83c583c000b0a90b4a80714000700030b40400d00020b02035540c140e0540045002d00d01c02c1c0c3d0100a00c141d05003124000446840f1540b40c82810001d0400140025800c00b100f02c0689000b0b480035580e88420105444406030302c4124051200f91401040d01e00c203100f40c0c0902000400518510318044941c92035100300280081e02c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 574983893 1250 574982643 574982651
    0xe18060f060307032d0c020615040911060c0a03020c1005160c0e010605030907050406060215100803040f05090a020301060c08070602131e05101704050f1c030b0121 72
    0x5040b4425040f00d0702c021075115640400d015001c0454450008070250341e890142083c425030555440090234a21441035440302074802c1e0f50190410015141661090b00d1406031120711003003030341d00c02d0020070043d040c1c0c800401b4142041c0c80c01038113168501c40100e204961030070f802d035a400e070000102d0318000803800520108003201c0c5801003900c0110b810011030007004000101c0c41d0390300040214010030341e0808540205070350300100401d490341c50050500503002100360900483d04082c00d5134200b10f071440005003681c0c40b540c10030700c0d40c0c1140e4040c040704002d680701000281042040383da00440040810340c034560401d9005410b124a1079001007a210780000c140c0180a001da05072850ba40c201c0e00d01c2865103a45041e80122002e0140c0b9210341072015182c005024a007019142010140710f848a543c0a070fa600101780c03202400410a5a01c0c1c0540071120340c3c030042c203004001703050642803000d170240c0010340401070444414010250510146106161003841200101c6042c908008000f107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 574985143 1250 574983893 574983901
    0x50d08030a0f0905031305101409030f120702270c0d0213120201020d020a030e1c0b0103051e010c08040b04050c04060311180112020625030e18060f0603 67
    0x101c01400e034000c240321000d160a2145007000b0021000b091580481c5c100190040c1e100e07020800c0f94120060b005001c2442400500c03041c040302409030600b03800090648a02407500304245007003c0490b81001d44003840003136801c0031071600c86e03000a030301c0681d8000b010031188400c84003145610094803960074554040f4510b013104090390129000240b62000404005030303140324841000501100480c0580200741a8a1508c0c0c40002c441074a2034140e6100c0300e61108440620144002c140e04038078007962442d03200b8021030803011000c0e000354455030050120402180c01075011600060740f82e0240d034100007544034482d6000d99559003142e001083d00b80d140d01c0c0c920300a40391547c54035401750441d040c0000002402695088029085019074000c002c107014211031004102c42400754411a14182c48014050305000c40540b0b003070040e9012a0810401171000d1200c4a80c0006044002800080d02c0030101d052680c940090180d8404003000c5900b0240b00041446050845040c02818084005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 574986393 1250 574985143 574985161
    0x309050a0f0f03030e0c0f0f010e0d0c0906050307080d0e0a03200108060315180f06010e01050a050402030402030a110307051512090a020a0b030a0f0216020a090501050d0803 76
    0x20209030700021030030741c646452511858600d81c0200542c0403034a09103800009100100b800c0075040c07001042c07036407200b09000410154030810390501d8108605d0300000c05858490300c00c1d02c1e003003034040c20507941010300d4000008250385003504854066080041c0402402d0b80014018888440604061100d01d26880200b00088210b60000c0d050b41c409400c0c01c81112040d01c0c41115044c0d0030385c0d403203920f5500d250505a40d40044001800d05d0b50004002440c5001104070f851b070008451401e0700c00206000361000d25010b4286c0050710000c507980c0042106280460b2000018070040e20150704500c0c2c9500080e466032002c91001e000c20444540006c8580c4d02401920701400c0001c04a05c656010715807607031601e0304400485480700000d50b0200fa212080000e10400b000e80c020542102503040c290840707610f0300301900c28003080da214000182050356074001f40242090b00f5043c040004100e00411600769059400400043d103030000501007500c0f2a0054050241c000128239560b440307401003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 574987643 1250 574986393 574986403
    0xb070303020a030228080f0c0a051608041d06150f0a0909020c100e01050103080f0c0709060b0d05360304120803010f06020105161209020909010606021009020d03030905 74
    0x611101303851070409007000d116500e080c0c1c1d0b903401095601c03140c59540328200240d564505a8074071640350b6051256030303140c51182c002485001202f01050341c95146aa84180301c5800030b4000c1c089000504011041e445400414948c0c01702d81120200107500d162140d002d01403007034002149200b0f1300042e942141b68001c5250703400400307001004540d60459070741c1d029142d001038007102440e00e0500204c054a83d2050181c2c0781aa0303040300c1101d240c040925200348060b4080344000c13070700e8028400d000400c16250310602004001900740c44c0e40d200c500d0350010040740d400a268202c8070040301c00301c0e0350180520740c140c4602e1146a41c20307601c40c0d42a1240728554001d0303901002d864142d5030074050803c808940070310f0407150344400d44020b194588009a00760b6504840d1030341e8240c242d8040880706403060210f0301e08041182400075286205402003403040340200c1c2c116a180e9143d44081003850b5040003c0100d54121490421510001780d001801c1c6219109000c0c0400d42c981c00300d00240101402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 574988893 1250 574987643 574987657
    0x3070201080903121819140f01090b010e040f06020c0d11030316180e0a0605120d121a040e1b030a0503040306020a090b0d09020a140607021009090f0b040b01090b070303020a0302 78
    0x6a02d0030242140b03040b0200c1a1f60000000d220f010311a088049400d05000e1051070710351143d00740e03160341e0800b24048503c1d10001c000352000c4040016900110b0f08610040804840c44809000040c0300c3e1000941300a6035401e04130015403080081004100c41c0045a00e0150100e20704495848040c03081c1e10f000c201e042e000011085440e40c28072606d2455a8400c0080320401d0341c1419060505031241515584505544008900424095034800c0750582c080702d40e041c0343d910b43c20184a41040840c0469620342c070b080803d0b50090b94003481d0040c100c05e4103084a4021401404040442e40e1b44580340d004a21004141d947c02042200d151030183c0c0d660800341c40d40c0c0301401d0f202c0e81d400ca945809808117030070587c014401241c01080070342d044217a502e40c8020180c0614a420b40590178030909e07000c00c62103501003101c1c1c44008a001c202e00d00074404440040c8034040307000074100003040101c2e82441030141c14011031204c20800310145d202618400c030307014200141c0303c16000034242c0c0648100741c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 574990143 1250 574988893 574988923
    0x315030803181c020f0606010f120e190b060405090601080703060b0d050f0d03050c0f0313050c1309050c031b060a0309170406020d0e0303310305030702010809031218 73
    0x610321007566640001d80e10b0517404040225400d5032a0040150b0b81c0f00039440c1100000340181d104400c00700d6503a00701c859000c3c0c1a2044519854002c180307414102c6c10090129240d084020900040d4078050140982040c0400301400280d45092040c03607076005281300081080c1d13141d0481c11842d41d1058090b403d041c0e00601074402d00c0e040c41203da42c0390058541e900012900e0240400c1240d002c0c60b050390115146d49148900d5074485284081240020b0702084403540b2036050910440e0f242d56210b00c40440c030480f8040760007070503450030328240440480094040d07030050402030101707030040f10480403211080e55400e03920103c00600314040d200c0080f010301000d030280c0c6030540740c103d00700040c811106641d00355801c510107140c04039180d221108410358158802d110400750300810364450f085030043c400c909500c08020700d1001f01c074081a54010b0300c0c56040480c1600c150750300b1500c0c541e449406600654500450103106e2050088007a204088043c690203c1e001d2010003040340c0e00302c5080350 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 574991393 1250 574990143 574990183
    0x114060c01090b04120305360d020607141809130b010303021b180f1512070302040b090c0423091006090b1e1e0f0703031503080318 58
    0x908180751401010348040764100d00b504407a0f0011751080c400c40780281e02140101000310140a0820b5220300850081080800004031518080800300b0031010900740c0c40e005422149070076000030305200e01c4a00b0400b0032600402c03550080602e03007083c0c0c01c0075a41c1225102d40e55160074130310521031400031074010310030202ea40020003803540000c3c0c19540350608040080b1902d0014060091000752055842c814402c0d40000c0b0702c0c240070400d1011360003c052403c4481703410b06000003507040004840c035101543c12400e005d1003541018010003046070f038143d45c50f0b003140c2000b04800034544214420020010000c4031020b510310100c100002c90080c00901c98401d50400c4580c041aa150a20482c008145205070004283c01080c087d0b41411040c0071048442c0c6400040816103a81704806035082525180d4440c000031405c500a0100700304480003d50b22000340d07140140403512010955101c1d28550b02c000c20018500004403036110910462014002e05001091443c0505021700e06283c000f80d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 574992643 1250 574991393 574991411
    0xb090904140d020622050c0405040203010f060f03051510060f05070c0306151703091903020a06050c0105150a050f0a0b030a0c031b0c1e0c090606020c03150114060c01 73
    0x100140c4e4600880003007607a4000300e07011000c05c210f500f0450400a1103034120064101a500e46035226a50081c000380000c82e11641d002c40810880d8690b82120000540044041c001d01c4810003080000b4000c40034041c5544c00c1080344801c00c05c51512400080208156004607118466004c1d0b511040c0e11044000400c3d07100e01d018009403002052101919003c0c090000e8054420452090118001000b441c81d1001c01d40900540720384000e561204148541400401a1100510302c0002c00d0190380d0281c079021030004545c00d640000c0c0540f40d01c0c40c84524101041c0d9103072480b0108481d8100d409288003001c1601180702103050fa4010b403d840d03008010424a4040c68100c0d81003900c80e95410001326841d02008022107104941140004180201da00d0004401d8804621001264044107190384450380d50b43c0f03100c80c01500001c03026030700d4840820469404004556003580f00700c000c0e08d03d4450707550aa440d1204c051089504246031070b585203c083c0ca5240440f04541d100034000d000e9510307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 574993893 1250 574992643 574992647
    0x3080c070303110d090213061a0c1c021e010608030a0f030b040911042d0b01050403080d02090406060809150c070503042912060405040303020c06040614010902040b090904140d 77
    0x3035032009a0083c0c47c0e5186100c0c4510151003032005070f6880d078903841925888040d44000c41d8000f030304203925903ca00561800c0c87d400b5140f0003449841903074014565150301c2d404d8103541c400810380b55180740e0305003a0244454440481075400d2803c1c5843e0410071690500d0701200035000809a1581140c030301032800c018040c00d0300706411881401e0b00d061240ca842612a0840350504140769412242c091800c00c007441340a801c001c103107640c1458007a04241e100d8943d0991035110303520305031500d5400074000b8100d05203030003003400809243c1003803400b6113810051030340c0b203064003984c1002400710354000800c1c01414800b40c9082e9500b20303003240d485644a00302520403002c110b4101542e00e480300204c505402e1204200d4030036048801302640079884160912000d8070f00608110141a000d01401c1e000d524100a824821401044041140c3d04803200d800031036001030b040200b030700c0d00410080c4070001040702100c100c240140c0d402d2003117a55a04104100e45031031511b03007a1600691001d000031503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 574995143 1250 574993893 574993901
    0x5310207060504051c1d040c11150a0b0105030402060d0b041b08090f0d020a120219060c08070e01020c0906061918080a0b010b0a0905061c0f0903080c070303110d 71
    0x5080d00012540c510324031001601c41c007014220411241c1400381b0420600d0800360072010703000e04182018007134001280c6403141411501891261a2002802000300101203400f1340b403410042070801d02d241d030515801048480c410241d0400d901502c51384850441d880d03540c414080c6490b00003120030000070505004015503815514200207125a10150f110540080380d0110314009980060900c0e44c2507030394003001781c14100c0b086025802040e00f50b0000c0103d202c1211075080c0301c1e00340050312a400e01009001c101010701709004000183c40010b410f0390300020703038801c094800c07030b50703038500d5a91034000a100f4454590b41005991840c0200c801d110380200c410b00184550b400c000a216454607030031907440d01e00b60001780c280848076004210641120000303202c07a8569141c045500c94844020a000d075012080c10f54121000321000c980c84881485860030344030b1807030418424105035031401043c40d08050641e5a000d01c2c00201c0e030301010302035401b0341810721910718056207400b44112503034020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 574996393 1250 574995143 574995163
    0x90307090f090c0e0121170703090905130c0b0c0c03030d0606090b070803040809030f0d09141c0204020306030a0f05061e070206010b03090102040f080303060a0531020706050405 78
    0x28481c10b00c4013141c80180c801e03016050b20b10200810202003000d201ea4007807443d15601c141c9007500741c40c2e500c40000d41c080700106400b500940310381400c0d529081c130b20400c45c0c10040905286031314440708400082c14010040b022544008030390780e02c0e1034003030301410f09110000035120303450321000502c03103041149130f0007140455810b03480d518240c40c2e84900c0d0a82503c03480d00c000f041c0000410008001840720400751100b000040c0c100c031181c140460a03d460100c07110310090202c0e0904000304481c45d88080c0c01110b40d0420355132214211051200c001540c0003032580248a5030700400042d54a403000c01c4650308403500030b4440e1211100300c7c1031003626000b054940e00400742c0d00c2445400721082402c0c00f86d0280109500a05541e868140b5102040e000074001c1561035400700000129942c0c8803849402800c1950091962030402000300600700500c1d0748154020400203d601c20715860030203c800c0031081d211204076090f044c58a070700009210301c1c0c1c030085c00700749840148030a1200000d4a10380d8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 574997643 1250 574996393 574996403
    0x21c05011e170a060c090b1201092009040b010e090a055104020f040e15090a1505091e06030313120c030b0f0709050f0a0902090307090f09 61
    0x42507110001021626a04481603200f40d00140b4968001446a4092020321500c0d107050b0740400d4456032880060340c44419503000c2c103564000140000309061007000302450102c03400c03120301d62803055604020b000b0054160f1045941c1c61070300303400e640211203a0000c400c3c01800707050b86103450601e50000304419190280b20110100e481c0c3c1e9038082d8080702c0d85000344005c140d41d99a20350403048803a243c50490038454900303c4000821507503150340c0050058109807010564440b418542e11100300a001000c0e401c0400000c0c8035043e05449040340a0b4025140710004900c4400d844c18901c0c151031940d00c41e5800c00010700030880b030821b80329080514840705c50041c0c10a0340b10301c000c06659025002000541500c0082b0400084a064401c5024544036940c6000480c0c4d482d00c46030551a4100c0302c10120003558004c1000c8a540300d500480030b003034111229041c3c0110340d404514002c4050103001c524550004515180d6a0704004403002014036410911414543c8600c0001902c41001e003220 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 574998893 1250 574997643 574997699
    0x90c03050615130203070c050d0f020c030c0a170a080d05040b0a060510030209040e0607020d080109060e2701110a0306050306010e0c0901050c0703032d080a021c0501 73
    0xc500c20509400d051003080003400000300b8040d01101600950006d40b540042c0244c0d00310b107900080092252469034041c40d20389c0b40e0151030001020381004240100c0c00d1294100b00e2191030ba07952480c2034402a07601c1207000110000c0d1800900345494100300e406004100046404005100180c1105214501c10000408039881e0960260155805405559440240f40850340c4d00329200354050b000b005002040490008440c0c410703c3e040c0141625010b0040c0c100c1a14401160703080802c242c01007183d000100041d51501f80400030290024110b8400d45a09501b4009400c4500030014150200d19000301719001308102030002e02c0e4414880701002c00d00340700000400380780104074035048401524846040f5641c14810114950058503d00c2c10320105000b001441c0c81d04200303410246100f0f80303403007030007150108410034903c0d9001301041c81c150054001058103544050169005085c1c80342c0540c90b401030040c41400b211110819a40e214948000029084048082041c0319603d04403a56 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 575000000 1107 574998893 574998901
    0xa02090a0207030806030616140c0d0908010b030c030a020609011809090302101a09040507090f0f14270705040612050105070912020d05030409090c030506 68
    0x21202075000c50100100758006240c0d50304050120018040c41c54042d10304040c900488101c5020810100c03207420750500a10103a4002214480c1950390a101c4100000c0500c1c1552145440c0b035828050120035504003c501d400391130390007070040c182d501d006409100090740316000c1c85042008091078000782c021591030f814041c20342504d012174206c0d00b40c14002e2a010284003a000c82d14900b6002c80750705920801d41000d001c200343c0302c0c2e01150340d803400c1c17207401d1440d40d0b8030890a07641840d440b0b11090095a1040ea0302d41244c840800040800d40f038134178041c0300c0895101080030708091919084089070501d003400415424101c1c0c140c581c50300c4c041426a04a584030004896104856004004081c003900c1c1d4400c000346800c0b001e08dc40e01d0004040c0c0c20300000041c1c0a800d120488105001c1c040c030440b0040e080c01401480224440d00d041440081907102c00d5800b805104082 = true := by decide +kernel

theorem cover : BRFrame.Cov 574820143 575000000 := by
  have h0 := BRFrame.cov_init 574820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 574820143 ≤ n) (h2 : n < 575000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
