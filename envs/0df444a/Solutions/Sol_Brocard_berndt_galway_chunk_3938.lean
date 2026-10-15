-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3938
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:07:04.122344+00:00
-- url     : https://prove2.me/submissions/b3b2c68f-14b3-4311-bcaf-50101f424b89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 708093525 ≤ n < 708273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 708094775 1250 708093525 708093557
    0x3040510050a090308130602271f080a020c0a140a0b06092e030204020f040603050609010b251e050c0d051f0b060a050d0e0106080d120b0405040c0501 66
    0x240c1103030f0300103020940c1080410704189808203500c0456204580241c134011501d00c25000c0160150f14840b0318987c81200c28040f45031002210340c4032190245000741c41000c06030001d1040724080c00c0d003018154001050200000309011081d003cad0f03000544088030420501303c40d03a850113a40004e55045800c88041003880c0303040c01b00c80d406030a4a80c180080c403a8811b41c10076803ca4401100350520413004c90020050303c0314005098510341c45140552150b252020103001c0d00c1c0c005101c10301c43c103000c0b070060280c00f61510641c0d0480442840b440340321000d9602c0354091990303056000d4448000c2c280d0000c00b000180342a042e45a100300c05450036038502c2c206004208184000060254202c201c00c0402600143e0744000304030300503000030445034030b9040421907591090300400000b610018a2001c9500c16000311101d501c080c02c020004686490380f0540c41c0d112181d6000c081010b804010800c030005900a020f0190000b00100a6401e040c60074044649291194074046802d4106254210f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 708096025 1250 708094775 708094781
    0x6030708060610170408070302280305220801050106030e1204031214040311090105030c09012303060a020919121106071a06120703030e0f0f0603040510050a 69
    0xc5000340010401600c451003040503140e90350100e481000500d80001c07284041d4191407a0149000c0c0c2016507a5110a00b0004d05010b801c241400c401040b6071b021900340301300f00242c5251309416290558a4a01d0204c035203d6404510f40041400d41c080b44022812075010362091b03040b180303192820090500403101a5440d440010b504180d10401400b04001040110a03c404102010318044c846064040901c90300c42c0c10a41017924160602c101041c4d484c245450203d014007012030042010200c1c0c00001103032060140200e0500e00084074142414410301110700083c07080040544405150086080c1c1c001e400c008901441015910040051040703d178071400d040d1501d500850420381d4480d02c8076440100c0800f10150042c80c20440356010452102800b0811359500001c0101030802e030040001c80c0d0b130464078241d40c1703801c22181000040c1e0884100d0364204c0d41601c220392003440030300006038200106200f05411540000410081040c00f084504c45c07840000420401c54031503044460403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 708097275 1250 708096025 708096029
    0x207060f14041a040513060609140303220512160608040b010b0309120a08070e090106020c040906020904020f030718030f0209060d0c0f0302030f010c14130f060503040b060307 77
    0x401c0070442401909400c10b14884400d090140107480c140d030758008900c1d43d18183d0156000c403940c0d02418071400f0703800a80700f0024403810317212404181954000035200d12500b1241801203640410259181c880980e8030401840014600034800d4088007103651074010b0b403440e062000d5407061004c5070f00d601800380340303004035086090044540c0c2842d21000d02640013038204c850300c0c426000c03042c29503401140201086001c5940b0b80526080113100038140c039001d0b00095129916250041c0441170f800101c002440c4412940071518540302e0920303a0007885032050103604180009211180e65800c40015070190440ea651519100b1940d890340c031840c14240801860300504602c6140549001c04c4441c4c3c02000042408600e0281a039822004603890380c050080496113103030400545c035003131100c1c2c10080c01e400300a004015054100510000316403450001500c008502c0307100c0500f6264025000d040c0740da1443d5079043d22020058000e8008a07400c46d0030401c69000980c2d50305000c034803401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 708098525 1250 708097275 708097307
    0x418050c040302090403020705061602030d1d0409021503100f0911030c0a03020d0515040c020a05190c23040f021314030102070503040e150d051903031107030207060f 73
    0x200380790642c3d00300090142c02030300c181c0441c442d407100443c4c1c550361540204261243c03030901e503040841134810b140c24040c18407504c005000308212159034421541c40c03034514140c2c0445000512410a1000032101d401c050f003407103024040402080f0f022003c800010b1305844d640362444000d641e5070a044d506681e00071000715403882d401c2c0003103100c400d400c00c0a000c0300d04107400c0c09404d000b01001040c0489400300c940d12550b082000c440c0d80d0506003807003207040180040c8040c000c0d03086503481e41d42e5604940a0120b01649040d81712800f400b5202070a00c0103400944034241c04802d094419401074402e262400340b0a900d80410681c20240b64821120700c90146d2030100c0e40300b8580800c013040450040c8440e170301950204155000103c1c2400140040c0040c960701c0c07802410214035814880c2c2c001e01c00d03d03000308098842c481c007203600010011416106900c80c60346c85140c81c0f0f0b0823030142280383c9031884240004141e11080680110310101030700d10541c2c803584616401d04088415001c40d0701510 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 708099775 1250 708098525 708098527
    0x1050906060a09090b06071a010f09020f04030b0702030c06130209100315091e061d030901090905060a0f030506040b0906220611040308040f060f05090f180c0418050c 73
    0x8481c2020f44c10175071042500030031072400d044c001d80300ca10b03c1d640000c080b5140c140038400180005d4078112808000381100180c02c50514043c280d1000c030500c22800003810ba08251000036070b072580708004070368040106605840c030341e040c0b41c007030002500c414500032489000840c0010b80e1484a0050180842e5000320b00e00070201e5008840740c00038000b00105807031a2400700c0a482c150f01400f91480c03c0684101400111003038140e418161140307080040d0b85030b5401c20040344a440c0c1e4044038910541d07503140000141030702c61a00198120106911009605803260000800d0100c040307030036485240510080310b4581c2d00c00042a0b242d15089131030380780d2180044445042d92400c401b0118040c0e106410011304903413442c50301406500302d40d00499440e0030000e810b100b030000d0350603444000c18441c240003588840052004d07019002c3c0c80c1c0070501a40f50620010503641e54078040030f0542c22000c02140890404140000751750f40300c0e0250f056a250080e00c0303840c01c001d01c0c1c480e491059040038985 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 708101025 1250 708099775 708099779
    0x501020d0509010c030c061b02060c0c030f0a050408010c0f0e03161401030603140f070b03090a0201030207021816020106060804330f0c030509032701050c010203040b01050906060a09 80
    0x6545040c1d40c1e0809508100846c1d41d650700043d4144102400d2501c0f244c61407500182420009203400310003805450881814001c60403003400c000181d0b020150311204294607240311303c008a55070300499200d83d640c1d41c200004060015080400402000240d0341c49085031601407007419502d90b440c1c138200d812001c140341d0800c01184113418031840818149004034541d6030382d464504a804041101e070700d480c0c01c203180090f000102000038a000300003840100d0300f14540850701d15200c5510f0b1030b001e07040c1600050b01c03208550324041156200588400c0d03000c02410b114441da894102c41440f1000075601e0010040b50060003000c11070f07c074907031101010700072098641484030403814000519a00e030740d444802c1c004440450040f4039400d000e00c2d00016610344071500003410307148041c181911942040000c041903844004210040440200752940302402c1000122410f208640c80380d062944040306010030055400d80843c100c6504481c00c1c3d15985030002042030a1051102c500085082313505d00b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 708102275 1250 708101025 708101027
    0x60f0108090a0510050105010801151704020d080a0309060e0102040b041520101401062708030403032d0503040f0330050711101503061b03060501020d050901 69
    0x124551000900060303030b030300c221a9625546010405581e00c00d03000e48400043c012540e2091401d8010701948120810301e011a03200074000307060740300c0940004080030000600f0340d1910304500d1202076122002e143e5600c0d01d01401001401c29210843e58203052200010b03616805000f5902500c80714414a85410318001c444040e000c541c0d5500810b10600c44800c1086074104407940016102c440083c00031201d100e161241140c0301c81958009048501e001440b0041e88442e08010400703060b014203010300c0c5005e41c00a81211694803410702480000703008010140d10904c0d94440d807845100d0301403002400100f82c0e0780f810b004605200003440500000c1c000c0742204400f064500c0c0603080c240240102070503404203520340201448841200c0721030046403011039200d810f61081e00c078078154100c2d268401c0f94584921f008840c4055072600c0da00c05445140c4242d0701c0f94021a4841000c1141d90668400010010304042c898400303e072030144e00043c1e550000c1002402c02025030b49040c030305240000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 708103525 1250 708102275 708102287
    0x2016090207060e0a051b03030a0f08091c0e040e030703080c032802090f01090803091201151205101a2101090503132403021b0a060605090f060f01 64
    0x1100351501503c030b06100d0400c0105010b1040c205000d007028281c00f001d64000c02e410707044503819460290b481000400070081e4170100c140100d00c4a840c00f2070280c0c0f03d00c01080d182000500000300c1030f1a04c400c2226042d90825050154040d06503402d000b424107051300c0030b0f201d01801902401083e200b0002480158240300216407080826800f800b00206502d00c024601c080f000301e140304154009040728140c60907d11071001e00d4000d01c1c1c001c0245090208064a9025143d21103006405407000c0c10b0081000f1342100c030640c0c6000801e0300c08199141d07110144440c00f01000d1fa03c90061070581c211450041c01810f000511468070400b4800c0010700340718846510109144070620106c0c92050b242c1c2081c02100f00780360160004580740c10110b8151070701c28015520030045c15003603e21156090303503960746803181165a07050050b150700c2041110702008000c0003895443d405042140c000b001026800300c0c090702da082d544a030695558440309403990600b502c00c50384c80504010700c403503e0b42c4145 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 708104775 1250 708103525 708103537
    0x71d0c040909081902060f0f100e0a2901090f0e060f010507061a0f010f0c080901021501080d201903030b130603060b0301020307050a0c0305090d0320160902 69
    0x1206840c82c20004203103000c1441d415010303d01c0141c201b40c1c20b208a001480c4100c50f0000000741d410b0310ba50070322081095800566105040c1c1c0300300b480c0d0004074140c1c1d880e80042ca52070141900d034203614500940ca08184a03500703e80c02e02040710b0a0000c107844020300348203410760700c0510207240903449110800070306c0c0f100c55000c541006800c010410004234540198043c05240c1c460950307107500040308004800c48031440660411650700c0c10b1040c0b0329881400002c500344c000549075504c140c2c05004030300f403034079031004144409442030001031076803000140c100007040c0d10395031304605408140c5800c0080030024111001c5a2090a0004080c0c060980031410342d40700f400c0010b0819103950201e5030310080071000d41c40103a03036402c00f04140a41ca004045da100d80031402145907180003e405803090049800400820035007909580401d070007041101c1269100401107000c030f4001e480c0043c103c2c0a1071041d1320004c1519070303518a41c0c400006d45d03420341c0d004030a200c290460070000c4c0e51000350810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 708106025 1250 708104775 708104783
    0x5091f200304090f0e0106050402130608101214070e10150e031c02010f0605061c02390706021f06331b14010b030f071d0c040909 57
    0x2084000b51420943c032443d2100c1c9031300030740800c181d4412100542121030907888640035500410000310f101001c20304000a0720a10308028550742c86200000d40400416000b140c6500d80050108040c000780101c00080c40300040101c40e0700c55125a0425142607050307a44460383c81c260b50007804150010405103150001621f04440964104000079190000d1006c420a001d010844101000b690a000718108800292418001c0303d1030080820840d2081c40040500c80501c20101c8400d03c665030115404284001440107017203106c1111513a58002c1021480401d0906075100840801701181460886207250060810b0140080c007044482c004030003640f0103079a0b520b401003140f1001c801101ca96000a54602d031400c0a1b03c00c42800440f00184100140210340407240d0808414170400e203500769104030400403103810038401d140501048565035a041c0904001420341e950002501012112a900040f500d040c064411110704c200a440503840740000300410301c40c458058012055842c41 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 708107275 1250 708106025 708106027
    0xf0405060c0118030f1103030f07030b061201030303060e0f070c0230240103120c030e040513020f0103020903151e01030b190e061b0c030a05091f2003 66
    0xb107003d64002421068008a01003840106180c0744d059010340142001c504c2d42c1c0040d442c50401030304000366032400814078002c054541c051008a5100d003000c0e1440032400854404032943c50b4076025000e81403501402c03012007600030000700344a090202460040b1015200c1401d0005103400740030108060030641d903c80e81c622811510b5807104504214031a840e4070000c0c1045624000f18182d80050400c140d81d00307e66800010700c0820491280903003201a541402500304106107000d56541030400c8407158001d141500700034512100300300c0c41490038821120265604402e40040d4100d0180e000460382581c8a0810036120340c041643d102d4000d00c151400c000500000c0404c0d103980700c0260411180c11320103a007030001d100070f020035a06550311b41c20424407004084000780d80e610a40107041c00d0038400c00c0b044c401e030f1340b2043d503084404429410050300e50310b0510a0010b002503008141d03080c02946203400c003102d01c81c3c0f4108050f2901c14a60f0782c3c1103004e01c00c01820080b90000c81110141800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 708108525 1250 708107275 708107291
    0xc0804020910170102030f0a05010503070b070c05060a0302070c05040c050d0b060d05190509061915052d1c030c030e03100905240613020f180a0b0f0405060c01 70
    0x1845043d1412180407410015a984c50400f070440601a0701500d1100c3c07090070034005114035070703001c151101640c0e4855039107610f510003800c18034040b880700c4d406150040c0000032a081c49070b40c50740044c18501d004644108080d5910030a1204481c1542000c1001030702c01d018050341c00d0090780002030b040800408080c101320550061030225001600da054000d40c0007101011a4003103401001e500084800c003800342071800e25491781205440c00004100f41e90398003200351900040c00044806450003400a40d10700441c0000700b0444052610482c098043e01e9640390080d20b01074904400042d0f01c140416110f400c4d0707075070a0302d280d0f000300b908a05000c21001019440d403010000340340c21304100100420300a80e20705200b402d0120740c8440c0c0d00340750b0340300c41d1104014041c0d50a0a40151054803511408082052100000e010707811020201c076000181e08031030343e10f18007221000b04104030b60b01e0750460f80c1c91044030541d10600f616038107101003d000802a40c505030001e050214102400031448c11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 708109775 1250 708108525 708108539
    0x2030c0d030509060702010603020d0b06010c0b040309080c041a01110307080706050a05070503060907110a02092401111f0e030d0603060b06040e390d0c030c0804020910 74
    0xc00444803200000356101c04115442d501048499044071481c00200506400c60300858040c1c1035100000e40311243c00004104242d219100c150305481c0c009141c0c8149040a150003031400c0304070300c0385159502c2091034640c0c43d890719215515480e80721903144c034107100c00000103540081087c0b2030103400f030109200000128500b400104075251140c40c2c0000e0b94a0b02850840c11144081d03c0c0f0b208100007801080001d071214203e20390040001e050070600c42100c00c220310318000568000075049800c0364103001503100d0351030350b641110520301901e1264a1850004460307484c2e50741041c45050344080c5142e5486076580520112010845501203600c000044d4498910b91004140703001c099605d200800a000710b612940d08402c900301e03000341c60315252441f04501d407140070f400038195003600070b0801111100b83e4070f0440500003181c218500c008654240b0f4004d60411070510318000c0c10a9201020706210b442000224000340d202d80006c1d8030741c0e40034030452420040010301a1809144046440c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 708111025 1250 708109775 708109783
    0x708060109091b051806060405040c05070c0605070f0b0603010b0a06020c15040b070b0c131203020f03120f10030c08010209040e1506090c070b100905090d0206070f02030c 75
    0x1e00049940480c096240b45016010001c0e40f1610200200003904144910398032080c8071681c81d0300000d261070070f80d11248005801741c030403039201541c803602d803101e6085410b0f0860080c02c0020b008244c0103503007582e10201940c80c0d220380c0d50011f000700b00750400f14001420010b0a9504044040c000051500480010640c14107041d0031203005070780a08580070316480e04441966812611807092820701c0e1034000c448030140a10703440103000400c24030001c0e82c11603085040c2c07210300e403606080c030001503518000301810014803101600140905003d59025040000884d200344a11012001d03a43c0c0c1c86448001120a0182205688039544c1100201042d2184403c4000c0e1680320001651041e041c010002102c0d8250b85000030740c0c0110080d40e81090490700d034543c0c01407040d41d03050000e6540802200c054450307050010702d850101414003c000ca082072081042c1c4d424400c00f0080c2c1d0303c603400080e5070303103146040c0034006901160014022a11802d02202c052002c0d0044034280400480001c1c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 708112275 1250 708111025 708111029
    0x10110f030304080c01200a14090402030c04240503040201270b03150415140d06020c1024050118080f01020a0e060f0d2a0804050106090b010e100207080601 68
    0x803c0601144202c003014080c0324400d202d901540000c0010a03c1c0c20040e410b501800508100b48042e100908055111034000c0310201301d0010301c115924075001c0b900e13809d40d4225000c3c8040e00b46e030b42030762100c003400a45404500120503465250840e6200d40c011216548860b02956201c4090460702a103800c1e5811300384060301d41c2000c43c4e40c485c94a1942c003c00c40e20314000085c4603d00b880e00c185180d44445160406842d1703175181c40307000c40941c0f0012070700c1d44e40c415400402c0e0603c0068400d6018102042a12450305200018007184c00d4640d420001840174034443c0c002004100c100300140d60142d940c41416546110201050b540e841c21814104440c0e90a40340309a5000100350500c5a44074001d00c0b5198401c880040c00e18401c191034090314000d000d11303140503075921741101a81140d101102c84060100801d5441010583d210003031036090701360b0b0200c17225801e0003400f081c00021070240c01581ca1040e9281c4013202107240070031507600091038591055020301c000100c0c4030310043c440280 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 708113525 1250 708112275 708112283
    0x60a031406040201260411030106080312040c0e010315091103030a090f0512120a0e040e0c01120501080a1104060906081c05040b041206060902040f080f03040510110f030304 76
    0xc510b09030001500e40d901714004000f00a812480c4c81c801c02a5950f906078005820211188603848040042801000d03280c000010172301c00030400070041590b402c00148598443e00200700e8880c1e0b2903420041c2800280001009000312100b09040032240d580401002d0780a51000e880311202080407d043d98400200b5400207842c4030030071b210403d2051400c0d40144416903500502e426411000e6842d142040380d44c0800803000100c4d040302d107120f00078460101c1c030010010040150f80e015a00e1395103803502c28403404030b402e66171041d1780f600c1c0600c1580c0c1250050740213040802030300c0c4d860400519030000307200e078016662000403032954058070454002c2c0c40400014000380c5014000e0800c041402c0c5040c3d805c01000f04024484002040300395401c41d0102c1c400003800c0350302413070140060004c680088107141d20100d00062440c000e00521000c4510a40580380c0b0b40515050b010f85034815800342503008540d60150640d000d105500c0701040158182c1602c01c0d50602180650640d44203407003c0d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 708114775 1250 708113525 708113533
    0x10b0d0b040b0901181803020601061d1005090108151c2103090318030f1509060509060601090e13080705070f03050105341d0a0b0d0b030a0305090603060a0314 70
    0x520185c0e240c403c40042600c2c04200700450a12560000c3d960001401008200720204ca07140003a103076684103d80c1c9140004011101c0fa544492008205030030400c1d807075000038200f102003450324441c7c0000a044040240c00e02c83c80b8002d1040003041c071405c00b00e080ba5002c40c0082c00d1091490b0261004120818039500410b06002c1810000c0c0120a84442ca40c4204038402040000580d640d0002d026182c1c419660702810a42c801c0e40d100030701d0400c40141000341444200b0030f440c40042500740c40786100740c07514410552181c807a4480100216a9412101c00f401c02600106215001801d40180706030304803a03034180c440d01040c1c10100e43d54412140f0303a45039014070698201024441400d05004000a6580c9491460b007401c49440f0241740010300040381c4407540110804118100c1080d800703451a4011030343c0d84010313003490b806012603640c064a000603120140c074000c5110b20741c4507003658545041c22494402c10138540d20160526900201c010000030016440004651910500310050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 708116025 1250 708114775 708114809
    0x803040203160b1e1b0c0909280609051f110c0303040f060b041508060907060914010c020907110709021903020c3c0303010b0d0b040b0901 61
    0x1041ca4801403140c9400b40310402d6409200d16255141550400d2070149407500450180160aa8442c451040d08040d00c6400203020700d4509030002d0042089a010f50b500f80007562459600390702d500000241d050441076000d40e0041e2481c8034030400706110f0007400005000e10b01c0307542d190320340070441c20001d41d540f0380802e1103806500c45104261a10b10241c4050b80341401030114035499200c020001070088060f0322081060040b15407040182c508080c004000320442001d64110b8554107210b000901d105107800102e8070640814040115042a1a00c540b003c3c10080000f20740807100205034104440e107542c00e00981d40301c45030725000e262281c50b00c041070000007481c01d003890b1454010100b42c500400649040d00314117807a40480b103400f40b0b80143c596038844030140c03e00380d400f00c01d640c070300406407440710482d0240c403065605c0f008003200780d0800885009100752280800d00c205594142c2c1030cc0801c2c0c4220341c5070801d250442d13005000282d0b1161150000c1d040c04420703004180c125021182c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 708117275 1250 708116025 708116029
    0x22b0510051b070f0f0605092b090b0a140f03160c110409050a050d080609010e0402010e060c01180c051216030f0c0e0a020307030b06070c0b090105090d08030402 71
    0x1d0240c2100c1800b01c0640566102d0750310807814425031070000c000e02400f0802d01c0134008500c682c0f161066200105000c10b0030b12031601c60707442e4551038143c80c112410710f0205900b4081054074000114a075201c1c0d500d030303a20b80b0812011030340200b01c9101c20310030319040f600301c90045203008040d610804502e0356203078144800800440304a084400b010b100714040e859000c507802140480c400003085501080385041450500d0400154480090252064032407003040326030065516441820252100d2001e80e0b0303900d031a0100503c0036600640810340070600e0407114280b0600070a428450074001281a9140301e440c0011810b8214080d1014a034a11041c05145004504101c1d2034bc0900004e058600c0d20354203400c8000020b1000a080c051030050302c0e0200001011440700078036014030510118500249507030065807080320000c0020345000107200b80c40c03400d038040e5840c00343c121001d016558142920524a94854541c0d18180007082c00302c89001c1c0c0d03032071032075100261003850140d480341442e03c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 708118525 1250 708117275 708117281
    0x712080d240e07021507050f03090a0611070809091815040302061021110a170606010c030c030806011b0f0605090a080703030b1903060e100216022b0510 67
    0x1209949a20b0342c248012650300181e000c1a08103190f00034181c60702d0f4403106072440c0c8209901038948038800b1080080b065804920241254010642480304803d400c001034500d104150b0001d280800511152160f0300b00621050b030702450750100b080110740080d0203e403608040714400007070b81e1060803c110426506002c8113800c07031f81d0213036041ca0032030030004e048000750064a404100c4041d0300c0540c0c3e09010301d0200100036100d002d030400c0c11003a100c0d0031080d0701c1003007043d01c0b0209104542c0858865407040e42080c1d109601650b400102486c1c86d90102c54119020717041c1c0b810000c441460040840510400d42c800b40d10880c450304003255a868028141c0b08020300c10489900401c0402000c1243c0404a4140c10790610300040c6140003000050300001d60b034460310914400b09100401000025844440180103000c1120100c01542800f5020b0b031044450309800c010301e0468040041c2003480081407051540100e0200d4082c401100c034112102c0000b09540641c4005402004030b4040c0c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 708119775 1250 708118525 708118529
    0xf051503010b0d0f060207080307021c0503040b01180f1806150e0714120c0918060109050d030e090a1407020705030d0809030c0d0905010e0d050712080d24 68
    0x203002484412070660009103840b000000191451412001e030f981000030503070495448648c40f04070b8546900300754100959500e100320200e401c101d01845051500b80c001d10650744620f5021701c24600d540c2c00e2445812500e41255404042d0b151103a00f03003c00c0c44107600400703040c51802e01c51841c0510301b80c02c103501682e101100d0f4582c01d0303082c804240032050810a03403e81c410310508020b031903c1010108008184550030003681c1c0b940707400d005c0c40200c0314038000400c09104101c40e20b01384d901d02010b52a241032020b940c9140458010182040390381454203510079014004e0800f50205000840444c8400c04125200c11a071903940da00003100a0142e9007054108190388000c007046030a0002003035945140007a804240302c103050000b00402d804204441e401842e410a40d2220b10a06401800704503150090f540403d20389028504a414200304d00c81c0001d030404010a00c0d10314040f071101c028403e0810964001c103007000150402d419074050038040b850224024030140100c0e030681c1a4208080d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 708121025 1250 708119775 708119779
    0x30b0603010e010608040c24080a14010512070308070f050106080d022805031201151809050406090b15090c0901020303070e03070f06020708100207020a0303210f0515 73
    0x384010301800c841c1d21659415141c0302d0410351300351b4603071307050010820119910001c0014040501000e82030540801010820b12549820805403078058800341595003010541080700840401080700307203000888035007500c8c003000a07518000c4e200c1c3c0343c041c0c1c1c50340200000c4c0c0b5291040104841000001d126807001000803901814410105600003500c1e8100c513000171380011140c008900d00080046c044e1511103a1203000c4070b0391448108002c101e102802d20411091803100d408800005015141440340c0f90030951403090102d0500c06003000500000c0d10907104c60744c5d07844c02000040e83d41b010481c00f9140c1c070038108440070f03544000c2001c0482c0c000e0a414100000340403021141e600002a260081098108424442d2000010910700005036010070031481c4440000100e20785c002c15000203481101c0d050320314029140c4207842c240d1040d01c60003900005544404c0000c00e02c68040300020300c400103445500c0c0502096a0401e41e08070591040c941c540e0341d01848024030300c03418000628041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 708122275 1250 708121025 708121027
    0xc080f0a110307181a040606020d020609010b0d03110313030309080d0c030c0b06040b031b040b030715080c0c010f0e190c1415030a06030327120302030d0608010507030b06 75
    0xc109200e0310002400401a428a8507026042c020307000c0c4200f041c0c060741c005403003040f04643d907035002994ae1076602d45a5015008000104842034030600415035081c00103000549803040030b945c1221b6072031a010300000507010a100200100c1403440f442c000850196603803c04450030101e03901c0c00e11840c09079801c02d2000281181e000250428241e0701d1150b04200542401e40d1032502140c0904921644158540078142070b11944004011a0100307203a4117803420030a008000090560306c50f858021016030384281700900311202c0c4114116a400b803081c02105040c4a01e0030011800e40b04080f0102c50195114600b00d00404410400e01401003001c00780d0203111802c980710244810b440d4016181d012034464981e6510340c982c50b018526001f0700d000ca141d43c07450020498001800240000c43c00500c502c40200c40e541500000790481417035800010065074640302401301807050800c0101c0030b60106201c070401e003070b03010311800000789001800811a442e1030340c401412542c92107032242c07103044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 708123525 1250 708122275 708122279
    0x30d0e0a05010c030e33040305030f13030b010312030b0904020f091308040b03060a080a08220509091b040212060f010302370302040501020d0c0c080f0a110307 70
    0x240d041800310841e442030030101e4a900080c103080750b010145040e01c94100c0c0c0c580020382185a09070801c400c1031085249002801c0304680d14481c801e2190b848050000d6206100740c1060742d4140c4000c050300d00d08404540c07803103030b560750751200c1151007644142c42c04011606c6000b2240c0e01401503030500072045460325184e00e0030f0ba000441e102c4208107580d000710450000030700d8120301192043c011580100c102c80d00c0e00d039200d1600d0348550003118100e0141240b40380c006102440011100449503000300300504111401000310294032400e50340d00f64680ca0310301c00107a10745800402a000d200040040e0085480e000c0450600301a49004103000d075104000c0d0814004403c401d0740d4010000b2505448104400d00c0100d01030b0180d002c0d41c00759102c2030798005000916846460100c072003000f0a4040e00c410a1406030100c0c0101e00c625070240c1c00601944915510a410100340f60b84640841901a0f88400b0303094500303245082100aa03a0018901c036081c05030160701a03080e240c04800900c0524 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 708124775 1250 708123525 708123529
    0x203070e060d060906021e0705120304080712051e0c2b210204120b01050f1008061207080d090801091e030201061e030b1312050a1107060905030d0e 65
    0x410004001c1c00083d513500c05402003141503011140709084030340703015aa039900842c01c2001540300c00e01c122854412031440c45c00c00c1400f001900d2044c1d400c290498101002611026140c4076441100b0b81000700401070344140031550700030658010340c52600c0d20303110030b0100b150510304021101c03031100080301c10350b502980d449200002c10100d1054074000340e0404288040b051205c15036064283e5180c0045000b2502d40342c020080840c240c0190140c40369a681c40090040b12141883d1040e00044c3e12000283c4040c0141c0303090380c100a01400141c84200001e07099410410759420420080e0450802d694000d41c1c0714034040054440740c0001c03c1558103541d982100c0c0745115517825002020b40c01940241030007903005c00028040d0301c480201395840b4494a000c00c5055020495201c214400400c0003040361140080c8000c1e0300c2000f01424544114044d44da50300442d04490811400b03240d541d801c5001840040010505d13610b480341100d040104050800760001c0f040003c01c80300411040c0304d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 708126025 1250 708124775 708124789
    0x30911012a050c0603040f0312051e040503091504090606031b1404030c0303081605070308060918010906020706270305070602120709050111032a1e06040203070e06 72
    0x41215140e4442034400c01e842c000303041281000c1d146078843c8000c41008280708441f550305000c640310303907914508503860402d60781c201c50054602c0342c5443c29208c56a10046001084260068000d8040700c0c288081322001a0314110b00c2c800041010601040421201c891030064402416003414103010260803c1a8510780d03281c62081c034400c01118408a070584081c080448020310b4202d454840025242d05010b425040c064800018410102c0c032001c422900c188241c8075000d900d03565018a03912502d0800425000207488040306505115850729241024442c0c82c24052013a000940c9a22042c02c00d94221095400417a5090140b08009a030454540c0708551045501d42000b03501d4118a0030020000c0c0111505010014031440a0205440d041000c40d400c8a0090343c03400d003151700d40803240381c90f4058818001c82e58942c03c40202110f164015030101014040c0d02203440c448032518522a1184080704400c00351b0300305109100c1541818440c80000c1c018600c120100341c10544041421 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 708127275 1250 708126025 708126077
    0x703060c0914060a030e0a0b0601021b01080411010e0301020a030e0d0e06121308040305300d11090901061701080705010e06030403090305070b0a030f050f19090b0703091101 76
    0x86008001080380715030340280d100881b000c590f00106c8201ea4440d01c5c000030008426a40c080c05803044040681080701c03218603a06856006a641c1c0c803030794550307983d0560100c190311b240c54103100d03440440300003076102440a00941d030025640442d4982824014604004005030000200404450104100c0d183c1c40125803900b060384041c20466034a442800070900070207100240480400940001400700c0040c0183c011218820101031a250410035119400b10304224480000c0c0144900c041072411a40f0102500702848159843c0440f200000b8200c92002d0304642c0110307582d2820b440015003440803c0d0b000d0140040103260403800e10300003802031550480041e12607400040080c0800d441802184021039000303040301d081c2501c451b40e0619641028400304002854032554046494440c05001e008110001300c25071943c0f5810401070b5200c00d403000300a03056440d154540009074030540f50521031401c6980000d40340ca41e600d8000052034543d1001e0f410454148800e000700800210360b260 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 708128525 1250 708127275 708127279
    0xf030e0a11090a020706090602030702060f040201080112020105042d17101a09270102030f011217030a06050112020a021513080304233405120703060c0914 68
    0x2c140d80e8241d555003c0e2082810051440741404241030400800c5c0e0050b60103100c26400b81c44d49951741501c0f01149540c00c88010b80080c4054004010a440f0706540c1d080c001c2c01850a01e24144e15107219a0080480c24070b0f22403114020076200100014110308007002d01031403020340030090060702d40296240c1d202c4000c01c0c0b41d00d81d03803032103042c2400c40191980c814020280191300a46070104620580300240040ca0102051070414046a8031062003100d2140c5040f00078116075900301103022005064924084401c2d001c415000101c80300c018000e140304a0070084003017060f83c2090001001c038800603402e038400500600c411000075030049400c000c52050103080040507034032900c0c1c05101c0c840c0c2c6c4c000541801030000500c41400f48920140c1141d10304c45e15117504c4020074441d8182d0340e03c5c40101e601d48030981c0c00e00022071045940d03440118030b50a00c0d0080d1445440e0b0001508280d104860f404407903004550801c2000101e00481005400c0d5050881e00a23140040804440d02d0f071103440c43c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 708129775 1250 708128525 708128539
    0xc07090e0f0615040615020105100b1c0c030908120402010210020f16020a150c1106040807061b23010609020c070501030b0a080105130b0a050103030e0103020703110d0f030e0a11 78
    0x3e200c40d1240d602850007400849014070340c040b545103019008200030748101c5400d0304076544c080b03a84d030344100c00c9940d04410a080103003c600440c0b886002082d11001c3c0b60304041d210400f03440860a02c0014120444800c074031030311241071920000e071901d1f60501c11135540c03a0050100035000c2d0140819030750940540c100c901a4441316200049420582c4e0f00702100325420b079081c420910748c1c804030b640c860314483e00e00911400c20050030010703140a188620201170780920380a10038a4440c400c5510342c176002424007000713020039681e0382e04130f1200448924803445040d2820f403041076090241c1c000910002c2c0b411881c21200b08900d64681505003d0281855207507030b070326030300e07500c4c1d944040c1c2c010701c81200208a02d0801c1c40c0054502071000b44151101c07100100411498803c5120303c0d0b0480750b15844d24109118a14010750180d003108030180e051080c0e80c0044071500c2001d01030302c00c80407410f660740389203650040d0b4050115200f55201e003140303078040400000042d84085000d41d10030021500e007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 708131025 1250 708129775 708129811
    0x307090e10030204090f2f0a080307031b0b0403050c060a05040b01060e01020a052e060b0d050a0e0a120f0314060d0822030308060405390c07090e0f06 66
    0x80200882280401840d122681f950300c0b50b0303c6290340401c41d42601007912007989104960410003001980d000c1c482c1070740c1040203484000f90040c01c210800b4281d20901000f03a501680b5204082c03c0122000d601240c0002001601c06600b80714284d44031040030b00411082c1000c0c0c07101804488140a03510a12140f41c042980f2a070080203503a03101940001200c1c024001d54142c01e105040001c80041000708000c000d1443c0d83c2d180c043d070010303a03c400f04400d00f45040110160003509018116000c050f03a030f00300a0940355824001c40c40c0141c05035402e000135181c01c071002030001100b0480402050320b04641e20b404040c0c880617990b0466404c403200c4044100d181010052440392090701c40c2c420404201d01c103400c034032003401a401c4074081c0d1681c291555841043c0700070380d90b003140c2062120000c28110804401d48030540404040700030074800740040b40c00300c043d42c4d660041c10018030f20b501c0104104005047c50050341290802e50029003005180f402d0348541c0c5c0c48000e080c00c00301010000003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 708132275 1250 708131025 708131033
    0x106051602371a0c2a031b280312050412152a1404090f020304120201020a14030901091e0b0702120f1c0e030307090e1003020409 57
    0x6205205425045000e010004552200416800b548a4003e4800348003180700000c40851041e120016400380c05800b04186285004007001c442c40881d0600080e461680d2003070340c5082242c4101c02c54080301180c0b030040290100035020003034041807611803403442010910952035401000481340d009521314070a090840301a1003900070b6400c1210545400c9044034280400c0c3d015510407040000340800461a036440031090030201110416905030302d5185110049114841820160070200c04c010f0030039481e001c6050580c0c240c2280d28421540200a00080c0a000b820900411003940000c40c0760450f036110141c40841e21180b0440b138110007100041400800390007002681e68810140c5c01030207a20b40000780068508441550310500072000581079500008400c4038a00c026a206030800303112040001c55580b060100905501c24410701c5400f99043d40070788800b00700000e000d10f441c0c0c0741100c001440d850703803944006070b0800c1c1c440900c000c10083c940b100040c2e82d010384000c1250365030303420 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 708133525 1250 708132275 708132319
    0xe1b0910090504050a110301051b0a09030b01060c03020c0f0108180a08030a020304120e09010b0d0b1c02010f050f0409020a050c0618010e1501090b220c080106051602 73
    0x10001d801642031004020802c800400c0d0a60314620940a903803441c40000c040c1800c0316011110305d000c1aa41240101c0e800700e0940c05000c0c070189a281c1021007036180d684498101c1000e074041004210403003184410580c0603c418851508103441d80960000c1c3c66000811031140500006034a00224840c1d17007494009000c4a1341c450f40180c20f21340d40b810403640c14402940300306e506a545501c4d80d810021401e105250941103240300070042c0c152030f4280004100140d0200c820340c4059a52500c002110f0707200d04044034814002420440958440c6000240c14000a06c14607020001e0070030030b2940b1075107440207603810794603038190050300c0c1c002c0c210040c0d0b8644155000108948038a0040001130000f0181019804543c01d00074054004e15200e559070b103140344c6907031041c007120703071030043c0010500d503440703094600002442d298030011103200018195103a01042a485504c8600c0074500c9900207000c40c2c0180024a05540341c5149110340c0c00e48107096030350081c822480c60403e05001d0070f18030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 708134775 1250 708133525 708133529
    0x10501050906070b0c09130516110327092a0a0504050306190f0905030f090f2805090105011d012006060307050301050915040812070e03010e1b0910 65
    0x7602100d15030504c1701d0030020703903040480a20702c0f401010034204501810350140c14043c0040410345840b504079041c056400c04000d1a03d41010300c0140042440070180e00c1080040304010000e911405182c032091000361200103280e040d0401c0078103403d81440303e02600f10440d00c2d48211074242c0b06e10071408126094801d642c040c6034544114424450540108030f01030050141a50041100c03c0441c072000d011344410760f0300682260000e0083c5005c183c941001090303030390030080c42500b84041c0000000c41980b0030300b000515903042490700c22044800d00038418042c101c00c5410490540c075200000340b80c00c03088407640640030700700008494164080c0340e0402e8054104080c0314161142065000d507540c0302103030114424410440c1c0080c0d5403c0c18030801780290042c802070410020303071110700a8500d02c01381080350210402c02a2659040081c2039a46c069041d580c1d9000003e40c101040609644119640c641d0360381150b40e004001d88142904503898420658101486070344103084000c40072070503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 708136025 1250 708134775 708134783
    0x30c0606170106090b030718020918070801120c0302240a02030a08130317070909090c060e0a080639031e0f0c0903010209040c0f02190b01050105090607 67
    0x12001103420300c1050000404000181c008000701c968441180041d40d00110007641c042c3c0001d242400058041c5003035a01c4050412000341c03408840001003564441d00c00c45a0007a80a02402e10007100c0d8892075441c018104500c4c40301158036180c8480307140c100d8902c8001d206010113555120160100c2c0b07024008107480b0849ca41d20b038801041c02075140e510240c0c1e42d00000712000005859000c130405520025509a6940000440910b6080ba40640042c10202c00d03c041e0301d00000d1000b5090285601c0340d4031881d020391010f803809101500c2c0352141c40740d1600c1000d0381c68081c0108400001c610b170f40600344060015410761140e10182041c1e080d14441504840c081003a084400c406400031800740740c0485461a0f042c00308403a1140e184030690b40340c007030101840c0100b40004503d00140059860040006240c245031100280072112423022040100e40e29203044098290140309a282d2842c1d00348085a08001035a02e00780a1134050140d1414400081000030250302c43d0000d8907851544 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 708137275 1250 708136025 708136031
    0x20c0a030c08070b0414120703080304081317100b010c05030d02030403090f14040b0402040e04120207060521090705061803010507030c170417070b1501020102160f030c06 75
    0x80303061182509560780500d503001d200f5060002041030040d021038041340d0751007078000c0c1d49000c0c550411880402c5481f00c54094425034a0201c0400d00340402180950b110701084c9603601c1c1200203003542594103a00890070744245070060b056000001c070b126043c071041541d000402c404600f0068864907034a00018143d80300100710f941c4d0303080a9600440c0507a000341c070b80d0b1445581e901281000074a05010b181d02d035a0200d618103401d400d00c0e40000741e50702e800400c0075060603103c11002c02120002c40c0c040d80d03940107500da25030340079405010700c03070281013585031461400d680540c0240700300304258007165485085000041e04180248182d101400c03000300065622044460f0909207941400c809903c02e5207002c010443c124040c3c80384800c02820364032402d40790300b444102c1d0081c0b90001807003076a242500d03940302d10118003980700070300c001c41c814000101c4d1402c00c082c0301800310240c210000d05680c4100501e514590004460030305056000031a1103c40f012440c04817007281881400803e0242 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 708138525 1250 708137275 708137279
    0x1080c030402131107030c1103010e0a0303200a05070b07081b030a110f0403060c39080a17010f0b092202030f160311190c050307030804170309120a020c0a 68
    0x140c007c505520f40c90003074821001110250007014200c03481003c518500340c1c04010350f40c0000e40240c00c000516405190000d441e81c8000241c4c0c06240e000d1400031000030380018210040001945805401c0002c0c1d144c08030711b80ca8034404148411a02c260001c1c0030344c4004c4002000035115030011000000c0b0389521940360070780614106180c0c0c001e4002168814204604409106c2c401d5038034030310507a03041d560450b0710340c49261888040c0c001850820761002130700c40700c0c00100311040024480d000d01540c407100051036000301c3c1022280e040c1c100d01164107100008210041114081c0c0c0e15070704040740d440d80380c5003004005c101c0da01c140025800809001000300040720240b078003014030030308200c00400000300001c0c10490807600810752401120307400b40502c030414064015049401041410a50841005900d4107440e64016190403030000e40030380704100c200400110785150100d003600005080d8100f10440d11345802c250350081501042c0401c001402a01c05c000c0400c0b010000703404804815 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 708139775 1250 708138525 708138527
    0x4060f060c02120109051f090b0f07120203010b04091509060306020909150a17031b0c0a050d0308010303050d0b120d0f090e04081612051801080c03040213110703 71
    0xc29800740d229003602d16041d0186a4180500d45c0303110342c000041c3c143d03030034400116190105801202c810b416511081000002d410b0300c1c0e414040c5549a00e0140a8607103c00d000380401c2c00c0205010025005100402c20304440000707a40540f624200040b5048981100c1a510001203030b010400d40c50404400106005581e4000e110fa1002680d91160a5641e0180800003100400703980d504011042020040c400282c1c5018610b4031550043d203241401554044d2510285001b84c800c5a4006c0030030030100c0c0c80e0540820006150541d0000302541c620386000d840c64005201c080e00348040043d6042c0340c028240d0140d103520800500c588203200c09420141c0c4e481c9030900e9040045541340a241c2e08a50046016a0454030360303400c0c04051380d81342e41d80c544240e008901d01903420f210100da0f40c000600f5201d0f4501031000e41e0340c0c0d003e88450710000100a44d40311480c4103410b015003401804001380c0380d0011030b0f0b07216030180e42c403d00c440100442e141c01441142ca4181c40102c012407010105 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 708141025 1250 708139775 708139787
    0x302120703020a020106050f0f3705180615030c1620010503060a090207080d2306092401090e16030b09012103021005071214012304060f06 61
    0xc0301513070007040500e40300c0b02030004094101324503641c00040001e00d42d040e0b1801070790032078080f840030307000e03040c0003070720050181c0c00d1402420003551100202605202a00b400d4542108091112031100c2c403074100309012480c00301040d024807800c140d000000038110304810f4100c4000c41500c42c01070b00c821049084c800c080c201c6007240d200b603c000a400c8403031258491400d0701e0250400400019450f031800428a00a50021404660f220f0003440404e04200540c85070012000d0801c1c1c01c0e004c031500c00389503001d8442d8020201d40c07007005c001041c41002c20b50b0032132400f8a01405108050100010401170f160020641e1200b0084802041006414402c480841804101d0703500c0500459000c4010095224002d002c0c0d440d06842d2041c1d00b0040c0d150607001126003e020740151062071410034605000c3d201e0445003000861030410312035407a41d8080c4100c4103840354000c60000c06506064060f03800b4241d1000c1e00d400e01c201342c03400c00d0315981c4588c82000103022160411840326510b034806045 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 708142275 1250 708141025 708141037
    0x90103140607021c121d030306010917060403030b01050d050403051b0f060f0402010908070605072a03140f03030109050106030c05070b04020108130b1305010513051c030212070302 79
    0xd01d000d4240422003050001a40e050f03005080a075850100b40c0458045030b01c504a0020800301d2030300ca003130140304421608802c0c044160100301070f5581380341020016007149000d030301841c40300307200b88890030300300e003000c01c80c5504641d251802061300c00b0354500423180c502415001050891418040c003007050b42007401403480b010000d8002c00d0f59490030741ea05446070001944620700b5080346000444c94101c0300642c80e0710900c1410600852034940702c00b680f070000b040d0802004203500240c40300c2813050742e520000121490501c0c1300d041c540300600c14000c8035554400149001421303440d2504488003072080c2c52101c00e904080760303100d41c1d6645500000d40806c0c0303d210003191814103944003452141084810864000409050507140c540c011180124000c0c186c01080810640c4440011b1400498501071006101c43c1020317010282000c03821100080d00a1003103003144a42d60300040c4020407040004c960121301da1024101003141600a4840d8a00440c0010158000c107c0c109030590b002c0d00d0303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 708143525 1250 708142275 708142313
    0x306060305071803110a0807140a0b09030c0d02010e0301141009020406050a0c051e011406030705010c060b0d0203010c0215090318130e010216110901121b05090103 72
    0x108075224107800742c450f248031000184440c03401d08410310100e40c1c1080105400180585048005a6500d07425802e04c8110b4005202c82e0b40f08415074005460060710500191041c1400580743c460800b0010740c2d81c210300100d040c042c10828400e0010b580c00b4940c4ca508a0b24054001c2c07205800f1a4110010358508840020f2484042d0707034080f418251a100b81c030141c45582d00c6071450300105c8038065952400000701143c0b142310300200c602c032a040c4c050070006c80c0da01100001c5010f081010070480f80500062081d0b0007640f01c00c0781081142e030301200c040b18503500100c0005d1414003500c0424050050008080c1d019801c11403021060359000402c00c003642c00121512070a40c44d41140b071601c0f845804413000200c0e010307850031140c502d00064500c24902060b03000203071840d40c15054500f0781c2c0240d507100c002503043c040802c00f80020703111103201c1d03800304450b214419070400d0744070108003034182809044c0059200c0c402c05102890b0f08030b1400f400c0000c0c00e1610542e540e240041d90107422110942c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 708144775 1250 708143525 708143531
    0xf0c05060d0c02071e0e0c160b07021b1528170f06010c0b1816090b0a03050303130203070b0313110f0a090e0c06030901090501050108161a0408030a03060603 69
    0x10110114051a880d524400105c030a07001e1410740d440d000300d0300c0070345034801043c810000029020b0070200c001081354410440d070350044c81d080c04081e0509150540c00d00000585002c020201c0e61101c045250700c14140400c15207802c090152081c00000c041c60a044e9581c015002c0c0100e00d410481c032000b001034580b004c0500b5a01c2c2c0401d02c10704101524401d0104189000e03403400030324070b6140b65a003d00b81800602c1d48404400c1d00c6403070810399403c017400d4103100030310034001c0e044140158203030041c0c15159108500c1c915038a540c0d480c88014580060303002d03ca49003404554051042c8070042c000c40392499102e050071080c0c40030090410304110b40c8000c0e9042c0644160030056042480f421004251070000c52070096443c0c0130703150401801c14a401003401c100003564950b070245000e107100900029904600e46000360840790103030000c04250340400c981c900301201d448049070948000240c000150181ca81071050b1500440d00003d03414040400e82c000916030540c40340b4102c8010356018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 708146025 1250 708144775 708144779
    0x1909020a140c07082a0d020d060c030e0c0d0c0b07021c1a06040627021308070e090f0615031005070c0501051b0f07050708070e070f0201060605070f0c05060d0c0207 72
    0x10700040c440c001c60f081810060b45c00c0d1070740c05140101003802c085001610401c610745642e0395030700440300e0584050020959a40503c1c001070020414030229420030303180011740b4005d50303c0d200c4000000303100c0d044140c0300000d8840d086495a0902e490790701140c10021042040c0b80c5010088004542e2100c6521003101002590300d07c1c03e8010f20040b914900b000c0c00140144404030f00e41c0101d010a00900c064003041555a041044003030341004080f490701030070495003084510150044040c4c0740810581c442007084e2030307816010500b141c10075442048420000d0b044408642000701e40e00e0300d0b4000d1441c007000c20400603002451b56205502c0f8000030000d55450380040d0307002d080b0540d03051206090500c4802a5401140c0040c20aa4080c2c1c04858072a681c407a4a186891610340200389070390f408909010303080c3d400421552144c44940002d0101d181810001086400f41c00400740080300d851000030709124155101394050b110180510759038542c070340f192901a11180b90100014482c0b80f0780 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 708147275 1250 708146025 708146053
    0x1809030c0c04020f0307050a0903021201021e120c03091c030606020f010c050a030207110406060c05072c04080c0601061d0f0a030b070215100e061909020a140c0708 72
    0x220b130364031035051040c50b08589860000703c480750001445003051121184001c000345c0d4450507020441e081c03100004d030707903203800700c4510541034018410035482c07841c18841c0300c011071019440c0d41e034058a1140215141e42e01c800c041494240e03011030031144850003451500312a54560410303810f0392525002c6885041b09c0102c0d40b4220b454081178000042c2040c000d40060038840e400a107019030054400c20000b1294000203001c841c540c0d8000004a01681032401c104401400315200401d803468010029502420468070b82400e08080303c0b209800c1c140021382007120300001c0e100b00c446000c0403901c0c41c0d0707110200a440300301c085690120111030140050514607003074080c1c0f012502c02400b03090302d1070300c0d540d910302c03c188c0c0c0945054150300942d46026843d1341851811071280d0801c1044842c2c0740e20b0b00700555200302019080c5070013a1000707094060b04020f00d0aa0038101c40c8107400050744c0c0c41d207002048581000c00c180d142ea43c180300086121540400244c2036080c0c0e60400d0590b0440040410707 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 708148525 1250 708147275 708147277
    0x1051f0801170c04240b03040c15030204031a101a0412050f160f0b04080316021212071101030203040510150b0c0607090605031905061809030c0c0402 66
    0x10400220030300c0c01404001100100c0d099a00d00c1d0104031043c4946950018059a001d9203048031500e90300c054040044400356040f20040c9660185c070b0f45182015101d81c00000c1141c080c100d00030782c80c40034200e041c0c1d2007030381210015030704040c1c150003071894038070801120b90090b0756400244c0515400420402c07540101d070f050b90901000c440c0e29052914030391494060f000d801c1900c40380602007026128030002c0c0600d5040d407451030f0b08040d085081c01d01040004200b030b04088100314042c042448074080000850302c1040c2d4240000182001e54400034000000d0721f01d00d44201d000706180420500f01c054060044117104401c60301160788500011070490008440203015a408141e460955039050343c407d07030078031080c0e0091020260b03c80038081111785c016810100680c0c482c2c0c040040041c0d125080401070481460a2031460400c507280c1e090030b004195828801e5550764022601c1e564880c00d40d03070808004074603690703130915140181c16180e8000d5219802c05c1d008041071110b00e4074041c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 708149775 1250 708148525 708148579
    0x190f06020c030d0e07060e0108060402040306181e0f140f011a0f09070212070512040b0a02160506030610030f0e0a0c08060702060403030f0b150c010b120c010f020a06060e0105 77
    0xe9220002100202c7c01115081405082d50380c0040e0f0800000c000305105c2c0c002c0000c58080050480002031061400240d01800d201520500300058010707500002c06505861040e1500403210170501101d120704c06052502008250109603c0d094690a0348002c3e016810b10300340d400c07102403126000040038050410401c50f0003600603000b1005c0c400c1d840344084003070014140500304403045413204030481401607002c0d4119010000c40451881d00190341003101c1c43c2d881c3c11098030100318030319200c0816818003001c0c10451203804c8000400003014403e0340181c4001404c0102031000140c90340c1c060303440f04c3c00240144e800c0c00f4801404a400e604c00651503010b00c0055008107170f15516502c0480090903a41e0b45c81c6885900d03800482e65941d100160b480403280d114106503528010b9540207400c43d003001c4440303400f44410742c107920082c082c040386050780d030751003801d0020b01d8011200041342056440300700208101d28021000c24801b0008503c3d6068030020b90b80401c1034440440c034404080480 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 708151025 1250 708149775 708149777
    0x80d092c0a1d06100e0403020f0a0c05150c070504020f120408070203150f070f0e100807120902010c080703030917090307140f010e031221100503190f06020c030d0e0706 74
    0x5204c00300502c14841c6016903200d40241b040da0301c50320501c04490309015218a081d51030000c400e00602040c501072a1250705049071b541901e181000c40d24402c0e40b00c00251084501c55603000c201c28030050203100403940fc1484030482c0010350714041c6807600880c0c01c1200240d0080c0b145403181d5806c142c0d0f4030b40c024013404141a1403103245d59072103003c4032a1003055041800704061240d9040c404c0e02c880d90200ba149010742c90310140340c40d01100040c040b04c1c3c041d9036142e00900384020344000d07076007008000c1825600300003171554549180c10141c01403c0e00c4407000300341f00d541181e501c40ba10850744c00741c038046c4070403070596040640d110001d1842d5905003918903841007420a19407960742c0901c100c9583c0e805c0142c1a1841d01c100c0c030a2558168014901d24024101201c40c2c01203100716170003100390301c11081c81c3c09074040e03420030021079503510301c4078004049100602000b1050084054041c2e68050f8032640956407900d0302419607440742c20501c04101c1d05420064034080c079600100d4900c2c251005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 708152275 1250 708151025 708151051
    0x100c02061009020a0804061112180d0f2705100c06060504060e0c0d0b06030a09050118050607050a05040f1403012901051c020301031209080d092c0a1d06 67
    0x380c0e19140002c0806003c0266010000c108078000441d2403480f0a00c99807803610134003542c98603142b40300d082c60318400d404010041120002c1c85503640014407090141a800c1640304154610040c0544007980c40d0031042e44045400141e4850550004601c900c0c2031080209000541d40c804c2880705482c07541c01000002c84030280000c42c00c028031805403e100159140c041860b0750100302207062907000f0343d0140441074a45180c0030a014090003084035071f98007004908407040c0741d52281c41e2222409050384042280000e404d407450303031042c1c0c280c8004e403d56403c0702c0401566505030900b11540b40d2022400f035400d082d00301c64401044040e02c01c1d0f031061090600c6618030100700441d4640d2010340700f02074800c907251110203000c0e005d20146001c0c62127020710003416041e042015204010b030781d100d4803da91107030340d89007100c582c01000b4500712565004038106100358054068280011843c14094450044080004d205840c2e08134441c0090580700469a0601d150b80f440e0316a0310484000040c151 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 708153525 1250 708152275 708152281
    0x32a0e010b280f1b060606080105030c0307150c02010c080406030f06050913020f031603082107050702010c0c05090907090b04020a08012c010803070201120c0c14100c02061009020a08 80
    0x1016050b500b40842130540c0c144584429540d6403c219031503030304404005180e40c40140081e0a040051040662046000b030803c0c52502403450214203401902c4030401030195051030442e40505251100d840c2d0110381d480d16242c613000028001c003100301641e41c0050800b600010075051546065020305101071003c01010302580a2251b1401d070304241a816201da0303001e51060324603807001900510f1113400015944c0e0001c010f50500b4ad2006e8010882107003980081c00b8031142c00c4811a00c105e503082c20100810340e0f04d4107000c66440281c0d8069900100c80074104035000102042e450191030407031204020b18030400e41448128025400854042010700c00140000461840300c201421b80341c40158041b42c0c99112000803108007030707120159903031022581c03008540c0c120030300c40c0d12032604400030000350038814001031000c0000c1e50043d10b150b070307170241e041150b007400d0004140600061005122103013103240000d40c0c035441114201032140b15207401113080c00407802241c445044c01e5076200b115031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 708154775 1250 708153525 708153527
    0x3030601180f060207080f0102030f130602091305040b101208030a0603050a080408060f0c04060c02040b0618030f0d08180705040606030204180501032a0e010b280f 72
    0x2151008201041c8100860002142e820605621015007400c0c1e010b40340151404042e0f0349413188001c00d000d2a82d00500400140241d02409a170340308420070a00100c066171420a01c000344217a0766650780200c0091a60644114613400c03090080b48604a1981a80e444051fa04e842400758010003420040000c40030b000b0554980103150401c2c0700d4400007981d540d4960704c182c948503a050040700c6884000c80c0801004500780009648001242d400c034046140403510100c8034441c038000c2c0300922039810754600035501c0e158401c800b0003402800342c0d661081c7c61104c81a541503d000098868404c1155010f00102c001c54a212250a0f645548503a600c0b85d202000b04114101054500c40c420004002420744c0d0b00e0003104004c007050b8500595071803c0110045440c02c9204034001d010b82001700400014150420705000320102038202c46440c41d0045407404c2402441c0d0083c4000c6001000100d85141c108009140c840250070344950318000b00c00c5803104042c801c0759804e02007200714207100d8280d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 708156025 1250 708154775 708154787
    0x1e271002120711030a0b091507090b0d0b0901090b031207021f1103121014090f0a060321031b140a300b0301090b0a0213030c0b03042303030601 63
    0x69100c0c818401c000c809900110346001c2440c0c9040d9148a650746c20711518080070b200c0010501011000300390300d07103451203005c0c210600303511031b020700c08000141950400d40309a0121441010051802c0034559540700f00a0160070b1030160540304c3d000308504001e01c16180b208480c034907540901080400002658120380880714400303070790b00340003288000125040e01031004001420b803d0407810035908003000000d03900d0885400c170701748500405e0820002c40c0d94141010342d00040548090007150b5500d171100010303018a500042c4040f468582d0000d240f818010b2180022506540c10030403882e0041001020105040404003c20340660188440346100c0e4024183c0100710b0800408a071484603601c4403144291410034607001d000300c0300610804140c025420b6040b4110000e0040c0000c94541c000d0f103a07005455440801ea000a011243c0585121900011900701c15106c9809070346402c0c5840d0f80d070040380e080350021044e1800c00f0380d01c21035044140c0c0c207441c0c04004505550321000103580c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 708157275 1250 708156025 708156037
    0x918050403030e060906010306110a02340603020d0f11040b0703140d0911010306080309012001060803030415021c0213030c0b040e0901201e27100212 66
    0x2050345443c50300680b10000c00c5a41e01640300351000300819855030400404640386030381d2550618608000e0112500e5001130585140d0100010710f0f1004403061401b16440d07032264140121442e81280005180ca03015801b82107a403038100024040b524504002c003007182d1030b07102808940f11040c0000c0c482d4090790005020300034800d080040c84083d005000000d1a004503100d00300c8035072184803580801082100d4041c3c42042824244280e03030520386115100c2c003500c08482d04100d0b85101406040005880703100305400208020800c43d034540381d034203407680d0040b1015078010003403010f82e2102014500c21035004407105034110303801201506c4408041d600507400031041850100c1c000c004a80c0740048803000b000300c030a610382e03a14505a00d00040e01e000429143c001d900d4030041401358166802040f6a6240050b501680c600c80d0740301a1490950b0303101540742c41800031544041c82e800540d1400c7c01680000d420014584030401001000366008803a40c005130040f00103401041200005851 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 708158525 1250 708157275 708157277
    0x60f140915041403060405030d1107080c06070912050601050f1216082b0804171602040e030c071707080f151602030405010f0302040b03130b06010918050403 69
    0x1140003050000502140c50101511001c070780d0004040100b004011890141a030007980504400d1070507468850304c83c099075005a044507183d14000c41036045040c211410b8a030302c000c0340b076120300e1214034480ea034402c2100e8000229103600c4010070001d103070f40440b000d059800390040c029607003400c0900528181d03078180d940e048044c012680100000a0111044061100303d03c0760141e89400c010170703d8a0119150b01881041a1005066801c0000c040940445190404440c03a4540f0324240c1c0f82028010aa03010154020030081034440d030b240c2c00c0124150084500f40584030031401d11941724413071411412441d90001404001c044140d0303c032042400d440d0340c299072801d540d51840b58140111880b09401641168042c680715848802c16960000c3c80c05020081003070341408040d47e64440c60262505003e0440ca480c2ca10314842d030102c1d40584014100c1c2a180c0c20841e407942d04d40d050002d02240e00c1020040080c0c1d503035100304807410031500d0800d111814040c1d059002d50051102502c154 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 708159775 1250 708158525 708158527
    0xe0a05060103150615030b0a051804020f1804060501050a15021c050f1c050a09030906080a0b0a08030a0f050a050409021c1d10060501080a021612050408070e01060f14 73
    0xb4003000b20600405c0880d004e0b88021640340e00b80b00411030700d0105a04a0740c0306103000284440400e034004482540b00b54150f0b0011844a242030001b124126090200146440b80004000404c1000c2d008241214029144000b041d52180c40210210415216010041e07001c0d24074050301c4001d080d40c502000c4205d0602a240081104203149154800c00300c4050028502c52442003803961391250a5208260000c20007842d01c0a58009221058900c1079600b00004100032402c5080b0039440702d804080f0080c510f0141540c0d0b10b001c00d4a94100442d0b030404a6102c241903440e241c02041150030000c0c00e50703683c0f840c00d400c00d03000100a400900513403203400100881c20810285030301c9400741d144803030765410f00380c424402245481d05190408015042e03052034030400069070000003035a00565000009a2280d40341008004c0e620f1402c00d020f080c50380088440c0d04440d801c000103000b6156250207851405072031b1450390004a40078410b000024040400c1d41c01d001748200c0c488901d00700c5500c1d0030703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 708161025 1250 708159775 708159779
    0x20f0d12170c180a0906090e0f07150f030e100b0f0109080d0c0302030d020f09030f01060b040b030624030910090c17070905190c020a0c0e060303040b07150e0a050601031506 76
    0x3905c1220303542d42290071300580d6210070145815080080c4c56410071031800402e0414240310090700c04050f45411002400412071070000d40714040e07000115000b8006044038040c40304007840002403d03064110b2401608151020481c6503c140b5800003500c0c1100014024030456160496240458407015021400113004100f10070b8814001001c6000740401103d40b55414601014140200c80340d4051190713241031010480c1082e440305440840d1445250300d51a9074a00010450612400380311aa01c02008950b00301c6100034030000c3c50203020100201c0b5080400c1140c120110713409050064510103074000c040006000e617840e11102c2d402090192035419944841384001d4400070b590b100950210302d110100c107040c0511603907034038000610040c04403514503142c89201c55210301039042c3c0540c11000191003074078108103c400405101c0d0b406503440021782403410b01e030b00c005c0d0075608046080a0b00d1800103080002c0f00340703250b50800e0280885034650360321628a480401114201c130781d1542c0700 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 708162275 1250 708161025 708161039
    0x1120f0209011b0b070f03090b150906010206090636060a060515090f04200a0305070f08130507210b06032103060109050603191d030d0207020f0d12170c180a 69
    0x49c40d000c1da402c812184889500f4404204100344010700e030a0455101e4801c00002c0b0f8000118103412820340040404280380401c842c08852241e4080f00c003940f2040b2030750703521001001860a101c1c2689a1040192945031010407001c900301780c070070506565060140d110203151183c0c80c10000400104005000041c010000344403084102107a072001d44041000000c05d505070180e19840001ca14040c0009440a54041c0c1010b0001d407400c500460800c035290304010040001c07030040c00030a4441d0080b0285052511840a0340440446003020954080350340e904002901072200103001c6525040802d1520020910390001001e16041221070b40c070000b07040e1a48401107014136100400c4101d05110044000d054825000e400c0c400f0a142e074586095498000c03081d10070b070303902c07105015a07141128000211010a05800c5651145c00d02400d2810403c0c100b0100c032902d19640c542003007069440600c5008407008031550320200104226180200400d904004000d480041c07641502c0354036594 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 708163525 1250 708162275 708162293
    0xb0a0f060b0a080a02070f12030f020310031e08040608091915150b03010b0f0c03030703020901120501060c0206160b04140f07050a1401120f0209011b0b070f0309 71
    0x40201e00590300000c54600b0194050500340c0e1104e08000d05603d0241e155980311602001c18030041c010300001c0744541a85446a0004003070300030311a070290340303e08000b004c1c044000aa440211441164002810003100804016188071070300100c0507410a0314101050721480c40044c8440c40f180141c0031800d16030300c2c540039a414041e02401c400091038850707d46900841d1601607551130f030340c240c59608010110380c1c003084906440002070200c1e01c0e54103a203131003003281c0640b0b40e92a000d8000030080003040350f455400781840c00c5d826a0fa00c401c50700002c0c0810100c450a010741e00010b052200e03094054280f1000400c000e0741d100340383c0c6103641e2440c0c4451403051002c2e03400302c42d80003581c0c0c190429540c0c00c104204139060103c018000c280d1a000004285c8203251241d590440005803007560640e01654400c10074041c1c80f130040c0100705416290308000d40c400700025000c02c4c8141e0300c481c02c0944070010341c40156404841c20a0603183c030030041d05c4240e81200034408150703c6020f41000203100342 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 708164775 1250 708163525 708163529
    0x190b130e070305010302090109020304050a030e0a03061d21220909150606020c011205090a0506011706011202102304030c030501050a021315051b0c010201050a0b0105070b0a0f06 78
    0x240d0000f40650552040004810060744203082441c014818800031400120b401c07a682036050501342a20280900491080412a40041d04040c07410304d1400c0d00c0031652080c0340000844200b5903403194100d1100c290140d0022021010000050101c44c80e8012039500040340c001c0c10006044403980e803100031105445800c0402c035058400a1000880f072142405580701400707860001d800001d0700c80e40020202924501604403041c1c849000ca1640b61092041520311504481612a150f8460900420f140c00041000ca0390b441100000281038580954000c21294010409140c1e801d02c03003070032118a4480c400380c008400d13600d400c280d500c500c1c05000f00004c61051280003551841e40c1040fe084910007445941903a004000390070b54550712191400070303115414024080321807440002c9070507002d0b4a805040504000c078401640a40000d01441031070000d82c000d118950b10221b00c0c2c801c4c5c03400d40c4106030200740309009020000d0b01d1140361a0344445070100c00100300800070f030380d9026510340c0c3d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 708166025 1250 708164775 708164777
    0x30c090e01060807051507170c0d021504030e1e09011e0905010b0403080d060b030f090607110619090203010906020a0f0c080a0309060209030a030306080c190b130e07 73
    0x109901494a0400e000310001031040380040d1074007903d07003404070f0420312000221b0700f240310002070000100114140344888282d1541c40341600c484d00228035540e9020182e40c00005031185440c3c0345641003e80d11442d00c215495078a0050113080002031008140f41103003046034181000c0d01210720b60f16404805402407100c1c0302240340b0040800c00c2c2d00d00c0205141c20541d005810400140401e07030203001100c0440c0e80c0440782981c1e81c5015485d0342d005003080d800c109100380c400001e102100031f4901c07a560080c1001c0b4140e64080d102c100c400c5d03c40000c040c140c101e030380e00440c00281d030b84c0300404c10400380d100e44004003041000c91680000d084480840084540b168080341503102541c4c010017203900c104050070314141030319003a1108000350080042410801d40c4520b50310f000c1080607010740b1860030f0040d048502e012407520b00030340682450b00600c001442403c0c02120140b0340001201c06210114440b8002c2c0307801c180300040190b00500c80521014081c0c080000c0301482c88500070300c00c40403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 708167275 1250 708166025 708166031
    0xd050f01090f020906030c0f1303060207020915100305090f0616090626280e1b01080112030c0206030103211119110a170c0d170d06030c09 61
    0x406090708115401d440160440718410300c00704042d9190041129000542105001e44400300140d0845140c0b040c02e113003c40d84a15020f00200b08005600a000441e100302c0701c11007030b40c1d9080c0d0954280303804840496448401004c400300d0047c040c0e800f090700003100382c0558001046950b051860841c041d2052001c00445010f4040180c1e032000014016068504d80700c000c402c2ca29040d410341200c0e1540b41c03d46c0c101c0c1203005ca402c0680581800f02d01584aa003d02c6520314019085002001d01c01041105802281042d4a031003508005000001c1c81c140c43e0300a007a42007054131000300040f8201182440440070740d000240e5100406236009501c1900034654101480b02102802040454242d0601152100b20140f030b14010504001005410807103038902492418205004c11440040d507402c60390115000c200c00d90000c541e00d0031800c810f811124084000418881d07029007208014002d82000c2c0d0801c0c007981c07008401000103010f55a40810807035142c1c0c581b0001000c280c4c4c054840595 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 708168525 1250 708167275 708167279
    0x4061d10060504141b16030e100315090e030405090f01060e100906030509072408010b0c0c01050a050d0f0518150a0c051611090c25020102030d050f01 66
    0x5001c0e901c06400240c400303001c0c02d65a02d40c000c0c032494014002040c4030840c004441e4200da8404103a407100d40002c41c00325451541400e001e091a00341403551801848034803502c403c114021f0150001400e0303c40800f84c012858005032200a03d075244411003e400304000004290b03484c110385c94000d502c01030801c100b9514241300a400300366042180c501070307211240c0e9a1500340c0c1248a20b01101c0c4c05083c0403d05a035825041400c2c01d8450b0000305900c3d40100c010140c0c240507005950610f0b10715101c80381c0d2030340c8a9052860038020820341d40304581c4200c40c412441c1d403240020388804441c2e828011b0800111120801c103507020701c6009d4080079950340c10403d00c00341c140410b8403c1e68844010b0114141410f030b1522102c03000404400c403050f11090050021885030080b910b00444981d402028591a032030101c246622a03921030348111119000702e011080d252007120110340c6c030500c40501403000d2010600040b00100030590641c00140f0890082c50014000c041c0f0410064610038601c0d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 708169775 1250 708168525 708168553
    0x60a0201090b010603150f0b0f0d0b130f18050705061606021602010e01030b09160903020310060f05060f1801050408010c0309060e0f0705120f1506100804020d030804061d 75
    0x2411a80460070710b080742103007000000d08000844100350274404810b0341d103285040780c1002402602415071303007010010300c0b0440140640ea201c800e05203803080c0140406084040c41603a181030985004d040e40e00120000c000914080005200c46400d03108800150541925000e0480c2c00420f00d0011903e11240054115a4018a440082d41003401d0070071031114400003142404000900c81c00306040b0400c0c02206180c00750100e10000c1d98010f086440780d00004403000081c00e030303d100d40e110305041104007041525012050b50826004403e80e141820360101c004214561440713150b0b0b06100d810000403e1008007801941e038280c4d801e850125490b51903240c080c0480c1c00c00086031055401001d00e40304940000310740c0b0811500100c4d41d26655055084407217003406514601500188540d00321902801e4030403404610880c412a400040b180c01008181c0710001c1c1183c0080d4814898121100040c0c00340c16001e400500654002841700b4520080c0103d00070745015807441e940c05003151a18034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 708171025 1250 708169775 708169811
    0x3111e0319020f010f2304120309033810050d0302160b0f041811070506011502151609030b072f07030f03051201150201050a06080309060a0201090b010603 68
    0x6030f08207281c8801000c400d00340050254150380c01d0b407240e010f52001082d901110f110283c2d4003401d8080304040b40710380d0070324008d00300620314441102d00015032603054041102c3c01100c14034821542012001c04000e00e541100702c00c000400742c40d86e00102200206281d124103030701c0203550380319800501e9404004030018059422030b500c20200030340100030000c0d58200140584007111070f02d4005520340c0d00800d5101001d00b00f000028504610b0124405c3e0034000c00137003c0341291181040c00381c032400000001c076211595289200c14416869010a203000385100c1c0c21051038409103880d10781c5984a907514040704200351201000a59038803d0700350107074070a5a600b0004040c22100112441040c1403407611504130303100150021214402100505010704100c4111903002e070b0501c01c0640e114040102c58038600800b5000561824000410b0b0742c07031910895050700d00b0000154180150b000412105522110303000c8115500c88044a000901507140b582c040d14140e240400c043e103424400b9109 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 708172275 1250 708171025 708171049
    0x1602120f03010e1014010e010c020d06060e011403030a110c0d0606060201060b070c0501050a050f0708030a0e0a03170a060803120103060e0d0819021611091003111e031902 75
    0x144203604a041110307400b0401117004190b02070a100a20580400c0140c880000302100a50420a030a80c200c00b00039242c3d10a1040d620003d8445000c1d0342c980244e1111025070304a10f6425610030414400e0160240d4070059040c1e007181c00b01c4928061080c003003140c100c00c2010403600300b074540800b400016020b02500c4003529003072542d1800c000b4a071300d903011510f003248078545c1071110001d0f000c40180d00c00c00c215090030301d0001e0516596907080c903141c041a442192520b461500e8a40d000003400c80200302d0440c02605941d4884e110180c00010410b14000a40a044603035542e0900107028501403020380603051584106441540c514104a400d5a0b440007071500260810703c16614a1a0050040d80c4c001c0f1019160390070a00c54010088000c1c0f0880c6684940548000b00b0b8a04200c0f07904500300719007801762100001078030f03030710500f00c0090514000144004044480b5550a00b8440c45800d034240c2d450b0103040310b030200980424242000d1150b40d00c8044009401582035042c10200703510 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 708173525 1250 708172275 708172291
    0xf010507050c0307080d0b0a060804063c0f0608072405030a0c021513060e070810051314060106090b0301060c06020d06030503031e0a050f1602120f03010e 68
    0x45000a11802d41d80c891184041c0107120707200120310404c1c904015400145007000c0602104000341e283c02028007541d81c100d070101c0e001420705c418410361304000814208601c500740d090410404206800c1c20032059801880c0c01842d030f0300c200d0040c10074101e01400005100c940c015001080c00c10071041290b5081d046178100e4060103114695491741e01004482d40f00c0c141c0100000c0e250b5a240c8202e041c01c85403d001c80c00c4600031424044000e0f01301d4000104584903580c100710003060807000a460f00b400f445404441e0300420700c020000a00c0f90041580040322031020064550b066032868100c0800840c0d07500c1d10f902920060000700d0b0800d4120000d444c4d420000c5040d585000802003080040302c10007403a1540102c0e641e0030060083e00150003550340308003a0303502c84c40c107c4411101d01c0f4a030303175075038403c1c054080200b110341d01c075807084a0140c0c1e001e5214540355950100d040348102c3d030700f40d5800110311440c003071501c24290f95005810850061b9802c550780754942044066030b07450243c1144 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 708174775 1250 708173525 708173527
    0x215100e090604020d030c051204030305120601020a032c09090c090a05010e0601050c1e16140a091104030b0f04020f030d080610050405040914160e04170403140f01050705 75
    0x44013507916400c6410075a503162422252a111510302107042c10030302d24100d21381400c04a004001c140c2c20101030040384141100c1c0c841c0f00e60302c003001241d03a8100e643c40603003c20100007075500c85c0d90f0522010049001c9003510210718800780c9011a040d041c4c21204084603800400b0885a1807a02d003490fa50001c110b1103081c0204d5040c060310740e9010300042e28041c14000c00140341030b0740d01d20500100100c04001580c0e0882c02c03015003007140d1900100c00101014000c01ba00108031284108800c0c01d0445000d0150121103080c001c4e10300043c5440068084101010312000000462842c0c00c10700c204881010700d22035040034818010041001040580b10717400c400b0702c000809a00886958ac04101195038980c0b8000360741d81030b2001e2240d034007e01c0e0040c0c1420051380500079140d000b4051105c243c021a403407003055519900d0441c056005031480e03a16000c0114003c5004051206c0070b1210071007440e45066543d43d034110b0402820345c0b1500e074503000b104010010340002e11904d80c1c0107000d802c0c02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 708176025 1250 708174775 708174781
    0x106090b040e0429010e091203010b0d021201061d120a0308071e020705090901020f0301120c050d11030c151c060e0915091606050a0215100e0906 64
    0x324660055000d402c050706103040010b4280100360000ca5441c400030740c8050900211140c0d0408048002d003d100b40c0e8150b1103000c84c50b001400144462851040c52103c0c1c116428410203011561064030030b0400d00340c00b400b00c1054000f40c04021802025192100030080118061840e812200d1024482c440d0048904100004402107604000b2a51510300301102d075894140c140c40400c000039100d8403c1c006611103018550b00060806e01b42c1d00d00302c90490396a030310402203500740c1c801d0591510601d0014801005600401e25651244920413440380c0200364440340441d903040c55011013a03a6000903d1110181e0f0704040c410050303503641c1580c000b641060602d0344181d1500c1103101d00c80c802c00d40624004802c503c55800b803006800240b003000d48a003007071581c0d19a245e900740d08507504443c028001c2800dc600c00101c80107004144007139411044d1a0240517a00b0f904211900820f500412420307e000d8100c030100c9620a1a81c800701d180c0c1c590412a14140d0140c2c0200071464030341c440018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 708177275 1250 708176025 708176039
    0x30903080103021908061603110301030f03080a0e0102030705210106052a0f030307020d090f05120f0a0c0f050a21140f010b01031b080705090118090203010e010609 72
    0x320a054079010344500445100624000050300c4143e8000c003401e0042c0c40a1100108a103001160010115a01403011445140940781640b10a202c001c0034510803000c0c0d440002d004206803544072000782c80004500c80d8200c0f405003a41d000b100c081c0d00090380007400d8880580d14650440e0f855003005181126513041c0b1380c000d0040d00c030388030300480340803800710040403103081c501c071002c0310b002c017960981e00d8030008484925501c2e0815512013002d400790403a120a40c91040b802c01d0b0448241a101b880480c1c034000c02d2144600091032004841e000d951110a40003408120340d102c40780c802c00c12a1000c1d840d20100c2c0c0003d0141c0c0d00b04900c10150203804200c00c02801120b080b841c4500102c4000070740042c50f00020b003510410641c843da020f10048d01103844010740c4203141001e406c1c0c07070602192301c00754030442c14240c0406003140416151008181100c1c8200051300d00c1c06e0301030400c810b40407032600032070000d030200d9070019501540002c01803010b00d0030000801d004040300d042c855440384c02d200d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 708178525 1250 708177275 708177287
    0x1a0112120804030f0e12030c03070605130308040609080702100c0b01090212061207080601140315010b160615030609050d0504080706080a1103090a0b0f06211203180c01030903 77
    0x5041000040c544045c11682c518840d0440c00c8045021280e98106d100442c503201d030403e83c42942c90382d103042c00260103078065080318051136526a4580050740d885035a5140200420780054418280902881c03006841d51001007566003002d0f101c402110340c4a20701881e0050050f000340b401c2c140144504214007081c143e1503600868129480b44a00105880d540d02d8441f40380c0c40742d105485060000a41c0c0d9200150840e846801501900c05043c021160240140380a05c03490a20300740170840002402168a80420140d00c100350124140901e40c4e951030814042d5001640e42550b0355510b0740800c0420420121031038210304006040a180940c00e9031601241c0c400d241c140084400041d00e099403030b6100383c03101d415a4003619124144002410350701c07170b520b0800301c44981d1140d0101d4144000028800d105813030003404601090a619244246a600007100000d544241c0e59405a07601209003d140304440c9a4461406860200c401a1900c20019104c03810715141040b5503001c03c1c0d000e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 708179775 1250 708178525 708178547
    0xf040204050c0c0a230312040314180d1a0703022101081c03110d0207060c0201060e150a1d06011d0d060c0203070c06030e1b060a0c1a011212080403 65
    0x2080f62240002034400b16145817409035011201d0100007808882141e16100490240b0b029959200040502c4800100c0c00d204108041800740208150b40000d450080d000004841c030500d52a6a0917a00e60080181c2ca182910366002003500820b12a07064030b002580e201158440c44c110030020352500d800c46459010481c0c0c01c0068084d4102241c0b88123010350051060124400e10540e0344025001103600203411a107421100641001c02c0c840145105014500546540342c54039001c6842d5044600200214844a20342015240780c00080c02046e596091783c4107a44003889004c2c0746002d0700014008610172400c00840c85240122003001e4071514030300c140103035002e600001c2e40303170088601380c0c0f442c004c248000700030246212012030b440d035043d00031038840c100c0c50381102c3d80400040c44105a842200ca072658000f103040c0300c03064107240306003d044c3c1140e000e0b49084856401101281d0030300d2809800025840c42400d41000800c4200388071600044014279140c400344c10980d4005144207448 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 708181025 1250 708179775 708179783
    0xe072c040b03030408060705030a0f0c09060e01020703050102031e220308070c120c170a0e09101208130603141f080d0e030609010902091605040e0f040204050c0c0a 72
    0x303000d081c101c0e4a0820441c0c0160410000f00c0d525440d100390010040d80c401c480d041e01c02d90a213a001d0f0304201045c01241031036001c503166020780b641005011589072031604001c60452040b81c4001000c601c3c03e10055008030f00c0d4082e0751180510700c00718000000c10140020820070202e14840d00d40c24000e8071604903171645813034540516160044122044442c2c4d0001510030821603050b0310100f41c210410b0040107101c0c2c81c8081c01c4200c1200707a228a4041ca1800c00081104012101070b2494800e4055a0007400040201200d0b0707111908084081488034003150607800000b000041d51809000ca003006200741d06d001d002a1204546072401c007480a4000c000c82848029040707102403c48400001401c1c4100031207507105602c84c002414441c0004c03005009020702400306601c0e620600480c1c00750784d000340803880c80340c070b03121120203011046181c120100320082c08049500040c40a00c0b0340074003025081002c032400e10340104412103601a00c0800c19500402c078458454202080b040c00c00c43d04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 708182275 1250 708181025 708181031
    0x10308070818061209010c0e0f010804170c0f0f19060c02010915021206030d0206010b03071803080405090a09021005090d02061605060901150902090103150e072c04 72
    0x44050041c0b288120b50298580c40000410b200c01d08456411084d44520250700007806101c90055058400b0200d00c013189412110756180031200b94000d0321f100f41c00500c0341c02c80543d409481c40642d4115004001841855040761031103a01c5210104500e280c14900c003405082029103006608140c9031014400034000c136100c04180c00d4040c000e511100f100c9401021602b4a80410b025140003544009299a16040b981001c00c00c0d034140000c44410007489074000300541c0c0d003086070034041d90700010040c6042103103802c06c0c0e41c0200074041d1030800030b42c82000802d031520700380001c0008401004284040c200d25100039440580c0d20688111050b29050401c217a9440d0801c0c00b10764841000d04010390001c03400070322285074203052804c00c0341d207178010420b4414640321003914034282c90100c141306250042c45401030101d074840d58010904502c05040000780000442d030001c503d01c440d648015118000541007150310784c0c00030b8050075085e6564590100b076043c0000035100c2c440140d1000d0b070180756 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 708183525 1250 708182275 708182287
    0xe04020109080f0a02012105010b130e1302010e190b040609080d0207090b04060e04050c011b121d0d0516050a06021002180603280902010e0909251505030103080708 72
    0x8004813030310602050040d004c8c0300039a1070b8001e40d0110380c040c1410113280500b071382002134061101c0742202e0050f64400b0081480c42c0464004503508045441642d604c07102c498141c803000c01034000b949005242441e0050344807880d020b0f02402112059000a2494002032a00340507107601158030400e54441d40700005260003024003107002004140c10903281c10314540248014404002480700504100b643c070b0850280002e120400d450b0400d42c0e00404c5890006c0107082c0c01d9004880784980b410840c2009200740707400c4000030b10403000c003403c10303180b9030032843e00824501e00b1200b800c0080e100c141c0c0d800000c07500e800f0009694010011440d14401c1c2e0201d540c0c0c154051048904806000003000c454590800881140411414003880c60a0114018000c03000300310b6401102c0015030140c40c0d40c0903124103a424410b02c640c0080401c03816008900d40341a504503c401c0da43e140c02600e0007102c414504145031449225022a0700b2030901c02c05000400010301040121405944c0c451aa5a01c6d40b0f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 708184775 1250 708183525 708183557
    0x201030c090b0d150603201c020304111011120306120102070b0a0c030501051e040905100902011b050322080105150f191e0806010e04020109080f0a0201 67
    0xe10a4110300d8401000146614070a002e13034009420821310075466a030b0b0260b46100640807030390390f10607048000e00d4080b2060080c03504031700a002d030200c00002015035580342c0d10f1800c0c100d9000f04c50846008040780281007407801d01c0440e042560203a07041549094001039482a501d240c040382e905015800000003501d0754031402d4090340d900019800035529007080307103441e01420800321101c2140501d8250076101091081c02400c4c101c56010b410501c0f00c030494800221100441b41c29a608a600c2d00100340000301d041001404855010f00b0000791480c882c80010030182d44681c00d822681032004609000c17800100440760702c03406444690b40c642a03072003590310484403560702c142400d510300420007031800021065200c1020040703404541c8603044200b081310f00410010502c52003410224107000401c1081c5003128200e0030601c20003e80c81e03139020114649107090b00300da8134418441c0240170455800c00b180318003070590030000d04241100400f00307990702c00e03503040c0103410030481c0701e503554401d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 708186025 1250 708184775 708184787
    0xf0b090c062709010b0415080412050304032705040b0108150108070c050a0b0a0b04151e050a0305070801110304030e0603060105120f070e060f030604051005120d020c1c0201030c 78
    0x4407018044200315a0741c2c1d010f01040360450311850b40c7c202000c2c0940390405200e007480610881d0710800b04042809a8a001c13101c9400080c011010b120b4050440d41300d80740081840740e0708000780900b624086040c9020300064811114005040c08000d00078801800e042d0410014180c2c2d007882c4c034040c15070b0340e6401104d80311100c80d0060054000d5013400e0060101842000d031007800110410300841075500300340011142507003681104554000010700c02d2001c50070711420100e0030b0202d003090980d03c0e04006070b5920290b5204684540c03001c0d1003013150b15421700680c2403c05502c0751141c21440c00352070244c0000107801c00ca41c8140c8000000811607030142041d83c03000380922100391040c1c0740086280b0360f0a10b040c1c2e580004100a038030541228030700302c81290300d140e80780018076080d0348454017840080c10b4041c0140d000c9400042000c03d05413a46002d20030110105002881022910701000c3e080407503429055000e070300d0b00340200c14645138061106262070f60a01c0c00080452851754201c805e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 708187275 1250 708186025 708186097
    0x3020a08121506041508090f070b07060c0507080706021612031a0a14191a07030305010f05060301121b0807031a0f010b0f040b070f0b090c06 62
    0x4489010030180c107400c11407a421031160349914403007a400e01001c0300300211400f0703912030000300c2108144030039030382c92241849941104800040369a1001c98180782d074203040140e045032498100101f1034070f06002c800c0c080d00300f240d100d50800500e071001c42c2c1c40d01c1001c1d1081003800303003040381c000564900e52060402d0070101d00e80c01480ca0b40090780d2400c8014042d0801e01c1c0041c51418000803d50f8451520f14403100c11154104030b00c4a181120b103080c041814054410051450101040003442000441c05043c00082c4001c030103540d1200c52601400300c55040e0001c0d144080e0102040c413141d150001200e040d154500208601c0c0c0c0c0c110300d031070078040081c100180c50707200184d1000039114a001420b03c0c29a4400c580c561480715000c00d80b012110b5040b20440890301e0102c00401161810340010003400c10480c805038903003a299810b012582d40004000c4030030b103841d503100b2000d0000782d050141e0080d80c0c40029014004114001840c940101000c0800c006507c60072800040c0d40c1d1590498 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 708188525 1250 708187275 708187283
    0x406031a0c130321030c08060f0d080703030e0d02011a1302070c0308040504180b070e06040b0a020c01111b1908010e030c010c020d0c0b040c05030604060606110703030503010b030403020a 82
    0x41d50b240c4034900040c0240300c0e6030b103441000905400400c2e04501900a81860104554070f511040c3d98a500b006500381003844540d40090391071032070740040f849003401451000d020383c40c0803d000400402e07481c903001504000303c0440e454901142d50380f041c844601e0740e241c50304880390303176900415a188000921685a00800c0c2c2c00c80e10000104001001c0083d2003207803003c6a0400401c000208640c1c48080b80039401402100c0703190005070001d0242c0d01e038024140014268a0500340c1b11003e615181c0e00c004000405030707000c407041840c07940e40320210b0314100303c00402401e41b100405132050154807034001c0842c411a244c42d45074012684000001c3c0061990100901980741c0388460a5125842641c08040650811160107142400000ca001d0b400b440ca03514619040e0060b00d401644240240c400c442074403080c4400221950100010380c0128050340c000580f40d403401601904d9070207016110300e003503000321204001182d0050296811940e0340f200c1c41d592035a9910f0102e040680c0c0e500028 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 708189775 1250 708188525 708188557
    0x140d020906211b0f0702090403030b06070c031104020711010e130603030903060506091021060c081014150d06151d0108600406031a0c 59
    0x709840e101e1120341c0e003d000350840d80b48010000d080b9045052050600e80210b0040070000c0d04010304207074404507400b40c0649000501d00400400140c26503002010a942c4008044010710034442c54411003c518501161b045203000d02d10390790301c200c00039480c00050500030381b0754524000751a1016101c102d4008400204181522031038060021032107030005449691070203002034000d040801b100d5004100c40c080305c0f0041c51601d00f00400003170300b100c3c24904c504241c006980c0082c0d4140641e95520156448041c80c610f0722021a0740207040d280d0207049030715a042c03c09580350302d4480c03141e01318030a81120950382d040745003d02009080c07141d000c038140780c4040c048280125801100032203071001c1807000c521252452001118512010b071549164001c4c4440340b1801c5503c0310034240100c5e0380a504005003040152005004c216020030410402400c041005504a40b006101200c1d101c045804224441c01c54851910340780c5240043d001d002201d20105511041303a400f510704105184940b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 708191025 1250 708189775 708189817
    0xa2f060106110708030f0322080310030b0a0b100c06020c060a02090a0602070501020c0f0d02040f3201060f27030209060d1119080111090a06140d020906 67
    0xe0540007980b14040340d501803c0c00103e00d09001004843c4034081e0002540e0540c0c9907600441c0103200da686805400c1310050141c40000b40b85440610302c2a6821140107034042c1c80c606044c0484000101003010141c540032003001079a6070514582c92003080c03854000188081031134100028400c00105280c248500c0c0100010700074590010300301608107440100051366101401d0340d0398501401000c3c00341c2c01009203400c440c10a2007146280c00c00042009898a001ea00400c04582400226811b099207810040c5940800f0a00015003c288050790329048144840f21802281c2c040c0503000c10407000c4110500354600c030b460700743c060500001132618001c5071032a02c507111050501c4124020444007000461600d8009000c12803542c00080545400c80000108005415046503208410302541000716202400340314440710700245600c01540ca203150803c0101c00c04407035001c1400c110f40c00d4200b003091101c00080d201d54051004025856600400c0011a135024404090b4a0103051002c0c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 708192275 1250 708191025 708191027
    0x5091203090328110d0f0c0c030206030a0506040e150f0c040f080c0316150f02010f020403032c011202031e0702030d06150c02060702030c04140403080603030a2f060106 74
    0x380200f40721500c2d0300d000d04104080d2140c88094000d0540040b48650b08014183d41c0511444101e5603c910070a0341ca050f00d03540090034a4006541c1d881005959104000d080e003020721030800d6031034000008103080c1c01c948900c0810014000d0010000a43c65030102d0442109101640d0103045007001003800c4d582c81d071282503a030b0308080d83c16038424411141207442e05803200c01030300141c8850381c0d600c544401c2448419140c81030990401c07000c540d030340d040c2d40d00c100e030a620103400514031036901d10340c04408840c05003040c105803805140c58005891040282681c1003a4418002c2c4000c05c4050303104c1c0e603802c0c0040c83c0340c41145500c0c40704501c0201000022580400107005d44020140208039094462000403d0180f09480e0500400d000780c0f00e60002d4540354001c1c1c501944020121401d1a040c2c0d070104051302c48840408003001828010700041541203d01e16600440c1500158248000c81d40c1c010601ca40020b80414501c100c00c803208002000b40200714504d2549200321652941d50380d234 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 708193525 1250 708192275 708192337
    0x309010c0c27050609071d01090e0703091110200102070203030f1b0a0305040603020d020d0c0e011707080c030a09050d0f09050d0c0608060d0c0605030f0604050912030903 75
    0x801940083d241100041081c0390001c003150240b541691200440c02042a0581030f2140480701c45040c0103040200081d1042800f04c4e07180308800640e070204109140f45491000c200e40e07030181c40d02c65550190a8241f113980074032600c00075444810007140e6488107080c014024450303180040c0d0107000c0000c3d1780040800c0e0900403c0c91010f03680900014000105400e42c4079031300f200005000400800007040407905ca60050f05400c2582038005243c02c40e0711403601c003201c050000c0c203c0401c10411070340c000c66030000050640445207100b04410303498561001400c107500100854041c01003c00442d41281150303100c035101035031180883c1c8070845154800342038424404001000105901400b01e80d03400c20940c000d82c9140c0c4008140c20403414044103450b245001405c00e41c01188604012010a9140e4440c10051105131900d642e2418280d02c100c092043c0241b08a00803802d000501120810020700c0c800000360380e2a445460751180c40f2118154451811000d2400385a443c034a4001d040f164 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 708194775 1250 708193525 708193589
    0x909031d0609031f0b0415030204060e0108030313030c1b050f060408151302030616030506010e1c0602040b270d1214071202030c07050a080309010c0c 66
    0x25082840805800e02081002c0c4210742d0380c142c00d6080705030701d507107140e4050030440d01d080c45400011469902e040003240c126144900d02d0105a45011000c10541c1468450180a40024005502c09604104c032482ea6403001a091480c504000c80d00c0038240362203041c0301c102040c2d10a00210104d21511825403041c020350040c0c030b100f0700401c044040c8030301e4048102c4041340ea400020704035012041e1403240e52801c00a00b2407a2010b804406100140c6c0e0034801d8501c161848200f0301d190510169004040b00c0000784001d06100110906041668441491040740c0c2300349080c41c4900451847d090000c0d00660b030103000c0028010482c01104040103021011080d900c0c13150a103c003440c8410094503148000b4054054030412279100d01c001e2007801d072100c000032030421840c03500100f591819980c440e01108600180c0000c41c1c0300011680c08d118031030083c0b0080740d024602070704140302592240f040a51480c14440b00301912400c02420901d150010244003540300344161002e401c0100e211149 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 708196025 1250 708194775 708194807
    0x6060e030c0105130e060d120507050f0c0a1820092b0b0a0e061303110d120b0a0b0c0105040c1d0a09060f06060f11010501150c020109090903 62
    0x2449a007049948980283c3e203019900c04619140e04d89021050460300c1d0010f4402c0da000038018480310003151801844201d8040f05680300c43e9908014103000d402d00020b080d20769510b03000b1900b40205035070f030003210009a901104000c0c80c0c000008165400402022120100c202d0170b02c0c54808000700c242c00078100303440c8103851a40d111000c01c0340c14a02c038991000351001c541c0c40a60140003103111030700c0540d802a058240082c030040303050b0990340f400408440c155092003101c100401050b40c002407034030040203080002e25040c03007208400340214000403640f140301a074500c4170901c02e50f150300c10200103042002c03544d6a50082000c90307501800040300c060f102104034901c0011992011400300c031328400d50000b031300d0341511303014912000307007078800010388001e921001d03c1d42c0381140510a2100070245501c402c00181d500da080034004540b6031800c140e59900d020010451261090070b011440300c420324044510080620041e2008141a04480ac03441c2c507000c011001c0640040c0b1300c074840542 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 708197275 1250 708196025 708196033
    0xc0e01081b1309050f2404030e01211d0619050901060302091f060f0c02061809190c0e0a0306050603120c0f01060b04080a0b0402040b04020c0601170d1b06060906060e03 74
    0x34240b030711951a001c11b401402425071000500032a21a001c55150014149440c5e08648215000f02c40a030000490081485903a00c4425000399000301082c4400450a00908144d25100b420741b030105151407210560365444000140d0071550a502601c00703590f008000c02d03800c0c20021a01c2550b00f00c010f840910740d1124000110358913000d48100c00b06807030135079034240d0441855400c4c0400f60f08904403500344030b03284005000d2240d4800719081d10404604030050740024901c103134101074071100c46580040c00040e516201c40b544840016109170398201601107955100c040100c0d140102940003007180350710100709174404010102d040d450351246000240001510307000025070130310444c45620341395800320171286e0019208110056000d8001070000425017022004a010b0740c0c0310035450401070300807c005000403a1030003202c0e010517142d40300501940b40708020250210b51220609040b595030030448808000c1c0310703001500507200084090089a0f9594006445961103006c55031082c05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 708198525 1250 708197275 708197293
    0x1005120702010b0303041517070c0c0911090411070f0c03050705061306031a040c111e19050109020607120e010c0809011419020a0c0e01081b1309050f 66
    0x32050107028070403503008028501d4146011b402c911f061001d071140c4001c1c880851120800e1440504015103e0301054450f100c3c001018a002d180c00074203904603c1b906450081402c000e140c840040e540d4068060b2400206010704240010550090520040501042c860954208500c90344030b84200c3e8411030440340c05944600400400340034285010550800c030150802a8510070740010107000011032004044001001c040b8050f150308041102c040345283c2d000d00e01c03400080050034000044000b003192030402c14045a07440701e07c540640035a8820303160500c02441000c0d0b00181c00c0b154010455541c030800303882c0811541490480c004089001415000e01c20350148009403d4140d01000e05898000c40000648001c60840401c50019009204014455000b900c5808010000740c00a00c0000507514110104100302d81090079040b110388010055268009042400012071400e90f0130390300d80240125034020a13038048002106d041082030300500c40080b80f0b0218801b408015600301e21 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 708199775 1250 708198525 708198527
    0xb040f0b010b2701180306020a02100207170306061201090b04051503070e13020a0f0801050702030406140912011805160501080c090102031b0322030503070b0a0b10051207 75
    0x4060003034000c0010b500c40400040e01c400202c000c03c0820320504003010054000c480c154900c0b182c0d500102d50040c2d000918000c0b4540401a034207034014222000e524242d55a80e031010107a204905d00aa400c00101c041907041c1e4828050702c030140758004401c1495030b074860b96003024000306200e480c011490140418007401c410120303e0004c42c0081c1c000c00c035080c41c2284086000704010302403482191003088510042e6200b04090004102c40c041b42e40050381802c00c07041c21258060054004d651080108014240d044244c0c19000507009052a4031b90100038041100c681c2d490300c2d2043d09500c1d16440b00c215071081040740007864003840403940110701d651484102c09183d401620702040c0740800040c9407402070740040c81c80a02c188184ca050001c0c0340c1088030b440100754442c401d07030b070804607041d15800304560000d81005514140300d0902c6286480700340e168070400700050580c4440b0b5000a0004900341c000402441000d04003810511030a000182140c101c03c01440c6e0900c0043c0115a841d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 708201025 1250 708199775 708199777
    0x40e070516020d050c060a030501140306010513051306021603090501050c0a0803090102120103050703030233040c03082d0c0706050c010621050f28050a0b040f0b010b 73
    0x4540c0701c80d420903140e0a150200401031940c04012600c80c814484500032940703452020703096100182d1004a02c55040001400315011400b0280d4040c0c1d211034010070a40d9504020704903903001c42040015107485086803000800c4805501031300e031500018590003100c1aa5601603200750003682c07015086a2a03a00440d5913100d180c80381d4407998401030310040400c240ba002035030012100d074001450100380d81030a0180f15001d910584940c0c02c060005c0051580600400c0c000f0360021080081c4150900420310a080700c8211210825801c0c100040401100094020103140c0084920b511150b11183d90f045130b0507903141000c0c45014440c00c0000880600013a110030007540e101515105083c0301c0111001d0300419400c3c0c032a50348890002420a051301d903488004035210071020250f2465090040c5031905561404405910400e1514038821203601080201015503190b0200c000040c00c2440c0741c844524009051034000c40c082c0010890001d1a2461640c4103410554880c0e036103410311039407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 708202275 1250 708201025 708201037
    0xf03110a0b0901030f0b0a0815070216030b07121a0f04200313080301060c030e010c0308010608070302071e05010e1923030309060604150501021906021e040e0705 71
    0x4600180300c0340d02c0c0c0d98041e41146515040940f400520b69880301700068184150390700c103c030150444c01c0107428901c40040d00561008150004000070070701d00c1c4880301018410310000d00005c03450008290308074460224201c40042000d01488844060034501c800030002c0c500d194411700e50480790458504007402040096001a102c11050300701d00f40182c00c0588c802080c100d14045c0544000c0002042e030405140600066594402103810614028046401c0e0010903818046922140d8002a9020b440c80d030641e0814603004c0000c0c0c071031050907030180c0603041009240105d8808150302202c11085a010028000d40082c42270306000c1e4103081e01c0c0d0070440c40d08c1c1c0303c02d0507014142020030710000b07840108010096520a030300e00c440d0440c43c02e6030415540481940c22841c00d11440b480c081c01022180480ba0450f500500d1a050000c3d6807101070f41100d980c2c01424810b04d00a11406030706544080940c010b035803982c1c104440c1090526882402040d035142d0a800c04a14081d02c9007059a003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 708203525 1250 708202275 708202289
    0x706140114130c0e0a060f031406091503010b030106120c0f030309060c020310060b0702090f13061116030810060e010914240c0c040b06070b0403030b0603010f03110a 73
    0x82e912481400000150040c6025141070241540080400703480e000002c04c028412562000c00241d800c15009055882c4c03030030714110b0310030503030240041036441c0b101342a00700b110307443c1e42e5144144071404213002d0b014070111642d00d94a0020009041d003d5410300d1044c240c450541250740c13640b2040492149944c80c0000340014400003c144010790140c1d0020200900050480d022204010101402e6441581200909541c0460f000f01141404010300b5000800366804400701e1910040f110000901ca80d005005c55498108120620b00c6c0c0404846148001d196200c115154070b08000c1d1140c0829501500000d11402e00020301c0c900c1001040c5440e04140e40e0312041302d161104050001c00741f0b01a917036010740d0500a161805c00c07a0f008451040d1841c0c0b0000d62104c0504c40300504003e03002e1000f038015400c000c00d641d040e903182d0301150706482e40700b01000c0068490f0b0408400030301d040d01d000c50b04103d0000000c00e03001080221201101c1c807c0b00000c00710032811041c020a0011392007614 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 708204775 1250 708203525 708203539
    0x1508060f01290a09080607030c1b171902060a0b0d171903200c120304080f070b2d0c0318191b030c0312030f020706140114 54
    0x310010075948481d00d1400d0682d240c05520400142120495a0203159282c000c9800c2080070001040144a0a40e000102d81410401d24514500103420b082103c914850600000d400c04010885400301162018540e280300c151100e481e5000c540e030744030038299000003511a14001540d80000b03805038054442c00507014048011032590344011b840f040480e048000ca1007402400c0d005400c640e0202004a91642c0100f207810164003407058600486070552010041009016180c03000000d1107a0b0100b07018103c20395a9650b802c010109018281419840100c0002c0640030301c0089582c8034000e150140c80c812030020036101d0282c5d00d1001010080c8400a5803000a808000000103594060800d40200140b00001e4010740d05182c0c0032904590108044208002070182038941c40004400743d01640021508580f1503c84107040b51000500c441c600000038040107201e5007108900ac8071880b07095403640320383d141500180c0740c454010f000000c5640c0000941c2d42a81c0c1d01c05a86607006440780d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 708206025 1250 708204775 708204779
    0x6011e03020f120f0105010e01090606082a040e0106081e0402120f070305030c010c0216140105120a05060f300111070302070602010c0806060d020c0705131508060f01 73
    0xc0408841c0e40d40805910000210390002c414a0a202050031503210b41300010341503041c42c1050310040010382003900705a19229003802820b4003d21040e8100c4010111003801901520103e49403c5840c42c03049000c0d8004240003036070101c202442e81c16640551940051684c1d00d080140c00491700c0c1e50f04440c0126000003003809800e05044100350750300c42d90196620404641c1c4803501d485060317030003202e8a9200161070720880d00c003885211348040c030501c00342c0102c1c4580c629022448400d070046903c41c00e0301d241d0301006030703010307604030303201044058900e000d14a050003c4c20b00518007207900e540502c0b0180104c00e041d1500311282140d03150040c00c55400d10030744024130001018592820000340d9a200e1401c0890410380c1c02400c00c45210b03038001d10180342084402425201c501035036109000c0c80384184011940d40304242ca09a00d0400001600c0310381c28606549814444c0c0d000603046401070048007510f0152790400380e081e0303140ea86041615680c43c01c030140d840c0400c44040194444503001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 708207275 1250 708206025 708206029
    0x9020a0b071b080d0206181e0f06070c050c04050403050a1101060512160906030b060909150c090102010b03190f1a0a05040b01121203050703110d050906011e0302 71
    0x1819999000b00328059868007040d9468500c41c031140c1154042e948071007941c1c0520350b8100700040d4014041c200060414075001d4016659010007803200c40d440c0e5402c1004c030072030f210070003048580a07a0710781140c07418100b0380c03001340a21560f083d00b41c8050088900400103405c01e400380358051a85581c501d407a01c4000c10301110300c040d81d049984a1552035200000fa0765596038681088044464082c00b01d140b40c0e018521040c0c7d005501801c0406e040907010070208100b0039000340d08c800107030f030034602c82ea49080946042105034904500103040c100140f1900c0d1011002814903510700b0380003089115016802c2642e1602e201e44a80f1254060313103515000180419070b80701c0146d109039992840e5540d40c1c94450130032203046510715901d5542c4d208001c240f1140004031801000078404c4000011803d80710409240881d2420031300385511800030611041c0719a10141510100c2000161034004002074031003e0304e401d41e4100d095124040000c50303990705e15040c040c02c2801804544104600c1e60303003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 708208525 1250 708207275 708207277
    0x1170403080a0b030f0106030b1512060a0c030b03160807090e19020d1a190b030a061d030a0504080f01050108100f060f0801050a14090714060c070303050c1009020a0b 73
    0x14440740c00d4084c50140d001750400074000c05000d103101d08003801c014a03046954581003590019602d201d4684001522010040410740300e40150700d142000c10264a10101a0068030343c0110b0b191305440340b003512036828008021a10182ca80341c1013a22815603880c114581078680c9010f03c6040b640000040c1501c03070000ca100c100c0b0007071018100e58030440042d200c00401000790f58804906400072010030001d9031060546142c0300007402410809440d212000c2603441a00b6100207000d141d0758503e001d0303500c80f0402440030f400084011a96520f44031100102290020310030b10a0030700c100d402240042e401801014182c83c04400200044203800b58402d000c0e002c24940d080800781d4644012500c0d0b012886010f018003030100c004100da0811000c804101d500c02521318040d004800e0620580782d03c0442c0c5042142d210701406d0240c6690040052101d01c28600012030070302c0382c4030b0004100764000002d800c04075100000e40e2070f41d00c10108207609640701c001000b0b5116010a809004d94400342e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 708209775 1250 708208525 708208541
    0x40c0f0e0d0804060c0c0602011107020f0a030b011814010302010507032003130806090c0604050d060f090f0506130201050403320c0a090b060d0c021002070b0601170403080a 76
    0x2003070006a000503880e2901d0760382c0a900309000241741e44c800c41d802e101d00c0000720030007001188020041401040104903e074051410000d204281c4ca060101d001e5680740032000107140c12498014041d42c1d03502c128624138045815512b03010f403d0180f041c66031510340d100c43d81242d4041c1c48031440c15000d66001c8828600c4d070704200c03000d02d496010a03146500c042000e81005503600c500441e030503081684e00d074946040100100700c10391000c1d8141c01d80d521141300361006c490301900c1c5c08034544040d140100c060841541c0e407600041c5070000d44004d1103590200148214002c1c0e095a0b05030719402440d40885d207103008064081201000100001048803e500840040c510b584d00f14008500b801446400d40b10300c0d800701268455580d9880c0c6151003980c42000f814012000c01c0f113040b15501169160051841c0c0c11496592030f140c07140528020300208044440c2400c0c1155101c040e46050026120117803030890004643e403d014030a4400c80d40118000c9800d6120700006070b84d040d4000000d440c0b10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 708211025 1250 708209775 708209779
    0x30109051005221101090e15061309020f040e13321c030605040c0e0d0807020a0e010f0b03091e030c0d050301050405070504050a0e040c0e190b040c0f0e 67
    0x940b0590f6050704091006400b14800c90310341c3c3e0800386200005003401500d0304a4200c0a0201080c01132050604c00950000c1343c0c00d07500c0ca40c0300c1e15034000c02625201c2c00d900110142d13000041074103d40d80044000c0c01554072407a10843c1c41c4d00e41c480d800381c201c0902c180007051800b400703542d4100a815082031103003039100c40c01ca0b2400f011005043c0c44c01c12a400c003816842034100340882e900c454140c00781c039018000a5508110203002c0c5030005009a140c01a11402980152024000e11000c1002c41c1c07007981c2c024110100311552080d0b00280b1079024450044e82c1c50b01e046001c200d05086908480c041e207000002460300411010b10417442c40178140341c1c01100d100801600c1c1c502c44082c07000200c1e4959985882c0d8903503160806010503200020408810440d0401c0f0030720440d918001600240c2d15158000030b0a80e807603140040f0100800d0b017120a01003004020080211a07080f01c8070540981000d041c0480d4180384180415a000952440c0c0031a1584d00316505451089150014000d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 708212275 1250 708211025 708211051
    0x30221030702041407020705031c030905030903011e050604050402060f0901270918021f021009060204180b0f040b18090d02061612050c07020a08070f05030109051005 73
    0x501d0b80007908a0307950b1003c000d45080014100102142c05001082c020b180c1076010700035080d0b619071000203000101304128185696090310b542031000800c251055150003900801280c00e80e04c4401340040603981c0065040c0f401c2a00140340c9040500480703000743d07030141c5480c2c10f00000c15003c031200d4101c07440c2c150400036010303000960791400c80007403a0140390350100507041c113060280d501c064814030103071072810b007004c000310700010b8a605101800d014011003500310746c4182d58a00301d042035104110310794041c0c2080c4071a000c0c00100da00401c1200c2d04442d6085502c01d94806040a0f02c0040c2c00d01743e485135410070306603590300f03068004400184004020001c3c600c14805a107860301e00680703805107554070409654485a404000c02908a0140910f640c49240100350040994407600940690785484001003034410103800b044c0d4090950040c1503c0019456001c5265184002c1c41200c07410312040400080d10b003418031179120f25130b401502a024035001c030303000307000a41009410910300b485 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 708213525 1250 708212275 708212287
    0x40b090d0609020a03060b0a1413020a0c0c0602071d040c0506030903040308031f050d0506010909030c20010f05040f030803040c0b07030302030f060922141204090f020403022103 78
    0x550100ca25010303602c00c0340001841c18544c418003ca04020703030001c3c0040c1526041403013031a032b506030401c07100d21040c0c03001603034450015800320340c00c0d082100c00030301e00d0130440e4000c82c095401080e6401034418070760040b80381c41d075841c2104a0303500e802d030b5003e0b0111400035800d01003428600000d40d88407014200b101d280543ea035032959645c3e8400c840f0f003c1550f12048403000900c407400d0345200145021038401414002513201c450308e59006118070703100c0941d254038a60806000d0500308130540d030031041030030f0461840116015041c0205049a001460824501814a0091041d01d05803410142a12a41404d59942c01d1035603002a00a481209483d02c00180c043d03540c80050010b940300350741c050303100e0034180c810142c40031021f070849101e041c0002c100b000c034000907803c1040f54115040c050102c01818101100c0c042c02e81d1116128030701907140722080d0790140000070300454a201d80208500d1050441c13900c12801a40030003584410140052141c0f400700c1d5025081c00e400880a80746400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 708214775 1250 708213525 708213529
    0xb1006050d05090124030212150a0515130b040e24061f02070f0f1d1b03012309010e071409061303030e0904050c04090f171e040b090d060902 62
    0x5401d0304c00514440207081c170b0900c11410700c0803e800d5445c910800070000e003c00310b0107041e800a00200340131205581c5070002013a1102c00c108a030451640034100185080342c91034880080e000e141c030414040c0b8181002c40241e620002009180d0003901107a1002004100d12041c00b140310140200b540a42c0c0151400648081d6100410000c04260010000b80d8a840211000e50665910003030365042007401c02c0059020b00c03600080148102a14222143d8840c034071401174004211500000c079001200100f0f40341440440d048039800c0a042c50002c040440081050b401800d000700946040c00402040b14180140342c0c00d020546500c01c0d860a001940c0c1c042440c640020034444898400340004105040c2c1040c040d40c500c00040d03401c403096140c181c680740d50340c032215440c1d00e01441c2d86d5130020741800030514203035956507403101441140b040d4260460010340c00200c1010301300301d0042003019207901420111000c403081c0c0001141814048401c11001741500c040950b109502c03000040010303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 708216025 1250 708214775 708214811
    0x60f0325030804060c0c0603051006052508040f170c010c08040902031501031b210b150c1504110906130536070504090501060509040f0b1006050d050901 67
    0x11340455914040004480e0800b4004080503034888800c3c5803402003071240d01f280da0444041a2101030520540d55408a100c095249902c5050092003840049002081102410040003107800c2c1c00d45400c120350321615895a800c2c0850310109541d8894171010009500681c1324911403070040c02501d00302580d841070041070342d000b158030021410070541d40700d1280d0303090311a05000d0407a032900c0c5040700306140400340c1840c102c5030b0071070740309000b0b040042000d051542001c8403011025100150200300c1c6802c105076034005040b603007068050000d03456403551800e9030892003140c004049024002e004400c0c0610303020013a00340c40d0869854a201400d194160003118014401a40d840411070300070b860a8105200b65020b000800ea07040c00d1182001c0c4001030b4079820386004442c0059083c0c1c4a140c00b070300600340d83d4801c41d0410600c10401c0244103450f81c0c6000b80d0750149501d50039a982c4c1d101405036002440c000c0d0400700b8001c4c0303c909001c10455100d1640320010000000e1480351203202c010702 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 708217275 1250 708216025 708216029
    0x6050702040b06190e36091e070e0c0c0601031103010f050106020f070f0b1c060306230f0f0c07020a030501060807081c0e060a120c080906060f0325030804 68
    0x17049101c0300d281c2c01030800070104250250168080315031041182217280c0a40415075910507110a020081000e5500902c55421031143d40e00c4191004288200b10a8030382c442c501c1007280c0c8211100003d0f2020b89407130304903620045840d000d0442a82195203d07110708081e501443d4042d03603140f00c803840e04403051186c07501811586d00100030341070780c80041e07070b2800c041a00045807880b405d08082009214080540d1182d00120490507490030795108034030014a101e034005030140303041ca0702c4001c01781c006003e000c0c81e00b0070600040b40103903504802414510400e942c056004520000090000600800a894140d100420b58400d1590340c3e1102420345440c1e401143e41904130640030040c2c40703001c00210020402c44400c1140d45020060050040d10700c030702109004101c0046c400340e05c10302c181840c1a0346003041c20704205810b0700e08070080141d407080340c40301c1c0300303102e00808203074149031510b84c0c20036011004001345200802c1d032111200210f50500b07044a02041c90300044001119103000d480 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 708218525 1250 708217275 708217277
    0x4120215040509100e16080a0b01050c250801020913230106050307020d0207150f020f1501050a1202030a110d060e0105090c0a060c1209080f0a02040c030606050702040b0619 76
    0x9113450070400c0c1d0115220b009800c201c880c19500a000300c0194014507655030051038000d0004038410181c00586440c07061240324221400792a00c41c00d1040c14041482240700c410035020481c483d01c03540030500700d100d81c8040c203900144200d195812105a6045070303c400180c07940318202c8071000e00380f0f0104000d0a0f04a50081880401041400b0707a0400886400640d10720003002141c0c0b40a071072199031844480c1039420002c0c84240300c900d2500030410030308030464520441c0e000041110701d1a05905082c00741d148205038030840001c010790180c200c541141d40040282c0001c0c5511769a0494a500341984076400c402c6000d82800418a0340c0b05006007070660300c0001c595841c05605c00707070501120b10300c95031040d00f00d04424880c4c0d0f43e2081500c9a115400020035100c241d203542c2c10784d45d450460740305184030300c500c5035500007084012a07001103a52080d10240002c014525080c1e040d00c00c2ea01641000460a01024025141580041e0b080d06c0011302003501d003101d960170341d82d400d001011003a4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 708219775 1250 708218525 708218551
    0x1e14100e281a060f070609080903030a03050105010e06030702060712060801060b031e0903030c0f120408133c050405070c0c050f011d031f0c09050604120215040509 72
    0x42c1011000c601c40e41d0001600325a082d20f4078501a80c02c030107901a01c14040c00180d41c0e0080c800c100412281201c140000c0101140d0b258404480d0040c040c06090099900003000580541003030304100003071300d020760281d4000c1e0003030707580c1e00a044514007aa9140f05a4464071403130b000a05100038440d000160962810899807883c14060f84088108003039000e510049a00013004890750010041e81d07000003030158a19541c4d41088075056060080e4804503044400c11010320040003640c80040142e0f540c10050501000d6640c141d00403d428130007602d50b1415603040c00200d0050b800b400196944c2d0500b45403d40b40d540b69000b040407120708540c4000030a01c070100e608240281ca10010380100412034030b031010090b00718002014585001c103041401c0c010700060b40010f0340d0511002c000a16079440002a40d030f8103047c2c550280142c2d0070b12601044032405c0204035030400c0303c00c580981d610800c24031082e000369400c0c050341d046943d80403400048240030103d1550b461a00c03850060018110302 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 708221025 1250 708219775 708219791
    0xa020304080f0312011a07150c0e090f0105010c0c0911070512040b040501050306061603020c0a0906030f0f05160914280f0b041e14100e28 61
    0x1a1800641910304082c5a00900540e100038066145480c1901d084403c10070004000300400c003214000c5120040121400706d441c011305100542c090b4a209800740d0b02d0b180551104400d102803c0f00680d24403000342180350041c407155000b0068490141c1c4111261403130a640c0300c802c0401c840031040f1001d504400004c1003000d01108004061442480e42c5950b86080c0c50041010f009100746c2c40707994140240800007030007030b80d100700c00d4a9248501c030005500160b11882c00940b94590030414901c00c0f1004040407520407024801c20042c0c07075105108600c2d0f865203884900c040c28a00108540c00d1041c01c3d05040b000300c4580e6110000d01c40709801150030700400d0950384040c00d00034003109100c0e2448209840b0460702c24502c41c01100300b035400007400c00070400f20310007500c40b11701c0403a001814102c0d0b440c41a22808442c7c9801600000e081068410f104802424a001501e085818004010080c0911420480400e41042c028104c4842d00c50280e039141514820000e400141c0b00c0e568225 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 708222275 1250 708221025 708221039
    0x9060f191511060a0908160624262505010207140f040b03240f07020102030106051803070f080a0b070f17090a0c0e04060e0d080708060102120a020304 66
    0x100c19034207524240400c5a0580501650703440900030410040a03888aa19000740440303034048425140041000b0407413285d00c3e0811601a004060a281d20301c02002402d540d05250407034084107565010442c6403242d400ba09003000e00c0d615021000901d03000300c220103051040c1c0c40340789121083c88074003d000010320b030500190504603154030000c0e1400f01200d1030f03952559480081d0381020021503000030064490300200307240a0541441e5030603960104604150b141c0d5040d002807040d808955084000e0341c03903c0d0102c0c02d0780402e1084202041c820300c840f02c00c00c40d850b41c524244c07401c00390031111415600c4407910414802e0b50b2082c02c543d000501007a0610900f505903036441211814030b40890000e048002b005d1141d4060a60750303101050008c14946902402010b5009400018500815440d203288000c80081034408684031460320b00703406a604000f1400e48038000003515440210b50b2400810f850f00381d40100454118010150b1084048446e40090480042107a0056850380e091880f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 708223525 1250 708222275 708222299
    0x631091b0e0a05040504140f01023a0e0f1e031204080f040e0402040b0111030306010c05010e0d0f08280207050120030601090503030f030703150902040617061e09060f19 74
    0x80c2034422764010011120014203844944081409020324006014511070201d000603400400356400242001b07030340c04510000140103100380303003074000b550702080b992940222903070200b00748a000ca400078011801106103140159511030700901c0a01c0c030b8140c00901251440c0e22a070030003080c585080d014401941024824a15406000e081c110f000800844c109541c070300000b8603240c10001e031640e542040103400c0d00200030b003a01c0c1d801102d50002c070902002d045289091002800100e85000043c0800d14841e14900010b4068000000003103218141c0030181d80004000d03500d1b5034a4104481da011030f260341d0454820842c84010381c4a05081e00011305505c00b686c4928400d030310038040c0354404900d00c0200c0390042c125040000e4508200d10010221000a5101c0b04115101040001e0307141c0d0003840611700d13004e1071a207400d05c6a40f1402089401c0009401d001c1c101038038000052145d04290041c10341202c40205a1420383d00c05d44001120748549442c00c0c55440400b210411407082002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 708224775 1250 708223525 708223543
    0x9030306090b0618101b0804030b0f010605070206160b0f04110f03060604050a0b060c1b06040311100207120c08060f040201050313020631091b0e0a0504050414 70
    0xc800d1440d001c2c1054040000b405103104445c818103003018440c00207030044c3d0110368544203140e40b80e25080c406003455400c0390080e200a41e030390b0020b003001400a4040040443c1030300e070b65454141c203001c1d03684c080c0b00c9a03400401b0402450794017064084049180f9041292082c0c1d006e49070301606290610340700c801043d00200c03690090390211300c0001541d401059160f44114140d90015095540710000d45c0a4043c0b134070345581081c1e000504821905003c210101218202c01000c950002c0b1302051080c41e1285110141a680964034003c032075160a4000980747c0f00c0394811501c04c01e4441011002000c5410704c219800100480200a00b010a006880d4001c040710300344400b0b40791940020741507201c000c15400310004031105690071551400241c0f8025070100c8801100503000303112101303040413109203000400064a9000900e50818040e0500e18418810aa20101010721050381c594413255035160f4401d100800100d00d94551f07208442c03141c2e0041d0300d02d00400c005100503500703003c124 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 708226025 1250 708224775 708224779
    0xa0c031104050607060b040b100206042d060c090e090307020a08012a0c0b0708011d09070b0901020c18160305042006090d050d0e01020708060c0307021009030306090b 73
    0x14442002150b5803e400e60307400a8010380302054003040700000800034001d0900744c0f544441901030040c900c5900180c05845144a0b005002d10324582030758040740751075416003070a507a40011441c40d001400e16008a0215001400c0c40180c0384d403180a00e01d6404021111000e1592001c1900310035440d209030700c02c0040143700c000f045011480480100100c00c402003034182c60318111088420300b03202d01c00b10400c4541004040c2c1803410700481c010300c100001e00c2540c0e440300440941400380c00f41039260a00a12a90340103104181c03404101d0107468100720982c0341580a4030700405482c1e100d2610940c081c01101402d40b20340d25059000c42403003106c8030700d01f0081500c0c040400000030740c9000c2c0403c9591940c880c0c01040e900f2400002d1540c4264090716070004d1108124204100e070000d034081b00380d50340b51585400302c040c030001280d49003014403601c400b42d03100c13a010071310310154600250b0b0403074880c0c41501c41c1d0228201646007a615100811030000742d803070108019062542c4030399100c1e0002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 708227275 1250 708226025 708226027
    0x209010513030b1e0c0a03150f0b1b1b0906121014070804170d090204090501091e020105032205030a0203191419050d060e0103060e0a0b07050d11030a0c0311 69
    0x41000f003440180034081182040c1623860403950310a05440700c0441c0141aa0800141c000d44c42e2813951040d41c00041d09019100100c5820100603c00426101c24092640400355401d01300181048446440900800e821144049680035440000c0c019070702c444000680c041641004804100c0408500504038400c0040e40c90602002440b802a107000d0f80b000c560b1095115201e080c02c003001030001d41e0380290320034980002c031001c104040d0800c803240c50048414088041c8a441200a48008558000d001400400000d003150590142030560740000641e5203c0f01ca500e65100c1d440e6070320012905d00942d00100d02501c000e9002040014000d5031417030001c44250f5100120071080c058654030b1540c00420744206d41055101f042035400e014400c80050201d83d5035401040201002070209590131400c0500c40080c0d0200010390032400d030341c0020640015951840103c0307141d00503090b0b10302c03001e0f00c030f104401a0981200c007841c01510b126070009902c051065000e0111060316020100c1104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 708228525 1250 708227275 708227281
    0x90a06090f0329190b0406052b060c020601080616090b03070c05120d1503080a080910020d0507080907080705040f021306031d0a12030209010513030b1e 67
    0x1000010040441e0f61081c00900007810b0401c10000b0800350305207540801021508000e0a00300d80c0602d03086107400030500f04420140b000901007610243d004070341d000769000464551040700c0c480e02c481c9034000312101c900040303003990b07810045d540c010502d440103a1149005102c2c903038081c040b054004401240e0781d03010b000211806003044400303101d41c204240c0048001002e55002e48281c8000c40d034402c091b41c041415280581c00260041105400b09914040000b955a2503080c0e00318166500142243d00385a42c00c42d0446400742d0091110100340261f100c0c000d444030060001c0d204800402001054030701d004503004000c2c1e10014408182680080002c03c040617010804009481050b503020130001c468200280107440340601000f600c81904500149490b0f05902c035000c3d03d0030410040340d8008c603444c0001d5540101c01009824031340c00040006845000c0e0380200420201818031a003021203140c80707509022290790007903403012030042c2046800c0015194082140c0c503032002c011010300b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 708229775 1250 708228525 708228539
    0x40f0e041208090604080a02150702010c0e0103050907030f030512090703120e240f0d0b040e0d02030301120c080a050106150507050601050f040908130510050306030d030b040f0908090a0609 83
    0x259028001402c6c0c1000040d0002c6640d10034442c0b81e0191604001b0320792141001d840090082c485041c201000030f0030113a9500041d840307402494002e440c0c0720000d04009066850b06441101c1000084041c000300700841403c0c80b680382000d91080c80d245019100d03d03451410700c51400da81d024644d0b802c04c440c0b9801e51500d65568040505048070384502482e402e089000e0740c2616114030078080307003102004140c0c03900070421904012000c050a484c10f10902d5080b40354507580d601c0c00025240540c02c180b0040c84299441b058480d11300d401860148640360345c030f4100c20704010b0064003d55440e5100c85040c4810611042c4520b080586c600d455881c11569440d840c0d02c030f40c03040c0240b030300c40c0c11510034072102552140c0106a601340c000804559941d08840b401c540d5403118455240514054aa05e492560051040d24820640130b000f8042440d0846000c0300244482181d260340030ba40ca10481d94142d100d4401c1142c180c0c80303806419030701d00d1038008000070000700394480800c1021044040c4500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 708231025 1250 708229775 708229783
    0x1a15131701061e05210721110a15080903040f06081e130b060d0b01080d0f030c0e0d1a10090e060103120c08160b0a0c030522020303040f0e04120809 65
    0x200b240f05c0203006190304000e0200303040481c0c40d0700c01101151a00d141d010440005041562003501c200e40030044840c5407001e000e00c0c10f540788600d20002100e0704011150700d0140c046280d21004040507a441d05440c0e03421000c0f21a100e410183c0002c85450800803284003e8582d4103084000c8028004a46002c0302c060000765141c2e071006044807a180040b80b55902c40c03624117601030740c5c400d4070608550b84403c49a6602c43d4594103590000340040c401e08450381c0648180901180c096592070b40141d2490288248648034000440f05003030080312680c102004003450f14040d1403080b5003180b60034505050102a540e6580300b9441c10303040000100009183c01e144c02a00b20a1810000542001c50404061ba40901c0d55050190386480302d001c0304108103083c1c1c007449010035210410035464541003c4080303e8007201e4100c2524202e9000803011610280e06400c110310050461740750549560301c000c1c8410055000d40310010140c0184820028030500f03a07142e003402480c01070380304e28160800c01d0ba5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 708232275 1250 708231025 708231049
    0x506010206061507062012070c03080a0506031609050105041a060d05041401021603030e16031b08100209032404020d02040207080307020604061a15131701061e05 71
    0x24088000a282041080c990041091024408100d0840030303280e03030f414461540100b0380403503041fa8200000e0303031303807070188150a0456804d40d071580101e50f212071561008100103042680c0c0751041043c0803000030318003200b14001e424140004102545004284400e40b8100751700005019191448164140c03104d0055641c0405804408a071fa030311941000400158039032a080200d50002803074080d091003111040f069903110f03640030406082800b01e0580c680c400710244180d5110200401c0020030103006142081c4214a517004010980d110019071400d0312200d99885003640220314848640703000c0c000095031080f02c0d041c01c1000c000b98402a89081e800030802031150f0401800301c070a40d200d5234140c0d0320003648001d400b030f681e003810000030b03503980c0c0101d034202c951506020149000c40d583e00c00d43c003c0e0203006050001d01c410511030440d81600312400d88040e0100c0c00c1000150100300c000400203000c0303c8400042c01e2030604d0240210442c0310101e000052503d690100142c0d101e865541034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 708233525 1250 708232275 708232309
    0xc010504030f150209120129030d1409040c020714060c030d05101208070b0606041d0414060106050c010c140a0c02012c0301061d1303020106080706090603050601020606 74
    0x100c8003d003004040000e00030000c034160008100c1d1102000410150b00260313620741c494623a040008909601c0074403400c0c800129a4058000c0c00c80c0d203041c2d9009004904880d41000031a90500c0c84410200c0c04850005684100691207090304020f070111042c404e002610f0281c2c0c2c40b516003c00740c18491756134802d584403481c2103695580042c4003005000300744005056021f0f9269000030242c00c04131625000f0040c1a56600c4c001c0d000700d0120b00d00703201142e080310f8205100c1100087d00030300102d03264030003d2081d9424100d400505a40c2e00080c843c983c0a07003450744a440e112001028158216000410454140246c88000ca010310000320240c41c845180751800194013071480c40100d0b0040707820201c2030b0038071a4690f645c0c4c0d50950034041251940c0380a80003000b4a9595250800c03c29104d41c410658903907070f00300461403a00110400110072402400081441c682d2510441d00c2d003845607003c100041d522003030a10803650f240c043e50f0b8210400b44024041e41c03d00c40001050384010000e044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 708234775 1250 708233525 708233543
    0x1120911150d05041a100305121806131509081506042307032007080c0a1a06011106040b0c0a11030301080102210121062c0c010504030f 60
    0x814081400c1203400c1c02c0c940d4041407000382082c0c604031034102200c5c15520780b03030300100b40051006030821840400301c2c0d411000030560b1000740310503c5090b602c2422a500c01148001034509242c586030002c200f0700c80601003001003285401c0d16014101328058242007001207500742006152b07000240269140340c3c04403000040d84461000500420716550b000c210440c074041e00c48448401d0030f10080c0304240c00d0314184600e414602c1c941001d640c901d103040c010b242c42404810040307803c00010748961419070b012500e2344c80703042d03c0e906441d140d17400c650860070754040c0800c915964040c1980100c9400d85005001a00b0191b9803901c8034000104400181c07400840d0442a5070301c10b6481d03000c128124002d90350340756120350b0614003070741c0414010440b1618980134061000c100040d920b0484000c1c01d40ca5014070300c01c03189500340d50300402040e900d80c0d4589414802e5405a0401e90200c04480344088204400c44404541421188034030281400310a010400102c5c40040006078410780c000b0141d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 708236025 1250 708234775 708234799
    0x306070513180912030902090a15090c0212030c040302010e0a05010e0f01032c010515060a0f09050a2402190201080915040c0303120606050d0e01091401090201120911 73
    0xc2e401042a5100a0024100b5110a0310042c0c0c155001952043c0256607041480c0e581154120996656034604203103828404000c004401e216401860f0000c40f0b44103890103542042010303e49a042651454005003000401708110740e00503081d01101380040c0c540d484a6032400001a06182c9582c441034018520341d143c0711626842603000380c010b00711003c0300c5800c1142d00303021800342c120701610301c100c2c81d03207000c003c11003c540441740e03440d505030700900551500103124404c03510000c1701414a4207211030395401180c0340c2d441000c0d00c00903108030b0904429980c2712103121003024440350341c48025504840c018009046030403010b5034003d90203090002940c0c032007102152401200d040304002462035401480100807107100100b080340d0083e80d0b0710322000e442c1400751045540c41d20882003c00e80401041d0006e00c01c503040040f440c00940c000041046160f1240c024209111504458595483d041030f405c540e0080420580ca641201c0104048419603484020300180c03030345218441d40c1c1002c60 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 708237275 1250 708236025 708236069
    0x1a0f0405101509030506090109020d15090c0b2109030405120715020303180105280b0405250c0803040b04020307090c020a0c06080618060109050612060306070513 71
    0x20001c02000702d4030390812105481d071401000c00d1010f00040340c05014070404180400414010080039503002400200400d850b81c1e250790703201d90881d218000e01c2e0b07101c40d521008503622880c404020203411401980e0703201c0040209a07400da08a0140314032840c403038207019440314000140e130140da8050707642d54100c1d14107607079162511903d50301c0919103804040034941c1490f0f02001031805880002401c079404a441c0105034242c450440c0c585416182074500340014074002030740c803c41103410110000301d4102c4540840c2c25180215010a890b407004e51070704c000c0c5000541122840103c0e881c01002940b41c99440507a40d100103003000d00343d0035560000c5810340d501031242c0d10040c80302100400000c0d03001040a5201d24840c88140d0395156100f00005002d402001d2191140c40010200c4101846000c1224884c5002030003150412000550104d90754494500034405691303000f079110700314580309041500c2c00600404a00070030034144009084210a0324800b0180c910b0420500c00c54048600 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 708238525 1250 708237275 708237301
    0x2070506090f06030c07110a27020c160e09010c08040f080c0d030509070f081005070e030706111018033b030708060c04140604030209191a0f0405 64
    0xba52045002050040c0c0038614401450000e00c500080d2070908416400c00034020f07041c0c4a0130341144281500401c0d100602c0c0200b04c06011624001401c004945626520340b41c403400c81c5482030101441c061000f900f00c003004da82c0c4a81900300a025a080700c010041405d180500000e02c0140c030b40c0c1c8158100041c5905642007070f0109401c43e01502c2003210014040c00741640c040c14180144000440c5414118204000350b0302294001d01c2480c004030300c140c00a200003000d40c0d00304844030144142a0780e05000c45801421036550300402e01410f400307010704200e0591181c070802d0740352910181c40c0c00500340b03490700400c2d054200340c5072900007191403a00303040030b0440c6804c1201021141c03c0512803071201c2001c2d003030700030740c01c4500b0035071100782c0c459907a9400c2e5460044201c0030701080003220643c0c0322111030404090842c504007943ea90100e4002c4400352140791104088420030254110148518080b500001c00b40b40381a02088d4080740301900302c0500d01380140c0d1500006402c045034a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 708239775 1250 708238525 708238549
    0xf0b220f0303111e06041716020d1704090c0801170c06071b090e010507020606090a0b010311070b071e0f111e01020c0d08160c050a0b0703091101030c0207050609 71
    0x1039024031004080120740c84117001c41d4100d80c0340c1c7c0c0c4c500340a100e10b48040142e4196002d0145010000b0100c0d400308000b240e411001220004a601c480300303003000c108000b03000280100003000c903004a408101901040050300003030002d20713800c00943c00d548000120603000c01425581a580c50403641005010480d0350f040120900115110018226220750302060941410340001c00c429251000100c0e200e1801384d4500f40d00880b1040400e410800b43c0d8000420000c05040000b281ea44100359514240c01c0900d0035101c1c20221001c01c0b01d0701e4ac1213221404550124401541284852040a1300304181e04030311201b0050b61880c0d0711004001007142c0c001105420f44240c680d41e18040c40a4040e40c0700f012035500b0340c007810403e01402405400707494000c0341340391021072140e00e86200480e14501d03142c00c02c1c1d0700d5204801c50440810007000c0881d001e110303150303030100d41121241454000211b40142c0c890415241c698450000e56020500c00290788080781c0c2250740328507040019006d0f881170 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 708241025 1250 708239775 708239803
    0x1d1e06070b0c0a03111e0d06050a0314010b03030c1207030e06070f030f0302070201020a060905070e0c0324010507140f0f0303100f03120302070c0f0b220f030311 71
    0x20300502c000c05995034040c280311a542d54080c080d0703030480c0d03464161601420400c0072010101032402d48500d28144050b21207010140d80c0010200e50385c0c030028000ba00d00c0d80c01601c0c40006041e54018000c020b026040d081c40d030560055291103c01c0e09029a00c01030900680f131208008184002010321519042907910380c010401e544502c91801c200040b110031040c1100800c0c600104800c00760b001e8001d030f644c1c03550140c016041d40c0c40540c5500016104240d811100b9018a14021818880440141d80202031184005071281f61101e0280c034011881c04c180000861480b4901042d030382e10204823502c0592000042d0303008588114070358a07007034913071180040d24001e01610b80143d01c2c00001a500c80c17000205e14036604d40c1d850408940201d19804080d006070f51089004200780c0c000d80051000c07078071900101218903507900128060001580104030f0f44000054000a42510800c490440f0740025513199443c503c3c0401c510f0904501307101c014140480e101c207001102405001180e261a40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 708242275 1250 708241025 708241043
    0x4032405010608060405090c03030919170307050606030111030c0901140a0f02150c070b19090807020f01031506121d2401060906080a0e07151d1e0607 66
    0x480b40d019104103000c4684601a40c40d00300041c07900000080c0480c070b44840074004e50314160001c0144280025041014803607103404d1000000c07050b002c0410b03500e0036540ca201071a255006898030303c3c10300c00e02a1400e4480d030305020b1005050254001102c0e00000c0001c1c03081d6a0303030810001610350034002140300d040c108000c2001031b03407540c00c000a1813403084690700340c604c030444c6c2407804d80302e004082e10f100301016001d1180b80002481c0091454010f070001001c4820b4815080015040c5c2c2c442c040308030ba6041011440c803045040c07015003282c000609003418401c8003040e82001d0306802851003004200200803074025180010795006804856501d64201c580014007500b81d41c0d151801c3c1701c1920b61f007112079601c200c41c4020403142810381c1c0c0070784d07215404180303081000c8500d844007034190300380c40e6030380c081074000c40404002c40c0b0006c00e0303100440da4070410041c030040c00d202080545080d2111150821440e641d642403142c00604d401201e000d81d440b01502c02140c568056880f0040000da4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 708243525 1250 708242275 708242279
    0x60a291f0315060305130602071a0a140a0c02150604020f03010902030702120c07050915040f1512030c0b180604061a06090108041401020c010f0207060606050f0403240501 75
    0x75154105180080c211000c4011541d940d100440481d0000c03507072110007904101b04900010303420f80080c0989802000400020781c1c0d03000200c969104c06031400390031f4a43d2440d020180c01042450799510011084040206074031483c000785d1602e03400082c4201c80c820960024545680d0355058400400b2a885031503225138458201c2c200070740c001d442400151040d0900307405114440d90803034034180b6106001d400c01c1ca10b03041c1801a1000c01900c40207400c10125170900b0f0b00c0c2c4840c4120b07200c0d00d030f01d00b10128198040e42188074071104203401841c0f00c14464800b401c00700390003121150000d40e10010042090782c07040b42001c070030420a1412825402164103100901c042074000d0084100c600c5070821031030340c0810130000140f094007040f5012400c89800900460114186103443d401e0703400015142a0340031050900711028600706000c681d40c00707e5039100344100c502c01d034409400c80341031091800c0764004500ca51800f4610008004031131142880d00e0f8903821104201000d00b103250144440d503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 708244775 1250 708243525 708243527
    0x80313030201110417010e01050c0d0203041104020a030b01230f1b031b010b04021e030a0b0a08011e060e0105061c020f03040303180c1203020a1704050102060a291f 72
    0x440c1760b05c2107004641c01e007020484490f03010300c5424010b420141d005031600c2106c0341c80c0d902a403c001d0068a108500304900034094540e070004084820032580c0029038441910000b4140640d44030100c51400311010004a01319619412030760b0880300240110b03114030800b8910344412118900356003050002181800210090715030030303c0b0700d80041d8024800307540d00d201480101c0c06542d8050f120000b1044103401208215002550440024100405da860081c00410b003482000c1e030040700180c0d920309007920560103c00c5e001819030701e907501c00d0009925200c000f10903030b0410b01820780f0822000458900c46c4000d151107000c0520a10019511554410080c813202e400483e000d41c00719080072290b041c4420380c50091040d0700c1d80300001c114001d0a000b00d10707842042040f021000d5215001801010480640c0024003c034011001d15641e03e0402000a0900340c01400c0703540141e00301150071000ca03902000c82d5291807030000c40c0d4444208442d0020700f01711101c428020b1015181d0103800809 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 708246025 1250 708244775 708244799
    0x6050426251a180a05071205030706050c031603110a0813060f1b110a11040e0a060e0c0901030309051c140f0d0504030c0b07140609010203090106060c0803130302011104 74
    0x43e41011460100c51800b40e075095445000102000700300d07070080070b030901c0b104551140c0404410300031001c0744e0810201d95203800840303a050b03c0341e02c0e07080d5002c010040c1c03051170740210b40800080747c44c1c140000ca62148400010340510103000c1c0502c06094002404540000c8400b0b00703254200324280079900d1510889c00c01041c103200c00c09283c85109401c5c0032036a0041052410794055403001703051600f11038403505510030ba116180d0f80d0044c0c4450ba42150071344200b01b4010710034040c410010780306d401101c0c01413514001100350360103081e402004201081d0000102012903101b0381d0440c1002c04200e1154944984808005145000d0f0b92450100b4039070010720f84c81018587c0c0c04a81c080d450094055890f0f01030343c84010190030103650140030100819002d409400d109184040303035003c04060480c01c0003000c41d28685542e501004008214400340a440020012400d01450303840040e21241d09a02c0000c00e0702054002a140110030117100b50310010203501115070343c503100c40d21480c1004007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 708247275 1250 708246025 708246031
    0xf090406020c2b05120703050601020309040e010b040b0f0907030f090210110607030515010507080d09081e13060302092103130803090f10021906050426251a 69
    0x2d08216545040850041003190340075a5041d00003881646d92001c01c030040c10f002041ca40c1140001d001e04d48050f2141d00035800c0d010051000401c140c01c49805200403288514801c920540c100d00403408182c40e204102904481d4500e804034120401985110140c00c3c1c00200035000200035420302c1c440d0707500081e118514080d12040d02c03219110103c0032070943e00151048081130f00da10100950035070084d0010a4410f00c954016418492030036982000c80d0307040c980036204c80c230700045c081050b402800c0710318031045a001031060400da20403000986001c00c0d40507040606a002a400840d9611200a545460240350265590600320881151690003c4042c89006500c000c401b2441c02e0000c4261228207a02a0075401880d00281c00c10440b0b441c00010f0000f5405241241c00450050f2101040200c3c004c02c0082040e00f46494405050010301c40000e007401c06095064100080010881304890802070114a006d035081d042c9100b5100e44240060080442c114400070070300102c01c9841c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 708248525 1250 708247275 708247333
    0x110f090909250e151c02150f0903190f020906040e0106060504090e01061a16120f12021c0e07350f03030402040207140d120501050d020f090406020c 65
    0x95503407078402903500102ca4044140b070380091000504040c0c40003145c005149280003e250194510003032807005d605038403d0481c180c50580001d124034403403c041100d2507090000c010106c999281c06d8076010b81040074a2802841f601c0c00d400452610b40e515000800109034100c0204521079941c40041c20303a03401441041f0741c60781020404040900180728000444118030150408104c080d40b00842c00d80c01040b0381c0391241d000128000104800880310018240350b40c5640502c2043c0060103044107640c0c80c18041e106004100c4914141c1c50705000d01c08003400603c021031079010005640d070030314030183c005114100d0b036942c0110981448128194000312480322104c4140d0349030800310780b200d96506400c44d00307500c100007080c01810507a00400c80d003802070b00b1550020200c01c88550030043e40030f20000000b4407848c4030000b118014464280109811111400341510340e50116940e1040c2090207403180c684c200000c0c050000c550100c8002da4010016250342400a2060b03015014003200260 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 708249775 1250 708248525 708248549
    0xc010522020607020d1e0309030c091a09060319030206040b0c0301290d0e0d080a0605030d320c0c0d030503040b09010b0907050d110f09090925 63
    0x38a0014840080940268000d049945049441e03000c3c00300c01068100100c504031061031210000500c0ca807403241c94035100c3d40d07e491080c0e1440c04c05261414490b008600c585140180f464070161250403211410001540d15100d581d84a01c0064108031224541014452441d18004c01301603012880307e100c1c900c074100c004880c1d200c4405d64501c0780424010042150380421207181c10007500041818140c07444031baa0351170701c4541d2a100d03050340c00110f5072001990113051145e00c50794200f003c1c65031100c00c13040c04029907850000000ea03503201180d00c250901c5600c91026107030341c2c182c441510700740f000c1c0c2f20040c54894a02d01c00c0a681c1d4414000e014103401001020450741c034006141e80c00194059495074119101c039100c042c070b5004007400c004c40565981e008010759441c3c250031184030702244c1e103503c0c3e11100b00c410100d05844001a6407210728804205840890002c0d00944d0306000741600c0c03850741e0340d64401031945800002102201c200d02484001d01450b40c0310981607041d00c00300d41c910 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 708251025 1250 708249775 708249811
    0x81602070f0f0f080c03061f05040f0203180a0b06100207080d09030c0b030f07030f1e0b01020c0910090e25030312020a0e042007080301050405060306100b0d0207080c0105 75
    0x4544a8685d0034005a05810103c04a2590003004c4607212540000420b031400040d66100094112805c0c044101c107034540200070440851407040c00c281c4a150444098420350400b5515035041c01002046584600217240c0360420052080190b04090003d52003140e80c1e40300c400c08090080e007083c0c0300c115580440088049803902549003501d000b80040403a000c00d40d210300c0000d8020780300214030864003558440220188060f00518010121608071002407246402c0000a0910142c07411050003105102d05104080741032068441c1103694000700015525034030354440e82880c0c0240d00441e03a40b08610b0000c031614800d10400c0701101d109032900c0b801c0038010654501030340503070940c4002244d50380c2c4030403065080c1a041110103202c4082c00c6103090714600415100d0360070140b41170f5100d14000c1b005022a0402d80724482d04461b04500402040c5084103100d0b004002c9030040100b54400816076034500709540d0180d461712070b88891520344544201c003140340203140c1164420400b212855003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 708252275 1250 708251025 708251039
    0x118050d111002031302040f0f113105030d2d080406090213060306050a0e060105060a03150b040b0a09051c080f07140a03170601081602070f0f0f 64
    0x10301035a40300c1c0c1c034003906100225244003002500014010101d12424683e103100580d51b5109103241c840d90701030000740b941005c1680d070046a00c4141d0800c0e0419040180c8010079a0701002c0044154840c0d107403038501c0c440b2200c46030040700030307920450301032290041c400300700d42d0003043c4129040101c0f00078a1906c03251568005402c500f12000102040ca072901081c0415100d03001000c50346d0000c0d010300d110f00c1042c1c0e01c0100b264240d5100307a030714658a20a00c180d00800b4041d41d490b01d0800c1c0014201941404001000c900c60004010203240e5a540d0115040b9030502d41d10b001000c174400038503241d5503660548509a4011302128001443c0ba403c04a9180b62007480c401c0c0076a0300c80110b051100c46640c8031000c0342e000c0d04000e06d88150500c50b12001a4200012200003414400500103800d013501d006442c80300e4091603004550407010401001ea6031185010b075010004aa141101450040082c0d04008180e0004144100c2c030303642c0070840c0591403803000111600d0010b071891080d0303038402c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 708253525 1250 708252275 708252287
    0x90e060108010609060c050a0b01060e0f040c20010e1509060901050403050904021b070602010e16050d0206030a0209120601050307272c01060f170d0f02010207050118050d 75
    0x2880b408034036100e9045c0052441403481b80e01c201e204600f05c0d4205802c640b1407181c118403d80c800400140020b18038203480c00c080120500440080d2414080e0714000c0c00054a410030241a00703458035140e030a001c940703c03400d40002e81c03a490b9540590390b40c4e070703d111b800710b041e200300321945c43c003500c0345901090003100d0521480e441260180c0d80d4a04012003a01080060f5200200c243c00341c02c03c103007410030203007005e014040003004a83c000080d85203100f000c190512020540e042001103540d80e081041d03442d42e06010003400c2c1c0c100e071001d40d2555600c64220080c0a1004d00c00e80246180000e01003180002803194160f8900300c0032a5001a41ca00c03002c200c2c0100200f04030001124041800c0310824180c00c0204114044115918120884034220040d091007846003d01ca80d1110750800101180712030f103001600207404030b00310f55580c0844c0d0640d03410820b80c045040120a05031812040c3c801c2d03040d202c0181d4004020302a0640a10507140000302c60b01c01914140604550040e490303001d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 708254775 1250 708253525 708253529
    0x103180f031b020411041a03010b0901030b18040c140d05100b01030e1f0f06050117040503040b070b2e0e040830070201061202060f19090e06010801 65
    0x5101089030340d0325581c040b01c40300b20798410140c0c2c03000141c401c000141d0b03a6004030b2840260500300c2584031854070713010b04100b291050035001e24017800c100603c10240d02008440303510700c0a0901180c1c64180d080030809002c295026000d9400c80402030100b00600f0700c6c80b41d01100c0f107010300b03180301100110402000441d2514001c0003544451141c45e08403800780c000441e0700505060008900c440240f00710709080c407042451f82d10344410f071105404404a40300d40d81001458036000c00c80700b410900081d000301700851440700c0e1007100100080412204100301c0d4068800d030b03040785445503a50315001078244c20948903104024521110108030b211007041003075031079000300781400241d031809180c1d003c0070001800a07100302404000c101b500140d070040207404810010580c900a00350a404a540144060803510071641861810405400801000c441c0d00d07404441ea02d0340d400c0040321110151203203403e0b81d002c80d0a070320f011040130b603007250104e421507465081003c0c06070b9841004403a030810034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 708256025 1250 708254775 708254783
    0x2010510170d08060301060305010203010608101514032703091305360d110f0607081501030209100306030309240f02191430160b0108030702010318 65
    0xb0300e1245011a1255102030340041001d4000504681c0341c0c3c9a40e400d9074004d80141d000705a104040c0300340c103041d40c049a001420400d003c41980308c109038000304a02400690b4221040d07000c00440d685854400e0101c0050510f98050030300c01407081d0a017922034001e0703032216100325801305d01484500058040c0314410b0910302c80660001e245a2150408202c4011452050010032042102626810862a046051240c035549000743c0210b88203842c0600d03250220000d6000760381030000550700482842d400c00c0440a1b001501e15945004034000d000e0504250761000103140000d009540542c003000540e8020707a0340300d0165803039400141085102009c10123062414000c400340c401d128604582400321140f051700d0f81159800b0170f46250030000203007600c42c00040c280c8002d220004212400c1c0c02e0150440c0703900d4030b881848071800d00e80041d10030110b20b0300000608591304c040070403168034041da005522400c4d40d40c461b00f100c0d50300d40104600b02c1c04070b032a2024028103138010f04019110300b640 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 708257275 1250 708256025 708256033
    0x31002160201031d0643032708030f0c0f120c09060d0c11190605071707091514090f131109031902010207330201051017 53
    0x39036004500805503010043c0d0000c18406160600c00000e101590041010140e611039000da40d0a00f0001114000614000c000d0714141002d01c1240300011405404058240064180019050811203401d443c05001d18101c10701104000c00c83c0400181d801440000c090003200d54502c0c2c0d43d130311544100c40400103680704c00e00071410101c004c0003066901c540300165641c103010422000c07030125002694254105030b202c02c02d05040c55480090481d0490780e0340000d12410303072040c14409084510a0014210030b880310001100c250161071003c40f483d60344185c01e0840c0c5071524004200c121503000d0b4046c03202d246000301035598481c81c81c2c034400d007109000c0940b41c1507042c020003c50007441d06402da004451801071010751385040c454110310409458203c1c1e51582da0380100b41c28015500442c0500e0003001c0400c2000d40d03400035010054448604034225900781c030818507a07601c0c2c0b00406545440c6618522096095410b4020a00440207104030001c00c54842d20260f807142110000c8002580c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 708258525 1250 708257275 708257317
    0x611060105010804150f0213080307151802120102090907051801080705030115020c330f04150507020616020123180613060207050a08160303050f090d0b0105031002 72
    0x91a4020304106d0103c00e0300510300b01110000380101d2103264840d55407a000030a03414103011003a040100d0300f10700f07040c00701300100c003280401c2400081e054010b80a040000030814440000354100c9003400002031004000b0300c3c10328001030a5a00c010b00c2003200d4001c142044650f54041c1d0308a42c05460a030320340d00c1c116030901c2404d40071464481c1d240300440c400c01500d000d2540300d4080326104009403542d10200c001d0090703c0e40c10050031181c502d000343c140410008440d444c905003a1026559040115984c40140303043c101c4607400780c110302a6003c0400076000814021800d529499136100f80ca90003c02400d102c652812007401241141ca0755008000c1142078001c40b80003084422002070a150514a07040d241c9071a0a42e580c02110143e44400e60501c181e113400e51080d002402801e004084010141642c10210241480014103000c00824261488010101500c0c1800c0c40603245070404c59080c1801e102103002032007098040c0c01140102c81003108140200d40362039031803505139500300e2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 708259775 1250 708258525 708258563
    0x15031103072601030b01140a08071a0417010f0f021908060105040911031b1603051b01051303031a0a0513020705071502101e0f020408070611060105010804 68
    0x4a612590103080c00540640c8060b45880c5065042c003031400360000524560615610321021a01e24100c2d503c1440d9001c070400c60540006400029195145102105503808503810412030007142c0042102d600d04800e449240c0c8815884541041c0b10304809002e55244001101c0c00c070310800c0440c050401201c0700080d81c07540202581901301e401858400e05d417643d40e240340d20888203590754516040200000780242c00320041a0302c98031544e0440814940030846400e804010140c0b9401014088045075070541a82c18a842440d6500e1400003400f40380341c41802c13100b08081614041b0040792502030309440340c0f03058045c0095188005091203200358200410480790b00b081240700486039408104001c006503081c0b00100080c07000300e00d02c1415a5003420b0190402c1c11005590340c3d124a080045c0c224200760310061210076625600c0003400145d99410b0300c000e8841c6d50402c10700741c890040d00286c0e46a10010601c03020741c60340c058914607620f400c01140e8806065074040c048a44105c5580100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 708261025 1250 708259775 708259787
    0x1050306010e09090f011404110a080d0f0203091002010c0f080907050f030f010207200d1e0318080c120111070b090a05070b0c0d030b15070204060b040e011503110307 73
    0x90403000c94108101d03407140142034801147c0341d6000b0b003144400340400c2102d250420175900360115036080b005824100400e5550f05000003070b004002c2e0800b00c2d840814024401c441c0007001c003400746040b10080d40ca020f0301a04201a001c40010007880106040d01d22440146000b1310300c0d000039008451609041007004041c004010b40e041c0112442000e00000c244000c0003074a10643c20f080081c41c00344100c0045050385004940100039201c0b80b1000243e69024240d440200003103c0d60002c0c841d82002c582858100303528010480c2c0003003010032034160014442e54510700407103003181c4201c05544c0c014281c4080d401c000c0c006c41828001c00b800903101022103907020003240f0841d13403030386410340b50300c0d290808560010310700b000e00282500c1725000901520144c2d02050a003806801c080130b000c030b0011000c0501620900001080950841d6680d4001074010005809119215616007a000454507820b00c68155244480c5000128030350082c041c91003c2081c0c0b10200d411951000425584 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 708262275 1250 708261025 708261031
    0x1205070927020408070e0901110d050702190c0906060e0609061605060703020d18050d0e0604090e010f06060216052403090c0901061407060c050412031d01050306010e09 74
    0x41049404001c426445a10190008000e194000c0c000c5624040d4a0041041c1c041c1c203000159040040e803d00240d551405c444e00040f2162001415a4407804201e04281c054000a212100c00301003400c24861034132441015200b07040b108000701d0f5900c0c001600e0a00030691004c0c0c02c1581070101440e02c0c0341400c068901901110340480d0411265502d060030190120750520100b54040355a40b00b01000b803154600e0700700701e001848500c0c0c20f5902c420b551694400c0742c1c0e004100e554000502162600c02c01c2c3c3d401407500c24403e03c8101c1d26090841c2c0030f80005007501ca01680b0300440041c3c060310001e4042501146520701c0080c1505102c1403018900d03000104001205183ea450f00303940c4a0080154070641c2600058080862418104120b410303069009104101c094035048443c0000c00c01101c0700c0607800480080d51114018056403507015503030011000c020315070040c3c800c1c9504807242c1c841e5150030000a04140c0e407520010f64080c0010b80348a0300046070503030f0030311950416103a0160 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 708263525 1250 708262275 708262319
    0x306040c030b09032b200403110d0b0f1f080703210503070509010201110309011a1009060309020406030b0f190c091511010501060507050f030c1207061401030c0612050709 75
    0x1402d0a041c000710a51941b40f0f020641700c0e120005420400c1c0080f482c5d0281c0c50110840e0409040f100607180c005103203030040d010000d44680e000c0072409062458a200103910660000b013103107146c5c1d4452164694001d8801a61503000316600c000c82c10051040c42d030b240d07a2141d210281103403100030b0f00702c030541c00c4040281c0c1990744e68113203071080b412807002541c82a40300c00000302e504506190448080b4582c07138240360280c1d02e0407900100054000c0e47c01026117000380b0740080c1701c511500000e000307840c4a0b440a044841d0303d10500115074002181a0320400f5440c020b0008242c0c200301902c200c8009051500028034a01e40c24410b41181c0340003010340d102149081450310348603004241c00c49400b82c0c0f204c0081080014640100300e000c0c8010401c90113020055400d201c5001a1103886000c148070003071142c100021070000300811584001030b14141c5100030681d640e140d00d0700d80300c0c2d80d14500504000c14240b0008082189050041511421003659030921745843e040298021411040443c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 708264775 1250 708263525 708263531
    0x81b0603270a02031509010b03012a0903061109211c020f01060b03100609120b041506030b060109050d03121505060d0f111213020f0306040c030b09032b 67
    0x200542d40400030701d06050303060010380c03060781001c4201e1400c5030088e00b0818040d90400c0601d60180e00e03412415404452840c81e24092003111245c111041c44c030a40004100916115645101c4017110000c1c050910050341c8050184451580724208400d5000c3c404d822580504e000013203464240b100900410304500444801180340c106490a4803500e0b081202220f1021003000b440310300341036684005040c01e00b0701c035070020f0070f00720085107070200c00c035010b4401d5080101117000c001c1062130301070443c0c029580800c40151207217444e9240604c190f4603280010b40094000c00c1510300450007440c0e260b4180c4560a0458a861500c2c0c05014003a02041590140040002d0aa01c0e2000200010303401004006500ca540c0d0865404450301d00300701c0b19000c0d0050000b05010881d00011940000132020301203006c0d129440041c80c201c8200c444150140219401d000800110000480681e885139541307071017550307800b413160756a8000c4007000100f403116441140c03803818a076444103041c90308421007c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 708266025 1250 708264775 708264793
    0x50304081c14040605040530070507050307150801090b06030403031509091a0a0c090618150c0501050601030b0f010e0d021801031a04170306010216081b060327 70
    0x1d075015a02103e0a60710144c0b50030420007000400c0c40602203280c100101d51003400904c90b081d10151810b582c4042e02941c00081950510a04003d40001800c000301182e0400b42c5842c103c0003290207440c0502d020a03505000803801d050b00d40600021564060300c10b1781150341d203072011005800c00703d00d040e07080151030350042040349241c01080001d83c0030f522009481340c1004e007000007201000340303500001807810001d060f58540c020302544c00c03102030303142c0310018182100c039410300383c1a00e03806200004444401030582c80d406c55004102180070b0f0008004942e100c4005500751907401092650000c40c140d00c012996004036114a6040070143c00c0d613038040c2039130340272074a04000301c2d0380b421003102c60400403c2000b280b2203450b003c134a01250780c1c10f103a01f00340e6618040c04005a244000b8108044001056030b4401c20458162104071541c1141003a620b000c0b0030b407174440e681c19400c2010038420b040c0c8410f0800d42c0031a80100c42d20100301c414524003072001c1030103466020b4641c5c400d0040d80c501c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 708267275 1250 708266025 708266051
    0x203070e0901171213053a060f0b0306011703040806090610060c08030c1b0a140d030537020d290907080a0b040e0616050304081c 57
    0x2180c080d2110360384600e0118103e01c402464001c200c40390780c501c0c2000b00144000340303a140d44c20900b214001e076005402d03c0040c402000e190890311510f0b900d5074983d0b6018a0807040411010710b0418010b50040000580c0e208041c402d031104590116010341c040001084554401c48403a07522110317a4054030b0806031154819820023906480d0307250f1a9021030700380001032403028070a400500e01410141010707076182e13990007034a001c003c0c50940d00400108103030018030041d01015407250303140c07000e8a0341001c99217030034001841e130501520941e12030400000d0440d8060722443c1e014103120402e02c105000002c07000c1e81c4004003000b0000450302c2541d0014201c99103070003c2c0c00e52107a2000c0c0070900d058044e1990780e5211501210702e502c4c0c4c03401d45100c6c00b00e0b10350229a6401c150180380004c4c0700e5034ac28003618007801c285c1300f0f056040380c5054001174088101044203400781d10005503550041c44412800ca071030780800d507005440030200704036103840c0c0a221b844019802180b01d8001c00c0c1c111005d0300d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 708268525 1250 708267275 708267289
    0x310150201140a0c140c07030f06090b070906080a020909011404021303060e1009020d060c030e0a03051b0303010501021519051f0510090614161b050105070b04060203070e 75
    0x3d104115036114000c0d502100e41007031940b500990001061414400c104d144203a40d04203502c40608035103800409101404460b401c42c0c4c102c960070031034050300360405c4400100360304c1c4c0902ca102e0018035000d000c110014402d00884a0042004042c2c1d55180d0034600500210060840355990040d4200140d001c02048903182c80001d41c004c1e5000180c081c0c43c50185400d01312000600c0000c2c9103070442c031070016a543c1e5502004642c1001e00002e580724401015002811400a8860240303d0720441c14101030f807080007081203080c00d011040340031101c509402e960f4042070007100c1c0560882c030358030a09003004a004507844141c1044110000020482c4002280c0c420341d47c24000032110242440100700f2002c910004000550b100b28214140040013810440036004841c00c00400012410310301034030809851b441ca8014a5035a422a031502e48403510100c0181030705000741d0312001c0010b0560080d01952a415000308881c0c40564440e6140300080d44002d00d098180a4591681d4000d41c0342d01c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 708269775 1250 708268525 708268531
    0x81e040812220605031807030822051309020301060905040503091002010605040504080903010e0c0f060c0709050f160203070807240e0d020106050913020f03030d1a0a0605031015020114 81
    0x916419030b01d0500d08019400c4c00c0c1b440b41400c0070303036102680401c00101c208046a1428180000c0d1080d1404459140c14152200f680040c1d0300c1045881c5c0381c84802c807035a003d070031142e108900821203659034018800a503202102d02a0242d002800b0850860800c1043c1005501561000003103a54a881c00502110804d80d02510740000102c0d0410340c6080910800881441d110010b000d0904c070300c4d000a4810b12207030b48880c040c02e408640c500c0100320400180020701583c00d030501c6141340c41c181c04150803608031030071209184100721244038580017000301d03180345800540f003a140c41526216003078103450701d20300455609440c01ca6010070400c3d07446602c1140c11404007820310300030105002401c1d1490740c2c020038410031080c0705010200c400f1002040f65280e058aa000c40520007000203030641c06a42c02c10034a60f403d1191006080e194001044082c4108680444005031110303000c50b0b043c0000c6610400c0c440304010f041c043c0e908028035407000c10215100110380d4268079400b440140c1c80c1a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 708271025 1250 708269775 708269777
    0x70c083901110f15040312020c07060302090d0b011d060a0303050702010305060a05090a060e061512090109080309070302030709140402090411030f151b0f070c0b0304081e0408122206 80
    0xc81c1c14081010303401020004d90500080b012340c107001102c910940c035044288139903402d0560006814445413501d19070568650b400c8030011001c2d42c0d41c1c40007000328807809a20045414503403000945039150204056041e00d406039140d600340201c5900540040c0400f500b416441003141200080d80c0d5203040c0340c0f40c45421250b0010030424908900c245003880f002c7c110034420301500c480200701d1440352040d50411080460340d511107480e82082c0340d006000103400139050200020420582040002d078400440e40300342c0889800c559601303001402c60784403400ca0291852040c0c04100589003003204150018014000090007900640001c1c0c030b0840e4448034503c5a03001000300b8403014480712151980002c61613201795554445d400d100000d4030440d0f0303484064180c00b041203c144801458424007401410b030076640d82c3c2c10541400b44454010001c03681040e0b000040071104401c91000341c41c1102c030b400380104900b4104010010745a04910300d481d403034205100306d00a6005a00359184014440d07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 708272275 1250 708271025 708271063
    0x30408070302060612030702240406052107120b01112401051203030c1303021005090306060a180b190f0f080307030f050708070c083901110f 62
    0x1191030083d04045000b055248642e006251140c040c55010080b50102c50303040300d0200030f44101040020410038808090450603070041800b041007a0088000d01c00442001480d08000c0c01e40041c2e11b980c4041100c034480000d550481c501c2c096009600300103c410342c1410300307000c05803079810b80c14a007081d0015015039036607030240d180c0400d0303107010060b0780581010b445902000d0b0748403034002e54a12016141c4017621400003003c03e000040d448a1078090365004210f1584401c1e0380500601c590400d075000b40c480e016543c0030540300d181041c0d03c02d085800302e00358400340d10245c94000c40100580880185c0001c5030300c44081d000702100b4862009000c40c6403004030101c0c1406200380b6000d480e03030016022030f4010805900840e40000341ca418140700c51038110f43c1d4006901e03101e00c0e50701500c0f50082000d42c00d950f000c120f200f00420148101c98031400c2d0b010281c0490006400d1801d510103085410748680168540554454001d1541e50100201140e103c00c1010080d58580301f10310f0a11b0540002d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 708273381 1106 708272275 708272287
    0x8030304140a0515040c0e04021f030204090905060901180302030405100c021f080606040614250602091f021903031b03050910050f010e0c040b030408 66
    0xa488020b84d0f9a50120320744452980030290703000c0740c110306901c01c0410502241091640b040d5001000040d403078120311092340c120316500c1c0500f420580c00300030101e800b030320900440300f1152043c4020245c80c44c11460080c01c42c0c0014200d00c40c0c000082d051100480e50000a49050303c0c3c00711200180015074400c16220040d41035002904000011031049210f12010b282c081342c07035040d84405c5290342e038903c1004058440d9004801c00b0400710000b201c0c0d40d01c04500600300598044009801050351051041e58025a411303040380c1d07603500003550401ca4180080300c1441e0039007410250416410441000e034981c20100009800b00307403079950342c00c10315100350007010f180c986494810640d020452401006400100c0d170668017482442148280c0c03400e2889040e105542c0c00400b0481c0380d0034900c002030a080041c1c888040d800f814400403441a406600540c00707944100364140c0d40c1d81d = true := by decide +kernel

theorem cover : BRFrame.Cov 708093525 708273381 := by
  have h0 := BRFrame.cov_init 708093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 708093525 ≤ n) (h2 : n < 708273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
