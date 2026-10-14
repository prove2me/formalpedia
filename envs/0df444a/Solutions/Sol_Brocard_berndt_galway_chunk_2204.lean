-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2204
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:59:11.397125+00:00
-- url     : https://prove2.me/submissions/b050fee5-5154-4050-9d5a-3f47cd62a8bf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 396223021 ≤ n < 396402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 396224271 1250 396223021 396223081
    0x18031812010c0905090603010c05041a090d1511040b0702130e070b27060a0c031e05070c0603060b09120c09091006060906090b0c10020c0c12010207030e09 68
    0x21801400c10708044c064607015900000020301c1d01c0c541401030b58040303c07840c2c0b6500c2ca000c0c1011a002090000b0014400194000b0000911a901c607001507410041c0200d18504d1016030b2a24164240c0e0151b4114507000c0000348014811444020201d500c52a070486000f030843d080205204050302c84910a01064013403c4800540410804018600080c2007181799102600c00055030440c07245140005030449018449040c41902400103000503d02130309201c5030b50803a500514450701c544287c4100091030101e125000c200094950502500c070604084c04010308160554102d405007400d01449400d8480c0b071100e4100c0309100743e079510000641103811901d0201141e40d41d4102c2481920440380c54000002080fa20541440042e14400e03900c2c0c0c841c00c3d181c0400807030603070028000390300240296a88041c2c2903041d44000c001c00d41c502005042074086800400090280c251441403199004100a000082e80214040742071941200c10981c5c5456480194a6603039003100c1048011802c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 396225521 1250 396224271 396224291
    0xc1401020315040506060a0f0c030302130f06020d02010905030a0e0409061107031805030d111501090b0a0608040c0306050405191b1409040305160501110a03051803181201 75
    0x16428a180c02e04250742c148442e0b110a000e0184901c101c0003078100150745000c2c14660700348907410b42c680e0b441c0285005410020302420190501c074066000c4c00000711903ca04024858041c040142048000c0c0020004d284480c1c440c2c80e203e1050381d0308c0b41c0421000901900c00c82c1c0d0341d0750080400a402c480f04002e1500b00005164060380841d5055021601414404107140f25142c1d10000f981d0703002d4090000c10014150070354002e2004000812035005030312400d0103901d01d201986009090b0303641e000c51103642103000d114003403000e504402e04112a840c10000420400700800e41100d40c0709500140a42c3c840c1002c5040032110300340d5884d82035002680c2c4040c4401c021070120005140d103a80b000f401d5541c100380c00c0e02081d42002a40002d250030000f80820300400151003003c120046403800c5d4025075031800d08403040354105908800c07001c034004096030703407603c41c45a02c590b02180012440d0544a9020340d40e0045882102884204540b038818545501f5854800503a81c88000c5c400c480207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 396226771 1250 396225521 396225541
    0xf0f0f220506040b060f1215040303061707050103150e0c0703020f0a0309051305071b02040b0a08151315090c0308190e03010c1209050a0803070210060f150c14010203 73
    0x2041d61700b988030b803c45c0f914050251520f102200c07030710203190300142901c0801640c0c0c141d000000500c1a01410750b1103500185a010070030840b020494188040c0c501c40e403c000025085460a00c03c6402e444078202c0103101f03544201100c5601f10b40e000c1c480a0f240c411a2500301d1a140318510071003002d0090701c00c0b010401d90888090815507a045486407844688800340d0000c0b68001c4440400140315150b01a180d00b044d4517158010a002800102e14a501e00b40410421451540241d400f40c1c400305410391001501802150020100050410700c0481501d4070381440d564103400c05000c03940d4000d840c04102e0140740d05401103501c94445519038003401c00d6880b036500d600708944081440c5103680c4c00d40d860184910308120311151220f800c0c0c140c500501e03a00500c04000125424032070102441c0c04691b0a8014500c074441c02d9004040c40000502c1250648002c3d901504210581140600514200400d604910716031407030010410515030921070704160541e85040c500d07504c004140004003907 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 396228021 1250 396226771 396226793
    0x71205030103110103090f0f11220b0a080327130b0102010b0a030b010b0a05040306050a02090307080a0521070c090b0f090f04080306011806080f0f0f22050604 70
    0xf01950310450011403220041d401d445165600a010031402c1e0a55800521815480304401d800340400b80001110003012542d01c03400040e400d1442204600d41c2102c950440c0640903069200381c072002c40700c518004071640c1e680100030b01249040100d2051703a000c5003e809803401074440081003500b102c410503480d80c00500140580ca801942840b4002100b4209021640c0c1142c3c1d0026428015a1803d402d03a04242c125480100401c50200400404112503000701401202034050069030b4249140415151019070b6100080e6500708420301c1012450218006030001d1030320350301ca002c180141122128034030034018018a400300720359000c40c030509594404500c40360160f901c0c011403030100c010081342e608216541c070300e682180c000213000144850013541d08038406043c01c0c2d8000741c0224548011604ea5040103002900030000c211246c0c40e0800c1040d04440100c6000309107040c1042d441300c1106006081e500b4800103c070b180d01849400c002004070041d00602505c04a060910300001c000c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 396229271 1250 396228021 396228023
    0xc03110a030507060c03050f070e0301020409050c04080706171303110f0604030801211104140c123108040504020c030903010b0a0806070c020402070c0306050609100617040503071205030103 83
    0x45d00d4120007916460081c8101401181c90354103d44150307481c4d40084964090403c000ba0b015502800b0015111240c0e010f40da00903240507181e00d07101c0303080c844900c0c40c004680d841741c41002800c080c11114260780006031a08036200d0642025000e41c242410303610800b0925540503140306420380c40840f40c03404680f0b01d002c2d41c13103507450f5140340e40d0f1400b00890032661240c118110903004031030038000541c041c0c40c003036002c40050401700303a10410703282240704a00c0c2220704684140c030000f005d101c0394030507002560703003d8080c0b060809107413090420b0102c40c0350f58510118581e076455484034288032401c2e00755001000c00070020340d40e685500a01d00d40702c3d0002c0310018000c3d801c00440c8034580c540915070341e0580f840480109415070ba000011689400001c0e01660001d50801892001c42c000301081c0c4080d40c040c0c2c901040a06154080c0001c28100412602c0c81c1e50341c4600a110b40c0758400191202290501c013140c105840d00c1c1049800e42c032034490001d0650030130076170f046030315034024019504072 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 396230521 1250 396229271 396229283
    0x917030702010c0e06040e09010f11070b0a0213050f040b13020901030e15190905070b030105030607090b0d020c031201031b0e07050f0705010b04060f0f0b070f02010c03110a030507 79
    0x903c201c094155a407140c0040750680c0000140414480c0c030b4160303040158407200324800411340b076510341244022244501203030655510000f03808410721003a65071203500070101031021072421550400c44040d0942a0007040e20544c01800102140d540f150040080c500000702403600f0303a6049a035420080d840300320b0250100307003070940c0001600d6020802e000d0902c031540c0344003140c0e61030340c0d203c0401031620610280b1642d50741e02c0c0075005c02c008105080140603e071919640c0d0394144410145806002407080040088001c8184886140b136010b481080e00e40490158aa4584800003030441c05034403041d2107403020840000092002d402d00181c00a50b0364410580c80680700d1800d60440070049071500041142001040c404405500040c24424081c40000501c212100300007415a002640400844516a40d040c090a003001050a0041215059042c9001a281c0c1c409000c81c04402010781408000c40c1c0c4881414000d61450b0361000c0200d003682c520659a150203883c0d60051002a214 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 396231771 1250 396230521 396230531
    0x501020d060923220c030c0b0a0912050d0e030a060e0102180102030a0207050915121b040c120203100803030a0507020d0804050c190b04080a020f01050906030703020d091703070201 79
    0x10210646101c0e40030f1000000901c90384420755000d02d10814441342c0c00c0751764214089001000c100480080806014a00303000d070b0b50b594800400400f03801b4203404c403c0300f45a54200900001d0400120f0346000030460a005c0d0461124000003805c240211202a004600b403100080283d60b065005020f44000001201e0740c0100e20310049035280500da04000140e44840414000c40c588039640541c001c1010922000011404020588100310a24400410ba201d05108080500c0240300e4110680d002d44082115800c0800d00a20000200311641242507000011400701c5039061400070292901c04100d941c3c1303043c5849010024038044804000601800ea51140164450103d060155800200802c2000400001c10011015403800155119402038001a5810412000c1d01c0101181c4000d070082d00c04d18018410080d4405c030307856042101c2080f04072000d9403814141ca820103400c1c0350040c0c071503d2049030750000385a07600c400b5260100c0510b0714043c0c00c0003000198468046503009002e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 396233021 1250 396231771 396231821
    0xc160602150a09061d0a030e0105031618090920150403080313120c0b0c0f030711012009040b240a03020909100501200a020d0501020d0609 61
    0xe207801c1484120105052040003090307440100360001e00343c0034000c680020301c1c0c01c006425010020390200710207003942c209a20010030b058004550f5a407501003820300d140366141c035525040340d2034480144107040c400800003102040003851b45407009445441c0b01044500f1203030402c4d104410322000c0b400c0701010682c00410441c00c00360034400d107008080c6e000e01d043c50306682e1000c5140c4c200070009035001003160b9200300851101c40034540c1d2680c498403841c0c0c2ca000346051603101c8450050888180d56002c00480d018400c12008070380d807195051070403080c90040f400c1024007602a0b45058100042c260706901d2512944600510080c2011101048030001c0302043c00b80c1c131007054401c4010000d100f2664824403802c40d00502049079203241c01890850302500040040c40d00740c40722000000980c00a02c020750f0408000c0641d1304440d00040c01809060120329a03484400100a00600c80c042e12541041025010303100741004061043c0109501c1c1d0036910010110759100c40307082c0c1c8800e03107024 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 396234271 1250 396233021 396233023
    0x2a03070c0b070c050c0d0201020c0a03060b01020d0509030a020907180303030c1b02090f130204050901050402041d06010605070309090227010302091305100506040e10060e0d0f080f0c160602 83
    0x1800703e0b5400b0000e0a4200d5030001001200030300c0b002d044c0d056010380c000d802007554920141001440c8903810000d0081100c00c0020300d0003141441c5441400f50130000906103590019403855074a50448210311240c5e100b0358126082c5643e020401030841d2915408420903416801c031200030601961000b0016010f03000c0d050041d240014081d410079001000300e82c0200c000c0003420350000604604081c045040d5005ca01192421101c0410310395450041c001145064020100d11520b07003040c440d0481000340640361116810f100d003000384607002484400f00f41c0070b0550640184489a811500c400302c01c507403142021030f50314241420394400040384501d5030083c801d549401a0140461043c5441201e10130000c0c040503140c42405c640c642c0d0001000ea40d610000c1002c1c100c071102003880750605d80d0140c0380340042c940192080c440b00c491140e03800e441307254a4860740d40d044081d1082464581c10072810622426050a890030800507030b078032904900051801c05100207000c08002107649200072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 396235521 1250 396234271 396234287
    0x7060e0322060206070801290f0403050106080105012909030109021804030809160b16050601060518030a02060f0904140903041e05060301050112180b19050105092a03070c0b07 77
    0x82011280c0b41023801d814500000012401220b201c2d40c5910301005401d10305500e42150744101c5281c0e4440c1002e03c40038a082c0107450042451144038484203d203030040004074482a00109003c02000c19007000c50b0303809410034201e1640180c1b070030300140f1442a00e80c0506008540a5003c21414404100c29040009485208494a4441c10f00e140d00308900010b06520007400e5841d46862000e8120210304207020141c02401141c458a9885110001184400b0464500346200f6001150a080035031161021209850000e4012580c0e03031700d48100140c004d00544125644542c2114100066100008020310a6400e8445100d04103011150f007081d41e080035001d09500100c040c0010807003540100c0c40e4114074410f4a50108800c00c201c419001005508a0b094030b060fa5103d047c4100d10b4400c5c03a20309000104500180120343c10100803905100000e070114510b00d088140320110223100d10361100388501e00100d181d680303050401c00141407030305130f1a00b0341e0000c121102007001d490240401c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 396236771 1250 396235521 396235529
    0x70206060a05010c080c010203090f1e06040204110d0903050d110c0703020906130e030703030f020c0604031805060c010b03190c06030f0608030a03240b07060e0322060206070801 78
    0x708400c28241030044036802598a421075144a040c400800000c40a001441c0b18002100043c201720b03800c0901c2030315001c02002e170380d10004041d50340030501c5080466001d41c8260151000b084034000c501d854009031050301130564034070307241003221010190300c10014070119a10b50800e201c1140d0740382040089110390b28400b0760a501896080006007005000b0384d900840080490704503050001c1400280c4480f140142d03840c0d00006251002c00d41c040c880c103410340c00070705400c6050240031480c19607220310251000d805d0022860000c80c2c0c040f00f059001014090242400e510341c4440f41c40103001e000403412052190080b001c6807010b01c416819207585c00b0303401010007003c40b03180500640c01040360f0607804a540381c03101d10214440200700024a0003403481c1e980040c0b40000003041019000159541350602c0408210410908050b42c081da440d070798126000060031000d140702e052552141c0b0421342c04154660300d05881d8000f00d0000d02040b5860390302950519540d80404458802013401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 396238021 1250 396236771 396236779
    0x20f161208150a12060b03060112021c030f030b03070f06170114031209010207050a080a0302011103061e04140403080a1505062502150705120f160302010225020907020606 75
    0x1042000f19130000c00203024040d64000071036506035408242003a00903041481511a40da81c400c0450402180d445ca005103d5000620500001d80e801481964507103401c50400d500c0b0301e000e42c0e41c0c1d50b00707003c898024003022240b400c0c160b070f03500805000c00b003000c20003c2e0011489000010100b03200c0000402103480140070b070148003030b0041d034181e490f044003c1507811403061500c0810540c5401d01107074060080b620041c07480c8126450000c1c2541c05041400300140c0d42441031195945072044840401440d000c0c1c07a4104542c40c001040090440e00e0014400303840d004c0c280014503402110003070080241c8a8284651841c0c00d80042000c5140d1080e95000601005084002e00320040b594880403081e4080f140110f11039000200b980380078195210610034000340840400c0010400e511258050b0742819040180c1500040624000c0f4041c6d0350500200035001c5081620030350403141904400d400258441c12545000c11000b2107880c422801101400c005c10751650001541c64443c1c42c001b8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 396239271 1250 396238021 396238039
    0xc040b1c0e010213030b090d0801140402070804170f19020405090a0213050709091a060a110a061a011d06090310020313060b060c030d020f16120815 65
    0x440c050800550340050100020340e109030381c5101da6020b00040444211201c0348002d46400c43c14000c220800c06401d80410b54002c01d400e481d03498009a01e40d0440d000c00741044010071007040801c0191055850040c9030490014002c20f80d01c0c1e5000341aa4030f062640125000005c080302120366580e000c10054a0303100c900c08103c40103103041d030070045e8400199001d4401c0003d117907001c20401c03c0700e00344100140d6120300800600a41c092142401411030710400d105000030311491031608556a00700324080d4074001038041c14107024560710038100b0001c10445010030351608040b0018030f11078080c11010001d45660616075072080d42d00d01d800001c1d210242114805140811429074401c011007501405259640b0926800a102452155041072401c0c3c829183c5072070000c046440c00c4030011b21914041c440c1044981c0e000041e80c0c800740d103e110050703942c1c40702214015240582c2c4c003514007141d8a07009550400c84502c3d4100c58200d800e4581070013544584403510300141500c00c82d960003803048 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 396240521 1250 396239271 396239287
    0x8030a020606060d0f0513140a03052709090a030f03050108060a0f06080d03020c060903120c03060d15091110050a05070c0e040b16050304111216090609050c040b 71
    0xd008007403280500f130b07000421050104000003a914112640030005040c8001f0506021030380301400c640711500c03000b415410100f690b020340b0380c1c01080240b50115040e000b50300007030910150400045100105000761600e408241c96580c0c07400c6250840004034242106640d8074000c2c0181c90685460b170f8041d11305640c40f802d1000c000c0501904411080b0780b2094000307107011040c4006140848a40e401580c0c608030315202c245030100150504800c1d42c0100951000c02c000d101c0081e800c403c0241c11300b5601c1c0c4900000400d03c25004101400b15180032140020810082d4403c0980038407501c0ea1010701c010301803c004409040c0c6180b0340215004200040c8658031980082c680d2510030440d10319060348804041c1a0325104450440f8140380300802d0140c28040d15244019800749840c1041c42d5181c1940e0303400c82c004241c01c84038081c03101045a400300032000d105c0e80d103108068ae80c42000c90341c0c0d6400d011000c0c0009105650341e60b4640400f04111000e004104e400350343c4e00003041c0745080d0340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 396241771 1250 396240521 396240529
    0xf1802070b0f010819170901140a0c020a1202100c11090109023105061c0c030c12090218152812020a0b0a1b0b070e06030f01051c02030f06040c08030a020606 69
    0x326124440c100322041c0c2120320766a0070b40c4090580304180c3e5032811214042d81c0304dc801d001000e50030940f6800a0001d40c0401070742c448140021041c02843d100020060f40e1814a00c0c007250080850762108945001140b410030702e9024000115007158981070100032118248c4419069968446204698050602c03160410000402c181e050f5048118100301d44402030104a0f032084540c040002e03150f06038564015404950320200056840d010083c4190b1a4001348000c21144020301d001800c00300061240d00210850141b51000036180d090054907112081c60000c1d4184091814201d000f140882c0602001c80781506503540a03000c200158204100028a074003c0808007081003118143d2411028441d030b04240030a00c224040000380c1020308020740708211840f003850098506004100d40404624400d504441c000e03200c1c08a1710240c00c5400002c01c1810b40d004e5010301c50080399101e04040001d00620890003019200f46164481c01f40070344901c60110b5500060780007a022419511b8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 396243021 1250 396241771 396241777
    0x302010f0c0204150f0b18040b061c0f0c0509030c0603180307050a0501140402060904090201090915031103010c050d0506030c12250f1802070b0f01081917 68
    0x109400d1411180010340e0010302507a110104c500d005a00380f00c02041070609007610800600700e20100c40d03040c6070302c0c0003505c10340340c818200e000d2080b1386510440c2c0c03043d120b4004940710340f42e20034007150346184100c40c000044e0080c146d00401191800304107618440c0b0500a0f1122408010040c125002d03400f410045690009022075917820720b80341100d182040b00308000d211251090018000078040d03802c000c0d00f1520144002241c0201c86000c02006039550300498107151011200040c018410b0300040360303445030701d82001c8031082c500302d0743c00d446502e8041d0000c00c4900c100307101602e072603040c0203160903a20101e490101080e01400340c40000f10176600804d51202005d000c4621040349080020b07404440c40d040944250448038100c02648150070720040380503100c1040d0354141385000c1021a09014500c0307100002840441840c0e003a00f1660112489560403850206075802e0030b0142c41c0120b0700a21445030244615a031611074401e030b0403c2800d0385900507034002c40104450441041980c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 396244271 1250 396243021 396243047
    0xc01030504080f1c0b010c151a09090313050d020904080c0109080a110613030f0f030603061d061b0304030f030f15050a080319050a0c0b0a0b0114030907030201 70
    0x80610105000d0005480600742140003451800d151840402214089403e0703c81001c1c10400305002a00201c8c8a00b1191061606403c0000a4034680c158030503d01e840c01c4d042103603001001405211141d20004094211460003010100c01d0310b9441e01000321102d2040b1000303407c0014040050081841a0058038486401100204000d040d90303540000a51000240d81c000c25800100e1021180c010000d140d4807916a8076810700d10031180d1805402e901605c01c0c038904000b0f0080a10362460311907000100115131107041170281d134903040503c004018000f0780d64880c5c1d20035100045c2ca108101540d000440d60103128041c915211620101c808468166500c0140740d01c0f59030b43e041420143c0309003800318007030103e045811810903040101801840c2e0060b082c5a0092015018024603084121000b003c24101940d4031440c050082c3c925845130000502030501140c100f014104260b040180060426038980e64480303e04060101c8900060743c6800c001c1d401140700740019401518989001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 396245521 1250 396244271 396244283
    0x50904081309050717090c030a11120a080705060f011203030c031107060509011802280f0306050601021006031a0a0e0d0e1003050108150406110406050c0c010e01020c01030504 77
    0x289888450b454141ca0090700c020000542414031080050340c403603007440e0080e540348064080c0340c00e550006075544401c540c0183c464a80d2a401c81020354070f183c600c1000b0400f02c03056580c07231800b5081192098100c03c00560b000d01541c00040c07210782c140804103050714015a01410781003140c0c2c600b28014441c2140308028195901c08441c2d038140c81e94046e0500c0745c410000403400b8984140d0030790941d441ca504103c080c848041e800350041c5c3d100f00540b03031251031309510008086c0c01c08800c0c002c281c0c119406080151a141c3d000300500c40d654010500c00c00007070b0215184404a05091400c8400c244400340441003040c941503400802842050340110a004020400303e0100d590310b8242075103401440c02180c040c028641440c102180c801e200500c1c81c0c1820412503142025107600d502e1080c0d040110854030400240c104005036000034030800c107524206803111303180e040c064129488184400c640303208684041d82d01d9841002d4103a00d12006a016200182c0741000540c040d00014100b2560 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 396246771 1250 396245521 396245557
    0x5030a0f03031d0f07090c0516020a0914040b060609010c030e150f0904150e04021002030c0106141804170a020106050301020a08060109080d020a03080402060c1506031605090408 78
    0x510203819034400c03025120750081c0030030041051310350b860261070b40d02c0b04101a080c40c507402803141d00078040e50541c4445e1803069086040c1d41c800103070070100c241c0003030301e0721450a54282c0130340e400e10034000e1003244140620070064540004001c2a80550030000340004d17103660000380000d01c100c01003042100d010f44400b60105650711907071002d806c19140c240d811040882e000c2c3e45450a8040c454061750b800314620391250502c2c001c00701c1c042c1c00901c0680074000d0701d42e20700003862080013101c0f4601d100c0e01c001c1080c1500c1707201044140030310200e12446054402034140701c954152000034012a0f2107862000c40782d0f0f070440c8803138443d085000720b20295545c4a2000425440a00041c0300715052540d540c0030514012001618602036074001102a922040c1540941c0303030001580200650181801d284030b60365480050001c2c407500c1040240c0e401006441040018a50081c50003904218140d410941d03280d804024000410310a403948030442c03070040f030007150000004042c11608081030840c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 396248021 1250 396246771 396246791
    0xa1a1803070b372403080904020310090e06061e01080721020d060608010605040f031b150306080d181a21091002030c1b0c1315050a05030a0f0303 64
    0x3c5044821600070790719445541c1c1150a16810b9000c515041c0d003891155000d904545030100d0a000b40d0118078040c55002001c80d0092489402e0324000b0807001e841440206840c1591540342c500907140240562014034050f804002e002800303070044101a0340f0a40e0555074000220f40c01d0b000701e2400050a2402811a0103444050004040703550f88480081440b516000d0010450b0300143d00640804ca81800207018542a0580e18421030b9000b603240442c0d41d00c0703c40040e02c0c1c1c0c01151300110714240c89414459640d601500402c04550a48083d14000004000c1c103440f103591406c240301440b00b94050901c401040c150a000c2d00440710080c060074113144082002d04140e1540b8004020700d8514104120414100900712101c40080e40c251305608000d680701d240d90044540c1030480340709030348807081d00c05420811005500300050040c0705035000420f81200070b110450802c1d141c100c00e0350003c43c150810002d00811030300058001d1901712010740310180c1d0054941d008508054940780886 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 396249271 1250 396248021 396248101
    0x1d0609030111120705030106120506060412050a0203250b220806090f0d12020315060d062402030a08090705030a1208070906020304170a1a1803070b 65
    0x490304071100b0368195031075607140502c02000382d0042c50344042050400c01030107403030380c0541040c911805602000c5000d803620030014880b8000c0d23810203458400c82c0c800a1007800800501442c03524000d40030f561002c1949215880c0b00c08080c031481d803030050b0180b400c0100d009400002c107518058810582c1d200a4010303a042c48100240d844810f2680c021410f11201344001d0091514911510005101000414801405032400f121043d00101e50120009494040300502c91078200f0f401400c0700c0c0e894010603180300043c81076008065500703140041515085504015400442c89980c000b1828404c080c0421144480000c20010307180c09130350000680d40e201001003e458501c549488241040440d1300100055401040c1008212414004001c45600402120300b41c0341030340c00d00d1071114622250300d0714007c0e58038001040000e00384074614098050040d1039015002c40700310100c400e01000c01d950b50300c0c05148801303000e00407500003080d040c00c0c039803404040804040345c0210300d00000400c0c00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 396250521 1250 396249271 396249281
    0x1303080304060b01020d05090a0905070c0b07020609120717070804120b011d240a0b03010f08010b010c172a060403030612170c010e070612050112031d06090301 70
    0xc442e940c0d291060500c496805100f514183c9280d481c2035800c1c8690711002034407603042485400241035840d00030071a1180314088012248d40c1000084580b82405800290358050032540c80c0d446000300913034903411002c40c40403a1040c68000341181d600344030f2291041d81c582d00c0100d0445154504000000d03080b21100303030040e1494020061801698582004c62121010031201e10603038940c1c50301000034821000300000c0346142044da403000c0b00f0160b44c0c041070f140c42458100c1c00303552002100015440c00d00c1da042006481415009001302111400152000d801d04000105960180301902040301c441d10003034201c840311281d109120402c04004414404141d501c0700040e03801140c10007003415014040d40e002002118160041160079031140000802c10704c08a401074000000c0000b01900250002026003030710300c003a0b0303c4035560b8800182100c01c000550042403400c000000035030340804050906100d4058507000320341c0390307101d00310b131100651550100e621440510070640300e910b0074468 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 396251771 1250 396250521 396250523
    0x30d0201050601020d0918110f070f1101080f0f09071203080f010b041d0603070f08070614041a0913151e05010c02010c05121333051303080304 63
    0x6a1800c040000a0902d000ba07a2150140079015404001d9110120100c45414103601e90008008c0e8100c0b85003076892003131508203203406001094490900c84545412800300c0c1c89503560144c032018981c010341d10ad0f5011211500c9810442000aa40d00c1410040d298080c034448140c40c111134441e03101401101681c1001e60004012008200454031002e0009002d440c0c140501e07400d03d4588104c9909414221410402c04108100421030316181000240c0c09000340510201e48039031074040351544c2d0a014841c0c0000210035900304808400d4070b804031000e030303041c0d003507400c1c010302606409071069880349000c20782020b2024071400b24803580f8800ca4022405001c4481e48061030034422180c140d005c030400c09003403030400703c04101c03607a00b12090814940e82803c0c4401c1c0c0390140d040840c1050880321212200718000506410b0409c0c1807140d81041d11510119043e40c201c1c15a600da009480261141e100e6864903100c13400d240d4054406055508242100310406a44a90366070603545c0040e58 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 396253021 1250 396251771 396251773
    0x30403050106030b070305070207030b13080702041a0112091a0c1b0607021002091011120309030901110f0a0201140c0f0102040321050906030a02040509090f0d0905150315030d02 78
    0xb00f41305171244e040c0109500800300d88000d0040504640f2400d140300005401480b415040c1d5009030308000400094071061074004008016403601d421030103450305001c0c000c0e1070002d0292420198045a2481000c0410b50862185440d0441340d0810702801d59000c2c0c0006034640c0d051003801040030741e04401d51036090b854406096103080410010f8506028946d5464545005001030081620340b002c080080b4416450030880203440c45000c2414848400e030205880c0000004002121700b000000303103200a02a81e91200441d58090041e031261011720b100c0c00241c106943c513602640c0b0680040c4901a130b5000501d203405005040246003004e0021806180e03500410108240100050244907010036281c1b400c03120580b00400521134030031031445034423503400440800c42c0c0f0121030f8140e038003800c4040c0207102d040c200106203aa5a1600c80c045d00540d21503200c40c404c0903846070283da021130f003004d0840319009640d403225480e80c0e007008000d48005a00c5281e09000d565042280032200c4500350 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 396254271 1250 396253021 396253043
    0x8071716020706020a05060f1b0a021b091306092901090e0f030d090302030d050411040f0e0c040905240403110c0f010302090d02090a1e05061804030203040305010603 73
    0x104020b410402580d00010a42d000255401c01240d40442c18580c8011003903110043c03176032003103032060621007111a9a21f0004000c01c8070350402d82c00282c0603209107250304030000341c00d854008200f00d017541100c150099030355218440300041c0c21a00074101803071051411800030503d840340000a6108214110030310034408004200805040c07080c41d01042c0c621015003050340102c10b00070340d00d111f80500c1c3e8801c2d596030070255090510038415a482c5922402042c0701c03505080c282584403600e4a070406114074030303200f00000e43e4000c510507019444101005041020f010100f0000180203c6105541c0c3d8029030070f0261200803400c482c098450340100c0c5400c40d80c01c080c10020442d80c010240403a055002e490081469511820704004900003442c01580c1c980c219000301e41008603d06000390014032100601040c401c05800c8020541c140305501001105041140c00076038a05491042c3c000c0441e00d400b560103001c44178000e510500a00403030b0318165480c4ea405084034000d0b402511203600e80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 396255521 1250 396254271 396254311
    0x60c090306020c1510060f0c050a0c0b0c100504111c0606030605162105040303200a02010e0307021309030504080f010902040c05090a0b3a0605060f030403080717 71
    0x25042504541881085d00c95582804400b90400159011003024070690008210400c0f0040181c240d001e544400a10308441d690610907145401c042043c000a0240c1c809104402c03803180714840c132a60f007000c4411000075a01c0240f00c0940307104411740e20148001030803100850460b01034680154030035080090640b50002441d42c04154900060003085035820101e80f880c00014400b0740710b505401ca000809071203614058009102c502d040c10241c049005050030503090200160401e204141c00921180d108400e200f9207074800d82e000258030608110000740800351651003e01c0c40d0744030b410034a181c10f0302e407407145141c00401010048169100d007144011814907000d4544041000d040007420140a000000c404400e5805000c520f03000100c1d82013121000300c0d60002050450210fa40805841d82240d020403c17058080b4500c02828901c0006150800708100e0701204e21600b81d19041d51295613044a5110024043c00c0c20003088046038603110400701d06050241400c3c1c00c24888104074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 396256771 1250 396255521 396255553
    0x30604050108060403080705090a1d04021003020f03011202030a0c030804050f0904030c02040e0c100306090c020727110c0a0201170907270524100c060c090306020c 72
    0x81600000ea070b640144060000081d040007000ba08001642800c0d80c80703000c0200418012556544000c00741c46456080d000700c82e6903443c43e940140c1c029108402d220040c0d11066040c0d00c907062000c40c00290030001006101c108070700e08040c2a10090685048101d00d44070100a003503035030001c0d01c480c50001400c1086140c41c0d040852003040c2540c442000f480c0039103002d002c6602880d00a402907843e400c4003144440c051102c8002c2e444010700e864942c400c84200100142942d0096590710703464610014a8640000782942c1202ca440040511540500d44403444030716801c0b0341c4020040c0c46030b00303044003585040060700c1c05541001c02480484501d00004200d08201c920b000800d006200a0003654400414900283c50501c40da040c052148449180079410300004201c2409103480c00f0712040e090410f40700034807520aa40c50903600403001c1e04028403241c12410207008250700022040c0001c032103812031075200509043c10a0901c3e0f40c1c3d2550b4060342e1000d4581c40d80d82d0000302c2087c03c6000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 396258021 1250 396256771 396256781
    0x4080d020619060e010303030504020a0e0a0e0106291e03042411030c0915070c0620030d05341b05030a0309150f0504020a170c0609011112030604 64
    0x81580c0903c0810701e000c00e220208032041c0000b45c101a103c1d0005000d5488100c1c0e8100142030890016115150032102c020040803108055949542030000000701442542920010029051034030010101030420341035aa0b07006040001c65600d154038a1949a100480a148140d0107803040b05a0449142c02c901d0245440c401017601052500c0c3c00701c000354040c1c105407644218204125940c1d200c01500150102902c0c4c600c40c69844400602e201c01c0003a03002400c42211381769251800661541c1340d0410030b5507400711070b1201551090000c0d00280e2210f80085410040445200d20180c0355074415009916000b800154602c1030b280032031280d40d40c400c004018080f09200c10b050003000540e2429124862003681d9000c15031540f0818042c0040980d040c1c102070329205040202c448080d0f4983c0141108403000d9108443c078800000b04290300c2c4800004141119010303002c0c00305100c00b0131510b9085040c5490410003650300065110408119505850386202440d03503c9140c680c0402041da4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 396259271 1250 396258021 396258061
    0x402090a05090703120908100b120a050309010810030b0702011a01050a0516060222230105122a040f06050f0d2403240608070311040204080d0206 64
    0x38640010003401080100f0300a06030b03a80b0a0100896020000040703807000d005800c410800e02584480b4140444d103903028800c040401d4806404a1138050225030f21803030460700251651b081008880459841845102d500407641c50703000c0003440d1240c45442020b002101c000d00540c0d07407903021001881d102c5103044040842480d1240c6051b206080003012805100b64083c5443c901008000c100465601541c8900c9592440304214014007007014500c0b040703c0c42081e503940c1040d8065100480e090190032915501070b120a85814060703a201040300e8002041c46002580d800202005c0c964242c2100f04070a000d03031511610345007041c0381d0303181c5641a42d102034203006040000c200505a801c0c180c48a4040300480080d40c044041c5601c0d215040014610070300c2544404044100001090226403581d2024040011900074100600460700a401000300544c000d800c208009425810a02d8400c071000c0c20160400e5681d040c40c51038180403e000f00013507007121041210506401ca0005401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 396260521 1250 396259271 396259291
    0xb04021902010903023d0e03070c030b06030a0b150d14030d0b0306010807150e0a060f030f0509070b0d1104060905010f03110a03050a02070c03050102090f0301090c06180e0f040209 79
    0x620a641a20210480c1b5082100c041004026052045508541c071211807010107006481d910500c0346042c181810150104541c41240b41000c1350f1715050020350007001d150300841c0500c498840d107100c0c030b01c2c140e403100e002c640c0321004451400000c0c0f6445452450801160010740c0c54100d214494400d940c003110200d40290701c61001044241400501ca904880c00c03c4030520b8a140301d100c045407083d0840c0e0800c5c0e0000c412150024119910034411002c1880c140d8042200034440b45c04007007074580c08d6520b10b09580c01248184443d064a900410300d01c0a40740000a024031008403100d80c0381c00030ba10110104107100003c0000b541c0110140c0c40322182c910f000c1014500310340c4084064001d5901c43c9003050341d01c20014450307202d42c2c4e0440340001d0304881b0040c4000d541c1d14006020b98003403815103000c2d0907800014020750805004010980e40d00c1007a40500343e041c22000c440c210681480103c4001c1c0f400c1000a442d64510945806864074804005441c0b41600500c1217510700500340c0191 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 396261771 1250 396260521 396260563
    0x15090b01020f1c090b0307020318060a0c14150a020301050907020313061d0303030405011b02070f0e0c07080408060105100e01020c0d1415060a09060312030b0402190201090302 77
    0x610b8804944202c001d00300400d10022150080b030104e5080800c0d03008140703400303400001c1c004202d0b00000902504800b03108043d2004440e0782c2801440d01030380e00080c001c1103890340300c1000202d401c1006a4014411022120454900c0500366180c00059516100c2a41d00000601c041e0904440803a840916400290710304180c0c11044400346501d071040303070204007490004142d8506d240e00220044100102266201e0502e4144035009147e0000a110540306061020340c49034000308400341103030511300151840f185000c41481206100425080f41e0352410420000004c0201000e00003814108008081a41c10a418400d680303842d400100306100030001c48107500e80c0d0018900e21003040c1500d00c0900104a4600000104520b9103008031074016074402141141d1504d0526203d018120303044858165034000e144100d41241c040602415058681c01c60001c3c0690084000480054001454411a00e11048000c0340c40e21540c40181d440e20015009c4c181e0422034682010460b00c58014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 396263021 1250 396261771 396261793
    0x306080309010f050c1e24010315060e2d27160f092003060123160302071d010b0703090b1305010e0306010522020d0e060f0a0203011503020c01020c0115090b0102 71
    0x80c0d1f021051000420310b40001c074035842c411103ea040f00380100b500c00e840042d1420301c070004400b0700d041c000c1915004185a8812523039044c4803c03805004101d001d401d400e5022404403655004241400c492800d8420200310520681e0380071300250040001c04020951135040058900c140c3c0c41c00c0340d18401d90003852040c811842548012a9000a0242040001c10300c001e80b400c22a40e030202542882d40d80045007040c980912005103180d182e00c203600b0f46124640341c1009602950601240300f01e8140c0440c018031014030840020301c240c5002c0d00300282c2003035545070031800035400144043c521a030410300c00c12407542c210416150340e2108401914032507040401080030320b0303440400c940d82e80070f03404410040f8030010340c11120030000d160801c0c0300b12114079000560f50030068500d8141038502c2e03030010300154072510aa83c143c44041000d0308a090001300118040d400883c0c40a149550070450f11341c80407030034459860740d020b01e140407410301403901c0701c420210303030800d0449415034000000310300d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 396264271 1250 396263021 396263083
    0x1c030216061d18010305101d060f07020f0d030c080604021801030c1101060b0a2a0b070915090302010f03020408060402190308040b030a05070306080309010f050c1e 72
    0x6044104440100c804081000180400b4203260f9150316001c4003034008400e1001c0400e44416142035050280b100f00b40c400014032203015005460021500711001050454042131741d015003144c02c620444210a032032070310660511b0004000140820f5651142e00400340e00001c00c6580060216411402c11400442091401040100c00b5040690701e00e955018140644c11030000e0580407402080907a46030302590340b0a60240003400b02140c44401007030051a6000040009864000c0603544002d0b0079a441121b4400b0140800d401e00c84202404103220311034034400360319480d00d40e407400402c900c2d45c00007405000d510704980080500400040c0203900f230004850b60043d50650308000c2c0c51040954901d0307100280c0d08000c3c241c41d4001800291001d4102c00f07107004a0814804100d1622546025803c9600394071070203000c0d82003400f24440941c0034804101640c00075042c5541341c210581c081da428030780d403000707004c2640e88501030b0034420003400c02c8089242a4803500c01249081003900c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 396265521 1250 396264271 396264287
    0x30402030616180306151a070f3008010905010f0519050904050a290703091a011503051b070f080f0d0504140a1e050c1c03021606 57
    0x10340b50711610304200e02c0c0c44910801038000c3c00c402a50110003015101d103064409030143c507aa00f034581c61003043c041745070303040502e0301d00031400c0084645161080726910b160003095040001c0e120b5420000305620007084110401306041d0016400c10700c00b91140708041d00f1000103800105034507160000601903056164030520558070111413403954042a00c405100500c075641059130054205418041013200006204641520415402a0a52855407502e51403410504100e28000a500200c1c8640b4040ea0250080d03130301842000c403189050860604803610280e12090000d0441c80c80194499458411650007801031694240241d00300c2c41020f9441c004c00a0181c83d03006001c004000700804502101c45032401e40b258070303484600c0b00395440c0060404940a032103031426040441003402c0041039905885500441c200340e41849080d01c10801090311034105e40520440c070700d520584d581e003034030885107030b4280c24400001c2000c0d10b0300900b0b1003040c80410818245841e024003140340c2107841 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 396266771 1250 396265521 396265531
    0x504230601061b060603050c0a06110a02010305060d0b0705030919120f11060106080a060905040308010b1303081c0e070f09020304031b0311011803050d0203040507030b090303040201090b0304020306 87
    0x300040803c640315000340c0700b01c502c0800070200c40c034043d03000007044804558020b04060440d191003c0a56540080d6103d4201751a009000d801c001c09500041d8025480240c0041025140710440c2e2402d0362207200502d010f50300280030400200070014079074420441f40040c0132413100040103139134041e60f0b603c0600800d4845042840250010410554410181c00001044040c1140c81c80d580d2000041c0450b007081e00c103e02a5420050045000d0030a8002e2600036075243d134a60b07105038a488032840058000c160251140b0003000b400201080041c0d0107091b002540454000294800c2c1054500b162120100003c0030341082e0420000e800303d0780c561004441d030500c0c025035030765100c3c50110b81480720f00740b014100c801082d0016050584c40300311140001b91000080100040082c0b0f641d101e8114202c0080000740c04201c441502e8503940c016603041407080c070072a525291240e030ba40050403412141d100e060b52021040205660384034000f80001d00441c41411320f10b007000e0300480c3c1c443e00d00802d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 396268021 1250 396266771 396266777
    0xc060109020c12040e040b0721050a06050a090b0a05030c030607030903050d0e0c0406091a130608011d0d05030403050a0e0d050f0a170301080309150418050423060106 73
    0x15441c0c00e40c001803111450b650f4503d021140c3c0c2d1038a40c0b0302d034010488251003d55034181e61320001001a170141510344451100c00f00d1b030360380311501e0920400242000504441e4065201d4a0018040c3c4414030408060440c000c0301255074003401c024420344102c15403003980310381e12082da01b00d020b8030080b96041d00110585400304491000f81000d40d01803060044001c02c480c90800904030010300494100514101140e081c4141955864070b54140c81345400a0501203803100503c900925004095404105d1911000b060321903542c0b400d50708440f500500012040850020020000401e10842c4080204ea007011800c60602d914002e10500070341e0088414041a5001145280d0300c41c6645000a64014210307800454446800e5889800c0383c803084a0041211049800c1205c0d00d4050720706a8410400560030011403104008060020ba15660319410b020800414034030284200304500f80700550780410f0604141c40d000f00d074850321149040c0408051003400c10814008105141140c4043c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 396269271 1250 396268021 396268027
    0x303030a0204171b090a1815050708070206220816030917071802070c090f0e070b0901230304050a0b01060302070c030809030c040f09030f0203132312160b0c06010902 73
    0x1b01003000038181005000110300d60f00c4030a00030401ca00c00410036907514500248071544540030f050390380c0c00b0240e4403080507820010001d400d0000742c0d408030181c00b21040c18a800000c0645a924042c2c0c4410a01009017a03241250b80606401c211003400030b150100742061350210f070070314464545880340100e02c011f0203000360b900d5030540075405a560032500092412066a0384500300d000410a6401095455080161100c84583c0c04513241c5d00f12507100d94a41c0c03510300c03045e00440b075003011110485030441941080a540d500342c4001f452207144940c00402c0800c150341041c880500c0b05034066003c05004020040010f0401560101100d40c8405055140d4440000090418150f18561500113141588038102c8000a8000c02d13070050280d103501c00d24a000b004200d80760320a0f10000d0100010b00001000712140d1880700001c101c1a01903241d441e00c4502001a0109050261403c0180e020f4589411018640c0840000419840c2e4a0b50f14202603c4d0380c180e20345905110700c0080540c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 396270521 1250 396269271 396269281
    0x20c0928060315090b0109060b090609030102190e0901090b0d02100e0d0312060504021204031b0c240206060307271407091505030604090c050303030a0204171b09 71
    0xc1e00404060740c0e00c648202038079455850300c3d81c010404140103544817034244000099284480c410744003a521918400ba20300101c01d0103004855120402c0940c15650070010006681c5900c5500000305d22590741e600143e5614078100003032040182c102c0c804172850001000751664034610040c079407030ba041e601c000301800c5c07070300c01507a44544a50016400ca240020280100350b8010090703d000f12050340200040b98480c021700040780244040c403010b019401d804a40800d004100304501400f96510900c51210103680c0c111040c1d0543c1d1002d400c1c005070105186404620b908004072201c5035200070500361414000080c1c0d9140c452080b0865034009c03000e01411103000e015040800c205049040c840d00c0404282c00408040840c5c0050000d4039800c000302e43c4001030041d00310108226903c2c2c50940d199481000014015441d0480320619000c500003000d03201400510310400d80e0150040c1c44134a400d00d4100b01c0220040c241d4041d03000050189800542440c81c0d20840b46d081c1e608101c42c1da21 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 396271771 1250 396270521 396270601
    0x30306030b1602070e0606070f170f09011707021c020106050604140a06051c1d010914010b0f06030a0e1002130f050904110f030c0a030506040201020c09 67
    0x810380014200d46035120420544070300c40403009046000d6942103443c02c60303440c0c440041e402d0003680d4469000104104110104424046c0c00600f580144030802c1e03c41d600e40c00004a40d0300c0303004070100452002c00c51441e1980c02c43c1071000320908115915090b49403841000352558070701140c0c0c5244002004028004a10075407040d006020003400c590350322900d94418865590840040038420041d00c40c0c01b1030003904c50f100360b0780c0c80744144030f6030400781d0080142c40025101e521402880720305102040f000008090050088450191000e64080c0310b4041e440d5003512841112240940c0c141c0810300c0306a1500c6080b240d2181045000042e80181d1940031402c018410101c400114000300b20011108200d100c81d034100e407104001c082d441030b60740c8144801c0140445010702503001145074004241071035a003402d400702004007601d03c21107441e40010072419440c0c01c280c03101ea0140c1c0c200011542c04020541d06504211240003841c175107005807000300c0c50748040400012074201c0b962a1150740b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 396273021 1250 396271771 396271781
    0xa0204051e041b080105010b0c1204181a1804060605030706080f04050a05070e0f010f140d05120c01020705010f0504052109130b131a06160c03050304030b10051c0303 73
    0x102c4c002031100e960b5401c4074a80b15005801c02c0c0710140544894203007400e213a40d04070707800c540428808204480500d00300f04000d080c400c2c5100440001c1c2c130040d9274a84e0b035440344880304001e00e0410341030350300345820140c08803001600801d0081e400030b40309010160308a21161740c0900001415042650307103280c842c1c207255081c080101588a041d80220b80c840c4030141c40b610950907400e419206a988698143c442c400c0d6114000820004000c01880c50428500b00c0090600840844581a0640c0c0425030240d0100d80b00c451565030100b00501049000c1c0500810203500301d50922060030b064a84a807100060382c0807041d080c1c1e40302d03952508000d02e6000c1d030b510000000c0940150f50080441c080142c0220f030021441541000c0081031420414815124040d8111481d929022070442c00e000741c540c01150540400d1125040d0440001c5a9240202c040c40c85900616111850f40c070302980440c2d000341080c241c022030007070705000a490382d40360004408900c940c0d8803501001c5045c1600100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 396274271 1250 396273021 396273029
    0x304020a0f0803030405060f10170106050a06092102090c030a0f020f180307290408010e031c02040b030402040903030e011401051206150907120e0a0204051e041b 71
    0x1c01e40003000942d480700400510710582c0504103664140e5540721850302c0303180d02144d090119a030603e03004c2c86050002c0d000c0c410103081f002c1c00000c0098480c1d0004114810701c0d844107000070003107281030080d10100c858000751500f000d0401d6041101c60b50000b03031030070001010844500c01c08400909c4403078058014540100e2007040c215950150045071000b25400910141104000707043c00000ca0309000468070200c03001a4203043e410704042290203100d4a00c9524a25800b000b03100c045182c2c58284180c80101140c41d0040d07540b00341c1b036007404520725a002c6030441183e1050104100e02e9003c501140e50059044400003825032043c40d00b90002d06000709050300740d40c82e010080a2007401490302d80e060b2002114103099855100040750f5803070348126141c00114101005030a05800c100f17040c2600540300381001e82c1c940740640c0c240d0040368580c4054110b20b901c49141c4c4819401d141c480c107034100c0721889020300880041c842d03502204502400050580400c000307902c42400740c0020803c050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 396275521 1250 396274271 396274289
    0x2c04120c08030a02091f450306140c0703080a02040e0f15040b03190507050d03021506010c0308070e13020c0606040e0105060a0b0c01061802070302012d020304020a 72
    0x2410590f070b842009421500d075a901401c1c003880e4280304d0401007266025440980c4d5140724a68a8186d5000007064100480c1e2079041c015030051080000903a180941f030b18800b030340d00381e001451402c200094810580c02c1e8154040c0090900901c4694102100e0505400d030400c24003903291000d000e0000e1017a60300005003414003c050103075102d4074001180c01400c000c0c0054010300d002508100889500300d05040e41743d4004c2c9501280c0c200c0009010403014060829260913507510808604110b529040440041e0011281030710703c9000400710300e0f08403000386020394103080942c0c1c01410a0728041c0100301802719807100158240d5840d80c40c5190300d8620f200130364840e00d4441c42c1c00d0707441c242554103501c940e0510f4a200c9080005100e40c0d8400c81c0c1c0202450780351450040400c2c1a9423041000c00565500d449000c200308111103102407440032020001a5500300d1400d000b0700b141d0f210700017105d204524914900398201504003019800511100044e901d880714800100038030407903480150340d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 396276771 1250 396275521 396275527
    0x307060f090512010b0102010506041107061a03010905030c0f030301050907082703180402070209042402120609071e030c0504050a060801030b01080a020303071202030c0105102c04120c08 82
    0x1460b00c3c1034121043d402c40a130002e0082d901c0d01c000304415280002d030380031007000090150070041101a0056001000b4482d51004680b6207a400b09081d9000e488050380d040d8000030305100c1416013045030803021b01000700511f00315410000040c000d8034020700643c04101c5074002103028017602c2d0144800005402040e40b074ae041865154603100d4000c1030304010729070011884c07c20581080e00850708580e6008000601c03941e1982d80d000070039403d070542c01c10707852480c241d54112400103200410610045080c2c103905890000204115200000d20320700c00c200001402e8882c0ca400c0b41c80c0c00118141c103040120320000c8200c800c07249030007264061035010280d250005800b82c0c00c100d4090580740075501c1003050f680c91701c5842d642c0d40328480f0000d4040e8800c00c8010003080c0d074402407020003072662050300e241010b51410365081d1030090f0391030325200e441d0201c108a0f003500d15004104c440901d034501e00d00120110130940d00b4100043c000317400b12003600d001e03035100e502c42e00040e4091540000c1c0151 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 396278021 1250 396276771 396276799
    0x80411010318031d01050304150c0c060515041a0901290d14060a08060103080913020a02011a03010c08060f0a03050d0207090c05032e0b0d0f06060306050307060f0905 73
    0xc0d003103e00d029000380740c2e4807400130541940304104a03481079070443c004030752030a03039a00440002c2c50b0404030070f1300b0804126208800580f0714001ca034046c01183c070801b280d62841703804001c11142015240303061041d8890780207007183c644860300b0f411a50400702d980e0124100c40d00b88011400801200c1505000c0080d51500e00c100300c0c0d101412402c54451403030365940d100c00c10b010b50389045001f9641113610480041000075503400080141c5100502006a40c9440c8010002660000c11046025035100c2ca40c901c60060320715200c0b10314040c00c8000303000107100040003520758100900300c01d01610550480c2ea02a44900d800600156486401c03281d13503001c00c48000352aa0018002e008011303003880308404e026440780301603900407242443c0c9045031314409004a02c1d40c00d1a055420303107041d10810001100b4405002070800c41090103000b05400840b07503292012070310f00d0380240c1d05251400c0818041601c3c0001e2110a4500c40e08211210012001c01036403c0005948010303030200c5100703801d82d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 396279271 1250 396278021 396278027
    0xc0f0708070b030103021503090c061612031808222c04030504050603040201170c04060e10020c06070614040c03020316080d03090f1a010807080102090108041101031803 74
    0x10200c40480c419600516128180d4901620003032001a6028110070941c00107001034600840d005464074007111800c004850100380d440d00900c00341d096080d00041c41c00c041c826100c0c5d45a25510152404000b004400107000154906091020b031202c100400c1301003244030240b01000c4200e0261810b260340517903410501d005601c4440a10f41d60a044d140c07039a00f641401c0c070015024950544556003001d09010621000e60030007003090b810401001f105040241a0000c994051521980c2c0c80e580c4034201709000d07108807071718180799004100001c64003258a40c0412101080303101164910350f10422410400040c005071440000700495031010f000c10803140040c0d00003124400d5054a4280c290b009412071080124440d0284507000b50400900c3c0724465070250804911078082c0401c80d180c82d40380c0c0301198440c180006a002d81d140018000070303804108620003031020700003d600c1c00c0352000c002070006401400c01031508000401c8682c0c940c1c041d41100600c241d000800c007203d807000d802c000b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 396280521 1250 396279271 396279283
    0x903030f07050304060f030207020a14030c0a06050a09120c050d02010c080c0604110102010e070e0711030f13050312070201030908280e010e010e151209011401050603040f1101050c0f 80
    0x3090109500c0440310b40c0085c01fa0007500c0d6000d400030004103050340392402541c28500c102d006158180905d4004110950f0f6120b034800182403c2c3d80c0d925203d0900d041c015080c5441a00401e00300c80f51a00c000c4001380c0c0441c0501c0c03d440b401e5912042c1c00c4038910059501b62400e01e0010b024810205501580d980005042c3c0e210740c0c05900d603080d07070402601c010b9003211100c10608a16401c410024001d2506554206820200c02e10b480c80080324103c00d014299001001a0414050300140206100022452050107040124003500102c030104c0d22003950b510071a60000d041c50b449010100522401c002034900300f403410110120394038070300c505422409080000800100e0104807079481c003948036101c03d003006001a100d041060722480100020100000d402100c071280070440d8418410300745010b140100c04010010034500c402c0c0ea80c0b00c0300c2da601600150b00407041403007000042100b83c0b5083c07808540081d40e0000403405000102c03064807420044003030611688051100000e400124 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 396281771 1250 396280521 396280529
    0x31b0a0315021c14010b03060607140c0d0317090303010825091b08090d02120d02160b100b090a17150c0c07080106270e060406020309100516050903030f07050304 71
    0x709094607030f246c05045c41c060005441681c2c0044052103000001059042e610000c01c441c10202c601521020002842c01100c900d02100020401d40283c0e44860301340a450703070841030850255040d50b050409040d642c14008ac440d00080300590354800700359000b28440720181002c08018828500f02502c9185104001360700300d0000381c03a0b14000341d8602d001060380307400150745501038070781105c080d00c4030180d0b80c001501d1282c075103900700302039a248503407d19080740091065506440c1d9142080400b41c0c2224544d010b80c0c0008404c105e0400c5a5071850350900580c0c00700283c034481d541c010302142c0d25104802d0002c10382100c00500f03010b40f190400b8045c25070710000d80111480240c9940c0c1d114244c40e4180315402c0308000c401100081c9500a48204900c01d2581c980021f00b0380c201c00610385441c030251000d0319402c1c6e0010502c41070348000e0140d8034000e41e200209115500380b03036802079010215180c2c02810000c0118038181c455800b03004a0354134910701c408842c0c45c4d401608250307407039510600c6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 396283021 1250 396281771 396281801
    0x303040e15030109050304061214040b0417210703020c0d0504080f030408030322050303041a22020603091005041101030c0c0c1a0903150105031b0a0315021c 69
    0x10078440907140500541038259404000340d0304040c640307001a12030341c03940120071080c180c0b1490215035004c110741a4034440c90107140c140e000c500302400e02c40700d0028078070100c407000103041101e1501141d401c1c1a02c8090070140380d0360303140d03036031030080c01c82c001d028404080b0114040c40501c0d850040e4480c020700b050740c0085080c6d445450b000340000342c0e0b922842c4607084441c1c00c14800116031000c00d04c800201040204013280c5a07500d16a00e09040d580b08941c1180e4051542000342c904446e481036699204840700c0801c0003c04550700e101c47d00100c000c4009101d8080000040e1014005121104680b50300074014030460030189050b00d080c690910700180003a15000d40040480d02c107030750320070481d500701c102460003500304006050041d00c0000c051101e88820040c0d1011520308221814511003900101ca40e554101030405007440d01c540d0810101104007402c054880c0d444424a900f241d42c032006044c030041e0321f080d000000c1c3c0a14051041d0f03a1a00a016410442080c1c2043c0b4480111071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 396284271 1250 396283021 396283051
    0x4110a1701061713110303030703230705031918030806100201051012080405060a03020304150b012a0b07020d08090118110f0924030c010203270303040e 67
    0x103022992080d04003d070103120390441e404920210360890580700c142c2e00545c83c405404401e81c020a1542d0304c252203800000c0c0c0d503500601c040898400082c2c4180c3c0310120000580d0500810040240c0000303072151030301095001c5103a04105050748031481140c03e04180c1c6200500d14200980444c00498032607004540030710100d03014520600ca00c42c031800030b000d244030303005080c000042d5405403007030300444070f41c0c2c42004041855603c0e84068002c2c81081c0d503025903a450b10785440010703140c003c402400250300b0417220b1030040ea00211004c41b01e003d90145540c24800c62580c41c020709400c1030000c1c120302c01c62800d03c242c2d61f40c0803481404040458a55040a031602540982240c100c4802c08643c200103200b0300e00010318401501002900040031901c1100001c00003c3c04017400355404044049400045010040252403850401008401500341c0b40401da0003c0c0d00e078860307840c18140e451200401c0320041c40c0000807055141101a040300d84480d29051040861751080c3d0365200301050b20 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 396285521 1250 396284271 396284279
    0xd0c090e101e0e0403111f0903020f060c04050d060f0603030507021206010305030d050c0c100605030d02150c07021813020130050a200421050706050904110a1701 71
    0x10400129403d80c0120040c513507550310304035070a4001d1010001503002d0710840803484800c80c6600103001c1d01e45d1000140041461501a2409460740c00030b01d905c0d00010b04000000f0100020b8404407001900d0752140c0481c3c500d441c000402082d500f080d051890031f10b0200074964080094812103200f03640000120070702203441c81c0c3e02d10003440024a9035108000c4002e00701c405800054105909851483c20312200c982c5050070304401c0c0201c00c0c6940e685020402451804000c00c211000490010f0b28400401400746806100020f0210ba500000000d00348115150319090291120418810141500381064422500d880c0d051069001030b04082ea4a0781c04204146092140c84002152020f11a0380d1140c250241c08018003030006180c0d40d51035001001b052140c21841c14203d80c01c200d40d00e50500307a07045903000c1100540f01d401a1811402d1000460000e00d41c4160b0f400c50410781d854040c403a000030050212485440c1501001050300c181c1150007112946c407840102e4000416a030325 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 396286771 1250 396285521 396285569
    0x40b120105031204050103020702010e041410060509030a020d0314070f0209010e0118050405011d030705062a090604180c0201051612050405070f0f290d0c090e10 71
    0x700606400f01201000100701c5580240c3c01000e8251040c1004070200c9260300001d000c982c00d040080443c54a034204001d640c00f400010b040250900c0c0c14010700786003c0c140400e9403036125603c001c1c041c60b8081298401d040c0500511f00c4e04440e8688000d17603805503840c0040e0941000d01d000ca01403e001c0c0004104c050b1207049440c182c500510084e840748a1405416000e4413000e84242c44c00c1d507841b050718010f00e00054000000c0000d11004507503a17207061038404c0c80c1810092290018221203480303040d003021601254060003c0c09170081d03840d54184400100c40c1e110b26800100c0700003c4400001d18005140c0101e29201a150000c00c815034034404041500690071104a0000d071080100c0c086036255a4030194109004804440000d0348900d80c001465060313410101c046100c0c1c10007003100203a4198000b5480c0c0440320404006500381002d081140070300c00341e040407183c80c0c401c1c8440d514407807102c2e0702c01820b409142e243c46040a5000c039078000b120703000d030010300d0200c00c20380c84030003003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 396288021 1250 396286771 396286783
    0x3030819062d0311060706090c08010b030c040501080703080c030408010c030e061506090d230f07171f021608030105040605090105130e030d0510050f1f030f020c0102040b12010503 79
    0x1800080580d00344d07400c0420480540c0c46280f0449480e6651303681c8502041c640301625020b801030340e000003140f01d48101054030b040d010340c802e14813460805c8010320000002141303020803241e10418950700c80050460180c15409590040340c02c41d86804000980c13176525401508544100c1c00030703106e164640c8a00034500c070740c3e010542908080100000007050606103c144042e03070180e00780b1103204544104901c1081041028559983c2c07003050401600c01003408018020404504985642030700d00810f1621519610f0078505642001103440150751f616404442140c1240c2008075080781780c0d85450a0300d501f0a0160320b00039807403d50085024281070056606903180202500320f240b0540700c1940c05404c9680d21422640800c1c401c0703000050090054a0007a54950708840c2d1840c141403d01c035029512203416442071902d0003080080344424444a001180325140208107941e400c2659406407085c082c8a171940c0d84001000104000303940044c12003118424103600d1566a50410903641c0d007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 396289271 1250 396288021 396288023
    0x406090509120a050f120f070518090411061204060e0304050a0e070c0212060403080604180b070516030206190c02191703040809010810080703030819062d03 69
    0xa800b072403184003110080c0300948143d6000d86011803400c0d5261605d04000e4010b060810002c2e86244207002c00c41d41c070042082d920034054501036040c1496814071012a8020700070940c000d056450104041c80403100400c01c5e6418090103003070f03607101c041300c090803c0c08003100e00340c661a11340f080340b114500d0b000c13003180c046600c020300305034080e81403551390402e480002c1c040d00c06000c9080c4400006840d903075100d401480c003040c0a010340c1d103030a040c0038224410013450180305518040408001040e1020703210301041d002a03074010150303180c000584030b0b48500c3d4844150751105045c80410568006003541c880c030b4008048a0480001c0000d01003551042044580942c01ca84091150040c60203141d4407424050b415041c24815101c0065501e43d006031000e4030307038050015840701c40b540c2110720309070031584c4812030800795480c00700c60640b40d1100e0300000b010000302801140001c045091400740060b00400e08002031992018800c600b08045007402c03018a4880800c0305080c0f0184503c80112 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 396290521 1250 396289271 396289273
    0xd14060a081902190e0907030b0106030203010308071e080c0703031b1a1024080601081b0d0b06040f0e0115050409050c0c0a0b060a09050405072718020406090509 71
    0x2070142d503080180d140d03600c412420301c01c00c2a420025444c10704007840c5029900d980301034464982075041c40f406000c4160446030605004100400006803c04111a001c2e81c00145400440c15099050807050b01004005810448085000802540049150401c41e0703ca034a80040d0066103100c01019000d0b0750038007500c4452403100c400358030b10000c0703d20f0740e000c281540340c41c12407615045c8180703091156104502891120b0262400c4182d0071854507a00719000b420a1112490800d80500344d68091000e1041480c9000c42d9029143c5029048040504001003e00b910b9a403103642045800b2050f12403407420700240000000c0e21384a0f401c0f10250403190b0303910300d40b40505100344003001d0300000c0c1034025625020170060445100078000b40072058410010048281032440801007004055000b0310406403078501403100040000541100711029113082c2504100704200c2c445007544003809100401d42400d02444400c480118840340051007107030304100701502d039070115003101c0d011a440609 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 396291771 1250 396290521 396290563
    0xc0307031109070c050d02010501060f0c1214040506072108130f1a0a050906100807140d0c09051605040302090613060b04060801080c01020607051e0d14060a08 70
    0x2039041000c2502d03802912030400e00700003003085e42d800c0c0c42d11450419010050b5500d100511a651f8024a101c003403030000e151002c8141c2c10394481c40340740b030a2441c50ba1306201401c590082d101000800380d50043c1030051043e0740351181401c11400b10002460042031218070120004801800b42c1215405074001c201813041d040010743e035986881c480440140d4080f5200e6100341c02c03050903041964894044038001040300e0420a1110b1314107030300600041204480b00c9001d02000c50009040030803251103d01d030201030030442000c00c0e02c2d0300081358050142e105008020514104540115000b42910b001e41d1304224800345044500c0c4c0500c1c0002036000d003404020890919150b81c0b40307a00301200400002e0f03111344e82c0006095a40c41a40326201040010f00104451013050040c0d1100d01000c0c0040c1c8810319280c0b50042c803c1c030400d03101d0014541e030003804c20040320610090702c1c860300310480c1c100903003d1550500b403500e0700122000d45c803904031f14501184494000c940c040c003244075080d60403d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 396293021 1250 396291771 396291803
    0x1050703050c030a020d1415040c05090114180429091314010b06030106020a21081305030d060612050604060305030a030b030307050d080414010b010e1c0f0606080c030703 75
    0x1e540320f10781102d1b40b1030f21442e50380204d109040d2064000d4a490103d44010020340081c44292006403007007005000050103d1600c0366006072908803104070b0b2014241c0e841811412000050b20600203440e00641b800f883e0140c0500e503c00042c505507d040282040c00d40c0740b404100148100f2101514492800c0d040280010040020a030f0710003080c1001081070f01000000c500290026848100180d00c101079000c2844243d1508822600e407a201c242084040b0b0140a0600f4802500803103d4460500404c41403210038005e5035106a03038441c00f401500d0303465100030214401a8483c109452520f004034000b031500748181800c90383e100d000f42d0f04200c280c1000360002d00c6e221449540501040068070f001078010310024030420225210f04000f805c180c10228605004440d240c034560385442e500d40c480c0e81c1c200084095a0000b224903030042080030585030b1110b400c01307030f0042202d201c0326202020403811b80c00c00700540310f11400302d51182c00d00c001010358030141072001506800700b80351105 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 396294271 1250 396293021 396293041
    0x1404060e01031e05040803180105041a070207030c0305101109150f0906040b0307080f07020a1721060102010b030703020d06020906091002011416080a0f0608071701050703050c03 78
    0x6003114045400016200f9506110501928402c0700d040f01e07003c40010422402c2e0f10301d4250a0301f51038407030000300010300c2c2c10f60303d1061303a020b04500c103158000d0980004650910070000c100103940e000c00c40741c1c0300a55070301c0d1030307a2b5074070070001c0c1138200d182070068448908186105561015000810300b0190054201a859241d8411100390284840030003801105c4e0310794200a00c002c0220001d6160b4238545104011701e400d0010785011a042c0c0e03600d0500910355400901d503400303190060b01c000c4811840c1d0350846110711642c03840f000e64005c4094080c1181d49072400d0640302d01000c1c4c00038082c080b0f4040070552036081030300000390312004074417511002c9492503000e0114940003800451030f002020300003402000450741c2c1c52006039160f100d1810150900340b84070f03401501003a603000036003005100140801301b004000144280d541d0122003001d0810740c0100780144800c10a0780c03450341d111040c1c94011807010801c1d42c1c466003040301142c1014400d124141c4200098a030f0030381075442d01e0440c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 396295521 1250 396294271 396294281
    0x2024250206060418050d08060310020a081009021e0f1303050606030c0114120c090402130911030f060d030c1416080c0d02100201150e0405100b010e0f12100c1404060e0103 75
    0x723190544510441d0711000368603440200034003006071f140d50200303203080c000742401e80d011368011020356801407100254841d10010040c03003400c2c08822081d00c41407000304400160041c00340c1401c0c81c000c0002d0000501401198050080780e0036400d40c0c91031945a0300641e0f007400c004215950807802000030503180d0030f03041082030708400804207180c5007804510001e026a00007050b1031042d840b00d001e0030031841e021442106410303000c202002e411490030380c09002c1180303001800c0768050184d08101d07804141c40341c0348644445900180c04a02c10240c1c49480b42e0710300100112081d02180035501040315400020045c82c071030001003408080401d1a8240401d129410503000f0030b41d9212800c4048036501500c003103024290b007007440003140c50181480c1e80b1b080030411010803041d1509407449070b1a64040b000c8144c0a00c195501c04542c82c800000c039010703141c042c03070003003241c069103640c1c601203542c1d5040b402210f80c80d5071b03407175190314020101807041303210303a1041901003407000008031450350182d040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 396296771 1250 396295521 396295531
    0x80106111c11070911040605070303090c0b041a031003020f1f05070c05010e0307090b03031b0105040227042607032024250206060418050d08 62
    0x65509009410381e4161803000e105031041e010407009992600da4580c01c12500006103d80315051010003c550a8a80310740f080d8001c0c002000070029030401410700a420100d00d4580c800b01d8054420fa8400e03000381143c0082c0075550000900030f007008000c02c291015280111070650a0b61141d600d582d08110348119000b103403d4010b50403940006140f0303024000c441e035140d0b10391070713059a07080545090080c9282c07030f401250601c040c1c1440150303580c4000540c1800d48000d6100014801c0104001030710718056501560399007000f140c1024543c074419002607002d41d20a40702484030841d0082e9443d0200c0c2200107903681d10503e28006030102e01d5206500000030080b0254044a82881c5000070942c1d02c82c007070503408201c90315032406a0310105d1400c9001d0b62040c1f0701520203031916400580503014411061028400c030340c030200701c3c95003c0c00b01c400651040003280d08640307034081002035110382c003c4550038440c0b40341800135031214881507081c1d401281d1010207009206c41e118810740d80c200e00640 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 396298021 1250 396296771 396296773
    0x2040e0c0318030409051501031e15050307060e1c0b0c090d1e200f060711040c09090506011e0c030320040320030c01120f02030a020d0c0f08010611 65
    0x340c01d66031007080c4001c00152003845008160f51501034100c0b487c501e00a20103604051410054100c09048c80106048043d140c07035020900e8140c01c0c8074112185065044a9810b000c1d40100091060b0056808054404140c0d442410442c80180000340c0107540030002d05030503210700c001000f0007000402401d80000042440f41e6101840e151403d90007501c00d001c0c8008450481d401c2c05109412071540c03030307420303111404c0c110842050010070509001d203140f4030b00490303010585800308040050851f01c2e41c1000f40080042019901008000c50028414a480145400042265544507201060b1070000c0d04603008400d20750000c00b10341c000c0c905281130b0102b40c0d840004554800b0220020750844001d48006510b807404c50500440404903945540d80010108606400c262004900040e04520074202100ac00c0f90003101c03000900512515850f12510000070401d04154a90141c8400141080308100002140001b40e0700100d4030503145021550310001003218a10406580b014445904 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 396299271 1250 396298021 396298051
    0x3110d0804080d110f0c030d05090301060e0708180109020108041e0507082401050a03060e100603081305041a090612010504061b08010b03010b0a030603051504021302040e0c03 77
    0x840325500340164042d41c01c0c00141140c1d420011240204103180040005d5000303400001c083d400040d03640c0c500000c190f02400808100110103540a500550003041030490585030b900d003410004100072007c607852952104a51740c0c081000c4014032804e082240c0c10b03100c183e01902c0d281c6a40510142c464604e174001042900148002001808850000c040d004000e2800d82c00800f0000c10345a80300d500c406511555000400c543e40d0350f00c1d20403085981000c0006035031414800e070380d4142121281c40c50901070401200100f08503102d001029142c1e403400b9246000c585410801040c4e41d01101c41c80503146410080801501d003214080e600b050700101016440d07001c4200d1242980d40443d810b5941d103036520410701005030510140303110400c451500c2d44856042074034880d060b00043c050501401320200d003c92070b2314081e42c40350000c6c41e042011240401c0300c51652030500542141c00b24052103d0080f0300d00080d49078005e8a0507201d0b14545903006a86903100741d03021307810081407041642c2c030368 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 396300521 1250 396299271 396299279
    0x1803020d050109200105041a161202010f0b22020d0c05070b0115020a0305031b030c19020303010815092b020c0319030c03020c0a06052203110d0804 65
    0x150101800d284200008150428507080c52500780e09032040400c40b10300400c015403400c0c0e920504550694000b10442c4680b050045116230541c051880000b9641d4a90504101400031a001002c0030101c03a900a1005000d507801c07400642e842c40c82c0c0c06070451504114464440b400700e803208010400d100e001410119020030030b5081c0e61744540c078980461000940501408001c0d0002409028140c0704031914504010009554a85203070020381086004000715044035501d00960100290318a070054681c101281d48508580c4013a880b0050b0540000b480c150a0f0300110a581c103c1d001ca502804941c13210302480c10003028010038518660140d503881c503000f0800303986924402d00040e0140100d4041d14403010385410b000b0403000380700c2d074004138004955280340010055526810f2a01402032411460240d01d890070401d03100340d12070642040420055404005027515030240030440c0b89260011384100911155400050700c1c0c07024043c00329100b07003026440d10b000c2c3c40c41440f83c1440e003652 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 396301771 1250 396300521 396300529
    0x3040f120518040207020303030c13050310230c040b07030203040801050103051c020606311a042406050c210324030c0405190f0506101d01180302 64
    0x1039000c140c041400841c94403656880b800c0c5540c00c8500a440440c03a086a540001c0e40d640001440005184800a80004001401e500d0030380280b20140440b0568400d80c1007010242c84201c07140300041442030740e099041240603d0413801219038890240c68203051014107261130f40075103020380c02d41c441044001600442445054000c50041000d010340d0b4045608100211a07410150411507002030203000666903605d48015618100154060422003544555024080c2107106422000d140c04d00d0340c0d440e401c5201c41c1902010f0121001c0041c44a00c190718201a01070280f1148580740c042c1061083c1030040004010031070702c030b01c01c2b552403041d490380c604940c228200040e4601c000c04024400c501040c048660812100020302444803040380002c46d07500d048040540e40b066884601050344000042202a0102c1c81d020061182601c50398004000c1d21040c0e40144c003401c08082400304c03c0384a281175001c048001001650056085801180c03014200c0c1107994800d1108000000142d403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 396303021 1250 396301771 396301793
    0x1020a0f14010509120a0f120903121805030706180219030501060501031109090a0f090f050c09090601030f0312140a061a0d09080c010e150a1b0503040f 67
    0x4031a240950381c07801c03011009801e440000c0e0a00803541c1c803070044580d1900c2488117848005895107041000185c4480084485800038104912482d1a111055047c550b011300a010041a41241804080205548900d810203120b6010317006410601149000502641020601000000312028190903a4000800ca0b0310901c460300c44039003901a04104001c0e02b80a5800109800d003001c101e0905c0d140d001c20003500c10310721050700c200f00708000121010400d42c0903c069070020f0f8001c2045816510300300b2001c2c0c102880a960350b20440a842e405031030074210092040703c7c00c0d00a840283d1960343ea07a0822541e00d4000c801340118200c1c0f001141700240300c0c1d40344200352114003103103038200090310740210382c0180c01003108500400540000b5602c200304171241d80483e400001142400c904004015009240314000b01e035082c00c0a102580e000000c0a5000a03041c4112070742c0c5031035001140c030803524140048149031118400403a11b0768014006181d000703006000c5c0c0200e5804607581c07801816 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 396304271 1250 396303021 396303023
    0x80c07120f0306050a0e06010f1e0201021e040501170a06030b130b071715060f1803060f04120809162408040c050607080d060303020304050f060304020d080901020a0f 73
    0x66820384155400780d03140c000d440003054140c0d004000c81c2d041640040d0740400091149040c800302da10007000700c038800c40216000c08402c0340701150515a5500c024082d40c010041916094441d020404c010304003001180c08803201619854075100301c1d10882444107400914030580555074880020114441104081c41123440c03460400d01c22080e0301e0f000d01c0e80c8002500710303801c00c56a0104d240864240350815500200003508481c00b60a20301c00203010391081c4110044810380c0450180c40c002c440c1c4802810940d402c0f0161080c40e03a0701c0c40d800b0081281110f018010420a81c15050024041d400381e60300504000152101c203c01c08422003540b41d600e502640490300800b1410f04841090413084462040e00d2806c045181030036181c2d84040714a6008840c800c00d00060701404101d6203d04895590140890901942c0c0daa4100031751640c2062003201e0048440324003403034052510004036031203660b00401f45c0d410190f0030340f1003238410740114030450b065104200700380000c03480c3c40071008501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 396305521 1250 396304271 396304277
    0x6170622051005101410050d0b03030d050901050c130b0d020d150305071508240904110a120b070818010e1b100f111c030e12030115080c0712 62
    0x605003803011110b0a2013940c0005941c000750384419280b5030781d003102c542d01c0115510b001030b11059203041403001030a4103403606034148400210b4800440300c40d00250300c1501420020026965000440545031081421000c41d10705401030070300c4000a0700e0040e0000c03821030880141015000034060b805c684290b16103624008400b001001081410803c01c1d018240e1480c10040e048041c5001070402c00c00a0240070404008005489006054000c603210504004211005a0a007400e0142c030803c0c010b240e55020300984500480d0070341201070300c60340080c1e204100e2030040c1d40b426000c45421102500c0b0070382075102d81e000b14030301c044240504c0c654039003001c4c060000302d202d07030110f19000d000000e145405803510b425141c0540750400c00da041c4c0301a16007000d010449030001d26504000b1a070040c414407005000c030805116a02d0380c408041a118807048a110907090182f11190303000900c2040740782d00f81401400d1210340300d0281c05801c8034400c0005801d20340d807983c0d460340c0071200342c2080c800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 396306771 1250 396305521 396305531
    0x703020915120108070f031103010921021615030b01020703051e0618120d020d090f031206080309061c0c0302030f1f122a09061706220510 61
    0x840b00b15005050041c1540002843c40c6031030403503039440c840e2040c072010303124200d410800d0100e43c90a411007503003241c1c4140d0050321009030f07450201ca01e034000650b800041c81503001600354048003c080c0010740da48201c0c4041555208041100034103024402d076030450080301d8000000890810404802d010260402c2000e111821003042c644400108a4401680c2c08502da6604040110741c103000d4003407514031595945c0702c0115117006440741400d614010340c6040072010a107c1c001110320b21041c03080ea41c2d19100f036941c0b9990030035500c5900849145410810140e41986080c00c01051401b1b001c2c06004000304418603104c08407a040044034021035000010070030b203015009d58199114004005403407115140410f0b6428100c107500400c01c0d41044034400d0401d0004100402155080c3d85040300a80400003040d1a007024841c410386035460b05000001c42c1491002481d0302554426100600b0b659603030101c40005004000c1185403c04203485a103404900c0c203100801805a00440c0070034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 396308021 1250 396306771 396306787
    0x50301170304030c030b04030c1406010603060603050f1501090302060c010b01030c09230a051003090201030e01090f290705130f0b1209010b0301090605060f0f030a06050703020915 79
    0x11600d04016255035894004020520008481855100550b90010504059540c903031030309039640120080040c3c001040904030705110840026030343d050b5005a46c0034880281d4070201507013643d50a0710031380f0400c0200741c0001c4178400740d07401c442042181458420f000e50703626000305920341d005850120982c1d4444101036040e58060017441c3c03085005140003110341d8548055107010300d076504034101503045250b4503035609640d0464143d01804000300364031001e40050704054001c0c02000401c07404a030800a03408000311040c81004180c0d9082504203116480903580e54071000c10940d0000184102001c0700c0d900001851000ca1003145140c0305c40790703241d06109013514810b48035849550300e402c40c600c2c00d005840510059400f841c4070441c19102684501c0f2286000d8442c0494441e09980b03080642d4051100c40c0e045107000701020f403401c4020400c14000d110310b44000c002c4003601680300d0b0907d98000f44043d40566407100e0035242c01414002d004001071106140d40482006004020507410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 396309271 1250 396308021 396308039
    0x80105060d0302060705030a150602060a2405091308070f1103030a050f2d09010909151505120c12240607020f0901031b060503060d12031407050301 65
    0x641044080710300c1401c0d111150303002540e40c00003c040108120010020640010341504a42051000390880c2450070381c071400000d550754811290740100783e04207498816128041911482600305151202441c6c50a080078001b20301009030100c4010411003092202040c2540058500c403813080743c12002e030601d04c3c03c0c0295241c68581c0c0485c441d400c200003650541d900305084900c06040441c8003900e8540d00d000c1180d0540243c06145940107d59903469901c1c071a4400804442100b62a20001c02c2e03191250740040b500b0500848150110700e250902094148580c3c5110600451600c3c900e0240943c41d100c00c000340540f14000880c801190715000902c403059059408490341c02c0c0d181e107030b00780d0741020400e44078850f0080b40200b1001520038155140c01c1e10006d100080540304244170b5a40f8505141c1a50300409210307140440004042000361090341164003615008002042003425030300d0340c014180408040c0000d043d17586280c5145c4140503c0c1407480b91420303445440e2a5032501f0108 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 396310521 1250 396309271 396309281
    0x905070b0a0c02121e0d02101a01031503081603030e060420012717070e060121230109060605030f100b13081506010804021002030f070c0801 62
    0x1408010354144003000c40158048001080a07804490702c103490880c21200905107942d10040c05003031301c140c3d101d202e481e020000b1a5440a4456800ca0780c11840c021030039412a8420142d900365050307900840040c5603ca900b03e0408450301c9031900c10042d03582d540d121115400360604118103178101840c041416054030400c0c04208144002c7c0115180507620a0080401c04800d00410b1111a003802d01c0c0d64407895100c08901000600185527503000c0b800c9003c20702581c4645840c0844407012401c95100110b001d504584489228482c07030348481006545d82c80e9041c4840040f00310152005400d0941402006411180110380020312039590f81c4561035544140c100410381d900b89642000910781c084d00b03c0b40d100001290742440c1b034031602400e1610340d030b5952140c14003c1010848000f20b5036400b813800c040b2400403044031410034802c8a00c00d00705c0700803580b081c0400c110100180250410701e034842c41c0c030ba4041c4107403031910f200740c2c889581c0e642001030160b0303503201d4540c020710080d1340902c18 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 396311771 1250 396310521 396310529
    0xa0302040528060c05030a141c091e1a0c1204030f1101060b04050f0a270614010c06021308030301090b130212071101140403050307020613080a0f0e060706090507 71
    0x4070011016684402e0b0b1b80380700300c6060204200c0004141e159100010061b10208144c0300c03168806c0b42a81040c490103408210700550301b06440c12110229070060413000020745600c1050f0020b0fa80d07040300343c682c040000921007006450200301b0403800c660589411440f40d0b00c680c42e20000100d5018000345842170320752042580f81c1c90040300340603174041d5806a0301113a604943d8501903800c1680420344014195000403482422081024041c6942c4041813180582172102040745a941d01d40400241c810b490500307000c540e05444080105056030010000386c2c10045050f1070b03959648180c5851540242c0c8444c2140d5503c115030030301e41c580a041d042015502c01c1095040030307074000342c8030403050000e00804107001140407a03410313018003900800c410400e040f003500310f40e142130308010341558401c440d000e0040c05100c001490f24856506c031441d495420200e1030381001004a0f05950105917006441c0030702c1441002500e03269604070003041c042d8400d0801280c2540e10340780c07a51030013800e504 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 396313021 1250 396311771 396311777
    0x220c0609060f0c020102190206070c0909120f080708060111100e0708010207080909100806040b040b090a0308010302151b0703050c0105040b0313060207080304050a0b0c09150a030204052806 83
    0x5503d0001d80e80c0054000080401e08051592600280c8009200362003400c1c801003101c0307c01100003440207020780c4501507039400391f0150500c900001c001241d030543c03031540c640040b6017150045a1218840d0000c5944448181070845a45030550501c40c582000c10a8985000e600c403084404074820034440907009040761802036050816958600d01c4134000c6203207031400b5101240001741c10010014450000b85403c0041d1234141c00d0a081402c25020211001d580b01d04a403000305490f482c000590403107103909940c40d00e201c0c1c2d013568200204c980016410701070444051001154041c841400a140810301d1002465502e1543c9842d0381040c0b86a25500d05003c401e0004004d0000010200d95001a0711404c402700b004c40c6141850007070054840242c400078010003008104100041c0c3d81044a0090100c000035a803001c1901e5041d1240010031904494208a09905003025074080c102e10402810094149521003011410491030b00c0550a400d06640c040c802013903440b501d0590141ca01d0307203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 396314271 1250 396313021 396313037
    0x171501120c020714041d070303090e0601021906020903070b0306030111190309170706050619080a0308090a0b0f19050112030e180a0e12090306220c0609060f 69
    0x40c0107916100c4901c00c00c458402d000c22095034941d100c0d4010100702e40700381200b84201807821b5650766070307440c1408118089100401d01045c0c0c1c0143e00300c0a40300e64416401402c0902c1210080b46080038022000c980e400c0e02880b80d0b460941e41407242d40c02803c0a1001e40f512450030300701b0523080d03414131041501098400c10840000c92410840504600c49034100407449001c14074010b4011031005001030800140030a0350000c0081c4c54000358001c1804840e2071030040003400c0403040f504154403503c03010f036110a40c8080064014007006600511820544061004a031074001c4010710840b030001c000907510040101400c0b03802201c44413511413210400866050064032405148000c40140520221003078102c0b5030344e103c0346000c3c1c000107504601101400d00304540c9001d4082c4d203604001c240100701200d41d81d8003003c1e082d203032040c4000b0f0082040381c036500d80c90020340c0e030f0b4082c4441c40342d694040c40780c0108420708000d030001d0041d555125035452800000404009500e44c0300300811241c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 396315521 1250 396314271 396314291
    0x15130506010206071b06060909021207060801061d03010e03070507061404091109131a06070804090c230a0e0105030603280c080a02150c03030a0c17150112 68
    0x5000e1354060181d08120304110a600160081002d488000600d401d05207940460140055086a14543e100b5102115580b40d40c9141c00d8440a890198030001078040c00100b00d645e1003804002a10440718034525410401800824251000e42d058803049500004002d010008100b00d0a0014030491800d01c540118141a000040c030940c424800c40720b407980101c4045520807401c407100408004c14111610290b054544098000d044201d100720300c0e41c1c4603821450810104a440440d40042000d1403c3d090041072001060342d03c2d400400c100500c00f8044002d40e5005a540c640061700d042c0f907850380d451050003010007a1319141706041040030f005008041e10300051503401804e21744041800e5034031812803020900741c903403000703043c6402490340050080d0703000c81c402c104035000b55000e62030301d5614507028040b80b049800d100140e82c801c00001300503426540c4010b00c160010f00e4440100540301c030280d50410400c3c1d03140c285454001c0c508488079a002403521205158960061000e4108 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 396316771 1250 396315521 396315523
    0x803061c0803150604090c02150a06050109031712040b01030b010501090b1209010e070f09050703020301080a0f02010e060f090a0e07120504080408160906140f10030e0303151305060102 81
    0xd442c8802000c2c00b03181d0101151303652425136014000515040185c50f4030300301c00075610030a10708421800d0340510041745041c00c86025107002d84006844081929103940c3d6140e01d2840203801d0b145d8180014400005c15044603201c143c0903a00405c0c3e41d08846d415814084040c3d00180d02c094140200307007004110340f1124006032880007c1024801d5042e9490962250242c102c00560345010b020b04540818505480c0c0441e00030340742c500702d08005aa584074400d0b0103d200a000b80700c916480390030030720001100c10090b03c0600c0c0c410f2511184540d12000810f120740c01c48100d812a074040440c000e01c01c0d0522034030010040481c0d1000301e00da4100850050512601d4131100d120340e030b89401c0054140075150040303a004081c10811100c6250340d07138141e62410221744c0122101c171800d00c0b41c00240404204049202c04a00400211900e100d00e02000480814841e040041c142c07a0040401c400c0c0b020320142d44508880c0c896a080410000100100445016048800545880c05020703443c0d0f4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 396318021 1250 396316771 396316777
    0xa05010c1805121609020a02010501080a0c0e10080303042a0302300a0b071412010b0903100603030e03250909020105070c06020717060f07050d0b0405040803061c08 72
    0xc020b4079880c803e806119442418000c00c244004403c3c0540c15001815142c158000c2802440c0f96001300103a076241c100312500c0d211072000192880d840d0460511030000240c4409412940302242c0c1c0d81102c3d640c0d80c0003411901308803010382c3e90203d042c10600740403001c0c01c0c83e010001500568006458110750000e0f00c0b10b540860048124000490424540301d61040c19142402280c0101c0d030188000746403600f050001102c103030300000c00511002c0c109445020985486c6220107a0381007517a030030700c50544403d070065180554103100d08612507890b08514800d65001d980a691a60804040030b030526141c203807850180c1c0740c01c1d070a4002c0b0419403030032521000d050385e80040c0f000c42c0e11041070004031480c1c00303032840160007000800400034030203400003640c00484180010044510100c4a40a61100e100f03c2d118042801c440c000070382154401c0b4010050545a4440060720021400102d4101e400c2200e04070b40038400042800400e1520741c910b050b03403415101d900d400310321705550b4101c4140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 396319271 1250 396318021 396318029
    0x90303070306290f1614010b030f1027200d050c040f14010b0403030224040b2805100906050312030403090b0a050a0e010809070b07050312090a05010c18 67
    0x540e0204407070110302071240c2101c5d446403240d101c150081a45081c20514401914081c00c0558070313140c0a050141800706502d1201c900d000041c05900c0601102d41c0d020300004e42150000c65521841c0e80701510100c0710720511030340203a03403156194049840c1e404a0000e02c9400620840d02071380c43c600003520025154400c41015507012405100400b0100e0103025102d885048007220030001040c0702242002a0044901075400c44200c0b0300c1039215060304400038040e00300c01720150000280450207980c00a0b4100c001c0f007840e480e0501410803980d03604840c040403401c500340c990051090b0b0340c05070745d40d5102900345004200f003014078040000ba507500d1400078140c1515404000a41030600a50300000101200710030b5654900e51501d005145602252040e0003041d882c2481c03802651203510600d2150b0707002001012524100381c0b03007807a03540010001310341c107200810513100f4103540030301e50300e0142214400804c0313440b02500d00a800e460600001808004c50700c0768000c215140c0400c40701c115 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 396320521 1250 396319271 396319349
    0x30e010f210e010b0a08030703080a09020a0509100b0a090e0f0105010206070807030b03032b090c0603020c1f05060a12110603090c0901060f0e04060305120306060d05090303070306 79
    0x9101c5400c0c0a0140003613012240d800364428600164640012000300403251182d0b40f0180c46699040003001280c2503104080c2d0070059800b0244254180010107e40092510500d0b02d03080303503100903460303071030303102060303120025611900c208103e400c031322003440d082030034121172324030715810030b00001d50710040148003604101c0c140c0e01165145001b540301e4854980054140c0365201d40d42400e800841200c1001c203840940300a603d480107105030310800803103aa05c242803c0c10685041c0b030480181d04a410b01354030501070f1840020180b0410713002240c025207145d8020680e440c003c01046050f2410390301c0018041c21785528000003510f800c0121100c1d0004031541501d83d2180f00b07440d854241c4010703011303411072604000800d409411000c02a00002542d607030b40515000841804150f5240740700040c001e60100c00056010a00d6101071a40407a0103401103040284030000601a0b84e4240c60207505500004180041164036000c4c84010340702d05e41461400d03464110604c0d40100c00d069401d400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 396321771 1250 396320521 396320531
    0x1b14010e0c09151f081008060915090c04061d010b0304050705010c03110f060906060d020a030206030601111b0310020301030f1203110c2503150e150103030e010f21 72
    0x2a900c00c50820340301040c04aa610000d540f22001a01c0c5070411b869050001c0a15140052410703000151940b04285117005050011503404140c2051807001d804060b0034010a0362000080e01c0700d224000051000c00282285450920440c01c50743d5018ac04c124403c1008008000101c0c0c00000c00c83d00304c030801e00e04001c03600f0603401d04461070880c240000901d07000b0b1356050ba2003c04001a000d00944403030003541e071541c440d041044000c0e940f128009402000302c0c0410409440c000300a1940701c5410b0414100881154900f2410200c4d1480400c13450340030024645024101040b40c407040c210041d00451641d411074541a034031082c16100100b5600392002140c051328800e07002501c10f000d6076009141c0b14070f6010701c9140c4860004030101c2e44c450703610610b101101c410707401010482c0e4110040038025030304022560040d101d5401221850310030161000079480403d85454002c501903030340c81d61344000c210001841c1c586040c040004228040406080c804500c049000003507071000c4c00018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 396323021 1250 396321771 396321811
    0x100201050103020a1a04050607030e011e090b030c090d140106321207230301200a090302030d0903110d0201050d0c200a05071a03011202011b14010e0c09 67
    0x85e501c02c40e0042604130001103000d00c20103400a909005403502600e840383d06404403280842c049504861090000c1c5805204200b419940b000554212290441c035914201120303011810a42000c0790445030001082300300c01c20090280705800151000d031302d20003a08210080d261521040d032004000408410901d40e60240d030701d403001d075008280c560b8155800c16584806600800c5203603403c3e8680d0320102c010f81c0d909071806202c0d40f52240310148001c1601c41e0a40c001012a402644414080c04098200800175960400c145c600740b040550383d240c1c030507056240000005801820041c080c10481c518400103030707007040985070305048202c40010204110801152102d06015106266030350449020688445c041402c6803031601940441e44029601c6410503010042c0140143d12074900703000501c1840600170459003440e00502d001403244002131f856007529088440c0440f641c0b40b0303844c44000d070841d080c0a2105080d06010250198584800c003140d036407480241415450350811010034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 396324271 1250 396323021 396323069
    0xb0702060924180405090d0c1b0305010506010e040b0306041205040e0f180a050705191508060307060306031104020904060b0d0c080f16110c0607030509100201050103020a 75
    0x1840010a5403046815981e00d200070150b640c80034140c0c0755020b4501c880d00d0b602d82050b003c1c050042903048010619144844812910042c1942049801d00440055611011a070344886806540143c00018080c1418000500440e4020f05041d0040d030405400360720503500450825030194001d0341b00c4149042207035040b143e5210790303006030380e01e40300542c184000102e00a4016104a07895250040700201042d1099a10a4803c8004080340e0000005102900341120000200061500f45402d60b944807181910a00c044004617030009100004001e1913240030410301d4010145030a0400ca42421600e4161407031800783c03030f86401285c00058218041c2c0383ca0f0701070801003d81500194940036003070b0340c05019004860807000000d1351140820030740202c3d10907940c0641c66440c1c516014020040d01640c0c0d40084103207001050050400120715a2545002018a10311960310242d4030194034082000d0030410600c2c44007103a03d0038005200503101d0500107400ea4026600c2140c1c0c04401012079 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 396325521 1250 396324271 396324289
    0x2220c0e180624041d010506040315021606090b0a020a050405090417030c0d0e0309060901030b130e070302010216212d05190209060609030f030c1c08010b07020609 72
    0xc2c01411550321124001c20038a03001400035100039841003080381700380c1403c00180303036801c1c012154407070b030100310410006000b103034042c6680542d07084c050304047c0015507001c00c02c01078078400da0304030303444405400400c1140f42070305600a030300010443c106211500c00402c40e01440c015580500308030008501032001403900d803e8080c08a0307400d9684da2901907545880741d084410740b07a015504010314642c0809000c0259060310601410381410480310400441c00345c15101003064100c803010300351942015940c081c0300c01c00e0146400400109285200092408440319810030040242d2401032120384140213008000040e4045880041b0b901070601030400300c80030035540d1080002d1624002c84003100384e50200c0d800c0c02803003030b1600c640d100da1307640b10090030090f0000c2d44200c072040000d20380d10780b80e03001d0301c040d51003e0122074556011049051455201c111089d240340d200845951050900010400c62072070f01d40380c5102e075035140c01c0b003444031400f1f4814024818440440c0324440c5484840f02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 396326771 1250 396325521 396325549
    0x8091902011704030f021911040c0315080105160512010e1b160213021c02030a180b15010c030206040204091104021911010b0a05040c030902220c0e1806 67
    0x1c10b000c42d051074540030304400341801c10740c009402003013800c4100d544241192100d140d00030b000000801502401c00c801800c07859041000e242d500c0605042c1c100514240314040c104e0302000084c64180302c03500783c0100094200010400604111545480d01c80083c800d0440b40c00c4006651992241003224441d208049c2504030840c10210b48802415050007840c0300c0d850080d5694405484c8040103030086c0d01c1690404d0b10b08068901e0352086405e2141e00441e0700c000031450019611031110b180c1e4404c41502c85054541e003506074103010301841c41e4284910500307024200300309401000e0380d019490303000061002c2e2003181d45079251000d10a88a8501c02c01e840c006100b150354a5509a40c0045680115032a1000616442108050400c14418203446c80401880d181c009843c0c60100405482010a0a000c040d1111507507001a1120040d0168000f10400d0028908403c2841c0f0070444130240f00d558104294603031a650340d074070390305508082e0100d07207025481340d5a00d62012035903000d05144 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 396328021 1250 396326771 396326807
    0x30c0e0405010207080d05040b010b04080c090426070611091003050603160b030a06090606020309060c100203071d2b02010c020a2907050c19092a0809190201 69
    0x600c00203002c00c246d011032300c030700d11800080302d10b80d88070240c40c0e481d0b01560148040b5540400d0b01000146003000c440c0368428421880002d050941b49482c2410144000540c8082d000205030b0b102040003a01400e21070050a91900c0e0500240400246107800d50740080320038940d8070000301e03041d62014007000d1400040c42c01e1030809241d55001d60781440e4000c0f20403640051604801140628190040104448281d8000d40c10907010004120462b805050a4503141c030680344202d00c1c41c1400c0c00914030417000c1d40c54060041e040b4040300006440032012561250140c0e5a2032103510300030a880c800300d41c0b42030801c041e840000b880180c46002a045010f5440166140c00244508615500c4550070003080b9450700c01c00d00040e51203809007c2c1c3e410040c0203821100181c0c4050a1056a03c08111003210707a0650300e41d80d03a5081411603624401020f444581150b00b05d69011603070001c15040c10540c50702d42841d141c41c650303594403a010510905201c040d203010400c25a0720960b40b120300c2d01255a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 396329271 1250 396328021 396328027
    0xf0423041509052512270c090506090408070f0b04150c0c0b010611071809020a060516060b13140f010b03090a03121b020c030c040204030c0e040501020708 68
    0x89801403549040e101d00301015040000041013180030600004c1340b1901030a0020f42e5901c0403000303540004981110600d0190754034841d5450040350342122091100740c404080d404005410001c09059090308400381050400051203820b46400c0314451340940c102c0c100d9130f03d501940c900b20301d040008010241210012400740f00600c014089400c009981a180400c400c060010080c0da5544a000015203485010001009114000e10040700352070301e80700540303021035200d03032010840300303110050b891501d83c1c0c4104480031801c1040941014203260b04255003030000034900f0400403d42503400138003187e156180c6d031103039441d400400e40c10030342e145100f4841d0000045001110002c2212240034500c0c0100c00000c3c04001c3ca42140d00400d4500d002e0140801030352801d45112641454202c80c5994a40c1064100f0240d8a090700e450010350f0701510303c407103103981003503d000c1c064035015204610400c0308000081e03200211008a4040e0300c40315071076540e14104180280a8503101500400c000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 396330521 1250 396329271 396329291
    0x90b09060f071b050a2c070c021e09180a1115071110030605030319020a141e011802120102040914180a0c120c0503010e010f05010b0f042304 62
    0x180c4810f040c0d0300140c404068003039a030742d40c04a600c100c15100281e56591441c0601e00203000d1151280d1002d42400c10a43da00e04a030302266a40088103051100341e819070300b04501a2816182c2550171445458a007218041c08550341e03501d40c0520800203010000025100c0119190450381d1051a001160400c3d110301c55410f00002c1020f1400c0c100340f03d000305e0003060602038000d2080c402906e10145c0210308280407022241d2062628041201c00c1d48a1400c86000064200108e4981400b41c0c0000d030282d40c0043c4400c1508515811454034264141440007150058013184100500c1d0116a0700c04029200c0510078024412500f1405401d410516401e803000320f0b550300c031790061410104040082a80e108101e07100c00c50510f004000142c03003203040007124103424645d1089800340130316a01070303903481000a0844071220300c17440344c90751900c2d000d0542106612034240102011400e440c540582440c0420a5104502454400070307041e0600c0341e603940003140100900d0f0b001800c100104880c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 396331771 1250 396330521 396330563
    0x3d050a030b010e37140103141509040501060302130f0b0103060308032410090302190303140304020609040905101503080a0503090a0606062a0b0402040209030a06060906080d090b09060f07 82
    0x1001c1c6a0360209041407030420110323080201a501c22900ca000941a00803110104800c0c4080036000307a4032036403100e4020016940b59040c0450705c0c2c0e1055000640300b400c9a040e003040d01c0c10030070f0850502d0303d854002c0002c81c4040007125030001000000742c40030440120007900c0441131000700c60700410b9510b440e891051b084140b40054138022908d00c1e1407007902e1340907211000f806010040010301c6d0085080c9804034008007030350304944002c12003801e0140d40400308049600005084c0c4003035000002c48031140b002442400c00d0a83ca5442109200f804d6444008079172256054100803c1b00020006040346402d001c4801c2465203c4000d0003034071341e5143e00405c40a403600030394468029030b2605080740c00310050f001c01e00d198001c4840506940702c1d007c110003500447d52076074050040f02d6494001071198425580030302614240001d1030342c1400b1140e403800c1e164503540d500740b2580303800511041ca41502903c69855040350b101c0d44d10a034000900050f401040801400d1249040c03907501d82c00340c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 396333021 1250 396331771 396331799
    0x315030c12030216080309100c08071a0618190b0a090212221101090f091406100504091806020d1a01030204053d050a030b010e37 57
    0x8060fa00704c40c0128001002d011051481d880b590500354001c00c441c05490400c0030341c101e0b4204a50a000d0b100f84110b840d01040c9a22880e0700b1500c00c3c0000702c0940c06d48101840041d000300d820b0f28003001d900c0711140107003250000605141c100d14003071103100b5154001a0850042620041d1103c0704403a6905c403000302075040003140042c1d0303100c480001000c00c1c1032007000c03003040354000d0060840b4107441d44548941e100e18215240c10400924404030303100b0b0511000030028030f030303140c40080c08c03d00035103481d41e204a0140c0300521a03941a030895101507030100645040d585843c0000440649400c1c41e0201185403000060480780007144c072150390143c0781e006061005004912070b401c412102d00442c1240300702c0c0110780e40208040b1440d002210074815071542d414520001050855a030644034584a66200c80308001030400107030900356507854014822411421308000034002e08400001e8100e02000141d00003210340a0094001c4000f0782c41a0844911221501141607484044050b0044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 396334271 1250 396333021 396333023
    0x30c06010909030504060f02150c09010201060e07050702220903080a1d061f030f0b011a0903120304030e0a030309051203180f0a170303011410020a030315030c12 71
    0x801048000610040d242c050110210390598403641707000d081150544442d481010307220214440e9107154050340d581d00002c14040c0c0c2c80803140d2611480101b000a0a44416400080d442c064000900c01c2072900142540c00f2580e0403a500e035420559915290700203800c0c02d02c0d548545003080403800038140c210105901901c1845800d000240c014400c101d05c1d80c41407810b6001c5503102c0c000159294030850014080441d10010b18100070b55603445841c085282c0707620a544005e81c010040100802000c038110308000d00c48125030601c00d400000985a0607081540c5880510000026082501c21510301d40d08080040510581c6512030400070b01e00c00171405880e0040e06200044c40320481d0000640350040b42c02e00c02c840c0c404001105020940510200309500301e9254030010036a00004a1402c00c25000c8000841d140c1d1301d0710710740700c50207080920141c0c040c0455912418009501042c160b80c00da82505021502c00c0308850200d801c01000d07070026002400705c002c04034202400740500c070713612 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 396335521 1250 396334271 396334273
    0x516180507080f0a1802090103080a030e240c04170c0a1208093f100b01050307030b06090d0327060c030813060c0206060a06030b1e0f03030a02030c 65
    0x303603580c40000d5800322000c2d55079800034a40320b40081ca030004940c0290050012018000c20003510503400b14410074400c4c0c20490744140b0200701c45141740d50500c41c3d520490a200000c1c0715000c0b028010800c2150b88000f1020365031f041c0720004116030340ca00c048800a00c0f0074207810a465007410980c17510740c41c8000316148211a08200000c0600c1005141c2065030740040d0454a000410401c000a02400d02c440c20840f4045040c1e81c01e4030b800703800e0101c011065008160000c0c5003003014030750030044482010301c1e5140ca0484100501e0b64060103a0754000e01504000541c01080d03070000312540a03021046900050001c2c6840805034042003a000b1008813004111111802c0c1303c0d944074001c050301031900095054403210010910540026070407001c440c07520001910aa120002614482c07520075000d6844a01800034508003d40a05c0042030385d46010050343c5100c00000c0c0320010030400c540c131504c01a0030301496654034003503102e1400c0307001800ca80c0d83c0c030000600a5180d0b00590302d40c0c042c07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 396336771 1250 396335521 396335531
    0x20f25140111180d061d070819030f11010e030c0c090402061e070210111e03030106030e010e0a110901120c061101090203070b0c010f06050307050607051618 69
    0x10304501405084031802e01c1448150030300440c50b18001d6560040c840e40b9070302c5000600345801080e542c0c82003031180104e500701c1c130f04295400080649800030680c440e80d80c550003403a0301241e001600c11040115581881d01d510504e0032007004446a8040c0b181c201082d5180c00d0050486520000052012a0040047d210781e800d2420412502e18001c0740d010790070110420500071010681108042d0071322118001c4d5003025190340205045d0088480740e0808250161114a50f0040c1000386504c0c81d02c0200440c000394003d00405da40b40d00041c4034440c03d158407020307207146a130002e4020740c079188808403c940818040d81058440b001c004141c1038010042c8800103d9844082c292002070a030300080c0d80e08055250031400c558941d44800d49005a5580d17040d803500590b4180840c80c000d040e00c0e00402e0b00d984000c140c250071668148155841ca524140c400c001e5034501084080481c0e00841d1050385504403414040d08000030441d102c025026000c2c008280b00c580c03034004142c03502c408041044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 396338021 1250 396336771 396336803
    0x717090303070e010c0f12090306060807090b060a0225180b040509210a090b0304050c1c020a0b13180905010c030902030c040f0f061202120c06030a020f25 68
    0xe01400c03d1709002e094901a80382c3c0c8401b04211001c0b1840140035494000f215543d00c0e04d5200480b00c0b0303501b0840380e680040740200080440d50080c0c80d4006e6080710210b152a4513008080c0d602c20040c00c14031010464a1504040800e030004400020843d44410311041ca0a044411005214404800e80b1480c0f900707000c5030200c000000c801812003a060601090b0b1224411000215040402c0610402c0240035005c140020f42c1c4001c1d600840c46000140300c5d84081c5070812901e860100403883c0d0500f03001281ca409039807040807080c00c0380d1a901d1803d641c0c49808010f0300b8500c4094001da0540740300b044101008248540c08503180c01c0c060802080040e40855080b000d8401e02107000e50f02d83e2000f00c4100d590b141543c01070b20a5042c0800c0007445020321044030b01901d41d140d104a6441c7c89000c0720809505101c41d421300e1005204000d4024000071900183c0700740405400c4109156001c2072044440c540c40703040311041a0003c5c1e82c000245c1c20683e0010300d058482c00121490140880004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 396339271 1250 396338021 396338027
    0x180509120307090b031b0a03090c170703030302090d020916020f060f0a0b040e0f030a1103030c0a27140102012d020d09060504110915010c0b0717090303070e01 70
    0x10780104000d50311039018a01c0c1044d210450b82010740b4808045107035401d00d0b20310078034150040202d2925a00c010421241c9401e15004008a5600c4420081034180c680d281c444404140d0009407907140c1001a280c14425021444103103215400030742011048051008406400002c00040d400c00c0c1e080710b1000b544040d21030b4882e107090311040b181d02401004524a5140d903080540400d0010780002810b0040c2c11186260103004007040e409900001019a6885c0c2d102c41840d59030350031032006614505100c038010215104581c0c03204104110740c204c0310031404a0200101d2501c40300308101c05096211a04061842400c0d82410b015620700701e046050b58085001e441e109a480f80a0901820001c1020030003a5000d200820005a644c15003640050032520607076001e10302400007a000c0e0b10b1604140200d440000c0d101000b103104505d1114040e82e03102100280c12940459042515203482c5800c0d40c41007544d10417010300e458040200800c440001024500c500c8240d565440f06284d0703a4019 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 396340521 1250 396339271 396339277
    0x40e0108031c111b0c030a1b05031605040b150c010f0e010b090610120e0706030e070e010b16021e01080109150902070507180605090f060904060506040618050912 71
    0x280c11605011303400d100c10201e002c0e81d08950302c1c201901d0320f01294000007400c0401c500800c40d4404000718000b00d902090844010190106070001c00c0022910820b02c90454810302c9158881d0303840764500d0105884001040148410309104a0344500c03805207203a001e03101001282d50910300d020215100380205004001211501820701388454503418144403200342840d801800f0b00941030300400e030980062081140b030340d00c60405400e1060070302800070151146941007095541c0f04d484140044031080c0a546c0c1101c08480751603541d6544004005040e0b402046c0280d071042c000040001c076620b01d130040032000715090340c8041139a81c80d00403000440d50443c00c070312611038024100780855503895004261040c000c1d01118802d80d91070382a640590840890380012a44030030741081242808039800e5009070f0000d032000701e103141c45408103003181e03802040903140a44450100e12141c036903034001e0024010355047c0c949072000701d40486000e080141d0382d94a0521844140424010300c000603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 396341771 1250 396340521 396340541
    0x3011701060b0d0b100e090f0919060e0c04050403020303160c060906020909010f06020a20090103050d02100b010804030c03121d0609010b0f210a060903020d2f03040e0108031c 77
    0x303881e8942c8c8403580a0341040100902e000303618491f200710300c6180f10580ba010307040da0b40315010100700381e0301c00c002c090305018003d00e2981c0102d00302028440001c1d004415a80e00c03640c40b940b140f01410040701c085030500f60b0401c000d03204910300300c400310911109400812004c2000d48641e40281d03070300e40c1d00f040200054401d150060700405214000030344c0302d0b1940740742c0301e04050540c00052113040015101c0f00081e8011101503000800c1e01c46c003103405200c8400005001c000801c51651200006051914010001010401000300c0c007001c0500400f5030303074a807441074802004484035646081d01c4950116410b03541c14446c1c10700140544505000da1311a010740a016030034079690740b02c01d010700e00303403900805080c84c0707030340c0000740344c6080104813204105008800100c0c1c45080c40c140a410220700d00d000704104110031071540303404100c2461045c0306001c00c20f54510020601c078402c0c0d080d4020740c1c0100c06081707a010000503400d0030004c090f001e05182001003120f010380710b400c442c00b12460101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 396343021 1250 396341771 396341779
    0xc090f010509060d210903020a0608040516050f06070311010e0105011a091311120a0c031b0c14010609020c030a02070f12020603060a0e040f030806060901020303011701060b0d0b100e 80
    0xd2040d17860300488610300041c01e2281800c4444686030b500041c20120305400c054005003252081000f0310038108001e5011604c0c9480d41c01001e030030400030510008101079014002e07280010007504251240008036100d06000d03008014281e10101e4040c0644400e10600f01303010f0b804481210080840411503100d84401031017154100090710465010b40081601c094040301d043c000105803483c002c541600c14540034000182d580030144014040340d00c07064040c0c49521201059803030894109440d1a20180c2007000d4905501c050010035001d803429812922645e400442c000188020000c007030300e001c2c0c034141c0036691402c0d00e034488014400d86902c211800342412020b40005410b000b0020340c0c2082020345014070007500e500341e6842d05c260580f411103105450500c0c2c0d81c04d141d8003146240c0c203c5002c542440c540a001030000703540340818011204c80c50126451500e5846007584005c004160050a00d0344401c45000004020965030021500844400c2074040901d441244c50301440d60b0024 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 396344271 1250 396343021 396343043
    0x126011b020d051c091106030c0403031704030507020d1104060f0f061803080703050f0a200f0a02041a03060c04031b18020c0703140102070203071d070804050c090f010509060d 77
    0x81021000c1c1410410a5a0380c0d007240346803031b0894072034000440c4940d0040461a559070310754030740101426103140646643c9081c5205100010754494212030101d90101d03080e1940c542c0301d0901c51031003460100c003107038801c0c03400000103420417000b02141c003103880035025030003203680d6000305031241080380b030f01c6030301c1c6058000080c80092050005040010700030300d0414140018242c01c201140d001c0348503040400d1000c0740e40c8520f0f450f21b986000e403a4030300c01c01501e594a030100350141c0d12040048000d12998403400e0003c442c088030022801d403901c0003012a0441d08142d032042d603c0380d100340415a15105001d1400c0d80702907c00130480c044404c05103020000301c1e03541c0d5481000750882580c4050314041e08800201095081d02141e095903000740c00140d480c0c0b9548105458200306d54007a030f881e15502404031400d81802d0401c40d030f200149007481c8015550700d00e050390500400b903440300e62008411050000c800460f40b4114140e4605607001031890319001c040000f20601140300901c240440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 396345521 1250 396344271 396344317
    0x61b030f0c050709020d0902030f12040605221d0702061006031a130b030d090515070302070e0c091203190f09080a0602070b010b070b0126011b020d05 66
    0x90250500d400e4003400548407004d40700e0145078181d03402040d01ca000e0a0301d5680107815072030180300c250f808464000003400c0d00364020030740c240307180102e00c80e10301400000704251814060f07080070034032640780f01d246440a850f201c040142c0c5081004290512194640e80080c245500001d003003409007003c822010415498242c044000e000380901c2d5a0844c8003001c00c2805d180ca802c03001c080002585880442c151001394141854142d19144140800042c0d940070032213622441000001e246080f00c440c2d90b901854102a403600c0c2e001e038030103200d1080d0682001540783c0c82c070703018120300c4030b08450b240000ca40c000300c1965203020301c20300c075034003480741e100300c46040c0e40104003c113041070030b0b82811000107a031086108e040c04034144080d6a040e40010700c280400280140c2103001d0705204030078030b00780202074a03403c0c03c40d0301c140201c00c105420b803414a45010310303404051100c2e007030400091140480345070660402c500d01c541c02038054881d1071840c280280c055020785031440a00000704003001e80c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 396346771 1250 396345521 396345527
    0x6040b0601030603020d0506042901090c02010605060409020301080d2f190602030109050c0415050d0f06080a020f0301052406160b07020708071223010510061b030f 72
    0x540394605140d83c0c0e400003c01601c85114140c0b0040c019005041d45207068200801e0f81e20040011070003c3e103801080c5500d0306041007219042d200e210500007031b58044c85105078010403540c0c020b554420700100e000101842d0307540065040c0c900e0201980c0344845807002c01e0710108a1041c0c4daa20201080d01c520705c0716104440c0c100600320ba130104994030741c6421100c141c40c0c40c030741c3c07441610015000001403004402501070b058100121800c007a181c6850440301e445007034040940e00e02004070001e4021019051f50f0089014219009010019903a0b540c042c295918000c10040b8043d400542421001e40340c184284c510800404c071505c00b042c440300000704040e1084000e280d034050414002203001124002e0a488000d2155600c96600d0514030000f81c64a0b096500800507603111240501990003a4080780c1c40041d0322000340034051410001003e408050340322003402a6113400c0412032604221101d50044401c0f0751580d44901100054411040c0c80c45503024002c9500740500c002d410384 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 396348021 1250 396346771 396346793
    0xb031207110d0c090b040e0f0d0f140414010806042d1413021903032a0204140a14160e012105041202030c1b01030207141e0f0604 57
    0x14081c2d0025a41070352002050421500080243d6a54083c080200d0505110ba00b00e80103101d00200035034101a01c086a031806000350381410000c0300d80742c9a000500500018103400c808a03070711030b2a681c48151102114408100440c0001c0c503440114074582403520900504c108101c03401c2c003450045000e20008501c07440d12441c8919514504018001c0c00c0204c01400f0f0420348031024440d10050040000d01c4c0c3c101105008100f828040400002c0c3d04480381d004034941242181c01d00401216807410a16000c00010b508a0f081060740c000b6a1504195140320b03507031840e4204010641c0140516108900b25a100807000480c010030550900074000d1283e00301051500c84080f9810018041c1c0341e603c0941d80051142d01c80081c0810044259a1303e03010841c20310040d424825810009541c5211403403d0610003104c0801c1c60420f80d1281c0c0407103500d140c21240c420280d03007040043d81d640d489203243d45003949001d07081d1041000c1000c90a1030380f410301d40b03006004c1d58549032102c260501e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 396349271 1250 396348021 396348053
    0x2f03040c210204020f04080a080301090b010f020d180b0706050103030908030403080d0f11271206060d02010203160803061003090c031106070212030a11010b03070b1b030408100b031207 81
    0x85c030180300010f410241002130310b01480c851074241b0307180c0d41750000a8090b1443c0045440c184101568294000380c0d0020b4116003200040c80e1803941d030042c45901ca4010a1581c001c82c80e0036030000ba40005001d0310f500414103c91003540c074204610784e2804040d0b202c1c010703400001c00c400b4040110210341c51042e002005000c0c3c00400c00544e0b0070303010700604840c1e884108800b100c45000b401d00e0700d81e4041d03402060100042502d001d01d0040e0134900781030316100024502c5100300003001c16042564800c0042d90f80308008030b448030301c1001960400c1405031700102c802c0c6101c1c0000c040307143c4804d07100e0701405440315444008171074083d00310343c0d07021422541903d00b01e41084081c007160000d43e0350900c0c082842c070901c0c2e0143d41c0d07510710303110010809c100319501c41c6d95507810000c60684036100081d8803030885a020a045456404403401c42074890403802c1240384030320012401003001800030070510308803a034400c02000481502d41c00d15442d09008901104191403d2003280b001c525401074a8001e9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 396350521 1250 396349271 396349297
    0x10f050d06020708091009080708011e09141e0c10050304081b0d08160305010f0506070204021605060603070e04050705060703031503080901090503070b030403032f03040c21020402 79
    0x21030311103c040f40c2c6e10384034685181c000441d0920200324414080c001e01c009854800000d20104d890b45000740c80c200649134900452990702c0c8007803400e002d6422401c078400d2030703031000303071428410720241081d44100d9150318203101c1e00030110002d60a15200240c2181d0020f03648070030342169100e071951340702900200e140c0c400d42c0315101c100c00c400e481c00740400f05c901c0555440b0000305003020b0000c2103410201038198000c0c545043c0042c42105031a2628400700d9404640f0702e81e4a50143c030106020b80203d00b81e0780044002041d9070402c0210200d0034030710030f84050701160501540d1710038003144068141c03400380c030755040f0000a0105040c07000c010094140070f42408188080038501c003000000c801c0c0d00c140e4044030003003510162507078021006001807000300d000b0140a400c020000d2068480078000078141036031200d03075054a000304c2400896040d08521180e01d814405004081c1903441246c0440e440c0d100300c00d000c034a5015007449003850b03140b03003040d4180313043c8198240002540460142080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 396351771 1250 396350521 396350527
    0x9030c010503101203080f0606070c030b1f0f0503010c080c0d05071e11070b0a05030c0717070501020d050604092a1707080f010b1c0204060b07050d08010f050d06020708 74
    0x54620102c20202045110b1b545071a40c1c1d180201d418445031001410030b9124071010041c0002041180c460001941d4000c4014802ca0300c132a0300b800118400c1c8550000340380d07004040003804020850850084680c250024031a04800100c2203030744200403562408a02e40502c00f2020380401c56012903800000b90914804021104149519180a03104000000b5034500380003e01c04000703002e0080245101042141005030684003d4a140002880b11206500129a0009110043c0080ea100324420380007241d44008504009005c1d52000000154031401c1c000400e000e81058400d451482c0d820609600d1741ca000600c104034209140c1e00c80451020000101040c10b40c442494615450b03040c40040c9481d078a454581400e00221300d08240048c3d240005000a50b110034803505031031850000c00250a0b441b510015004010710b801c0303a081c0d0980410142d00f0807a0005148080d0b80280d1039070251071b03a0703c60107030001d204c0b2401966000b2007040c012100144d0550050b154803441210900c0c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 396353021 1250 396351771 396351779
    0x60105030a270b07110d0507111903050d030506010c0b13051609140c040b03010b0a05040803070c06080a0c0e0409060b040c0207050a0f0b091513060e0a0b09030c01050310 75
    0xd034042204005490f40b010280500001d240c200440c0c0d00001d251002801c0b0b024403d00000c3d2441c080ca9101401c05a4541d000d42015541e61401d11803594051000642d02901ca080556448503000c009101080c5010003090856004d08416121070307900206048a076a900b80c00e90007800d00d0300c00125228400c07a942e00044d142204040805408603000004000d10011040c02168801070540444400300704030611240802d101180d05540300425200c2e80c404201c80102c60910031039101c1c040a00000c50100d007001080a015003ca0b5030555407020302d40c4a981204040340c0400b4443c1000c01c0d403075003c400a5007025004044042e0003000001110758860300401d003903440c6055414016080780c0410b21031440c2404001004e000d540b201100c4041c10081c91980b1486000c00003441000030941550700c6034903403000c82d10804d1006490b08200c1341e4940700a42041542c41050f44140040d10001c2400700481040e034504850083c001c00d05040c0210040d00e41d903001070a210111100c00310b0200e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 396354271 1250 396353021 396353081
    0x31006140d0c031d030a03110910030b06040305030703021605010f092105100507020618300a03050105130e0a060b0f0319031803020f211f0605030105060105030a 71
    0x100140462002e0351b0b42d06441c0078000e04031101450034100c2114240008400341d101d00396103114803a1117003000220084500d00140c840d014943c00145144000150b003403c042d07011030340d1401c07041800c402c23003400c90b1107000640700201c590701c24000041d41400200a2850401c0044121380c1406410001040c0c458442c4c0e414000c0d4204542e03070044d2103005000c005541040400c2d400f0020040c1070320a16142a50039480b81001209c041d540100305110002d076100b00d02d90401012a1800c010b0360b9407003c6100074000e04401d1088600c214130703e070b90055181c0d04600a188089010501500d040841e60355201c006207021240c15800420386904403c07035031000c100d800c5800201c0c4500701412070300b61a0080c40000003003452481004484c00c1080103844050101c3d50103007046030364449640720342103003045451042c02044800d20441d40340066107139012203081c0c508d009400c828040c50751904141826101e06580b03080c001b941c100006002c0b102e041c0d02004a240103000c840802c118082001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 396355521 1250 396354271 396354311
    0xd0f0509040f151a0a0c0611030106180e0c250602040f180605061c09060612230a140f0102070b01091805030a0309020117090102031006140d0c03 64
    0x184410a60710601c0c2020b012440055000600c001038013150000e94212440009008643e0102d080c4285011003070100f1000e90481c00504010b6141d00c0e8403980e44400040240b014040300c520744c03144007034011660803500c2d06050301c260a564140d91070101e094010110240010002400c003c1250b0240000209079000601c0205080c51071000075a0401200d00e54484801748041c203170310300d00602004991606070640c6c00c545002604103034207900303044031031f80a000710b41002040d0038035040d1702044465070700329a050720901905005015400d0b810f000182a192803c4030b200b1648001785440000d400c0005400c6440717003160035034407800c00d80c507c99405d980080d241181c8903407100c401480702e81c0d5544114032413004510210010550107071241500c0e4400c0891309800c240e1107642840559000e0b000310b1a03407080601d0381403031034600744840c03500070342060322480442065160000307101486a4070400301c171210aa00d2914040d1505258401131100404032814940c980c040b4042d16581e020301 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 396356771 1250 396355521 396355541
    0x150d020d05091204051807031d0105160503010e0606070309090507231905030c04030b180f0f03040621020d0629030c0f04050310020d0606110d0f050904 67
    0x2000c1801c0c200041c0182c00d2011685803010050030911003004170740e075024a000c1c0203421a07080c3d46915119400210003034540d8004586040e4200301490011400c15400644540014072248000c0022402c0072a001c0c88288515207a807480031f40071545901c0c07c0001440344070f1090510884c500e540e143d402d025600304076011004540b4a80042e1202c070800520b01400e00a440e0120346007a0810405a844102e103035181010071601000140285100328111030196411500d6982c1c240340048030b1006010301030541c00000e0180c031070b59654070440020040079890f4240c010f1800c0c5818070100725080f00800c642c03000c0300320040c0d25007a4500b0b0742e0b10003804841c040000104d5050b041c1000340202d415000152411641c0c40c05464a0804400d02680e40191200400640d64000307081e2070300060203580c1085070300d4003504c0080400c4203130903401059881c103a0042803003202c5d5034080075103c080e0880380c1c0c620a900100351404a03d4810350103030700d0307001e141d00740380e41010250000300f000c6a08101c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 396358021 1250 396356771 396356797
    0x40f0e070e0f060a1805060120031308070302030d0e012a05011410030303020915030709170a0213020903120d09030207080c0109050d03050d050406020d05090604050c150d02 76
    0x148031049039030300c44041d03000ca01a580520182c0c90001c0c2000c1701c00413040d60700e4515650744041006607104030340b00c0c2d840403802100100d021a03240070b415101d92224040b01d4900c0034040000448040200324081202d4004002d401850011001501e5104a07000b0f460b041080c00144070ba520004140e0058800402028512f100700d0213152082c00c644114042641c0181200c04108281415528580039290315284c0940c84825400114602503050141e94401c2c00b0080304000711154400e508800711032a083c050540140c0314800b1a40316072400343d0103908020148591003010004d5001000440341c040c08039251041d24400900d025004017080c0b03020182c0381c441074410705604219400240c0030840160001003855070000e4099036192040c14000d99842c5c140005150091050b101e1000c400741c2d040c45140f03000d03e040380003580b014894202d40307860b1602040058000040049c030071580b01d401040448850401c100b030140300308a608403006000c101d1010520901c1c0054081405445 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 396359271 1250 396358021 396358049
    0x21903060518012306060c0703060e01020309070605040303050a0e031507081501030b0a1203050d062405070308190902120c04060e240a0503010e06070e0607020609040f0e07 76
    0x84002c0b42911301d864008a4850242c140400c1c070644041c00709500450100c030b21941e82c0b5420558207080013000d40c00a002e851401c0c0a00306000010b4004611030440c00041d07130900c58075079009545502603030002600099042c0a02618a4051901c01e0140c20009080310000a4010110b480902041b260b8a000521201c18031200800d142001c000c2c50800f402c0502c2b403a410a00403c0c00d40e0a240f2440ca022075070a9031002c140340c05a8100c83c081c088004052003440d803640d003045000d066408940401450081d00309600c2072040e0309450750b03158556200f0303441d87c50702e020540740202d01003c1c01220f50386e50740100700107079030345c0d56006c00c09805840235014400c1c0790001c204c11901c19501c0781d000c4150240400004c0c42034812110b0481c0c0316806440420303184034010848986540d044030342c0543ca014415106807100046542c0b1401d00c0303a441240c002441c2d0b040c0040c0d4001c140009400001c01c1c444140d40f807a0581003032454a070070031000941300c2071404a0710310f03000b071540c00011954215 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 396360521 1250 396359271 396359311
    0xd09020a150314061c06110705070e0103021516141c09030c0608010e0a0e150a0504060b010e01090303030906090803040f03020c012c030a05030f0a0806040b06070219030605 76
    0x2182049902003401c441c43d01024403aa041740d40d11401c80b031401030400d9a20240350000e64412029500b10f541c000c130444e0a020b0700c80310500c020400a010503407090000983c1602d001c9608800c035100540c0d110122400c101e80c030b80e0b50700a098407050408019010340d00f90780c520040300d1046401c00305070360b90350340401a15504002c002216103400c480704100d041c2c40117101c8000410342c290780110038480006100c1c03195000160916904203020301c09003141d582886440b10311600498003544c000d10007040030190800066a0310140101e4180c08210020010030200c1d000b0344c0018082030207080b0105214145036070320f040d030f5407080b2011284055458581024035904100c06100e1002c00e00f0144ca211a10781c0116803e1a032149540f554540e1464101d19103840078403c603080c0603441411651240711141e0a07040c613030044056a80003a0031000001c07410f00c0e0038007600b031035400043d03d104d03e0901e9940911071611022801a03282091150001000488500c243c030711440308018001512489 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 396361771 1250 396360521 396360551
    0x100801020d0c1701120213020904050c1b0c01020712050c03010c020d090b0304080334030c020c060f030a05130c0f0905010902030610030b010c060501140f030307080d09020a1503 78
    0x103850940f030b8081460500621031990031321826401107804442c000511004154604081d2181e0b40b5011780080c1460107100e405820f14000c1c180d05c04031031507000d6003004d2800030300e40e807080840140f60040c0c0c0441001c00203444420703080c0b07081902030801d851241860101003820340d104001000010b1b4080005200701640c0901c1120141410700c2c4007502d503060a0710358000303600025000c0c0d103599560110708040d0444080c0b10b49030142e19200e0304000c110060b140940240328207040b9801600482903581c856213480401c80760f03004002c407400b5046480e040201c03401048000c0070a00340803017a28440d40428484d039641c2d0000d1242c03070140c41d08241842d00301c0e416140d060f84408482801882808919601e036080c3c680d05841d1071900146120f08200101d901d00c0e010034000d0f01040c6440004168101c081d16030300c1840c4c605586c240c051507003440070305d0368030720940001420054003440268111740c0190090517240e40000d2000d05080d895122070324a020701031442e64003203956a1111450440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 396363021 1250 396361771 396361787
    0x609070305070e01080a0204020a0903021c060f0612060b010201091719050708070b070210090b1e09061501170708190b01050901120609140106030b0a120b100801020d0c 74
    0x3050a0f6441044d4901070782d041d13440f001154001d100b10303004102400c0c924401d0203644000e5400400c040b81d40d4a0603031044154580400d41660100c1c00c090722058a514180a01d40c21a081c040300c000b010201a2602401022910f9480c1d0440d5202c4004d68046800b9242c40b68a6020607100c4507540d800b11901c84802c00e211800b0f0b203082c010180070b0440401d540000f42e500319a00400807510542e15501c0c12070800700034450b581c80c10b5203059501010300045c0e5101c540704168000c14861f03032042403440c41e0600281140d091049070300c0038000603101c4098020312014241d043c1010390004400480c013017070b484d008075000000138613141c00304210440b408400c15905040f8400801c036040f19040024403a1165003510390520185488008a128440e44504c0c001e01002d1010130200d8103503d03103014090800e00c64200000c0c01d01804000500d40144c80004981c1c040003000c100041036a03410100103401800d90582400c0c156000440c20000c0c0010542480c070b148002504148170303c0003400d860 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 396364271 1250 396363021 396363029
    0x903150f0712180201080406110a02011d0304030f150906020a080f0609040308071404031401020913060f05040b010c021e031905030a03020c0307080a020c010e060a0f080711060907030507 82
    0x20300300211071000c50014004100f80580a19001c002c40d80c8605211000c4d00d030424a07540c680794000f40148110b9170642c007000a07403151a0110802d5088220600c0d6680111701018010b01c4101400100166a0810543c404600820041070401c0c064032007000300d810112a1a011891120421840c03410822002c0d6106e48111800360940c1010385006110340c0b002040c036001c1c8008400001d80d1980e528082e14011a031000c0b25122460a248555000c0d401800042d402119100301469507241d45000301008d951014482c0e0142510380420000030341191100c00303040c0807620740c002c80944c071003500e0034400d15030200203102d41e551041e00345131900003091509000103c040b1421000110044100e520b5110b00345800f503201c0c0b02d14403105045100d5034000400707400002852142241e00420306458544c000d03290380086440e060305010413403043c80300107030003d1049405034030010f000d103804e5600400c0380d03e00001078546082c1c00e6480c114007561012f4041d4045001001008002c01202d40030f4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 396365521 1250 396364271 396364307
    0x6180b040c0f0e150c150112030e01050a0905091003050616020a171603020606040c052506110409060e25050307170a0e0106080c01050f0903150f07 65
    0x100c01c103000020500c103601071100b401c205815402094035075903038810f4041e42c01000121941e0321803140c41c4e103070340c4c0080d82920b01c02e11181600000b014845540060000c0b0b0305500c44c64031452070200111003641c440100c0d0740c14802c844030081410707100e2400d00c51281d928069401c00842c00d41c20010314160000f482e071803840440c040755a040c0c56012803c10b500c2e45d400319456802600000e1a80401d002c2c1a01b10342040380d000c80b295043c19400142640540801d680c1000440660002140c0078440c60342c0d100c00c00142c0c2082c0e180384ca01c2050300c80c594140100000180c0b44107681980030180d02645c0602d040c00c2c0c8a000903c400c1c80f4200e1460b0704050705048100a0004080300c200080d4540203c450500c44048001180e00b8081d05503015222100715101c01d551402d001400003c2071680c00c2800c1341e40c60034030003049409001a011b101041c0586916041005504200090b0307441a41801c0d0580a4595055103e0b10340b006900e02402c0307807030800c03c2e15250149004004100422001e03d403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 396366771 1250 396365521 396365531
    0x50603030a05091c050f0607090e060604140f06040602031809090601180902091006120501140d0309090603080a080a0b0618271e1b0c0f0106180b04 65
    0x21500712040310300442081d02c0921005070300c004e10160b4400c9240c006007a42c0a1518a01500c0e000454201e2055401d074985070013590310380004405800c8100c8005404c0b036410030040c8144000402003402c8803d000b0701040f0943e2050003c105940c015030322540c051380c0042100815110414034100a00001341c482100d945000264113948038818441c1d034030022900c01072481d110080340c02a021640d000b400300c07903682c109144070f503244000500c510400120302028804850140b40a40790403144c112064061741060801040065942c40c0b00880610031500390010300b0f4003040c00b80030011030050244540350b0f41700000207407100d10014050340f802c41ca040810b000c150b580d03034285c03540351804001c2d0510301000c0c4400709800c00d007030803a001140e49107010a000486600030155109280f9111400401420030b58820072803041515010341c102c0d052040546a9040729002c0c05890005004440348064403070856400c42d030f5035400411203680304260a01c511607041c0030b104100001503c007000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 396368021 1250 396366771 396366787
    0x327090e010f053d0b0d0608061005040c0e1e0109060207030f0305070305070516080c0a1208300a0b06210c1e0c06060102010615140d05040f030305060303 68
    0x181c5148002a02003000d110500300600380070454040c0540079450710381000a11740c5132225030001e0740122190052490400740041040c3c0000708109020703094072a0081c0300a41072a08010142010540c44070400c41150720558443d501c0802c03689031000b024072a500a044520001000d105050b0049825940010000c00000360764006400700142c06150998442e070580c42d00701d5480c425031001404078071070030302580b210390120400b40d400c58480500f1142030f85034802c140080100180b0645901180c040d0f00034010803070920081c41c5403031110904c040044d0101982074000000712442240100000c4100148141c040c800c518083d08101c0e682030030300c4501006240140c8900d40c900960303410100115410020040c15100707184442040b06824000711500c1c0300340c07500120b2501c52180702d10004654254018401c800c29215440c001c40c02c0c0c070070011010f0ba003900903900345e0720744004100314045507080c00b449145c0c0610310038040311585019908008003030f5003011785918401e030800c01c0004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 396369271 1250 396368021 396368041
    0xf220303091802040515031603110a08040f0506101d01030c090f09020324011401080105010f020304050418020424060c02060d0203040f020312090105070327090e010f05 74
    0x102100c2c8902400e8001c00c042d41c40c454068003031070703000c150000080901c002001c144480a58440d4003099010200410310700783c128291115000c103800414420440c82c00741c40e00c1111404d80c01801213001e41501840f50781c03401d2400c2401c503841003094400e48018498005503e290600c02940c0e00901901541036450b8424142103511070841031581d1a20011011b401c181c011003115a001410b441d044118546040301e680a00d00b504a00801c3e42c2e40046001101d001141d4402041a5a0050300361300f888015035844214001e0101544414000002c503031b95240204034082884042161400b03115106000654118681c012500200c0600500c21101001d982004842c20b515000d110b019440c004508144112024240018000020002031021b55642a41014825400c444a90260342c0c2071140e280a85001540000c0c81040080c0200348201c031174004954440041040300b00c8440f441030300300705096100404041d141c480100c00500284604084907030501c00501c0185011391001c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 396370521 1250 396369271 396369287
    0x308130201050d230705041a0f03041112010f0c1e0e0913060614030d08010f26030d0e1006121b0b0a0e0f100c1112030f220303 56
    0x220000d140d80f81c0c5040b600d0121101c0d0300c0100703048008440c004e803c4c0904001d15581c41801020031403003809082c000c0781c1a202e4111070307418400c00342682c1551551799802c40a0183d0000306640503008130311405126000303201d0fa0f442034400000005103080c24034000340c16800300d044000814030310401a0442039410001002108034111100e03e015641c4540c4016015031071000034041c0d916000d030100302542d229000e51100d00f4100c04480e02500500300840345180240150703101c1d400c2203202004800c000b80c40064000c4040c5a519101628500d891071640d0003101d40000c0c00344c0c558039410030290741032098540b0104e40b210305004048c1050032280e414112080000c20113010011800d02c4065848901800f40c00b0750703061980d80d809407110040001945001082c46482c2c500e1550760350346003004008000320403585501c0007003185030f103560218403140c00520340c1141c41c8917044440d90744148020180b034030f54848a00d4886000c90720794014050622218504071030209030502c0070035045600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 396371771 1250 396370521 396370537
    0x30201090f081509240103150e030d090f02060f0304030914030c06030603190b0103050d092105151e01150507150608072303010c1209020105040e0c07030813020105 72
    0x10201c00d41c079080807441c40c1001030500c00c010b031807240201071003690b1170f0b06405040380c5c00748008281c1243e425402904454440c11800c995500410560603284880c1c1c00c50a48540a224888000341d241d40109a483d84841c1c04805060000800c120400d5004903521b0040d11040c07000580c0d501c0c3c40408a0340c1c401100e50390520840c00800083c2c1c09580c2002100c4140c600180c5191045140386040c2406480038013044445014010304294500e114070382010407507158441000031a049588500c3c100e8007100d40641c1c0078000e81c0000b244101582d00c9450080940311916508139140c91a808903219040e00046c41024201c1034020702c0c6076000058411064006400848030303601e4025200007409680c0c004441406501e00004c0c04180d41001d840130048900311206050f5000d008040c201c0c0da84050460104220142440c640111588a20b90140c418104207240c10b4a56507011b078036010845520030001c000003045410140c0c081e000c6608240d06c2040c0d4220030317000da40040e00c4c1d4000e8a0f0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 396373021 1250 396371771 396371803
    0x50a0b090a021308030a08040311030702100809010212090f010608010605130b0a0315020306041a0904080f04090e0f0f0601030b060910050d060b0312070804140105130f030201090f08 80
    0x41c0440e40f50310360050b04005103c0503040304d0742c0e18410803000d00110b0007100e0a4000c5995168081241030740441202c10305940106500181c200d2618203540e003c2028214800666003449080c00344065130070304030f004403201c4000308070340300c1d600482d58295420354002045690521008012948800044205440e414100860940a043d0105e03014521540c0060400c8500c0708124492003c960b000b103029240a50741804180d0394801c207c2c6091f07411020682d002031900c00001c0119112402924540302c0704c1c40d482e8030746a540c14510090351185019180660020483d4011440b8108002d4185400020281c80e040d13146032900049a40d000704002c1c01a400c17600018002031800359a50040c1c0b030020301c91480d9003401d0074400d009201010000d8000d10402c80c01c000d400380d0740c5043d00d003040c0c0d00503041454582003210741030791920780071041810300c14213201c840c8004512200760400390020504d551800c520b1400010841c42443e40304501088032558180102500440c229000d000444 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 396374271 1250 396373021 396373027
    0x111030c0c0a0b0a1a0603060d0b041509030509030105010f060c110112060b0c162706151e050301180216060f1401090203060d1412040e0a050a0b090a02 67
    0x4507a16080c1551400c004090350030040c20081c10718030542c00001440502d5104603005110442072010f5032009850161303200c146464894009401043c2d4158000c1c490300e501c1089200760514103041c2c03081c3c2101100031643c0032a8006080c1070900c19140106801039031014098038184000d080d001007101c01401c500c415044e81c5000f80d01a0a64511000e01d0203820800265a0324410106801074400303407200d03000d10420400e68603a5590100181c03000e00c2d103001240d681c1900700301034003201800400a0942c407800300140010801e060f1000440301625101660402407440140c0500490721090034082c0910040c441e52880203250840d1f003164600069481f51507000e440940f0075024401000a0b08201c07060440c05e03241d4001c103201c5400c1502c2100f49980340c3c202c050603800708035141e0350015403d54a16000c0b403440c456400840c2810400e554a003607801c0c4111a0560042e000307964825482418858883d410384181580592006d008204141d01100060040b907409815140e0168003c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 396375521 1250 396374271 396374287
    0x3110d0609050d03060602010c02060105060d02070f1505090f0f0a0201050a0e04051f0801290a0909050d0f18030b0c0f0705250308040306050711100b10020111030c 72
    0x991155071281d030800c0803102d46109140c0c3c000c001d820503001e1400154201120724203200c0c000030709141a40d100030030641c203042041001c2002500b1a120a445503110320240e0000f02e00440c0c0014048414144042190710700640420301e014a502c00c603644a9116000e14850f0312404030305180050b0f424030303045584415141c01291810115007810b03504c14604400e00c00c4000042000150f00072080d0300d2940c40342c0c0d40d01c080c1800c850304656030010352803c0ba070b200c4803043c0d4001d030b242c84003420007070600f2243c1d600c640c51074086444541c3c00b20b42035484140b8015016800504107181c0d05840d10744140c0c02030580811b07500e5076a141c80010140762184001c1150440180e0585d0500746c400710040b500e0700750300d090465682c1c01c1c01510305c100c14404000101400031810800007545d800001881c43c180c61550790030000e100003020b000c00c0004040c101800400d05010078800b4208607100410b41140c188200030b00081045250020340e8940b0258100c9201928141e0b9403103000040030b183c070750001b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 396376771 1250 396375521 396375533
    0x3031d040605030f0a02010207080c010e0423070305040c121109040620190207150503150904060c030b01050910031a030304060203121003030c060f142a0403110d 71
    0x510b400c403542c5802210580305020b1400690182d01d80d000340d0896140540e0350118503110002188503500003940c2421141203403c26401c104d02c0c174050700c7d41600842030b06208155041005030b507a0300010303454206000902c454800458086c1c0150003016428011613a1810444c0e12194032190141e01b45d00009000d1120661207a190640d1075500803980c0a0010781e00101a0302510103403465040c0c89000541c0d43c0d1000402105845003908414440000128103840c91f4000034014689038914000300506911800501401a445040c011600c0200c88a000d02030fa4038040c0340303e0401c4024000001c081c4e40b00c0c041e0007100e042a00700000d1048400c440f40b5180c1034520800354061000280c0028010390000042c0f0099111310001c80301519460000e0954030310500c00580015622440c40c000706440f0703400b002c24a61700e0b50000444415007a000c032030028040715007400076001f09105205880c0c0300240304101003071700b000743d41c502429540c900580480500c07000c1d0080903803800000402007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 396378021 1250 396376771 396376781
    0x60603051b03060901050f0c07150c05040608060405060a05060904020706021201060807090501020a140a050a03050319110a0c0203150a090210050a0f0e1302120601170103031d04 78
    0xd0000141e41c500030480340c1c0964441650032070907010b4400c5000080382d680e0b0603c41c1c2c9004240024080d500750712603030300781324050b0401c140503a4007941402040405c40381d288104100300e8015182c1d00d440c1d510302500034207030346c80040c8000d00982c2800104035040d0340740e11315041502c0701100d20315184d07400c0c100414020300441c800188040e00c00201e001c00120704580aa04a810550328051503589842084403071011a1040d0307400350f0320855a44000468445d80a0740002e4904100c070300340038260f00c0d0240341c440201000e40204074000140408445000a0b45244400b405004d0084501030041c48a0030b120f460440d804114442c08070038115035081c0716081d07404003030040c242c1003401d02100d040700038074400500301e129039044d0204402c510302840560702c80f04201d841e0740c0801c05015000b0390307007980322080e000c2c0d0000100b8601250b903d014805000c591407001c1e0526064580b0000240c03005c80b440341c5c2d411100703061400420000fa484115180102ea50039460078110180c5004200505 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 396379271 1250 396378021 396378023
    0x120b130c121a031216030e010c020d1a06040c0203040306020a0c0b0a060501030506120a0b0c041208040e061f032a261b0306030a05010509033001050409060603 70
    0x181041070039002110110aa241c039800d046059540400c444c00080e00e5a00c83d103040882003681d0f0640c5140428003d010740c564001041c10021252030007036002a4102c1d0701010100c51034130749680400380d2840c410304501e510801c01d840c20404040040b02c081d5407801a444010200360300052a80c0d400c0b4822000305115642c4080644850b040070044a000b07400503010306800079141078002609481d0100c120f0f0907401c4e003a03004d0210702e074094841c500e00d00c500078583d01960600b000000f510240c0c110650305071070300031007819894a0414010340c2d541d01003d403400f449010300c21110303c0e003c124a1107401410703105042c0054002108c03c60866116103c20501070641e241092880c02240c0101280910302141d20407184161500c049032202e0307031026aa00b01e02220f00e1011800c4074040c80c402140c001c00020111022000c0a540703003401d482e02242d610115802c042101c0c0c800c442d400d070040381d141c141601a800340200a4507200480c0d28144280c5110381c0d21520701d08140910303644500d002d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 396380521 1250 396379271 396379307
    0x18041116080c0d020f010e060105010905100e0603090f0705060708040e0a09061109100c11010c030c0609051608071818140c0109210210170106080403120b130c 70
    0xc460141c3c040e40b6201241964040c9500f491500c90b410300d004200b660589405031160b100792400c0609210b00c241019040505101420760741d6101d9030ba804000d1440381522000502510205101480c02d1000c1136014a0158005201000009000354143e03402c1e901088020701181c1d8800c0c540c0303409040041409000c00d45080c1c014031083c8081d200174140c120041e04c52405140300090120b8464641500c041e06890704030702a00e000d90321806600d4041402490454180d10542e20f50300c0896140c850115119400311407001041c0741d100c07080000901e800c1000d400c1061074010360080d09040f100b245080581d4403d0011046480100d41a03e1107405c48a01c51488071040d5403981d84501e40401c260215011060018041a60004d10401c0b511400e000440045c842e0f420f000d4131003000d00c114814409489100c510381a52070031024020b10556035070303c1450400342406040c41c0c940341041c040050800c072154405403280030426a116004100002c0c07035920b1910308031100d8001d1441322a41c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 396381771 1250 396380521 396380533
    0xf1a07170a03020409060519090e0c0613060e060a020601090504080705010509060a0510060212090619020606040b0d0b070f111b0310050603070608090a0b04060218041116080c 77
    0x2906501d83c0c090400d444907a03d082003101c0c1c60740d0421003c00a58582c044108000300300901143d011500900343c3c0c60138400865448010000c00981190020342e10701d000444041002c020380d0f0342c804070030a5444419503015290400300c0100a40b10b04050080d00d130200d4841003c1401c1042c540100c3c0c0007950040020800c5050190b200e40d03c451081d03c050186074101400725443c08004082c8404407001500101483c10002c2030080181c0c000f501859407200050110702e410f42c440340951441031034207074060001481d16030100f2007200c4030003240501400b928001640013604455001e500f00010b801c01c40f001843d041000c44580e03081220b040c05500894034001c111503601500c0780b02c00e03c01181910020400074030028100c80c4102c80741d941c164007001040100358012a103982d0000c98803c203a420701e110507114554088015a02112203d07030010314030b11031020010f0703502548a002c84003440649a26000005103002d03002460705408203020402d0100500102140c9201c0368120a45035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 396383021 1250 396381771 396381787
    0xb0307020105090601240e040b03011d120708070204090203010b0a120308180304060f030b030d0804060e0c010203190314040c060215100b0a03200408070f1a0717 71
    0x800380000ba01c0c050754034410342e4004644405904280240c41c6406c00849001038282a0120f41d006074921a02e034020399a5400c4a820b07803000e01558021005004505074816501c846c19464030f82da584564030524024000980040c0040b001c441011390100c030003040b8001c840c000a40144460751007217500058942c000555000c0c0380d01c2011446010340c039188001d554919041c0c5440d4200c003014411500f0400090048a00500000d0202425483c000034543d5242c008039180140341504540812030400400040015500a00010111140c003030304449003501c0c0042d41c2c07070050802d440078185180c4480c22403180300b40c0c040400804a10600030035406d150502c0000702406004440050183c9204002004c262080c1c0d64003850783d14014034034651034501c2c5140e850700f20812500416803560748008182e8405039455000d210101ca8080d9154a081038613803030420698401c000d402910201004500d42d0340c680c1990071030310b040d05203980700114600740e10311604062861000da48082092a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 396384271 1250 396383021 396383023
    0x70f0e03010f14100b09030604230a110a140d030f0e151e16020907030e060f0a0c0914090a02120c030f0609160f0306090e03090405070305071b0c0b030702 68
    0x58018801c6040c4a54065140e51076080079100b11350340f0350781540c070560210300010192981d00c0d4048044055409200b45246034160501d00c3c0608240c900f940c803030cd040c00039072411000c0b80c0018252100701521040304100440c00406e0b11032806018468010103800d4100e00408610100d0740e001084c20040c0c2c0d907100a52032450b081200001c00180c1300005460003103100900700c40a1032141c6207446d441d00d00715030030040d00b044000c0c001d508041d16450703c030300c007a85c040150342d01451044201c80d44c40d00d850403910040324070b4a02c40d482048031140d42008200700c981500881c00300192004030080e540e00e840303007020341310f55040c25940010104c10003c1901003a0b0103180101840201034595444500c1004a014401d40e46a130f1210b1081c0da03408411405686105c24889403070401040082d035840800d000c482100e00980013542000401e080c032454180304180d402006410104580e044c0a000103091071414515803440310308000c3d40400713100c2e02010080060800c2a907140e40d902d172201000b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 396385521 1250 396384271 396384311
    0x9050411041508011d1e0a0518010c05040911090a0e0417070309090b120d020708060907081207051213030b1005010807051b0a0303020304031205070f0e03010f 70
    0x40503031603200c044102d039842031049904a0300d0510300c02c81154118030052007602d84c00b40c400040c0300c00c8040c1e51071940d03280520740e40c0706251464000401d4902a1407034100c03410b860711964203c0e45441e55900006400c001513400350392200c82c3c0040d81e0403400c02184400e201d695409940701603a00400680c0c55180b2100b80d2040748070f07504401074100b0a4181112901a4040c02808078115043c248400341840c0e0202994500042141445d0290f00c2509801c1c400c0c81c40191005810500c4103102c40c15081040070f410503004001480120f140c4040c09880b107000014101e00d0b0980003030241c003485820030100d030440400100003030340e951400e0f55800c102c25840c84200d80366181c00c0d00040385602d041c2c260704215501070b1501132f00d55070381000840b440d5004820100340b4207101c500c42d021340303181000700000741446628010717568203241c1400f038980031403c002910101e04110800006a50045020180c0305a60a04012213183c40d00000e005d8a04024182c001d90725107101010400e401c0d0046c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 396386771 1250 396385521 396385529
    0x6030d0518011209051f0e2812030c0f08100e091e0102040302040c03140106120f05041209150c06021e0a020d09150c020f0d02030a060507020d08070f0806010905041104 74
    0x69150185d402c14602030300d140280d20047c641100715500c03001102140c4000392010890220316052480703580d5107001d408032000c00320001c1d80c4c50041c1e1031119000900340011014505000d01549051050400440d0040c06042c044075000c1001c0740c2005000c10101003200d00b8400c10002105c0041481c034000c0d045840107a210b6030034a003680031580e020340700e8042c0040500740c80b03003007aa00f46007003a10031803101e10519202e20b540742401040046140301c0d150145101d828428482d903001d0200602c1c8000c43c4c0c000094a20b000015151041d412800014460350300032800341e2141940000020425004203580700c55080000794040c0403030380800c8003402c000c40c0783c40303065030961142c00c00e0036082484031400d008940102180300152414014041840703100814051600c4642d50220b4103018102d84100c4101d0740310828003043c4c03a014000c03002c02c24500d00e408070491400820040c0502a621851701c01e120705034002c06e44c00d03442040c955024002c0a042881450a8180b00100d0707039007d482 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 396388021 1250 396386771 396386803
    0xf020c0304031a0a0c0f030908190c170a0801030b090c0a031101080a05091f06150507050d08070c0803040f0803090a03031d1e012c0606030d051801120905 68
    0x155805228410120303202c3c19646c590001a81e590410f8004242c0458151144401842102c03c1109410800028108103988040e035210a0b07140085500b2000c440300f0900039800d2103e442c40035489644241105d411049204803a15140c03e142e0408070554a86500450000004014800d41b152010f10400d001ea0b075800c110f6640304421000c0740d40607075040203a0307001a100c0711441d90035501c1c01c1c0903001510000094140d62509180c042c60039901c26440030600206580c002c0c88014440032103030b400c0c2400c040c401442e1445c7c00500c1a000144d00404d0f0341170201c08902031007200200000301c40d42c41910f4569a081c4208041c0d41c0e0700001500303c0000c2e00308030691755014070444440e004e2a107580000c2c0440c446007c1504008005114200015941c034802c03500d0800740003c414101a0620640381c5851168202c154241100240071601030380c01843c03002d4481e03912204849031131001c1c1d810141481c1c41503004139041c80211030041595801c5c008100306010000c1150901801185 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 396389271 1250 396388021 396388073
    0x4080405090103060b030c0a03110d06020c030309010e0f0d090302040203041e050c12010b09010303030903120609200a08010509270d0809070303050a1b06090b060a0605070b0a0f020c030403 83
    0xc408c024001c100b50000030090400403440c3e800300d0508010074150741e4482c0e00c000d8106802c0c11600751868204442d5000036a46071715800345144030034001d11490042a001400d0480105071015101181520000f030244d40e000001605000300c00b07800840304912074a14604030031042c2001581c07505a140102e100e10300c0a003d070080f40005200c0c0301c40f801c0b0040c2c0b200031507a04e1520290014a6220410f41c00d00c10942003038045680706108003405000c100303a001070b140041120041802d240e100c0702d00d01d005400c118850406410030241811620304950300141552110042407908551a08103d100500d100b41404803110100725040140003507a2031041d45e42e00e500d6600c4d660740c92480041c2c04690100248080c1d107110300c4040300176141d030140075400f40382613548110032030b000050262000f81404061010b1480d200c0213010091540c1e290050501009480320101c810000d03041d0b1614940d80c2c9405207442d0f502d50140c034580c050540030f407511581c5d6400d10346c01c00408400301c40110120b00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 396390521 1250 396389271 396389293
    0x70f030e060702180606070b2802030c07021011010f0e0d0509210114070804050114010b0409021e0708040609080313031e0813090f0c1704080405090103060b03 70
    0xa8501d1683c000b030041022007440402c00c40d060030043d10090700700e41c00b00501300c04520380e005960b024003101140501000c09503a100880300389400180c19295004005001041203a40255400640c041714058a8001d007080705071030101000000345995400c1c00c511030320340f04c16a403114103105545000d44000c0000a00201e8482c818020010f034072032540e00c5280806d5089030614800900504000500440021214860184115a9440000c60b000108000c011003030080d40c00c0d8042040d10078500b54180400e5100e40c0c0110701035240060384c003052009840410884060303804003425507155841a882c105042c01e58003e00559001c50007100000070f07900000000c90300d00700d28003041100060700715955444015512007007410381003021042c800100e5520402000c403004114580e42e826490b04403a1805c3e10140c1c0d05492001d46008440c2d200700c0d410041d055070503103d51100c2c070b042d6034032407406031401d009580103507800c40c010b84004000c02c00d003540a00886941103040301d00310064 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 396391771 1250 396390521 396390529
    0x608010603050a03080c27010e01030e030405060a090b130e010f06120905011b080105030f030705030a0e0a030c030b0a181709010c0b090a11010c0503030105011803020303070f030e 79
    0x249100003491a40f10380c2e8201d0100f84100e074510380091354402294a041c035800006080b0804114030041d080619141a030311540e004188038800e82800e08040c012000d29104c0280c9078015441400d004410025081e452107204890400c058280310401648401d2000c103070003010520707801070510345200348002082c44110b104980007210b840f0354421a041a21b80844000b038940c0078400c580035902c854144407001d0401d00c010454038915941c0d00c00f590b2420f0308151170f00b001d58403524140e0f042001624003060010080f80d40074400c4d414001c20780b00e400d03404650801e92550028064010080d004020001008a00c074040c2d1011402884800740c0904145919401c1d44002002e00120480c0d1700e4041003d00b025007000c10050400d50000c800d1507d42451030002103410b0580c50b00b0200440d000c000c542e010081c1c480c5000e2138045c904401c80c0d610107a4920040c004e2605000d81d00049188200e03444c403042019542c0034003540d482e0440c915001440c00d0046a0440c0403d0980da004099420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 396393021 1250 396391771 396391781
    0x4020c06100e010611071a07060c0c05011b120b01021615080c2b0b0a0b090a0e06090a052d272d120c060705040608040b130c0b040603060801 62
    0x480c80000c6e0041c1c0380703000048280742d02418102e02100c08148000400306619101d80130b689826178071600380103415031510a003180c103410700c2c981ca0104540f94085007298041075000f07840ea110000000c040c036900006034908041310384014684c44801801058140d040c07050704105902079200d0f5401f6866a501c20f20f603134028401006003c92201c0000310381485400301007005e5840380d050001d000c00700f00e804103200c0d08043c1c004840090703001503000c0c100d0400c080c840004041c2d2610441d800d0804800181e80c911020300034211031621000851b072014401341c604c8111000c01d09154000345e4481c8090410078070b048600000340801c4050038210303803908002d06484940d000c0c0141a0040d04285072210000c404a2a10051040904c5000800d00100010003c01040301c01d41c540320910300c2c0b455443c040c4000c201d28100a4107010800c001034010340459000703031380407a081c1d616070358252805600c0d8420700c801030000608094009501c8144000410a40b403a6035001d0140640740d14002d400d0354 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 396394271 1250 396393021 396393047
    0x408100b0915060a09080105090309091303200709150e07020c0303030a0e0a17041e05030604060c020109050105040303061707150e0a0e070f090e07021b04020c06100e0106 75
    0x411003100c120309460058014408204907050410303c21b03440d403d607182110070031100d42c58107510000d50800c140c41c154141ea60b006d02d41301842030800c0380c11350300241090204000b03445006242e04043c08900c00078071402c07021b04011b00b000c010346180e10030f041040320442e10410510418000202d6030041c4049041010f11201070001c5203180c072405264001000740e143c000c40c1c90b0003105503150002d04195242a4030303265041c0215200e03404c10720320880c100e042d503074605401103020300200199140862981e521503080b0f01c5c00103c0084504040c0e01520424200408a51034203080008140d0164040002c3d581070760101c101c03601c1c01e00070f100e0307650400d0301030445811642d010f095130540c801c0c00c0c941e20075503025040b020b10a0f6140c502658555054801202040e01403141012050b44104c080c801081c820100160038101244041c2d215880200c681c3c040600c071313080314020f03510340360111401e01032400c0464005190440e9001114500d82c05204551170410340001010340c42001030741551 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 396395521 1250 396394271 396394291
    0xd05070201180b090106050916030e1f050703090b040c15020d082a0c01060e07050405010c0303110906071412040305070e1f0603050403020f0f0a0b040f080408100b09 73
    0x9002030f00c5001d40700600412040a03992901004940e13a2280c1e4821405001c0c0c0c00032000e2a50b014040140a0701c0620079800c40d01d5000320841e030003038059480e00c1c84201c0112100001c00303882c1c8280890140511110142101141c0e038140b00c10000302d0399800003119010440c441d2121550a02262a00c000000c0702d40020000e102007001003c8014150180040759000c0210b00c0d10307480d04180440e0800a04008265505c007020401003900d141000d45c001d2040c9811460507041c0130010300a011212009402c0680d210180318140000008540c00014020f00460303c1351418a0130303c544154045501409002e84004e400e00c0b031a0400c20740d8140d039400303400b4026442c01e055107402d068000400c26101016034580e00400b010340d4120701405040681d902181601d407508001e8541042000480b600342d01c006550400041d0104083c079105900c00d2030304080c2d40700c80c10700c0303111501c020f5000f0701040c0000500003460b801c0010004c4001c0e1409206120300c9000300304020203981704803148940 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 396396771 1250 396395521 396395561
    0x2040e03030106090b25050a0b07051e0307020106051309110405040c06120b0904030e010f090e060607080f220909020f10021e03041706010b1b0708120d05070201 71
    0x17116941c01502d9580d03002c0a81d4000c00c5e500b034117407407841c0c07900e008140c0311900b0036217071981440900b1888590041d118100303a4039244412400d459082c60640900003289400b1010a4a02e4802c0d084400185001080d02c102007407450710400003800c1d181801c80760781d2292000c8491a0030070380105403083d80c00a002a0340c0780e20700314054441064548091012642c2c49854900594074144401e001d140641e98104c021400400090a09101500000d0078031103400b40820080b501402400d40c040425500340303480e650385180c25070b000d02401d901c0c030340b503e440802c24400002d681d46080341c500c00c1c040e603212442079031805d0b01c000729022044040d402c040310380b2841d101414400500026030809104550b064940c02340e406410384420848030516400000301004605180c0640e82d50810341c071405010a0751412000b40c1c01d074030824201900c03034405000c10000804050000318020110a000d480078070040d07603c0c400659114040d030b0b5204c079190401140e050b501c1481030303541828010707101d00e003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 396398021 1250 396396771 396396779
    0x302012d0b010e0f06130f0b031006020307050c15040807180606170a0914060a0c26150d0c0801020307030f05060303160203010b150909060f0604060c1a040302030702040e0303010609 80
    0x708580c080d0803000362a001d42d400c005038007c0d19001d0038008001030001c55440781845250b10120001550280e4219482441078001081007c210000010f00848000401d91001c240002850003580d02191890050000000e404461000001448200414100025502c803101030751040305594075043c860181e140014100b0402d0b501c083d811328010711801840808600040d460304c40120740388880d0b5078841000c01030081c0c0051040c0304041403280b00b5844d516030303460301c480b007220300400c103282ca00c0381142046aa0340b20002840c408a412035060804962036403000c0b0701070b40c019604003000038a0107220494080d840e108260194800030041c520304081c00b840b1528027103040e98103a80c1035684e2000511070703035a4261f021a03011500585e6070380324810030080040390500104200c0c0101850880d4110aa407a00d0844043d205641003500e014584ad04224920714008060000141c1662040c031051603000005040d41d503108a4081c420a20095807807922400203225410101d01c3d801e40030300c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 396399271 1250 396398021 396398029
    0x6020607030c0203040f1d0c0c0a0b04062711010306031a0a0e0706090509060a14090403180636090c0302090d080301080706020309030c0d0302012d0b010e0f 69
    0x1a10b442c2403803045038141901d0302c3d1440740e886840c0c0e005006603100360180d405c2403544a05a00c4c3e21068a5a00e20301b0060a510010380700d0007038420090540b1380c518005010452140d00900c080e0000c1607182180c6840711150210030714070700300d00780c071056440d02c1c040000350b11030702401d425aa800020800d07002060301c005801620041c1240f00d0048c7c94041000090700308000300c600a01c0302d40c0e00c1044691a103014080740700f0740030306003d010b90b241070000c1c0020402080038590700c1ca000c2d1110092a561400e01300ca100130603001c00c0800c0c140440001440b0795101e6144050702c0c0240c0f0a45021404910781c15210141440c3e6020041703450940c2000550065880507282c58024100540340229040000e5170b045441d040480d501c0b980400140000b81e41040408081c0034207000440c901000d00d0300103a500e018003030901d40714515505070f12082504c00c0d004012805140d00502c102c0003140c0300040c50424000300c491004501c2e017044d6209645c070a100c020f81202000d440c10074211801c8040c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 396400521 1250 396399271 396399281
    0x9091e0311060405010c030b15191b060605120d091716091b0c0f020f0619021005090d1b0302191214250201140d050604050108070602060703 62
    0x1582448040038007120340310824019a40b00390b220310b00000303481d5591080a000c0b5445469818010308a83d80820701c255055000c48803103200c414108880c00b000010704884119803443d130b1044480c0c00f854034904000c030720340025003a143c084944031008052454050759a0080b0117003440040c6509104101c46c2c510701c080d10901040c0711041c6c844152244d80c0601940c801039204492407540c035002503144c0b400982000c49100c1043c540394180d11441d490b01c441c12648024080e20660500c1038038401a41d455044030340c0340036100c0001d40c1203111620007079142d08441030011021070510000415540002c1091080a0800c0e2070b61600a500c560022051007481d0f0350880540c0701d00000701ca01d203422030114a80040c0b140895180c1d5602c40000280f14403d50203005100b060240000580c20242c0f40c0c1c43c0040c002c42400341b254188444c0012103040f01c001d14060014000010b5000c20038500d80c1115104010a660070300c00c50340e031490090381d5100d852141000603041480401d504910075000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 396401771 1250 396400521 396400523
    0x30909090111270103050405060c03070309060c05070213020405240c01241505070303150f0b0421050a08130807091e0510120206040b07050304080709091e 68
    0x80c1d000b031035885511240e40110b40007940c2c6060845040880c0348150b501450b051002e103000c0c40b0074101a642c0c00c1c0e131a80f024095004200c40480002c04d014800d6100d00f40168000e14140001d991115000d41958040e10090740142400c240120011030b00e402120100c0c2c0000e0201c22800c0d51260034140384441400900d00c001d00100241080700200b40541c0c41d07540c0c0041d80c003240e000350b22450b06448200c01c0c0d201d041400740164001034055008001d075150035805050100700d542c4001314a0694a1854000542890a5210108603c13540d4030152058802e07240f0220324403c85249130030401180900010182e5203c000d401c00014503a801916280c0f441618000e82c45480300f04080c01c0036000d4001c9100d9a03640c01d58030b010035203090b41c0e0462250350036004000505098011b400580d005004034156585100301450031900e820003150b00030b190318003400ea00e80100e0318000351a907115104110881c441d400c0c1c040340c1e043c514441e010800361b10a81d044200300120454803101201204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 396402877 1106 396401771 396401773
    0x100b0301150e0a091b2f10050a06050f0402070c0504090c0306020a030c08060f09010627030609050705031513110303070c05090c041d1003050a0b0a060b0c03090909 72
    0x3001c641701c4806d4400f00c0003c181505014984040c502c1a09040f524241c1000401101c59008a05590342121455201007030041000103a025815011b03000840b00502003240b4900b40e407100010500c103158000c1040c0e604e031103090480c0c100c04034010120340c3340c1d00340480087d40074041c01d0b800402114800ca2358699000421042d00050003450240403c260740590348400030207076070100036610141100e02d50744900d01100a0240460115298840d0f40c1007c1124903000c120400c04654198032440c0f40c0c0e4840944e0010700035003240c241c84415031007a1204103900c0500081c10860f02139035680300703e40e00c2c120a001502e880109510401c04007840b040c003841e41c1c1804161000040080031400701d86540b014201c3c50011136100501512035002d603001000680045284640c0070070741c0c108030107581c0304c00d01096841001916501c3d900104081011450420011170f00451a00 = true := by decide +kernel

theorem cover : BRFrame.Cov 396223021 396402877 := by
  have h0 := BRFrame.cov_init 396223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 396223021 ≤ n) (h2 : n < 396402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
