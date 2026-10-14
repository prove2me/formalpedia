-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0874
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:20:19.659022+00:00
-- url     : https://prove2.me/submissions/a4d57b0f-1964-421a-9de1-efc38d828fe4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 157014388 ≤ n < 157194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 157015638 1250 157014388 157014413
    0xc040e13030306031b15022b180b03071205040f0204090615080601060e04050f060907020a1a01090501080a03020a020405150402042301080f150103020d0f060f050a060c 74
    0x1010551211400700c040b480d1740c41038840514100018010080c5001d00380860354a50000440440d0098580c0d010b0304083c041e60b6092148e41400d402221400168041d02d618044607554121110356042c00a002c444000145114031070703030b4484425801d8080c814604550086400521711007004122a0140c18540d11070984644514000a403481c074100089010007519407011005600000041c8420785c0e005410b01c1404809607028009400d0000110518920050100c0c0c0924809030010303d155100300007081041d5081807503070a081000f0103001182c500d0901030440c0150600000103a00c207030000e415850180c2590181c12617259603420000549400340005480958000388040343e80c0e00c03031004100601030866000e840c940300c0300403111104038031103890b4180b0500d00c04101c1a840c800025507409420550280014240c150058000380556051a07000b07510700120840d030b050060348400140c1d803016142209095842c4100074000c040c6009890024000c5442c003000180070300100c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 157016888 1250 157015638 157015643
    0xe16050304150504050d110c0d110a12080d0605060a1715040c02031804050112030305130602030123121002090a0306020c03040e0a0b21010902100203070b0c040e13 72
    0x50094540c414400b0503a002641d09076400e4000c180444022504440703035101c003140311009070038082041800a0140300490201904023524103603211400c1e5505072140c0003418211403074174450300c00c07414000c8080e00000383c01d0199900d060800b050501c1e0400540315101059503800c0428055180300855001c030290002d010458402c903100b9080d9150f00480c1c0c1095134550007543c0351168008000369104882c1e0102c0e00552030000140400d2040d410000c14890700b5041c0490389880304035122100200020028010034808400402c1c40c03074588410510203c0c444c0c004248034072042041100542007517007024019400710710301d4803801c03e03a83c0240c40c854400410828145a4a450300c8040c0d038000785420040ea00000b80038094084071840c01c0d500041d00740010408103890101080d500810603c21140e80740c16400ea10030402e10940041d03c007164080d0000c4005801458060350b2a0800381045442170b03e100c001072401c2c6003000984d401c5440e94040242035440c2c0301021000100d44c80002d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 157018138 1250 157016888 157016903
    0x180b0109081c03060e010311090705070b0f0601081b1b070f081c02010b0d030c060b0a0e06030d030e0703080c12040f090e0303090a11030313030b04020108010e16050304 74
    0x2800da1014811205039030030085110420b00c0142c0001000c4a01a4101e89100350b400d40050021402041c01c0035020202070390100d00940b00c0340400d4600f8015020000c1c101d2040504001010707038985203150180000f1f0300c5050640d15000c0021140400d00707461801da40c182030181d00d285a102043c0d01038102d4009050b64005130310340225954503002904007100e59030261078004404004441021661034a501c000c010192020b00000c040b120058806400c0191881c045414050700d544203804540f8000c082080c1c15a82d030316115490502212380902c20700507403101c500317040e001c2e01428058038420b4000d07001c01415540d54207030303d410400d01610300f407207100c0084d0320202d400d038014005000f8217070341030380c0da2881c2118000c1074603203280c0c00c0030403500140b080c0440c030b030400140304140c1a4003182c02c805060b200008649180580c0c10348200c039000b101000001e1000d00a10b0030700850007030741e502050b40c7e20360405c08988a070a5940c8200e0400189840034014414005182c010f48034244 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 157019388 1250 157018138 157018157
    0x120c18070c05190515010e04080a030605061b0d05041406071a0f0f060604030812150307060e0f0303040f0603020315090c03090d0905011b060e0a080d1401180b01 71
    0x491603e000c51540d0f403903030000b02214401c000d000701000701c00f6050301003110f0020f2941c10001704400206000e07200a001400102d030700c0545074040c0c1c0198000e0304014181a4031035544803509100400003081000c0381d802a00e46a5a5080c81041140c0913202d100d12208111000d482c14440e155100e8401900d814006d5141e44000100342e5a840b406103001c0c0040304081d04054000d03081130540903103070314070556041108200103504481581c041000c840c03070740d805690301c000342102e01c1b2080324400b81c0d241c0504178010032501c0d0031000e944901c002c166840c46885201d0024503070b80c1e101314000c000c40f8003810101048a1482030f0001c42c0d200760958942a1602d0004001c906010b0090b102d54880382004820800382050030010036111182c2490107500e07003450038002904100300701007510303810440920681e09001460700290b20500c0d05004030380051030142003950380d64204680c00c91082e410140b41042c448e91211740345050300c0c02d0401424511000c007180307c004002c080c081505008001d603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 157020638 1250 157019388 157019393
    0xc0d0c020a0f08030415021b0915030d021608030702010e100311040b120610270312051b070b12040f060e100b04060e0103230604030e120c18070c 64
    0x1280b24010200030740110b0320359080c01c01580b0207842080702d000465000e660b80d103102c074201c1c207201c02a0001c1a506e04020380c0303e40c0ca1503454110704456064040c801e454072001525800a14034407446914000341318aa034079000d060351a0300c100300001e0300003a03850060098915050802808600942c200090380301409481c1c40d0013904194441045a2004179948001f000c2c100c9010364000011240c00000090441d400342c41d5138003581d01c00150820602c2350307195014003c2c1c15003024542000c06544034098500006000d503001020f0b488020091496090164000240780d0069450b4083c020f41002030465041c410f10070700400c10354100325562206008143c0750b00c10b070b0740d61b0000000a03002861001c034900c81a2013400d003240307005600d0900d0030450244a00b4542d41583da0040144544501d038906088541c8130160340c4448c0c900800d0180802c040d00031802c540d400ca0f041c2c501503130f8100c0c1507110a48607182038043c19004118260300301481d45110014035403022031030506100c40201038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 157021888 1250 157020638 157020659
    0x1f090b07021324030503030610030513170906040905101e05090709031a010906080307050a060c0e100f1403060303031501140a09030c0509090d030c0c080307050714030c0d0c020a 78
    0x194005e41d00c40d000002401102d007000154100560070314101801a42083c4040d4407152810030006800700e101da41c620082d109400084034032400d0001c002039101c9d510b4440c0c101c02000c082d030300440300040d41d01c400511210440c1c84440c81d11280d12202e001c90b80b426080c8035174500300618101c108020000007100040c408004002d40210340d007082d104030360600388170300200c50302c0d508904181d41c414490840024000503020256070360101000c41c034010040e00545202d10300c461f045a01c2801012010b20703070b59001d41c0d281145641ba641388401c44201c4629030040c0d101c19604981c0503001003001030070040125070311515400c0180b4041e00441680348220340550440c00d507980006080301420800e203d180c568080c06000122012091400e0800b070403903454420100b00c0c018161036801d4194028060b112180c0300c10b4110003815520700d4414002090b65211201c103c0340403041d135107407210781a00001a01c0100c1c42c00300c010250b00e19183c100b5600780e42051001c9a220b41032380c80104810b40382 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 157023138 1250 157021888 157021961
    0x20f0a0b09040e0a0803042405010e06100908031c022b0b09270a080a03061a03100302091302101707080c0301091a040207030203040305100203060a09020a030b1f090b070213 76
    0x3040d00f840124108cc9040060424180404408126415000344030340140803040f20a40200544d10f5030b11030003a90741d035002034003c1c60003007281385250584040c60004a00030384040e070b01414208000303400c02d0b030040015400e0103803981a10400701c102c1001640001100c3ca1481e450608212078112082e070380c030807010350300c00d5102c3c100290f140e0100700000021280301008940075400000d0862401c500c0d036280302c0c803640c40041d20440c95240410850182a480800090740250013000f000d00d0410340a0112070504822441c80c0e0380c1c1d03c0009003030b28883c00600d4010b201e2891000d2469103001c179030f000504810b101e5045c404082003001c00b4151b0320351005100c0140700341c0142d503e452440c28414200300029030030480450040007006280c1c0d56402440e02035030368010b401602c4481041d82100240301c60b810461b001703800b003000343d038086608403404601d45001d580c4451a150f11034010649134021001300030f401c4001600307001a0301501c6e410120010040d42410b901d4444003001088030b00c0354 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 157024388 1250 157023138 157023149
    0xc0706030b01022b0e0607120e010513090903080906040c030204050901021318060803030c091005190c11120a060203071713030f0306051309020f0a0b09040e0a080304240501 76
    0x1300282c903080c260088410b0504910840380c0701c0c101507040e11020104100c07401003c0030480f111010400c141c1c0201e0070303203400c50308034030312100d10b10b03114010f000081c895401d040e07000c140004005626480c0c001407940c0f045900490b9901e285180d942404007811740600410300e61b540030f0040d18501588404540000c012665a00e6000c0c801c020402c0d085a109411040b2070790010420040c1c40c0000c0d0007200c5048105551030380000e0501c6008450501441403000d40d021030307001625948950110038000001e00940000145086030410407014030010702c1ca03804250071058144000c17400c142c1c0650791082d450b00300041c4101c0c486030210f85c7c00c58116041c80c118a030520032101403550141b111400040e090500300003503410078000502a180c003085402ca003d4449903120219282c00b5902410400d01401210700d494545400c0e0380c6680189201d50b01886c50507010003020640010310144d5950040c0b070541c42d40d00c1d107485102d1040c42013030318082c51310a9400b41450848280c45004d00908 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 157025638 1250 157024388 157024453
    0xf020c12180a0302100c030203040e0a050709060810030303020739050306060108040f060b060c28080f030c160c15080106200a0c1502060a020c0706030b0102 69
    0x2a240840d04140341c486152850184003040c105000603280c461a0b500c2d10b91440c1444004d849445c60100d2540c415a08000f540d04400c00510000c0a426085280281c0030307034546201c0141c803104112280c040807540c120501c3d24841d000c00c08139001f40d0042025a008240783e03040c5e4600c0408002e000180c901001e0100054285010322203c80f4041c2d100140c03100724050300b250304000c1d0000340406400350010f06030420159011040220644c4459203116015005945a130381141d0060b44034a8410b0f95440e9a08000d09220a44038802d40840d030316540c0080c1c1c0d98240103000000883c00c0c2c10081805134000402c02c040f42c01518440362202d0b0fa644549000c4002e181040302a03100c100c3d0355610503040c0714031840188865504000001d01c100c841e48820600c41d40c489030028a40a01caa03006000601c290b44003003101c40011600b9142203605408407403aa480341c112007000c03489903e213480b134190405e075024080740d4401e0708903410700ca80500c102c4441440c2d0365900301011015044050151 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 157026888 1250 157025638 157025647
    0x907120219060e1906020703060b011107080601150207080d0e062506060e09120d0b0a0305030d110406020705060d0b040e010510090e030301050d02010c050a03020d140405130f020c12 80
    0x514003160740d0359410301134400d0415164a84180695103581034000105040e032586081d140756482003c861001070f44400c03c0701c2c1d140e070790384e08000c0d01c640c1e00f8000c00c2c00760a5203180c40103030180002004811617910000515203440c000800701c4042c44100e051660200e820045a00c029003035004180c4208003202d90007aa6201a14061088070095442500c610000c4000c1000105003c1070300321000d0a034014269a40350003001c40001807042c1e0b40040d510078100f5401005000b070000103410708500c41c000800c4800da191502d14000c1c0607620800c001644422410300480c100300b0081d01e40700b6a80c11004c24254400d40019041da200c400c0f10212a030765507030401c2200302d43c500300000140b20340300381000710f074001c440c5a44e141d1105000700341c002d4103000001d03411a4800c06210100641100a41e0746100280c90000c0d250035172640c0c17090010f800801c50b0b10040c140c08040780c0844100600c0c3d00c0b81c060082600501901185645210440c4d090240811910f030078410008200c80c02035070709555 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 157028138 1250 157026888 157026917
    0x301110307020d0219020f01120b0a0311090a0b0d0f05030d091110051305040203041703040503030901050907050a030605070327050610080c150d060608040b060108090712021906 78
    0x2032412403010040500040200300300035854148a107080340d0300a291042c44884400342c2070001e80f12b01c00c503881d0884203818002041c0b080e102202000b203603048400080715210441000c0030f4604d9040c940ba441b0040314030060000c0c42140319190607601c2001501d00345040c100058040750600041944c5d1082002c0f00071080303180404071030710001c07001d060450603e624940a44880c1c20b980c043c040c0200d034000041814842e00203001018525101c44081e903074503042c90300c0768aa42083c3e441d0701d071660a00c1c0c003286403203c021420b5400e50b40080c00440c01e031440c0d901d4080c00b0703020160814003070507561220210a00090604481c0c5d03240380d1090f8922400b420700d0301c07614004000702142d050340b4141109000c511000b0952414040c41250b09c2c8024280440d14100306104414150b040315280034000110507410501482c0f195000c1d007800103441c1d032144015074201c0b10455250255800030001805108044c0f200100c4d580e00203800c580500ea44a01c00403404111030300920301260080c0a01d008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 157029388 1250 157028138 157028143
    0xb0403060c020d0504061805040c0e15030705310803031803030402060405060a0909020d05010e0106020307050a020418050a05030c1204180515030109210504060c0b060301110307020d02 81
    0x1c07100c4140c402811030200c0d040b001016406140a07050800c004181d49917840345003025820060040200f04020300d03030705c0c8240500081ea404030354a002c3d414603009400c5002099003940c0c4100002d03100e80d450514490340c00303002904100c0e0b00345030a002e161103106014260783d81250142c0b0580d0010355903803c0c0380e040140c10b40394106011101e60f00400421005031a804140c900726a0240c4240381c54565010702900c1d981807a4016900e65071002c115402040b505030051412a00300040b03144080c0d0302d50f20220785921036844040d00540c400d4881d03100500301a070101140b802d400018031101d003a5603076060b0074259800010350749548041000b2940b030405101c416034613190b0309240c3c1d1406150144c0c501d826183c0f482c151388000d54401c0015168195001c02c3d0407d098010000c014a000d00d00d4960004010700030005810603040c0b9000000300c1c0154221002d85d9030700e072102e90400b6690340e1483d200b40d10060070707541c155480e5103040a00c54454070185000710f640ea00070b80b8888560010091 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 157030638 1250 157029388 157029401
    0x7032a051c03051b0418020f0708190c0b180319080103021e09010e0604092405070305060607020d08070b040b011502061b0309010603080d020d0b030604020f0910050306010b040306 79
    0x2070f0100c0d03505044c0c4c00900c0b65281203404076104184910404001030400100a02811700343d01c514120005a8008000300503000348840030908896000d0500156070071906281c109100030b01ca07030000c0c800315600090001e458105143c032001100d16003648860100c410381c5400f600d8901141d00e0b5801441146007010740c8410fa07128004180b42c05009075800145034032018800c0749170000d0a0307000318685450b02c1c2c120b90682a0008001c1070281c07203c030a260f54030740303191034500e219030300d85400700355128424081c032401030074000c00e154180701003030302001080c0c081d0420480d0749000800400000404c43e41c0342911441c00b40c002c81e05158903013112150001c800c10322040c04c6400c80000c1041140d10310306842d649055012401c2d03102c0d0f5a00d4000c1d801081c0c50b40020780568008140e611207d80789400800c84000e14400500c003d095050501d5690481035500941c003903034a00c1c01102c5814200d4003e607000000d40310016501e903950022034100042a0000d04045200203018814420a030140c070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 157031888 1250 157030638 157030651
    0x120c010b03010212190e060f0708090c280518040c06020a050a0303050601050d0f050709141806150703020a030e060310030221031b0d020307032a051c0305 68
    0xc2d85490003241e814084950002c1c203820480b001a440300507400f01700c1e4001e00920a00d503044852500f40401d480014030422588840080c0081000600400010802803205c070b40c05807400700151902003099481e807100400303040d80d1510b1301e0000102035690103041030041c00d072201c16103128201401c0c81140c150303440c3c20020648d400203000d00e00040001950000789501032400042a0319610012205441060006001d4500b45041c1c00707c0c01c0030961041c0c5c014900c0fa104d26545947c3c070150040b4441f5a8144507501c40440c151081c80396850718001a4844401428034002600c0c904900d103180c0c1101d8401d40040e400380c07000c42c04258104c00c1310720400c02e007102d89a0070340c07070b105480603807801c13550000034050141003a8050424010b40350703034200388078004142d940700c034000d291000d40400e8540903280c2501c1402c040652031070000c002c842d8102d825644581400f440081c11411040c03100304040b1803085441c2208011410a009003008000350204059140700d403400014180c0340043c001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 157033138 1250 157031888 157031891
    0x180307090e0106080613061e09050610080d050f030a06150909150b0a030e16090b09010603060305120a020c120d0327030305060d050d080106020708070b0301061b05120c010b0301 78
    0x14001151b1412810144e959880b03840403403140c0c3c5114005645000003040c007100a401c15441d44100308020540910a2844d00301c0a10b80c030b547d41c01000e9840642c0c13240540400ca0400012150800c0003004640c4142c0d41031f004240c41d5529807030646c22401600a0324001104030f082480180101d00424039107110084455407024100302211103284034a260020a00d0b9440e40a2520400180b00d0616054810709402800a0750303410200701a140c0262810703c164080c0c00007080190080c0f20341c90589410070010b040c40c1c0a0700b400010f0990140b01004258030402d00b045070240e07075560144402c0c0700e00c40c0150002c43c0201d42c019060f1a941000d45607006094000d1a40481141c4180c10002c2e0300752030089800d4a5000119100c070070344c0311000e0018007491001c0c62500341c000398030238102c0d0303ca6800c0f614004c0e5190909901c51138a4040d802441c00c01f00f00402406101e112400c01c10300d1b000700480070300c01d00f5940b11031910182c82d141761420000070507001380c00307075081c802c403030b01803005500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 157034388 1250 157033138 157033141
    0xf0303050c0118200a0e24031b0d0c090903051c090506070f0306120302030301170a0f11310c03060e0103030c05030d09080306120a0f08180307090e01060806 69
    0x503101e03030004410203910b1401031202c1820885645d0061240c2c001c2103088514000c50038400000e031450300848032a03400c011004a28880142400a070a41c400030a01e406459184220410015103000c2980d060362440341c00040400c1c00007951142d150114480c1c1c6659649080000d0042c0e41c080380d0303a00080e85c140c0f514200b040415030119442d03601a80307a26000241c481d1101e425002011690001ea4208000c00c0e40c0c51708240e0004001c5040e9984104240000c008540740141d6a00d81032800400126281240400141a8103109149514010002401480000080814203d0f510803c4030444001040c1c07440200440c40350680c009880d00d0144101d50401000c10940801840f0040400c5040c05181007400811300c180c0d0180300070b907134007802a503200d41440d10654005490852142e003081d20b40702e121080001d1103071030721036114015140c8104103032200344451704400d9404400721b100600070b00c01070354144080d07009005043c400042000c07540c2606401c4680c107802148107a0310080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 157035638 1250 157034388 157034393
    0xd050a090815041202031308031305240304020f10020a0b07030e030306060904020f03041a0112051b010201060f030311010c091208160f0f0203010b040b0f0f04060f0303050c0118 78
    0x1945994020340113a5800500050000e00700d145201b00301d622100b2003402900411140c0e0040014072441d0125070310301c60596168410440b80c4040188101085080608462a503402c0e40000d158090300080103901c00a03080404103032240d00168248006801c0640e46400704001400c059812201c90702d010080441c0d11080c040d5a88406003100f80700300c00210f049143c961f19034040717680828515004644a05003480c001ca000d00c5146005403240d11040c0003c6a80058903c3e50100344e07030404018050440100c42c420b514840020804d0704554039544040727440d404600880700214803a46d03400d002c00f00c864038010b0031104100002c1041000d0307018100154013804510420719508014283e58401400c0703e4000b40c00c003428401440e004840d00313443c05012180c07100d10304160082c0c000340400c080d200d04010845004030807595011041a000b104541018050b0300003011003d080001c1070354848500071680d4081f503000300c0001d01c0c00282030762851004c4c02005007401c210640c01100c5022503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 157036888 1250 157035638 157035673
    0x70909020a0c0b061504080d030507020c01090b1e0f0717090108072106120317010303080a0209040f0e010207031706062b0f020414010905060702090405030c0d050a0908 74
    0x2c0ea0003a0881242e800814119681c1210100d600c0030f143d1400c03a500c59440c04040e071182c0300c45200001081c17030b10000070b40c050b00110380101c800c43c0580d07851031035900b42424551950018082c100d0f110340c81904850030425140c3c0100242c00c02c4010140d2554510310b0201000050b1140448240b0000d000c0405c0903604050190703000b40060510032803160500a09200c11110004009505800c0100000c1c804a00d01d800458482c0260f907001c03050320400c03221002d105020b01c00100005d60807400100e000391540e02400d0071410040000c103a00340309900780c01c182c81d030b500c04442059600062403010190440501c00c800040ca181072405880d00100045a5020300291180392103171103002d0184005c0840d40403035a030200c9074810032001c95000940c2000750001c0c0076003240e52035180c00c0084a0340c0540b6100045a030020010743c40c0a00a500380030075040003910454092000b4071521503a884140b0082420a0a9964041d2502070314840105600780d160301100154000074804926034184 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 157038138 1250 157036888 157036907
    0x1609060f06030216060221060409031205071112030f060306010311040209040f093909020901020f06240907081807050a23060408100f11070b070909020a 67
    0x11800e005860b0707004030810135005012280001c0806100107090000b02c07c0c1c2ca0003c440d004049080a10345a440d581484102d801e10310020303010580030070440707001020135082030b54881c0152500d0100c009000382c2291900e640c410030111b03440c9010041080310000b00714491703403080c4106c000b40000d5245031103074049152034914035030040303800040c0301d402510303290084a248000c2030020401030b825800c241b40f600c001c04e05240c000b02ca041c0b00000c81c0003c1e001030b0400210f1070348a2040031620301680c1400941c441c040903810341c0903070340c001000c601083c810180300e0100d0151a0f0a030300e001c41c02c00130301d036031070590704600c552801d50502008a9009a045a0180e00790940140000c0c0a411451900e4182c0d4045a0304c200c40b030708045848003881c101c1910158902888020407900c0808000560140b0302458085502071000006058403540140c464182c80210008441c4203442030341c0c0040e4081d08054a41e401001e09118800b5803102c0440001c010041b001c600703008a000700182007161 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 157039388 1250 157038138 157038149
    0x19020906040905040c05060c0109030315080d0c05280309060206010e04031b020604081e1902190e0a061707060509040207060b120d17060108010614090a081609060f 72
    0xb42c03480090200302000b41c05d50050000100b110351207900426145019000c500c004900107420415590700e411450310521080d00c40100240c100f081013164101c0d0103604000003550325208140501c1040c42c288003002c40041c8160039402000e0a16040150010902d94080c1c000c55100b100100000800c01506542051780b52800c0d0080b02038a5540b80c0c42d03d21101e9010b54400800100051096000281164078860040d0304150800d161000b140e119010308400da2918040e418504006140c1500341d890401c0b40e42c415521300d00c3e101c81a5841400b82280c100e41080d130389100071b102c000c00701d02507000c20720721040040c920300c0d080c45402003841c041c040380c080c000c0342c001c20315100300903a9030400c44100001600541540c03807807100c4c840c0d49041100d00340c000f091210380a0554201d600ae0b90a20800043c2c4405030a80d19240007101c0e112507140c1d590041403414040c03505540d40d0030102c04005c11440008100d0080310009a0000300c44a40c44400d04c580350050402c10b03a55404035070800c552 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 157040638 1250 157039388 157039391
    0x90913051e0705060a0c020405010f0906090b030c06091807020313080d2307080f031f0602060609040606031b0f080a030e0d06021605060417160212030f0a0305190209060409 76
    0x121a6010f46d1041d01a0a000358064100740000c94540c0c036121360201211200d1105114150741e401810302243c0400b03882d00d815405c021218086414507000400c4450000350900c0b800c0b82c0c441600d1603540d20295a0400180c200141090850005e51340560107807500070080c04240c05843d20140406203001204202d418a40340110414081c2d0001c0d01d5139140c00c0140940e80d00104030000d40c803580b00321042d03e855490351000c248a80c0505000c0d800b40c0d40150005c3c101c603242d100420110341c030014411140151203a0001c40042d00d0114010030b03042c0040c81003940365042803001050030005130015121030744402d80c0400030030b138420350300113101c402666038116118050070300c10041d104031960701d049090303000c82e00000c214000030014801c2d40510080c8501c15540d038101c007494481c142152003081e40d4031030b90102520345401c1c3c00020b20320440440c0e1174030f00320600c0480a40c000710840f0000ca40d0395010401501c01c44964010a60807096045140c09801c000103001c6000d107000310390045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 157041888 1250 157040638 157040647
    0x5010806120a030e011101060e060a080604030804082b0209090106080709050d08040f060f03050601020303010b04090509071a0901080114030601170f100501080c04090c050d08090913051e070506 85
    0x141d002c0c815006e403006c6548024001c0f15219642c05101010980d03555001c0c843e54480000c9901000c140a4051941076841504c25140c07612604125084209998101c1ca1042c080707905192440e4044801e030400488007588850b0707414200148201705a100b2024011201c0401c107649502401e44015608110343c0644000f0a81c10300c20b1407070180e80c001038800c040a01001c10125000f01d40500905565601445641d40e09001281c40340828440c04020000500c81405a112590400da50102543c002c40340f24554510a000c03114003401003002803150000342460b415684860014007500060004035103981c0c000002c6507456038140306030301d800050a040001c200406001703850410000c03a085890000b200104c602c02484284101c0149100e00440c0e00803508090007030300c1520745c10044510395140b5220900c54100e40c0844100c0701c02c801001005025510342c1c60309402041074011a42c0011041d140c5145068410b0319010740032440d01c0380b04010410000b403130750b05488040d1441d5445 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 157043138 1250 157041888 157041917
    0xc0e10170a081b07030c1205060c13050d02130504081309091109060d050609241308090105040b030a1a0114070f020a0e0411010315050604140f0904050705010806120a03 74
    0x1300035440e0402882180d919070000307009500f4402c0c00b080b0b54041e40c203a5000b46c59078807000c281445800414102c0d00f5074044e0400007403030708072094411540050800f0707000116240c0c82d6021240d0841d0b007114138140c080b51105000448c000b1542c0501388925041240740c03c0f60720780d802c5030280a0320741442501c80c81d000681d01c0e00d908407200d0f1101e50000c1200c07450b08250700e0351515204036400405440994182d02d440900001030307210b0041602c07180144080c1c09603103940c10158403da444078140720003000001001c2070250300551085040547c00034010380840b11241000401621881c1041170500c405041114608c1c1190329842c0d10910010746107585d84007183c45402c107940645a45002881008148208001c8070900080300f682d04212180d0720005c840406262030041640020b0f042c4802e10281c0c40c100614030f2003840c014442c0d0400581100020180e0b40708903012107194004107820041c551b0081440c540005003210030309000b500c000f901030303641d5000c0d0300e01a042014a03442201c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 157044388 1250 157043138 157043143
    0xa0c020f0d05030f042108040b0709051f050f0a030e06151804020a030b0403030e06010611030715020c0a1b06080103020f100309020303160209010503010e060f040c0e10170a081b 78
    0x15030900d41d20310000641b4151101a110707910485040c8d642d00f0b01e031000075849030710a07000d01302503803402000400c0203103140c000d08130a05030088002c400c3c044c003000803505c540d03206c01c050200c12665950208039412680d44c418100100038000c0e80e16800f400003c00c80642e11707896800341c046100c4480c42c1c0b03d03a5036800043c0c0122202c0d40b02900112101060006056140d0049554a01c1080443e030007642e0300c0004841e00c0c413803200030345440d8106200c50f030005444d1008016216004030000b60505440d2a00e080c1845000e10003210709204109503000d0440310600704200410382814202859071440c0c001c106214000780005105a81c01c0c411000030034000c0d48484c0d02c0e00d402a0807641c8400800000714001c0c0390740c201c02e80c40f816951000103240d1030140900a60070315890b015141e1610358004c11007101c1c4c0c001d0f000700c80d6500015030104600c1c405d4180e0b24030030180000100e50350ba00e0030039a91040510244a860f0603080710314502c4c00320b40a40110384498a42d28105108029104003160 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 157045638 1250 157044388 157044413
    0xc130e0c04300b0a0b0108160522090507080f01182d060609120809010c0c0812042103140f04030c0b0304021002030c0616030f050a0c020f0d05030f04 66
    0x5a010703100b862158140540c081c1c18a101e001d409400704200081c0b0401500d4039201111100c0c403100340c3d09420011079204a0242040365003844403450040b095a1110759103600b40d80041251903070354410044115440030900d41c000c40c1d0007403101815410070213044000018160543c0c40389864010440071a44841d02d00080700c00e0754000d6030488005000800058142031098a0003c0c08102012510968101e0721001e907607401704100b0b14050742900192043c0d80c12010035151000305c10b400045d031440500241c001071580281d20740d500c03810282d14022603094400440c0b05452040d0011001130340040303403e10401d6402442c01d884d29685041d2043e1841640c0001b8015615540001034800111000c0c50040d4404c4a54500075407181000301c0e0b0f6400f80480c1600164890303400b207500c29a243c124940c04083c18500410032083c06c030300c540162107055555000542e0360b01550303800590f0620161280c0c00100c800b40c075912058910041480c0405482200112846000f180400241d0923540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 157046888 1250 157045638 157045709
    0x1b23040b0c0a060507050f09040b0103060506130812030405061f050402070c0f06080c070303050406110a110f011b08060d050a1217070504090504050a05060c130e0c04 73
    0x9503a0030809540c01d450b9400c1210840b52039041c007010400e09801241542c49443e101c000c001d051555100c1008041d01040142d40e040c140e6440020408c1d1312400010100c2c0400e18040c1031002d4988400b007480c0c518803440f600c2101c0400d10601c4000b400c04150507803c9104240c0788440d071026a41c0030305d1401c81c542c3c04150310600c0000c1d44c0c01045084e6007408105c0b13100c10b011052080d5600400d555500b02221403504910081210000082c000c3c2c1c0980e4005020301000600e108180d02104940e0740240e4401d40401d50422410360116420000c6042039407010340244841003101a44402d002e02c0f2000c1801848141400248503445061000d94007070b40000c21030384690090b00b03002c0c0c0d4440c064850700c0f0010f02100d841310840c001042d1304c58090500b0f55a594a0246050811402082c001e0000c5420f401500c0d00c2e500801d070300300075181c000c014140c0604e60b03800002040b20403280e41688a040d03c42000e4081043c2c1c2d400500c1954121140300c1c0b46403008408409806002100e0030546 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 157048138 1250 157046888 157046909
    0x1060e0c2a010c020c04090309030308100e0414010513030f0309020303071a060901090603080406120e0708010c020f0a0b06090c07080d0b10030b030c1504031e0201031b2304 76
    0xc004581500303c26001c222a4090310104102601070100b5511700d903d000c1d003c501481030400000e07225002083d8003d000b1041418460b48400c546100303c00f040e5800e13a0382244a5079103170201402842030603000001f10003041074090665a01601d070004003041c54040c1940c50001b0029901c0a0044901003584840b000103a81c245640014807100c054860a004800701000401d604007035108a01c150780d0172251a6091511700300086603407450782d4000300c0d1310725181c209281c150071b0708016030700150034041e001260925079000b00900d0488003110003407480c1d010740e00da040803031b010f0a80650010000d649540040e9142d41c85100e01d442200c0004101e801c00103a24020020907a02140d40b4180c201c402403042e2484203021010f0303d4160742c801c0d5040e04080003610007440c0400da4818902d007401c8403a070400d980c80d11545c00e80c44112880c0c2807501c68685c161000c641e454850350f88400ba003c540f484000d882640c00800c050181c907046100c0d0040ca8084a43313804400d01500c00820380000d9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 157049388 1250 157048138 157048207
    0x3120a0203010e090a05120a110a060603020f1804021002010e0303070201051b0a05030601030f060503010908030105090a0203010b0d05130209010308070221031c14010e15010201060e0c 81
    0x20240025402403003030306081c40c8507501095140e48040f0780108625044001000301d5a0005c112000740d900020961090140480300410400028000744907a1801800000f4131289540140412160320070441c91140701805420140c0035074903218950050340503170f500124150b40c9842030b80144008140c00c18544030100030008560703415004988580503241d84030a245001c002020103c2c05004085004158244005006940b0a80c44402d40e055150408201d9030380d988082800c40710b01e10005c0d1102900040103110b41c0c00e0500314190801d01c03030b0310114078561500d10f05107110b00071040142c210710349840c041242d803124a00c00d0f02a09400078104409075035a490014216404148202d00500000c3c40301408035802200c1c01e220280d440010303604d01088281ca80070401081c0f102d080c00b8907954103a040040c203844403000d02820000603800358600307101892945892a07803502d203045a0410000344614020040d10942015480704025202d400d291f01480b00054461807035100f10410b0341 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 157050638 1250 157049388 157049401
    0x102130807060f0e4c110a030206011203050403060606051809010807060e03122b060807031e05011b0f0305011a1b070f0914150609030312 61
    0x600300040312482c1c2c807480c00c00a1109001d4800440408200b0b500052882d4840701c04000c54a40d0041c5e06492440c0c0400326505598a40f0007211884040c0501a000c0c92950351541c4c02c64803005440d4a008010f1000c4042c070750b4000d5440b40140100701461070f58201e40010103010300d041e5006180c4c4100107110050b01c072000100207401c164106461a54074070040d00d01d5081c2281c460f810f803510200a040440c1c02e02e1001e50342458072400007500b43c480c170001c0c3d00d46030070704e8005000647d0350305802c0301c0070104403814800c03070440718600385250034039041041201480010304402127a6000416958038200e024180c60002c03041c48000d86503500380035120003001004903020728540000e0311422221140c031041281151000d006145555004104002984600b4406045d20640c000c11f01f61183c00d40b108030038140035560780f000500000124090224031103502035a072000ca00e0104454191802816070204641000d80160140c0310002d41040e0702c3d1003e00860303420350500164621390741040b8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 157051888 1250 157050638 157050643
    0x6020705030d05130507031211010905010501140909030415091206050619030b0c13031a01060906082502070f0605090a050303070f080d060302090901091a01180e01021308 75
    0x840d03861050b1494040015415041c0d0804900740c00e42140c01021450300350340d079080d8841041720b07140d405c4c040d020040315140d8034240144601c0900c11000802c255140c560118030746007100c0c04035840340701002c0c204100c0700000800d4a003102d00000014070340e034510305015a8065085e400400c0062101c00c400420300400b504000d020f010144c689288440c00c00c5034900c480310480c000100012040c5001c40c16102c5848050007450b141c0350f48813400c060303803035a43d1003004040045060081d076001d8010071086800020a00040c0030b41e0030b04659510345401704203010010313901c2a0300b120040d2050883c202e48204101c01c0070700b150310b06407400310351030b0000508107400c1320503041d00c10b030111b81001c03405003404015141007503030182c10007032628800c0d80d07200d4803600005101034680b56903038000005a0307100c1038030714000c65a01000003072020701800c20041e00c82419290100380045000108420b41c58452a081081d07041c40000412440e40c540b1207001e031184c0010145100101d81c404200c48001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 157053138 1250 157051888 157051897
    0x1050d090807080a2c030d200718180f02090a0f05092a01020d0809030c010207080a11150a2409020918010308040e06010509040e0f0c0f10030b0307030602070503 71
    0x2d0b0180003d10760b19180801c0d22141d040c00058240d00944446801940105841202c0c806805840300156945218481ca07010243d48800d960094071500c4100084052080745982f98500c02801102821510b540c0300481c02c0c2c01c40240600c0c0d10308001001c402407030b4000d03a182d04140b07a050200342000f0f4541a560401542d0710300d0843c040e1141c02c0000600c6500d0200c0c1080181c020701051102808184c40c404001026501c1502007001807090301c100030b100400005204120781e50300c4900c130070750003421101910152100d81d0320198110581000012031190310804c1c2d1080401d405074035440d40c0e4038190613000c10440d00d40c00c540d00424845246e80242912103810796403c0c0355612824021814061300b844040c2c101c500410052182c2402c6031200d50740204113040941c0782807071400c0482c086a844510341c071606c2d0005c0b002d000c40d1000500240300c0344002150040403005141001664110640c0ca0750005c0c180ea40b002ca00305c1d52070901c100401540c00c110215102e00c47c03401c0540c1c41e07900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 157054388 1250 157053138 157053167
    0x1030e07060801080c01050310091104030602040312030f020c0c09220507050103231501050c0d09030b011403060a09050c0d06050f070305010321121e0f020901050d090807080a 77
    0x10340c05c00c0745529485203003900d10070a121403007090305030328010b608002020b800811126060b401c020100c04a9110b000401c000e45c032a10490b00000b04101d001002c55941d5000d41300c041d40100400d103143c0c60001843c140040049445d007085407074002a80e21030b095549a0394a03040191000501400004035005085a40c20703202445044c05500d19042040c0448515018214510002c103841400440c0d4400e41d940c010b06110f032915220155240c07600d0303803041c1303076000148200e802401040f2410ba0070700c2c014120424034000784400000040c0c0c03105002095025616030340c1c540c601c2800350400000b032049402610aca2028043d40c14400c0c003404080f155500302d400910003103403400c1c0c4a4800c090490f070300060740005030350740e10040361091522500004100700c07074020b011a0102c0381e4880e1140c489a1181040c0815001280b09015a00020189210b0600c140481c0361640d8000c0125544004082c000081120303d520b08604140161900a00340b1100405c09145640d00030451000c010b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 157055638 1250 157054388 157054393
    0x2100903021005062d0f0a060c0803101a0903010f02090f0112060b0415020c09060906010f09150c0203120f070f0507030803040b090f0c01052704090b040b070503060d0b0601030e0706080108 83
    0x3402c6ca800c0c40070000c5d180c8502d20004490031001070114450030065604940c19540313220130b41d83d840004803119104202000301d0f120001401c18003e2409200e00c0708a03183e080750a5090007401000035a8000540c0726040c103002030521408034406140d401070003d0010710030101c5c1c0380c54888461000a0413001c40c52000351090318603281c42890721921582c440d41e001400101e4035038038180116440000c041c0035070b0600c04100b40200b0340311001a1916003581459075440440e410b140101460140108030710318100400b0404000e40c0c090b45411240343c00e400802c194481c0f21079181080c80c0854651010740034107008000d200c01c214003c00a14050032038035088601e0036400b1804152074401c0100c52074080340003001105071040b800b00c03d5401129110b0070404007a4038050206007031701c0070034030300f203e9100d2140200410007000d03109041d0400c003e071412a003540b5061001c02c0440801c1d0b8400b4210000540010302160301c41e4100f004c0c0c000505060b6078840ba40d0302c20107040c10780c00703020300a0f050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 157056888 1250 157055638 157055659
    0x509010f0323060a090303180312060911040303030207020102030d05011d152206050310050f011e090f0b0402070b010602070803090d1b050607110102100903021005062d 74
    0x1010300c0b4480000c02200c92000d0001501c542c500304000f802802000c600345503c40c00b048030368103244440174464034065250281350082c00948402141c85070303040f039810b44e860100c01c00c0a0b41c40b418203450079241c0c5414010394910550005031f00d180114100383e000036007080000300716072000fa1507408800140c5030100c0d106403114408a100c0104400c5e10580103241c0b580c2181c1c4000c80615801d5505000302d4000600d25214000309040c80e05002815880350784400a201540084040503401009094000500400000310403a401a00703440758000454580000704c0510fa19603000048540c8000c0c000c66952143c1d03c0d014901c0f1f40300748a40c40241c040c031040003030340c2c0c1000300881e180c44000070503c0c1d6401200e070750b51b00c44000080c2e02400c919042888081556111440100328941c0240d595900004004c030009142c004a00f0601d40c0240c203002180001a40005840341c030340c1c0210340080780550743e000206140d050310039641c400c0d40011010400e82d4407603403e4100d96014040c2c6060180 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 157058138 1250 157056888 157056923
    0x50103060b03060d14250603060b03010b07170a020a05060603010216060e011d07140102030a1e030b03070902040f0b0301050907110309090406050906060315070e01090509010f03 78
    0x480d4035911408030034100030000180c2c145418000c16201c0c511580c07041c105803220114841c07924a00c4280b070750540301c0504921100d01100c11074070008146520301800322a0038074401d0440f900040c441d90041c1c0302c001c540e45003045159882080c0781031440c03081c107403a4000310030001d544a0048800341c0e550700400d070200d5180c2c1018000c5404c04211260000c00e0503e0075500e0000511000400144556a83c1401c00c0800080400d1100e15800100106000303410001c01c24004141c000b405030642d4801c00c40300013001c2d080440d8410b000701e81205c400220a50300c1080c1c001c0e00a286145915001c1c542d0041031500c0254050400d555818041040442d11182c0c0c00210f0702c000c0c083c031a4404e4030b0900184050380f01d40785403e00c46e05a00241c0c0c1c20a1011000304444003400e44089414a49540802254081c02c005466004504800502c400100304a00d80711000c0d001c3d01d80c00c100f00d081101c02d4107036401020000001c05000d0311015042da901c0c600030320448102e01045a403041125030301c0c5003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 157059388 1250 157058138 157058141
    0x9030210030e071a0c060a0e1c02120c0a0f1202012708031b042301030b132403062c120d1e0507020105100e06090702160602030c07050103 61
    0x1a045070b4004000190824145060180000d00384a1a290040060000e5402c0c01e01250f80240c91410000c65821843c509040c2849481040c40004004004030102c449a0000d805000d9180d01d4000d5656620180101c0d400d2050300e0700054496030b20b01808030204203403a81c821225038041c0d0b0003006054001c0c2e080c00d284115032000d4900a1040d91002c00100301100001c0d070300710b8800c92150041e40301c1901006555003050f480a410004a0a403408042c0709000c4001c2034a1070074039040002010450024043d4003402110040441d1348482110f1541c040700204403425001c511f020800c0c990b02d14010000d400440c0459171a9100c002028200284512441f510380820401501c840d1540001c0707526250046402e00c941140c480e001da03c520a050020684010711b80e0f04040745500c0c01c1407020782507840280c120021212082030811840449031a07503604054115502020b6854a030422498501010325440780054140d800042d255000401419005803110a40d07074001c0d9207500550 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 157060638 1250 157059388 157059401
    0x30b060d05150f01170a021005040e090d020105010603020405090a0b01030204080a140d0203030c0403031b0c03060207030206010e01080703081b0706020a0b1003030f030f0e03030c0904051015080411030d0903021003 94
    0x26582c6c0c000d060640c0140b81001da42c403071800103450054103190b5200340c400030aa4042d1030304d0000760440e0264101040e420300402d40501b40606080d40341a29090114041c010000c040c02880d40d551070809044c0d1303100390120b400400c0c0340000c032041441c0c20304180340000c66010603032800e48601d80410f00c0701030010003640e10400c032403240f842c02c16103144c50070b99011022a801d52100a461401c140c000342d02402844003a5014130700c0140c64400ca40382c080d18011042e004800d0046522004100d041000148903055a9200c5821500d54101100207040018031415800c110b0185100c040350140c0c2c00140100b00a0154220303440c90348500b400a010b05d070071070001074000340840813880100e900a40010152582c042000122052000201d03401d580081d41d0418601c0070002e0448414034090103016007007207070080890620b07807401681441c01040d54114005110f0014001820f0001c011803502000744090140d8002001d5070400400c8007000e400f04030f01c10080d80900c2032030940300b4822030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 157061888 1250 157060638 157060679
    0x306191406010f110708030307080405010b0a230109090e0102091305150405070c0204052a040506030a09080705030c0d12090c050f0a0801020c07080c060c07030b060d05150f01 77
    0x40c20703d0081e803404698040900802c41101d201e0260300059400e010401180b04210701d58401c00c6c00d09143c034103903080d1003102d0b420600c0b9018000c01803141d4045051942001c0c401503c0e603001170040c40005a40c0c1e22400d51110405900d4035500301c07100d000640007000300a600b15071612444040c00c5010003112402d946041c0c0301141d600d982034060405500264014200d070400c0160750641d03a00090640c0e400700c84030240340480b01080301c0d14807003085802204c0e8004904260403d03040c00c01060f0a07000040212450703c0d20f808000d4180162030040b0751410b0342040c03d87c2d60b64101d0080781e81da1000880d0100000a0032910001600c0f145407040c11450303944222410340907450a0100f0040789500d552959001451060001d40e9050910040c42c1c40281c81024281ea60b1900c0c042900302400f00000c2030068408120280600d0408600d03501503030b41c0a500340030f05440b80000304041d01c890003401041d5106030080c44000000e0007524603c5020403a002020b41da0702c41241ea00750182d070782040e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 157063138 1250 157061888 157061897
    0x1240e0f04030e0907030f020a02100501080304061707050c0d1d0a080a030e04020d18020306061512130c03030203070b090f0a08160b0f010f0f0b0702061602030619140601 75
    0xf01c0b65245030410080380c00075646e2a01264100808030950126403005100c01c025070711181c0b0407003214400b4000c0a0040c46031901550501d880d2010260200f03245c0441220343c00c26100000e80d0309170044054541d1840b18404981e82c01c1002040505290122500d002b8850015011003075245000d5441c081640c5007000500100c0c1d0450b60284c44444044811907809a000e004000784000136128005080c5808032891105003254018036081840180c9014010740e45e8801482209009000b02c414402e90094041750550307490b82c0107245803250500007441030010031000018903034008040d01c101c3c3d0140740f51510b29260448225511441c0300800701c400c2c2c10491101c03010078100d9016101950040d141c26010008507070b03071480d01a8044699a1410f00340e14010301281c40e00d02da16a0241004000c021465030a0202c158000e01400030002c0c0b064a0018266506c0d00901400d0110b0070f40c0a000c03210a070030440c864004401d0721014840c0801e2501c88001000c10980030214000d84060f1503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 157064388 1250 157063138 157063157
    0x6100501050d090f140a02010905030303060d021207051e0102060a140a091e05010c020d0201090c1a0d2c03182803080a030b090f1801240e0f0403 64
    0x1100090403000f038058554021120000c404a01d02c00040515818100050140c2c0721084c400507000010541195000c1d40c020700400240e0384600c40c0502c00180c04950b0100d1074100c143e02d5a1510140d17070001c0b5002158401c00111035070f08100c0d03070103944609800351307030741542e8000b00481102c07050080350030081c6054012404844440e40403424460050104201c5503660034040c0c0907010001d041151140e55480746002c3d0158148081c2c003154813148024049400d8035102c9110030001401440318281c02c0b40000303d4440007420844110a000010500400c0b10140c43c0c20461694030115510007161000e0072950800c000c070856210300806002e010710318450005100b2140128201c1720f407141200b11021408441b03250380c0000031445002e031207554844c180001002d40c0c0d213180c5040d0065030041c046c0904615039a89542d4402a0200349103205150342503050301500002c0b4511452444481403550305981d50800c00c829940482440907041d100d1503a00d044403a000c550141c009540e40c0c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 157065638 1250 157064388 157064407
    0x301030c0b0c100c050c01021804180f0206090f1c02010e04060e15060c071215050f070f020304120308010824190908030a140703060605070816050f0607020610050105 73
    0x80c070411084c00303d8603210f4109070025940e14220b9020788101d04807040c014080c90042d28181c021030554540010351003c1320009a030b108801740302d40003402480b6603408a0340340c40680f40c0340366100410400070422441404885100c4807a00072041080e4001018140701c3ca1071802c080c0a0001224a400c090072500d545034141c0c3c0a84000728224154408810008501138030405c200c010084c00381c0704084a0011502d15080e15141c1030991000c403540c0c10001001007011750702e00a43c1e030005d0541014580d42e40c59605c00c03800c6100e55005440000701407440744080c5948900139a0513a000c01088403140400030049441580140015602d41c682002c0010300300d241c1038841440c518012030001c03803038480c01e9903104050b800881c1d000c0d450596954406088455000e500c5802c0a0241820840c0078140700009003144034945000e4440b903000102c0b0712007082002c0751042d65980007416900704502c1e50701010340740c1e04103440041c0103100f2130010504040411f101c0900b01cbd20142c40755403038090642c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 157066888 1250 157065638 157065641
    0xc0f1706060d06030c080105010909080702060a030e0106060207031106042108040f0e091b010e15130308031f05090604051806090705010906090320030a12050301030c0b0c10 76
    0x10840c980140007800060900e0001d4020b08010b0340c0f18141c41080385043c081d1290841d281688204000317801c002ca040041031720b403000c0714403d076015901680da62244174410303006440c040e58403038400e61802c400010025400b141d410141c0e0710504d00c820030100c6c00420468903000c1d501a0116002810603840388904030300f010400c0311441441901d04040d640c3c8042c0c40e5800751684031410500240c000c1014020040c080c28103171941c51440a4003540d60781e03000030490040030000134025500b03c00d02d00c203040c88200c155084c0c1d454550b05a030241d516490105c14030b0700199100117592046000544da800640f1031041e080c0c03040a0050f507000e42d651000c0001800c805041880e07030340042d047c00c142e0310384244805882000100e00a1031021f190400052007504554403610400803800c100b4400150b15005001080d00750900801002c8903010001e0b09020f503084000713029055440020710300581000c09941200d0080c41007c40959458200740018030a101441e40d842e04120300102482455 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 157068138 1250 157066888 157066891
    0x212061f05090a020c100e060103120309030906180b0316030e06090a030c03030f05040c05090a060506030a020a02010e07060806040b09190924020c01050106090b0f070503091509040c0f17 82
    0x40c0011a506c50301003000c40d00884841040c1d82c1801c1d00501d0041c8140702c10982c0c03250100da0325240810002d60140c50090144600380145000c0101c2400840c41000318011440c000d00f80c81001c0c0c3d6941d0501504413581142903000e004082400c107101c090b0a420040340c55441031341184003a0070a002e05640c00c6903140107130b080840c01c0c184c1c3c50106440206492045901c564071420301000d07413a003000c040046000e030041c007001c4042d09207441484181c50b103006594212029410150312044188803d0740034040405050031548a034140c0090095400040203005030700650b41033100b048101c4c2441000318045910207020303042c440308049002c42c03540c442e85500d8007803021070b160252620504000106c034417411111681c1c000c10f03090315001c006e100391801002107080041c003462520161120b64008c0e013a8101890a000c2841005d00200b80225500e0324001824020030f00020310000046030004002c184c0958078240c00d1071200760007071004108500141d1110901001c804024a100050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 157069388 1250 157068138 157068157
    0xa0609030f060b040f020a030902030622030503040503040b1903060902040303200f010f0209040b040b030c06030403031b050d0f05010e0c0f070203120306090c040b030a0b0103090212061f05090a02 86
    0x1d81d142d404445c000c891016080e12480d0b5a008214610107004052070038401a212609204196002031044000c88105074071990345420569140d41c4d5608129003180150f41c1f00d01808000080c040800204001104800c030311141c5041002a4441e081c02040b4001c50000601256281c030480801c071483d0810b8034410780b00c2408807065191190790340b41c01e40c0c40c840d04001005030080340701ca095207054081c0c1601c202d01910f0411080c011f5100290360b41c901e01811500500c0c001020509241c0300390040072001d180c4a12074410302100702c40090403a840210030002d541d142084500c120052401035504a94040d5a600360f581c40e0034000300001c1c1c2c0801694280086c0811a07440161820302401d142c240145000da41c5034501a810b010307060078001c1203145508420070046c4902d04807901580c1c3c22941902d00010b038244d000006a009000c89000130354031000040500300c079140d0003e80f151184520080f6482c01c000441e001581d070404500400e40e1100841c00001d41c0c1210300d80c0900075151 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 157070638 1250 157069388 157069391
    0x1090608060f280b0a06081519090c050d050106171e160203040504060b0d061a0d0914161e12080309030417070e011a030a0506011103040806060a0609030f060b04 71
    0x30303000084400d4807a902c0080401c01c510300700010348c80041c0c0d03641c2411340180c603644e4896510843c034a180b440c00b0302941a074a0780d5900b8803102d5030b00ca58280c034490144600304028650b11588050003074010014001c0c0d903540500002001044126280c01c1148403a04116140d5100c02c030b03802d403c903070200310700b0400c501c82440005078954440c000d01000f8000c000e1070541c0c07020340b030364034400b980c1107a0004140c9000800081070005c0b0134008030b540007081c2e2000000c0c203184918258091a42034110249940300d80c042c3c07035882110380340f0040c048425611500b0152007524408c031a52403c544500c0b03854810000d611030209042200941d8082e02c036005032071070300c0e032a5a00802a207116126140b4641e10582d8203200c00d425001400c1d014185240908441c50714029181804c1d10004001c001080d84406c0821a164028009248180d0b03001007a05d842c1e68943c4546941c5020031030711203200300c40e50400016001d000358071485c1541e8000800e01ca103884030f0b489030800f4050020301141c105 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 157071888 1250 157070638 157070651
    0xe1b0406170a110f04031202060603030d09050c0a0801051008060702031e0f07050d11191b03140c03011505011403090309060409050403170c0a1b05030301090608060f28 74
    0x800f8014014040310f4031010110751143d040d030820800e00d600100c1043d040d94000014061603507000425280d14101c06000461150f00618010382032603c640300d4070350007c4a25001140c02c90301908010b00ca0001080e41030035656a1711103040e6039010540d0784030090b801c10844680003280403090070800e00b6034a074070b041c50b1580100061845074040c107802e4038503420009041c03843c0c0d540300c11030982c019041e50003800310000c0d980451340b0311840c11000601c0203032600403009503145074500c10340041d40c0040c0307004120700381c40118a0701c9d510801c5c00e0b5403195180c000300310030700b0740a41d4841c1d0a42d0010780d1010002c12003d60420115400a405070b001480103220050300350381c800000708050055220041243c0c01d0a241c06001c1821820b456001c908011303080006030036009054075401449403030f00581804686920b40000c00b2000c8001c4c0c0b0350700001001042280c1182c001c40d085408510450340555208c030a1560f0812040e01c1d406407440c00a040b080308800c416030842c8012001c0b100c00500e8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 157073138 1250 157071888 157071911
    0x9021803010c1d180411031c05030610020f010906050603010c0309050c0f01090f0803120108030a1e0314090a050d050a05180f0405160306060201060b030105040c0504030209010e1b0406170a 83
    0xf842114201c079542c0442c0040074103810184480e601242910b0030301e24503231510f40f1010708640002403401d80100030094008800500c05c0040e00041417800c0000c005e40e41c01400d01402425040301e64501039030904c0c41580b00c4a1181c42401d1003030340c104d80640881e4808004201c690703902080e05c64104083c140e00807440c95031890842000701070746001142da5015050807002506d5059000a046410038051400c0581d048001c90000c0c01d4546012034081a4000d0150300034400703000a0240303801c0c0e070010440c841000007100030240c0d005504480078400a1803040303030184a21584000055401e00c42d00328200c10110451000b100010301007004140208040b90481c1c02c03c03202108401d030312410b480b00c0d1030381501c1264040d041a100174071000c1e00b84003460001c2d100611130113001c7d0340d0300d9400e1a501441a010784000d147e00800c000d12a5a48245015020380c1c161500c5541e6940c074880304605031362810407901110b54a4031098005004c0703502d04035801500600c80c4407071540311241e04c0310 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 157074388 1250 157073138 157073179
    0xd02010516060615052203050c150409021303050f21090301110a03050411240c0a0c0803030906060d0b0112050a060e0d0e0402031b030a0605060409021803010c1d 71
    0x8880c44c43c0e03511030310f403244a0407001c0782c074083c005445481090104140003151004c5418054402e003900c40c580d2154604005d81090320442d40f1214060344045195100c15204101c01000c490050003142c0c00c950202e40d00a07100e80794040100c00a500294010045a8241010b00080000100006110407051406022560003d81c0d03541c0001e0360327501003004110328039013805d40c10001903a90b1018500b00440c60a000003025107001c1c456000801c43c120450410008400324552140c681d241d000d42e20715031030f541ca030810354200d440350213160000340442c2098005900b01d9900514000c4c20340c0d2030006410341a144c0300c0c00584e43c6020366900d0750046100b50056a4030004a107004015105c9489402422010406c040510550042062003048800b040c41c1c4501d140300c903281d40c0d6482c1c0310381030480010922030b0b000c0e541142c00810700242d11980d548c09003908200c00428181d508032400105803c03a110601110085103401c10445030301c1041003407005194401034207200391703008100034004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 157075638 1250 157074388 157074419
    0xf13030c02040c0c021819020c0f030f040e0106080c0703050702030102071703150f10030b010c060c120501050105120f07090906121110020a08030a0204030813140d020105160606 78
    0x4140504443c20071803c01010320b510b17001451074295407500b070882c007c207130050909030f00e007105603004075070044906018400d0618400314401180d41c0c629254208240300d80280c451071304c5400510000040c654001c5122510481505c1c1c042d80c6040090744d000e48954000341020798066600384203010026203510403024405107040b11140e16450480806000c020405c0712003805800400f6400405031030340b00850317043d00c0d4641000b181960320407004803410010300c0c03806000d840c24860b25421058000b00e454044078914a020b001580c0c8410040d5094030501940e40c2d641000400083e4500880501890300f00d0090300c0d0501ea030030b43e5602d8250540d600d9412a10720034a80100800422224070b01d000d002d0603007034500c219034134521440603455820010b4003400c207080000c001020200280d0440d00a940c0c010580c0d40c89441040d040480a10b00e0f0180072001e014025217004645407840a048100e0b905942e020f151200500d4078500e00907110b90104c8210361145030208440c002e81312100d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 157076888 1250 157075638 157075661
    0xc020621040c090e030f19050c03030f01030c060e030a0b0601031104031407050d021f020316060b010809030f0921010c0f090e010608130c0906120303060902030f13030c0204 76
    0x2038082418003000100725469003584030740329801001101b0055114209030740e95150000d42d8414200c0b107208007030f0b0b15880f8282c0d00181e20f00002081240f00150788010905a0b1f004028803d0a9a29124191a00c110a030107843e89a0310001301400082c221510b110341c050018980800e8600003400c18440c1f9030020740040b40c0fa03901c5440d509800d000304104500080070100c6061004080039004941d01d0710110036051010060280000c400a008000302d502103200c0c07402003c181315440c18044d000305030600e0308a00290b000300220300e030840c0c004141c0303000100c41c0d600e1f06d1400340300310200003009040c60210044500307450841d0307103000028454440940020b488100c0c4d0f550484000600c1e14140760081041c0455860050142541c03050540e03500c0099402400281210390900f60010740c1d1951040700207a05002c2c001c00e00b074014650080c0d4162003910b041c000c6a80700c2d2035800603408112800041015014005011000d091074450841e5020741005020458a5004101564802d2305807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 157078138 1250 157076888 157076903
    0x6030c09010f060e0f010c03050c0c060d0c030b0d02011209021503090c0109292b0606110304030b16180b0301050a050d0309030305030c090306041202011b0c02062104 73
    0x1001803d4208003044c9200c00200c0f0040a03240203a030000e8a081c07040c200140c100b201c041810506600304004004003508010440d0761208002d4080764054840c504807080000c0c24901196114145003110020035a4161159400c184e83d620542005099808081c1c1e4008240300c4207180e040c00700340080d8000c416800140c40c1901e0160005401303043e207540001400d503c00ba042c40c40d03010800361007029089400b8900c2e41e8590f4441601d544405284c2080d810601d0060001d89030f00c01c03c1d1340480d0441c0c01a44030701d0800b20311251899220700481c800541840e214030000b420001c1d41004144200a09040049034140900c407030f055108010b40102500140002c014081c610f0840c101e03100411040360764845031040c2c0c2c0e40c01003110713405220040c20b1040c007001041d2800e0180b000d80740b0000001c0c0c116013140c034144c10441450011a0f8a0030059480d1200d1440c000080a070007081e0f04005440e500500b420507801c0c00400d600018900030620100034220036195560304c003050069006115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 157079388 1250 157078138 157078169
    0x31b030f0a0c05040f0b0d0605040c0e0f010e061801180e06090a050903180111120d050603030c070e0603100c020c0102060f01050a03020d050307082208070506070b06030c0901 77
    0x1070300c1d421208140181c0080c0b0034240410001c05404141c580d00303980a9032030301d50300c46100c584000e001e407850b5009254010301308000241d000d50301201440e04014110703000840d20410100545219091404880d0021010021220ad091625007483d070b04460614198100e00601d1800250b10400350704004c0828081106202d140c0c80c25601c429044414028100f002d0308001c2c0c000e55580c400c0b008044e203e8001c1940d118016801a0711070400a0b020310b054841154aa1070305040c50340c4203402d034040c41490500490b0b82820000103443c0d28000c0c210003172184600b003108a1b03040c003200900e45907040c80384182d40c1d212551030f40180b143c82c0b1196002000c0c0149010006402c201d0000c00010600c1540390040100e0703910150500202c0e6015224650243c8250904038103621175003a0203481d0040c0000d03901a0300240b4030b9070000d0002074108a184c066100e1007240c0d201e50541c81230340d60091090018030082501c10854941107030303005007241c008805580100d0510102680010360800a008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 157080638 1250 157079388 157079401
    0x70201030b1c0f0302010515330309030408010509010905120d06123e010c0201030603060e0c15031b0c1501080309010f2a0512070609031101050615031b030f 69
    0x7455086400da0071980b03002806900030800c8c8402c090710031aa030681d418944a600c0040c0e07427106c00d05c9903441030001c0e070303d280010b04255264440d1081c1c0c007456281900142c0c4051062088002295218020304801509065045c030380e60410a03038001e51995884001402540c128640f2105a1143c1440d03034003004115036907412031100380c11081120449603030b280c1f021100380c03d501c451001d01342403c0592103c50b0004a0040100341c000400f25417500c811498801800130395a00003140458080000c0e400281070703100707a03010a642400d0300d142107405134001701e40d0a4010703001041389407049070341c848002c240d02a9100001c0c1d00585040c0c000082101031755904c5103250030b84111508000c0844031800720f071a400031110700d407031883c2d82202840042c1000700130700c0080c2e08a00503c4d240380d01c80140c3d0400b00020102034404a021505c02a10a002803906000d1f0603c03994000f4903445220010210380c0c2a650701c000c0507443c0f942401f041010034681d501002e1805003900100d070703201928042 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 157081888 1250 157080638 157080641
    0x3071e0914090f0c030a150e1005010507031d01031b0305010e060618150909010b040617010503061803091302070506090307020918160b0a03050601030c0203070201030b1c0f030201 79
    0x480345001d429020100480f518034002c1980c0c11130460910780d0fa0302e564201c0c00318010711898028030044901c85600151802c41c0d44030a41c000c0324042940320b0b15958900054a0500c1200300080116480c1c45000300008407070303564044140300604010401c2c14071260703c140c000e03d000c9030110200303964a0051000f00c0540c1c0c2202d078082c1007501d11600c1c01c101600c030000c0a11a44020910070644203100d00b10103007120342a2201c510340603000d040e0558503580d004050703400901603400080d180c21240c1c4001034003c0714450403510b01a02501054031080020290113080c107002000d20b100410294810f42c03a0408142c3c00d20400c07010040e12800720b480d200d4100003000c0d01015269005115050259544803456038200c1d8001803286003031550f02e402503040c041840304118117212546400151001c48a0060860a0003a83c007040907582d590019012106040ca0400050f8000c0c081c000055019522801f036822004040c41c82400d110740241040d5211100c1c1201c1d400c1000c101c440405409 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 157083138 1250 157081888 157081919
    0x30106050c010b030f030f090d0813090b0a03031403070215101a030601020309012102030a230106080606220b0a020d020c0108040b04020f03060405010b1203040b04060503071e09 78
    0x700c015000c20000c01755460340d01c0c0034404150901803400079150607a95665840c810006070301c0090300780c403a032011901c0000403640b44a58050141003c0c06142c1c03a103000341e0200c082c1d0b0740c19119a10030060805070809503803c010003110551040c440007688000340c50740440d200e0038070000c180304150704214800001d0b49805203003228031682842802026a00841503d040d09801e2a0103d401c80000c0c21114040700d503205111040b0744000b041c02124905034018070f0a28030a00701d0b4080403800342c18842c04d080380900c10000010ae00e5404aa420b00c3d1050040644044142400c03860400707540b500403200c082ca40c010b401014002a5407101d47c0e405106111600e601d50002e0071514810500280c1000c1c2c0050000340a084c042000508541d0b400040a40180c070203800c588103894a031034400d00a14088500910a0351114030341002440700008540a8030201802035080030b15000e002d07161504050200010b100c0340d8420a0b29007220140e00781c110300c480340e656201361031901042484440a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 157084388 1250 157083138 157083161
    0x70203161218080715020a0b010e1803090a030b09010f061202120706050301090b06040308030a0b030f0f0a060f1d0304030b01090b030c130b0d0813060c0c061d06030106050c01 77
    0xb60000030080c100001c00c281080b60382e035640940203125514800ca090012861300180340c00a00000410350100e490401880f80b04807160816026498001641d92801024015503001e054018140300288000300f403150081d05440000c2419041071003081c2c243c035815000041c1e80500c41c01d1006c00d500c3c0c2140d0315083c0041c1080506411420035000519034401401500c0d4850b40b03507024142d86c0c2d02d81c00304036401107030402c0d41d040d1241020ba440c040540120504036100f845940c10f100258200030908401e140b0182e00100340e142e0311b076a41c002c080c01e9440d0603640380716540c040d010792440c5c6260404150009010181da500c50071481e20300005401a00401c403101e1400b00c0d0988580c03030000315020440070455401e40349001505034032010300000b01d02c203500452070702c103d40c0821040c05c020b4000003a04110002d0101e841d8501155811125040a4142c0c0c00c4c00000308801030146250071400320f08000070700c400012550200301e4a0b0700a92124000a0307000a40440c411002e10030f8554508 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 157085638 1250 157084388 157084427
    0x40c050306090f040203071a0901030b01020c0a090902040209031905010c08040c0e100504060b09090f040c05060d1b080402040b0906091b0c01060305010c1202130308030702031612 79
    0x1401d60201e068084000c0028000c030381e00e440841c00307540c1c0820110000740411030485014451b09058040c29070840c82106001c2414480952010740c00803030b1421181038027504000e4414541241130b00a400391140030303a00f155082020102c151030a00c400c603100454141c1d11810402c072403421030b003155080302c500420040f005090000060f42c400112045030780045100c401d50b00c850707180640e004c0841d88100d5000780341010014540341400058444810100c8401c0c0250388d070f52044904c040000c460052000d0039515003070103585400b01c05441900b880c50710000c1d25a0740b841070701b04130491001c007810204024000300301c1141b41c20b0090795240c820540d151703001c60800001091403400047c0c205421244024040a141d0820a003610f2005951100a000180d92818002e000708221603401c0000340240c42201810080ca0007164880c4c4002c403040c2c882c0c185141c0b1400d50b650000f50400085020802c25140003000c1d8030742c2d0040b0b450046014030180d1001c02d00250643c4000750314500000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 157086888 1250 157085638 157085641
    0x20406020a0305210108060a1d033106120b03030732120a0207060518040207081b0106050a0618050d1a070503091e06040215040909050606040c0503 65
    0x5550120711140c0855060501c280c03140e4418580c0c004000d640004401d5690500c80001a42000090164000c103146081080b410410b040202a60221090101582e920401240307100d4901c685014244860605450805200740d8140c1e005420481e844038000413010056a5902c2e03501d88034000440c2c5088005500d005410b13616445240300300c4425003031031f0f2585070259090389002c0c0600c960f10f801120558011000083c107100d500d41000301c03458018410b40e003001c100030f0701503002c0740c03107240309040802742508550b410840a503010010840d0f000200740050b5103059014039500194600500012a21904200500c45803c4541c2c0c020010442050310404003041340024500a480080d6906154070310b060401d1107000b00c4001c0d060350200b05d207004104200740d201019502481108050b1200551700045448d9110700001f00202c5a40050020030010700d0500742d0641c100400940321810140e540100f0022904281016282500801c00f00103842c64a0310601c0421520f60514500310f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 157088138 1250 157086888 157086899
    0x80102030910051501081b0708071104140f04050c13090203011116062720060f0409020c0f0f03040609090501081207061415030c0414060d0201170109060f090204 71
    0x3044085003845c140b140c0340d004168210006004014019003038001d1681e604117500e4031018941c030140094031042101c02c2840a50320b8203000d8644a454900c880d1512900c80140d410307000d81014104072243d2250034240e44e150b441da07940080c02401c0050b0b0018884900d40181401d46101d1500c2d01040c090811140d41d4508054108001d0283c10110000d009400c4c02c52455050180c0e80c00a400040ca80c41448204484080d1245e140e03030404d10615030405952040c00f0351400388075900800301c0010702050010300166409401c0344401c04003102c6942d01680311527400c00c0c80c510041100c5400000b8207004580e000350f4120010485041c2c10045985800c0100b51a410300c0100801122000a81d46080c400d06401c51070209964050380a22820321040340b0303808081c0411000d0090148010054003464180300e103424806001c003414109035104404c101c0310741440c040c200c4c1807010b01c16464401d0f8441c01c6440b80640405040042d80d44d0408800540801d4541d0156030902c2c01003000303020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 157089388 1250 157088138 157088161
    0x1401060801120201030f1404050f030906070305090d0c03050d03060b0306030a1119140108010603020712080613020706020306090907030305040303030203061206042d03080112060e0708010203091005 87
    0x4655075020340c000000c080d840101d011b03002c4d2448003d1100e0501410a21649000100324013541c403e00c210340000441526568490283d070781000d078070200900030307840032a01580c024690080b000700a030702414000d03070f260782050700c5903041540c0603408040e800b4501e81d00b501c1480c014006403a180d50440c681035000a0307441041000c0240a00340840c0e0512207611004004074549120410025080d40c840034540320181081d203a640c00100440000203000740607200329444640c10143d4202c80c10705507482681c3c0f030240a40f000fa0424001d81c0420020841b0744041c2c086c940c0703c0c1401582d02d0034018200412014064501400394000502c2000002d800c03108544c1201da0500740980c490751920700003080160310529a040500884007080104094403801d889144071000c0a1528125052018103001c642180c000700411082c0d0f005000009000c1c505000aa1180a0204558111045890420740310b5408440c80340e4003c000d203c013002c0188080c080c0820044010049490898040b02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 157090638 1250 157089388 157089391
    0x403030e0c0f0604031401140108010b030607140315011e02160b0c100f060f120309091506080a09050a050a0c05010518010302070203010609020c0709182f19060314010608 75
    0x1000c1c40d602c1c1c6d90743d000019085d00710381030000b0340728080003466a58150460280040d0860a4441e000303040c00210541d01440c190055840d1851640e41503684880503101d07800303401d0070b2444c14050100302e144003100b40c01310004d81d8503505602505c10561844d904416050494110382d8001d5018050440003880004000f220306901001c049003012840542d200282110740100e0840d8913000c0011614640d9100b008080e54440d90740c80034403a80d02e80150f4210742d52464002d04070600706104100c22407013070803229082038800e00d001a0341ca48940d00c0e1460f202a415040307409820100c4120140710030340c3c0144000707000a00701b8528146449110400d4111361480717250505a0104103502552025849003010b8810407800b15035890503c000c0035515016840f86000701c07814050701c1001c4450408051600a500080500000a0b2181c0c0c29075403842280e500d2401c018000541480e5580e010854614074035070042a890b0345043c02c0c40102a02e081d0010381c0da500709030000401c00141c1c4902c405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 157091888 1250 157090638 157090643
    0x518030f0a0807140304090207050c10091413060914090f0705040e0a0218010504180209060d210815011b0213020d110306030d14040608040f08030403030e0c0f060403 73
    0x1540e420f918640707055101500041d8030128440820f012601000560040201d64018801c4510b1045142d04200050260800700c50005282040420a00000c01d000c01500740d070040000904008903c20745c0d0450394a40c0c40041c0703141e240c1040f041d03500c1501400c550000c08440180c0f82d0203e0700041c443d80c0344003030710803280101d035125031084841d0018441040c9641d4028880134109007030b180c0342c1036900c40c00e00403603100d145440035403074610082c4a0503003890750340079003000110750b5114104250000d1041c2d060700c0d035202240308506045164050f95a039000319455012050800e800f0008104400d025600d06108414408a0381241003240b201c03601e0b64101e400c1145044040e103071002034010b11118041d100d0900d00481110034030300010b1841001d00340c0881d0484511724038110f520460811414800440400060207414401c290305940280983e95402d00d0003026030b226481a40211000e0703000954420030955a44024800c1c9100844200c3d42d030841200d50b0000a240e500c40c40c40300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 157093138 1250 157091888 157091903
    0x80a030606172706070f14070209150103020408030a03060608010e09300a0e09070302030c0414010207180b0a14010e01120b10111c0f0c05070b0a0518030f0a 69
    0x83c0703150350444000004942900ea0a951080c14511400740c28206044c1000c3c001c03030741c04000381c485461044240c42c80d954008000900d04d48500c070b5089000d18605150071304058003040b010602d000c0c10001080c04401c40c1c0d6001070941d1401170003c0107004180c000d598528a11024001f010038000303914561030002e40c255403079034003410450003a695050303140000110310200d0208816a00a02004070302c00701690701a81569460f6011800c078441115802d0030060140001e1001c41c43c00c0071002c000100c103004079075025440320319114034030040c81c0901d8041901d03600034451a05000b1346000040c10500542d0080342d0210f8000f0b00302d1242d6214060410403d50030300182260700d60418041c1706000362140c128074910380c000510001c0ca40800902c1d910444030341004d40b44d688a2079139042e5055554000e071261250600300d03040411840162194440e101000c1029440c61000b4100c806454450030395844805c40c403146030758507580d500d0b4426045060b10300c0340140040740c6c03014040e502181 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 157094388 1250 157093138 157093171
    0xd0f0905060306032d01050f0903031621050610030606090b07020d020d050105070f0815060a050c010507050904060504060305030d15090c0f030e19030503091009080a03060617 77
    0x800d1400340050005c1d602008000c10b400301030081c6900c000c0c4241c2491000340071310340d00c8414140140c041907488501d29030003000080c0c8100004000f400402c0700d18909400c0c10340151003040b00301468402239148069440c0140030a600e800642082500c1031410300313200461400710050440c02503846038103c5040c2c001850421541c3d401504c3d0800c0f640100004c5aa140310f01348075000f4041206d9000c0032503c01c10300018064003500c00700f807050190120798400c012103202400419000000304006002042c40555403000d028043c25100b00c05503603a60380c550f0320200801c81030f0380715544150300580c40c01200b40003240d00882114041c1401000201c0c081d410091750740c140c00450350112081901d402e500380c1000754094000c4070049c246603000d100450311200a03944506015441c4103188480010f9003000900400c05581d100e401942928407455aa8001c1310540b04803143c22a0704800006a11103020b070544110b0000d0041841e0015401010380003d144901010384440c003104c9682e81e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 157095638 1250 157094388 157094401
    0x170601021002160c06050418091103190c090212180703080a05030402011e080402010305220b06120f06011a07060207060203090c03030f0906030603070f080703050d0f09050603 77
    0x2900070545001e04210b542d1242801c0318000000707181003c031031580103040c00194141c441c0c000d85084e80e62100074039180808042d4050010f0084440440302041000301200e0350343e0b0244003a000c0507106054003410030625180403140401e858220034110b5105000e080b503005a13140540754051402c1c441d03034202801207444076182000c00d03407006180c1440000c0b07074070001c0e0b0f00802842c000c500c00c2e22011200d040c3d500c0c517803071245041c416801c0020345d140006009503220780c10050b0001403114a0013403401052a800c0640010403034140e611036001c005103d21800c103100c1541060700303010050044103100400315034442c10113100312a00e103c0c4000391420002404401c50300e42c0f99121004566031042407800c0006500125800c0401c0c0c011411542c0032800c0c00301c04c480789103003d840035a10300034201080007c5604041d00d401e4042c4102c030404a0081c1d45541498041c1540200034000589149010340c40c04000c489500c080002105401c140207821a80000c01d4139400c554851300c075036444 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 157096888 1250 157095638 157095643
    0x90b190c020f030303010f06030c1e0f0908010f02070506100303091214100c030b01030603080d0e03090a09020c070801060e011a0c07030606050a0e0c1602030a0b04060c09050108060117060102 84
    0x920b8299030500002000003111820b54100400710399107074409114105060009030b6504a554442008240380d205c200e84284e4460b60282d06401c96906150350555183c0500b1803c40b6407200a20200c42e40c009040da082c41810052980c0c0a110034071000140381c15950300a14088543c0710701c088584118504008010114895201c40d5800b001141c01103c01e400052010741162140c040100c0d1030040c5600c0c0c90351081c00307450b050700d400043d15442c000310512600010682c003071694402e40000d008101055645c400d0402c02495032480160300c40082d1b60509050030b8281c0d0228440380e14000d41000b02203107a885507411640c054407020541d140c0d4490314480c91090021304040e602885102208106140d4030400994500342c0c2d82280140e11200401ca248005881981000c0c42c10f0000306850701e50407a4001c200352002c4c05032200d20352590703505641c407041901c040b29500d4540608803800c3c0c0d070190341ca01c01403d0903e0660341c01d080043c0041d065001880042c120302e03840500082c55a4000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 157098138 1250 157096888 157096909
    0x903150403080115230a02190b0103020405010e09070504020f0d051f0603110403020d020a120b0f0c091804030e0a0b040f050103020a1403040c03170a090b190c02 71
    0x8008610000303103803034500101110002d00600c000c01c02c1490324001000d105154808103002d0206141d504240d44141001840c0c0081400c00114403d488400b405410f0b00e1896008140c820005481c0c00d50540c4100400d54105070006620300d00c0c0441001320400c0006100d600b2101c06a80050f0303940da04100340c0100c2e06c0f60400b400071960421051083e103120b05408001015000c09010904940b1000224250350540302030b50f07500c880a11040c03000d0318107601001c2d007480c402484a42035a6071481e200e100c820010209490662480040010103840700820550108081c850503141001da42c002413400f5450f00c15245800409100140030140240f14101c800c0390010000400c41d561400860125172242c084d0820050584600140c1075001e40250341020302591501c1844102c40309103420300360402082510b4050840d20000301140d554161031882e4050400f80300d9030703010040ca0141c09a0541e034042807000c001084110f11032410280201944002e502d40142103040c0750000440c10481c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 157099388 1250 157098138 157098163
    0xe0306071209021f0e03010203101e08012c19030309170f090a090c080708040309090908090f090c1b070305010e010c020d02030403050304090203060d0609050f01111305060903 77
    0x140d980881c413803207003a55a8005202c80e956500d003140581c9024507090340000c0d90083c100e6110030000f0300c5007102a117078220450054004903000c407680ea580072825290002514403c07140c0d0380c420300403180380b140d42c00c19511003994014841041e5980c0317084209007940b0380c050201542d0303040340020002c0403007503d801c0d0010a0045030704d5842001e20b204032070b0303c403012482c41002d04800020302d0080c140540c110304105034641c3c2080d1355401005075103001d0f008004404100b82c0c502d020400d151a84a80180c26004640c4075880d251000c007800100d240d1741940d0340c840d001070741c00c00c100d0642c0102103c500c1c2d10703825845e80c20100581546894403c84ea0030007040365081644180d41034078158001071740c103075099007100c507504200002a038691140d4000600395410401c024020411a0340042d07030012400350550014601c60f844407411240c074460215655044241c1d203e50060f42402002020200c80041c1d918042407000c0c8980c44940d02d00c100c2d4004c4101013400c804075502804100b0700340c40f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 157100638 1250 157099388 157099399
    0x1110f0f1e03011e0b0a050a0207120c0303030606051801050a0c0218090c090103080d1d160602060709080a020d0501020405060403060b03010c050c0d080402030c0310050114010e030607120902 84
    0x41d201d030a1a00182c009000c0c02410620103003070f80c64000a8603142000300c60007500082e01c0c0c9503c00408032044e0f4081c01165055204407400011150040380c241185103000d561440d0801341540f4005003a101076500010030001c050000e2600301c602509018001d40090905039a6844881407d850360b024400b006907024000000e00c1003003102600740c2d00c0c45800795030281c4011070483c10030400c0104007130001511420062081200055450b4042005030030300a04d402942080e0581c1c0e64501504040c144000303400e1540b04200140d010440d49401c202070b41031154269003002c3c07800303036910340e1004060300c601c0200c3c2034241440820b6045801609000c0d0056995a40380d0400401801c807001d001c50082d0305e803907043c5403007501c030f5001c0d1268903011002400800d925500c0c110350254020f4002e80c0d044c000c0d00c55401c220754007003114003c6d001110310040f40d103614129401c003400340032036420f5041c0044414400820781d0045241c603801127250030704242640c01d10304404024817414100a4015 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 157101888 1250 157100638 157100677
    0x24030613170f0403020406050d17030a15241d040228090f0e06010c02041a0301020315011704030c031b05030d0504020316180c12021201051201110f0f 66
    0xd0b42440c001c10980703000369402c2c02025602c01c180528000c2c44070014005000ba01285084d008070900216044050420b0210340c0b00440d02840c05900d02c143e00c4021000c9a41200480f95180005500381d4054141060003424041000b6110381d40320389034900f44129800140c001914448254031909034840040000700c5e0740708030074050300c04201070140303c2111308010700010f4641e14540215204010683d2502e40121840d8203010160140c8064403480e9115548070441079102440510320401021041e0410140301340009042d61841c9468074284903000010031020940003403111031004e5161034500310703031901e804500d13100c03410000d0018910f0100051040c4034640036003207680114000ca0a0f00c081c541c5040c0e41c007940d07075040c0c82602d0f843d642c60100c108046400b94420700e19000300f410486400200418401e04a80c8080540090044014010310030390500207100711441d8000c0300204040b00c601040e06c12540203101e03040c1c00040000459004e403068010507560a20744000710000f0a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 157103138 1250 157101888 157101907
    0x1090c030204080f0724020d110102071a15040207080a110f030705160e1005060c0c19060e150403020913060c020d111b0d020109050d0503032403061317 67
    0x3140100c2c841d9a60b080c0e100020440d050400103003060491b095034000f402d4a01c6100c030151528500c15101b000e17195800d1001201051210880c6201201c0e8050360b403601d807610240c2460041c0c0350b1003c640c081d92051064a000074841d100700c685150035420300e544444d030b40303000d550300d09900f0418080c51404041902c004016001844038440c5410480c00030003940c80d50146044180211452204000102c204015900b404c40007001c0c0c1e1240f40c002d88581c80900004101d42044041009901c00d6101c1f01c1009515070200200b801a10200c50720010b101c61200d5071a2180902d00011348111400b00104d40080b190311800c1e2080399100d070f4280600448600065180d5881804000100340d60105040954001241400c407071002c8a40440642c0e41810038011130029012040341807202e41c1c40007140da5070324030b118100103174070030b0000355680e161150f0004044400d00d10813844c9a03031003034001e0301c2d16500030035484d174050803141a00031940001e0405d14429442808850301202000034007856 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 157104388 1250 157103138 157103143
    0xb1308072a12020609011116080a060b030109170a0504050d060515061306030e011d030c010b01030207020a050409030309200117090c060a0903050d09060e1801090c030204080f 77
    0x758800000000441c0d165250039424182c4001c00d0002c0d80034508100203541ca40c0079610643d58020b1503800c4519004004103c170800d14210b0b0042c50302e682c48032030190100324083c09036801900d0b09070000c2c4804080369035940c2c40c20140f010015650000070500e1001e09100d42e05640090100030010003104516042160017801d042d0f681640c401c440205070121820001e00300c0701c58101c1d8410300303a209860018102c0c002c00f03090702c004055540301c001c540349480740456032071a0703000200040c545e2580d00080b002d0031620b078072405505050040c89000c002d40c6d60b00b003401046580946002c50303401154039080300200010310300109504288810311034540700c009101c0200010030f891740030700d4104d040d142007a003813000c90b9900301950203c03000c2c48590801c1d40180051551509084e08816100d80d01c4500302081543c0d10800a07150b42001c0081a03880f000c07092241d00700380c8036100c195440b0030700a4071110050284031501038450708207012152003a8105c90007001c0c0102a0340242503010600768 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 157105638 1250 157104388 157104443
    0x11a0d050c0304051b01050d0b030a170c060709080c0105090d0b04080307090504050630030301030602030a0f02073206010801020409050f07020615180f040203011104030b130807 78
    0x98041c407450358000101454030b4170300c40407920b0584500b400e290019884d00c010300341c0c8030080c42c2c150041071014800502c084c5820320040a8046686445115a00081c1e07c0c00100506141c20021080c908100543c00400d079001c9003072003841c0440e80c1d5540c000115183c9110400001c0041d01d2800422080c401d0450141d40641d410f5900c4910b01342d920400c01094800c01e55550754000c64204100907244c088002c0342c825061001c0c1c42808586050100381c1c11600240d1080e00c0460b00007040000d100114861030300340100080c000c43c00c0800302e807219800f0000350403001000e80d60120030351012030740c06084070900340b00302011a80303a9a142d10304907020350040d1103440f80075410500031404145140c544288210340d542d000b81907941e1003000c0030f412105410009904040300074244011004507406580c490004030558a24a0174184141401c4450107580701d188040c1c203000500014107109142c580040c0f41d144070800d8860704d814a14441c0c03095400041210906000301880c0050000001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 157106888 1250 157105638 157105643
    0x10f0912110a0501050a140d0b06070b0405060c0c0312061504030303060504110403080d0209041503060c08010e15090910140103060b030d080115090503010c02030d051806011a0d050c0304 82
    0x140383e0b03507a00640d414001e1a802001146a06805e028801c100c2d6026140f14012a600403548400341d5001c54410b07484050306440d12a05a010441800800c00c80240c10880101190745040d011042c096203900513a0200d22400d14450301250321956941c42003103a20602210031503485543e407031b01400820b41485024041ca0600840e03e06c181d80001c1913504032330700300400074501041d45001000030752040e6001c50744a076076031011030309041c003c520003000f4600c640c100142d01c10004001501408059100c000301288540c20054880024010150551000c2d40e001c41680c0300c001d0b0f81810506c0c101c41509949140c084a14010701c1c4101100381204e01881c004c11404041da0241070b19000000c1d45140411000d2004119003650785501d69038905041c035184100d42c8d03c0b01d0000b070943e11400c82ca400160b001090303241c600c2d1414840c42c0d410542c1525108480104159819206c01051041c181604010001d90448014460803180c003400b150340100080c0c40d088143c4001ea0300203a809 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 157108138 1250 157106888 157106899
    0x60409021c060612031b03050708030c090f04151a0d0504110a1211010f030e0601080304062a03050f130603060f050409051e0109080c0c030607021209010f091211 71
    0x1307604002d4035020040b560165150200710740144881c8188034130a00c821410400104010008100284080c500940040c040981c1d1140304204214161811003c824032032468900d8451112955010006c215410204200381c0f04108104034038560044020b801d00c41c40c1072100300700070081e140301008150038045600018a0341c90740341c07015032025160b500030613108403101070f88103640c006d180c80101075500d45800310f180307908601400d05000c001c2c2c1c0304240030b620126061041070707000f0320400701c81140d602e808503407844107015041194800f6800035060210010703a8010000180044a070031500061a0b006855034440008008000701d1041c0d9008041c030341c81c04511803500d170142122075034016000300462403140c40340d1410411145104400ca41d170703844c0060001462000a0001c00c0c040001410040a52a00345410410000c001000f1034002444180300d4584508c00d07200248020318010140d1102c020003035803456000d8018698031304091600d54100400007130400c515002c00d441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 157109388 1250 157108138 157108151
    0x7080a111005040e010b1b100614061201092004140f0a030809040e070906062001050c0313030302130e0a06140102070314160e0109181703060409021c06 67
    0x4550a0140e801004c494070101401042005044c0000d00011402c1041241007254043c01c00340c6466806100080c8441c3c8909040280344003111014810700c100380c604030b00d0901803d8030542c1d00c540500400ca00c8550750b0300340605e181c010364241c1d48060030404445648989a45580d00040840d40e5903d1040c01c40105009041c00e00c2e0b042501240d0744007144608002c10322040201510a0f051030302800d1042c284002152840ca021b00c100401e0580c0703400d1414040d00030400003408001102c02d289038101000d000e00030200400f100c0d8003841c0315044009071602442c00f103001c0d1088004204d0440e0101c4404101c1003c5e103d032150082d803141c01c080118590303c0c11451a00400d1000076405600b24840401c0418a000c2c1006060130144064450307009400c804017a100300990050030319040c4c0c0d03400520945031b0701e22501000d03407201810130710590025030382c034442c0450009c021425244044089103064407541c1040344401d50080420800512a203441d1b40301c045070500a9903070714200b01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 157110638 1250 157109388 157109419
    0x1a0405120a140c060403060e0a050106091e06060c0b130f0b150f030c060a05070b0a0204031208010807050609030c0d0302030306010e0d0506040b070212030c0a1d010801140307080a11 80
    0x61140f00c07500014080b20b0030541b55480b206d00500c404074108105014004055000030000e10551024255486000070b400105401045002607a00040750005290003020f11440b42c100c1c40c1105c40560122600b0b02d5a52192400e01d903048003d94001e184000c20440c2d0000c101004400b40d00c13440341c2202c018950840c1000b005044c007062a180c80d059004800c429100b03007000c00081040007000d08280c1d00d020400d070f81c0c0c802c1c000e508a07801e130f42165010a0078020400c3c3c0500c144007410b041e190a04095040410303a030740301e001e40d00c900b502c074a9000407441c003240c9080c400c807442d4050003001740d004000700b81006500c7e40e0085a003a0b0000743d904900e22400d290501111440d5904a001042240d0b10380d662a800300c00c01030f20000640c8541054085210441c40040d489485001142512848101e10241a00042d602c0c000a150803020150030f0340d17603000c8482070440e071404584000706569000468100107030354206103054000c1e001c1e4a0241700b444d181e14401000240c84013268200c035079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 157111888 1250 157110638 157110643
    0x60c160513090c061b08161703010e0609072001060501110106180c0203090307060e04110306091627030c080a03081303090e0a0c0305070809071a0405120a14 69
    0x484005005500c3e10005000c0144a091080e0740001003800121240c559621140d0480d000b19020185c2c0c0301342c00b400001000710351042003860744c030420041c50655040401454030f031400140958050b6800d040005d9800744200001c0307180740c6441c002c280603842c0301d0b081d04d4080c0429005040c0481c0b0b0b4110f181c41200d03814450f81c2c04a6244210202424210007e12005041004121000c40c8000e201920b0b9590342400380900800b036036116248030b001201c05010039942d050424183e006428070400040d52240c008c100e5010f40324442d1488588185002918214020341c1d042e4400001e01c0900807400b09082a024113881c080e04e40502e071203580704116542d4152940005001805020215402a4408401c1e44500f8401d040000e0220340321081502c042e801204c100300d48580302c3d205520407981500c02c05800034031902d0291010303d0640306140ea105220f2155114004a404509543c2d506802c02d03503000d042d00034844458180700d590b4513540c07104407000568521012032494a0020b400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 157113138 1250 157111888 157111901
    0x11040c1106010f0b0d1a030304060c0302280201210e03070510050606040b18040f09030315050a0b0a030e030f090108070c0b0c0c0a14010f11090915060c160513 70
    0x20940307a980740017402c12050003d00001d03042d00329490403000036880e082d64144040d0016141c951b80300e95015020b810000e1820380410401800c0401070702e454122a4220030000d1900c540a017403c40f810191003125028409201c6401070b4110714000c50f6802c804000f100400495002c0d000f1245490010030b00300017124001e80d001640134208100030811401190090500040e014919802904401e404241603400341800603c203103941d030702d28030b04064046c411000f1003a10008801c0d115800c1101242c695182c50041c28034010005ca503000c040e500c41d81245044184080580307840d4070f01d5180c10b0503207810a00400f40400d003184005000745102d40704409925401ca0b80b05c426944652260540030f40c80b9007138501a0780a03c40207900880c00264071020450703621400002c0e80c81c4081c0b229403c8900c012500e0b45003a00400c1080803680d100b484050304207018184104680007290001100b92085c00508070303203401946190810004c102c4d540400b00c0f6002d80341070100c02d907110100800c4851 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 157114388 1250 157113138 157113149
    0x30b0f13051e15040506060f03040302070f080a0b04031215030804030507060f0c110109121401050a0b0612060307030b01060c0b06120a11130204090e070501051204060911040c1106010f 81
    0xc84003c980d00b458107070000381e0070180c05030042e4a44a8048024002584200e5040d400751f4400c0d00100302800306044441c00900240d0301030a00d07444503954000b401400030300040c040107413070340318510500700c0ea034085032107000320702d1906000da5940c2ca001809900540300c280c2c0d0b14001c820340003c006000b07846125501c0701c15031b5082542482555142145018010494104141140085200718080040a0500340580102d0a01680303134030f005030a6480043c0313251905410310b03442c43c4064450906070380100315a00010080e55440e0804246085520b80c805001c5010000001498603003041c00145034a00811125500c1d586400621000b54094045035040343d00002600c2c01040ca51810004101070003032950503544c1540d001c600c2680c0041c0c0003400002d540b41a01000303601c0030050740004020a0070102c0c02d2403061540c03840141401440508030503180d03500389003005041c04030600a21001070003040524940070000b080c20448500399409482644008160f1104003014a01242c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 157115638 1250 157114388 157114411
    0x6030512120403081b030a05060a0605130302090a14010e040521190e03030307031e060302061606020702061206040b090c03150a05030304030b060a2301030b0f13051e 73
    0x700d50b540c04440d100f41c010007555400b20350140c1c24170042441c40c000e5008500e280c01c0800d89060410030420400605e43c0403070103110b01000255851291542c8640c112501240c04200c603030760700b202c0032000c0c050782c401a0715008049800894001c0c01c41401c0d074000c0740140100e5004d091403c044540c001034080703184d00a000c0a0010000c010505201048204018604400340c030800d500428a150400e079812800300340c41c0c1d01c02e550b003102000d1520055000780d440a0100c145550085034503449134a10009003480c030b8038045014003485030100c8a4443d4054500e558462149004e9101994203a8242c1d1003130b8107142070752400d49080f061150081303c07200388441c61500c4041441802c0042603404a0700421301a40001e16079070188060301c021805500c44080f6403801208100007400c0c01d4029001f41882c40c0c6541122040092078022500d00030f080000d007a80008001446c50140d007a10b030b613880300c82e580c81450781c20f8540c4c00c058010000e01280b000303040071091340d504407a442240c1d2842c084 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 157116888 1250 157115638 157115641
    0x140909010902070503120c09040e03120403230d05011802070314160b01030c030b07020a11010810030212010c020712030e0f120703060c020c0f01050a2d02010603051212 74
    0x18010b500610700a03206804030b9191010008241c006244d0846e000c00c80a00c010419010078209400740c41488015480594a031100e0000706204582d4058400341c100140c01c48803280c0743c4502d210701003000c0040700c4615103400d040141c1d040500720900509440e5994156050508510743c004e80307103503540c103803140e0000c04440600242c60b80c00200d06906002040246c50000c520392014282c0038500540d9005a56400e60030800e0386d8040142000003150b000340c0200010400740790540c56100000d1030001004d49079207000d41103450440d00080c2d40729080f80c42c2d61001980c15032043d02c40402c0b40e02030310301e4283c1d5400c60303030010210100e010740031420b1150000d039140b40c0a0440c4406c524014903000441000715602c40c58105103400843d5196580c254040c0402d8040101d44060700080754045401000c0c1c1000801d64000c482504043c040360200002082c000c41890107045403100055081c0d0a5900400078060300d50351006035a82d003c0c81410340d0b4110308020840d41d81028104058816 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 157118138 1250 157116888 157116899
    0x6030403110c060a020313080f07030609050c10020f060f010f03021302070f0c0602060c160b0709051f090905040b010506030a020708041401181a1308030408030a14090901 75
    0x11000c0307848248203a0280c1c100208855540101805064009500464603004080503c6c0c01d098281c3d004011581d0082803903502c003a400084600035030f603100c42c2c0801c0d0401103103452032510750124049540006019504051268006440c00d500702d10ba48c200c0d1010348404161081690082c080d2510380c000c910401d101505200d500245000703e01ca5005140140c1074540d140c0400d00600d04942e0700304010000c200740341d81004140d4010300f2003603044e0702d8030104406010400c035500000400c0d8a841c00c0025031641d02907600b0b40002d102c0a880c1540e02030280c00c1c00780c007c00d504a42c240201e0010080030492240300e1082c203115551046110300283d0808c000c00a82e07820091000d0b03421502081800006800000680018105805c010758071941e50000907001c8001125416182110764004000300883c034103002c3c101615500d0495030b909080070842c4240f5040d0b07041891107100014000551940000060681c084a547c4a800380d5240d0f1065450310302c02d411b01e8542c000a102e006001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 157119388 1250 157118138 157118147
    0x3d1b05070503040e010306020405090c0f030403120912030203011e030807030e130905010902011106070c0221032a51061908190212070b0d0c0e06030403 67
    0x80030303029404490801c0d680c0c910300b4001c05000d800c11030707000b03402080c10003150400c0405207800011000106050900c000d02270001800010000f41c05c010000c504c075400712030198424002c003600020070b519901c10010015019510030700c40ca513060106444040c4551342c0080c0d0550680c4d40c00324000c0c4c605003040e01c2c200c91816115210b03960042c00500089288085d51081140381c034480c4001041d4803107075000240c243c3d0814038440d0b003240c1000b81048885640504403401c10781e411074480060030b41c21005c050111240813054074440c800020301c1d05d111b90101e070720b05d20090704440d244e0b040c0e40510542c0d00d807585106140c043d40784440b03a6180383c00c001c000082d4006000303c2c2500700d88010008054028100c80010f134101c003070052009004607424270f0b40001c1c2010132081000801c1c18a040c0132680c0e02c24103074500741515810240010215900e94119001d01c0100703d084521854481781c0f103a1169100580c501c29881c1703032a8504101a000b00008158403c006000a086d9aaa5102900c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 157120638 1250 157119388 157119397
    0x1f060c05100906020c03030103050a0501050c03011d04060b03160306060803070305030106120b1c0b0703021303140a0501050420010c0308010504020711040c0f08010909050d113d1b05 80
    0x1100c8136001e1040f0200a50200040c60003180940c00400940c035450030300c1801c40300080d22410075403100300014012030502c038078010102d041103e8400d05950721400e048006068003446a549400751042000b00661a00a148250383c095501000800c1d900c40b8115500e01c100300004010035024001000032500902c0c86610b88911200c001c40c00d0803843c0001030343d8000c18a00a008030240700c000300700f44006815069440131490404610704140ca110b4a419502984002018207003640c1e0a101103020034041040e1040e030000c003d01241c00c0c503143c1281e034440c181e080500d4104c41c10400071082d612032012141c0329901500c40710900d90030402440044d522588042e29041207054103a8407580352881411862a0340340c0e42c03101e080b0800d0300024611541a403000c000f1070300b040100e10200c2c03000f18001401d45224140f403040651a811035a06020030242c20b0128030148940c1c00f942c0e40030040c0e520b5082e030108031012240d1411a50240e08898040c031009100e400e044c1403454455001c2c10050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 157121888 1250 157120638 157120643
    0xd03050d0e0610030b070306051c08070c1203080a02090a0306093201150812070c0b0307030b0411130b0a0c24060e130303091403031f060c051009 64
    0x1c2007840e01003961501d001c000781c0e00028000c042c40810000d02000b141140d0304205149004c1c4a031901c1d000024101d075040c5424801c08030300e042448010014540c00300c40d0103030f9204580d18100c903602c2e10462066840c14100740c001c960740c0c1c40080c5510b925032086a0564100030300500d0300b1800d588a01c0002e1415400449201e07600e20a42c042000401c50300d034506121a4000b41940125a0801e41c25034210340e10508254010540500c0200f03000700f40058403000d010101900d9492500305201000150f5200c3d2058070400000d0094281d8035804c400ba50940c2982c043c8080164040190b2417841020380d01300701540810f100b4040c81a2400090030b00340000c0c90200c102000e6902c4007484035a800320050038080b4107c840704034a0086000d14002400c0150517a181d81c5401655245500d0410f44020100f50381e9422460070416000d0b80004000f01c5002266103a14110041440c1042d00301c1c6401a0f9003405400081c4452088140055255010020b004407100030100c2c94040c141c0d00504 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 157123138 1250 157121888 157121891
    0x12040b0f04080115140a0e040803090a12030614010801030b07080405031c0b031204030503180a0905071214060a09020f09040c050a030c0203030f160e1c020a0803090d03050d 76
    0x1803518824002e13044024a565855182545001004440b80302c000c081c003400b8081c400c10400400c00c0f00300c0802d5000e500028000e9403686c1d03109003181130640b5a0303c01016038454042d403401082c0c1c141e00110950320188030f0704628002080054800c4a803d01c002400d00b04101c000035a0700c2e11a1081a400030b200e0301c100c03820600b840607104105124001904075141e5211008511840d040100366250080f80046a150a0460300c80c00d8680c400c070320f210140e000017046402c2e100c1d200c1c0705211004044007c0c0c10001818040c0c002460182440d001d0340c2c255040400d0711103541500002d49000b03400c000c005002c001d2401650b007029411140303140101e8202807180c1102a2164019000e0340496542c0315581c641c001603010701110780d0b908403281150700910421400941c0c00503890b03044101c643c401c105207040b4183c12104505611806600502c0304420000c114a100b007501506a10132070700d00107055201e04540ea039030302401041d5684010380c025844007280c0514000d01410f10030020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 157124388 1250 157123138 157123147
    0x1080c0d150b040f090632090f0a06020d0510061b060207080406020705012a02210d03060501020f0105090613080c0a03050703030b090708010308031519050108060312040b0f 76
    0x9004c9804a0380d070051041d0f00c07511040200b000d0341c8260300001d504190024013014a00045030100e4060089503138118404901250352894200519015480c43c1c50403180e182c135041c07800b078000e500061030320f040c1c40b410303c03011403800401c0460b4002950590360b60a00500a41c4039682c0810605887c00d941d80e590800124021910450040001e880107400811085142000041c038294010b0000c02c1d01080e000c0309540314184801180441c40d804443c00007401c00383e211356089080801006951911801106414503a01030b04001c080310800d0f001e603885070403001280c40c00d803001200c040005410100008002002804070303164000d005240050400300420175030340c58450054010340c0422030200e100010582c0c18064031240003010303203010042d030401c00301c0602800410701006103000b02c044006850010081500052010011b04a0640101c1c540780c92020011500500340007810940003d4914100001d81c2c3e0491142400c94600d403916105501c9003035004400d178020340300710400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 157125638 1250 157124388 157124411
    0x16050d090506060102190503070f030e031b010905040e060a09050f06010605040f14060307030b0105220806010801060b0703050d0609020a050d05220b150d03021501080c0d15 76
    0x10511905500c144002c0c85142400000a890000e07103503080300004459840c55000600044191084150700080f00d100c006a18903041e038482850004864140c415440040d21030b03044040741e106884000e80b01d8846a545070004d12040c2c415000c81c0c1d0905611003008512103020941c444151140903a040d120201d2000070f500d4100007007a801007001500c0424148541c829030f009a500070400c5418502076031660300c0c0800e2490100030288001d25a40c2c003c032030450390042c401c031018401d4070712800d08045a2645038046400840c096011144a03440002c034a00310148900000d5550f080190341c00e000450380c1c00c4449600c4542958207a64031020001511019400602441c4e089500c0e0261502106101c19040b10b078018800044841d80d01d04510038213418226900700315401c20881d00b115030720000310034188080000c180da00003101148101c00d06034007041c40030b006114954903183c5130f680e0300d141c280c2e2811000240b1f94810004040e120000340d00001810b80d007c86c244002c1951340308034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 157126888 1250 157125638 157125641
    0x12130b010602061f060e1c0b0c0c16060e0616050102161e08042105030309010e06130302060c180a08160504050c040308070c0803070c03120c030816050d 67
    0x303034400000743c0d02040a20840c144840c1c010014407a41a03590011140340c19402404c5819011030a40901c08204800240004441400d00000d4014401003181d045c03545011a2991028940c0c0c0744a0140782c6e001168100054031450481d0829501c51149000c23000402010354444072140c1c201c000d02c8001600010020700142015012802020403e0b610505011001d04040800840110822440c0c0000104c804041c0ca0030f030344452078040c8030300d40031305421003200c030170030704081c05511000c0b0400c0104070054106147d4000b59030142da01c2912642e1100c102004c4507100180940c20900000d0b4100c102e840140c0301c2148040d001300c000850f0301020400040042d0070803e9643c0024408941c00f1031a001c10800800c0d0664040080e0700e8840f00d504264050780c08000d03c800740004000d418004016a01c1029110f00c10030f6a56400451030700c1a65a101c40c8000c40d0241091211028158041c140c3ca0038807070740545038004240c2e00c0d810380c06ca4a82c07800c1c1c0382e001809420b02445000c010ba9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 157128138 1250 157126888 157126891
    0xa1b12020d090b072f0405010b0a090b0406021b06040909030c1205122a0a0801030c05040513030c050f070f0816031205030402010203091e010f020c0612130b 69
    0x215005041000140d50005208903801d4000c0c5604400030000140003400394884412403224041843e4031030592000000c141c01c0b5600c00007513200d406c00d000401c1c40c070441030051284240301d03141c81041c5643d42f11121001c0c0103922402c2c01581001c0a01c49091221022032102602d00509803460036440300070b40d204403414030340107a0000f11151f66172400c00202039500e1030f0560090030a42c0c2401034600c88004189801006440c1c0c90004140e84c200341e240c03003c1036120589010445640704c0e891901c004086050274442510900c0000c0d40005040c2894411540910410024075050058548007507034400001e003400c0310356120b5058450440d0405004040c040c0071804601c107003651a01801502d005501c0071800c0b0703070764500f02017000024042807006001d05241d0409a03120f83d03036800180c1c118000c501d8100d0700030f98071078410f0f400180300c080b0403a803212090700c98030002c100365202283c0d114000d0007815005541001010304200716503107d25403004404c000700b0740c1400039603101c0610240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 157129388 1250 157128138 157128173
    0x30302090d0809030c060306240f03010e0703151203030203130b13020109080c0913050f0102041701050901090804180204030210090e010b2a01090501090c06030b04110a1b 75
    0x2180320f070701ea45400e11405402d440211540c07411801c0c02c2d00002c1102800d900c000c081e00c0909813000c00f5151240064611050310904042c0d02c035030f915250308222a00031075880e0000303842c3c0304010088403404400c032415203050103021204854203542c00e50003584058104025000350810500008443c03c810b01e1040c0c0750507e440d50119064400584031100a811040054000a96011ba42e44410401d0b0b5804a40f019040c03012030074038280241403050084003900a940001404100e1380d4141d5200d84100066400820042e6640c81081e400c8900f151401804c00000300810407503011600140300013580c01c03105c0103160581c0c990000d20b5090481142d18042140c6844c200300e0341c00c40b80c02c06030042c001400c0d110316002810080400d00c0c0070004401c1b041e40034108010314116425840b0600c8140e2000081041c6071036820144054490392140b400000d041185020b914141401880811044031284500740819040d003aa0042c042d8112190050803600c10040420300e0303002e90460391070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 157130638 1250 157129388 157129403
    0x30816020c0a091d070503250f0e06100509010918230117070b09010f110d020f010b0f0d080a03110d0f0501060305061807090f1707050a0302090a09030302090d 70
    0x64402918201c241c04444c80540c1d5034001c00750801c500d481c0801c5120003507e105481c804a42074039208840c00700b440d034020901001c41124040740c4154407030015805103208070b940040126080e10f0448081c4110401c850010f54003003010400003410007444810f0302042c00c40419110035040f80c450490a940050b507220b615940b0040201030520761745100e2000307010015084181c206602c00b540f510510044604000407244003250301445807079185101071425050314850328501c4030003036986041c40c461011951800111100340c1c0b900c40ca40c0c03510203101520b1490003080795118620a904142800400c0c152902001c2c823551090000070a0140f0b4242800103021050028140841e6070503000181810314000c14450f007543c501d0400180c0c40080c600288a9aa0b06170007103841d6540c0e5440600e110b04414800b04404001e41000710356041190111031106a8900800c6003804017840065000031000c0c0106010b410a070b00500c01143c02410f0241c84d00b20340c403000c2459424411810380c1e922 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 157131888 1250 157130638 157130651
    0x7030f020a09170606180606070804030302010b010201050601020105191d01020406090e06010201020301060c1209080d090614032a09030304090b0301050f01030809040e0c060705010b011407030816020c0a09 90
    0x2550b050034400c558003220401000c061405c000420208141d080428a0750104840065150364480c404c0700c0c203180e4441d07002031710340f6030b01d180180c0070780610440d080c05075003808001551544148542c03481001c40e014410260f0400d81000d40040000c82e81c8008104910a03500007164000d000034001003001c3e13501c0141c02483c2400050441c0c401401d01411a40104010404c8503846041c10031041c1c1c0040340b03c0e20440324000140c60b014560b602c500d0484c002c0b4603075a0441034004214104a0b4801d450303006d0812184072132040c2034403080700c1c0d0000072407041c014000c00d410001d03195035841505101e01c1d0719214200d4006499500203070b0150003090b0320b0381114100750900f0f0196a0b0004110303d41c04180394110354524401380510748a15018540e0781d288968050740c100002c0d4013109026000a59072401c0b0b040141c06010000c000d940810311100400b56504140130413a190700b41c05545058554549502c0c20144544500d001c004503c21643d0310754541d9100c0280c40c00070001000c000549 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 157133138 1250 157131888 157131899
    0xf020a0e07080109060b0403081602030a080405040e0a17130e0f0103060b03010c0e040c031107080d1b0804020d080405130606081302090f060109081b01020c06090f0907030f020a09 79
    0x503082d050300900c0d040381c213244042007800da484042d942075130f03440100207441c1c003041900300d004400340b5013000c0c1d0301d441080210030070f10101a00410585000340c4050203c800740c20040e40c0d50740348010000b01a031882030320880f035120001c40a001000504402c1c2c014443d5190103c03007005c2d100791048121807034444010420400c2510660301030200913030080c0001d1107580400351501644020080c0200e8441c50070700121071003503006202c070081c01c04466440d00310a0a004095400141c0048005443d22000c508500002e8441d14036000305540c0309040c660351503080c4030400c40702c072008850140050002044a5450f414899000c0c1c0f00e034100002c0300740c94040e0041c01c1507009801601c070088031984178005600c40d0307039100d0b6118450680703032019500c6960049507071450a80c044100b90043c1c0c0941182280700c4400040005000d901329100406e10108001c26440340d0188a0f81c800308078405200b42d41071281216601501c0d038100001d004200d110340105a9100711201e40020307022031000d205 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 157134388 1250 157133138 157133147
    0x60a0806010806041407031a0409150e030403080f160204020309010b0a060906050403060b2e02070501140d0914060721020c0619150e0a1b0e0d0f020a0e07 68
    0x9206400310b6040c480202040d81c41701d01200c000d40b401c0300b05516602c1100911840080291a0f0381000c2d08c104944c480f142003111100d60700e00302d110800c50800940f00901d0b90000181c40550750400d02e980e1800031240c60485459004000d12240c03081034404020243c1d8803840a144501a00d0002080244114080100390520ba401180a1040680003408250351220517181684c0d807010000800f0b000c581c002a0401103252581404010441c2a504c4846100d0b00b21103104020354007228079aa49440c010b440304001c02a007141400c0b01800803c0074503480341c02221865004103198054041c40c0c0190310308000b000c9078414041180ba810225450040c00c15520380012050002c6003881c416400041e01c0e150058054412000c01301e0281201081e07503403008480c5c500d260306401c810b0b50384030129034003810115148652945800700c061074003481144005000c0c921507648541c07242c000810045024104241541d81460070340852006840303203000c100180492010483c014585501d0042 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 157135638 1250 157134388 157134391
    0x5101a030d14090409060b0603090d09090c05160807020924010201150501030b061215041d0d080a02090406090603050606010203181017070c020411040f0e1302060a08060108 76
    0x1401c01c40b10040c0e40d01c0b000c07000c1055a214850442d000320301c2d240c49041510160403803a5226070301590010030b1054860300021640c0c0d9070790b9140c0342c203401150b82c1d40c8940c085802281d01071010840800001822001400c0b400c444180310b84405801c050302030300071550503d8100e681e1040b500d8410410100b226045e20086641d02c400d02c020b02841c241828060301c3c0c031440f0310a00341419110b9080c80d10356a0b0300b4040d180003606d00a03000344c06240c680101c0080400c240b007880c0c002c07890403c03004442039112500008550f0b00302c0062038085820003040350180ca00a00700840280c0c01e11080c01c5030340e031b1401004028500075002064807810350428038144140540201e0540d84200003c0311054940c1c10070801c1e01030100c0c1d00381d1640700300150503110360075403445c104503024038001081409500410741c140c125001b514200440c07103441121900c580b04600844046540d03104c1d04112144141c0e104591241072950103110742c030610b9020a9a41c0c100c191044045603840c2e081012139680100100e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 157136888 1250 157135638 157135663
    0x170406240501090b0c2e060b390a0804050315040b0c07030201090605040506100602030a050d0213031a15150409020901020a171b2805101a03 62
    0x4808551404001070118045445010700c213a10102e5403003e1800c040c13200c3d60088107001c4203629144491281e440c0e104d1000d9000d80c622a01c2d0220101c0c80f440a0000d0b038410ba00480120746c0000004c3c14508090200380300b0f180035655862243d802403190600008000030322450400340c0b510308150405050081e51005124a0546542000003044c6828080d0b071b0417101c0c4500d030b103545040c1030a040303014040082d0064600b42c1040140002c0180001d40c0d244500480e1030000780c80c40d16880100d84900c10031828900003482400600380d400d011398001c11170510100c8040340c00300d5896a4001200b080886001c0b62564000d040000b1541c5441900032094811507160b01d600901c4808400709001303500038070007400d07801b0440842d1640200002580b45400c0f1802426442852202c603140344c0c00003500c81420300000002185c00c40000456407040301d50980c20300d100c503102136058040c0c0a00c20702c0a48003446081001c01401c0d500707125513101078901b4000c1580c600004c906040c80d204c210043c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 157138138 1250 157136888 157136951
    0x1b1706090709030206030403090308161104050c0405010318291e07030902131a03011a0f090603100c02031b06040c03020f040906050a0902180106170403170406 70
    0x2005030450340402c0740000e81394115061500d0b920b0700d05045030036240c0c1d40c0004103d0782c0006030400740401041c0b007000b1318601c259400510310f46650140300c10317948291210108000c01344400d100070360103a0050005440213146801e0040c081d40c0f0341000207000040c10240300904900c04508260f880d50100703901c6500210106040180401c0d55040f801d401041d071381c1010380d50610042156101c4103942644440107000303100c840c0c0c040c0000c908010f405050325110350310780010f408103075001000041c403000004001c41c2d0300d218a8002e0145001d4000c000640c107005011001900000e14810307450300015540c011900c40e40984500c29416450b007400300c90b246d00c002c0800000071885407900c0140c03541564a00b4401e1894000310300135200b840002031440c2c0c1850104107214a06d035000c0201c1030700803a0805e0b0590352005403060598420300803c400a000c4014414042c00ca02074180d400070710078940740c07400e45400f482c1c0e0f0000300e00a4808070b42583d103032190040c0e1110004d5440301c00e050030342c50 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 157139388 1250 157138138 157138141
    0x230a0b01020d020d0f050c030d0b040515030a060515060a09030213052a090a06021f0207080f07030909060b07060c0f2c030601062d080402010c02041b170609 69
    0x103003c0c0d41c0310304a002e0301d41044100261301903600e20840503034881d1404242100d484117151040e06005d410409041c0e4000d42c504000900017100c1d0700c4103c0100701c0003601600e007099264980700d02605004090785442242410380720010340322800101451203460b901c00080c60700f144100610102209041c1100310b04210a1051844503034010041c400901c0d203c200150084e0840b885040c0203500c65103074403050701d407000608140c02062000084c442081141160f01c00c0e5035040040740503002010f00710041c04d101c44a0b041040c80c0007015024024144180880d56403200e401c02e0720915003140c000c031a0003050b910f080101901035840b60705d0312401c0ca030f1455501c01200030311000600d104420300c040c020030703920320780361110910549501010b01680d0b01d0b5a12100080c040d000c0c04890400b1241451014210715002c1c0e04540328100300c0d547d110392150300c441c0c004481c401d42001007a43d2003030356201440d401d400b80c01c13002c000107660341d120104140019a00c4581c8881c3c01069a07028500220 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 157140638 1250 157139388 157139413
    0x109020702060a0c0c081e01050a0e0304050613030507120201030f0b011d06040e01060c02100206150918061501120b0609190b0309011409031305040b04230a0b0102 72
    0x8058584a50f91403500b1040b901580c01e2140700302c421340d40f040102c1e00507071071114400c0c07201034180010501007000902c111b0725000c2c075050031076021400f000d940f5001404280681d19040300140800362030030f0543c2641c20b450380c07201400c00c0e000d0303442020790040c0c58010b07904558040c01840d1440201400402c414140b1100291044030f10b000c00500d800c02c9041845460b683d10320540c0c01804800114200350340e103c04d1b015207601c0c400344040e4030070100c2881114546100003032042c480c155900140d042550030a0601c00200c1000c3c050342041c615100c404c041c01c150402040382300d03814003060100080c2d2000300140c04c1241c4690507510131400c003105c0b01c8030f82d00c80108a40b00c811042e615844440c061940b003441041d03c0d5049020b5100c00041400180d4005411014030401152038100700c07031302c55a14841c0e5038425048400016800e8050030402444e141e4070403111100083c0010803c01c60a4036601c8a20090008620305925088144008030800c0e10620646030801e0004180a10900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 157141888 1250 157140638 157140649
    0x50913020c1b12061914130c050628030609020a0e0415080a0803040302031624060620030906121501170406020a090314060f06030601050a031b050d05030c060109020702 74
    0x10f1107010000010541003000c2e040070350109031602261500201c0c2400c1c41080340c7d101c1c580e483c405803001c5580d5440403450f490114200c401984a00407405499035429907007a040185c2c622042c01815520000080e400040e400280808021075698003801110328082100719a10591213002c41c0000301c000307000070f000c0000c051000f160840e0040307440340d8583ca4200e00e54420200d40550f1907034008500c60401c40c080b160028244548a42020400c808100100032500076116400000304600e0b02c2000c08141582c452166040303220236245400324100101d0060340c0315581c01e03c000382a44042040103286143e108841d80000d1810a03a156a0706203511103016010700050111a400103c2a400318050f00540c402194000d5400c200620703010749880d00d032030040701c00c08420b40c0d070480001c026140200301c05040e5000288451341041c1503440312034800342e41c0c0d01c1c0349030980804d20020a2695078030318140c1e0798501c1440256542c41c1d00728020b81c280702040e886605004c1c0180034450060366072 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 157143138 1250 157141888 157141891
    0x90316021302090402160b0a0c1d01030609020a020708010e0f0619140406020c0c120d11030405091513090c0308070302030702090a060807060203040b0703050913020c1b1206 76
    0x46901c41e118512020009000703100d031a1060707078050320008114460320103018408201c58081c0042ea111556092094410743d219100b0a1001880a0038044100c89040c00b04920503a010f15002410640b40e001c0e0382d00300c0e40140c0004003d41d01181d000c00201409008401c04070134034101428030f103072003030954580c2c1c1c82014012440300242d4042805900a059002403c088848500040981043d041020003548141400314460140d50000d185901b0205021501010f4503401040300ca0b410036000c6032044c2a2002c0842d50740800c00002466660710f00c203250240800021007000350301907008104071884058980300c6214104400300300440c0c0403152500c00c49030080c0001b5038600c4c9525089044d80700c0d02070003d42c441c2c07075071b8140700c041c00c06548444141c0360050101e03420551595000d903545e004505c101201c8890810050001921401c0176100d10140900401c2c1541d02c5c48461400742c0e00210b0380c446042d031120700c0b00c00042ea81109042c504040030748041c285101e014450300d448010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 157144388 1250 157143138 157143143
    0x103231e102009130203042612070311040503011b090602210a0c0b1f080f0c0418050304030609030f080114090714120103020f01030b06072a031a090316 67
    0x20105a12405131a0301071048004e00d201c0100719940c0c641890092450103a80d40513400780540640507152030355a400403510040214400c6904070b603030340c8104402a1141c0a000d000541062100180e5510b090240c400d84d02c0f464034000408184082c07008001e4501680710f0000c550007480ca031881c800f503001c0000001c241e042655591011880b0f030540c0d00102e10880140324280c031004004080c0f0b11071840c23203c044d08008811441980d2114155610b0300206864019900b110395a000d8929142c0c1c00b007094070148001c030b0811002d058580b9400c3d07410690040e502192079241c200101a4044000b0715107000508241c801c2d54101174002d520020582003041c05030a41c503012540e1180661030114242c10044a0381c1d50310a05110010804c4200b840201e004d50184889410b07150300034000c42140840241941341003020a0b00c940c80c0030040ca0000d1505003800090040d00c00e000445641e01450160090068038070b180202c0b103d007014010081a025003050080c00c0d002c001c10000b00c40d0694 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 157145638 1250 157144388 157144451
    0x207110907050a0c112707020c03061506090f0402040b0d060e010609050108040c0b0f0901140a051e0904090609051e06071101021903060f140303030103231e10 70
    0x800340703000300c1d41b000710540d80100c9909503c1004902ca80304184c0c8a44244500d90035100710b5400103062585d9424241c0d14940102800b82c040400c90511101820031010010250350820310300c0b80c0440c040760b005402c050101c031000140b002c200f0550340034040040070840c0240d44650715008009221001c40d000e02c2d0b0420081001103014083c07501e00440140c0a8040856500d00340681a00c0280e8458401140860800051410818030480c1034400d070210940b0351500d041e1421500000e2241809400892941d080c003680d1241d8440748903201c02c1c14824a4005042c10b00340c1081880e003113400700345480804160003109070344038000c038415070051064101440001c03021400702d1301900070500d8142c280241d0320b10b42c05040350301d604541c04840b15280065480c58490815000e07a822080f20a03406d540308000410000d070210600b41c50b001d240c00c0c0050010880c00820f141800b909482d90705590141a861501004003446481c82241e410300d4204808040404c450808455402c058140ca1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 157146888 1250 157145638 157145663
    0x102030f0906070606240206131e080409050a0f0203090d030b0301061206050708060604080d0804030309021207080d0e0d1202070825050f0904060b0a090207110907050a0c 75
    0x15202c0740140c03502c50b503000314280510368440510441e9158002c1c0000c1c0c0c00e40011800a410328004500a80280c0c0f84001800f28210795465228034807020760b06130000c0c0242480c108000c03501d00e50140c8040c00d800b83c2c000c50306080042c1204251a401090459038510400501044040008003004174007a20300703001c10b03c1c2e0609070010340102055404032842c4030340808000708201440d0b00c07151140700316490b80c148503203030b00d810302541e0300036402054500d0348607060103a0303083d0241c0000b691007446460301255400d90750340450b0200c0c052645000c1e4030b274800401444480c400b130000e501700040520f021554000d1007000648052042c03036000d480e42c4111030f50324003000c2c420b00080c8050062202251155001e1561044208400101d50301d103460981c8008126407405540f218059075004081c00c0c0c054070345840704401019064049a03000600d1500042d44a400e4005423980b64010240b1000409965041c8100305500400e81810402c007040107080c502e400401000d2744c03680002500020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 157148138 1250 157146888 157146907
    0x1050906030a0f29030613020d06050411120102070c0614090f040e0109080c07080c0108162001020a03050f101526041101090b03011a0f12071d0102030f 67
    0x14207030140340394401c40b043c41640d1101d1303480800300740d002201502141d00079a62400c01e014050a9901c000f50701c01100214100820042c0d008190007a025401150303013a00d00c20b0005100101c500408c600f04d94004c6005070030301c00402d1040000300441c3c281006a00c1180071800c8207803040028a520034082000001500d40b12580450301603000340008020510f0542412109034100511030000d9208500010a12010110b0034443711541038480c40e4403a290301e80b252441c14a6003454108020b070566800106603c001c0f5070400402c4000001a0b03564130001005040e600014000d050a407201c900307000101c594001d620003201c199441015165503501c00880b9110360798650807000b0001c80310070040300a281083c2900032841007103124a05005c440041d907000225129070030422105100411a00c1c8201c520304c00440c02000c1128a88600d0700c4100070700740c00006100101505000801c400315410541849552000120b4a6112698040001c0d038a10616041014980000c25080716 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 157149388 1250 157148138 157148141
    0xf0c010603020303070803010503060106030209100807020f1005011401020a020a0603020c031b010204090509010b0a0501200102040803040501140c0c01030221070c020310020406020c060c3901050906030a0f 90
    0x60769005041c0e80d541c014606196078541c1003806800e11a001c0c1e1000003540700e01a108481501c100505400d01074054094240e075640343c010482401e5001d49003c42201100612010041040650000902c0e50614440000e114000700c00e590541d84030180250142e41c414264500700d89061030050390702c10780745400740d0960140b444111000b603003494a00c6192003042d0044e10a4880c0c41004200303c2d0b564818a509888003403003050340000c0125024840d41d4415860b114220b042c10202640c4104104600d5013203a00c540d0181c0c070710740c20100c1d05000ba0341c1c1c03200d601c0c3c003a1041128018107001609880300e8482c16800505414103500003900d0382c0c00d1103000d05184200c40600d03014038040c50280d2000d0118140e02000f00c1c800e02030341d4242c80a2425510030360303051700d8103540144480c8901070300b0700000d60b00c020341252541c8210385443e441004d0781000c4540b850307491015850030404404442c603003400140e03601414000c060010110503229501629801107aa61001c5501c540b101200c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 157150638 1250 157149388 157149401
    0x3090503030c0304030b070306030f02090a29040b0d080409020d0603020a1502070f180e030903010903020a12080c0d090c03060203090c0a051005040317130f030302060702010c050f0c01 81
    0x941600001c100c0c0d00b034911001c0b01500880303001e04801715495030360139800c600300e0300e4601004058442c441041c8016080003c3c3d120b610041224000403510048650800307222003001900003180381018001031182850b00445029040c1030f00c00803113160103581c800301c0500450003952034580e80801d11000d00c041940000b401141c024203080c440c0360311910540c010242c00b110f50005441134840002d0b02c2130042050108407546407000b440807100200326403001d0850840480d900c1d100510414400e0343e400e1007020480e0f4441d8000301250402c5203010040030014040c41e80500411100b00805000007008a8035000c0c41c42000240903481d80c40c200d026009a5000940301c64808000c20042050010302030a8080c07040342d01080440e61f40003042006450034550f0b00c0016003d00041001500000030800c1c2c080d904001141401c50302c544e8019440d1407a8001e400102ea81902002071540500482d81c204016100a20156444a00280141c440d1213054001a140050ba10003484800e502c002d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 157151888 1250 157150638 157150649
    0x105040f0f0c0b0f0c210405010e040f050108070503100504020f103b0d0c0b16080304050c15070f020609030a171b0d170604020f03070206160c0804050d0309 69
    0x10b034459442422070b42481d00010717107a2030180b059076034240100c403443c1c501c800c0800300f81108900d06803c203001100e4403142040ca035608185c407118000030600c118001c05010788044c0c03000b4083c052602d01050f00d071a0b041c11080107241d1130001400050303200d1610258540000352080500700003020400c8079010b100c4605a5408032401c00c01d21034259951502441648000c050074500d171910f60704004c00300702d190340003d01a8500110820401440c2001b401e041242203103e12000a07d42d100e80c01258030844084034a9001031a40c90a640380c194110701e007031442e440502d401d00110341d4030400103100502c0040e1080b1801700ba10301196500700041c0c0c0c041940102a044805160001c1840741d802025882202c0b102410309005c14250000707040810007010f9a68101c500004000c51031202406041150132640800002001c0181000103501030881030340140181d2401580c00624000401619070801c060454584003250043e42900c050f0760045503403100e521681d00c4c041d06c100c102a03101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 157153138 1250 157151888 157151909
    0x201270605061f1815080f061507060902040f06082a0415030b070507030909051504020403030806041b0507062708030108060c0f041e050429030105040f0f0c 69
    0x54601c89a0310859030000001e40c0190700445507207541140d81445c1681c09184001000b45001036440c4801020803900301802074030300038000c4180303002c4000750b0380b10000550308161229030035411810280303d03400c22a8084542001064104030600e6141d40e03520030300c41c803001c0080684940200c007074440004528002882005041c00050f0701d5003819440d48070a85442c01581d00185c2202c0c00380b000c41e44541d51599441004900b094058001800003a142d0f40380300030102c2c1459001d4891388024001385029813030341009403500070704009c10380e00c50103034400c1e10b0014420804281c1c2c2c1c111054458659000380040ad4244020f40d10a24807050b0b1441c010b03050100b90b6612041c0b00e070070401141600c2180d070075500c460356200e10110151160300d2103c140994100010800c070683c8070b2140410081900d928102c0a640740c0028060315035207446100c5048403054024000d5032403080300c0c051000d0580090105207096114803a33107808000002c0c00322005000c080c801c0102c02d40c00d42000c1c1005810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 157154388 1250 157153138 157153189
    0x6010e0901081f0c050405010804050f0105040305220308030a022101090c0f030213120204200301090b1903140a08030405030d0605040519020a09080a060c020127060506 74
    0x42c4640d4038901070403400109035070740500d026002054041d1340310b9507201e500c0740da00d81031034000115180301c4018804d40e0180901d8919030f0041c4d100780502230103140a41d580b00d07260131326020f9a400555402c94800c0790103595034800c000186414054a9000031400d4005854080c0f03c84000403000c0d140c200d140702070100400107e030b0500d4640c01500542069956207010301e410480a404a00c41e1814524212400076800c1000b5040a80302c03450682c405440400d42400c01400d005401e00030110001d00c000000c00180318845103449041403807e81140d0030500e10400d58a101d020b400346000151032240d48802c00c02c86601d0030044c00ea40c19920004260b524030f42400d1090301c81e0401c07485030304030900b000340001e1503203040e00566004142c401c80600214200f502054000d501084840040c40500308000074820014020100028065203010801c14122103000b8211144008001c04000c1a45aa0640314440080c88103469901400009241e2a101d0000e03000301110420000d501c480d030407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 157155638 1250 157154388 157154399
    0x60f040308311a130204092405041b03030e041512030206070801090605060d0b0a091a18160e010c02060a120507020f120702120a08030414030406120506010e0901 71
    0xc180182c1500444103000b03244482c5520303014404055a00040e00c00c40b05542d50301516165110b100c102d03100c0c0c2a80182c608603052600c88000041e41c41c080307216031301c900b00001d00c803080c18640416000036485a110b103045540c050500002c045041e030080343d403010b81d08980c03551001c0040107003c0005080d6020070080c64029580d0400700c1e034000c00100e5440000500740c04901907113040d5440100741c54101030700c00103400e00070001c0c15503031035000c4041c41c2c00141c01c490700e100b9505007003200020000b207002214288040c200f0600c00a4a0b03401d0a1010080c8200070030f48035084060744c40c50400ba00480b000c004862400000390040c0d40f104002070b50040181d0014403410341065110002c0c0412754651106985421000301c205200f41c0281001d03200d600310f4030f00140041803004001c040223940b140d0600786000c4540900b111101d00000c24002800407104641851140c540000c45c6070600f07020000b400f000025401c7e40d20151140c001c200581c0c0103082d108154900900103070001c0d0b0b501d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 157156888 1250 157155638 157155721
    0x301080706090515040b0901030b06030a0b12060622020d02041418100611010f140420011e0318030e0112050c09090c0c0322050102060f040308 63
    0x501c6218003054001400141c64100401c80c1aa8521016400c50810345032000480075a13002650311410180d030baa20350311280d036070000618010300e040e0500095210600301440591185040a007040d40c1c0000708021a42c0d560402da000c401c000401c980700400103090358540680514140c0e000c040c0c0c008600868001c40d458102c0d04121002c45100c040e03238200e801c648038180d03c1070303521009440c1410b40510080cbd00805030300d081701405c00c000003a41e4070885090f40413184524030200b28603c100042c8428400d6030080704c400102c44055900c44050314000282001d4001d0b5002c01000b04d8a19500c501d0901075842078582c50001110a85891101d140081c10484940e034060702180500140e502052400e1296520031698400c5603413401c403040040015401000700800701000d010032a03503200c1d1030140081c00780110b6222940890189000e1255a1042250072050455105100700009403c4a40b1140d4020350141010320b01034030341415615801d95405010210605203040030f48e002001e8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 157158138 1250 157156888 157156903
    0x1204150f110105040303051032060403050609011d06090601060810050d050601030b10061b0503040807120c0e0702030715110408060f070509030706030509072402060705030c0a080417030108 83
    0x485081072403aa031035008044d8508800c4244818070204440000b040c2701c03a0106010149600802c0310b800c00342c0d6076444516007441111780005a0351545170000f0444020001d818900d01c10502800345c91404041d0b0503560700c0f05200707400030406000041a0f039100c828107981d02800012380b15030081c001030f00f0b000e40c4d100428403080301e00740070140000b0304041c1051241c406030303405551028600034020440b5041d40f451203000369503e01041100144c0714104100c004014040c141011418460a0330044010200d41c7c3c0000003401c0c0550400551a42c0842107070716540e480401c126804240c40c60324030081c2980c1c1c1c41036038100320010b8085464080010414030a0012200e8000305582d807010440341c0d80540d80f000f64242d4010b200501c00c03180241c202c0d03a031011422040b1607001e40d4a10140e684160702085044100702041b0f1304211041d0b040c00b04990040103424024910b0030207034059006403140b02000c1c0c2c1044582c00100d000c102c01014500d40d508c4034683d0581e02d07035844803035480d1038584 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 157159388 1250 157158138 157158151
    0x30b040903050a1e090b0f190f14030f07050304060b0909010e01051803031b160311160b0f0c010204080d0203121b0a11010e0106030b091204150f11010504030305 71
    0x1400d04c0001c0c140340840990a401e00329516102d801e0b180c41159070a90b00042640d0550b00d2080c01480502142d01c2d601041c2d041c0c1c5607075085c540e1000b99401a0410044081d940840c100800404c40c0c10b1860319202d82c1c0202062500e0350352940e1743c1c01e1810041040c1d06c5c1107684030741d4050501c41d1700901508855048a0710800821080d210740103032155600da00000301e060b1703820500010780900044400442c088100b00b0200e8645003070010300d04003150022008030041001c0c15040e416442040020318411602d07014103100032410001c1d0910640588800c1030002403001070701124000e000c3d01528005c040c400f044500d410202c03040039449400c4403817080210201b450004d004003d00001d1034070213070395022410b89840029007049440521244925040d50740322117003288540024462a0001c40c016030306410213043c02c1ca552814000a5031014005042c18401032003040100e0240c202d07040b816003000c1070040003e0500b5140d88070081344450440d4a00000c02091503099000305120b501c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 157160638 1250 157159388 157159397
    0x5150d09030518030313060503040c090507020a06050c0313060b030a1506030204051e06010507020f1c050d0f090e060f060304050106050a21030e12070303050c0f010b06071101030b040903050a 84
    0x3c506082c1a62800340a99074058111406002c014917030081c1e0013581c00500808207075000c03540b1040303a03038140c61050381c0c0500181d0090412a0034826a4450035420500101c41503196091111500003110000d640103880c035956a00c001c20075079400c003e0100c100d0390102d2803181c0312100200020003488075100580c01241071200140c0c24103004084883c25403a051600e007a644c580c41c0044400d5041102c0481e0480000302c4a00116030f50406e0028410004c1c100c040c48001c080d24001d41040d0300410000c007403220b000f120b900c0c076640103248041980d08e403125099242e0b540e500010240c044804180da00440004142300c180301d410340010b411f541e815200540c41958427980d03120320801300044146005800001c000020344101030003104100d00a081601000c400c15089083c03422640c01100421400120300482c0701c1c007071040f1481d00038035100802c55013401d41c021440394811800001c011041c034030152406a80240c0c4400d0071254090300820841441e8500500140d000302002e10208 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 157161888 1250 157160638 157160677
    0xa030f090816080f0303240f04050c18040b01231b0d1b0b010909150c02030a021b030a120903060f09021c05030a0309030c06181a010602060105150d090305 68
    0x29113000040700e010360642c0100c2e1f0f042c00f450b20103103101040380d040700e19401051000310004542d628001c45014610002c00a40d4818840b147c0380c1d00454004080d0380614140b02410074240c0c3c0004c0e5040c0100e1105041c48a0888914003c100510a40c000d000c96030030800c0d034566105200040300d003c8825941c4a0f842040c1d11821024074018410800401a194200040c0444641030700300c2030358240318041c49071154500d0044a41524200340643c0016840464040300403035040001d000b881c0c1042001c02d84000104c1e012940b01d43e95403c0c0603150030b084002101c41d5920402403903000f141c05c214100801840100380c4000b80c4001c2c0710070b0384500800003c41074051021a502c0c03410543c40710003180780c110800350540c0604072100003038050108001c0c103040450b4407401152441d03011041c401c00358041d45c0c50070440d64141c13440d400e01c4010442d00103004441e0002000d43c155041110382070348500c00b11900400520506c0e222a10543c1080b04d031204160f0003e010344481e011100b91003448 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 157163138 1250 157161888 157161913
    0x6160b0106021f02030606030112030e3f060a0c0c0b07031a030f0a020906030c0a0b03011a070302210c03120910090201090b0307050f030c040e06120a030f09081608 72
    0x4e81c002503540c80e03801101000100802c031100f01040c455941301e424401860b8004800003400c100c00e8a0901003008040c856682c960b403aa81c90600e00010700f210364108075040c500e02650ba4210061900009a42e00c05801c0c0c5c81c0b03800340c1d009030001584249445040c2c136003003a0040242c144045100d48698034480007201c039240210700c811440f0f800070000c00c2c1d40344e43c6400304103070314001030041a01402441004c402d541c48103100b0402408003c400f5550320351600040c2d070b0344108070034035241b00414240001d100113a03022660b40075803880440351011040000c002c10701d00d48102c1500349072903c0b0000d200e815110070801031600c118000c906444054500f0702d144419a480380800900140c40c0d07510500800385003201070350304200d00e0f28007682801030400c0d48034510b034000e650b04440030601040030080c0540b842c6010f80e100200391080c1142015109019680e4003401100130300b40700c0e90818032545280310741c003804010f004102c12600c0d001c4084180003503064a900410416010304c1a185d0301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 157164388 1250 157163138 157163141
    0x60507080f0a0c0e030a08090a050402130b28020c1f0f050f040b040e040b060f0a060e0d0503030114030c150a0c05010b032a030705010e06160b0106021f 67
    0x10412014501040c156110b102020040c640e14801d101803090346088070076140c40c100581c1c6001886062410760301c007074400030041200c481d40d221034465070040003618007541c0c2641a00c800c9808a10155440e49070321201c500b080d1445042c18804007a54030307080c07c6a2640000c034800d0f40582611030f1002071204981420001c40000c0106003c50b40604480e051a40700348005c02404001c1d280c90340c00c041c0c82e0344421810354410762040c01c0b10110b040034001031084200446801610442d410410381a2440128044000d0380c42070340140304400103660780315100c1c03c4050007240e40c0801035a40e01d6840740e84041103900f00708506030282c4114420200300382065888400c2d00c10710144a01c0c1000e22003031044a00500c501001c41d941d54032280c0c90354042c1c40070001060701899524101480f0103412810030540300c00006d015109510442d0100500e136000050142540001e559855540c0080c80000d1160509264010034184449000080043d80332800e0b209009403003600a43c02c8605642c07920 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 157165638 1250 157164388 157164391
    0x100305010503030306010c0203150f071103090a030f050a020d0b180a1a04030909061410031b032c0c0f101b150203090c1003140a09020604030b070201020706050708 72
    0x42e0140d00c10000701c0c80c0b81d07020302440343e0036901c004e089402407040c101811075003c0c4240c654000d001006010701c50459001702240c012403410f44021418240e901d40011a5000203102c0035003120740401e030090500c01e003402844803894024020160001e502c0c50500454901145d980c46200350721640c0380700941c008142100410b4110740404141d1150807004c01c10004081d00c201d091189604000032140ca82d8020310008044e51f00d108045c83c03548106001100d400004008205803800d46481c22102488000180c45000d5250018038842049810482c0081d601030b041c45003800401d420000d0180090702040222054540c1c0c2c0e020700c400014014507070200c03c110808220020051811040051080410f4074018000450309203841d101e1001280c0c410b943e4400550020468902c46090407450290b19850b64607003000400304c00300b01c80e0301c03001d8081c21a19071a9101c4141034195610502074401454201850121900782400081d00075849018116203050410b80016001e0b405000f940c0d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 157166888 1250 157165638 157165649
    0x61203080f0a020702100504050301060f03030c0b090c060408070801061205030403062d0b1008070f03050405031308030301090605060a0c150f0e070f14010c080a03061203030b10030501 81
    0x8441d40712101c240c081c0320001444070b445581c0c20300c07402c0090b980780c003c40c2c4136110f500e48a40e681c41e0304240a050035690385400007600c0311310404007000083e03404004800981d0b0030200310041611204040d03418041d81d640fa41e03501040c00303e030200d0101c0001c19101c1c202d40702d02008001856807003048000c410031608025080d0380052008001007801600900071160a805200d4071100f4041041010b079102d900000c070501d965809607141d40e0411a1a00013109070500701088980b410f14002001c54942c1d9918001f010707110f801041c200041002554540311903110b0115807587c891000c29580d4009104102c01542000800a0301c1d0402504445030b40e0344594030740303c202155840d0114064902c10086180c0759403100607541d24503041c4100655031440b0006400368614083d4102c0c0d11900075004149140f0710203009500c41c0c0e030001050400558802c4c05245c0701c00b042c00301940180792581c040c1d61f041c6505070402040591580c0101c00440044601207000d4603000d00071000c4030424001e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 157168138 1250 157166888 157166897
    0x314100e090721030509150706050702120405150c0d0f09060311070b06061c06051e031e0f0609011d01020304030806060f04050d0b04020924091b0307020d03061203 72
    0x14480110185507003d0112800b0b414501c2c60480c4000100f0030307020020765051700c1e519003c030f071030420440c940c01096004040c9d84010948401c60720b01c006414429840340a100c0c8248507180350540c8400300559490304015015a41d030540241c2c0080c01203aa800700710300000300701d6800441c200f4001d01c5035441118811540c0c42c01c1000135614104071500103030035542d00a800380000d8179203190100f00d10f425442010800f1921925050901045095040c8c50f165031507032102c0c9035185501d00040d55808582e900200d555102080941e17181060812010403d10340200f0302002884101504804012911650140200e0f001d40988a0803804240d030010002b03000780012880a1134260b010300003d4480801c8180b4007952140081c0170052231513021640a4a400104415441d01c034a945601601d5154005847c45500d007100706101d4036416034600c14403800010032003441c0080d03002d0242d0071a0341d40030780d85d80c14661006941d5405d1a06200002030928002040d404858100c90100c41d40c141c5a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 157169388 1250 157168138 157168169
    0xf010f02150a0e100608060105010507020f0d03030b1011101b0e0a0902210603010c080406022514071a0405011b0803040803010e0c03010e0601030209010314100e0907 73
    0x86406031100030b4084120580c941602e0305000c0414084200301242070702c4005982031928007200e0a10205030321040c1030040070300242000d0b07204c070808558036400403200581501030300d19042c1d004007014140c258101540503100f421107a044414010000001e81c2202c0b1051002c54010007511007641c00211010003000d80c00c01342e68090040c607041e50034020300349080e9607160190302c8100d811051003074091003040c0d1640d0007030b003401980d016000301058000780a00d045003070019020740d00152004003560f60001b1510400360954191444184141c0c3c450b4140c0402801d084c902d00c98a00041065400344580c001050000119049160740003c0b1940e42803600d004010350303046182e80e4003110740490000c03c0c000025003440c020741c030961203181500e4aa504103c1d001c4180100140209514001040103004810880245640c44642407a016030f4941601700102c01a10030b068a02c654100980103100315101030356601c20540e200c9902104450b614400810360b03658092240e08404803040b40c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 157170638 1250 157169388 157169413
    0x4050f011a0f01020f01020a021005152d0d03080103030305100f14060d020d020406090b04060509221a010f03061401081b13050406090b0a0b0307030e03070506060f010f02 75
    0x20049220b140c01401a40c9180c5101c1c000c0c103003039900c018404801a0010071003100b1071409807080541102950104407a450f45050128010201c1d04840000603501c02c03911640000718680c0380c424403c0c4c080d0425000d5800c510b006050032100380012800701381002c1c00621040c4d04a5a82c1c01262003811421115920b0481c0030f25208500c42c40050f040441044480d1072040c03280014501d40c1004000140e4952503c44018100c581c20780000716011400c010810943da448001d0f01c509500884403a0242034000700c600310469020080c802d0341605090f0050300e440647d030215955204c00386ca1350130042c840410100d045070298016009003600361003440d540c42d4032468a10780d204508001c2d80c625605032209004050300001c20035669000406820301113420076004000041c400c1c07503001e0007200321704000556000b03c1e074011113158040220004003118443c1e0015178010a00400b0749654512904005440300e90885005d8060440b490900320306500c070780030590541c3c45680c040d045506010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 157171888 1250 157170638 157170649
    0x90420030307062903060403020c0112021213031103040803030f06041409060106200613030513030317010e09030d09030309080316120e0c0409020301020403170304050f011a 76
    0x205840e05440144040400266288100c0f00503070103401c2101300014414641c0310380c90311445002d80c043d400c00014400025000910f5240e15402400c10200b0255043c04280c0280540c85416001690400c24401110440302d10006698001d94a0b420381c51400c0540c01d650748141d1042d408607038000c000003100c0700302c103170480e13900301c1d5004001007104400c4030001450ac07401501c040400b40c0090b0010460380b5084030b070031a062426032900c2d9540310a119404c0c4d4640b5801040c2d02d902844080d02041014451402c03075010801500000e200b29840b404c0c0108891441c20494240c40012400031940010003018030f4414003400c0c0003949000560800c0034060411a40120203140d01c440940d0001038209004e10b210704220078403420b8011440000400500b122030142621a180c40c100c1800310502080c0b802c0c0c1d040040c0d0b00071800200d54408640240b040342c1c0043d1290100c800a1715448c661540194001d50040c0e04071101540035148040c2252040e050007545070013204031529103400c2c107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 157173138 1250 157171888 157171943
    0xc0a1a090a0806040804060e01020604020108070503040f060e011509020c03030415110301060f02150709230402030403210c0806040b010509090405010c140705030a030510080f0a0209060904 83
    0x180c4034218569581100c0d0740f0780711065404807058900070405010b4a54880c40602150001b44010109401c0c2030300040c10700750014010000708071000002506001010b042c07001c01542c400802c01218040d4502c95000f03080340040001d085a0380300c80040d801010340251012a8964000755185440d50350724a01005606200c072806a0344130005000d2840b05000a54000c2025459080d1000d1861800900b0001c20304080e03003903100d14000740030b0025445078a10303050f602c1c1c00b100d62481051150341e4076502c0b40e1200c0c0803a07000b07000008200806030b02442c0005540444d10400c881409019504c40985840c9054040090382282c00a1450700c0c1c240c008204544040c10300610f07040b0440d020405c005000c0310300f0360f5039a454005c1600107607440341e90504104001c3c4002c5007045074654590307031070b481110000f004064884000c200c281004120140041c402c0000f22062039035840076417910f84c001d1302800e910402c9181e0000f122804d0805003140305551000e100d185190f40d60940380d0301c1c602c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 157174388 1250 157173138 157173157
    0x5040905030d0507110a030801030308091f020d020d15080607080f04030f030e0d110c040c08130528031205090309010c08040f08070e090307020303030f0402030307020d030e030c0a1a 80
    0x7050086900c51768061003107001d030501036036618800b03604505014081003005800c000d01a403204506c4031010100c5840d803600d20814120141e40c64100c80030500183c0160708500c1c01071403800381010b18500c60540e2580848070901c0581d20544e6500700152840d65080700c0c000c40b8000c4110008000a200780d848194a035120b080001d1034500c6602c00c107250800e90803001e00410343c285c0403488814020042d88107484000c90741409940041c020062009002400c440c40f400d50a03402941004014898400e000e070254044c0b40000c44400c07202c00d420030001c001030740402c8103410090031420449c06100d11901c0004025440c240d0000c00441d41c10381952801c0e42c94100c144008591504206c8001c001051008002c11807607007030200301d02540d20301a12140d002e038820400c1c3e10058134084203036a840086102c07102c0b05c80e03445001284c02d40c0b1548000130f41c403501c8401c4490416400002c1d03c10107003000e4040f5000501c41c003003032200c03040b250300600e07030201b0420642498443d480c500502c103410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 157175638 1250 157174388 157174397
    0xe091608151003120e3a050102090402031e060a0302090601120b15131e12050708060703050103060e0609100f1d030901180e011a07020901030b1005040905030d0507 72
    0x10790f03a0710755802d442e00410b0300100099102e0001541460f0011b02c030300603085805a6207a00d0241300c42c40408404a102410b52031034240141501480390a60651301c2203040600255500e00c1c004130b40889914100c0c20b00b03202e503608280410fa10303040c0700403030200b501d901811940c2c440e1603207401500c0492076201000d08850b15540681c4840e11950b00c0007018480328101d041c1c44254009019261340c9040d00451091800f04003520080b20010402c10201c0780000c40c0800c1c2100c05003082030600d2802e4000e10254400d00003800512581907001c1030483e80911800c018000f82c40041a85400099940c0c2ca03460340281844566224640d10a4100107280c88001803198501c07403031002c0000c00002400071075000410114402d50300800110341c012040080002c41d50f0070010724412400041c0110b9a10540900d10b09845225070070440e1540f0350001d085059642e5a0b14255074030b0b840441380c0c1c43c2982d400c0080090130b42130038081c01c094107600401071810190308010502c01420014004030412 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 157176888 1250 157175638 157175671
    0x90504021903080a0c021c1202100b06040303030b060d060b0304120804050a030305070e2e050a050f0a0302072102100e06010e150901030303020d0b060a051914040e09160815 76
    0x7c0012074031a05180b803144c880149a18200030003e42444c4060f1a070380041810070350081c1c45543c51000b1101580c0d81800c00003102500d200202d40d150160001c1d240c401352a0050200d550b550200c06180f144e8814005580c0b60440315108a9400c2c1007a00d000302581d001c0344142000038029046030368421454645007002c0006000029210013208061485406003030104030030140b00c040e03802c87c40b00f00c941401ca16182003804000c00610445040884006012076012051842901211121500002e0100616502c107404c0c00c0c1110040249001512a0b65030320b0080e1600360241d5207942064030050083c5070b103000c65500700d1a000a0010f1945104c03e81c845507541d0b205d40c0002e000e0750003907030300580741e140240f0042c0c111203542c0044d62181e00103111070080187e100c0121858240220900d0354141d5100d00c055481060360b007818442c1c139a01103004603c904404c0010f81c070170030201c400c45580c107403414200034040c030003402a250b1640020340201c1c0348518a211458103c1d200034000ca106 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 157178138 1250 157176888 157176919
    0xf010e01050a1d0627100504060305040515011502010f27170a09150504050d120c0c080f01060506090a121104090b1509011511030c0106090504021903080a0c02 70
    0x680d03201010190b035117492801c540d0302c440c520043e1078401c20003d03500214880c00031480030f01103019a115500030181c450700010b040001c14449000e0b440101c048010180d61554500d076a03014040c1d5050005602c0d08941c203100801500801c42d004060740201c121089030b03a600c43c650340c10310300c009a6a0150f1040c0c4031038800a094006c002c082e40307568440d5111801c6c40d200c1e51b6441c04003040f4104000c41800b080c00705a80340c41c2c80d440c2c072540c4445001d2104c2d05416040c0c80d1080025406044001d0700c8000040d071440101d00003500d0b0610303400821801d522001040b80500a25074a03603007040d444501401040d40c55880d5818060158080d0780364030341000d000606031088440100d07a4640c1450a00402c16040c50708a1139010341200c04640d95818186602c02e09040303101d1000402910b5034160158120a10031100001d420200034004141c4a25296020300fa054a04038007900f04014036041d401c4220751000305407a40001070758a05003c010b000c884042e14403600381d0380081d110280240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 157179388 1250 157178138 157178149
    0x1b0d09030c12080103020a0801020408030f03070c050a05030301090e210304032a0b090f100c0509120105010807060c0f0b070e06031008060a090f1502070b090a020f010e01050a1d 78
    0x4610b1615900e0100c190305502c180480b00c251948200d032683c0c010b110902111501005490003800e44c905000c3c0c4a43d00d00b2030440e010f0401c8074014010340a92480e110a024010008606840d0318081c14418600071351411507489500d13074a014070030003e102505526200c1c040086801c640a40384c0102d42e081e2a14100401403140140d200148030f510030110200140031303542030f51214030341c4083d0490841c024101902c40c4000641d12215030f556600300e501c2c20f80504143c4401c40c6010744444880202605030743d008001c2809010560302c1041000a6500e20803030040c00b17207540c01005480c9050203540c88010b0401c0c094041c0003444002c0c103040d0480d48808006d18424141d000c40700041d2454801c1207420310502800c410350b118248414a001f05087c1c1c5510800305600400b40c1c48500c0340c07110203c0c000d02030000020411802d6000744400030ac40003450202c114021101041e00c152400d006450410f416140240480c0d4140281c491081c000c1c0f03110703410582c00100c0303103004202c034100280c1e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 157180638 1250 157179388 157179413
    0x801050a0e01031202160906140d08182101020409050c0913050709031406070e010e0f0f0d060e0a05060a054501021e0703200c0301050415051b0d09030c 67
    0x2407c0c02c0d40e69004020702c050303010a0f5603026009442100c0c0541c242c1e10b03868180d101b0600d201e500b401c035100040f02c3c2500e0328140d40311581d995403035051503080e042c16080c2c040d50207131007110703100c2d030400e0007048400020b8000c031142c020f001000c0c441c0385804003040b5005000d00810b544203010340c80c440003001c1014006004000415400640070700e24000c2c0000d0645881008081d04200880740310702c0040d103c0034000070a24030100e0742b54101181a100052514211a000800b001d081048100c1d4119000a8204107540300c2c0b400e03a0040d030345d40c40046c811070f1070032141880c00c91203484c0c601809044001c81c2c07501c1c9984c503011004250309400c840382001e0302c2c04145122240e40c002a0085400c3d4200f0301d46204410445a0614110080c1c030002d0074040e040920211400003540350840b075200802c1036221002000d8003d01c034a1419041072030520100a0a8250103420304001641101ca4860082c600c11500810705041413400b5425400900c10050101c09201e40840c2e403101003015004100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 157181888 1250 157180638 157180649
    0x9120708030301090c0201150812180d05010615030e100506121c020d1d090c13090209090c091509060c03030f0402030c030a0b0109020711040e0a030801050a0e0103120216 75
    0x205d117020107410002c1c03c4070036812402d8040e0b41d2140b03003072042000105401c400614000c101e81d484400d004101c140700c108140318107a2100071440f90340e040140c10b400c800e081360402842c1d2070103a94600310940541c2d0f040340d07400000e5085a0300c442c1e40d20b161644041e0700100c016044505a0b02c2c415011b91800b0707420340b000b000d0701603110918440f19a040029401d030503da03207088040300781c0c076080c040b8400440c0000d451043c03d8600016028030b0146042d100d2003484003400e40b007482d5503004000c00941c0310382e15841c06000760394000380c01120303c14100e0340d45881c06440c0303925424900801c150302d500004121540228208100a10352030100050360040403c04079541c05030a207441014540a030380188180a600800309060118048403407950448080702c1e000340c0c1c0c480e85131030002c0c0c890b10701c800c5943d4001c4c901100b401d40b41c400050710511043c400c0d11141d0340c0741d881f0010010792044a10074452607400e850300600015107038044821010500e401120403008a07031944d502a00c0558128 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 157183138 1250 157181888 157181891
    0xa090506130606170a0818150d0f0603020609130b0604030b01150f080c180603010306091416050f040f0c0c050d050906030403030b0109050415030506060f03030912070803030109 78
    0x75441840041c2c842c0741c005040341e6491050100224810399202e40d8000409404c141000ca01c0160600082d40303c509404001007200110103810140010b0340d800c5107030352102c100d10b401d2059800c0b00301c0788200300c145e03a0010008c5043c24104410004210300e070202041c07680d6141d41c2c1114113601c031040900081c0d84242100105903050103074048048006120030320070404541c1d9140099500880340541003409405440c0d40c5105c00b5601703c2e1070100c044030090300030500000001c00d00c60701c1d50080100510039040f0002e201c482c8040a50f50b0070800300c00103920010858100054a007003850b2960100c80078101055942d0b40c2407080c012241c1d90145c01010412203070503c030070440c0500500c03211104a00b400350800000801007001800000c10040c01d041c0d49000082950303008003214001410020010302035119025003800d240c0b0382c540b208460034030403000401d56500d4044d07560691841c01074015800c0203200c03001c008814a41d020281d019001c1c0480c082401d08090009502a1224860 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 157184388 1250 157183138 157183171
    0xc103615080a05070804020907090f0b03190c020601090b04141e130b01032909070501021011030a18050303011e060e09011505090402130611120306090a090506 70
    0x508a031000426000b0068030701010400c503650094103080c0c0068060f6240c0c1541e5035916400d031100f103056080030480c0540c02c84005425203800000310700c142a500c035480b900409030380241d404e980c22145080d003d41c101d20014045000c15500480400500500100780d01c006050340e00c402000c10750b29407003004c510301440700c425104600ea042d04654107080e40800c6002c1a00c40c04030007101800000c00400050603414031443e00032010f240038079049200741d042030070486c5003ea5a244070344122030140c0559810f042241d44e2a104074100c1055100911b49169208241d410062210702a0001c03c00b2001c0040400308a007040594044c105009004101180b252448401c1c00c000382e119608200014a680d5000d8860103401411601e0340c200003810002030b00c106440501900c00c2c0f10b5002440403401c1501180000d4011084400e651106203406070b41001035034444040c0c18034100360b0401040442c803103040941959501401d00c1000051881d90342c1d980d1810100c06031380984410402c1070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 157185638 1250 157184388 157184429
    0x307030b09130206030606071211070812040b091f0914120a060b121204030b0c0313030c03020319050304060e0705030a060b03010b0a080a050c1036 65
    0x459080148800ca07095012464815038000410b80c100030024040e480100c08900c0030b0702d805040d10400c9500003625442d403200e840000708081801e15060815208203040000c1c801740101d21843d082c2503044400d1310b001d0400040c44860703400421501d0b00440c0611700c8035540010740b904010b00384070070b0369415081498581a0002007408801046c41480c000c510f040d52503a001135000501540108042658103e035000240c080d10038100410050054091103034420030340310000c0c03050fa07104040340c2581742c84200c02c0c01c3d600d000c2290a00040440c803100d60002c203005002d400065407091040b2440c1c0003007100c00a0081c072000002001050000c402c0c002003007424000d0b10700004000d0020649a840d00000130b0740c1e510040e002070002951a20b1001e03840d01e0a420149006034054030020003103549942842d034540b80701c1c8055034540075510359481d4600c0c2c14070489407100181d42e584540008948861a611000c03060f8084002d20005241c84407210b01049000051004840c00c0c501c110044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 157186888 1250 157185638 157185641
    0xa0803030108070f051c02040b0402030a1d070303020a02130f0609050405010e06060102030d020c03090402030f19051608090f01050108010606090608011a090105040816150e090412140c0102030703 86
    0xb504000c2c880141104c050000c0d4941b0025290096203100306201921034500214004290b00c0e20101c0c0c110340008100021007582e074111a440c0914003e8640002c04408895500e030750b40790000800582200c2e41e00400362805807902c04440d40e0b4022b0025800c0401c090110840300980d00c004440340c5c4850800060120a104810400307240307a000c3c010618100340000d403640b05400d4410310f030030f9000c910080c50301c50410503142301070b0340680b00b15603d042034000746100305802c444880000702e24031000383d40b01c189806058060081c0c54105440722000c2d490a4078440001007040e00c003413140d6500701182c05c100340545402030801000005a15090120003408403c0c2500118107200d84030004100c5544908840c0100b42141d21710f5980b160b00c0c640c0105e8081c4501c0c1e01a00c058070036049108810141300b002402201e5080990b00d41c206203c900607185000b40203030455200941c400001d02049100031f0792400980d291505d41e0700042c952202602c1500030389184c4c8c00782da501000300900b145c0c15 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 157188138 1250 157186888 157186903
    0x2814100207060506122103070c050a06050f090a03090902030705190903020909030906090402090d08130801050a0b010e0f01110a03020114071803030c1a13020906060c0706030b0f0a0803030108 84
    0xc0c0040e100d002003206c0a08a105211507180d80ca604c00000043c5580d4811034038130580d80d0f4400705540e401d550505065003d010700f520031305050781c09079020800f00d60b0002a44e0707095a60544500300202e00e441c901800a420040c000c10038401c0401588107058114520107103054241c1e15004503142c1035006010305030800500400d00d6034004c00c110b805941d1448103541c06408202ea0159030b5002d01c40104907000101da400811400c0e021510300d550300148507482c400c0d5030400c00208065916000994140c8a0514080d0b010500310203140b0351600704a68900e50144040c1815000207103032a0540345000707501003042d030050759203000034803845403000d041ea500980d50745001c4040c11084c009101c0b035010284001400e2290a00400d0b007040404019503c0c112801e11242c4440d02d444803401c04109502e0204070b1040242100141061515106441c00e44c1101001841c02c88d08041c400e0380100003078001241e120b02c01114002841d80e0b45500e000c060041b05026640769450072000d02d01e410b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 157189388 1250 157188138 157188169
    0x71a19050a0b03070e180319030f0504020901050909011512140c011b050705030303040309060806040c0801050402070201020c1e011d031f180c082814100207060506 72
    0x1481c840b04915540003411a09071050f1250440300c94030b8044060441d030410306900107403030201140c1c044000c80038403d4603540e0184c2e500c2c144111408615078404450040300c00a62101c80c8500600443c2410329606602c504c01c8000000d14490080210f03003050703000d0340050121100044c03250200801c10990002c61083c020052401110f454000b0f480000ca10321b505800721200c0402e42e003032281c108910030080c440a01034175039078101410020601041806002c020038075541c041480c80c01d0520815195a03080c0c2e6514995900f444104006580311030340c03c4e411072040347c03203001e00f40d61343e08018a480500d0b0400c0c1c0086803030000007d00a85070310200008056080003c11090b03450110700030210140540d00308041190485c4040014141000f1b00e49001015084d80000c0160b44900c2c042030703494810841d00b1203000700c101b1158400090454500342900c20350740d4000681140104030360303d010034040d2a103003200604203204a0700881002d4904540b10014450719060543c0d20000601 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 157190638 1250 157189388 157189391
    0x902210915100f14120d09141305010e0a050f09030f03040606030f0308090c0607020a051e0d0503070210050901020a0f02030c03010207061a0105130b071a19050a 71
    0x2419032203440d19160115408007010149000048107450502e0985014101011101c0201626400c100300604a03002040303002d03400c600b02c205205800081c114065600d145e0b140046139080c422240c0e9103108200380b203500105040040d82e0400e195002d400c0c045d06401e94131b01401d00d0448599400ea40c005070101b01c010540d042800206540801102d55140108608030340d282c82d14600310000700020391000e07080240e40e00050f4101a48801003501840d800c90440394a00203800c1008114410300134003d6014500540400144c1450a48a55140d84002101002c0512080818484c0c030301c03180122403c1c0c10004680046140c410844020441d07039150040c2002c0461001035907501c891170000c1c0540f191519540300315601000141c40c1414090000e5403290300c50710f0240c001e81301c40c2100c240c01ea46841802c0d006d9521680c1a220300c26603140740d50002a2605840ca000b66100c07000c16604841901007202041d510401050700402c50260b01d011316802d08150001103450280c074191886 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 157191888 1250 157190638 157190641
    0xf01120f020c1501060f080c0f070609020f0906010905010c0519050f0106060309030c020f031e010c080906060105030f0a110a0e0310090503030a0b0d0b010f0807170d110102090a090221 81
    0xd1340c1c0b120201b11401e196081824243e00c910b511002c0c01d004c1c0c00d50070041507074005415001c215041d00403d42e02031094501e96001070302070003044502034007191000e00040f1000c80c108507a620624254001c01c1c0944199552954950108081611250310030b4a0992199003e032121413800d204030402001589006c011043c0c0654008000b400c81c41c00192041b4aa520050096601031124014481040c07101109403190304112034040d1007205000b10114468000082601034003151451240805030740da40d00d165a01916a04d1071080078101f4503003c0e540343e08806544003800020081c035100c41d12411001c05507801098942141c040400b1400c03410802260001500001540d40141551030046035905040f008501c520b040e11001405d40b1440301c0c00001d2030035000d0501416924108203030b80c1c4040d2601080741c888410301c01c0703200b100d6001c0c0031025040c80c840c0302c0d0b40c109001c603100058030b4107540c00000fa00c4084aa00140d0034168002640c00c135042101c2185001c0c0c0c5000501e00b11103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 157193138 1250 157191888 157191899
    0x200112020a120902030f150a0f060b0d050403020f0307080d050c16061e11181516030e060703080604060828020a080712020f041a0f01120f020c1501 65
    0x941d03100032010351180f6210020541150340030300c14609048006411110f007085044005280071500b956048010740c80c2c1460342005410501803081904d40900c051490040742c00040c04c010640204282c3c21401110390750b0080c1e010070f100410300c090251010503110705142008004480000e40f0b0103080c0b036020403a0050b4090340080142015402c43e40000d07070358045c0b05000310b08080c0e20a00c41390240c5407140148521740008064901405c0d040c3d1510030b00070b0410144810444020000320703418000344068a080300103161a20032841c070a141408850440d240810210b40165404030f011640740d00801100f1304252007044c000f002c000c13000745240081c0e6501d140b41107007411005e0084402c400c01e20780642d1034500c503400c014140e80d81182c5c1c4036039480544600c1071103810412441821070300d16001c014030380b40c00344000c2151094200310901070722404001c082c010000c02141400100c8440b402101c4040c030810071012403c1402580c3d4803d00c0c800c2d213041050900007042041d0001006210 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 157194244 1106 157193138 157193147
    0x30a02040f06053118060207110402030c0c1b060f030912040308030a0605040501050906090604090209070306060216080c060a05120115110a022209200112020a 70
    0x704d03c4591031508180c900c25030344992800304958402e00403545590041844500c2200070144990f00da40216060360000c42d108031400c0c40116040742c50f11010b020441080d4a58414007443d0310302d900000c3c03d0b43c080d2794035281c0341c84c2004c40000e209403410490015001116241c04d5111035a901d4111095401181d00064040c1890b6001515041c5030044905a40c401480150755a03244020310800c10402854113902680303074421000503880303c00145011340e1459070040303040b0342082c2c006446c0c000e0380300d00c400101300701c40c404200040012440722403400d022105166100307030070081100c440c00f548484a20341100c21b4000100c0c90706100c5504048100b58482050245401180d1030711126030444c003075001070b2075080041c910b641c1c940c01103426030303024071001698010589170003014004064600c1040581a68607180c5581c008500e0480c560740b00da0305629100c120703400240b = true := by decide +kernel

theorem cover : BRFrame.Cov 157014388 157194244 := by
  have h0 := BRFrame.cov_init 157014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 157014388 ≤ n) (h2 : n < 157194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
