-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4707
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:28:48.507146+00:00
-- url     : https://prove2.me/submissions/f7a10776-f612-4f4b-8f3e-db3262f9ac88

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 846402877 ≤ n < 846582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 846404127 1250 846402877 846402901
    0x2040801050123011b0f030810090e1e0f0303090105040c05041a103e01110d3605120c0a030c02210307140a02010f12062103020105 58
    0x102642c0c0181d095454501c459809880e800040610142d10100c5c80c000c0354607596843d241401d802d4011031100d40400815511200c0b024029025010b0300300522041b800c00240d4909500ca111b000d81484000e1550b2690070400030b45000d044411b0841c1c0c1c4d00e103828640302e8081e15060f1001c50f80244901e802282c00d2806008000b42034181844000c50500700c0820480c07059094160881808503a80000b4006140300301c0c0d998040810309210128404014802400f96000310031010a61749810342d08d03000820303410100d03540c1089841000c600c0396241c5142104030000d1540c40c1856903544400040410509040070b00c40d10300400c2600c0c4564000100354086100d0343c09030003c0c9401c12400500024081c0c8074000b913003030024001006410800003820f80c100145d0204001c1c80e0310204818041000148841188844140251820b08801e50001c0d0101c0340c8112a801448a035001c910030302c2d40782c1c0d84024020250302c964907921b050140101c1c4242000c0c940150b006500f8000040d8101c04c1c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 846405377 1250 846404127 846404159
    0x40606200c0906131d0102040e090c09070c082101050415060818190803040b18191110030f060b120105060a020709020304080315010c0506011404021606020408010501 73
    0xe0705041040d03444004001c6000c9070f001307000c90900e90300d60120035002403440c01205c108070342200043c1d56508040614444440060441c1e0b901d40c818541c00115480d6601d195810084c00e00b40f00c00048001c1c58510400d0040450b03032106128815030640c0140e0003a4a0141200c500f43e40c10818103481034229010070b0014080c030000718124102242c000001c2040c008101c0b5218010b4401044e0a44094842d020300b1075403d50f0400f0002c0240070501c42c9402030660000c0c652014400546500920240c544002160304242c240404850805000f13104d44100c4619500400d80810305541107806001440c240c590440103d00d4800086480010202100c038448010701f11030105078613200400c003241d80110148030440c01481c10009407035105001960080d48542210341c1c4920b0542d150745d9401d54010040350401403490700c80c00100c0d10204049043d200c0910000510b140c0c2d050208010b4400c0c02c44820704040d00c42d0b0082c1c103001565006d00251a40b010003488580d0b40d403140c5254003050b0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 846406627 1250 846405377 846405379
    0xb1f05060c060117030408010519060f0e040615090c02061603060b040b0a23070203120307080f04050708030c1e030a14070c030b010e0403031d0d031a040606200c 71
    0x80203006100200700e01d0416210013002038100d0745466141c0402c0380c2500c4040d120200500c441f80c100156115480c0545405001204191640d16103892400c4c0352108015101815059403551100d8040543c01d522901403c8501010700149000c0d00b0000e640d0241200c05c603c3c160718070b203803502d4100d11a02561089855440496044c42e041510704640c1da400402218248080706c40d03000c4000c80caa0f10b040d130030100d14429543c0c95008600506082001526562050810800801540540110013a0b030440b0320a440480a6526132604a00d45902e58111105030301c80400c4005115a00190b15901a03e11084952041500c81c0c181030b66401081c005030003040d181c003200442c0304110700181c0610381c015400c54100382e41c0c0e5120490307151000e0b00106254608481004103241c0c040c0541e00b000e1021a12144070420140d400030f031100d0302c089807081016102c8e07001c07000034404101035548000d00104204003407079440d04090314441061252000c080c181040c2d41600c030308041001810300034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 846407877 1250 846406627 846406633
    0x9030c03080601030606360605041a030c04090504060e072c010803070f0510092d080412140f0606100503010305070e1f060807031d030f0f070b1f05060c 67
    0x3660a414400c0c7da8000c001e401c03032000c111609402c11144250290009000c2034542d940d03030740d042030104602c1c100c2c0c00088100007941001031040d8240140100e600f1a20b0400c0b0029180e1a24544240900450600d4008520440300003050741540000740c100b50840c2c09410001100140c2800700c44400d0134070808171550002c1c01401c0c042100180d20a014504c02e0342900c004103a0b091000c022a1034991082d00d00b00b4400391003c00724a0200c2d51034442400b8120000d000090584c1c8111441c422401041800301e5248400d404010b401e80914540032803080035111441c2d40d0603042a80d0300e1080302d2052150045d10000a410b90041c4100c80c10b803908000a0400982851001d40200388060000210142c0b01c9e003d100030000c2c1441c050016040360f80d141d451505007858000d0503143c801c0707481003045010381003580f0001c0340001200c00c400403001c8226283c052001140d00c00c0c1c000c910018000c40051000c0100352140e4011080b10300e480c05024140b042c1c1c60320244000e600855060b4400c5034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 846409127 1250 846407877 846407897
    0xb091e060a050a052205010305090309030606240f09041b080c0a110a0327061b0305090a09140a0e1011090d060e06060402120115050d09030c03080601030606 69
    0x7610403070003040c008000b030411925002c030b040c0000c00341c0c0086030445400b090214000740410741c0c0c540101038200030101e00450625540600090311000082c0c9a1031080f21000341c0b0340702081c45203440f03899000c00c0030070907a140c25005400340904c0d8409040d0a108602e0700d0034104180c03540c07036a80c00c0c5200041c1e46040c190380c1c9224008455901c010130141c1840b804002d1400c000c50108414041c292003561071280400703400701c649103440210b0b5074a22091440700020301c0000d0b484070070ba11400360302c486075800c03100e01400d06481c0c6118501c041c2d40c200e200401d000c1144652038212041c441810716a808569403070104d90390440e00e0b1001c0001c134540000074221844483c0790003040c555101002c01d0742c80d00b4600000140d00400e0f8041c11240d650300c039844940380c66401c0c00b8050f4440c0c0d0a440640c0307004220100044911014024008040040800c2e032180d40e01c10001d4541a103440c0e04100300c001d0342c40c10f002c0c0c031864dd1403000318000f4542c0000a00745510038001d000840d0001d8843c44002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 846410377 1250 846409127 846409147
    0x1e030a05070f0602031e060406060c080d02190c0308100b12040507170c1e0d0b09031909050906040605130e03070206120108061b0f21010b091e06 64
    0xa584590401d8a50032004142c0c540440c0451006502400b800704040304082c07a0103004481461009140e240b1462825108010350340c1c2050039059801e510064890350b458081c00704800a0003029a5a20300b17941c000014a81c0d107801c4070f00d04500034000c2d02c1e003072a1941c405032500c61101c4940601103000b038061184040a81841c009144c10074800c0c1c0503100074503111210400310b20308035140a145548654040b404a00708a208610481d07000c40c03040d10500380f2400460b0b8070031107418000b4403005000c4005a08240705000303580c400c0e2110080380c1d201c441c0b40d40004154203110300a15214811540200c1c032185402d10a60003100c2c0c000c0c10007030801c503416400400030025100e81481e00e01040204500694450b03000b0010aa82d0340c26000841d41018440c03440c12400402c1844400380404095402c442d41006841c41a400400b0707842c0e035100300400c0031981c044c40c4c01d89114a0a8848004200000120f001d0000c0a601b03550610850345c20f10030303d40d03031405014079050700300a080098000c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 846411627 1250 846410377 846410387
    0xd14090327130c050c0607031b090323070e01030312050a1a06090406050d140d0f1d0a03020909100e150406090c0e010609060f0c03083408091e030a 65
    0x1c0c1c3e25900f810350409000e45012404c0580440320300f00029622035003a8003030071400c80040d00215080ca8500501825a80e0b20960030082400d45903010307115000e90341804da020400390340038081c0002802065652854042c015100c01142c1845007030078200090f040a000d44580305900642d0b2030107161040441c018045580d010708107143d0800c0d142c00c0041250748503440800700d254480c0741101c00142d003450b50b07681841d402c80c3c8140204080c003400018040d910142d10a00c501440008248010300c2e400010a500382950001350070110340d20410185400c0812041340e0454909400d000303500c10280c0c1240c035030001080c0c2d100c0c10308600300410081002c50f0b1051015a1083c400c080446031184010700c060402640b1402c00a89402c03000d11007654003420740c0e0a182240d041c01c00a5102c6139501509040d802020440b0300b655401350302c002c88071241400150014410764190040210402c001d11200003111004003500c11b807880c2540380c9400070701070700300c6104e40d502441c180f074000e0300105c0b9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 846412877 1250 846411627 846411641
    0x6240405040809030a08040e010801060501050d0509030d05070e030c1c110301091a0403090b03011a030402030a150608120a08061210050a1a0a080d050d1409032713 72
    0x30708080203202060380340c4c40030012150801d000320942d54845161100c24180c800301600b04560340d905090703003004540d8208040d0350003140103280200d00c9940310603089182d8001e107e8200812400e00d81030152007900959200c50103001074081c4c443c92a420f4041c066101030901c2d4000c60511b4408158021441004541126007402800411942040d82f2042200003040e05010561100c440c144410103802140043c003c01901c40c00d107085601d040c604400700ca1000703088845294001001604540c0d0a008002c0700581c0f0281d01d64000081c10508070085c400e50103030840600c2910060b00e81c0101003001d680300030940b42c1e980051a03030b5010034130103405595101c1203c0d9204403101d1209008113400760500c0b8440c5001e0010304081c48010705460f4042c5460218058211081d041c0715903a400716460a9040d4141060741e1750780c00400c0801300401c1e95420465900000c4018000c200720b02000402c0384280b01f642000385644100e107643e0302d22030b80c80c450a034041c143e5040c40504c0e03415a00448 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 846414127 1250 846412877 846412883
    0x1d010c030b01140d150308031801050402031225120e030c0a030f0804091410050d02031b120307140114090606010c0602123d03110d0206040806090624040504 69
    0x4170719042d8020708030550304c20607002140c400c0c0020007008043c81482d18a00c8204c1e440c440203003c20704107900802c1c1c8540451000317815040300091065510640940741c80102c031034a00307002003107010341d0501440b24508543c4a03400280701c6511803116140004640c600c18900500501c42185160f48018540410200496000600380000104400c0910444010400038401c100d507615241c071082d0004a83d0350810b9214040c101d500f800941c40c0020015114200500040041c0ca44100001c0c015003c4d00511030151100196410800030310020504a00d03139071340d0081c000e50085048460024034200c40000341c03684a10300143c0c8a40c85034055030b0310b96015040052500703da07801812403410040383c001c4007026814681c4904c0d407240700100110f040c601c140304440440248841500c00100344030282044014100d05d00240e070312200d141c1c841c00c0d8000c00003a91240d0b43c150903500c0703d00c1150040b10341c0c000e900008004064100201100c0000b0000e05205c8542800401004181c060419 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 846415377 1250 846414127 846414131
    0x903030e041a0d050114060a0e040b091e0f060f0108100f0b04050a1b183005061f0f0b0a0e03013b03030402060714011d010c030b01140d 60
    0xba50380e0701c50f052103010540c0590004180d00e40b080c0032111001101500d000e0241290403010070201c694030402c1500190b01c0030800c000c580303c280b4110b11b08035014006601504041c08021084080015400107024807072054400710780e900541c1c05841e220902c10448a41c01444070109003600700d40c002c02401016141c0042c0c4000900c1c040350495804032400840d8030355600080d407a03512a03240050440102d880c0044104500c55404600040e691240c10224501111001e0300c03c42218000c0c2c130640c0c00926004964400c40c2005c40d0340303440c00d0f62a03d8150111101c19500312104401c0d00040d02c05c8a0301c5039490034908000c401c0c440d4045651708080050241903a5001c1c0d40a004e400103400062001005071408040d0300301e4030310108807046001058415070407411030b80103c140d0b079001c3e0b011180c03640c40d41e2030f0b403c0400441141400d16070300c951810b031403807100742c0100b000340822400c0c0000800424103100760580448441c80d5000d404a549040410140001000100900714a084d80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 846416627 1250 846415377 846415421
    0xa170a02070f0b040201020c09370f0203100803211807170c091e06061309020403031e120e0c0a08030a17010e01050d03050903060a0b010f0903030e04 66
    0x40220307078480c40804403146000f078000d00c030666a042040c4001c55008854000341824607241060301d00080d407603104203403000001d240c002130030100c028541c40601c0100602c509482d0003044c07130080d407088500310103194481c240402d5503400002a0750314004107100c0403100c3d01c1c04180c90b01056200800c8000809000050500c1604041c403030b85c0024102e540700c200d42c00711024407031030428400500c5107015400c44010800800002e4200368051150b410316642c65444c1c060100f6210321072000303048441014100b0010f0380d0b8205030700030012640640d40e4518030288000d00b14402c10520581c450001d505403000480103280303584800c808084c0d07042103880310b0400d2000718100d2100755014100640002c1034034002150080c942c013124240c80c1280c03003407960600c2000b141d4483c06005003802560040800420140281c0031210f0740003004003104c0300c5103044100080940840c81c0c016001034150400860307840d01520000c01500e503d9216840310601080c1488000c101c0060131405910355101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 846417877 1250 846416627 846416633
    0x50c12180415060318111302071b05010e04060303080f070504120f0209060d0203120c101d0708030a0f0c170a0c140307080702010c020102150a02120901020a170a0207 73
    0xc42c101110400324421048103181c61800340c00c50311400f404012240b0664a11000680300c0d400c9131911043c1240c0c42a0040c0481540f000203000701c660060119103020a149074000702c031031610013116000d82e01c05100b15450b07810310042d26480c1c40003d011400500100d01c10040004c01698400341500c0c0440c109640c440d00c80140d25a01c0c0c41c141c1d518203640000c4020350901c2ca40141e40101c040e50080810741943d40030941d11001000901c80440000ca03202a4080c0c090050f110344d8014010148050800c81c3c200014600501c01440180d21940b00e0002d044003001c019941d0320082c540394803000100d4444140e440c0144100201d5001c1f20708501305030b011310710102600c094a01c0355250b03041141c15103404010030405224803803107640103100240000d44984100e07119644d0a2812103000205440103071302c0c2541080c150003151604100b00541d404465000d045400c0340030350101c80e01c1e01c8281c221801c034402c0ba254480090361088107045080c4071040344a0704212401401464180561 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 846419127 1250 846417877 846417881
    0x80a0c03020a240e0109110112140a06051306050f1c0b1807120506040f0609020a140a09180f0302101b0306092c100515090106050c121804 61
    0x311030301c10f0400d510714604120031091140340300c0b8108501c000c005000080d00c03450304910404910504202503861798101114044e00004010041c0d00b51140030341c288440040017400311401361601a8000c26505181c07040d4a0042d5821540e000c0c240000c00c81842c42804003000004600c02400d171380f12580e0100190846003402c0c480c003004039608482d5400444490708281e00c56000390810b024501c85440130a102007050360b08140d100c48004528202d620b0880040c00141801952203c941900000c0c043d4030903030040d040310000c85142c41d50580310010741c4100d6024504440d80c80d00f4801920001a1b240760f404191503010703004403140005d6016048003034444100c80b0480850b414028501c07960b4240c000c030000303018280300c00c0c80080514803c0d1024034030301000004003003448016404080070240210001480300040030b001d1841c0c008200c103069460b003110a80242d009500005481d80310380252100242c2c0d00c000381c6150300045e9101d00154100c01d50307004441800b50000301c440ea0b10740c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 846420377 1250 846419127 846419153
    0x70e010c0213090506071701120c0302030d18050d050604020f06120c1c060b0a030f020c1209120303130f230a1103061302010302030408091c1509080a0c03020a 70
    0xc003030040f82d622002e180c0242000006803a101c20300c030041d9029004220400700e9941511241d070000081605d86041480d040c903503641c0040e4040c02601d502194651f030001e103202810301c04072450400e09a8403006d20007580340841e0050910780248010500510304a0310000701050010965030402d90a0120146900c10a0340e651035842c2d000108004c140c1e0240707120b000020019001004203e2405c40210b07940c1c86050100020540e6480454948890b2641540c51003101c40d01103e139200302500b010100e9611070760081c2d00c01c00184500200b120310000859108040f118038800004032550b883c0d81d814450740c20b04a032110a404280c49050200c0300d0904060b19103000184100c42c3d01342003118080d404507001601980104040000c5e401c80c1c51f21494005d50b0a20f801a642e0b65641040d25950090743e045990111030340d0102102c011301c0c2c04080081c13502441ca8901d001c50411a080b00b2110840001000d048050018000540c0103851000d0240e0180c01600e40805030f41c1d442911070a65 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 846421627 1250 846420377 846420409
    0xa060e010b030910020405010915110601080d032a110c060a05030403030c03090b1614070c061b0c05040b061b060108010e0a0b0a0b01231e070b070e010c02 68
    0x44104003c00e001000401e0000c000003c0451402d0704101c0000c0c100702c0a40110745503150203080846000c3e00c00c0d08540303823100b4107000381c40c81540c441144030385440c0c0c0d00e007072000000d0401c0b460200b410022040400c0340740000c898151606042c8005450314221164501e1240c0240486c0340103541f1201c1c01401541002d0361803540c3d9241c01c0c0b801031b0417500b4981855040620b8254844002486c1f40001034000e8010300c0031443d0340350382e4502124150070380c841400f00c40b60040b540c1420402c0f032070740c600151100b80d02e0ba00d8001070031900b0000c4d1500d00710f0011300304c042d00f030f0010411414164413418100c039002e03059908d0045011580904d500c1b80c10100203180d4002001040040e10038031850101c0310046000d0b01801990741c4448090b400c01a1002130030380d0740c03038410301c01680c0034407600c10003480d80c00740811501a21602c100d1032a0003920480528422401c511703045200b00710101c402180e407000f40e0b003c2c942c0703610004942c0c1942c00e034001414441860305000140e500d5402d02900300700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 846422877 1250 846421627 846421649
    0x80703030507080a09030e0108061201061502120a020303071419081008030c100b040905060a2703050a1101180b040210030921050714010507080c090a0e0a060e01 71
    0x501050041c8507040050880310805e00e881803a100080c0e1003541c020664401f413901100343d44640000074118500d040c4880c442d50300c4c00c200024101d107120110300495886070203441c44040320b401c103265a48900850b07080107801c10000208080d0140410003101c04003c5a0350b41040c2000390308030440200003140078041111a0b0810042c00040903c0101414400000e10b041440310407055595070f40700861151142d0311951409040d488a51180340e54a40140481d40c40d4140000301c20b006241241c02a520031502c4111912284450200072200d1a81941e80e946003003200700c1d045031103022281080b0010754035411400504c002c002c0c0d8680d8441c0c020b490b03000303050406104120700d038500e001c2c11505060a1980000108a4111040c0080c402c1050b040000107203c6804036454482c805004080d10110310051b40210380550100380b0071101a101e00d04180c40700c001c1d10383c20303014020b14298820740221003480f0105017106419000185840003107034030350b124880b440e0003d40036009007200e56 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 846424127 1250 846422877 846422881
    0x24050c07020a0f0b090922030c030e03060c040b0c15070f030b040527240412020c1005091c05160f030c15110a030e0315160f05070807030305 62
    0x1c6054000c5800414000841c0400c0626094094055006004411b40300b100d4100004841c0341040c0d8002c001c100d0842c1c00081101540e1030f010b49210902001a030000321050b1440846040002e0881e024441911084e401c092629070000010740c020300c2071880f540a40240d02141c4031400d2400350140210741c071004a41d40c44544001c0c200d0b0400d4040d9031246042201b88800413080740a414288042c50600b4030380d000181c40035a141807906000b076401104484d40d00d910982507200c01ca4001c0703203e00c500c903407605652417080703a941c8005269954400c10303844540c5161406900205560701c000b801ea00055030a056280302070703591406007503c0c6508000c2032400300c07482d002e14a002500200d9402c03548241540c6a11691002d64020101103020441e110034025001e20020a1003854102c05c48540019500c2c4c02412289500c850311f009104582d44040383d2400001118405c0b14402154a1841c04158048441040540311142804010055500421108402444110b00940b0041154 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 846425377 1250 846424127 846424129
    0xd0c0908010e07050a121b03150509010905060c210f0103120807020c01080a060302040e0d08060409020303090d02120f1506010306030213090c05040c2303040f24050c0702 75
    0x1441d40c80c140d90302c464002c042c00340b045a94103903660742600d0031418140301d401134903e04010746003076040440720ba9030071031403000042010708205100c3e201c252440034030254460314901400d82d0302908000340550000700014456292110203040e90340208840c40d502580010b5840061000585160704221005401803003440f500003034a48240c1510b20304001a86081c5000035141c00000340d8940c10400d224000c01e0100c2003a1300030754080d54009000300009142c061140e07955091244880000c5940360001480f6441c3c24420f50000c907401070091490300802c401003240324040300e00101e9015543c411488503240342003055040041086c1c00400315850010301e0302c005884001d0943d03040508220b42400140c0703944000c80c6800d00c254402103080c03440c03850039100fa149181c0000390001c1c44d0000410185c1d620030208140164603a0303204418041d0703814003c01d0751000325809454400403840c4200040c207900d010300c0c24403801c1c00d4611000c1c0500c0000703000b40da40a0350006c1000340085951002c1d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 846426627 1250 846425377 846425381
    0x10f180b0f010609060c030315120212061915080d020d03050c070f03050d0906330308071707050703030e10080f0c0c030906070b0121080d0209060d0c090801 69
    0x40e20120389407160740c5440380c0140109540d0080c1405c10202c900300ca01014000c2c0c000249404e0f0202c602000039880d00da154035841007240040e4410000c000c001d404209010801c03e010381542813625180c146c1960014002d40404a0300800a003c65000060458020700c025002d40c1c0030303a4042c111800d0070845c0141942d5002e8030710f0304030620400486001070002c0e9400380480c0d034103041450b03e03515080c01c3c0c10700416a803e03014003c10b08105002034400181c42403401000c405860003071804662100310484000c0c1c40c00000c150006c104582000f141100d0007428a824907091a54a0021301d5501d0307604201460303000b200403e4020321100e0040c03078122060340840000e45001c0c1054078245910400301d0360003600d01514408001000340418000344100c0b6002c580c003a000c5580c48140d03140c40c103040700c024401e04c030040340d6850402609009200b1083d0400303401c5050307541041212060301e4020741c0040c1a40d0382c8500301f000000c03000c075031b0f501520550310701e1a21a501c0d050f01d04510309003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 846427877 1250 846426627 846426631
    0xd140d020f0304150c080f04030c0203060c04060909180303051b0c07170118030305090c06070c08010501120302070e180a0f05161a090a0f0e010302030c01080106020a0f05010f180b 79
    0x142e4141401700d05807449502c178045540c00749140039646069103a0341800d41300742e80d6a440c0a9010302941e0101310404480c5002407007298100c0e683c00100b41c2d602c40949080b5070a540d00604550003401c0488082480303034000c0380d08020450201d001ca035007020310001680e400303079a00000075005000100402c00ca20614a00b0350410300000340301242d25900d108600c418004402024140c1d98004255a08c1080150001d86000940303655a144954140b003c2c050055100308103503582010004504900faa0b0403020b031165041d0020400641411050010410000d0215001c22141c0c2d6030760316901c4c0c0410035070803140d0007100b080c520444103003070860030600c0b5102011580b401040382001441c600c10b00c442c03009443c1034401525032110b0f400066011046500028841c4d00d07031807020940000c8824a01e048900c02c4048401c1d45214800540701c0140c01d2160714050303004180548003040905a41621407031003000001020001c0c24480012a50040c00d1520a0b07500805110104179001810030f0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 846429127 1250 846427877 846427913
    0x70306090b06011716090b07060b0a0b07350f071704050a1a09040e1b01030603080d0f0f021815030105030c061b071401120507020d140d020f0304 64
    0x10207403110841303880d03c5610024200c8110440035440f055205482844100050a05c846900d5640c6c0f00364203100c4080c2990805007407192000c00c40024490f604072080b111141d90103580012100c0c200728030002c803119140305001aa82c1088090078403000300000030020034441d91489610382445041c03095000c00440c0c00c040c0d42d50420042448690342701110b10044590a00108003075420300311015400c1c0c082d81c01501d4105040c0300b40c1c96501c0201040040c0b000c0050600c080364660010011811f8404504c0064018107080120507286c40040c1c004400381048030038007140c502e50b90038026049030300030102c0c00c1c241c48891503088190b2078000100c8555031100801d0600b1941800c0000c1d403100e4585600c40e104100014015401c4040d103a0214944903003401034030a15035984540e0035a1041036034609002440000c10140c0b21034040c070465008401c2c950003484100d841d0301047d1050310801c046190640028401c0509084c000d00060400314070340340d4580d4480c28a441c0c00c92050307102c51510 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 846430377 1250 846429127 846429137
    0x30c031a010e040b04110315010212030f041e0515061228020a08150109050a150e1b03010b070c210605100801090506090712020f060a020f070306090b0601 68
    0x9100c0c0d81e030700219004000b0811100091110144030010780104550800640b2109000c01040444011341c092070031a40820703026103120050800d46000c492204881c0310b0340f4100c4010110b0003040d0942040d21341034108103280c8030340e20841e0319480e03e080540742e4038084541040c0d04010041c100140303100c030f1840e81c800080c10f29100165510400100c0494050b031a115107088040c05d42d41d94400c1000241460000e440c04000030003000044200c09015503082c840c2024041041c1c12818403070714034025030b1309044981d081e0408500502c59580507104142003a005064404120544002103009101003e2601c0e0343c2c0c4440d142164008a00354410000c0280c5c08088030031000726400c8980220360f00902c0058203030b81c1d03c0743c07807052110035800c240865803078508410304000c000105103004460150442e00021354961030b8801042c180c200c02034110011100002c090700b4041c0c05030408401c00e0050341d00745036402003aa840c10f1480e40c8140c4080c3c0c0c0f41c42025090048403000c007078000d1030038604 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 846431627 1250 846430377 846430421
    0x10302011808030d0c0306180501080601140907081510020c0a05030102040b1605100c02160e1009020f1213170f03011206060b040b2203030c0b0405070b0a030c03 71
    0x10a0780341d0113000e080780c00b00d41d10b8161205141d03110358843c0340500921071016048048804c0a080104000d010311051072040000100e08000c01d6590007454080041c51081c290350b802c0000c4820301c001800040100d100c0d407080341c0b0303155901c5c20050341100e60369000b8101a01d540701000b0000703034558416806640304200500c014008402140d180301400010040c0042c0d1500d0b00078034110305136444814042c03904c80c106807019030204480540128507091040c00e95100d140002c0340703000c2a1034140d00342200b80e400300622030003a0003038080e4070720300201641800c002d0151540d40207001c4134840a815403010384c000402917a200018039038000f85400b04d0078180f80d804003003042d20060180d5001da05035001203000b0000250001c1000d4410004c0c2c0a40741c507a616495580c5400000d4201c002d600941860503591140d403071380704100d070b4156031100016100307601c0b100b810312030142094409001d503c0001c5a03080c8001c0060034007541e16a130005407600c4580c001011a80541c000c072080000c0c0c004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 846432877 1250 846431627 846431639
    0x705070e070c0215072301150b03070f030f050a0b1002030301050f010503060d0c0602030a170f06040506120607020313050d02010206180c04060305031b2e020702090a050103020118 79
    0x4000142070b030544080e08254070100750244e007405000d80007080000407151002c07580c101591031180f81407500c8004d200947c840c0c01c40c141c003800c030781c0629a0042c00500c00a4489481802c90000d0a403590400041e07245810381c80c28103803030045a0800d003098865400c031030b0034200480110b540d4200c51001d542554100f10024a6a03c19941560f04005000c004284a580d403090344038421780e417021b0340c2d1107082e41c0c0e520300ae0345035001802c1d040e0125100522a4449048809450f44900e4044007021115516541004000d00015010703d80001030800d008142a030b040240030b0080501e43c000b10303240c03080b02030002c0024040781c12250241e224035010a0040c0d030006110354104001040b40c200f10b8000e401c900d072518922500c060b41c4a400d002c00042440404002440b4002a07113941e0b030152541090101e5982d40c911401030203031040b068a00100400d48002c55480402c0c04030094545201c940000744440000c3d40c0c5010541d42c0c50004004568201f88854640c440e0040784030302c01e6190031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 846434127 1250 846432877 846432887
    0x108071803150212040302160b0a0e0402030a15090b09010f031a0703020903120712110604030509130f050f060307150e0f100f0207140d11010309080c030705070e07 72
    0x700c40107280900700340001c9408440e6030142d461030710100011210303070b20701820000c0d5504010000300ca002c000c0400041030000b03002c0708892000e42d04c1d45815002d60b8007041484029440105103124aa079180e44802c26401c182c22900b00415580b000481e00300a0002000400a0103078441500840840703020000070380c070345502e0342c0440d9910031264456610241c064000e403140250095050245020102c036001d914030142c40c08034040d142071142910280b0f01980c15603a002c2800c86603034810030001e000240300e20002c0240e10300c040c0140301c6100f061046a0300740c2e0481a40017030903a0715601003012211000200d158400070072402401303624a40381c168074a030794480c801c07001044080c080c7c45c41241c954546035000e000000e0501c4c000041d040b60001c184901c0145d11800501078841e00084201403a82d081c41c2500c80100419041d0388660380304440c1850104c9100d040c9a16084450046000880a403562018240c0030710b954450519043d418640d10703800c200710411917041440302c040e500c9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 846435377 1250 846434127 846434129
    0x260d030911040f0906110d0e0307051903020322080d030b010e040e010b03030c250503102408030d151206020a05070b090a020a14010c1b121101080718 66
    0x1590000b402943c0404501c0c098803003500080c2c02c6a040c901900180c01c0300000601031008031080400c40548040c1d070341c40e01da2243c05006480c940c842440c0416861000c024214158460300442c0d180145400190070201080d0700d18024980856070104042d080a0203c4a040310051608100368040000003805019404400f140100d60394400102807000075403091030034103001011241c40b03542d01e4403a035a03180b0006604010f050940b00c00c40800110046d011002c0e104024060a004681590b455004156809103d40040d440b1600c560f0711260b50004038000c3c5c210350000e1a9641c4920300c810044e501d504810042900310b0900070040a2074411100b07800c960300401c00740c0d6408841c641120180100c0d0300107864410303130800748201d6070340004e43c60891520903500603e0b1959245180520b18120341a054003258921001c900020f00c001101c400301c640000107111440d40f600c007020000d2090060454030003840380c80d030f03002070368001612544c071040d9447c2c104d407154050078105140c0707045 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 846436627 1250 846435377 846435379
    0x31c030506180c07030912110409031e0206010e01150905041107050d050c011503050318031603080d0f05010524091201020711040b210304260d030911 66
    0x280e040401c00755a00d40881030080007585500c19124100030b060081654030040040380450400140040d00c0c1e10014104100c281e00441b900070116036203018440900244602107080100d4100748660362000000010401507003a130007010250704003044d025114a06810013400d402042410b4400c856010920509444069030081540f407550142090365000b03184000b0100e01030001d111010582c46400380c406c070b0062000a005040c1c4441c0307108040c1881e4040034121b60020080603112600182001c00144c0c000b500b2241030340881501110b94011a4008955180c4001044840b0003514040d400300f101a0100402c600e500d001c00054180101c5181c104150b01044410070b0011040c40507a10301c110054000c0200701264a1074a00035800341c40c0440381051524060803450801d449a00c1c0035a0000d084000c441100c504803c09000134581740c0e003110b01c420000440c081a06040c145400000c051000803080369034104d207424000c100744400101840c1040110116100d68894160040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 846437877 1250 846436627 846436631
    0x11151003081315050c010b0105041206020c1005130506061804030c1b0611010e060c1e04090e150c2805160503091c05030304080c030d1802010806031c03 67
    0x4180020020819002d60040007091100c83c0c4810509421000404c4100ca00000030041c1041c1c010066800d4001c9001c2c440070b0500c11034800d000a021a40280080c6156100f2038145031802102007060311812194110311030554100030041042c200301c200d401c8030044030b00d40e0f9401c40c4c2c07009250320f0000080c0302804112501c0700b00b100b4000002c00152000c031400c0320700700030162200c0c0040c1c81d1801074501c0205962a20401901c0c0d10b0012503002c0c042d4aa2619242c0f9040148015070405940c607402016207000400001840101511851811058201c0602507058403090001d00f2000300920703205003c8410000c030002c0c81400d0001c101c5032221903107980c204e01c0780b40e141164680a5141c00d01c09615180d000f01c000c0c0f06000001c2c0106800c00c5035019030b1083d1101209808000031040103140e98070a102040001d03550b0400380001c4d42c0c400c011070303080840e0b0603042000d442c10501017403504e440428041c4107550f0301c40211540406c0c142c00038440c1091a10065110001c10a08441055 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 846439127 1250 846437877 846437887
    0xa11060f0f0705120c04240f0e010e060d090b060d0503161a090f010e190605090a0b0c0d060905150f010e030d02010614120604030f0912031115100308 66
    0x10f00580036240380109034801d9980c1441c0011350040e0300c2c1d106025a52412041c44104c004104644080014080d403035901c008070b43d0041700050710010000e149039410b01410702e208881945035400500402208000041000407241c10800d68a00e0702070041d40c000c4c1134200120011450000407119081402d50242000003418100710a0182480e10708000b1130107503070244800003800041d880d2100b208803000300034034400c460f411a540c1340744a00280c00c900540181201140c126400300e40d00105050070380d03005074401c0e030700c20b81040703000c0310720341d4504e030303020074845000d1710300d07100700006801d0900d0100b01ca41000030001c4484004100610b2298035078192034921644156543d09600f40054102c0d0041d100b0004064080c0c510f0303008a200c90114010400c0d00c61a000740466080c2c598000504865102c9031422902102045014018050701d044c0000c1c084c0100c48112a509001382c2e111280481007042c000e0402d00345541c1360802d44860411f1242a03554078651104680d0300c1941a0758907 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 846440377 1250 846439127 846439141
    0x82d0a0e0d14030405030d020f1801030e10110415090e07020a0807020f030a1e2001050316091a040503010507080103080412050f01020406031e0e03030604022208030a11060f0f 77
    0x103128408041441d68004034540c082609c119014115441c4007100c100001c40c0907400440031100111441360540d4890a40110040000d6001c0d000400b0b01c1c0401c41d260640781d01c0e6104501d443c410b00e030000156807407800c009031042668107a8100c8643d10151210320030030340399200700c0d01844001034422450b501c5100c0d00365400f00420503541e82d000e04d032a5251809445004028420202c050b83e40344103c3c081c2c01d030485e490030038010342400141c40341420340e19a0031800c0301c00c0300400140342c10301c00002c3c008a50350741260312241020840740f03010344e41c81c2d051005241c255100901014140940e2100500010303940805680c1079400e144402d510b200d00500341140340040b04900001c0035480018080740c072682c036410044407800d090582d11090352820850b141101c0f2210600e4607290404c2c0f0114030719240c160020300e16400300e010006084c04041b840d85600d400c4542c0120140d42c000503001d090690003100c1c41c0d40d0800724002801d518505603c1c89072060000402081175000e6040009041c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 846441627 1250 846440377 846440383
    0x2d0f050a1d190920070203120702010c0c0b0315040902010c030e0102160807090e15070807050903010e0c0109090204050d0809040617030d0b060c0d082d0a0e0d14030405 74
    0x1a0140e0100e04aa203640c0c0303038180c004041e261041c61005a0105440c4d8668084504a0b84c0b00c1303074090000c01410040f0b81d43d003641ca80005000b2410020800c108201142c0c0c0800504080c0070075000f0750f0768905080c48100311040c01c29256034012400c0c0b1000b0070151f85c0104145445a80504200d8441e20b95440100c0c21301c90510a10083d008420001050b0750400040e10000c1c0c0b41004000c00c02a050004020341d2010f103031114005c2916042c0003d03100740e11422a198110707045003801810034510038002801e440050a0008181e4084004a4555a880080c4000402192804501d40f03070178a000b00b16084240c0728054860100043c61482a441d551300c014014180b0140c1064480c05200a5545075030111014001d07490030510540c44529000301101e20540c528001058015401c000030f44604500410082c181d564041481048520001d600d0003130310b0a0703054007001480c1a40024003181e000b59400c0209a00c00000042502e030862900c1c004d80024002141e22991140780c0589 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 846442877 1250 846441627 846441649
    0x60507110115140301092a050603040b10051012050c040803130303031410032603280501080c01110a170702090f10090207032d0f050a1d 60
    0x200640c80c01402c0a065014580c010040c0c41e201c00c11210004890001c141c02d80d500000e0140c05912074403000c41c55132004400f62241c04604800400081e07075110002400381d0400c490580b090081402045503400a42039500c000e8201118208000c1a803604003c0488203107101c44d03034041d0398036000305000d400704006a0340100b01c080c040b2980d6504241c882321111050303102c1207001c2400c12a0403401c100d50403100078801d1484a102e020020f1441d140c5410b1003810151042035030040e071150300c1000e1f04150046100302c0ea06400101e9800d04c004242001d2420524611072403850880140031f40003010a0014030f00b242482c3c101c15140c6604d4403103040c5010600003e06081c400011011a541c1003405081c460307001302d560b03034002d80d1240c03005807480f04226181079000cad000e403500b0700842082d9406000b01c1c0d4024644456103c494200508290001c081000c0c610360001c038450407086c1d846a4801001c805503d4074500380507100c04090141e244414102d5103903403440100d1a21034890607107101d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 846444127 1250 846442877 846442907
    0x90f0a03150e1f0c081b090405040809040908040f0605181203120a06051c0203070501050f0708030c0403021c0b0601140d05150a120308010e041a0403020606040612030c060507 77
    0x107001905600d210710001c201d01c829440201d00e0b01c01c0096030313013007602d040c0f0b0b061b1580ca54a01440c1030440c000701b1005120003070080b2110031040c06841d0980d11140b01e0100c03158854400290f50710b0500407810b5401e15164060000c03c4010080d14003c050090300c00d000c4040152000d510040c1c03000010f905601440071000b02e21200a003c100e205625034004c04100d5409036010b18201c80581103a8000c4150304a019405a000e42400c200c9e40d48a04000c0c0100c400b0114214203026048d1b0b0f402105038009e592210620030003050920961428205140746044a104d01401c40c645a90700d54400d020020305003030511184840ca540c003103d403c0202c606003031041e0340400562601441b4491041d12902c0407500401400d0800302e06d1030b52541318051000c1d00b40d103e00405a2a01c101d0125034100148111303001c5404d004a148154807012200340182c0c800c1c1c015003000d01d0074900348000c483c1c4039441382602c1054a15104003113a0401910480307250001c00c003045661302d2050a40361291014614 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 846445377 1250 846444127 846444163
    0x816050705030d090306060e09031b03130603090606050d0b0c07020d02040f0507080901060b0f0702040b090108030417070302130c020c10051c0506010504051009050a0b090f0a03150e 80
    0x43e03c10241c3c0840003000741c07071041c1c2041005e0f0341c4070304213000509401c482002e115401041340d181c80f44081c1c4810b1320003041d400d0403a49895000c83300c03803180024642c0100c0109403148540c600b00003203409950007800c4141c8001030124056105c07030040040240035400650340002d503410542d118204501583c540107081406078a640d0403110008103022144080000c1ca4100410082e000600a0600320780c9841742e804d0402404072407284040c0d1004400300d911075030783c4c501b851140e1540092140240a100040c2d41c840e0b180015241c407801d90004181d0558100c00d0382807005070f0b584200301e00c40000300040003400031460241640341003051a01c07aa4464084a103800040742d03c0801880c0d01e81d6802c10b0911040e40c2c0c981c00d01d00765401501c80303c1c0815001d000503c19400c0443e58000e0014103450900401540e91740030403e100300c90740042114110008024070075003011541c102e61200300b9a5020034040c079580711010241d201c10303040e01000c4c3d2203044414501104000c00c8040110420781e03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 846446627 1250 846445377 846445393
    0x70e09032a0c0d0b0a0506370915081605090f0a09021806030d05040509060d0f0b01080a0201030c0c02130209060405040204150f080108060403080a06081c09090603081605070503 78
    0xc001c3c03114211780300c01d0100c6c1400005601030515400d116600c0040080d61000c203013200340e89104c07460307004440200305500d500d0300103200c2c0c10318040c100e0b0400702841500c0c013050402c60360030704005107107241c4452070b019460208000c5c1c840040641d404100c40300c0d4001c65132250110040902081440690b00103043c0000e840c4900f10301c10841c0c0119011800c480018420010030743c1c89002d217104581d48065064001045400c0003d03d250075548500118401c80f80700e50b56540f04d188003030f000000c1e2640074884160441d601031040300708180160400011841240e80042e031003400e03250821090940116440d8903a07121001a10050b1100500c10b540303440c1c9481076604581c0c07081002d540041c00d403200c1c02225900806036141070350855000390070241c1d110f4900351408074000c1c11801c17a060b40c6070400584030701d05200980d201e040c40c2c03446915180d8180350040c501041504500c445914010080000030650000c607460700c000f002400c1d801400d941000350408a0650289d90540200b00e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 846447877 1250 846446627 846446633
    0x70e1002070519081504080702090906160c1e0615080c090a0e100b0315011403070806240a030204020334050d05100b0408070e09032a0c0d 61
    0x14800041c0c070b0040d54143d14004160fa44418a005640b01c1c4900e5a005044003c550242882d074080e4418000c591052070541d60398041802020300721896060b54000c0303014003084d12011181c0020041051600d001c40104507210302075000602c15003940c00c03480c0030001208201c80c0d504200e030380c4004008818050b42d5110406612003018041e80d510170146200000c45602403841001d59103400e09c030040014a11002400c0300a28444001c9649441004c085100421782c031250213020300100c845001d0322040003828149051201c0c3c00c0f1401d96048441040100041c0f01d2807048900241a841c0401d0400d81c000b20780000010b409c046d401134000800c01403032302c3c1c962072140d03140048070b00341c0415400000c680344408400c5001c41e00024404007c07070008010903801c60390b004081384403010107a0780e5861030848141d00503441861281c0080303404102182010307024580c4048080c01840ca45910280d828103101d56072912a001c480d00d000240502440400c1040c1e0004400b80c42034442c0c080500b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 846449127 1250 846447877 846447883
    0x1080a2c0312091c0c030e04021602012d0e010c20030f0a02090c030a1e1b0305060604090915090302011d03130e0c07051b03070e1003030305070e1002 66
    0x2d034601c88040c19401c04252491070000d102ca50000c105424070710314215407601240d86060341c140c154200300380005040f0b07466403648010030051110b01c1000d98020303a44c6c4005482001c0d4412044400c540503184011450030b012030300e8030749190f20700e021000c4110440058801000c4007401900d0007010100b4101580d01840c46401c2c030f1407045040300d0001002901c400e0340c40495000094001000101040c05122050080d40d046101248045240160145000c1c40d0310b0950340325012041d101d1130300031042172985501000c131154500d4107000524121001c6540d46c404d6104051460350b81c0d2084e0b00c00d0040100314000901840d644c1400320044906009005e4141040304c080482c422400720003000340000211072250580d00454030b503640c40c0040c540031240c0c009040400400041044c81c00042c0140880f041021002007814a100100b0b400d040c5401455000803104110744424002141681d4003801b04503985458085100c0e91207030000c48034420029542c1d0b0b00300c0c903856080e001c40e98000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 846450377 1250 846449127 846449137
    0xe07030c050109290702040615030b0f060a0c08070807050d0806031b03061305010230090c0315071701150f02060118150308040b040806060f01080a2c03 67
    0x90ba03c1103000b5441d80c0518080b10703004691802051840050b00c200c0168200103072420f0750005000041c01c80d0303501c48008a114a8003c10000207a60328060b40c47e506e04805106c0c15a14203946480c1415203220003c6c2c00782d0100080a01803802c0401c2e480c007009401421903049a81c4282581e85800f64000042c0903200b0544030300c0c2c4a402041c1c07002e115160006c8078420984e070010020101a11140e03801054500d0444041c0c2d00d41d5005c0108540340035140400012a001c98400c064141c850f040015032985000341c00e840d41c5811400003610140d070300041310444030000030840c11030307501c0d078400640c0d900310004691800c0c239840000000c0d0109072903a40860030040c9880d41c0c518840b0400080740c44010074010b120030b4a030044400d044007890341d4080b14036020204402500140c03640c035040d000341c0169204a0140c01c0c000350a0245a6080c000c158020600b5142c107038400c82c5440000c0c10b559001000c8000183c0e4405107000c201b800340c025a20b41c0c2a943c0008803d031140220290380302e41c80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 846451627 1250 846450377 846450379
    0x712140d0f1716051605160503070f060206043503041b0b04061809020301090b12030703050d02090418030f0e03060f1b1c020712110a02010806040e07030c05 69
    0x15003a40c0006524060703a940d03200e90944800c4607030100700f43d081a581c541081d114050a04004030007500040c1007040714266103205c1002d641d0440b490402018035202e1660070181d000d17242001c040008540000341075030481c1c0d0000e00c844a0484443c0151170000d0b0010484030320303122104100060b240c80704001c40c007550007031030480e18801001d0341c407203201d04651069600460b8208801c00560740b1400681c0000500f03810101e4007240d440c5880c0f0309076082a00320490580d5107003181e400030300c1d1a0510110785000d002c0650700b021a00c3e20060f121f805040240039082c0e0300094210030994030f9620030180d1901264041c444080d107410001e0841d8441c41d080408a03684231203041041c1b030000703003103440b90711458540c10250781e0351400d081080d00e040480e0b0113500f4080c03000c5180e100501c07517589030303074107074510010380b100384504082d90181c04c0404184140030010700001a00c04011508803021502800d0410303007620b51802250052030003640310411405102004400c01021080c040200c0344 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 846452877 1250 846451627 846451637
    0x1914180a1d0c03100507170414160b250b040303090c0803040b030412020c09180d0c02010c0f020613120209010b0f0a0e0316030318080d020712140d0f 66
    0x168038090701d40e481001d580000d42c540d03c000c03121404080203400050b480282c2c2c0c540740010307401150b0b40411020003918122943d482c0c034030000c90561801c200581c0c1c0004900340d20391a20385403038402c140c0e81c41441c80002428200c810305003503e20000b090107025aa00100800702840c00e81001001040011401c4400540a17035000070382c00c1000003560265002240c0c01031650b1140c1d510b5001023900c5100800070350043c2c08101c0026940c64008a1082240c038081c280c20351009c071540303402d000b5844104400c0c0014014410301503603000c6418415a0741c080c9803140c0948450001170820300800103003440034450300001040e0b0171500c461400e031041c4252050115640c0b40c00540003280540c6c0c940d01d40c050014400e40040600c1603d02d841031503409020f4074101248880603e015005680054000c100b040f001000504691340048005002c0f21018103c004001c100003501d40d0060312031440495408580c030340522502c0003612080c1805102102c1c1c64840100010b841c40c04810716401c0819 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 846454127 1250 846452877 846452921
    0xa030603200316051810030c1d01060305040b06240c0c01140a080f040309080307080702030c030a030f1d061917060319050c04291914180a 61
    0x80041d110710300c282c484c000c0c01e10407400c2c00300c0101c80c501140244143c0d07540340b202c01c00001180c80c0814000113818041841d21005c030b00000b0842401906a00030020103140c0340405c8085035181042d160007060444054110441e040c940c1c998000b804980a0207101e40050180b042c070b07100041c086543d62003070325100c0407050155101c40990060301e04c0140855076510000d1000111441001e501a100342880340009448100345840d60b00a047c0481e0001000036918042d890100045407401408a00911071503885540c000e050b1516480c204c0d051000015421604040c8483c2c80a92541c015010544940a900c1c0550001712072140d0040410340c003220324103030340742c29507030359441010080c004203507c541e000c0340d54402005019042d1264015194401c0d895610741c000c00645806449075a4401c020b86191070801c0200c0c015207500c10701c020b0301d4810980c183c0f409003074100c9180e03855041a1f075403a01c0c04100e6079105000d9055004142c003003048a1704209903c10f806d5800342c000080510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 846455377 1250 846454127 846454153
    0xb04050c0406030623060a140f0d050901020a0e0613120507091b0e063402090601021501090510030b0f100f0605070213110408010203011503200a0306032003 69
    0x20400802017000308042d040310041940c2007000040c80307000b01614202c40c0f5203010100002ca660445c4550390071140c0002a026580b44450046d0f039003046826000f10301e08191a00044e01d801c80180c01c960250340f02050601103d6030262503140281500a0320500c405c4107403403da6103030704850260b25402071801001003043e0154a0040e070354800c035602d66034400000c000c200807494000e4041103180c1d0380620320700000c1250040c25064004038003d001c3c030160465104120005400410007030465018208140d498050300781e001d030460b01240700000321526424004000ca00b2160000b07401c0d03440b07160512091002810701e252199445c050403c2c420b64891041c0f03141030b019031040ca80014414841d480261409903214480307011201800500c501c41c00440d1580340e0015441035416960100040111040844904680ca6550710302040101000c000896951a10040021000078085070080300d032030003a40a44040c54000c0000c8181200c1c440c03003d6041460a000c003130080c000c6064002c29 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 846456627 1250 846455377 846455399
    0x20a09090b2406040b180a060c030206220b0a020906030403021606020303060915130c020c1305010b1207050c060a091a07211401060806011805130e010b04050c04060306 74
    0x850000c01072843d00345822031a00494000303d4005440780c0ca480481821b81c0ea030b150000000340155284c58090740d05078100a8181080101100121034000d055044411208d0a0780b0f600c00d5804408600c0c0e54449001803030007405510002a0001400014801895000207001c5e0000040400b0300206c8da4841c00120f03140c4c0029074000d60007002d840c000c031792950400603980540d90b00242a00c1000c004c01580f01040d21004032207000580c1102000985504107844501c89490f41c01e00244587c2d4035140219010707220743d401403000140381d0f2001c1f508851060080b100087c918030216081e5080c9908224024026244115a00140d4440401c080c0c100001c00c140710781e40c241c0b6101d0880b10040c1c150003a1065084003110b00c2a95102d082081802c1680424003a00312560307000090300d4a440050100103c81c41240d070802c841d468104801d81d50085040e070400b6102c000400e0183d00c15000350301401899801d00d601908020801c9844208200508100c0780b5994092140316544d0030350740f0f2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 846457877 1250 846456627 846456691
    0xa0b01180605010507060b0f030a0312180f06090510020301030b06091e07210504080903012003160329030c0103020a02071203050c030f0405030d08130f020a09090b 72
    0x1010460901c170b4140411125804100d44a0015010700c0c01c07803107107000084c1420700b0349100314003040b401c00c0004071714078030740c030070605030030a41a1020406c588944940c0018100c02800400c0e058403520038030201f1500b8450030f00b06410003079003075403a961a07203441c41c0091000c032400ca0040300b40c4ad0000b41c0b4004c01c0000b6183e080360030b4a0140c01a10b070316034112404d80301c0500d0408081c031811000d5000400c80d02c12540300c1c2d401245055122a802c00805003521401a424007000704805602482d40b003084007205c0d04481e11004050b080c004560068010b010032442042c2032040b1068150888203040803a0b4541800807030a1351000d640702c0c00150102e00407a4090030040e0f0000380240300c440d21900d0002d04031070013401c0003802c2428a034012403855002003540d484648000c0b8040207542001c00c4450741022860a1618840c13811840002541d20710030b034080d264940c818900c034155110030301c000c4050b00103c03000340805001402c01070044582510401d1054580314403660741113082c4041c0303034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 846459127 1250 846457877 846457879
    0x406120c0c020f01020f0a050a0c0e0103030f0e01020a120806010206280b060d061203020601060203040308120402010e093d030212010b2e0306060f030e0f0a0b01180605 74
    0x1c200c03440e164082c48500580d1100080c10342c4034503114805669020022080c800384510000d240e020307140c1c60b0603c40c5150039132240d402c07100e0780c80c01840080e4002c60035600000302440d10480c02144200101d00d442d0711164050100401c03550b60480059000700b0b410b120700c81c00e0302243c14a84548183c0740380041c83c8441c0850341051054541d0203004950480e828006000305224102802d40891030122070319075002d0390480703100441075000c040e010700020f0300610050000c0d500b450700d5921004010f106002c010015031064000045c00c5a0040410002c0f42c0700c06840300c455480c00881440410101c02c800740d081901c10b24032042809035840421032201182800c0d80040ca01e55806e210744440c0c12002007046540320100a86151610743c0344222030304260050028490030004114207075421684150105414030a0074010300380c01a0345c640710482246000645c41c43c3da46030090500401709030700d04d080e00495120f1420b00064469045c10303501c1004288001100910300345040b40e40c648030321 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 846460377 1250 846459127 846459137
    0x506030601060509060f0702090f0103140a020a0302010c050a121808030f0412151505090c030609011701020705031303030f02060f0403030207020f031005070207150e0d0602041a0406120c 82
    0x284085003800f0014100b60000418140c7c1803804640c00186131490403688401d1038032003400100180b05440310385c40240c584120241c512442d5940115034041c02d6804041d042c0141c001c0c4080410100b040180c0e6510380003028a42040b104034401405038104a031265607002e105440420304040c040100d4043d104500348051416240442c0090b0500c0783d08020303200e0080d1085000540302c142d00841007600140359148441c82e040c10b0400241a0b8007510860f4200b00074401c000075902e0f013044190545801000750082c6c1ca68460005029220f150303c010034034080400c0c1c0324150903880341c8540a4901c80e031a00351012004410480e5950421640d14498000c888082004603000c0e038001d05110f4005800b500054480c00046840c082602040c0c0640c2580c420030014000e034148500710182440c009050078540d82108000e00002c0c403403085601c107400381701401040110380c0d412900100034000342c45903505808d410308460340d041403081b030001c0f4105408421480d0081d100306948242d4030b80359 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 846461627 1250 846460377 846460387
    0x7082e0509010908040b091c02031024030f020a05060c100b0a120b0601030608030f091c060c0c05060a0203061c030c0503130807090c080c0d06052205060306010605 72
    0x4540054000078020034065561150000c0100e040790004001610400e4900c5559000310000d102801c050980740c40c25096240d01c0100059a01040a1201d80c0b000480800e600c0004200c0c0d264039114468042e000921509001003044850300c8086034542c001c54016031100e503100140030180c4640045112160420b112038218402c8541c0000009074010304a08403030340d1103081845103000c10328000d84840004004001044d80e00d801190050a0310001075410030422401a094034080c00003103d10603120905601c00da25505102440031b190006400d001c1001c0c0d03844003901018000005842a000740000158008072a008481c05441c0107810b000202c615003021184002d000c01044040201c001018004110100003520b0032010421310002028a0025180c0c034101c0c0325486251410304020140c007079070790000162a8003507002c51031141c0e50205031420314020305058001c940d21200060103140401c12030781c510b1020349101e40d41040325032070b40800c05940300b10911407680000c1c000c004c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 846462877 1250 846461627 846461713
    0x80f010213030b10050d150b010e030d0e01051e030405060f040b0c0304080c0d05090a0e01050901050108042d0c090515190f180c0903081608070f03020708 68
    0x81060b900001c000040c3c40350541700d10014104c20b00314601950405450054000ca2450700d1003414844a800d017420111035040e10046034647c500a80075400b404000b0300411440e901500032625000c2450280b00103400c00c021080c1d40ca40c206580c01e60740c40c82100009094405914500c074004d40d000201070869503292500000140d000400071034803503009000e41000040204000301c1020f01c0b03511416101c0e9614800e00c10076040700d501c550a41b4000e80010411330f1940507156054840a1a00c4196035a4a04209000000c6609400d40254503203480c00d080c140c5502440b40d60500c2940408881c0c0ea4400551041d2007055603800c40024a01c8984410b910303100816070200281642c0890300183d1320b110688507407601c0e6114500c0c2e40d0368040701503089802071003045100c0e00c03641007a60b02d040c2161901811401143c0302c207132040004051402c24401c040040e07940d62648804094242c00b5280f80094841c0007603c1611040e01c9002c00b1008840c41096180550600e111a48101c0b1a0300310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 846464127 1250 846462877 846462893
    0xb030a090809040203130323180d0206040905010e010e0601050d09031e081b040e040312060e0c09040b01031a01030203041119060210051b0d24080f01021303 69
    0xca021900c4031010030141005480d20b002540c4905540d010020f561052820050240c40b0007000c0b089546210f003110001400a580070703640115007070b0085000040c00f1501044031800c1e400d201035484000824005007072542130b00b042c1d060b103869040c4800d10f42d80c0d0340d82d0389541080035501103004c00d20038020581488a160710a041c07aa0017407811140407411405012a4540141c8258000500a000b04400514240241141c03103050841072464146800c501c11078440010b4001001c210a1000340c1c0c0c0c20403241c0d00004041e08000707251002d5804c1100514100d0390101c602540100c1c02d04a00040d50340c02031041c10840c466000154203100690b01c011002540000d10480d1040c0341c1e840203040c151a414039041e1280c1d00c0c5106540954200400a80340052290300031502c00d0506c0c042101e01d007001c001042d0344181e080c40c01900c8503981540724000e080700d903800c41c8042d031004401038004201548d01008651582054800c0c2041c4001c070542030307118004020303070b89034101c1a0401c0099104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 846465377 1250 846464127 846464141
    0x8010306180209130203011104030222021c0501240e041d01090501050910110d020c0f0a0503040513020906121015020a2a0b130306020408030a0215010b030a 69
    0x501400049039520b070b800503490000942e042048030080000c154110709092141c1241103840d000001d062500e1680020f1488018059464a0b12869a603e04860f00f5680544501c50307035920710381c002c42003000c1d150001480c2c24442d11055240300388150041400d1001126802620b07039072502050750501040c000900900490052450b08600f50b01e0450b040030f104085881d485000049054144411124903040c5200e000b001c01d1440c2c0b005e940205036412040b40c0d0030100702c040250319100545082801c0003101c0000e540b5034080d20200008000f008802403064603001c459402c99030051610801c01c90144a94a41e0051303400c01290b913652001c0b040b0207501c2441840f01c4251683c9030742d05146400900c190020140c4e01c804010000c101c2c504000c41c1040b44180a03400ca44445000d140c0c0180110f84aa0389004000258001030a02e00000b1640a99003015041d0350740e030341e00c441060740e031703407000c080b500060141e1390321041c10500108045040f43c4c400422282076850b68081d2000a1581c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 846466627 1250 846465377 846465401
    0x1e0f060312210610020c13090609030c0c1a09040b030f030a03090b0f150409140307030801030c0b07081c06032901170d0c020a241209020108010306 65
    0x200c9224a000c020030344020844000e038895042d41d910b40d190218a10080d014003600e2044c01c295010000041d80007480180d40202256403090b901c1020070054003c114084001d0890b5080442c18401c0c0344c0c100010304007443c480d030b0590f1102551000c90300000c41040c001c9500d1001c04002c040340310701c3e090b001160369102c002c091b200e03e071840000c040d1843d4490782c4043c0100e503d4564180170b010107611019407142c0141c2d02411986406881500c4046040071a540f0442c0d48020140602c8011101522500708410450750307501094100603001d06001d200440f003030425181d0116440f954030b403d41c0c0f140341e0310105c2c0078200030031a00030400303240700440e03000d01440c0d0751440000426100c6030140618503082010701c0f203074080541d1103041d07000c0c141c2003000c800e00310b1481f00008180014940240c0803841ca00142e0600c00c074400240c1c104039030f078041c9011400c4101c010740d415840d4404d00020482c00d0304e89040115070340d504801039800004004c2d01203645000104003007005a08045200e0f10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 846467877 1250 846466627 846466633
    0x5030a11040f1b030b090415050414030c1501080a05060f0415020f070b060102010b1c0f140114090609060708070c050a06060f1a04170307291e0f0603 66
    0x541c81070300e012284030310708541c00d001c045001d085034160144a17643d251035050f140517002c0e261035140e5a00004003058221ba141d076441c0300060510120361100203218500405480e0399888002405540e10504203c4181e1030341e540000141150b00098510a207650081c00380c001076550300c01d500c00803007004200742c0b412803a03040602d50b141904d1004020801000610540751007840c28140b41c4c0c070b200100b516056a01d04189604d0720750320b126210180700080d81004503821042d00d0300303104030084400e0081801c48400994032090f001074104039504649512042040c0d5141040e5682d500401c0d0781d0400c50b60480705c040303414a4841e103040f1740d00c103026041045000c1d40586daa503183c01051041682c1c4543e4808041c030030283c40401200050004019030002030248916006c01d502c114460101240310354582502603840c20f2081e00c0d8041c3e009203850204a4030030401c250240600d91541d40080300f80070004070120700601d00300001344030300c2d0040c144940e01c0600b61001c000014180c00d60500c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 846469127 1250 846467877 846467891
    0xe0706030207032015070201051504240b070210140702010807140c061f030510240314012009010c050c043b03070305180a090902030d050405030a1104 66
    0x88405445012213580980140308025000441482100004c0d120004590408050140c0c800d0207080c1d507000c0740000c5070005101c8150300f17994150800c072a50080610700c02d0311000994082e01c00040c144443c002c0d102940300c00c0c8014002c031852400c0000e1014028400d0010304003652041d03001c5a8081a0b608080501903000b80445115400014106100703600840411031000c0c821140d0354541400c401060f41c0307145c1956115600c0c0c1041e2441c0100141c0d90703812480c1400c50b0340007003030011280c8520400ca4503443c1d04201c50f9000c1d03010b0256841d5824030b4141301c0d0a12400061b01d00490901303198500f40b07103115004541d1410b04900a0302c1c1849034820740380460780c1d24454200301942d881d600064582c0100910f0810b035212614621005802c01c5154503d48000b2080310101d030307030501e01159203a0f45a14420011190210216041405d811020803030b5003032a4030881081d40220200c50291010307810456103481507014080c0c140d08098892000206083c4030b00900d004000c0c0080341030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 846470377 1250 846469127 846469157
    0xc040612060905090f0f06010b070311190f12410f130e040f080310090f050a050f33090a062c070806030a150213090e070603020703 58
    0x39841c00d84d00d140554002c01840a01e0480800015140c1e184107070103444558907043c5810705030300410f0790140900c0804014804184d03000d000c1401c0f41d007a0701c85840c0d42268582001802c00700700c44401c850000f011145485114080d480900d10f03244c4096171460050b9651178000141e0092580c4941c0004000352421a422076000240590408218206817202100045c41e81581e40c0c940c0120000d6544034240804186070b04020458541c0062800d0380c2d0751a4031103030404015455116240035442e20786400d08070300b42d540050303003d000c1c600014092030300c40280311401a8000d48a20300d0085101003a2100c440d03100c0321031000c1000d1f822109450816040110358120700031540842c1c0c55681e00000d1010000340c501c0c03102d440c100c0d00e009a0b0041c450b003002400003800504140f007840007880024900740d44c10812404425404040c4164030315070319107500047d420402c0101e000980c01c0300041520701d0503200710307a451010100240b215a11308042a0000e5010000650801c024400c04c0090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 846471627 1250 846470377 846470381
    0x201140114030d0503010509041b1e09320a020d020418110c06040b06060904020c0606040b0402160602090619170a0b0f090c1c02040f06080c0406120609 67
    0x800700000d00c0307208034805104050800c0e40040f000c80a120003403006000caa2281c564141e030155010714003094188441c05104c5a02c4960b600801e06076414101031071000340843c1000d401c4400081045c000400d1502429000164441c0401a5602c60b11540602c003011160501c0c1c0090b010000185080c104d03001150070303684190412000c0341d00300c00b09079092402c04d11030800400b081120546c1400c20000e001c03502e80341c0241024001103c65008a445c03591072608035140e072040240219903032485108101c2d290001101c0051069180541d8014581000c4c02200ca20a403e4410510600026640d4200030f410025041e41c003d0414820a5458040d44200d4036400004e0380341c803903884e401400201c01003500145041d40c898182490700b00c0c00c0d1682000c0b020141e42c02c03180c80c7c8003680c91415441d91400341000c80440d9203080301c80d14244194942c0144152040809010041c588994041e51043c005030317642c0c07550700307800c000404c41f60344901074840230340b1103c1e138010450b81d0b943c07c03401d01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 846472877 1250 846471627 846471629
    0x1b080609100b0c0f070801050f010b1c1b02010c021606031e14041b2418090c2d050f0d1109040b0a060e0f040b090c030f010e2502011401 60
    0x70140e13114003044084000100844002030248400a21480c13818111560850106210f01051140040340300420940d900780d0121003170310b40c0c0d41c0404c0402c41c0580141c681c00c0642c0310640140d4a4101c00d018003502c00301d00c9407602c1c81507400040c00d092508404800605840e481d00140a803500c400d84000e0141e400740c00c0001c0801c3c516a0f5181c100381c18060120303c480c0000903a00103180500300401c81c0700c11181c0e5102c1040460440d4400090441542c10a003141e110390195400c1d0040820506026480540c0000f2650340d24500171044245c0041084203107109004e80030301300c20907610120311440c01480a4200501c9a03418450000c1c0b1440a0710044c6039404400e02001c5000d14103802c2c00e02c50040c80740d8045400424283ca40784001d03140001030a0854044c1200f610000c080386c1391900216a01c801c09801541f251518403d03031152500b09039030181d400070b90400009170351035030004003e00400c01149582210361344000121303132840803451180295500d4a6982e6212034248100d14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 846474127 1250 846472877 846472897
    0x60f0b1c0f021c051501081207081303140c03061003060905161508070302070b06060d0216060507020c0a03031d01090b0a020105220f060e15010b070302011b080609100b 74
    0x10f000c02005161030b60400a103800f090240c090704100401244000080c900c41e440d9494808594a8516003009500380c410b60005800001d4001000420403084401005c80d6541590036200b00b500700384101902c0d000142e95a64036101034140c10720200c0c0071580913024092244e012950160b0041c10400c412440580c4144281d001140b500000c903504504d881d0760101c80b03407070f0071860400703507544001d1400c0c00541300e503004003800f085c641181e65041e412190f8441b140b85480e91203c60740d24003172003d0441221400014010788500c0705003402d045040070240c1e0742c1610740c000d22049000e03001d080c0d409030707250107410451200c400082d84510074000f801d00340301680c0081070a01d13000c100c080300d650700000042c000e030404000d6040032940c8540e1005560340c1c041404901812490308e4249440707103100c6030f410858417110000940108050051041c2071003900240010401981001d280040d07407546980401d0000c400140b00d481e00044883d0301850070401c1081d9181c5507100a1410f40180c1c50036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 846475377 1250 846474127 846474169
    0x703051e0d0908031813020f07051009050304120206071a1b0309030405060d0b032e0203010501080f0604060f08030a03110307020309060a0e060f030103060f0b1c0f02 73
    0x552100034041e4500c420307440d0030a0741c60545040307650360381c0f0300c2207021011030002102c1c60140d0700d59a50605803048400880c06648400d95a0a2040c2c2daa0080700d080b503580c0309103244807002000074003490501e02d0300400a075041038542085805a104845022680628200080790000709589028000444103500400311483c056040d202c40c0400e18841945508041c4104040110000111010303240c09407040c94a40b90f581c030903070000e4110010000e6041c040d205111014020b000c4104007254400c903041031400030307207001800480c4028020b00340080e43e514001854031000f038550320303004000070b8400282035943d9500c00000c008541c03c1228a03030000202200165810b01030203000c10b1841702d030b46145040000010396244030b50040d0602400b000700f03102d2482c6010302c0030440003080140c1010b550700241d40e81c480b0300754401d010031288140b41c0344040c29110603034410409824006002a410038070301c0da04900300503401e6a0b081322900b170000c92900058444180c03108141a80b07483c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 846476627 1250 846475377 846475423
    0x507230414092a0d05030915030f010b1306050924040602160e040f02031614040606030207032a0501020c0d080f090309010804110d2d0803060f0102070305 68
    0x4a5003880c201c082142030311500450032807409901410705050383c0b0822070f20144188181e1600e5421030041314030f0f5581c0301028172801c60100e505040118840d040c000c0000503075a132942c6280c0082d02810a0380c41031208000b405010050083c0010301048a009040b041c030884c5030361696124104901a00840d0500031800300b24180d0108190308441401c1d292802000b0f0620070450810407000f03201805240040f5418015920280700005d00740c20014894180140c0741c2c0340c1c90707101c61491b29003103005034074101c0d000070914401d2090345c1c41c07141d0554800c0820242c22801c07020480c0c250380d204070702102c0b05040c00c00044007440200034502d0114042c1400c4102c6035030142107078074001c01015080c00300204001105001100310740d43c4500908182d411070315a41400305d03265080005d0160443d0700c6210040a104000c90050003a810f402c0c411524040310b516070301030001d0310000c018a01941400824101d107891840344070301040c1841100d50080e5291070f120314001080155040c5183c11040f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 846477877 1250 846476627 846476641
    0x120f02010c141e09060a02010b0a0b21090102040504020739090c1e120501090b010c060e030d1d06010501050702060a080703241706040507230414 64
    0x70151034141c0ca0030314001818407503410300380a1044800c200d00c2e00d24400c042e200c03a15400001e43c1c00018000d0b0480d51607109000029000300780e40d04086114041c81c8000007201049201121009400303003140e482c06004407070403800c2c0707003034040c02e9640b180d5028000420703039845070320140c900d09016421015006000b06640071408560000b10b00c800e000f0741c241a400380103c110b9070301c211041d040001a02559119080324500c403825031035103800381100c403441e100903803040c800620402c2002c420049070741d031010b898007103960000099000c9440a01c4d54008103985501c0340c021002c0800a480c5000300c142201710440c0d00580c9500d182d120700c0e000300d50f4400c400b0446140541401e0a00f00c0c94942e0702d4000480a0080009000400c140d000006100d640310344c00c840c5041c3c044903c48030705004818000c8481400f14010603100d10340d09500002c00002c00603010740181e810802034040203007050950040040c0311901008020f0403a02d01810540f15403042e400d4402c0103154a0040d41484c103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 846479127 1250 846477877 846477881
    0x240d02010c062412170d0609020706230106210f050106031b0903030203070803041433060a05010507140d050703030b01030b0915030111120f010506030408041e03120f0201 75
    0x10700201034400c1c080c5030980020302c440d03600521000c21702410301d40300c04c40940514082d0500e50480000c45001040e00010001c4c1070f04010031074030b00004420444e6032400d142160f0003209103d050002980e4800d00f2001c04090902070311548450080410100141541502a03510a03800f40c0d0000c0c2d0790300c200100c00c0092560141038145c05140c01c3c0740721b900d5500d000f035490040e0300d0080c0c812440013011600b0070840b01130f0099284202016140031601704007020301003038001c210241010101010b01142d14100e00c603031910980000b8403c4005900b494011103264114410895213414020410703080d80c10104400c460000450313544968030350503490014244d8500f910101d05060402e00400201e903114005180c0c05420a040f48a150325007900281c0580001100c4556500d00041d81c084510345501500d8030400c54488031800f281d0784c4206009451104450151001809000074418544080c407913810b24032403508003c14103a1280c0342c0d0041011581c80140102d8441e62201c80c82c59028 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 846480377 1250 846479127 846479129
    0x1b0109050d0f0203040f05040b01030209040c091e12080708130b0406170f130516030803010302040e0c13020d1b05070605060301060510030e1e07030b240d02010c0624 73
    0x60f03c059410103242c00e4a80078060070b2405014403e40c2c40d0010b81740e45903c030381d05982007440010001d00a241d00740700c0140150707070907008128002c40b96030f40800b040c845e800c40d0a0b040325071410480174803600540740c01c00e040c1c00644040380d4007034003040208071040d8591284e4003d401440d0405650714604003000e003401502a03102246070300349104202c400c0c3c4a407100560b21146c50002003c0141c424038101d07040c00110340384c64000f46403c000c0401440050b0000d1030583c0e1094030100301028038054015903480c00103c0043e0300403524a01001c1c14409038005d8054141442c5002c120488100b840c09000c842c1c003880000040c4002ca02d101c00d20030203004480d04000140c00070000d480c01c090120344540038188450081c10344400418030414020402003006009038081d180e500b410020503562140301900c002d403900040b60000c20810440081302c20140c405540d80082250440003d00012035100c840607030600c807404217010040b929501425004040c0c200c0c1c000c0c0701c0d1040d80801110b0345c000d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 846481627 1250 846480377 846480407
    0x1302040e060a0507021c0e0103060f06050414033f21100b030a0c23040e01060f1b08070b0a050106141207030510120b0709050609151b0109050d 63
    0x80f5001394030030483e01c07124018070000302e41f400e0042d032002e9000580282845034403050480340c148d080024032591000182098804c2801090284030300c6108060b80e65402854410b04c0074040100a8400841c01842417411029170034041200c3e2011001000550401a220700004242c0c00580813075180103071110f03500821b810f580c44511400c0c1099050a03000050038203105039500c0d105200040d01964030f242600e04802e50314000404000c40064103071700103109d102001ca06000010400502545128a80341c00c03580c0c401c0c03c002c0c00d000c06004080502c01c000d84500c80d0412112010513003510601c0d1041004042c0440d00e54584103008042d03854000c2d4210107100280880000b0042455019400040074903000c9030540381c00410144140b0690b000040080c0c0351104441004021003800e8440d90036a150030f0070860b0340320184075241c031807060540e91105c5100d500408220403603000e0180326002c0303500194880081000142181c01c003900507603240e4040c1401a0312213134040040ba070720040c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 846482877 1250 846481627 846481633
    0x10501030b39040320030607050f2b2f0702010203070803090c0603041b270906060b0c030405040b1516170f090907050418051302040e060a050702 64
    0xc582e5107034500c52100840c006107640550030710342500340d2030501075501454100e8141e81041e64583c440448003010454840e01134024400051344007406402a103004407004401685000003903d03c800040905119100c0b04007a000c0c0a02c2e0002c0d00c5200384006091401c0c0e00311403c84404c1e42480010105214520341c0d85000c0090b5801070f40d0100c02e54041542c403811054036070301c615440d00d0800a1094010b60054400b104010520100304603c206100c00d030350003526096140c02e0558413001403802c1ca132050724401032000381c01c11000e6120304401c6000300d2001a20507201d08252201d90301a50404519520225040c4030b50b240038410300c83c22450449c0e410600014031200028240190820301046d501300c00804030a006c0d50007030f8070302d11400324060b1960b82c40700584e0b0760000d50025040d89000d00300d0000000c0c1000d00440c1210255642e010b240001b4641c9450700c03001800d8000c10b01081c04c0001020040107031224090170340c078550350300c0180000b032a02000650031148010a4041154 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 846484127 1250 846482877 846482911
    0x415050711030d0e04020903010f0203161106060901061220040504060e010501091205190803150d08030c1303020a0b0406020d030b09040311030712021b030f0c1014070302010501030b 80
    0x113401203a80307080300340b0a41700036880d001420f0010303004101540c1c00800180c0008200300301c2e070720001c03c41c00c03006069072140311441031543c0d911940e034401150702d02e8010721802c006000300340c000e02401c0c0c501c0030ba2000104015480d0820182912400211410418000304d81440a03242c98041c403000f81c12500000e541c80c0d0716000000f0203403005880b6919071003141e4030141083c8a814000c800c001ca01346a840e19680c550761a28081c160f100720307010307442c1c0341d8255141d0907245840b03100b08800e0758101c4401401e540f1240c1c0f0324216a0300074401050000c42c507020000040c0c8544d082140140600099184c8852078120007a0801011148801c205480d0000305c001c03039501c20742040d402641524040d80c01c1c4d0100c0b2081803a510901c1e4002c2d1014030441c0c444161594009945010101744030307030002a001800c000e05645152601002042c3d400103400d0071070343e051081c403107981c050391460518885000982d00e522a6841580151b0050751a1001031040c030040c00162074111202c102e10300a03c0d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 846485377 1250 846484127 846484153
    0xb0f0a0207050703320a080f120103081b030703081611060c0304030906050a0f2316050d03110d0c0207050904151505060d0c110d081602010b0d0308060303041505071103 74
    0x10f42101c0d00c02408004041102d40700a0744200952707968101110311001156100c1c180718405800c5150b100b803c180c2c004860a650110120a4400c0540c3c55202c04520703032202c07140001d030180c030241060200f0540c2444107016034020809180915940329404d41d40742000e0030010a08213194000e0000e12408204510785036500c0300c000038440402d49811071002c1101c20541e401c10345041c0900700c0c07507240898500c200742041c0f0803801c3c5041c03040040f03c100d0b1480c014142c05440c0c0007651000042001d100040031101960004004500c180c41610705030303500c9900181005105507000c1d42d89211035078500110a58522a18020302a251b070481d01c424034100c0012154881c1c0d01d4030b442003d8032040c0381080da0340030309401c03114a00c1c120b00751003e50b44c40c12802008601c00712000091a0600d03d003045034580180300740e06c44014054021265078080d610162402400501855010300c010000002c0f4800300702d160846501c0c480d603c4990710240390500e030380c80d0150b844500b403180d00540e10071524 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 846486627 1250 846485377 846485383
    0xa14041802090c0c030d2901022404060612050a060c05091005090307170f16080607260414060f07050d1802060c031e070b0f0a020705070332 62
    0x884140d00114980c0c48044c001028114051540a094060b05000e0030b015419904080c124410501171014001942035000481e543ca4526031480048104442951001d00450005d01d50042c0182d00200b240c581c0d03415141070f605040107096035907400c00007128040003031034050300c1c206247d04d181860401e00d00800140c00d44021101c0041448800120a0900d86003407028000506101c03080e40038600e0b00300c0c0150b03100d03203e20100a20358014600301451600300c0740c401c1c40a85500d07500900959075034400c1a150500800020079a0100b08074480f442010380c03401c0684214460300d0010110840c02d00058074140c000f92101d083c0c56210000c10a0440d40441a6101503140c040082005002d0402e07060751042102d4020350010300005100300141e10010040040e45500c10b440c041c1c007010614800583d01400310b00512000151010600f50700f01c5410017034200e1040c0100524040761a50380c1454910113a000304c0d4504100641800e085250501008000500310206164920f181c0c8004e51 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 846487877 1250 846486627 846486631
    0x1003140a05030a0305040f0209010306020415090b040b0333040e030705101a06030c09090603070b07030c030318060605031018120921110a0803270a1404180209 70
    0x3c1010360b04c1d000201404610985184220b4014000100a5031a410500007070342c41805075094588080d46000b41d2a4403d0701c0c0c00d800c40f034030528810708090414405003004e41c07001e04003d01c2d500300309484080281d030030b4101c2c454203a41070703281c00c6000000c80305003c1a210303400b22009080e0014047e060110300f0124000c9410701100000140301d42c0900710341d4030442c0f52070307001e160400340100c20000ca00b00030314010214002d046408408543d1501c04140d500c0d100d600032181c68820600180c000607000749914280c0e0392090602144d0160100140e02000c058004140d44454940104100b2030a051010300c9154501000500403290003e2000d410001e50020007400e00c041d010807001d08900c1014640060400d003a840000002400c2d05456140c151350415103104a01101d5004a8a0300b994940104d40c0e1401c00b45041014413060203002640541e0070303280c80c20000c0041c00147da910056000a818001d200d600311407200824441100c5218400e260803409400454016a0b81c05000030303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 846489127 1250 846487877 846487897
    0x20a0905040b1c06020408030a021e030304020121090204090f020109091104030305070203100e0a03020607261015021506040b0a0b070c081b2404060c0c0506031003140a0503 76
    0x18550321071500d0706138024400d0798801c0501d40401f06500c0c441e2640850200004040102e003e550690240c046070345910050707500902003140c0104142e006040c00140382c80c003889561000504942c5c0d500480c0580343c00c1070040310f4003100141700340c0840d80c000b070f4100c01400e070070320040008144109100b9100c0c491800040d0030303c2004140c2d071085582c100841b403c1004200f4003400601f411106c0b10f9990000300a044002d8000ca1000921261155940c510094042c5564003100889101220301c60080a04006942840c068020429201c03080c00f003040300e00780358010040304041441c0d40d60a0341d80038017070701c0c4142c0c01c2c0740c400d07881c6a81f02194039060310703900868940c2d03a2a85103004a040d0300c9542c004c070940e0041d4654026010b00340044000500c8041c1d0b003c040010502c0307203000700e0343c00c40102c0300c2c230b1802d092000340010b622641e446441148595181300005440c2c5000034050b4104544800c54405d50a50070b00400c0b0303c9040c1c1c4220400d4140003000e080751070703648890b101d010f41e501c0c0c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 846490377 1250 846489127 846489169
    0x412020624030c060f0306010207080f0303012c0907060e040905100b0a030501050106050d050601031808371403041718060a12050115231309020a0905040b 68
    0x41c0042d5805001050703c10b403000302101d6032080ca460200c10b41750001c440c480c1c05809902400940c2080100d0200e0a507803881d000b443c996802e000112aa04401818505039080d469a9403089120705070010350250401c400141b840510740b600c001c00911039801d03030500480c20068408000b800001c0d03141c0400017140c00105040c1450804034880c40d030b50382e2024166600b40400041c0d0b0f150020010140403a0103501805150348410054055a44c000120004820345250800100b1540740c09412110001002103181c009414441034000303d244e0070300040012074100c01c040043d085545c00c01c0c0c1880c80100b441c15850b064440c4000c03040600c0e440100090005480250340034040552000c02c00c004000700c2e1a0002c804004280565181009441d40c0c5400004141e028504d4050800d49200d940d904031028a04502501c0c1c0da55101c000310b140140602c29000516132440707406010b01080d2030b0040c1c40e80511080245180c0c0c3c0b6910807401545030001c02403490719000900c11101c0c0c000184 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 846491627 1250 846490377 846490441
    0x3030109021620090606071e02010210060e06090702070303050f0705070b040306050f25140909010612050a05061f020f01020d060305101b110715030504120206 70
    0x102d12200741e1044000300161070144440d001c0210f140b0805031003900540e1400b0040d0340340002d1210f18403400f14041d2419408949220254034030b905503600c1030b44184181c40354a103078892031009031030080e000040d51080000410505090049400d98807510132300c000c01c0c020b440d548028280e442a0500d0070b40410000860b90f0500a003044400001c0100040071665507a890514000801098032078a0440f11804081042da04a820090008000403040e0314011010180b0a41d030718861022100d8410000f48584151942c920b401c0e54000c0c9010b44601e907080009048850407502c0007400711142520b070030b084c04200e4442655030601c4065187c40710180d0518003a041e171400c004014210603542c0000340b0709400d0101c0782c200808891151048440350400c0c2c0d0040300640ea13240d411a02a4840c0e002d60100d100d200d404c0b00f2624400341c50a64490395280c4602c1d50b510381c80c00002c1008070703403640140010000805100e10070403401d84080c255500b085100c0d41c02c082c051030390b0038100001c2064 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 846492877 1250 846491627 846491647
    0x503040b150306070801080d020c1f2a03110d02060f07030e1c121a190f0815090a0506310c0314070b031308071e060c0f020303010902 59
    0x2520004078010200d544a240c204002000d0307500902405146000f1010f00516041c000203901450402c0100309a01a03500f81600000e609920103100e01080320709400d40c030541190748a000101da1002040080029003410040d003110394501340c200440c1d01201c5403800079036021950b035402444840340144242c98000c421005440d0540320382c1100d0095030072600454401d4a03500c5a04000c0351100c80c0030004109444080301e11f440e6020b50039100c03000c0400424604040c03070624245a2207071403607003143c95008a80756010300c0d07045020a41d00c1111000c0d6a0322203d410140c1c806030b10b4004040c500817a40d038140d1915800390006c00c0102c80f021443d08030000039001c0d011144a1180d094180d40414100800c1d82c1c0083d100503036040030840c1c0181c030310490200d83d10003500c0c031007074500c0d01d5074807031441040d00c4407694401a1500e40741888000005090306108101d80c1200180e584414042801c2043c02c4440920b000340900074065180c81409802006803811a5004800140c507500014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 846494127 1250 846492877 846492901
    0x50a051804230f0c1c0302060606090a1e0306200702040b0103240e0709050a14011b0807020907081608060316030b0a0614060403020d0c05041a03100902010503040b 72
    0x80b22056280c0600404803030180d8000401101c440012202c4652401034014581c074401010b50000d0010b030484e0780040c200c0d041a20080c031140070082c0840c1d11650781c8030740c2207401d100300c0c010204020040c98010000e00409000e40103614184200414008144240c0d2007054415002c00902070ba455203c11041d5038002e50000101c00c1c20ba80a500400e0700e11910b6025210082c01010030403912807012481c40c0c0c0c81861050305444018003c10b16050600b80c074002080e44081381c2d1410000e03640c82c4c0700180040800c4480e4801e2060415a0b2520010302c10000100e1300100003a0802003408100601400c80c900700ca107010382603081080c1d0302d4503080b0200707007000c0d0001114030284002c82c5e000800c105441080c0d9100786a20441040610740303a00391030344485401e0740030aa201c3c10502044c005880d0549a0704c01c618814461031071075560761000714095612416610110b0b414115160959050600c042c408680c40c030441008280819400a40b9900025201502194a1000103100020301e0b13 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 846495377 1250 846494127 846494183
    0x60406030515060a030f0f0c0c03050f28030c020a051b0a0f0e040b1f0306111b2112130302030d0f0603061a31090606050a051804 57
    0x291202d0356a070403000014002d1b042c12228980319600d00710031000000079601c26040c0c110700e1940c84504111642d1411202908000c984003101c41080010750808a0031020704114401c007508c4040c1c80010a00c400340441c1e00200501c015034012506550009002141d140d4080451050080e1180c0b000b6010880c0030318a0742249180d034000e0100480e0050780702c104c1c180f156100300c00d0010703181c0d907540c10801c1928080d0b140b01500c400f420014030000752103400c10700039207000d07402180c11301003464042e005180742000ae95519400400d40c1c0b80341200c615600e5000c001c09800900e00e040007505c00c1d0001640000c12640804440d0b1610104241c800d108451519804075030030301803444035080c0038000380018801110078618203031010580c030500c90400d68600c1c2d002001042c28081e004400e0388541d0040651030701c412414060400d650540d131180343d41550140000103100342c201000d0005190f1b80f5040301c1c2c8075025014203c158440b54540c402e901907440040244920031000f0305244117020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 846496627 1250 846495377 846495379
    0x3090608091e06040b090f0c0402160b18100b0f0d050f162c0a0e010e07030503130905010f090b153015150403081323060406030515 58
    0x9042d65020b40303100005503180510301410b1024003903140ca0401c5680c4e015002020f036226007004161006134500369014044603082c03440241505030055035007054000c4102c401c403c0c4c8a0709582c480403960303800c01400550702c00d008010080342c0f850100042100088a0029204070300d0bd03940d5030101704090002c0c41d0560010700444200f0b00580482554400150013448907451242054862000700d0000c0000550819003100207a42c0740e0410590250114111071310301992280102039200c0020084000118098400b9540314031020100c2c040414080d4041c80ca002d042c0b0740103015415540c00d2000072203541510000e003004800380442ca0010b00d00c40e00b008180e2001c01d80302400002011802c0d240140c1201604510b8070103400901181c070305442c148221081ca42890000b4103118080c1412401d501c0c03500e030f0a16503295a0381c00260300c002c0807a108e146808108001000040c500a00c10310b89540304000c0d0403014202140d0f0b140038a03c168400c05482c0e41c041142ca20310318112510100c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 846497877 1250 846496627 846496663
    0x907030602040b0309160e0103200a0602030a1b0b0718050d12020d0215011e03050d020705010207080705010f0e060c070602210f070209041e05070f0e040309060809 72
    0xe036841580c031941d007003101c8825440c0031b0812040035450000040006440f0640c00119070b40e420754998045800460104410404d600c0c4075940055503981310030380040000d94000c595480d2a00c0008002e0035500343d0081c6031114105840c0005010390060030b0b803242441c64400300c00b0507403183d80c0f0310108855000982292460700c001050143c0300045010074141602140c051016488040740d54004c401808203020090000600004a00031009140f50810040d004e44017512074079450b040c10981c0c004003025a021010030401c6517018007600c8001d0030100c1c040c0039401e24000c0040c1c03402c0001202c80041001c0c240303288280ea502c04c0180d5004010000448080c01e848190233580e070100c4804500c850420030028040300308a44c0210b540c400e682c82e200700d0a02003180d0900c17464140182086425a0380b11300c1d055061030314419100506030140d8001d0081501d02064100c1030740c0d82e80c009914104108040102081d040841101125440d15000c16940c1d604042c00c1c0c10441c920445e0100d503a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 846499127 1250 846497877 846497879
    0xb0402060421020111030c1c050c0303010f0509161403070306030f0c03060b03010b06070b1b07151415010e03070510050414061e0307030b0d051b040203130b090703060204 75
    0xc16450000b03110b41c0c1c405e0302e90006001c4100b072055a00e00840c001170010b64888102c091001725003052200380e242160410b1801d0004144425040d40c0090300070a031204c0f012041040755142511802d600801200c10f0744845080c440801000d58601d400d41003071900b40000862030151095204200841d04014414511802d070314150600c440c5511003031f1412400c21040001502d010310030000000402014145003110640c0c414a10b294010300780e0302c2c004c070021002c0304454208001804006d201e6030074075042422141e410400c60b840e1442015550400c1c004005003450040c100d14aa80800d0a000c002e00c5031800002e03281040e11303040b0540000b0300c2103000d8070710390700310003d8010b03600780d602920030162450040c0b007914020b00094940d19a00703100610301410300c1314025a0400c2c070703511300400e41451190206221002154040f19581c0c444e030a00d0590071b003405400f8051000444081d455800c245e4102205960015070181001d100301c00450a04902040010011760340100150344403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 846500377 1250 846499127 846499169
    0x90a0210020303072a030804060f09140d170621030d0207051c230705010606050409180b0c0a020109140a020a0b030f0a09030e0a090204060306080106050d0b04020604 73
    0x280d002954110007080800b40c00c0342413049401c94080b00c1200d4000c40c1d402c2e0641c0398404480087d0040c009032041c6a40d040d4083c11400d10b0701803010580d000703c04448502c01511481c615106200c2c00300d0080110040098228a80170300070240c000703e04070740c0c0c40c0aa103110b0020143d01d80c058081d580740c5210000321521142e1540d0050014280500191190b001560451548a5401182010006407500c804814090900082454100d018540c0500b4508159109400c4540c290045004204045400c1000301040e006851500000700342007401c0035859614a01c04050113040c3c0c076800034000c01c01241d0b00e4400d611109080d030b04070044040341c0c08141056511074118030b8099001c0d010390780022812482810441c4d02820410721a0038040c0d5888070701000811001004804000400d03d00d00304642d244400e1034058a070074000141d445183c008007404480050f440290543d06003001005513640b03420300a007400350442d10380f00b250303521840003e80b1446550000707008031105203841cae440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 846501627 1250 846500377 846500383
    0x6030e01060e0411011b050d0314070516240501031505060603070e0d020f0d0c060e010e010509060912060c0702011b0b04140709140415091a090a021002 67
    0x14190808008005040d1140c9410b401000116000f803d25210080040815403089048501d40003a0b038101281ca980700d90b071420b0414508030303100000242c60f040b103600b000341260141c40c3c210140341450fa140c480001c480c00080c10340c1c0a00a4010100f4007120803011070b405007000c10421880b0020421582c49142101e11400641c80c2000180d146c040080e00034141003041324020200c1751200d0300b82c2d01c00c500401c5a401001c25040341c010a89290a400036290741454140e010702c12500d01c5045c4d07041480041000003498121410440a1070707906185980190031a000d6083c20b503001070341d0310300c4040400c03402c90311111100c42c01d207d01d03010018041b001070050b0078020b100341e071a0000300800d10358111104010714000760500740390201003400545500307a040c298050140c01d6401c51030342e610140040350020b0520481307a650a00800c0100700300040d251918450b6402c0800928105c1c0d00c55a20a04080154483c100c0000e00442c0c4052000c01a14171000d81c000c0040841403d00680291 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 846502877 1250 846501627 846501641
    0x10204031109060a090c021207050c090609061005030907050607030207030302013b01110d090312020c030f0c0f01090c03030e04051b1333050306130c180603 69
    0xd0800e140d10406406281c150b46142c0609401000c408030305003000140360051200c600e09109610404144a510f14520b02c00b8000003030054000e812500c1c005001e200c41e188004203954407031000b81c0200205036940076507180d070381c0c24545080380e02d03541ca5803025032034840e10342c000c542d10a00200c1c2d00e0081550024104003507921950090016401c4804c007081820480180c44006201d00040740c0300600400c44402c8004120000101e00c804610f02100003a03032103d00100d00880e207030300088040c036400102040510007026011854503030348540503a100e020329003489032442d00c0016603007806c0c0c80800c140d154400081e40204a034034500d03e40034017102150f100880202e00528840101890140310f5a40b059490324030445107001003c1e901d203115841800d140701c0c00c0a00e80b8002c10501d0800c80c258442004c08142c0f0314070000c02c100c01011110351603c507e0100b060030010004642c0780d07040307001032942c4200804900c0c030001a01c20b0b04e0f44445804580d1000702403000c009000c030f9041d0807100d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 846504127 1250 846502877 846502883
    0x203070314070e01030c050418020904080c0712020904030804030c0b010b0d0b240f0c070f05123415080406320406060f08010b0f0d111905040c0201020403 68
    0x10b22610f0743d500e201100710b0402d1102425020030a0410840e904068000700680d060410907050490b100398000f4000380d2055600b50740181d40800d80d851200c00401c40c480180142101c00b94016400d60b0028000c90b00c000e1006082150700c2d00481c0c00c147c020f65405000a82c400340800b003541e128455010650030217030440c0c0203035040001c07045003408c0c640c01a003045600c00340d0020a03031f40d449420011540c800c070292100310608110b400c42140b010b001920140c8094016440308524200420415087d54048414a41c1000109403d44001030f14850550300e01040d034480300103000120038100b0000303a40000450603d03883c0300080a03600c8500944518415901004a8142d241c1500812040c4400ba82c03a48c05484d074000d038209500748000d0382d00a2150401090003511460380c95a40c0300c0513449440d00760b4641984e403155107400117403e0307c0d03054140e4000d441d499480d159503034410164815a400b90621007004244504003008002c013030700b400b41080c0036800c03014800130300035032181c4010303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 846505377 1250 846504127 846504133
    0x3060a0501090602062a120f1e130501290108160e0609061b0d0320030601110703021c02010206010807060503011a190e0f041e020d090203070314 64
    0x1140e2507020705600c800303032492a401014030346c0c0e406100c0140b055402e40305903000d00c503613104181040a050010003100c0c0808104850a0922040e00e1000490180009402441080b41c99128010080f21103610080001c000d010b10405410010b004001c0c400c1807861481c020310326242041e01c0088442020302081c5c2c1c2e0542959607070b0b200300c1200703841c3e40d5016000407102c80c400c520354a03200c1c01402040304000c0c8030070b2038410102d42d13001c5030425041d1800480c3d000f4800b06000150035120746121400d2200c1248007035481ca14407100c00b8400100010706021081d0483c08a031070003049660040d42e0701429048a054805801c84021f001c00d00c0100d006200c1c1e400007203070950300800c42d90200c403526140c09095909041c01c010718403858661603031419209101840d000c0300481c1d0540c511801580f10550301034818407c1c0700b251328414041c1ea0041e424039850000c403818040c0500001600c2c01e00068540b4103004841001e00b900c488041c1d410f00c44c01001104ac45590b4442000000306c400403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 846506627 1250 846505377 846505379
    0xe0904120e09040b061005090307170607020a0b0103240c030204140303040806011203020f03030a06031118070e0301020f040e0601081602060c18041b09060309020f0d0c0e0c03060a 79
    0xc0100342c0204a600034104210b07080410305500340486030100c450701d40d0400e0350400c21001c01003490700080ea40a039600401d1070756000079500c014081540c2004980c80601900c5070145c41e00d8141e010180300003041144c02800b4030711044060711210300c402003226400c2c4000c3c40f503821b0090223504a40a00095000241c1285400385400822202241c0e018000b80071240c4c6011801204100c60003c150190300030001da10855800070b10040d4403c26920b50001945402d5050035024440309103122802034038180300d0055441c41c103007803456024201e890041c541500000c007084c0a4017480724124003810001c02c01184000c5442040c5200c0d80e400c0e030705c0c90102e03656100c0d24201d440c401d103165400350b0000c0010400000c1c1180003818030001e220079644086102c500490112020f02c014a044885140441c503006070340114100010135080c0b0301480010203e0b00015144200c0012651045580e41e003881d08201c51095000000c1c0314540c0742107428600851602d02e240d1044490520403049160 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 846507877 1250 846506627 846506629
    0x9040f1d10180209060d05032107030608100e01150803093a03020a0c0b030709060e060d180204090305040f0b0403030818070b04080304030b01120f02010503070e0904120e 75
    0x20a444582c03042c8084080c91203841d809000a286010302440d4010503100c4c8408085042000140f01440c20b42a03c0b02d1101c0792800c0d55591450094030b12410141000d008200d1894000344d80201c040c0e94950005802986c40350085c0140405040102000c429040000d00d844011001e840c101030b042d10510b4500d0705240944c0d00700708905080a11030501521580c24400801c600f01c1c1582c1d00c41d0046841c08030703503600c1d00c9151f0111684841b051000010810811662054010004000909248007407607032100001d0b0450260b01d1040080641e1592032400c0c191200b00e00440180d0003a208002c0b0600908000b84140d20a01840107445201c2600280340c12011084804680d0183e40d40f90b490340b40c0b545c0c2100c0d09014401c88801030311608101164801061340248000d00312680195512031a5190101441005031700c1700380c0b072144002c0c1040108028040c407045203542407801d02c0c0d0740da94020f02540c3c0a042d804c40990000034290400041140c43e141d03603860300485480c0c3c500c0e40400c80c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 846509127 1250 846507877 846507881
    0x608060f060708070c05030604060609230c070611030109020306190302060a14090a09050702010b010212040e04080c0d120b043809100302010f18030809040f1d10 71
    0x1103226904003004120000100b10b40da409401040d00c03c000c01c020342560b0703d0000b440e21500f52000e035240d40d502c000801000c0c005124281c902030b01e001144c40d506285400e02c1204c00b10050070000b00f0000002c1700c400f040425440784800c404c540601c19202d503120a5840000d4108864030350003031501e010800c40003e20004201e040b264001c03e89407415032a58801c0b81c1d851940401c0b055070300303403e21002150750384600401c00602034803407000803145420300c3c00900799021f149907a419500a120000203200c640022101540c4203601790079259111454240d510303100d1504001120700602403641c00090740448048501c00b01d43d8024800c60700810200310440d01e5411084003a00c44212800208034004903007840c111855407840315074607070290085082c500c412038490b402ca5250550a208568010152660034105403414100d9060007013070010030440c072400044d118000201e5540465039458101c0390b05040203c4e030920240c0c0029802c10304040c102d42c080c40490007030201c4503280000c14 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 846510377 1250 846509127 846509149
    0xf0601081b061602030609010f11120a020705330c0406120c020102040b0a0c06060e0103051e121b070e07090902131d04150c2f0115060806 61
    0x403011003200c1e079044810410079a001008044507034140c408801c001d65404d00c5160303c40c0b4408000801c6000c508520003003143c200b071151400c4858140010404010100318240c4e1100414000507030711201820840e15000c00c04640c0b6080c40700001c0200c0b002841c4005060542200318840101600d81d01c541d6402030080340104800921440684c0c046003040e40c0144d440801c0c580001458642c030707480d0b0300480307a000c00396100118601c40c540e60100100307071090720300800c0c1d4010518490350540e96540d843e028150040010400320701507058042c0014010078962007458070b5259a40c11603804804da0340b5091606100b4503018202c00020740700c40b8280b85600c10700302541e5070b0040742c0c2805212030094100c0d07040d003800c039503511402040c484650b6084240b44640c0840240030b030728042c40d011450740480d1090010241c10003070400442030300040d40c0d000e14034901c41c10b50f805890264100141c110704803a244015801c04e900d00c07140d0304440c0114420f0322042d07611410141e6440c4c1c2400300325000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 846511627 1250 846510377 846510403
    0x3171e040201050d0615030b0a210305030a06050901090b130507050d09030320190504031e0f150f0605060306150310031a150108161b0804080f060108 66
    0x18000000d00158812801404c40d070610040020715162101c0144001d03010041942c000310755a402c004170645441103a0400803c520b02c00d51004c1d003c0c00714180c1040410600050903c403000c4040b81d8054429001000580000703805940d2540c3d58a0a2101800d08005581d0003540114061118030a450240c503114002640320341d4a02400b40c100d803001841081425402c15136105004491010401400503408440d288115164011050003e20221030000d0010600c50100410070000d1140541c0359292540c44110100034091130401d42e850210205000341402c4a002000769031141daa804043d006006800801009454000b800668402560042c2c1d00c030040c0000c60784400f1071000156400031926103003207541c82da42d03070320481001c114106611144000804112141d610000308001c0a41300346020f41d003a0404801c607c6881d0344214009042000601d040b12668500c031602111195200010075550303595988a075480354061884400c80c3d000e001c1c0002640381000660f8880948 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 846512877 1250 846511627 846511681
    0xa0f02011103121506040807030b0106270b1b010f09110102030403051513051c02010b0a14040c140c01020702090a0e0d030e0a14010b011808030909150604030317 71
    0x1200401c0c2e113001152060f00d241c1c4280b04110105100c2c10074825140251711480303c6451550528402400c680c000b8494588000e01c55080c40c1d2000c1c442c5207500048580d000030301c543c0c6540d0a550385805102c070b011284215820001070340d110540c180e0001b00030b980278106030400e814181004a80b0383c411840081c01c1c9903c0102c824103402d55005007950072405e03404207810090216654030781802c2100c0c0ca110340701040c004100d40030b80e40a02808941c0881110018030050a00e0030045d024802e1442c0d041c0215501d2103c0040c450141d520101043c0030f400c0031135203d02014113103e01170750100c401240944613020108402c100035004070100e0140d9034000e00b01c0700b40400821401061406072802e40d0f44590007801c2c0c04600c00004a15242200c04000300c4c103071b02ca07200003400700c0301e003004c0030f942d240c105000070481100701005459003007408452f04942610b9020060403594580c50700d940e8402c800050010405411203164103e011582160344050380d00c14190101d15140c1030b4495440d01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 846514127 1250 846512877 846512881
    0x3060105101b050607021f06050d060207060e0f0d03060e01060e060d0605040f0204060201390201110a0305060109120804090504030c0b1503070801060f0b070c080a0f0201110312 78
    0x38003400d42a1400d2040140440c0300b41e1158955a18154043d15a00050f0704030310300d0103803546054000001401400c4034103010a518010210b0341c0c2003060400a08090b9020880e4820090340c0c0d000f06044440c000c00f02d80b00d441814111700c1c0c48220404002c80428648003000490000300c029850488a941d11511070034402c10050140c05c1d0b102d1403090a1882c1d07900e80100f0345695510409040e28410440180c840d4207040000e801c442040c02e0100d0721080b2420b448150700a040c0700c02840051003500020500311103c0700340d01504034420003403000361010910200803a49684500c3c4905400d990300001326544a605a5000c41c042e200641121420041405008003070380007250003a04c20b00d0422000d0f80c894450030000c007000e50f08191540e00101c0039007600d01d41000040c007c5c10788107008110032440c0c410540c00854207889520321005000c120603090018144140008007510700503103000300324070301c0c0a20018602d100124082001004410400b010000a58401090340d1b00c80c52803607 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 846515377 1250 846514127 846514159
    0xf0f0221070807080a0305040b0a0e0a1101031404050a0c0608012409120f022817030403020303040305010f1d061321120b0d0302071e0b0f0702030c03060105 69
    0xd40c007414080d20b00c2c0e10100b0002c0e001941c400018510503075140d50010342405d151a1142c0521001780c01400301c98201240d1410340305020070b0000e50254041a003500e40c41440f401a0013600c010705e43c4180c1400e100041100b80000403a5440496225801300741c1c10a480b0344d42550251428022002030008022945030556001a80c09800c0c220500740221942d5642c034820798408008482120305803481145102141000f4004401e4013450220303c0071a1080c84041500700c41c5a0301c03c0741c00c01e107030003165501001424021a009542c0240550780d0345d540301d0a1040c081c1190150b1020035601d0000382c82203002000301c0850b5004030362800381005440e02543c01850078040b1205a80e8200388100714141c0740c0d076400c4110303480210381c1c40390001c80d00000d9611049540340c0b003d55004085205107180083d60100d070450507a80c0586511482450501c0e0b11008025190001e41400c10000303044014103c2c0312004e0b02c1240d20840868080305074000c18151507100a1050b00c0d040344d241c11100341d031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 846516627 1250 846515377 846515443
    0x20a061b05030c0307020309120c0102060108011e050a180b0f0906160e030705100315050a050315090a02300111030604090206090409030e0901090e0307300f0f02 71
    0x8160f48101c034100201500041c200c4101c01e489e0660541c003088481c90036503010320119004042501c001c00080d403442c030b1140b04034070b5000804000c07240d4a43c00550205059800010741c01008817216242c404d80b46403204500100780c6902c1d800047d0003000034100000080c080d8419100545601420950030313400f0f464070f03c03010341071340d9050094078000b04842c0c41c0c45213141d1000d25a545c000c540c038441542003440c0388056403c02809220f910405210301d84000035100b00c0d20b00c0796400c031803d0303030303210000e031404c11001380c074025806990b200480e45a020000d06404102414038404100d015100311040d00b00c500504c222902c07240f007800040c172189040d9102150342400549118a01442c10000504230b03421048103d01054000f1280310302814201c2205015003c00c14041108141d0081d4040d600c0c000d000d4014210300c06204d030380c8040615010b450350009a03a40321400c48052540f4080c20781c04091810740002200441d600c0c001600c005210381b102d01303405d008106508899010200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 846517877 1250 846516627 846516631
    0xb0406050f162109050d1703100f030b15010e2b061103010906170303010b0a0c1406182d030f0a030213050d0209070305150d03020a061b05030c03 64
    0x2c108071102c0d02d140d0128000ca102e4803511405400c1403501c2441d500005420058036411185c0610004242c2200107052a4009000030b2040d9503000d489030343c1c210141440d040740b23400900c0e2545403a18000100441841c02500a02a4807501004103248000440d0a00c2002e14601d9116017410318510014030031400301c00300706c0c2c000c08409403001980e403504016240c42e103c544046032000401040440d0042c4984000303040303046a0605662040500d1a81e070f0f0006019003410400001a1409454000c2022116003540b00d402400c03400350b042c105544032242103d11044185410190765480c2001054407600d202d508101107984641040d24a48040852074054000b88001c01180410702080e10242c00c248080b6a800341e50b60b40703a648605014840350f0700c068020008032018034010b90b00c00c4651039001c0028a0005640d9403440c68000d04031b6103101034103802c80a1b01017003a040c15400320301c1207119401840d09000d140d06d00c0c03c2c0b00a8800725404040005401400459046170359100110b03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 846519127 1250 846517877 846517897
    0xa0201021c11120910090b04050d081006050d150b09040c030605030d030e01380a0308090103020a0201090b0921090f010f05071a012c0115090308030f040c0b0406050f 73
    0x440c0100e100d45d0500498040d40760030b0b107229121100f0003003042001c00507070658461a2a18007200d0511203050403556886000d5442403000100d407125250f0600d610410702e8481465040381100d0b0349a590000310f034482807403a03001d40e041200b6510124040d00405048500260091150200185044009004000f0030503495501d03844d0903000e882000c1d08054035808000101151012100c00d9400e035010703001016130084034280c4080011482d03c81c01e072038140b0750070300340503076254000c8030700701d0040c4105c50004050094030014071149990000b55040002c15561f24951903454100c20ba80d101e024280416034440140c80b080d103081d5205a80d02a01c04501c2c0c1003e505103c2c0719501e00a03c0105c4003586000013001d6401040402c84510031004c0381000c0113401600300340d807500e01714141481401041070510002c042c161a05101c1c00c8924003c0d900240801d4a03410311003542c60b10030600307517000d8501c0361030310364042115854003045400b01c90258480300d103880c6c44d0541c41580c54120462072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 846520377 1250 846519127 846519133
    0xc250c09020c100603080901121b08090a0f03090501020709020f0301031b320105030631020c0106060306060f020a0308150607121206050d0b04060605060a0201021c111209 75
    0x800d43c070107250107090040d40c8203140094031100024001410003886441d1505000c1c101244060200004d181c01c140c0c80340280745c104101d583d1400311600e44a40d1010050203881844005014103904c559144107480d402d0342031703510441e9640c2841e8143c3c0120300510203c9a8100010000a24085800b0325540c1c44002400741da20f40d6010b040180c00740700c10182030100c0510642c1d11404c44c01c03000c0c0b00c00c85031090801c82d046040501c00308800210021280002d00700d408103200800342d440101651040c4d04900c155501c1010360440f41c084c0c0300a100d54000702e4241240461428020b100c0004000c01070390007421009240e850444a1036000341c4455100e0400c4005002e80d80c94440081c11418020b007111450741f040c0c1440200f0403920100b14001081c0ba00e501404140c0e26042c00001e450f1300144030103c10b4545013000350043c102d550000d07a100d01d0028825244c5038044d0040c0c10505184030704002c8030311005000a0a981407404100200c0b08100180501c0b65500b1070920b4000c5005412 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 846521627 1250 846520377 846520393
    0x6040b0901091805070201050604020c060a0f020c2b050705030a1d0402040806040201080a0513020103090219080a140d080c0d091e06060b0a02060612010b03060c250c09020c 76
    0x440807110f84680c020383e1079500e81c02005030703081d024001d140e01f000080d10118684105141030175152000a0071440825071194582403c4226540650b015070840409a03045805082c4894600c408540e03112302c200d9180400d00400140030f141518400b03500700d0065481e0200355401119051f160040c04031040300d0031030102a00d03407102c2c4048e20103000700b14000c001f40d003403d00000d42074a10003014441c0c5241840f040140030b1302c141070104910b59080c203012400d00010b2001442d4081e0601c081c3e95848080b80000851003000990040c40034013a007402d42c4904401d622958950084848000102e4520008115211980c2008203690942c0b41d000144062465880a0214690440001018038129081024080d05205417002050540d039160b28280c400030010351503000080000d8851a040080310860400a402000144900400759140c40c50460441580e40c0c008404134001201035003d405820400303c1e0213410110342084d5804911450641104080d50200341c00c00e119000d0400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 846522877 1250 846521627 846521639
    0xc0406080910060f090b030703030203041401050d09030c0b100f12151508010b01021c180902030403030c090504180b0907181413081e041d011e030206040b090109 71
    0xf04040180c440c3c4a904845145041150310580350784014291094000c2901040001c0d000002c5508407407401807110100b80350a00103a40f24064026211141410110080d04141e4041c2083c408288981c000d040192500101e00c8070801c000d014020401310080c205110391031101e015143c001d4811031b40030210f4040040742506440800011100014500c0030911001400707001d02e05464200f03200903c11040c1040c0c2d44000501b50b20702003800d104c04034112080c1900300010050241110403001e55490900c0d2a00400804103e0040310000e1401100410b0510305400b90401c007e41c9400400b18485503074407881502480130745000301ca44500000068603c2e01001050b0b010450001d001840c45105682c204001100506219200745c2000040f0001084d0500350341502c170100000b17041140002006040c1c0b40b01e00e402c0800514500c400c0701303030412030560b90107060307620b626000d103060249110802003a40040c00000d500c598184000d0201022038009442034600505d40100c0e503a548803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 846524127 1250 846522877 846522881
    0x3040f020f150c011b0201021201091109060a0c02011707021f1d0a120e0d060903050702060f1b1f0917040b0a11061e0901270203070506030c0406080910 67
    0x8450380f0340694642100e240c4451100070324041070070355400254039052080050700702c181c80c140030380d0300c510759a00550034901203481e0039035149440140c48950780303015400e8041c200a102d81401c070700140050304204403442c100d0050038050415a002006000505041c0030300000704000800c015982d154400f104810710140b0300c0341c05109001c050407229075207003815190040504604000d00c0010056011540c0707841d4070340d40a06402c0840000d0802b2180340c00c440601c12024007030b41c01035010408116100d802d5005040fa00e041d216000b10300311155910946500c1075a1744560302810f01034484c2030040d51034101d422101d124440d010a140a9001484550b4202e90012411010040b03800d14403250008504030140390594021312440c0707403e101d01c486600c403c0700b950b200022900041698410250408202c4207140f00a02e00b0b0340c0344400e0603a01420400e94140c5c0300b403203001d41c00a400d0a060040340c1c020310500032034518040c10100e05888200c0041c01c2d0a681344180a0100c446080c0d034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 846525377 1250 846524127 846524137
    0xf060a0b0a0e0402100e1e01110304060801030b040302070e34050301050409060209030105010305060402010f14091e03010c1e03020906030a051b18040c0e0a17100612051203040f020f15 81
    0x88030900c140ca03040c1800040c070340e09c0020140041581f0800007400304903005041c075070440741c9c4500351400c155954502242804020390101203041c0040081c40184448101c25900080158542003000c103401111f00100841d00805200404c500308014052414540c10615980b40228809450125031101180c02c44009a1094446070404c4d4148011580d00c03501000200c0c10710314002d0107034030303065015010600c640400c40f845900844103a105c080d00c034440d6107200502c020001c105401010801601c1000b9031180c0480d14150032100e0403000b0f000f031003680c04085020300480d081d65201c00000d0300600e405410210f02040104090066803d410000c08010400c5880b0384aa6100342052106640c60380401006001c0403000d100303410785501c148102155490440700600540c09401d0f141003202e50038503540c17001d08102022a150401039070780c1640d10b104004469007400702400381d590707900050747c000f0181244a80600054509007012415891004100c48940e04a16007812216404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 846526627 1250 846525377 846525409
    0x150e120301031104140c04050409030318030804140f0a02040e030910120c0e06070f1712090d030c170601050f0408160e060303090d050c030f060a0b0a0e0402100e 71
    0x2800d42445070038280b41c09041e080c000602c485c61200e0421200040c020301039400380601403565a04000181840303070300003e00c00260200911a0301c2980c0c00c009198420840b020b0707610785846400f003610130390000b40710f008030030144003d8501401907508100c064031045801c10900d1200384181011503844c0d000300d48511805440703586a140c2c0e400c0079503042d03498550040d024040c1c2c07446502d042d6200c590480c0c80a0b944508110702040991900c2c011010400b80d2003100c00d10040f41c1c0194120105021034040c080e8a0200e4203c881e4545046069400200d6800001491800028039648045c1d190541040050400b5428401d6125280d130302500581d2012403a984844222502103089100384005000b080b400e00d9080d182040110fa901c3c40b42c2c208007401142da907400c1101b480300a102002c0035a00003800d0303441c444901512207071b0343c10056501e207140c0b518004a00243d89029040b020498028211070f4080742c3c1c494007000742c13081c2e4074030702c0c2c00a01010341d90170300031551440c44690f51040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 846527877 1250 846526627 846526643
    0xc0708030f04080c10080f0603010f050c09010810290c0a0c0302090901060506160c03021008060109060e011d030a0f150b0108090a0f08300601020307150e12030103 72
    0xc82d02c0c50b484d02e003800c60013815001e40c1c4030381e0070f03580520350081e03503164451203c2c03d04481071345442010900601c0610040e0904a01e840240960001030500900035070400b6070f11003070b860316800402c40700c00110b4401c040d400460b1440c209445140c83d12a00450801d6008081c02c00000141c86800d000c03c41008036040c5034484424002c501d40890f4264000384a10000c108185c04c1401050091054601507096143d003000340c1c104101d07031060034101440e400b9003605200d456411010300000030540713900780400d50340b0340c0c0440c40c144984070440b02100305030f541040d15030941c0014840c0c1109030b0102c0750940298550007001c036921121081c4d000b0310418031101c0b84030840310610100e940c40c544080c100050042031000c0703448005440c602640d040883d52071902400d1070003c881c2c2c402d50400d99140c031550f65254000c40c000b5003003c50f50045103100144182e07110801281c40388601140107103022004078020030252015844160b00c15480070440c0ca15031501048403000360801d81c01117840c45 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 846529127 1250 846527877 846527879
    0x3070608060d0b092d060621031803010c0804030c0f0c0b0a0c150902030a060f02040512010c031808160c0f1e051008040b061c08070201140901020a02060c0708030f04 73
    0x81013984451407650400401c0c1d4140c00c146041c01b600c0b003401030003252065280c0518084000303180d100b00d00c1020142d0044a0341c07180401e200171100c4030b45240d07035440707940307000d01402445001e0400c2d148102c0d030540d100c468400f0700e6518200030380d46101c41512155040d80e4003003100369141c0020710302c6a50a0302c0e0440700803e00c0c588850344800ca1440d0380c0e5180e082500d0b040040c0c90000d115200d42e82c0c448000309503540c0414a9400a02442e17020540c0410a5980340510b00b1065102c80c00d00f14540d0740902045901c094440b41c0902d10705401004903604100c2c80f1480c2c241581807182c900c2c454005211003a540389031052070010580c10401e14400e0002064090410442d640c4004040a40d418460000f840801405100b0014000b405c045422000103070180da40e402c65841d0a0215a01e650003540700e810003141c0c54110101c00ca002c500170015441d4903003541002c0d542088816401070031100c0d0b1550034400300c0d803c41344a248491007404008900800188040c00c10303640c0b5426055151 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 846530377 1250 846529127 846529153
    0x60204050a080609070f0f0b1e030123030303010f09091401151d0405070b160507270501180b06190807020601150915050c1506130b03070608060d0b09 66
    0x403202075403091182c1025a40300b00400486980036500b01e44e08c864465480340c00c1d0052071081c15a8a1148a001100000001c0f80e806240c0701c411460301480d0304d41c4120301000c03d0030700d6a203110a00513905960b0100004000851860f0414042c0318402c074040e07060118600c4001e42901da02c81c1c0010407100464001b80b24aa10004400c9240711074201081d0721402c06e81c40ea1522003a480c0540c034a8410009200400b50542502c210780076a403000489541c155258141c1e200504070034114600039145d1101c15207041d40740d0040a058500c24404007500b07440f460a20320051040e030080d136070003120a004031200407902c1027042020b102c00740c480c1e240c01e2600301c000a04001050308601d1000e5070110541941d903620081d01801d40385958180701d15120603401c25a10f6020303030310300d20300f4520070741640b10016001c044040b4000d601c180c90110540380409a20015101e2901203250190702840c0200f220f0b0344030f80e41c8a50400380181814044024540b10903416000450307510000e0b503c42804001d030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 846531627 1250 846530377 846530383
    0x50904110319060b1203070803160c08030709170c100305090a06020309240c09090601090509150102010518190f021002010e0615030d0e010207090f0e0c0f10050304060204050a080609 80
    0x4205c181e20265150081d0360740c8404c5c02d4000504001d4030301c051081510b00803402042100a0240c01044640d03c0e454103080040c03080b20503000f2205014080078854080c41000504200086801048010a065803d004500410004264610a10540c1002400b1503c9880218014002d060250000c001c0805204071000c240c007002601c0801d00e101006000352400382658120b4034100d4984600340c940c54012211160940c000d583d200030341d9010301600d00624043c001d036100c070a0700280055a01c1c80c58600740103c079070804040c13981090200c481140020f0390100030b01d5215a21109110101d900850050801e5011f02400360b0345d21100034040d403104000250b402054024000c0101c070100000c40d07200c01e54070030302030180085070a840800341c2c000d0110340050052020704010b2107004d80e000030b01422000403441041c2c01480221242400c00044802007540094512172041180c00022507550303000070300c01d030303000c960074000403070140d5415204000030800307480100f50a090140340710b42 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 846532877 1250 846531627 846531649
    0x30602091008100909020d0204050a050a05011e1703040305150a15031e03122d090b01180209060d0504031206050102070501110a02030a0503040f0e01050904110319060b 74
    0x802d0100050401c50703d4250a100315041e200030000c081604040da1000c03d00071042100025845400c000400c010403034036512881c49000340c03503424840c2d80da8540c251240045d099040400000d070b40502031100000c0401c031609000b00c8041140d203040c2c0e480e02d80d00c0c00d00c00844092042d281041c0180000315841e402a00c09440c90021110043c9142da031703420104900c44200e0907d02c0340700e15109410325014200f0840d0550b00480184a01202011100303c200c01c82c5104020604282ca513240301e2107003920904140a40c400000c1603140d003010400700d0164180c0c0040403030186c081042e90015101e0f10040c04980100307644c00b05460a10b4500500491041d40e821180039240110800080c0c1c0e0004880049031802c0c00d040b000014445031341c03424020740d20406501441200c000c10104440080184111940c4200e08a1808c2e1182e12203a6030398401c0c440c46901c0002e54001c140410603070044400314400050448403401035240940c8048d054400c419a04255108041900c900306009221 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 846534127 1250 846532877 846532909
    0x50a120e1902031f0e070b030906010e0c0c010606080109060b0a080a05060a0f170c0a4b060e0a0608041407050d050d091721040f03060209 61
    0x4809000c40da2901a541ca00ea00041c0d0210341c21041640c00b036440500030f42815150710100e0304107080c3c08203a500c000d41860100e0780c0032842242400687c0c032034524242ca00400c0e0b1000500300b00d91030135900780b160b07000240881c0b0041004010280b81c0c183d00b44a600004c2040b91160240c44d0b1400b5038190407580e0641c001e0b00941010844040b01503440307505982c1c404111340001580d49c032000081014811240c01805080d0503050021070346041505121006c6250300044600d545c80b00b00900000b4582480349511140181010b2400711071101017101c2e8a41150b107400c0c0841000ca2718009030326109010088151a07068400c0c444950b108042043d604000d990030090700e413601c280189000c00007440a40741d403402c1c1c55541401031062108000421000b0031494009483e4248642c0b5000d88551810116520510010300034440c0c0d0004501201c0304d4018002c80b090440803100607070503040f8000404101040081a0203681c481002c02070346c010200180c5815814003805601c0107910700781 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 846535377 1250 846534127 846534131
    0x2070501050301260f010e0c040f0e0319140d1508030301082a190e061c150e1b240f0703091503091e120309050703050706050a12 57
    0x504c4454802c9008552030b00024119100c0005403007002800d00d0098041c8190310f50805007003003541706001940940c090000c890410130010034005030f13001c0714412110620140c109018004480d50b00c0c460103400e002503400c00c200d00e45003489040303486501c0484030b0040c1c1652000000510310011004a01818805d00110310b5541000c0c1b1050f911003e8910321070401101094205d01c0007090120760714031400180c119001c2030007c1c5105c0c280304060340074032448100d5542c0003c9140c501540c0e800e0140001cbc48440585400340d0b1100c0315004420365900720b00c0c980b90300b5030780c0f0001e0702040030100100c840000000300041c0d24041000d2403100b20a0945201c600071010700d07070707900303a04105c8640c2143e0341e5409a4510042c94141c81d940c055038001d20490b0554000515440e40503040205154481c0510079000000d01c1c41d6030f02030310b140b50380160040b0304085020910394040e600030024540a90126003c2d280c1c0d9950391441d0a0305500240c0014801155026030160490503508500c4101401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 846536627 1250 846535377 846535379
    0x30616260f070219031e111006080607020a1203020f070506010801050a0c09030b070e01140c03130e160e190803130e01030503091017040c030c0504060303120504030207081c02070501050301 83
    0x2040300064017606e50010002906e400b2a40d401224441c9404c92107100740d4100268001c400ca0062079140704400c0c5c0303401a82c002a0903a84041903801e241a84460390610855460108030300035040402c0f1002058400c0000c5000305404100040c02010040f0000ca120302d0f00310034000c1034550b569650014422074030014400540c2030051a60710803107910b0940d400c0440180101c2e06450300b242d0070106008002800c00598a020000304079102034080041b294580c0d0b40381c4841c1050085411200d120200481122001d100b51115100e00e20001c0c180d00c07e40c908056003680c00c414640c08180542d00024401d80320660602e00600101001541c2c1c4c1c19a600d1a160640c403813241910f4288500707562004564518007442d05940a503a52160300794440c6071900d4071041d0940bc40c0401e0710b182c22001400112854031f400b66000752541135603a80c01c0610042180c1c1d000d441c014008406500035440d021440140400020141151850348280d4031080104007908044c200d402c803a041200404c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 846537877 1250 846536627 846536633
    0x5010e070b18060c030708030106091d040510051008030d1d0705090c03040303020d1b02100204180e0316030c06060801060b09010c020109081614030616260f070219 72
    0x80038441d510002c0d83d04a5a40740400c0815045100d01c08000b402c1e4000400041189035025640c1c405a408030300b403402c0340340880c40d14480d031503100300d50052444d80055401000205a074201641180c148403400014617154900d44d07045412842a8000450766401400ca82902c1030500380c82c030000c080046c10f4040d0400020401c1860000c01100d411100003000c81c0c200744c86a811606008a03a5104000b40d440c4e4881d14800d402810310080014410750340e14800b8a82d40340300f200c003210022800c0d550b0038407010760711034041c12140402c1507250109116424501c2003980071640c80318070076940c000d1000700b2890010200d55242d00305040c160700d410301c10700071075400307808403501c0d0b034000d08148500c09030500c0100e0b40000190800d007601d00402e501d42010b00103008040003074032035826180a40304900c1303003419541e60044804e20907002540d1809200d2034040c80c031481c08807803441c032460a500c43c2c41c68203416910050340d45844481d101d00820011560500a041c0c07203080010428541c0e0085071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 846539127 1250 846537877 846537907
    0x91502060609040f02100804050606040e06060d08040b0c011d2e02090a0e0a0e0a05070302090702030c030a09091413020907030905100204080c1203040b031003080705010e070b 77
    0x400407406840300714003190030312403811301c525501030b4002c0c040240d032214040b0041c6000002e4900300c0f5584a808040345045c5858011070b500401440c00031b02d8140e4400c02004403115130400c00350b83c41d4408220206042c902c5a0003801d510400c00008100001108041a0b40c0d540080182005400c00341c0c0365554a4450075010403040d80034003000c400200c036400d01c20024421140b10652004100b000014103c00d1464610b208400d445020030070040b010404949135448008020034582000360107000525103008900e410100c0c07481103909105580c00751324515800f90030f0b07680209200a60030041d0304510b0041f89206111030740e900b030303da08129640c05800000124000c1c840c80f410340000702c00301d01c00d900c0350341100d070403100f06c03600380c1e0b00e81d5800d400951160090b03052a02907050344009904000d88450b889040c00d000462402e4946a10100c041e04080d00c00e0000421701503000011884031400340910a010308000503900c00c0189919142074400d500480304110148904003048441c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 846540377 1250 846539127 846539131
    0xf18030b0619030b0f1e0f04020405130206091017010e090d0e01121e060f0e010e060112050a180b1f0b0403350d0e1615181509150206 59
    0xc0442403420361607488030b41010450080c0801b01c0301070305908202d0f030324030f170210440d018a0081c0ca041006803100440d07000c0d03075100200d010750005401c01c6400180d0a15156103801025185401011801d050030b0071280a00c084c1e02c03000c074600140c018026641800c1c000340c1e8000707040341444100c1180f0a000a048248400042c02c040c9954003c4008001c100c140745120b0426403040404c0480c3c1c80313072010030040545008401c5200002c2c4008241500800700b001d0180310140c41f07000c0e254180041e01001b8142c01071010031244d8507030203004041d4900040706158240701e01d806490781d00d010324024001d1100c1141c8081562518001044250901d0041b2030903a608a00c0c0c4c0006d051202858650f030034103200310345120001c043c090b44c900308441d1016220207010725000b40003201c144111240c3d101c0c00c0c0c8011501c80349242804008180109070f00890701c0700b2a09150040c0d401c8440c0340055450307294081d2000511050585c00499032100501c0c002d44820f002981d15000fa00c24025600da0300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 846541627 1250 846540377 846540391
    0x1060501090b030601020f0f07080c030102030f010308070c03020306040b0405150c0406050f090a030501061a040e061201140a0209012703080a050409090c15170402010f18030b0619030b 81
    0x30108130305910034881c417403003203801208856009500d15180b5550707440c148210500e900650b85d6000d080c5ca4103000b205c0c06228245c2c1c0c0c02c0820b90861703c801d82c1c50307481010112341400d0141c0c000001618240051403003140640141c120031b140904042d400d00380c891140d55005aa20030410030b10704031741019501910100c0c0350540d1901d902602c0711250b031003030785030881e03021000c90b43c000104481501b016054403100449400c2400110542001c103010702e0203200581f503000c0b40000c0380b508020b601c2144503044e600001c2444600c0d440e8004030303998283c0b20318600b150009488800765800000000f03001d4062084420081000600803940040c0f90000070003900700054040c82840c414015a00500380c0c800e41048505081d02d40f410038070840e44a003111005400e2501c25030740340600341c158294802c400440c10740c0e42c0c0310750044031800039081e13440c400c1c40408410b9004040f0a001d00102851051141411506040c410002000081c04000e039680b00c104505000103090070059640001c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 846542877 1250 846541627 846541649
    0x5030a1121221202030111040b0d0f0603020d030e030f030a050d0b0d05060f041b05010e04111b011d0d02030a18050d05010b040b04060506090f0619050c0105090106050109 75
    0x21002c1a02c41c0c09589109410350600b141d0300010615016035a0712440d1184218000c01190b0030181010125010302c0c81420051f000920100c003001100e034021000031054002c0000d110354681d40014002c44010034158002400100c4000540c1010000c1044264201c070003103050402050006000d4800d1002080d91940c8400300d0800584a282d54103c0d116403000544980c5e1400c070340620003c01c0c0031581a6901c4800004542d841c1c04485e0810040e240c06039249a61000300409002c05407400414035030a0f56000c0220b0780700b007552110700f00a000711050000c0340103041264024220b0b6034001441d039080d040007504861031900041202c0c560221030608410602e6041100070503503545911068001545400030020040194802104c3d03080c01c4504008001c043c074180000c5940f0350080310b42141c4c0030041c02c2410300e4400f41038019580000c203400d2602d0402e4014804000c012684e01002c00d5010801d0b0544600070f002d500d40c4031900d04004c03c0760501e80360008000192038800c9c511828 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 846544127 1250 846542877 846542887
    0xf05040f0515090301060303080f06011b02040e0c10200106060905101e05030610080105061b030903100204080615031903031b0e010f020a110f0112060305030a1121 72
    0x10700301003c2d0307080010014020042c5130b81d60b040c0074200c040704940b10000b501c90b410004091f580114100e0741c00c4290a01203410346441642400024030f80c00300242c1e09445a01250741d216510040d0b030a07940d510681e00c0d00b071a42e403446060381d500100c40301c4202c2c540e414580c0520a090f4011182c6046800440c0c090a09440d81071041d220384046000e600d107900003e0812523102c98001c0c0046001c1e407000e4410100e071f104405000c50392248207000305907020004200341e0750107c41140300142caa03840c19080d02d10300480d002c00a4a0240800407031441950082801c028200042c00b5155001d2156203481e0203503001c100c0004d85440ba6040284580030100540b501803611a0303112484004240c1041012607022100140800f02a10750480c00141c400e90358918441c80413036a44401c941c468001c1c520402c00c002040a01c1b4990740c643c0c2d04100013080b601c44030981e60b0265030000d60191010b503544012400c1c00034804554040d8441c1c1c6a0b1283e4240019001805010449500ca611440c2c1e02e80e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 846545377 1250 846544127 846544159
    0xe0604020f01110a11130e0a2009040b070206010b03090d0f1412090606010507320303070e1005090d1104180c0905060d0209340f0f05040f05 62
    0x2c00b0028020941c50f104d0b81d428481081105505060f05c40c90440f4900706c411210b501541c203950110700542d0701c5410420164001900e03440b440b11a502c61783c00c00c0030b410821800400e80c03041c000c45060320980e95500c18840301075014001e0b9400340000c40049491490511001c5030355182141d45601002003904080d0001441005411200480c85a845503120300d1440c41c0202c1000036a04008513004040c08604158000e07012218582c2d4004040c0c00030302002c803100800c0100454030b51803914560603540300d645006000443c071450391619118140384010003445414103001244a003480390820038078199a6801031001065071b0300c241c000070705c107081d400072a0252100e580000705844000300300e002000003481650041d1551384c0e0042042d60340d54170030800d4059450202a401611201c04500448141c80f01d41000150340c07520141402100104030031001d00742d25040d03000988400d4100343d890751244401d0f03180c1c4610b2a1960a06082020050400e07015102e4180b044aa02400603c0707 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 846546627 1250 846545377 846545387
    0x80703120f020307110c0a0f031104090204022706120c0c0f1f11120c0c012702090f09030d0207050703060203011d100f14010e0411040503010e010e0604020f01 70
    0xd941c0580003035403641400d078400b40050104c218021101d014640c810342280c24050846800c880203c100003550030310350317128404031380f410002d00b0303804c00d44450499001d030300c560000b0042c80200387c010b1006c01260000091749400401d00c0755100e418104000c02c203034207035152955081840f2315400d41c0d44084002c40c40d0310301003004000c24510302030303442c0000140c01001350450400010301818401d000346611980124803551058050b6228218003080c00160f225015202c1d155015000040035007400b820f82c458061301c1482c101040e00c6400e001d070114145490042d81024010120462604210721960389034015458040c1c03a450b8045640400d203c0b0811650300259080007046641c1d50b115680b0400c0b03910080c035020a00004100812a001d010f0401c44080f1140b5019070740495041421441505d42580350680c10042080250461580c2c2c0d4401c150800359503450040d51145400241070956007038101c0d10105915244c001501204007003a0180c0c09507046030841c0c4001861401a15 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 846547877 1250 846546627 846546641
    0x112d0901200706020106060e09040c1205031201080d17040c0e3409050d12180b1303110d05190303090c0902040504110301030f02150f18040606030908070312 69
    0x14039841500d070001038144d010352140003642c41d50b5032190103c7d1450710602c65070b50002e1b039006041003e44002000748013000c1c089011094400d01c1640c0c40c02e1148003010465403401e0f00510740d00d030400b05c0c134095180c0d0040c4506944080a41d403542c490b1070903031100010310b4032a1003000c1c00c0794070341c3c0d0015482d08044450422149030141d1000c2d000d4072121007040c00c0b920300c0e440c084042895484082078a25240d6100c20141f5031150728841414042602143e03e2400d044111051204a8101264041d40304014000100a01c0c4010103420b2035800c0c004002050003000d640036980107030340000030031408911609814090680c4c41580041032508070300500c4110f001400105042c000400c00c082c698009000f1100210b400340a81040e03d10b580d01e1500c02880700500d403d080c007440000600f090301210660362840d402c9141130001241e00741e00298015044085808041032100d00380e85001e108080242503145000c00c8840b400d80d86001007881101c102500b40074084171400441c61080c0c0000e4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 846549127 1250 846547877 846547937
    0xc0714030c0f0a021512010306020a030b04020403030c060b09390c06040c0603021222170d180206091203091c0614070906030e0c0301112d0901 63
    0x81c41e9502c00d030014544404842908a102e4480013070340048901464050307440c02101c421040519900c2e56540d0002544503000c00000d068a030030184899664610183c0001c60094442c20401c11007454030004607101c0300358641c4511081d40c18821031458845541090b1800290b2400700c0030b01546262042c080020f40ca0001e038000001d6a034070006c40440c80601032413041400d41e20880d101d030000c1d0140d005030001c030714203000344c040003d030390420001501d01d20548040f40c0308005400c5807200043d4441e811400b1080d884000307400130f941840f40c4120318008030810440984841190f0000310544106404644644c44090b000700d4107400034001c54160381c1d001401c0d003600f00590450103610448a12080d14002d03c1c00100c0000008035402880c8601c03c02d40d1209042810070360190001c043c200d501d07404510440c54200c0b070b262024400c000c2c0041010300c1440d164401c1102448881c590041486084000715141c0d046c003d0b01c800940d007807181d017428a8120441c2503c1c0640b1074941e03109000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 846550377 1250 846549127 846549133
    0x6030207050114010305210a08150d060606021c030e0c062124090709170a1403030405070506040b0d021806180406080d0c1b0521010606080c0714030c 66
    0x304580080c039a144843c814030351100d46000c84600d84258010f40c22340c0800b148588000940340400b000131905d103076074010460700601c0510b4440c1022514641c100b403016074440203000d0ba02c425509100212940c4a2805005688500d100291035078840f8010358040d00700404c42071582e1003032680002921041054040b003c1c81c7c00e03001940da05150a1b1000319441c0d03418012241c605103a01c51900c640d54a460f2150601d151020b8030f900d200f80e0b141d040c50380d4010000b00d1000509030005103060340100380c00550b164100340c1400707420b002d900c2d80a107109941c100020810200c15800303980c00c07007071030110060300c0711340001200000310398004209038061400120304880041134080d0f2a4807260a40d0b0410000351166003d03951912150080030202d1704003044030b4005000c9100f102c6000c0f01c03d40360303134207400e695001282d0101100071480d20038840a4000b0000f06c0400d05c140d200505051038920060b080071000071029101d094000707005c004454101840c0b4071000c20071982c03503040120031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 846551627 1250 846550377 846550379
    0x190f090c0c2f0d0b04020d06180302280b070309080405120307150c0e040506040209040504080726032e0b22080c12190f060b090106090603020705011401 67
    0x1203045440d607505401d942e081075419881e00d0303400e100da04558038561109198605803199002c002c2c0565042400b21500740e02d45012400e044da01040e0040c903d84650001d00c5e014199602c08940c4513050880404070361095900340020504a1a586822204a04002485024604010885119503001590490503101c40c18100c940c1c00001883e08a01411000016604d07a00c6014241d4400c2181180029020002500c192034590b02c100d0700320740022710051506440101043c103480044400340c0d12107002080c00f034140105219030007041106030000c900682241c5101e12100d004c05803c01c0c0b0819002800e0000324584103403a0440c0d0311307210340c0d0380d03914907030b5001c40c1038141c3e01040d148525001c001200b42600c14001448505444c4000d014214801a10050140042804030100e01c0c074407912184500e1000041c1c0d0b5a071a0902802008652480310300304181038440350301e0003d0280002000400060f0343c000015416a9540d240241c4e035031109003422805862100c0003005450b41c2a00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 846552877 1250 846551627 846551663
    0x2306030c04060813020604051507060c0f08070306030507150c0c080c04060911030c07020d120f0f1805060a02120f0a021213050f130c030b190f090c0c 66
    0x1001c0c00c11915a941c4010303c6654441845091106081000750040c000b0720051005140c001c81203c0c00800c070b15a800e003051503648410068401128420740071840e072244c141d601380c0c1d00c604016440032250900f03008552456072071a0381c4640174858404611140c030b42d44c0c0d50a600c40d8511925851300b00e401505501d0b210702d58180c40707071080302216100780c0c5403a0300090403c58601074a030100d100003031002e046a030b40881a01c0d00341d104e20300c2268000c41d0706041200107010501d030315410160540e5a418155640c4601500e100741a0104c0801e2000c40318001040303038944076070701050340c5059a1054881103600c40507480d000c462518910304103404a0003100800904000d0b000940180d401c59041c140441440b0740940318030398a14000ca03002c0384084c001410f0031401e00000d6039001c0c0001250161820b0168200c03000e0340f860200094480b00c40c2e040364607000c803198410f504a131601200b2180307820202c0b42d44180b030b071040b002e4043d12030790003444850044071440741d030382e80000682d041429a10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 846554127 1250 846552877 846552901
    0x306100516110f0a0b0d0510180f0f050405061611070b0c0607090e1b04030f060b040605010809190606030c0303090312020a021c020a05041803030b030115230603 71
    0x86964020307110b00707400f42c21070716069002800721070081800a141411214800001e041c00418400c80584074490000d0200e00c0d041c0c003445c01c2c0c1c1d8030322070000b01d940300705803048c007611148036505500300c0c00e200c00d02000c21030102e0910b0700300d4560080040840360091040d43c0000c0100840c1e1003d0080c1000000d04c1007050303004180218014060700d070b003507846a005965401060003203c071036941c103400264650754041c005421004181d0101c605003030383c80d030360b42088015030f410848810362250108851410300e400307188003400c42403c05180d686041d404081e5990100e1455599144045044405100e100c0e8444000b0359041205d0502e420b84074280500304511520080b07071400003910744450803510100d030050b5550790043c18500078090120b03050300300d1840440140ea01c0b9581d8000024147e64902c68002c0689448114031149006402c0c081d04840035412098040d904090f2840c002030304840301c040698000148241c2520101012102c00e405420540ea4000c140041031000c10007500c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 846555377 1250 846554127 846554153
    0xe0d050f071110020a0b0c0705070501270f051c03120213121202060f010f03030c1a151504030f0b09122706120408030a1e09050c12030306100516 64
    0x1b038141031071945800540021501c5070b071401030134075042410103210541c0319003400b42c00a00a403003000090001d820b0b51501ca0b864a910805804444000c108560304041d95480d210100d0f40640c2407a0142c40d46024020710700b030b8070301c1c4440e259000620b1496a5090b40080014100481162101c56840d15101c2c14840e034140f02940584140400070744040791406906060b02c000901d290340092543d034040d500f116070041e049821800348590b001410180640b40740c4101040400a41e01a20680c10f219020074880c180300180b0000308414008101e64981214510b54031001655a07591102109810b040c041849641d41e0900041c1081d0480c00181c40310804000200c0440c8610ba40034040004030720500307400003800c00800700000e0125642e840619404110041c000c100d845c41d008a04032882012105e081c0700554a468820510904200f080c002c9041900c2c480f0904124101d0f05540f0300008110358131822007008100d0101d40314205807840c64088400b6041e54042c245400c02030b507001c0f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 846556627 1250 846555377 846555383
    0x20310030c0b25030c02060d140f0709080f0319020708060a020c01060609050d02010e01090f1d010f050303070b090115090b010e060f07060905150f0a0e0d050f071110020a 75
    0x10700b040c1c036044001010001c02c825a415100d40c9000285c035400c0c05043c0d000a41d8031000150740c4c82c039007a81100c0000c14070303102d908986817090351440c11a10252500c41d05400050041e03121568038042d40c00000100c500d40760400b442144d2030406858124078281d4035400000190003170805005180b8500c0e00034004401620b0000d00010340c84090441c5c2c01203203441580d40c0440740001c40c030301550003036040d04084030043c0b4003040350b0707610b031181e022070b070415507100030ba10380320241d0840346001c00c420310703e070240a0041024505901e0400000d40d6800b900d000a032001000402081c613a010075803104c54407007000c0b004848410394036401c0500800e044410b00340458100c40b154203d40c5045c6044401c3d5007006520300c0d0400c3d4071511600010000f2402c110361910800d20355040c1800c050282c54494080e0301910b1121b46041c525050580f080d21090101c0d941c41007a85500030380d0841e0558031101c159080307458540000d818000340e15000d2500051700140d80c0410509100d0380403800703034001c4e40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 846557877 1250 846556627 846556657
    0x406020d0503101e1409060a171203330303040314030c0a12080f040201080c13080102070b1803040506030c0a0507020a090c1403160c030215070c030801050907020c04020310030c0b 79
    0x41700400f800104181200d1451740105444c0050100c508840035904c0c4082c103850440b0300401960301c802c0c5283c1d0050b90381021101c40030b00e400300110301014503d0707209401408440f0000e00503074046503482c0140d00004100a0408a250761206000c0054900030070207501258030038180d070305200207428070b245c0003080010100e00025003090322044007540180d6041c2d65400b102d03501c00318400201e803c50045490059031aa800141074142400541080c0d4098440114241462050055040030800d00380707100780c000344000c000c280d45840503250b000403500c50b407a5a500410f201110903102d40c003002980054200300108244400368400300060a0350346641500410015440f0f40c5070104581c5074850f004840c1506103064030880010f141300e4401e00449000a2103030301c210b0070304001243d070fa000044d8804401d2060581c013944c1d150041406540b44420750030804002911144200c100034040c40d000004a01070001c1114407800458101c0e440314280391700c0d02d01089841d4040306103503032441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 846559127 1250 846557877 846557909
    0x507080f0703050603251a0405100923010c02060307031406030102090d14030f0c0f0d050c03090909070513020d050622180f06020c0d02030406020d0503101e 69
    0x20301a104003406188000c0041c000464620010101e05192510186400c051b032040003132100e40340da0b844c000400e086800242c80300c5c2041c0c10b01616100340a2014104442c1810800005c07601203900714030040e151801000f21a92600180c44100b5a00002034001c003000040001c1c0c240c0c1076120140303280441a100c441a1180b4041600342e02554030400d500c0710032034911000090364100740008900e4601c040e00e003400b14990380003030b264100e00342c2d5041a400c0907110b0940c0701e4040c410328036074200c5070a2003403d0a162250280d0b81c3d010714000c1c03074090303a40440440c403030031030030480c908c003c00e002850100c404c1d14604280020b5004001c02c555102d007008081606417621096142c0f10040c8121403400c161881446039010304401c0c0421105142c422164001203002210500300c000d00420001d0394070503001c082d9270318101c4890702110442d001803005200c010b90118480010750075a10302103482e610341c45000d602481c090b40c041d101e400c1c4140000350395840410b09920803103440c145942892 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 846560377 1250 846559127 846559141
    0x7060b01140f0304050708071e0602060f040807020a0e07090e0609010305031c0e1c020613080405010e030102090301050405010603120801150c030c02030d021f02070c1a0d0507080f 79
    0x50401c00c0d0164040540600c8007641d8200818040c55002d0f00407011941d010303544031800d6041030180d800c04025400800c00001c184c1c00c2004c0510001d000620080101e85070203450442480d0b4003a00c003c208031400602d4030290360700c0c110081e000c3d044031030b51a642e6040400300507015404c0b5110380710407100c84100083c4280b4080711414120380d0000d002c1c0d0714044010680016807501c0c0e8500c400b9056490613002020b070b4080000b6101c00600d46855400400c118202916000c401007109490780b02e00e0044100240d800c1054504507102800c1c020000c20450780080d000e805000700058040d0310b00400c000a11030b0541010b01140d000700d07a8600c04110080c0f007107c5180c0b00340140c9144510450009280e00c0c03240c4d051b0b0b40828000e02d4940b080d1210303980001e051040d003040100c0140d1001404070114984040d120141d680d494804514084c010327651003081d614544034802104a00070700d00b41d1042107490884000701001c07c030070007039031404103c09842d880007901c078040c2140c5018001544 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 846561627 1250 846560377 846560387
    0x51c15140613060e0a390806030a030e01050c03090402070803040605060904050601150e0415080118030c110418240e0a0b041401060b0301090c0212121e0c07060b01 72
    0x6a5480d1104a40c25907a07050070240079040340d86074691504484107061103002418461030350000e10350100e8584204121b60000c2084401074130701172090b00440c4104000a80215201544003000e00b1300a8484138900b25460441c0914004550010b0000803040100203816000751b10940c0704501c100516101c00060020714101140c00070456840301b00103121031107250106052003503180c640070502c0c03203188011500b42d40403148018500007600500b44003075003080c05078a81d441035050940d04045060380380103040d21000480030302030108285a205603600d80e900000504018410341e58501000c62602103400c03100c1d91403040d08020308444081c6005858041d00d0303c500d00301c0c401081c54546a03211040ca103034021b041100c4503030076900305900742542806060000e1410350b1441c0e482e5031510340c0320804d4031214a400b0f03003150001400c1345103086604040d10300621650040c0324643c0d4610190301424613694002e03900c420906070410076802e0032000106000d41c41200b050013520142001510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 846562877 1250 846561627 846561629
    0xa0801090525031403090607201c2a0f0305010510030b0411010c050f0a050f07061b031101020d020d1415100c0b04030e0910051c1514061306 62
    0x180b071800b003202000820600300d400c09a103420a010390749041510340015055601440044580c981e945548600f5400100c030300409054081d079000100e61010051074a501c540383c00004c0600504411080b00a402c64403007030303048046184402180798403540003c2089030311b840111165801d01001550808650400c001103d5014052101c10707110b80d030380e502000201150843c10003541c1081c179000302e0802c00c540760482a40c90080c3c8040c02080c2011800c1052a0664900a0380505810020268000800100150070321101c42180500b40f508690740d421000e1021030302c0d0b002017548a1709600c194000c2640d03103d03a200401c0580001c2128008822084501e02a444000758840e2068207118070040e512121600e082440305090f6541c3d0700200e401610140c001406003c902412414000d4806400580d0740300b200b8a030a00e041c001542a414880070055454001244c800410100e8800b00300801c044134800d1115240654507109202011078003684102582120040c16140c0c41c45010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 846564127 1250 846562877 846562933
    0x3170a0207050d0918020a0203120c030610030218010305040507030605090313091407030b0f0306010906060e09150d0f050d0305060102070f030206030606030408130605070507090506031f0b0a08010905 88
    0x485c090840c0e68600c00940000d51440d0550001300706100c61500c20482080c1308201b0100300c40c0e10b078104ad40c184421061601d1048003414810812000740701c0c540d40003c615a0000d02c0d000c640c595031460424181341965000400d03407401c10042c0308016030301101070f2640c8420000c0c10030301940d4501c5480e058602d11a584192954040041502e182c80b80c3c0040c0b1780f40c1c00140412030b0b5541c01801103803074a942680040349446e51a0401d000c096485408114011012505039000d402c280c040d0641c48400d00013460300c6404101105002c02288248001070103400c8401d40f0715140308107002401514084a000340103015543c000300d1086845409141039a802034022410755803070000b404066800504141c0c0c40160a010024513145520849009030225617280c03070301c0380481c4c9805450f21007183c00201030241010100803040c2c400240f071a407801010540c489a11803d03114030b0004000790403500e0307003128036180c0105600c40f054008103040c5110300b04540c80b00440340d82c4174003400c0a150500c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 846565377 1250 846564127 846564149
    0x105160905010c150b0d030305100b09101b0c12020f040614041a0303031e1501050706021b010501080c13050c04030f1103030313020f010201062103170a0207050d09 72
    0x203600494203071071031300391441c00e03000c1d00080703c618a000084810200b02d0b821000030342c03aa801c109079100310400503002403190171002814002118000f480050324807000900f004240f80a40400c0c514003103004102c5070b001100b0000c142c1d241c1c81240303014080c0e50400c1c3c0c0214a03042521155040c180310301e038110f80c841d50a505007a007080c2c0401010700741e0510062100e002d070152110540d901840154004e5540782071115080f100120040b00303106006046030711140c4072440c5240581d803c90211146150702c03040041c3e881c0601440d40108401c8040140815840e110001c90003010020701e9419803e0b085510016161604002c3c009943c0212195001e09409001c20800648680031000d0038900c81e02020100100c5800880c0c81c5400807a40c001004808030650410f40c1440500d02504500a10007403001c01e04050700ca0002d40071f0120204054890a440d910906110320681300d01c4104003081c85099040082402005c0d40107a00262164000c1070030780581c69001d80c00076011246641c8032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 846566627 1250 846565377 846565397
    0x2220e0d021c3c0507050604021302070501062309130f032307020117100308031302090a0b01080105180109020d0e030a020717011404080307021c02010516090501 71
    0x35000400710041c54a4083c44100903101070000100404000c018940340203c042c020300b0b0720b0494601d0080c0401c0e10f418000104000c0000c144003140b11a40290103403000c3c082c10fa490303a1910024800c000016106500c1c01002048505400640541c0215510051190715400004000521406644d01101d20620b81e400c2000251401c49045056010f41403040d01c40d905a032144d200c1000389200705048500c001800e900f1980c01002c2920f00b05c43c4503024584a14100c24000540711241c0030241400c44003200084150b034803030038020303540c990107001d0680500f41f07164144081c0025000c0c0030b0110301458000705040c11300b41b841d64856041d1054001690346004250002540605111458a5210743c54558001030801c01022401081d03401400d600f4540384d14250910703808001d008207641003001c1000100404002c45400c130b42c008088030b17580c0d2a00c980c2a8a0042451000042c010ba5981c100380e00c65019440113108262010b43c0301641318440c1021601f0800c1402450302290161107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 846567877 1250 846566627 846566653
    0x10302040b071e020306040f02010210020f090904170408060a0608030c0303040b040807020a0b070308010e09070b09180117010606020616030b03010b120321091e01060302220e0d02 79
    0x210a2019201003d0707141da4520358010a045c004120340503500b140303c00402d282107503410003131a10002c015103411810709111340007100f0688110460913225210100c013080c240300c003480003200a4181d05c02140e544542d41ca00c0d864031408111005041030385807900000d82690040125060b50b4124005940307580e4590b030b14640d04642c054010b440c045814441900181c84006910b00a0300c52280aa522050b00303140050903094140c01c004120319900301406031181000a1060544007030382007041e01c40748a14041114601e1a001101c40318200b1400020060111420781546a0040b0001e21030f031502c1d4101039a82c0c41050b10808a0204041d011014451007940444d008407801030002c03a0140c03440c3c0005001c1c24060716220903540001950340480c9260301c40d5144446180c0359046807503e000c2c080c59271201e400c0c0010618040f0304240707408903c036083d400071f0003455008010f42420f46081c440a446042c1d812201007059182214503e0120b00004090800510b82e40c0140705500e101c0c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 846569127 1250 846567877 846567893
    0xb030a080a1d040504080c01180c06050c03190504080709090209220f08130e060a09051e010801060e15130e190503031e0c03011511150403020c010302040b07 69
    0x2c038162850414103100b81c02503030703618040c00d4021030203004a551511580070006003100c3c1c01556a0302042d0004000e140041c0210600e1412a111810171584441c0307240c04503030462284200160546110654010141e500070001d802610780040850f040c50b6101c1c4e00080481e04100006580b25400704006282180c0014800c081d6105150500445004951726101340403280c60003212000300214600c0c00b003280030741307402c1c0040c441c0d104d02400c581041c0020540011040c05011100b5071906c0c001005200e000c21081c01104103412044400d43c2e442d09114000d01c0603000f10310304015042c000c03a01c038025110644402040003031002c40c0030188009000e00030656880f5200d928040c405c183c980a180c081580f11001c0e001d0703405980c0d41c0c9000c03020440d00000d141610501514800f00b80032200d000901074906585980a403920f40030b051120a5031100f00b0242800200e101f140c6940110700f01e0791010074000c0b8426003c441c04140c0110043d07099004178014624842014084500416004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 846570377 1250 846569127 846569147
    0x3010b0d0c0c06050a0603060e0304052b23011a100e12010f0e010b0108160c050118050a0b0609070c02040f020d020f1201151b031e0906030b030a080a 66
    0x2420004400040c0c3e90f954401c3c0c82045800801c400d5440808101b8007005004183c080941c15002e10319107410030700040c416601c8010407090810404d01c40030040888611380d4011175070401c02c3c0300480450412109080982c00038080110b500700100190b041400c51804028040010035070b06003501c40c0d030011106651503000781c03548244151030b100381c000e1082c4902101e10010b088d0110b1859a400941400d43e200540c6003810000c440c3c003001402a990032040c040c10540d4584509164807d090550140c86025003114008140d503225108100c8000342200c1c0217481807840d40100c0d034609040008040044072404049000520704400500d065800034200042d820b0700182002061445803040340c0142c1035800d549800010440c210101c0411903038018416441c01410959030584014520f04140040c590040e441c01401400c060040b428285021030190041c0900103150f000204213882078400c80002c00d10b8128100007070f00380821801c0900307400401032880d04284581c01c450440c54 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 846571627 1250 846570377 846570401
    0x130602032d0f160c061a010e091b030c040e0c03090c0a0e01060c03021510031e4706010905010203041a0c0a12020313060c150b0607050102130e0c03010b0d 68
    0x2c2104c0b4880012000c1c89036888480008480b0034240b00c0318000940f81d020540c01043c0b2810b5400104002d50714090402202c418200c43c50399100d44901c0407001081c0100d8021a0086003580c003000000715a000c041c42c850303001e4070103e90000c1040018441400110f00800031400500e40061003c1d134003449025a040c0c1c0700c1e104031064001030b40740042c04405d095403401d800003403a0038100309000c1c1503581a0742904020220b440d11104a9541c51513000070850150905030381c1d0225a1200c178510140074006408006036a40d0341d00100402e4001048101c0d40a80412040b03000401d95510006c1038030180d840228590440601c1d10305114045d801c804090034480c8204101d210014217642000740310641c0c02e0f00210348a00c0190403a40b10011150401003c0266521070000418280c2200014420401c1c3e000500301000c0d50114440b407186441c040c1056000046c001928813000d5000000c0350301e0b04181c1c5070309031900b41d0303002100d00c020300c1489802101070043d503440b00d00642c040e0340790180c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 846572877 1250 846571627 846571637
    0x70b0f04410601090509300c0d1e0318060203090118080301030c0510020309040507090923011a0d050915070815060c15130602032d0f16 60
    0x11044800c00c032840720110161203542c11503401003100e000c0d1809840d07089641103025025080c007000c1c100301040308600f544624804820720000407158410201c401203103130401039440300e031201040986604403004120740e011042d80e24082200f8840c2c1701e54640c060086c03040d0840740805480f000c000c1e42014003040a155aa080841c40d0b083c0c1045038a180c4c5803161502984942c5941880e01624225900040c02440078101842e0107603404000c407205074604950000b221b40341c02404840301143c07a004111078920b001005065130749040078100416038070007045038441c0e8885105140a54000c0000009020300303000880c0040c401d030f044194080c1490045a020281130b0664050a8009455070f0020420b8002800084100962282100380c0c064074417a1030040114092640d45060750280801640e1607800708440c1c07608000400d8456801c40b00a5489051025028411044038a000c034880021544020b1001c0002c2078420310601e107400c00d505565842403240041003952400d1802000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 846574127 1250 846572877 846572963
    0x2040e0f0910061427090106090609020a091502012405030c030d091503060f14181501082e140108010312050a0c0f0305070b0f04 57
    0x10204a10188501080c484a00301030500e204140d052101542c031100d00581803c00070700200c1c2c40b856020110190a5900c103c90002114200700c2889800c005000b84040398420710140d9801500301314290740c0310a1040000942d5041080124811208000003046114a0400c14003401c558403060802060001140ea58640309210b80b2017424082240080070380740d54103204a04003007081c181c8005045d07000f0003580340040b034060000085e5104442a0109038400ea4103028400d030041c074014190803d0440a10b512048084100368850396014040e4003800c0f0010382c6810481c001c0b42c003a01803180da42040300b00d1b03d401120030b4480280b00d43c40c1103001c0c8000f580c0390040002c008000e000d03420b0b04030083c5410050581462405003c00d64100300315503005001141c0c8444981c09483c0c8242003440e6140d850b4402500e41d01080d110107000384503404c141c0170034550006c0080404d21303c02d40e814031540e40c1e0b900001c0c0b00d0480580d0086e020711002c0c002c043d500d1201c000303010314817400380000c2a40c1f0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 846575377 1250 846574127 846574139
    0x31104080307230102120c0c070806010806070314070c02040c09170c010201060923091c0203030907150f0f030b191701020a0f0c02043b03040503100902040204 70
    0x10360002c10120b400402c3d490310800d60181044843d0b1042000a0080d40b5008010078030030000c41e405403c2c2020940006a4030060030402c01400c8020403021003550300d1580d40300940c81e22400304594020110303040418040541740c685186034803e0901d42c84d80c1c45001c1c1107409100040118021190503c481d52101040303100d8000c42031005440408010b1003d0780801d0002030030344030700743d01c034841c400d0070700745450300f0b000303c00c0c2000154020000302a003590b5280da288628110242d5051034155603843c540c802d9540c0d002c00214410086e6070101c07a4003966a050304a070080d040c440c0c0c130780000d81c4080710b1000c00d4454000700201c1d001d00c1c0b0300429103540220014200a12066020410901d102010132942001000201c04195040021414a108420003502c4014034110081c100080d06124500b10350f07459010618401c24140d91070210b40d801c01c03003000255000e00a071100381000c0200c00713100c51701c000200d07000d881c005805010074040c842c000030060b0880c1d0030100e034400e809010100364 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 846576627 1250 846575377 846575383
    0xa0b07140d05040f050f0d20210c12040b0301090507451a0313080d0507021c0f14222d1a09030a150f06050306010603110408 55
    0x1140144401c04940c01c017031502d00d240500003440540203800c01200030950580090300340e5100b121900004510b041c912000a0405646100000791480e0751004104503a51880c003a080c916003080c200d41192540034404e911601451061060074002000144203aa901d5000140c00807620705007142a00e21900d41f00288180b002d0319030407403604044285d13068144942908105075040d03c04024128200b2102c00714400c0c1c140e00f0203900b808000f011032240101172030b4440300707107800085194940350703000c4840c005071170252102c0340144a0890707400b00307114a41c00200d00d41e02c52619203000c0010421790035140402e80070b00c0e01c450200148800c0030003140001c02d10780c0348502e51016102641c1030010303000b080d081ea034a40c00116170045410302c0310344100e1001c90307003600e18030345c80c030403d0404903448204240303e00034a560305802080f00800c2041140c052411341c1a01685c02444107000c84600b03182241c8491241c20b9055004d5801005642c0c003170f500000811002ca07103414581034541000c589 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 846577877 1250 846576627 846576631
    0x120607050d061212081e13030306090b030601140d0804030804050a06051c090c08030a0801030302060601030e06010e1008070e0403140a300c03090c05030a0b07140d05 73
    0x114000107602030001d078680c0300b0400a0502200d4610320380c1015201c5600034020040d441c0180201d54000c2041c0040c3e035032003540c4450081c480c21100707241403c1980d41c2c4050001c41100401c0c1083c8010035a803c65008001074480041c0c02010f90380e19000414260141c11409079811600858180c0042080800100080c502581101d0340d500d2410703051161401c3c0e01d0b8485010404180504188114101c1c1c451071415448400420811103078140740c010501c0aa00155085c800080c110b0b1146402680c858100e0340030390283c880b695202c071b00540541d09114502c00c12504450300511000c1c590003440d0340c0201c031046105900c0c90301d40c0252441c08010b45c21019102c0c0c0b0b81000c000070181e00840b0f03c0d04000b4034410301401c2012501010b0207999584942d510306004403555061800d0102d82c02d0003644601e01c000b80008090004007030b008288a01d42501d061000f1034002c00c00c0d0400148840400b40c0c848101c80c0356a4907000202c03920010004d03001078900d0100315000c0810414000c1078 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 846579127 1250 846577877 846577891
    0x1501050915030f161409130c030c02060f0c04061214250f090e0a0e060703061706070503010b030c0408060106091e06200a0602040b1c0501050303181206 67
    0x282d036030030302c40d401c40c001c020001c03c1d245410b05084000031000d6071100c0e2014181821861050701d0324a4200007a81102c03d49003052425413403c002c4688556043d08140c21440d220703003d498040e146d0a0040701002c00131142c00910420030030081084611507420500580b8950305c0008200480d00d0f410302a40300c05483c404900841c90020079000c0d42d11800c5c01e00042401e007003030381c4c2007116160050102081031060039068602800010b182e0592a0000b1500c1c08000e0260f071858038001f00d01074000c151070f0103000080601d442040d20b07281d000181d00c5014010a4542e03d085070b1a10742d00d5a030903400140100c1d0000b100b070100103441c2d00104203840c040c048c0d0f0b40700c03c400c05003400e18101c1031201d0155507108160303519074100300c07040c0c0169001d0961501e03001d04c105182c036103120303152820103003110003000144009400280320f124000a0200140c52303014034441c0300c400d80300b50000d8400a015079503141c0c1042114649481d608a00d40c40d1005015000c130710035160700d1400c47d06011003103590b5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 846580377 1250 846579127 846579169
    0xd0e03011d0d020d0f08070e01050c0601090c020f1b0402091207032405070f051b060c04080f0303010b0306040f1d06160201090b161407050d09120b15010509 69
    0x482040e0f0140004a80c0c0512480d240804081040d001000000701900610602c03115100c2c5598a0344075004540b0900c03010700890b03206582d00d03814900201540c2c010000140252000020350000c04200403140800030081110a0701c0400e040200960010028a6201c03840b200a00310002052041c0d000031401103508884008003071050044c8140c083d030f4000f020b107250004101e40550040da486499034400d1074525100d0b0035091b801c80300c070344400004481c0762083c9400c0042c5800078038010004d035044c1b03200383c8101076100020b050b40d85c01f0038019580c800d581070000501609103948a00d46108820002282e13040710319150180d041046110980642c119000708080891031a0105035020083c1c4020811a10755486406213020060800402208515a0164068030804400c80004a1070300d00d1030b44d50800e46451699403040c280f24001061030580006071722a181101620350300d42040d140f0403180d030f940d03180d40c0d04403018400a605211042c4001075407503c425002c0c450640642e081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 846581627 1250 846580377 846580393
    0x1d1203040c0b0c0318030c040f05100510020601060c111003020703090506090a060503040c0f060207092403030c03091e0e1506090108070e060f04090c0903050d0e03011d 74
    0x14007900000c0340c02070b040740c2c40308204201041100000300c450081d112011301c503038691498002810426818a5581d000d0b0030101c1d00e06100b00706a212074000c00d41425502c60075640d650034094012104004d840140e0003030030040140c0b42c00f5101c40d600d1207109468060001320b000c1c0000703c130100e00303030402d60020f580030405404068001c0220310141c10120780d80f504001480300046c03140c810034082d0800304280407010070100200d054a0b1000f402401405201c0d16445a60003507642d400e6115040c081c41c142110b03a591445185a12a540020f00e04400c624600719142910310401d0a502102084803841000812140d0407004007040840801044030051400c03400b64015100a8080340d00c03881050120141c940d5140b0031940031a40c01c2c00c024003a0f0b82c80c04000da5244002c200459004032001602041c60416039008000707462030340c1020800f8400b01e8004a60344516400700514560040c5d0b5400c5000d4005d4980041c525002400400d00c1841103a03081d40c940d000707650066050380f000c52 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 846582733 1106 846581627 846581633
    0x3020301090f0b0a0e150612010f0c020d0503090a0f02030f070e07030e19020618220c0f09051306031b0326030a1d120304 54
    0x4001c100500140c1441c1c12070041407603045540d1051400016184d4009201d10a0003045480013000c4003982e21841200a20010303020b1580108500c0800f880f4000174003e0001100a9110200d000e031280080030345445103c81181080c41802d108114600034006107210b003076034100064115041050000c07a0a02e0445a458989406100710108900da03442c14407030700a103c0b41d60100101080c00c007860740c40f090211001e8806044d1104d440001d0b260100140011209030f007202c3c201440d5200028251741d035411142032152007156103803140d03c100343c405ca5070070940303d0820b0740704543c040c00010440d4610380a4284517110003151200451481d074000000b5542c00700304190b11041e400c005076080042440300b1501d4510389950074507034902d00c10034421081c02500f2803905581751a4501d1001e0b00d42c031441001540303c4001821090003041221440c10703002c1c21100d603640d0900342 = true := by decide +kernel

theorem cover : BRFrame.Cov 846402877 846582733 := by
  have h0 := BRFrame.cov_init 846402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 846402877 ≤ n) (h2 : n < 846582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
