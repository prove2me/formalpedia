-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3426
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:37:34.862096+00:00
-- url     : https://prove2.me/submissions/786473be-9fee-4a5c-a090-5d8e39c2292f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 616007194 ≤ n < 616187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 616008444 1250 616007194 616007233
    0x10f05090c1201231f0e0606070204110c0d091d0117031306050901200c01031d0d05041503020711090916030503130902090d1e060e0304150206040302 66
    0x24080c42c81d42d01c85004100840c000d0344043d021030380401308880b0b2424460700f100d440c8505104030742c100c0c01c4030031418040050081ca41c10303003011007290b9003640c4105a10108014014500c0040c1c2c4074500402c200c0d100c030b400400c001c08644e049588240005440311641ea2429840341101e0400102d064014031010b00040401103887c8080b10403a810b0500c0d00c100e0411181c0e55806c80ca002030400705040c07200c0d507041540700030900da4256034503200c2c3c0246480030b6618010304032200c1c101a03c0d980301600c0506002103a003000340312130301500c00c10b09000c0005402540f01d8400d561500301020030800c8128820f02c25291500d901031140e10541183c2e40420080b8240540040040e00a420740361205c190140c039400300842c401ca001e95120f0004118041ca8031140703502208010303004205190582d5580d480016440c0c0d407100e0040382101c141c4415440b4070b070704c1040050003c2d00e00f060201c0c0b03640c40000a041160400800c0030386103020360310103c0c0c0f0b90f1340c1504d0040250b44076014502d42652486c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 616009694 1250 616008444 616008469
    0x41103073c0e0a020702010e0f0f150c01050a06060e090103081614030712090512030712021204060201020d0b010906080a090206271c1205181011010f05090c 69
    0x300010341d41e4591001d4201c0300c400f0364150700100d600182010465820088144032841c3c1100c400d16094062408034aa141000280d94424000c40c1c040b9889245010190780c00120120000c128910300490081c0003000c1038018a00440d00c03036007500b9100c0c5441049103040c2c0303500480d03c41c280694107161100e40f20103c442261005c1d41c520020880f640c0c00c1010786042c9005102e0444114035160019045c5242d135080307240685440c7d9a03049100c00c0003c116010030f5400b607400313103120b600d491081381422480e08800000c084009400580283c0c1500039104607200304400304480740d80c0400655500d203043c0700e40030109503480c0000e666074400707a020440311400500b8461401c0400303031100305182e03206502e41400310b0003419005018248202c403404828140c11000111012540360303405924032401d610340c01c01c603001601c505200c0f83e6824800500401410186008603081c10280114461540c03241d190748c640750b21119580c20500a4501440929000d00855044c51041c440d4964112 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 616010944 1250 616009694 616009799
    0x3051206010c060e061e13030509060c0a0b16030525030e01022b02030702031605070f031401050a150b131a0a0f031104090504110904110307 62
    0x102d1000e00460303801d01401300d0241c02d06000e0151864840419040203103001c000c209508801420003c000500e22480540c0315054144245c441c0c45241c00500c65115020024079103008001b400c0040001d94403c15011b50000c107006041c11008001c11402c64904a0349451290000810686c11419a5020f040e0020151502040180400f44801d0130f80e071020481b1001002050a41c0c2d401d0b4403000081140b5220f00c003020762550400000080d80ea000d080d840401d202040079030701c001c100c010011b0000501609880c103c000e07940b410300c000c070840354030310814241d402e03c800980b040b02039100d40c01100c0d902c40c48a003001e0303082c20105c2032140c00048101c031504040c284081007200858554040b40518048042c0c0e5030440658010401c20001c00c0c9803080c5402c001c062040001e4040985090700e905c060300094940c0d4500305041407514002030103801c00c0c150802d101c14030002c5d200d9110002e900b0f030100c2c0c1e00d090b6106070fa2100c418050820180c540c1c001a240c031400503030741d500340602c01042c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 616012194 1250 616010944 616010957
    0x1061706100e062a1614040203061903060902011706090a020a020c031b04270206090103021b0a03110f1e0a050708011a0108010302030a03080619120c0f030305120601 73
    0x10950602030b01102c50803040e052410510011316001c030b0412803085069641840003640c90f00d8203d503105003800e100140e9100c0c40d004800191142c8407000c0e108020078150820b500302a54070304240005019104050380012a04004038095481d8102c1041c0521070182441e0560307520102007000030b410038107540d07046005420685500f40c0d408c00c0548004100c0c40c1c0000440100ca404000888244580c03040101d90b205a0f00200e0040d00f1034410003094041d039120342e540b0719542c0101c2c001e1085105200b1400e0180e02543c620f014005007040099100f5202c1224002c4a84011170341c680a0700302c2c20040e5030100901070561780c0806c048105e003d00480c101c0311071480c107039601400c144454001c214507039940c1d1011121019096100c90005800b820910243d50464012030703181d2138081c40240920203080c0100302d40e501c1c0d02d02c3c000a00132203c3c411080365615407100416910020a00390b44843c21090045945a000500c0d641200e9144d21420700c0d04404503641d2080750401040241030015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 616013444 1250 616012194 616012207
    0x30a0305091603051c0201060e04030f02010204380415050c0a1406070801060306030312150513020406020c030102130e100305120417120f09150c010501061706100e06 73
    0x928400c420243d03224002602d90b07103141030040002080b400440c84c0440e8101785082180c00700f003010194100b501850841c4003170f461040d0590281c482d41d03101c030890850595002880f01c0c02d229968407200c5400c0d900203148986c0700030301184d80c01a402805440303001c80c19520162070103080102804078024084d41d412280640b64040824400a0800c0c00c1d40c00c003d041100d4140d1046c05140504120700742000f0346400e54900500c00070700e1a124800c0c0079a19443c074440b8010316640040140070040500c00048030140030032002c2d4001d8422040540705551014a081c90107000b80c40090b4904142603c00900d0f20140c0441c0c83e03406009054448580311300480070400c03d10101d04e400b2281100c40daa114509224074002180008441050350414250703400c1d45803421003250840143e02e05510384604002000aa504d100401000150800020700d41009141034001c0340c100c0b2103507161011801c109400407114002e040310055800011760b404011030070b008403110021404042d181a00300780 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 616014694 1250 616013444 616013473
    0x50f0f060d020d320a1515110a03090612050c07060203060d080c060402090105010509010f0e010e0a08060703111e070618050a0b061008130206070b161403010305030a030509 76
    0x3c228602241ca1184c96020508281c0c1c85501d80080c2071306002c01001c80010030011300d9188a0041c144184c05100008840b18415030309400302c000c03910150340c0342a40501c0c0c050702d2550284203902c040780c80781000490700754841c80348604c0b0f111440c856502e8055513680d480000d600082851364400d808401e40b00201e144030b4050003d6052403070092001e41440d0040014849050b03101504018080200c42c81c5a640003004d046100014103200485074080c0006130307090f541c10844583c1040c1c2a807000144548005400c40c0a192252410422058a030701c5040082c403410010a25601c401c0d40880d82044c2c58a000b40201c1d805144000340002e191400300345000000102034501c1d47c000c3d81321400f480741c1c206072130340c100300c00303c0c2c1107007600008046c0504060402041da013003c1c06400399540554540d8011251003135804140e601c1c46150401c030004034036010640300c4000419040c40103140807424001c40703042e26044401103061070240041280903001c0100b21190a01555503d1030030907 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 616015944 1250 616014694 616014731
    0xc0706030515040c0509040f0e0a03050706111306050703120e0303040209070e0a0e1510051b1b040b0a08031303020310060608010b0f120c0301050f0f060d020d 70
    0x20581a80c021030035003441900c52120440c0228042d105034540044041c0840d040000c4401140085d503010030008007c4101c0301c020042003c9111080c000c41c603100c4101603000c00200220b03807081c0f0042200405945040300c2d0790152003031100b40841d103c1000c0c030030a401140038110700380c400d1400c41e59280d503849a241c29121684404105a40040140f00452901880d890b41c40002880d20540c41400d05c000503103450b20902c10302d940b411041000c0740002d2a0054161200200a0003008031503910b18402009503000300038415603030030902594903a80e4004580c4481203902da0706004200b21801e41040018142c103100305501418641001a2444050000c0c00e804002c107110343c840a851401858181030039107444402981c5007032804e04c2000e4101e07420300d041d1440d4001c900d4456074007603035003070b805d20a08c00c040008010710020481b508414200075816241e044c1c071003401c010760410034441c804000e800d42541c045814001c0c3c040d00c4000c1e50141032465443c0d803010804c540c5c51024500b17903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 616017194 1250 616015944 616015949
    0xc080a08040b130f06031d06190f090203030a0504030c0f0602030d0c03090c03081305040203100605090d060f0501170d091404090204050405070501080619150509040509070801050702032a030c07 85
    0x444d480f0311030584400310641005001c7c00c4007002424062074482c01030399001400b51500840c280d61801c10901003152580b017945c12035070240803a0340da90030401003d04280c10500c070454054003031004c0070400404224064048500640080d804c19a8201045002d050540040c0b401c03d503a4848100c040740068081030001c5005070a1150345102210313011034107032442c0d0045800340b070042041c00074014004200c0c8080b01d4143ca009503c1e48040000076849603070307142c0040e0440f82410710714071a10421358003c90407200c0a5503544240440c00c8195600d42c0200399600d804034140403001c00c5180b040161840e12404010400a6a1044d03035000404980042d038040e10f00380e124030418001175070880c12198100c00c04849207030240810a610f5948400c8034000c1156006201404000c03560180054039076030000103000303100300d18000d03d4142d621040b910402c03180e5820300340403e9202d8004800c8903460a04200902107004105000008240c0c082c1d1108081b40700820124204080901c0008007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 616018444 1250 616017194 616017197
    0x15130507023007050c120705090a09080307080702101a101b1106070b010902280c1b3503090a050f0d020603010902070c080a08040b130f06 61
    0x6040c205410002c0c40c0c03181940403906004aa01030b0402d4508242203000c884007410103055554030303e80d280c11030500d10032020540c0c03c514500b40001a0380d10100e1aa020303140d003030b940039035039940302c244200a45044a0001d00418410408240800d1080316102ea002803d0300455004040c104140e07000c03110a00e0403445800321902050416150412001c61004290310742007418030121300800740c80100c00c102c0240310405041c1c3c4840703607132900f20544d007071990088020b010310b680d01c6e9248406907000c02036070011b80040c01041542000c3c2e801740c0e045003408507501c8074141200740d40c6101071005503001650491004160000701552240301480070840c400c43c4008088035541403600b40402406041d030025001800070340741986030140e00c0c200f128000c461005ea4804464040341e007640c0c070480080d41041e00000040f820805507001095541d1107400015083c6035105030380c60b00d922070580e0042c50f50138100020800d2241d10406000310000411901c010301d9036600c1d4105250a007030344a01e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 616019694 1250 616018444 616018451
    0x110109051f0201060f0b12070311072103050421030e03040306060503060a0504051009021206100f05030c0a0e191a090109020a0e01120209030717010c170604051513 72
    0x11070a03820302802c00105810030701800101d061030001205070042c00b01c4c00c220b0404003400206054840d4020100410728201c819940b20510b0a00a8100345108032041c03004c0701d1114002c0185111b413290714800c07500903100c6504104c3c0b6618030003884184a15031400c05071240d125420601d4140000c000540c400c00340042c1c0145082d05041c20b01d8401004040740034074090400010803030202d40b003003801d404010002200300061001a825040c044501002c03441450200a41034580001c000140d40c052654030802c141e95200701551060203c0c0029008401c0441c10040713140c0c07415202c2e81080a000f80c40d5030301c0a15001c9031013210558042000b0507811403c0300600c80c01c4c4104902e0150604503010361410000f65409009108070302c80e40b5041242c09003004040c540aa81540c3d034021004080d9402181d0740c9151607102003808131400c0142d4030381f40740c018030640184480b0380a00e5203941c802d800307503880900300b00080c000100b41d86041e14502d10318880d95681c40c00060b94180e0000c4001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 616020944 1250 616019694 616019749
    0x17030103230313050919021818040f060915020a08070306080106082a03060c030618010303021f02040f14190509070509060702120f0f2e06171c05030f0411010905 71
    0x2101000d403e0713027400048048142804045808d41c030001c001950085404914104185451041144c0c180802e030200ca10202d80401c80c81d500c10100ba0080030203640c02d010042d1540c04075400c81d08203119145d540d90060b41c02c01c2003102d083d9a2014030380c0c050090b990751800c075070307012078200002200c2c075030300c05c200000811006113040348103800d04060b00514400290b041d5038002c0d40c0c0e050000c60b50780070b0394200d402107921070b1000d40403200605014001204000ea6561440c140318000844841c4034030701d00e4141c0018041c4980070501240d8000b0140c40707080d207441c40291055440340320300c1034000c071301080000c0168903081000403012116500500b032400e10000032608220040410350115089450328458440000032181c40d02000d0386030000020519407201c07402004103900c4180e002e00c1880354484512030200f00c504c94103104075102c40400c490380004a9023880103c440180c11610032000c00c0104410381c03200c0b44980e5042c180841603d032600700113100080325501d074039808000e01003071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 616022194 1250 616020944 616020949
    0x4090f0b0702160e06011b060e0a051203150d0615060507111005030105041107050a0c1805010b2a0604111309020603040609170301032303130509190218 67
    0x5000e006074a8500c60710913424107075519038814002c0c15450421441c2e00704c1800c1113030002c40d1038003081d0b409030003008030702c900c1400c841e02c490700d414007550b50340140214000508007031404c4a10901c219a0030f04410b00400e020050075440d400b0040d254150b85681b9192144240c45000c000b03488580c0b10f854031102c15140c1802c4416007442aa80a4005281f03659411034010007581d0555030225008601d100e610300c2c1c1c006c5140100e107000381c00c07031245010120a00c00f052040030207540700c088460071031001400e03d04040e24000c0c07081c00680c1e10200880051002842d00100e092101906001504500d46d8003c078601001910140c0744410302c80d00c0c01c4c100d45804070b9065002c40c1115403e1151311541c0d000a403641c00000d0001d40465140c00c00e940c10024a15541509035201105594895840c0e0508041c94212401c40440021070040c2c8001140700c00800d584410341000340080d051030405e4140120b000b0040c0c600024a041255409040003084c0080c10340300c490641c000c40200d400e41c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 616023444 1250 616022194 616022203
    0xd170c16080c0306010b030c0d060923100612020f031501020c0409030507140a0803180c0409260405031902031207031425140f0d0f0e04090f0b0702 65
    0xd0307245944028844019518040356650459600e181001e480b95141c4410100300d12501a03041800c1303182030404501c00105901c070078161500d8603840d185034071004d03450159044040d10140000c090003c400c12000c0e00c0380145410303910b1011005404d04c6041d0440c0980e68000b03442108a1048913942450b41e56410096200c003104125418040c0d41001d46002d4524407423000082e045d003010380d0b85400e000408100308840710b50302c603a440f80e59103002c940d95080704000030781c00700d40760150822901c014500b50003010039054200006442155014036801d01d15000c0d002405045074040c0000106641c1c00d02c1711244c00c031443c80c05020203001a10403d410282c10018440c20200144200c0c40841e038040080c00c9203807290888641e5490a800411020034030301c6210224400b13840c3d40800c204412800e4041796114118100d5840701c3c81152110388989000b102d5100040e0440800544a8030904245181c0d070300150001811260359184c20890300d075500801e0303d681e4cc00d10144003003940d0411 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 616024694 1250 616023444 616023449
    0xf13050312250201050c0f09180c12010503161e030501061202040f0509031c060305030a0c110d02010e01230d06170d0905010c150e0f0114090303060d170c16 69
    0x10080020b490308000e56111405040c02d4000184004075550794651200c603211500e5401305a4161081d24040c019081940d01c9206c04503194910080004de09080001d018040c202c503141c00001410700f00307090000e40c41404050b800d0001e0b8030117000408a2030038442c801c003038001c5001c2800070106500620040d940c01590b0458058640b0b008c10214000c04020703500074001c00f02c40e10044080c000015405810550000340ca81d0000082c1c90070980c1d0072280039801144580c0e003103d1a1586602000100040381a004c0d003c178081c8d40903070700d085d88a00b80d050104e00c06410b0506000c00c000c4410055500101050100c2c640e031a441808120311850600c000e4902440091610304411600100070101911a42d41800503122506080103190883d800303006062400c01c10280b14440001ca565444814580c101ca501c2c024007602c070b03480c580112520a14a550056245d40c4560707017030001d60542d1030800d940030680a032480410030851401042e5080e8060020018140f065498074039002d07003507 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 616025944 1250 616024694 616024697
    0xb0f1308010b0319020a06050705071e2606180703050a0f030818030904050c0f03150f060915030a06030803070302120708060310110f0a0903050706080f1305031225 72
    0x10200304c01a903481a100741035902602c1c1c0702d80c03652003601c1c0192030700c1c03000c4d007205010b20390b0280c400d04104c184404a508a47c050079989040d100300c04d105403003c3d240c0c102050b907960003481c00a01c6000b401d84042d0042001907007180c1c03650343d0303c3e2502401d20541c00304c00c07030740208248540d00070300d5848030440b0740007a0412509480c40405000c07da0340c038032580984a026580301c0d00001c038681c01040c1503c010f01d03001c0d082150341e4075240242250700007a29020500ca0079690140c0740043c202038050390b0200c00c02130f0482041c0380840d100b000c200d030002403000f424651103100c04070001c7c89000186020300c404c0e80f405604c46a00110715803600d000100407500300b201000800c2842d80e00050b5000a1000021002454103c4410f4a5805110f52400711200c0980094495006988440b2110449000f81c080d145207e454000459042d031066400d001c2e9040a4400f0070900c100141201180380e103c0d0045903e00030b0880d9802c9044201182d0815180b40c14a66184904600c41c10007200b14816 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 616027194 1250 616025944 616025983
    0x21b060c0a060b030a02090705090102060c0c07030f0c030c0315060e06060a0f14040f1a09030c19050a150f0e0a1e0f03050d1103130b0f1308010b03 65
    0x214080d56903541c4900c1070160203592100c0460815440600000e80003d0300901100064541b001002e491940001000f600500c151400200d0440c4d000c0c0989807690090f002a0400341d1541d182c0c1084140540c1064940e05c2040b01c00200160003d1200401180318400c22400e80c0e00100c5880c048407021360006440d980d2030400c00000340d40308411200d501e0018240310344803200d619012108020b000000240c1c0c014001408105903ca0a030340204441000d001016001c0aa500b012401e014055030140c01d580000325824442c601208448800b050a01400c0c00180d80d032000505071790382a9108099003209617100c00343c1d0340d0b0700c40c4140601c070400307090072001e03048060085002c0a4881c82070f00c0251181000d164402329207444606c00404d0100c0c001c50142d41c4a0503c16112051400200d0100e0031240142c1d000c00c4012040d2000010b0410b81902c5c02450450618a20350240130341e0410303664200022042000d00300106409800c0c06000000c0c41e100e104145898a8101c94000100400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 616028444 1250 616027194 616027207
    0x20a15050103051e1507021018050c060a120501090c0f051602040507030906050405030c0f0f070603050a060801021804063002190311130606120e030c0d021b06 70
    0x7902d0130702182c010084009004111100b941000b1043c1030401c028203800040c000c007141d0024440c002c55045445c00c120990001c1d4401c590f10101803002481500b0180c0f8240180ca0408060403068002c2d0400003510b00c40f05030340742c0880350260403241501e541c94045404450740306000c01401c01050400c60300c5d200c04215081507070307810508000d2140e0740b1035000601d01d40c402d4004803070f4a0b600210511a5007030038034050f41c4a8200440d40c6086100b241440c0f0030410380003840702c2d81001c01c0e40240010710b00300881240504070003055224016140d0ba000594250240300415040c224251003070b02a0f0810420002500c0d02c40c0c0c07014610340c101c0c9800040c0d0041101c41c044560042492030f00e00348240d44081030020803a2910020494103000000052041c410403980c1e034950121180060f039140311803004210f9030640a40381c00280c20b561002d21445241d0b00c00104e19a02400700e03828102d01c841101d20b804403010700e100c0140c000c0c0c10300e00a40d04151010002030201100e50703604020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 616029694 1250 616028444 616028453
    0x402130e011d07200c131e060303050a03051510020303041403180402071a27010203040b0a0b0a270605030118020910030b0c0703120c08060d06110a020a15050103 71
    0x3403040c091001c0060442c48003007513034900f0000308417122000351500e400403100c0106000141013280c4803005094403a11511100f503101d10404041e6603060f1141030415080c038200b01c1c01020010145550704540c005030384140e988141d02c8103080c80850340290b03603d1900c2c2c0b9000b9a4002c5144c034000184d03105000c060240c41d40d0b40c10044850b6005d8400503190900760600304040b00b441507a10b14005800d000340000802d06020400c80082115800e00c030403881c100c0082c0c201e2100301c401501c6484140301280c0000943c0e0000044144010050b02e03405858182c0e5103402511519030301c4461101d03840c02c51440ca943e015600c010031044000701310f0000d003128030a2041c180710000a00c654424000940c2261000a14801641e004244c2600a1030190303c1b91075584e01c0b540050b00800c0f640c0f20000449012401554451085d503500d090789030301d0300303818880c0d58810b098003100d00d180c592072078403010350701c10001d4101789005034000c00c5107040a0420102140d030500903128141c0c200801440441c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 616030944 1250 616029694 616029707
    0x1060b031608190c09170d1d011e120f05011406070c090c1b1209170a0308090a050303090109020f0102030a050a1809091113021c0b0402130e011d07 65
    0x1910710f05000ca6840380d030f100c0488000640b42c00c66010661045401e036071084000075010840700341e544030305100c05480d45c0c1d900120f0341e902c0c030454001208070840f00881141010b170f03040d0000c0c01d0b00700080740754602c0c2420f0f000d4441c84500c0c1c0d80c0c0075a458004100440001ea0383c07003118082916100e00d00307105611803a240301d02038094049c3d032507203407121407104511528041e50100741084944590314020328040842c6105a000d102c000303955400f01043e02441d0000914121142400070031307526035035a40c00e0380d500c18000c0c01c0550500600d4a21000300f01c0902c011441094004000610103080340704204c24034604a21543c1194018840c5d451001d03007000c11607403070010380d00300414120307281402404800101d82103043c543c2d0074039946070304010484046440304482222a4102c01213003504a000324000d89002c4e80e901d0008207904132000c00154401d1a400c04050405890500d10200c419501c000c2d951000800062880c0104070200f10b40c5104d4560031115110f00415040c180380041c200d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 616032194 1250 616030944 616030981
    0x6040e0411090a1e1817070512180907090b070b061f0503070e0d0f0318170c09130512030405010e0703030e1009081b030f0a05190602040801060b031608 67
    0x213540d5281001e0304c41103981408504290b03030069a800840d81b5100c6940d95540025800b1103143c4115940c1c841c1c680010801c3d29216644096403405040409040240ca1040a842c84090046400d0003003403100099006040c441c0c01254100d8a905085084c07184403815549072940821b486031032807000b1680101109d230000401d01d00507401e2100c2c8400204222a130201c0241400c81100c45035003003580151500b0900912211040c88055803020080d80001021500082d0750700841d5442c040b5107008a41c4076000074148551120500740360351914500845151042c44810000c02004200a0300b400342984c03d0300f81c88060000c2524695029140003003581c4020711407070828440031036481c4a109520b005210b4041100d14002d1400300e82e01c041090565418041d000d107440300c20210f01c001850a0038240d000d0001c0c010a0340c665981211404020011185681c0810001650900900404014000c4a0501562820a80d140742980701014000600313101300e00c002c0190304c0d2041c0d030000c0203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 616033444 1250 616032194 616032251
    0x606070210021903120c0810170109080a090812040f0b0304060b032b020f030306090c120406141e040b0a0f0e030c061b0d020906040e0411090a 63
    0x1815581e280702a42002e07551031102000e4030800400d0001d01d503000030701d801c0c2c804191408201e8000f44507021591540c04440024481140003420800c0000c1e41076900c0702c4c0a03d0400008080070703a40c0d00c4010039400100c10000058000400b84042c49080c042c603000100b14604203403416140003001125102e06101e88014582c0110006043c400c2d5500603c07070700794008080c2c40c44140c08080c0d020001070b409402c42440b460081c0b100b0071040c0001840c542c00400b83c8011402d5036921740400c0090309005088e80541a000d100d450b0745d0681d0f090146016901c603c4010031b82d01d201d9840b56001c41c1c1c000701044100c0741400e056000b00c4000301c0c1c0d881c0e04075030405040216a6115507d02000d000c1101c00d042c41d542c0b80040b200c07030307140020000c0c02c03d944802c41030313420940714031900b01003890000074000e869039800c00425060005550041c0b000000250140b410542d0350010704801400486081c3c0b0740b0341c18107001d8403440c0390001c4415800100c0140c03c0141c0c0300003c51429a44040368410311 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 616034694 1250 616033444 616033459
    0x1c0c0f150207060903030501050103090b01030f030504360228050c12070b060103061d070c0b01060509010e1009060305060d050304231c1b2606010e06060702 69
    0x4180400308034058042408000c0c1950ba80803985030480050841140c1600041c2c5800d00100350b42d03110f40103031680183c0004020701d0f40d03401d40d01c1c0e403d1105217801081f024028100310004c0d00308006040d0700202c4510910300f0729043c01c190007000120085c1040e4012581c030410541c0902650b91041462440072483e80e40c903042c10004003950944262a6103d10503c07500b00e5222140000030000c10584e40700d8040a04c4a8440c10015025203d00380540c5e40f404110710420002d40094069032548540c03940780201d0200440e0300c0381c1c6540c6500380c20a40000b0b030002081c100c6560040680c1225420581b1740040c10f0500342c1004241c078005002d080b0030507071600003181c0d281e41d91036501502c4642000039695156511b0003001003003031440d40303021803043d0602c0c01d00358a031609107182400c06205c1040d04214000c1962154003e1000c4104501060034901e40880d2803140c040c051030129039051148004003002425407850000140d20a65120381900100101903c03080c0036202d607580d0650740070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 616035944 1250 616034694 616034723
    0x150a050603010e0106080a02131814150a09120903080405131b0906080c1201030f1b06020f2529030a2003061f0905060c0f1c0c 56
    0x9000d07118000301100c00e136080c100081000f00c40828103490540c4200d5840b04030090a018150a541d000d070011000e603a003100e0341c00003041046a0b0307901030201a80c20380300040030700000b6001800d070699910a00540c0e60702ea070b40800102180000600c11a0f08060b8140c52550340c0c1c51a29101e240182e50041c15503110749401f83c80150040c82c1c0d143d500c1c031505942d45056500083c10800300d84203880c00694107501140700880b96a040f90b03030801601540c190143e086850303940901c50102011034034120612580c5683d2003260043c90090802507000e00742568515183c40e20f00010300c00c0c08604e510380816211061084e6000c50070864004048440b4501006441c06080310740b403400d90800c1c00c0c0c002041082d460b20300c1d803240484c0c1d0100d245c5100c0b0640c00844070b10460004551090b0440e60105040310420301060701c87c640c50045103030002c0000c0d246c0001c1b6125401c0f034440328040b0f90140d0240e0034841001d0182501c1642020b0481c0034000d00044000d140c2602d51001400b41802040302 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 616037194 1250 616035944 616035949
    0x60412180b040902090109051e0607150509101d0c100521010504061505070b040c0b0a0804060f050c07032712021807170c2101031202150a0506 63
    0x4001002010551900d49546103d950003a600c0007240d540019074640c000b0680d890080c03800000a2500300c01c0135031000004090002952201310305481b25018010754200d0341c013003400360f50320503210480500303c42d101d0036402400351f86800075921002403c24040440540c0c0c001908454050300300e840d5520110141c00c11b4445100714051000d03a880011203013181481e40e0354419040301c000352010080c041d543c11601c41c0c0c01003910605c10000d002000341d0400308207546c000701d800c640991108150686d680360a2030b01607100308100350102e84102e00300710501250744120800021104014815490300c0c03110484c440c42202d41c020288910105450724440702e0841b84141d43c0e070902503103e20182ca44039106c070300142c05d040c00ca100c1d484403121700d507120185a890a0250005031541000c40c0110314140425107001080700a407840c0a001545040412049080182c00402c003140c2e8903506508014007001d40e803010795400d55011003010240920b001c01500e0703200b07000c000d0004241d1242c100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 616038444 1250 616037194 616037237
    0xf070f05030304050604030807050a120903030b0306010f0e061813050106510c030e090703020c0d020105060f010503150306010602010e07050406150806060f04120b0603060412 77
    0x20058440c0c880802000f04001d00011194081c41c000d0b00d460419603200e080403030300f521410180d07500040f90700d0346070041e10107240c015a40992203414081010f10307060020030301c2d1680980c070141006035480c0007041004511914140c00840c1510b200780c540b900420f503114441000391844250340900407410091100030340c4142c018117848140150700b02c240c41007448441000e0781d01c0e00d1020926201e00c40701000f50004085c20020000d446d001a842c070b0700340079a0030080e060000e0341400900782ca10052681c03202c000300c1c410952a100140c1f0f0f0305910a519103406050324106040da03240000303010755507035444440e0000348400d2070300c11342d0b9948982801160041505000b03406d880b415001251851301908200f81d04004402100e203540d035139108002c281c031417601c1007054440405c00076144051007000e4050b44818007904d10f500c1c2c505120140f01c5c45034001c1c2d00c1900c850a603800b07410100160007440e035810142c00c070020420307402c042c1c076250145c1610341000000d00c003003444005505581500b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 616039694 1250 616038444 616038473
    0x1b0c0213020d061a0c060115020a05191b0b0301180e030706050f1612022116090603050f1f080a1112030a020a17090607030203070221030f07 62
    0x40c041d5101c5001603418809803610340102422182c81c03148040000700d4010540b001d42d45c3d414000c065a929000c1d001074000c400c00d4104045000da10580c80c081541040301040b968000d0b000b1414100a41c14029644484825842064a414942007000f000c4010542c2d055581c00d5031751807901101c82c401d120007002c1c5186800350398080810343d4070502c21683d010720f108104c100c152410590381c14252030301992001904601080356008544030702c101c00c2c1e016204001c0c2c90200c40311507005c0c00581d41b130580000c680c0d98000c0728186207850482c5912040d40340042115080500180c149082c0080f00c024000300b41e200c244c007074160303412115481c030b84814000f0900502a100c81d12454249115080c4c6070070b00540c043d200300710601080600000441d19243e4080d40034140490f906d9407990340c900d071030110f1110b110310188080c40060b0354507001085c0d041d209400940d550903e900c1481015032407005c0040064503402c0c26140814000320446004501440300c0c2c0e5030b60b018500d0324400050605 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 616040944 1250 616039694 616039729
    0x1401020a200a05150a1404210507150507020d0201090902181206060f2110090501050f101404151e080a03022107060e1b041b0c02 57
    0x40981e60120300100322815003900107440803602d06440f5018015005280b00d040080394030104814442d41d8490700062101a99030f650b0740d0324107551203440b205c0780103c9840c4442c50701d480c050050b04110b0f04122080041c41c0798902120310748c40182002d07081d409100340c0a400348520202500c11a0300c500058001b41c804001c4c210b4860390b55a245441b10725500c1d060b5030003081e0303a8008441c0c005d40020001c0c400d0a00800250342c0070352500a0103210500e03210381000c03143c0c40300398dc4d0422203002e02100700740580c0c010000881000c18101182510006020142520104014826000141c21020f0290342210507842642071401010034000d048080440b9020300b070201c004207100810394610083c004502c504a129681c44280c01038a4224542c40240540e010b00c0707a04240c1c0f80c010701c1008103100032282a40c00d1403030646030701094a6005080000a400402d1080c1e014064213158210b003120641e001c00c81da45a03403001e01003030400600d0385001d2000c501c2c4101d00710b42d0780d08001c03580b003040b1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 616042194 1250 616040944 616040963
    0x8191e020327030a03020c1e060412480809090601090b180f040c0c0c1e290c0d03140603060a0507030e0703050c120111041401020a 58
    0x1600110029041652000c4034820001e0881e0094510081550602c0d0326000141d842c21a8040f000e8001751300050107030005d4010301098121014011110f0307140f40341c4200c00b52266141c50300c0c06403000c24100140030103002455210b00591044003119800720390380702c4540c545401c844600054404e4080003484004e42d608000d8204022056001c1c141c10704050310004115240d0000540e0510b1460180c801042c100348801400400c00e003108000402010385420743c010a0000881c3c26628a42c10246c04100c1120450b000c10512046405c010420f00d42079545483c2055000c00c40d10802d4803c04004c0704003280c2240c0c0420404403c40c3d800341845001e6230756550598402134440840701107000c0841d02d0009001c011807000c9661900c25200140603120b07503928400c80b040203210103041502003603503804100f9645002007003135101840c011001814800a941c04010025035082402d000c541d0400c6462450000603805036400c2d0380781068901a25a96900100d00e0040c4c1c420010703021103807 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 616043444 1250 616042194 616042241
    0x2030c010c05120f01080a062a05180103021c02340318050105190221040807051e0d05100204030b0708151f0c080f0a11060402010819 59
    0x200300b002042040c43c00d10941c0043e0b070310f000c01010340310302c244140c61041e00400324460014070075038480d000b4084250f102c000110b11002d1f000d11384e03094002030300c0046980054902846449090301080000302440c00390f243c46c81c00c0e9a42d68a40c612910901101d82d00440d10381e04270300c44181e0341c601c48515010b60410550f00400d100307081c000c41c2c1c00700354040794032180c40c0710241e01c418100106448060310707680d142030150460340c0c03d0860120204400c41c0200c0304d608007080b82415070f248040080301d820a4543d8109100c0908004071a40458454040349030002802000c0d450100c1c650102181c003600385105600344207041c2120342781d45410151000402000304000080e1640c0102510358a842c00c80d501c0124500c1d203800440c2290303500074400c0013130115001542110400e01069884d2034200c881041e5075100720784c0c10003000d00d4142c603004541076004039804540c1c8a00015030ba0000c00300c0e4149030300042c0108101502c00c41041c4200c1015140303d2860b41c024000042407a62500c04150 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 616044694 1250 616043444 616043447
    0xc01020d0c1e020106150804050c0907030605040e0303150616120f08090604031d0406080304030b04060507090e19020705060906070e03010c090e090c03030a0302070611030f04060c02030c010c 84
    0xb0b420303051107000c03000600324400c684144128416141c2080100890110b00c1005035170014008100f201c503403081c4101c6880e03e490350310b4801c0c0990b07419240407030542d040c10104810b031210350300350f0103095009008010519808010031040042c065860b5651003224040a01801c001c5180c058103141032002688901640b00301302c100007440039a16601107480c0e0401d41d680f00c004c1524060000390540340c42c40c0078803101642e085196000104001a1555142c102d00c0c11a0061740c000d4980020782d20070801440194000d09501181c113150003070b0b030709080c81010161101c01400e42407070b164513864074410002055044032501504041114181d04d410010940d4800c821625480000c00034104ac01c0641414000d003400c0201e02d132101d00d106c604080c1455100000101704c400244a8800d40c40c1d96614244010003059249540c056a00c01d200e080c1030381a60341c801424100c0038020000c0100c00310b03200440d40d400a03440900460a120052022403650003807503030118017546082500c24186 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 616045944 1250 616044694 616044707
    0xa0b070b0a0b010c060507110706081603090203250b0c031b06070e010e03030f04031a060f1324170f0a0b0609090f1006091a0f04020c01020d0c 63
    0x26100309068082070740c0d04920607058519002409010888600702e01000440d00c0d00110341c050a5480e024240e6285800d0080c61700265902c0f80c0c000c54202c000b0701c4080b60400343d030b460941d5954101408116403da010982c0c03442c110500303a11740f0000805145060312410404170092101d03018494442441c0b100607a00c0b913000d48002d07000d11840001d8078068003000b15036144980040e460b96615482c0340001505c00050b84581241c0c14001041040114503201d00908095400f4122058a010040c0b801c0302d03c41c64080c100c548903541c00c0302000d00076070b200340f404007a0050340c9402041c030060440c1181641d0142e030f000103030720903120039001c16901500781e00c07201103e51210444d80849900b4060310346590320b40d040035201065001c002032890030003c003416001300048040310b1082c0c084c1944603007000c0010104000341601c840d41000800c013035024070010707280c0021085010500d1071001400e0142a1481103005a401150b0104412029419900e102c0401e0f030007401600d20001008204 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 616047194 1250 616045944 616045957
    0x120504231002011e11040e1303020d020307050706030e0c1008062803080903100903020105041236050312072d0303020906090d1104050a020901140d06050a0b 69
    0x6070864241d003520a881409805649491103103e860007041c2c5401c004080c080307041400d424810100400a0100c8040d218544988614600c0b0002181545402403c110903503044c9411584280034a402080004c02c02c0030407102c01d800c0000350110b1141070030b418800c014101320b51000084602e80b48036500100300902c1080d088940400668041e2102070000c00b00760b020040c801002c101c20700000e11400c0041c06c420704e0083c12190301440030381121040c1c82c3e104100f200180d4607041032008001102820f101400c880c3c1c208442a0714a102c04c58450031440c140d4903001d0071080600c03140000d030116aa4015000c0030b0269450305d040440d201005520a0804480103d582c90101c0701c2800c7c0c10074244000400c80300c84054464664074114003a40000800da503211204001e0000b00381d84801203100e44912420190300059148402c010407100001e000c08030b005c0c0100860041340e03070300c01099400000040446a00c5402619580c0c00501c841c0d0860b90708101c48c3c034804521082c418010b4101c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 616048444 1250 616047194 616047199
    0x12040c0503061314160e0a06030c03051c2610170609240403050d0209040501060c03020d0513060503190e06010801060f150e0d050712051005010302010c12050423 71
    0x92440c4000003039038417003202c68604520318041005100d4401c85400a5400c480c88100c085440e1f5100d8550040064069108070741e03943c0700c010022a21203400e201c2108040442c201641c9844013414144a00036030003561113585100400000c0145803402c0026015007000401d0414003120401c200d030b0b480805a41c000c6691151110184540c01a040f400796000200201850707680c88543d01612150442f02c006000180c090000c007115440c1c600c00c150003080c6c00e5890b8104006c0e40c1c100030342000064031456003080820031a6a890310b0b02d00b00c2e09802c40d001480c3c0701da0341e544c50484418140056100c0d2030503d608003800040300c418001a103034165080000208051581ca2802d5500307030003244210400d52204040c00d40c100350142801035080c03100500a01084a81503496a040c41c000350000c0200078180030030281844070811015621041c8500c00700710399411500081c1001440e40402402d40019003140c048140c801c0d41518010701d107244c2002000403001a8402046950180f485e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 616049694 1250 616048444 616048463
    0x160501150f0807080d200d030b0f0406211a0708252003070b0c03071404080c1215010e01180b1509012307060b01020601030812040c05030613 62
    0x20598004161581240d4800009056065441d0020350301c0e034600501416020030b0000e5140c2c81b510041c040c01992030301c4e581c3e00140d801c90550420040c1070040e00503034042d529180c03041c400d0035017a64001075481c0007441e52030585a507501d440b29000340c06216283d110500d0314148403e09030462001c50064040c0c0000e100c2c054182c3c8440784810311440344000000d480d03a100d8185605e1a00040d0038210a0841680d180c0242904d42c408014000c0c0d4418840130000410801c10381d502c07080d500c001c61450640345142c00e10b82486581e0301c0364070301d40c1544100c040b244c00322000311081020480c2407112500c00038403980c0d140f400d034030140000d20400541820000f40140c05403071342c1c4a081c0d03580400910791a81c00500e6001040303180c200c204141e060100b520700240c0400b4044210189116000c80019640d14040c81c01c601900c105031091419580f043c0700600000c1d0750401500ca10b84911140e4280303d0f41d490400166200c45070340107e8140c0201010300ca003402000450000d001c0c010070158 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 616050944 1250 616049694 616049699
    0xa030614031e013b0d0507170702030d0f0905030307080405042315100e010c0f02060d020d05010801110408070b030907090501120c05100e0d0c051c0501060905010303090308160501150f 81
    0x1644039914851003c0011b0410407075100024440505500c20060380700e0050300300001d641c003291030041c42c001c0c05404103840d00b040e80b00c42580304070720902a08041d0041c40c100341c8142e85804441c0603900807244034036110510017130680a00d101d42d0310650110a403543c00703402c01e80f00542039524003014190280c201a07120058071801074079409080d4030182d440980c035504030384a400740c94414410499000d08100070444500849002810b503072601c045d0009070951400c03681070308441c111200080d02a100780420414600c0110f4840c0440b13107104205992603594441d2182015480d402c01c1c28050b01c2c0a0021601000114031410f90510480c49070341e80b5601c0c0d008200022481070180c0001035158580c2c1d6455080c0411b10010040c0304407090300005446100248440310105100b80d140041c0c521500300b40301d02401040b0003031043c60010000c5504680f401001e003122404080c2c18040009130100c1020030007041c0741c034200c0c0c00c007008101040286240c00c400021078410007410214440c0007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 616052194 1250 616050944 616051061
    0xf020a080f07090f15020c04050a0c020601051203032217210f180a0f1407061b080c160303091d09150621030a030614031e01 55
    0xb0076040e2130205066544040c64400c120f08082d000c0d002080844c00b035a4104001d03500e990081d40d0007102039200c049580b5101c500028544001648418030610445d01500700030300c0c0100c203e03608059450004a58804207070140011541c070305900400e03000e10070420035030f40c00b10344029006c5040d9842c11941c040e00580512604403500307031404c0c2d220768080700100b90481071010003071a15050281c180c0352a9243c40d201e04064500e0445c098890803200d042c10b01c8403503c2445400c0103444e4505207500c0161002200801a40d20384c0001441c0c00ba00180ca458152820800c244480000b107800c0b000064484c50024041d0a02d8410400c00b004400d00000c08541c0203440c0780d04c07950284d8000e2484e0900c40c0124255610050051900f1525099410000410b0a2244070344118108001e640c3c803089407500030100c4510341d2002004000800500355203540200706403104140c0d1280500d00e00d40b2414040740100380d01c01c0d4844203014554207107030110901034010b020081810001e4040312034103481 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 616053444 1250 616052194 616052207
    0x901200a2d030906030b01030b040207050c0909070305060423030a03091209051c080912011e1a0d061107140f0321040602040b070503090907050f0403060f0f020a080f07 74
    0x34000c0100320903034400c1c00314500c40c1d441040400c030145800300c0c1d071601d03270400305e030881e0b10032041920182c0118040800500b424049a03812090090040020b41e2443d1240d68668201401c0100354107103561425070403c0b0f550307010070300001d1600f096036600d10307038100082c00500380c1c15012682d00b0442220510114050b58980e4210340300640007811000c000c00c583c009203c003c42003201c40e5501030040004c0c40d02c80c812003100c05107082c00002440e45444c11101003030303031900d85980d4500381400500c185002102480c2000068151514541c11840349800000340031260a04181d03504040740b40e00034420b000d201e0b030b0a021040c43c00d0380d410108141d01283c5a01c0303010207a030303880c0700034842c0c03442419480401c5aa1083c080c2d900141000e07210340b1262003d620020301030b00c450b400403a01c07050303510301002016000103107814001c1c904412405000d045000e24480504601d079201240c28a4801a40060f600c0000e1038804550b50710003a603000d4a030100680e80b041d01502c84c48001090741d4007466 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 616054694 1250 616053444 616053533
    0x50402010e120d200102040305033c0310090c02100f0c091a040f1d0a091226070512160c02100513030c050111060c0901200a 55
    0x546440c0f180b444007500d44510341582d104141c0f007400740d445203080c028405080994802c40245549105880e180300c0000300f041e10340c24100004001440341300d83c250900d080310120145459407070b0764a0100640c002c0070700b58001d42c0c1e02c90501c034504184540c0440c0e0fa07400050404810000100900320000880d08401184004251142030911103c141d2820108800c0c50a000e554035058540c078044e0a04c0c0c5460340a000c0c58107014480740080604034000700e0340500d071958108140107598035048220720b401c00501060000c1040c001c0390f501103140c4106100740300288480c0c201c1c100910010705992004455103101803100300803a800c025002c0150201050300d588600c3c1031051034003003005044914031180240032040007a54000d00110080f80c1c010750107004554030307080c81e16001405070904030301c803c141900240308200a01c00208140c0c6c03002c02080c40c081507042100035141103141d2403040d51400310300c500c0c00c003601002040065010f410004884440e1002c140d0880c03d4400150b95 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 616055944 1250 616054694 616054729
    0xc050109052a0a03080c0718091502090d290c13061806033b0601080712140c03030c0105010602070b030609070f1803030903050601050a180203090c13050402010e 71
    0x7041001c18410300107060b82880318020345820301d0741e0f2840e010640c2919540342c1201602da030442030078130045504860503440c1481042d80f6005184002510309014aa0020190b009001200e41d00c855481078510b541044625060b028fc1012900c10a41d50410280303c0507030034a402d004104980b188421140c1440d140881004141c2000025806050902902e070302d86031600c00560512189800c80c0b044190702034258010140301c0024132070805805820140c0b4070f0b480380e18100062440e031140710301c20b1070b0012801074044c030541c50100d00f482d4840800b158076210105d454404014191311480c121070082d000c440fa10359540d0184c0c0524081211350740e51218031030001130082c42c02090350004201c210700d000740362101c412841c46600b01c4590001d80001c1c0440314281308105041220300d016180c00c860740d004952801da404000f00004400c81c0c813401e40c0100115020b44000c0240c404000790080400c541c1d200b0707400043c00241070884080e0f00213441a0f43e07940180c1008500c203040c10303a46 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 616057194 1250 616055944 616055959
    0x9090a0603020904030c030c2009010f05060a0507020301090804180e0a081b070e0115030506030610050613030f150c080403020c040c0e0613231c030c050109052a 71
    0x35a102079800c0c0c44c80341000e80900c208c401c904000916500e03013861003c000081443e0411480d00c040c0714400d0030580040c014242070440911060382c5050a440849031985003560707442c51948042030140041c503000808041000c41d01060705c410740440e24075191588002044142004040c4540e0b0321500301c2c014206050400c02401004d290f401d418120380054070488440a0340c0340601e000403a4244e014042047d4070342c0504a03025858041c0c140c0006044009000500381501c0c0040b50350300a22680d80f090400254940908814400002c000c640040b10441042400c0c242016009185c03800708018034580501c18501900650990340500d82550060811a6400c0180002842d068210000b0b00041220140060f6200c2e0010402007408101d0382c1145864054170b01054541c0140c0808070300c0c4441091041602d50310f1554a003842d00c02c1041862800a050964900e00881d501421130350800c0708000920100080c000c0011900034a8054142c0b01c0c0600101c0e01d80310b00c000981e01000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 616058444 1250 616057194 616057201
    0xd0e0d0c030f08151008060103060f05100503041406010f2121020307020d06020a0809070303051e0c15011401030605130f0b06160b0606070809010807120c030209090a06030209 77
    0x7050f61001c1d0f02c0101a80c013281803501800006039641c0100b0286800910800104038155a01d409020001d100b09011050024240720024070a83c0440d100c04040020110004003880082041c8040103c10501038540da542c6400400d40c050740c0b51300420108005413502c071140d00d099000401781c3c090304110281e0783c06021103064241d4251804d804070451105108400141c1e6410480139205446400f0059840c015102c0c06409103100500c907000030303040300b8402c20100350032030200c40c509004500000d400e0350700307050101141c0c0590010700c20f440c0700b44000400060f8400340c1040c1a194140d031b519070950f02001c0110159103160003519000700c02c0064401c114811a0041000f01c680541c01190b00f0751b000000c40c16680110850480c214000c0c0d56940900c0246c20380e564020000795801e510300350b030646509045109414140e41001004c0001951091281d1103052a80340c80318024015001071a10080182d00444822482a0780d030b42c0104103036800c94801c00c02183e0b40a82061a190f9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 616059694 1250 616058444 616058447
    0x301140601020c19051c0b0c04061209061104061206050a0f120804052206081506010c0302070302030304060f0806100c03050307091206050a050f1b0f0f0d0e0d0c030f 73
    0x644400214003000c040301c3c02284a80c3c2c0d441d081e12244c1401940c00308400c115081903809824003501c42c41004230300700070910000303500c01d690314179a22180d000407425000c00c2c40e100004090102c044000c0480c042404148143e01c003c948100160009081c003506844908001e120081c80c8281c40714511200410020300c0640034008454a02601d50681410350354400b0440f102124501483d820860408400600d105807141101405c80c1c01c00400e4803411282044440500251099041c000002c949004141c03003004004007543d07003d010789440382c1da82c1c40058410030007400001c021611280000310181042c040f404202041036903480c0307003404540c40580392540054000000c0084000d8081041510008001c0f10706108080018084c0740c05000d50b8100e81c4040c16000b0550816018040c603140c0d4880c0b2800299152070030780f50345002c40c501c09009403040002071140c8180100306404103501c5a4049003c05841a065030a900d007030350800c5880c0709031a90010042241d110f33001e69403e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 616060944 1250 616059694 616059709
    0x3030a110f0102040b0705100c120b21010209031203250c0609030e2e050318070e16050307050301090504020607020301020c010c0306050a05060f0d0216050604020301140601020c 78
    0x149820251040002a01e400500f668420740204032040700004a03c410010100400801850250001c10045206501c02013803c031140b100c00e104641c803685001d4295a070000c000001800c601d452240680c144056203010f90407071040c00e40b0a01070f103101400040c02c49011248102601c20712003618144800001c5a640d001d8000c10b020844208910000074005104036007441d03001e03272107038103610511204200410580d00f0040216400c0180503095901400b81e14000b241c1450500750703100d42c1e920543d41840410340e000f60404d4030031503000084c0c6441550100b4018000030301d583c041900480c1c02034540d0301c0207882c5040083c43c10030041000391000d520050700148010442803900e080f41e0000b070b081ea0050400760125940d40c8500d040391a416204020041200b80e840364487c0749080009551070040705c2c80360180c03900c001000c1c80b20703003035550440e900d5518080310080041407a0070002c1d40d50400720340c102d01961070f00d5220f42d4041520400c5030f01c5820140c0c02050054884001e1000784e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 616062194 1250 616060944 616060967
    0x307032a020d08130b030a050417070305122d0a05060102030a0c060b27060f040b0105071502043302150103020d050a20010327020922060c02061503030a 67
    0x101622900701242c0241000700860047c0d40f002c1010a643c03c1038202020203003600c00c0908581c000400c180d000203030f04403042d18840340188140c908650f640c42441c60681d000410341041903501c0380000100d03460f2801040e8022031a180c410809555003c00582c0e603071140c2040318000c105044010000118603404c4a108404c0c060240709410034041c8140c04d285000e01c0710981214416400c01151f0700f0300061078100a1002c80c0d007800154856000a004c80c0300348100900b000c0d01001840d0808034691301150014039088204a0340091441c003803d03e0f484561805180688005a058410030301c000b40e10000090280d4110700ca81e4070f581e0070005291074410b01120315004008442c80840c9a010151440046400103880c203101c00000040490f082d040070054040241e1010041c0744864491001025a040c1e540070100d0702d5044c0c0309a14424894100c0001072045468a4100000c542000306000e0a94080710100d44901c85d801902034640c001c030a42680c414030410390580d105010041c10f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 616063444 1250 616062194 616062217
    0x100b0d291c14120a11072d05030f0c130501030b01060e030c090106030608070603090b070e06071e032604150b0405010b07050f03031003061a030307032a020d08 70
    0xc81c0c100e580310b00d041c510400342d100000c10020940080381da40014075482c08070000d03005020704038105800c140c2e504c02c1c3c4240786a25901965446081701c50291441c4010349401402c6920350110100580c0d40e6112510400b0b000b4800c09941b01003034070f0b0030b00405060745c0c2d0142003000f0580c00d00800320f52a8140918803641403203500700c0030003241c40344401d03d806400ca83e900482e0322400c009010345881c034181c3c8003800b00751a01080c5008100300761031094100407189031541104040340c0004455008000b03028110510089a803c1c1c8120101d00d104d24642c840d440300204181d5241180b40700c20040c140a20b902151000080c00245601145400303150b6000c44c0003d404090a000c10100c1e0026081140740d0030b00003500320203002d4100700c0d118140d65000011f515600d4003060030b0049201034403004040b1625081003511a078491284005008005811a40c4a242600b002054510440304030781c0c00c0c01c1d0181c0ea2590f000f024000d04416549c0261003100021615074500d4003683c062181703490b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 616064694 1250 616063444 616063463
    0xc0d0f0314040b0d05010e0610020604020906180f240f0114040b0705100b0a050d080304391401140d0603061119170a05100b0d291c 58
    0x160b50700f001000e00480b50202c44000b0b5598101084031241440c064101882100c10030300100c2e4450303000441d540e0045e810b442c00109916000c0118115880401600c0c1590350501c0400c1000034288615a100d84a2140d41548a456220141c280410142642c1d178105020403400002035016901410900c1031842a1724a05541c540390b1300318a4204481c1112190007154882104104a02400d400c0810403514243d030300e8585400145924002c200003049d49a02100280500055550110201c071210f0030014201849121100018210f42000d03001e0460201020402c3c9003502110080050306842e05450000c00e00038151041c0c200548a005007034841d003001c070026149014009140e41c4018046403100301051141c50304d0036200321618100404118906180d00c24071080540000455000040d5a103850b15100368040b220f42001e4100400050041d210f00c40c02d5001041c1071102c1c810b9515400e00d500341230685011112495980101c140000f04a403890424182c01468810034600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 616065944 1250 616064694 616064699
    0xf03030c09051f1e0e0a1406030f070e03010f0b0102191e0c0504020a0923030c01080a0f05041b0b13031725060e01050405061815090f0c0d0f031404 65
    0xb01d001c542d504090340020324420003032021070809004503801f804101d072580b2048129034000c50f42c03500004000010001200012440041c000c50701c400d4507400c00b500a1081d84044554070003e4424100d51500621401000c8004a14504196009941c2c0200201410410000c803000502c002440985120b02d400c2e0f00020a42d48620007040d1824850b120740312030300d1a00300c101031310482c20200d1003102401c00781584441d80d0b000c2001900b0320b109081546480e103982000c2c100501058070000d2000d8030300024442401900b640b0035422074024980300004035216194035440340600f0399001500c0c042c0113000c0c0300140c400b141c405041e40450404504004580c0300c803d01201403000b01101a91400a03500e00b071001601908a00c2440030009000b10700706a9585542d9120007800c045409421000701c0c074002c10184140302011050304001c3d942d5040000d02540c5a800580351240c051090a4001d1400d05103100c450000582103198800d0189154074203642d00c0c09804a81c80b00c02c0000c0002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 616067194 1250 616065944 616065977
    0xb0604051807020106151e050708361503041704121e0b0a0e0304050301020f12010e0702030a0c0314030a0c030515130b0301090204090f03030c09051f 66
    0x20340020780d41c00204200034200b40c84060708441190b00000b0741a600d090002c42e0361170304020f181c1001081c407007040c0c020100601084901c0d0141c490010f01081c00054041e010400343e581130703242ea03803941350754082c0764211065060b010491000d40941160414240100c4401e142c009181e026004044814501c005001c080819070700c5600105002c0307038030044420600070800140f011008075202d880d00ca09817607032248a541e1200500200005803941ca41320407118052040d02c004003400740c0295151501600c1503001c603005030003080305800c00710000040d051501031425000b0101900910314000341d40f0021611704070020320550620803039030f510030886150f8030001c62042440c61000954074007031450003800c0d5000030300412160202041c0f0701c0000d984558150303003080c0000d1800a06c00d174410010130301600348400c02a520510700240e01061288000c03000c02154482e0790200042c0e40d03e100f0a8030b9000c498006c80341c004240321001c010605030012842120394040c01c01146181c9500c80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 616068444 1250 616067194 616067209
    0xb030123030a02092503020a09050f040f0c09090b19170f0604080a230901050c1203011e090218010c03030e0a0302011e06150e0109030b041209081f0b060405 69
    0x44d10b0340340c01d070099106a0300a0340300701c0c00c5d442ca001c01c0c80c2c1075140145129000701282801c1c020320703201c0d02d00316002d07040c3c4c3d6890350711020000d0030000702480b00c242d0341c0a01824510843c45103c240c28180564641940381c0303007103400e50f00794807118610032840c2820320508608020040710205482203501210103480201b00c3c445c40341e40300c1d0240740d030740343c545400c0189024420903002d81902002100400d00082680607204070003801e207070440c0c554580902c1035161011810f52500382c1c1000100204048401d80c1a0700781a858400050f644180d460221004a10458143c0c0da0504403401031041c0c658801c15036849194040e14003c5281c480b13101c40507081c0018044200d026039034410040c5164508200b49402d00b03422140e0400a091500700c000c4034000c400c40e491410000340b0181840c0a80c00342c204c29001e180c2107000026645850b1a04403856072034000120081001c18900054450307000440018008045911540301059841c411019118408040e54809410b01020401c1d40310501c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 616069694 1250 616068444 616068451
    0xd080c010603030e03010507091406070b090a0201030b1206012102130506040c110c04050c1e04060314150d050c06210603121b01110706150b030123030a0209 69
    0x1000000c5003861403902806952103004c11a000f030341410300700840c01c0c0d045545182154040d0b04144240a11880007440921807414014101d240000a1141c00c0c0c0740000e103006114402e0b00c0421030848030100b040420740d801341070460b50354804001800281d40e607100741e1102c0746d6482030509241d10150f001079122924402c10060340c075a113500300840d500e024041c079181c02109051410390440701503000c0307855500780300c141e41c0240d44500100310842003110882d5548484815101a80c607180c10241c5900e030700612032800041e050020000c1089424074000740141f41c1804889402c1c002c8009100c958402c0d00c000765014000d0000d18000b58907405c0c02420b5581582c0d9448107601030188140c031000d05d010741590f009921040c1c49501007441142100c10f048100c1ca417000304041c440c0c0700103000d000c000040c00c01402000c1414402c01c0516003000c404400350341408005142c41e4904e11860340024071440c55003100080f400c4440840200c1e403498491000341c02d030b903001c4c081a00805c03c420800d8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 616070944 1250 616069694 616069717
    0x91623060f0a082a071415010602070911091311210c0703020a150905070306050a0c02010e0c040209010203120112030f0302090a0e19051f14100507020d08 68
    0x51082c00d41c5500c880c0907640102c6190f01c10741c107007581001c142040e5a02c495240150040002c50307205000c0e42003c400f0b203a49440041361031034025030101d00100c0703000f0b00c103400c09403081c03520101e0346980500840810039154200541044040410883c1845403150040041d95503140c0c2413098201960092041c451509185050f840740802900170808000300a500c05030340920070000000c1d80807071f40d403444a0700040d1450480b041d501e401d00c0104000c1c04000c1041c4140300c0d00004005040e00024032468003802c04005071400c000e070907826924551002e03480d0b03400804940b0b1032460a640600011601031044070700b4203c0d11300c02080c0a00080c1c203d550700c0a16100114205a400501001040a149419400c005042e800b10b0b103011201c1c0200b410110040002032000c105500d40ba0f4002042100140b1880c00c141030f40711003148810300c00d50b000c02c11403180420089013104003c0f04441c80903000c010040f00d04041107402d50042401268004080c0d070441c00884c0d644000381c00300d41d141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 616072194 1250 616070944 616070947
    0x60e010b010f020604080307030209030319020604061407120221010b04080c060f0f031308270a030503030c130803121501080f04060504030e060a090509091623060f 72
    0x9103030000d065107501c0c101c00703411036102c40108800241110b080c3ca8105005040c09070702c0b150726500203400c45c05984007002144a202002819140d40080c2d490301aa014410401002130b40300500b4068100c00c66001d4007040c0c102c04400c40e40340e5030303078001d10f500d86035411040c3c0c45030022040120400420f034018580c4007004901406010030600c181000e114040391054078200c1d0008144416015513519010440030120000384603620b080c41b40e0003565805040c0c03e5503520381c0d00d0200b80031460203c0041c82c28030684450302c11030802c04034140541e50000015803e6948004c1405843d905c08400041c0401c7c0654000909010400c0500011104103680c142d00789480c21721200e07581c26803110281001075800c1031080581c4407903010b54006410070343c04101503685040503594440101c942d650010070025040240716440b6100d2020744000316140b9015032103456a4641e112188200d9038180c000c800c00410502d0b0100160903a1000400f040380201440500010720b160401c00140b080303c0c80 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 616073444 1250 616072194 616072211
    0x190804080d02010b030607030b130507120b0402030108030d200406120b0603130f030c0b010902090102010e0604080a08150423070906020613030c0b010b04031a04030f0503060607060e01 81
    0x40034840340400368020310003004645103044c0000d56400e00502484103040d80d0342c0911000380c55000110040c010904006e012a0030b01000c014056130404d20701c00c00c05454040003401c1480d0a0003240d040341c0076600110705040590315084018440305004c8a50700441c003135640c148101d40c00107003008250644400c0b00c1603c1c01c00000090340c1d028080c1c540300310410010008110f115002c0500da050300030140403072a0f040c600d810f82d0211000c4801a241440c54000010000c00d96001801d64140a81c028800c1f04000c010896481070140d8000340321040c140304101010740f01d103254a40c085a0341d940e03104880a100082030031140d180307090410b1a00700f00c4c607805003a0722401c2c02c0c5c0c1d000007040c6400c126051a0000c029120342014100117a401d11486040c41454800c1031040700c903a41040344c03407540d5603503814214a1a48284805c071201080038403031022840320f407104103110710340584901c02050b10102c0111015807000f440298086018081440031a03603a102d594100440100005804034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 616074694 1250 616073444 616073459
    0x3010c0e090a06030f0f050c0d1103211806040b0a050403060615270812040905061e0402030601120e0a0b061e1e03060c0304030e04021204030e03190804 67
    0x101c00428050a440c100401040010500c90b81c072140b03aa007180d481c800040c000e00e017081c10410840300300b6a0104140700b414051100c44c1a804030402c204078101c4001c0b40c641e0740745503034218590401e030399441d106000d500d458441d260b41448507081700919240c9095184c0e0010143c940210f440200001e80100f424000c001187c800e286c060915400691180d40d200d1000a0050008070001480c04025090483c0b80703010461214000d490b4082c1a9070040840100c080443d42062143e0302c246e40c05c0c4404141c4900f0041c1c036640000f0721004d1401c07011400c0e8800d00c4040d51002d0080c0f81002002065181c10032000e2107502040c0d400b48000d0689210103040c240700740d038006444644601e5044105103c2c00c0c4501c92220a40101540c40591004401e25003a0074400040b01c0c0c240c05000b20801c10102400c00801588180d00c2030f201c8040101c0402c06000c203d00034920000d254004240129002c00d0007034406250f068001000c84030300a000348440403441b400c2c601c3c01c030f074640310100301407102a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 616075944 1250 616074694 616074709
    0x1002041e0b0a110106051302281b030c020d1212050601050d090f0b0c0a03050c0a05030406021c0f0b120a02030c011808060c0706140603030f0c0304030203010c0e 71
    0x180031a8422412460400319484600d10a42d581101070142c40c0c41d104255807030a400010040a00a20b039a5400201400681c0a07602007980754411820004454000c02010003441c003210030107a488800f0700341c1040f40203101c0010b5503016010b11a5407841000182c2c3ca008042040d18452a100032829441c5030300a4440c140d007a40d01a8003e040030108110360760b0140039a592080c01240101d280c56041c10420021160741a0181c1164006810090704400400042c03400c088a681c0400242d070b240c911582440c01600500c0c40094810404900030274003e4001e00100f00f03c0a100651106880d8005000c03034158a10010496844245480b86450541003413600380c0180005084001203c0d8002070311081d103540d540d0b061281529001c8001d92811700c000000d4116002141c400342000602802c940c0c015500c00c46525080880c00b10300c940340e60071428041e810140045007848070b141034080c1d490308050b006c41040e1005000c000050307a824014001c600e00b070340d1504c4044179104400d01482 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 616077194 1250 616075944 616075979
    0x3110a030c1205010509130309030213050417090a03060c110d02010b13180f0317040302010b0901120c060e0f04140609011e030b0c09090412020610230d05100204 71
    0xe86103810300401c425103402d1040c941c4910420000407c0103418601034034001a0342d0400f940060704080c55690122107684418000c5001e000d09400301c1504111003075451007181040d6400c080b22410070000940706070420400b40351345040034101c12420f00081c0745041c44590103039005030f44a1403041c0150400303e4402020418403038041c0070761006242001d01c02c03101c1da10024220360f29031000c1c034103040c411201c25120f4481010303110030074200b40c200203000c0c21034501c0040c07140c2002000040c0c102c6003071999640f0035601044140c00e183c81c11170251070903c5440b901030340122200498842c00e03690f034426001002015000c181c1581081000d210b4902d00581100b05118610800c1c0388900f900000e4510031242e10510140103981e800c800b440081c062303a2200b42c0c0010304038050100b040800d030b41303d242c2401107508036002c6586144480d80c401c40d15101d03441c090703144d0403d1500850300044145580320f0307007c0d083c0601c0d944c0550b60300e880c00c4a0b00d03480a807229030206e4144040000a01503151 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 616078444 1250 616077194 616077227
    0x9090c05090a03020f010c0804033e1917010e060603010c050d02030705070b040b0a0b0609150d0608030a0801140123031b0c1b030106080c0d0303110a030c 68
    0x100303548807022442c0b01140c0c1c00082e100f06514500c1040c0c50f13200b40b02d505101544001c0907502c03182d880ca03100b9541000b0340a0442d540c003000000c540d56030301d07081c0d940d4011528207100b070108400740e00030310480794a04031035900710a0600b50301080407000061902e04c514242400000c2d40d000c590180ea040c8071028100381d100764101052540c101d5489000d60f82d0700b80e802800140c2e25101d401087d541c1e4070441c0f4000f0000d181078405c020500030001d20042c8950004030041c405c41d1032075010441d440c4580012181c0c1b03c0c001e0043c00c209800b010003d01f85804c1035040009e51151101212403440d00100600c1c000251828018460509160014400b00d03100f03080241c842e01c24000105c0002ca82c03a130340484600720101c0041c0c1d403584e8403000004501d9801e0907496035400c441c121380d44c07070369040e03c003240241c0342c510700c0d40710982014820a02221110000b5190789485102040b103030003240007040c1d00301a22072016008001070701c0d00a1030960305e1500e0002c0d024001c001c0240a405a030042d07041c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 616079694 1250 616078444 616078447
    0x803160203250e090a020d06020703080f04080d020703030e0a0f0302070611281a070315030203060a05100e010f05011d0109060509010c05070f03021f0203070320030a09090c05 77
    0x9001c404a104003001d80342c403c42c2080040e81c1d25020300b440c10891080c080d5000b40e00b1004401441340c10b0b401041e800e8000d43d640071a56403401c01395991032000b500c00420002d810032418441c0e030016030150460521234900412002d29410381541b0304040307545c1c1558001c64500245080540420100c00205154140000800721104010391625800d40000060012550250303525611200398401e10301d500400c071040941c11094548000501181c41c103000c00e242141070961261841401c40031650b005000b400c15a649010200140001520b102c803481e03850b03080402d090340a413400701c0c06003890b03204c4001070314509800180056200c0e0010601002289000e0041d641c1c000504001c3e80d04030300b0910f654040160040b901c1524038000030380039004400011546a00741c8502404490080311039100140f54010800f26201e03081e000d070340240e8070401140000a02071094003070109158402e40e207030006c039100c40c5815644402d011000086580c0028055080c10b4490a8440d148a1522a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 616080944 1250 616079694 616079743
    0xc1b15010806040f1128080106050a1211040b10050304050607050c0a120207091107050706032d02040e0a0902030f0d050904050a020408010c110c010819150803160203 73
    0x1a1140c203c04d009071440381405600000e43d1120428007102ca0544052140b160302e02d4001c09481d1242e0f802100001e50034070030f000801d80350480d455016605001d01d2184a000035680d0319482c80100300c040d580068445842c005c2c00d54444000c080240d64503220b0641d02d192500e849800d24200134030704014004240300d1009489400109990031940c0b1061039400c0e580a000280d1900f1800c2d0f001045260800c141e032810003810201824505e0300c03403070031035481d036894000507010b45011016a01c190322206107040600d002c081098910503106200040ca8151291280c6064400848498210640b02c410203402c60030100008400c0540810140c0003501000500914034419401c1d42449940c6800108071281e01541c1214014051080200640700e201180a000380301039541850482c0211200f001d403075401116071510030462034a620220010402a400081c1002d05602114220188021801c418104010130450701c01d1002035918002070b00c101441e1271589001c407410300b082820318 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 616082194 1250 616080944 616080953
    0x130902070f031b0f111302030a06050a0515160f0203151e04122105130302070906060207121a0103061a0102070b0d230f0f09010902180c1b1501080604 66
    0x4c0d0341644140041c00702c3d0b1546000540c001007810002c0c01c0c3c60300c00030500c000c0105560080045440c25901c07554202e0b034403010040d039604400d101c9195020b041020b20401040050b1100c00c4a01c02c5000407000e2070340d9004a85004465480383d9000600b91080c41a504032940b101c0329074040d00e04030b05c2000d21f07003070380d07048010940c6051001c01c0c4800f50740380c2155140d005100c05a40b0200203403c000c54580715090010402d001c55040c1c015008459011030803011a000b28415103e00c1d4000742211031a03c802a04c524082c20384c01d0b14440140b4616442c0441c41e001d141d40254043d480200302e00c542826124600070340c81d0049419036002038010450f00d040c074025182d91400303904e000034800b0940e20000c681070044030242404411424100901070a02c5810741d8050f640c14000d580b01d640d22052a20308917042d12401030750181c0020642c081d2100c648004035401000804414207103039207001c0e40741c0d61810411007098590840c0069850b16010b0700b810500503c00a00245200e0609498 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 616083444 1250 616082194 616082213
    0xa031b021b01050c01052a0408060c030402010c120f0306080a020906120c0303040b071217040b180a060e010b0a031e02031906050402030f21130902070f031b 69
    0x80001d4000300d800c01c0045a0248054803540824a0001e01042c507116003200b5001801c40005d111900700c07417005066130b209010030355082e541d0060040c10540ca680315003042541001b03108a0401c509124070000103070040210784452002501c8011195401c4000035090340c9840d00b0410036580141c1d00c0e0409a40c070311034040d410840c166200522154000074150505010301411905031000040002d000e600e0940100406801144900c0b96000560011108401c1c03c940b01c0d074184200a02140c0410061701d4446d0700120303a0504603040c002034503000340c01d0411956060320403981d42d0359489040c200a0041c5140c1da4421544c13100e6130303410b568520081c00490360142c407605224128040440d20200081c0c4600035a11101d040c019110349801409084105c500f04d01078040c0700402c070b650b190300241c2070700904408034031002c2d00790540a0031007464000b0114001c008564080c0080c0380300d410b1000b090f20034000c0c1c054894141079030401078803c030114070108070701806501e00358000c201d0031342 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 616084694 1250 616083444 616083463
    0xa06110123090c1e04020f04030b0903030106030609061410033c0b0109150e031e100603020f01180e0412140a05041703071506170102030c09040c020a05030a03020a031b02 75
    0xc5d00184c0302c054148100002c0e000707170740008100348650400c0c420124000006181210349940e02401f03036503114403003001600c0545c482c40e81558020b50300c0720352510f0480030929a8001e41c1c540018125290751f00d11a401d949440490342458010112000010202101c4010281c03001e1043c0b04118032180000e020030030920840c2491205a80500d03d0144101012440d12900408840001d425030119454441c5600d00300f00492040032170318841c52802c0e003e800c0c100e85e0002c0450000040d64001554007508070408000b00720300305d805c04180c0b50a65804203002d1030060040803054011101e016018140038a901e2140d0041405810020b5a0000460302551000c13034150400d9015100301502d503000300c2d0f02c001c2c0b100c81c2a103880201403409900c40c4048510508480c43c0c0003403582040741c200c0c4810b6406c014004c0301000321501500346600076444880072481200c8112203107031502411500a2090007000980014a03011115458001d0b420120046404080d9460700904065628070859 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 616085944 1250 616084694 616084699
    0x30109110405210a0b0f060a0918020105090604080604060b0a0608010e0c0f0c060a14010f052d121005010e01051305070e150c19020a06110123090c1e 66
    0x12a42480794940c00d00544c0f802940c06002d080320b07420000990340242804962543c080d0442800024001000303010ba40c60728040361440c82103c140a8004680a034041e040c1c0d2600300300304110001c0c0d282d000b008140c1c4114051800020b1101c101001c200e22610240e02580c07c11180d2401400b840e92159038480d0030012401c401503030382c040310300010018025964500c0890044408200c40c4080d29044156680030500f0803a02c0d0303a0321241d0b80009541d8500869405c400c8000d80500720b60360005a60030342c6000e500045000e0707001000001c079446103c0c4040006604810000ca0520003580240e9024000480c407160466041201145105000c021801c40031a03d80b004a180c0b103001c4c20300740000300c6010b01210302403100c0e1001807500740c0c0000050400c038814000e54005e03003018207404a021541c0140844a000e1800f078044654800000c0e03107401c0c0d95a144443e401c40c164410007080c40158200302d680846c03401c04c040c1070814410709034007405042010020900300c1c03040e10800c403020804 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 616087194 1250 616085944 616085989
    0x3020316110d030e0406080610050f060d0903050c0c0906100c030e0307060512060f0f1201060b0d0905010b030d0e2824050408060402010c020d020a0902030109110405 73
    0x14203000c0da240850001d01904000d00c40100414075a00c0b01304120000c8042d5400e02400340d590354540d54075002200c0c41590414602d0b01842186001c1600c0142da200081085007014004503100b01210800c0500320007042c0d002070525445e0406002c00c1032000400c83d000c506510f84007002c9014180500038074001c10440413040c00c100750103042441543c0002604980b8420744448001c1c0460780300080b003500b07101250002802518020309804508e00f0068002e0604028036014010000c40394120f4002c6552646004101c441d41000545400140300401203403400050910b2821580c0d61103001e0700079002410340100ca00d802c00b851030301424054401c400c1c0c0550110b1b000703200c0c03038415081ca00180c40d0500300040f0072a00e0a804030600351086c030162482c0e04c2940081c0c07400d1140e4460010f0310742100c1c0000303016601400031510028000750001c0c410b0600d55001070301015a039008600c1c0c082e8080018050350101e44100008503400700fa56a291504001c0050060500643c0d1440903081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 616088444 1250 616087194 616087237
    0x60203040b03190c0e040608060105030a06051e100513050f04110a0b12070809070f090b0409060f0f0b12030f030a110a021c0503010b12040c08070f0302040f0504030203 74
    0x411020640e0701d002005013040044a1084024080521114050700c90390400341c000c030302910003094041c1280d01c0240140b054031030b50303074404001e450000d01c20741046942c2d040320903062408046051148002400b2400d030036092104028501c0106102c107211149440e0822280056528900340c10680004542ca04101c840000071007421098005440c1c4090200f4044100e1004008883c0105c00f55160010199641807481c1d644071098420b80c25506d100810401690340c1036031114040c46400741c00032800e10101d8440c20700ba101580c1c9c41d00c001a80c0c8500b0b83e2001984c521070448007100c01c465059400038a03a000655a02560103030717507902e10000000ca101f000b001d6000100c181060303400b42c1d445440d02c8002a4849020a00c9a0181d01200c0c0011080d144101d040700d05a408039038a85050003e08810781004020080c402c980d4400183e0010440f014200117480041135840440c0d10064158410700040c1c560710f0f0480c00c006802c043c280000640c020007034603c030101c03410210b033a619 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 616089694 1250 616088444 616088461
    0xc0203030f0a1812030503040b0618091c030612031b020d08040f09110a08100806010b04050a080a02060306010f030623041503050615010504090c091707060203040b03 73
    0x4103010100c945080006075039854190491858502d641c5205004000310707079980700340882d180c00ea44d002000101d0400009000034130504034203130084000307441c41d030030440c082d10300c000300b010161088401ca83c0017040c02d002e000182250300c010400301e40f07014001c6500e0006440c41c2c03505c488030014140510000408074403074002441c1121160001c24400c08101c0b075040180344c03a40a4000c21402c64a0300d07401162035141c0303000d054440d604205a40e841c10403404000c69810300c01411950140c505100c0c00109040104600c5004e018042a02950356181c03c080285080080d4013103c8103420852a01d005690307444107582d4000803e090422020a00107001c60050240d40c001c4942e140141d0800c80640520740d02920b0b040310159805c10076680d860306001000103d500c4001c0c1560301c08800959180e00c4811071013071154041c1007142c20b094403207084400b5500461150340028090510806c044000d07940d000268140e56000781040c107040090007074585c03040d400b4010119034004041080c14 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 616090944 1250 616089694 616089697
    0x210f2b020102190e1807080c03070e1005030619051e0303160c0f1215020f09030618071a121008010f0902121f05071b1a0c030105060a0c020303 63
    0x30000303c29240100310003030740d01030804140090000d0080611080b950a2007450b101d1060240a1030b483e1034440743d4030f8022045040d8401081201040380f8a001c0c8511901da00c001c98140030706c640c441c0d90301c1b03150403420f1105000d140503807034040410700b41040100307032600e81291052146040c842d0b2200720031000440d1951040b640c4184d541d9180c0b03403052041c0598110383c2c609441c2044c0e11115074540e40e041074000100b0200010b0002c0c1800d05602451503010790041452940445500303080c14104400a41070000c1210a0b40c443c034501e800400342a0f0085c0469400b8101400c0d60001d940d07002c1e80c1d1103046004d82901144600c011030041a10701c1044d501d800010048030f0002e00091010100310800f6196041c1c00b2405420740e01c805280900c00803032800311880d01b4a072910413410a0300000c50140c0400341046c0107106806040e0808441e00301e4608021f580941c0701803006c1394150a00a81d402070042518407182030070303c0140100e586110845441d180c440c80d0a600761802c40c000282103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 616092194 1250 616090944 616090957
    0xa02060f0901090f15020d05090105120a060b040f140904120c080d050108011e18061a10110c040204050a0302010e03120a120b04060b0412060902210f2b020102 70
    0xa130808800040c0c141001c0803000b03c2030391103500f903450303070f9200c0c110640c0d4502030309060b1804107a040c080b03115100c10300110300398815140c290105180d0f0352491126410740c040d4003c150381d1400070740240601121007500000c120419900b10300a4030b0681c0b10800070400f8041140c003000315003103180c414009400284c0d4103688200c1401c000b42d5a403911004d0090080c541110107003441034030000e040041603c2090007408070039901d8032070800c03990341c1c800062041c085014400402c039140d104a58840c1e003440300d6620303075036240c002e101c060b480403481c51300545074021413103a40104400d0241c2c1e180c005c110012a41d082c24922080342342c180009041c01d40000500c0c0040502107000d1607011350108010413030202420f0704012000c8a401804195440c0d400340e4100450100300400c40e0000405203484030358028400000c200c401a800a40c03203a8044001030708046035a8125640c04200f40a140400c0303030b410005200c03100321583c2c0a01503006500e03000100800d011980c0781c0045c000c4d01101c80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 616093444 1250 616092194 616092209
    0xd0804050d11100306090b030d0801060327030804031b08040302060a0c050a050124230111010e0c0f040506010c1209031703010905091209100c020402030a0506030c030a02060f090109 80
    0x3110a407041c0700a00500b4203100762075a0300d047c80c0808803141408103200d40303481000d80d60354110368203101c402c3c3d000d008010302c803008040e00c400030309010390141e168425900d0302c0391740c0d01003c6e030409050050010b5014119015140b420301e0703160340000c13401e0040b078003101d0781a07500c540c980441400544054030380c000064000d0081c0003101c0e0410006501445000b0342000c0f09090590400035a80d00415590007000a02100074420049070203a22071507018112051402da1000e1843ca402c1a095170301c41c6030750080e10351103582c40015078030344801d0390301ca407200940f002c005c2d602e4120002019042c001c48041d040c4c0c4d91402e5001c500500c90302c0c0d840061a0414245030320000c0300b00285180b03620902c60000654500b901281150030080751000e560b010761256541490f1000007040160080d910340c0009000d10708030308000580f500c0c0080d61103100011400a810b203041000d150070103003000d50403407194200c00c0021006a45440a88204440c540030356034036104610f0059400d10f00c0ea400c1000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 616094694 1250 616093444 616093459
    0xb010c061803110c0913020f0316150c050606040902040216081b0d090b03060a0e1302030d0513090908090901030f030e040908040e040615080a0c050d0804050d11 71
    0x11030407506500010303000da1290780da600c080004403285507181c5400b21a01070340861107001181300329070440000c06280f40000e2120a540d001400001c3c6061464a01a0083c1200c10400c00c03045060640202c2001168108044070704003da4410703840f0380009040500c00c2d0341c0ca032015020354032264103071040034600307610258008400c0d080c1031605801000701c10b00044810340013210343c02808100c817401c0c1d6a10f91106440701e03003000000700203900020300303060300f02d610408000340d280c190400702c81c001c1000e10000c2414402038014941000d40507000602482000c0080115019544a40904903460503034002003421701890302c54002c1c459000781581c0044918004010b00000386003086425200f40c9900c590440e2020601c82034600c03140780a0404c1c002484104612210840c240d603019104d0b020004507241212130803031040c10702d900070074415440300ca50a000c0100f14820f410250000301ca02c00c0e03203072186580310314807482a8022540911172090180e010441c01001d0350440a80040011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 616095944 1250 616094694 616094711
    0x100303052215051210080325050307030801050f0405010e010b07030e040c0924020a0f020d170409111c0e030c070914070e010c0b070e09240a15030b010c06 68
    0x10144d41044107105503580f00030020886800400b04104210f5020502642c18180340c00b21085045e0b1404509585a002c80c181c400700042040c8014034a5511075110151554100740a00c901010040307040750007030b4070300001800000a001d0701c081c1110703081e017500e03585d500d603518081b607035a11a00031494015003460000b50705290440f4112065820006120190590644526510003502001900960028109e80000c0f402080745100418006030000ba02e600301981e0b00c3d02a03050040e810f40b03c64801203014826030307074070b4018205050041c2d259282000040b01c0c03004142c204141f6503031442030740c1d1010501a6501482564814203da805685080396a1100140501041d0082016441c05c070000500002d014010f90307058442c0c182c0d01e240031582c1603a51414100d070f01078400c1051080f1142c00c20660382d40c800c0418420a002000c500c90700541840c40501d07090140c1c841c41c07140003c00da06002000b5a000d01030324400b030614000c1880200c0000603102c148402c0009410b0741d0420030103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 616097194 1250 616095944 616095947
    0xc02040608211815040815040605070203070512030402150a0503040507090e1b040f0c0c05070602060702120a0e0a080309090105150405040b040204050315070206100303052215 77
    0x19104051503086107403903440b190000c082d98900ca04862081c000208204020290409060311407002d1180344c0040c1c0b4058542201030f1402074501e1085241402c0c0d00104410018240911508403c0a000540c00c042c1655921303602c0d440c1007000106c901101200060a40da14200c841402c07034280841c0340e80d54540700900070420351085a05895911030250000f40502d124440d4031450030000740940703011404551a5051004070000441e4815111840c07040e18507414465452280e0464031241c00c1c190300d41c54103d041010990080c0300b9074021a041201c41a004941881d814100d003e1003581c5180c0448142c406500112030030b604904e900c1d13404101c4150001c01484d4017442101c3c8140c1300d030380e540300300a0800080120390440e20380c180000c1180341440c0d0400503900300b0082c0054141038031750002c01c2c603205000b05281e0a05d4040340074810926010300c030300c036003000b110f284241d1a41e0858401402c0c1e4070498884a442c1d00c6032540146650000b0900b0b0720181120301007840008500440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 616098444 1250 616097194 616097203
    0x31e010f180f050f04121e2708010f0f020a0c0b040c081c11010b010e040e0102070501090803100f03030e1002010e06010b0a180810020f1b150901020a09150c02040608 73
    0x10f01311500c0240c06c1c1c075100c1c1c06c0c0c082e030020304650303000590351944201d10140482c1c3c1e2164400300c10060300144002d01c00c0c034140c86811600a0700201e8000107a0080c15240d10061f40d002200c1019681d104106012000d076206080c003a1450300454015520b03220b9190006141c3d159038030404180c01640d030100081d01d00041135a0914555603181c0c0d10100011503050f0803140440000b03030104016400c40380341404e06412400180e2003040c00141854059100d072401d43d011040100c51a00c030000410404802031100c0342c002d402803002040308642155806029204c01d0070f841841503210b207000c54141c0c0e100350840e01815403c00e042e154903594801106502d60429203034070b0f0100d10b1302d519803010764528920960844060a0040c90522030710303c0800c5c007c0d40502071040b28401c0410080045121710306c0c03040700000148000307103040c5000030043d400040014001e03203a0742e4010441690942d50001c4114140c03108101031045030012164180c0e100501c0303510003508207080c4140000d80c0c540104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 616099694 1250 616098444 616098451
    0x131509051f09052709010b040c090e0f040204020415020d020c12061902130609090c030b0f12010b04090f1106030606031503120d02031e010f180f050f 66
    0x12a005840c0c07003415402030715098035180c00d1001400c400c030200324503c1d080c1e43c403455204000003080210360a2448100340c070601142c9000c556074440d08858082e0400d80315007000320842d0b1810054a5003043c21041300c55001901d03081000341d544021505558695044a006003900089070540280c0c6550203521503140d035160b580540500181b08096050844c0300304504900c00b03000d00300507980c4a070403045961424003102c19441d03080c400d00710081c0c030400c92880a40550b4603182d600303d00c0d080c0780805488503450304504040c184101100c45440b101c00b02401d40f42c04076240c4400c3c1108045141c0180f4442210903409411700d0001020b0000300d48c9a10030160003240d031107002440440c1030008130311054402a03041301040000400b48620303d00740a90000f8002c00759001d8200280700307420941c1003842c5000700640e00000b4094003500ca0b509101c0201071144003040d0540c074151032501200c4440c8542901450a4482014050101d0388000c850181c6602c080029080c02e8070007200070030088 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 616100944 1250 616099694 616099699
    0x3010305160b090a0b070c080d02060109051b0702100e150d0e0102071e1b0905160f02030a050c010f02030f0106121b0309050c210c010c0206090613150905 68
    0x2140c0401c2d02c44107681280c1c07507a100036104c101c1e0b0f20301e4084d600d40f450744100400d03103080d2001c070000b0a6401c1c05122840b5082c480343d005043e99410505076600702c40000d0909068903001030064149000c191017030f10034a0f82c04603131040000e41c0d1200155500048940e1943d0321010189001900c080e59801801040c0c1c8070300c0c0304000314034880301c015080b0b200700003001d400810300103038040c1c1100c0040d22041c0200d1254549111a00d014003c0c215105030b10381000e44810b40722030801c0344440741040b041d10049120301d03101c280d40081d010081d4403032169400e4901007100014401c07107554401d4111080501319004110350b00c0c941351041600300d543c280280d000080d00d104585400c140640200407100d884200310800030301c0591402d40080108400071100c500a44641351516503582c1010b80e600c401000004103801c2903207400c1c40c1040c22420b685414081010b032a2809615038800352111403034199003032507a44001d0b4107a514440300340e901205092100705841c503030340d640c013222400031920305 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 616102194 1250 616100944 616100983
    0x2060d060801051914012108071101110a0b010b030a0605030604060c0f0503011d0604091a0601020706181e03020a0f0503060615090108250c021809070e04110603010305 74
    0x30760b8140c0a988440382031541105c80d000c014454490b0900d2442d60070801c1202c94010000242e1300c0f0800c50300f042c181035030000c0d200c292101003540c018a8040120140c0406820340300215034a201003840c2c180242c05602030080006003040f81709521903000f901e0010304032441482c181c9000d20180404078034007000500890f02d08000300c3c0c086c00c1605d06890a01c1c228810302000d000d00e5040000b0000c0c81254800e803120760f980e0114110309148000d420031843c1c2e03840c19260410000e444c1c40415448001007146171440385404860b03006030715080c1c40005504040c0241c480368200c0380300d000c0fa00b019601036548000043e5010000403540101c49096040d200300d60b0300c0d10300304041c00c0b80800304210611400c20410b1141c0d84a00c0005a214202c81c4513540d038031000000728600035080c042a0400300342194000001d40c50308410401864503403045051040c43c0c414107194455605205a0041c4000c01e408a001c1001402c802020000d000d4891030f00c84da035030b0420940d645010303008031024500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 616103444 1250 616102194 616102231
    0x9260c0d05091003020c2d0729070204150b180a030c090504150f0903030608030901020d141e0d050a091e14010f0501031509050a03050702060d06080105 67
    0x41d1040d40d0742c1d8000280701d0050440d0b200e60940c040d60140034109081c0c01000c00001c8404407030305201003d00c500010b1303080711380d504010385844d00000d50419841d42c00c06144680c045041071814034000c03003200410325102d2900b480170601030024030184400c540340021020480108042c080c0480500e200c203080000d004039400c2c015000700c2c07400040e02140070640113019550040d0444e0360070520480c600c030000c0261803c0c160881b202d0400c20008107454901040c285945070080300003070423104001e5441c1a68290020303641e92009a850710503c1a24103010000100e00e40a440403041e241d610404450b094212200440c0c4c01001c0034100c041c945004605003512a02c1400c00071a441000c00040c03803244020300c0440e200305542100c40400d0005103040c00300080c080c00d40307400254040403a03103504626202c105940302c048039044061620f040c01d0007050001480254a6404d0309140c7d03510003090000c10410302c5400c020086d50380c10143c000800d8801584085d11850807506803417041103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 616104694 1250 616103444 616103447
    0x1020309010c1b0308040b071e09080f03040b180102120a1e020a030c060e07050d1109130b040b060d0803090f0f0d021506061309090c150203070609260c0d 68
    0x1c004003c040d0004100c04000f0780022000f07002503401481c6800e125a11080c69400a149500701002000000e49444e4081190b10801c00ca0a44038006000186003401c1c107103501c1403564019840140c083c06031100e0510000c0c0d000303002c200000a242e1b08215940c030030100c400b0344000c0c1c44040f01c48a4401021406c110703c0e01c007142070345103a0380c141c1d030310554505640c803018054400c8291004076030088820000c0c0b40c8e944d0070302d4284c1c9907109110707201855008030b0070080f80c4038000305a088102e000f08100000581016680c0b580250320030007c1015450780c001003034840080b5100100900000801d214202e03c00207551f004240380c04040b1185480c41200440d1a0000740300c0d2280541d00420b070707001c0d10f6040701d950158001805042e040c10303d0346e8041c2d101c03100e200e0395014030a9155108814020f100c0003041203005000003100c0b002e220218100025564891884044e015580d100c101c0801c001140150110f14000c207504d41d03403190f441074046207096112002d1507207a0301c680400710030210b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 616105944 1250 616104694 616104737
    0x61b03140f2508162102060a061e06080a0f020313050d11030a030b130204060f09140d0303180203061e0f0714030408190503070e040e2a0301020309010c 67
    0x115804840d403810050071098159401d9000300c004c54000e940800310301030300c0f40300403800d49405217540d00814440c184100140c1c00c03611a40c00408070820b0328041c01180c104c041350b03114110f880c41e1034200182d9070740c0d48404004009003401540e03400e00020600c60500d21230039040500c5130060301501c1c5c5091000ca010340b40103108118983c0150420b006040f6114000c1d401040d0b0048050000c1d25044400395440c8100d0b40705410180100311181600200c40340e004080d000a40204500410786081e010001103501c0641040101015110380c0b524840345035241c0c008603000c2e405000c035240c030704041080c0c503e0ad13803603240e0b50481034960200190407880900d06090088000b52190300c0f500c18200411411580020002e49039400100400c919107200e0b8142c7c00c105ca9040c0e40c445e81c9a0501d038000070400b140c15a2900d2040d030602c6258030240304007040c45d1a20170407003000034101e8520521b003084540041403144d030380755201008000045038190042550030810341e441c81d03250b0040741c0002e00403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 616107194 1250 616105944 616106017
    0x2a0c060d11070f050c1917031b151305060a0b0303090d0809010216150806011803030c031715040f0f06030602040501230306060f07240e07061b03140f 66
    0xd26182d00410802090440381103400100c3c800e05592030200d6a41c02e50300e84401500a4180327076071022803c00e805c140f8003d42c00b034000a1580c1038040c9080c03141c40c5d195031100c02815165019a50b504001115a020411581c00ca8070281903541e01c09079508141045801c0f400c0d00e24098042c0c0c400f40541320003c0e100c4c01c4107991f01c4066a0321106901001110712610007054241401074400c006582c0300c0901001000442c4039030744090060310079140090540040c44e003030925170207144ac1444400011256000c1000200352000101c5420308900840603110105030066060f1604030040103100c80b1b40c00410079078400b038031000d203071a00311401c040a505203840c1c6003003080010f101180d011f00d04840108200098050740c6800c001003600c4441001043ca54204640742d0350b80100003944003d401030b600c06d4002c801c040d0040d41c2c03515034080e04156202d01168814256012072900301400703000d101103c1101680c120f0b1721444651009009548030401107800d4000000c8403e80016050191042 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 616108444 1250 616107194 616107229
    0x60a06050f0702180a0b0f220e030904140a11121303090306020d0207141b120a060c0917010204050114210702032a0c060d11070f050c 59
    0x10302944007001d40125045680126800f050082d04110b400d81000c2c80640615441c907000121504681c0c100141440f03e400000d02401050660702e0003510b20305202c44da0600d2002c0b000c5600b0b8200d510340c40c00d40c402e01c411103910034500310007a96012131030552144034540d18001004000b046602c004003c0c06002d01024820030312000054288151070504101d55209041030000207449075260020307600800010032409034081082c03420710010035006a6601a4180030304118149039211a60f5100640c00c8640215050303010100600c0c42000103c0440b0340122040008402e50340000b011080a8418061056890b200d1087c07024810f100f16070072540140c4402e0312500b00d400d40c07108550003041d400341c0030305080c0144e441c00c82c5c505110705104801c035501130740e6100c0d00d503008068211100a1462420160b1000d4038120074000900c64000304001c42e001f9072a960850540006401c0442c02130911550202e42c003010051000d0304105c000740305406550010003000c0038414540c80b0141400b2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 616109694 1250 616108444 616108447
    0x441c020f060421030b06070609021008060604060c150e011b0f0801060c05010b04090b0604140c04050409140f07060305011d2d13060606020a0f060209010c020d0b0a05060a0605 77
    0xd0440303403128410703003c84400e800d0200305841018000340050304014015204951100500001c518100c01000444a040d00b44855103007490300100c0c41038004d40c0680401e00c2032003a214018440e41d2400504801c5100d4801e02040c2c030291a00c5010b05141a82c05a041500d02d41300580c2501403018040c070302805907101d60f150ba203010350803035058003004815a455540c600041c0a952218000c4c80d112030701078603c40e40f031420900240b10480f03101044200c3c40321010014044040210030894040342c0088602041403820390410030845040c0310508200d6204009403044401404030703050046a0440e2400c00c001c1e030380c0c0e50f00c140e07111546000000d4010f40003070000c1c0403500a90b15072482d07044251100902c441c14250114001201502d03200704c494090074002c1e0810080c0c3c010180504510b101520f140319099942e50290491a003004010b181c0200e5103040c1a4411004030020700d400510091511555003402d540c0940b065541c1c2803460b080c040041d00341c0c02c00d810030744100e40480d6a0315 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 616110944 1250 616109694 616109723
    0x140f010c111011040305101a0307050a0b03071116081504020904020d0c0b0c0313172e05071107150e190f03120207441c020f0604 57
    0x680c01400d2010b41003209030401c4c0300100109104001c5800c1140e51030300000b0b00c4945000340e802035441540f480e07038400e601801b0107220584032050035034211482c030b000103902c944030084240d5181000a41000f060b103e41065050081001c503000c801716101041900c0e241c50104c1d030600031466007140c000e0b421440a5001c90018240100d003032450501410033141c0403500c440d01d030445d030392003020312409640c0007060100c405e5424442e040018500d0850224500118014490319665901c084052070a9070034002580525003103001011640b20701c03800c01c404d117003600010f1b25803142070708030401d82d104864000c25500c1d200c04458042c0942e03034550411080e038000400c507000014604001c298420039000044070884481203d000e075201e03020030b40c070311180090020725018955004401c0380c014140d100300d04449200030070001000003403050704107160b800268141458001d40341d074600d200d00e561000c541080c11094448401d800d6082c1c84601c241c0b0031082e540d8542c1958094414550181031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 616112194 1250 616110944 616110973
    0x9040c150e04050114130c0e0d08090a030b1f080c041a040905060912041a0a02010b030d12230703020a021507080403110a200409140f010c11 62
    0x3800d82880515110305815007032008202614000c5e445070110640b00070070380d802891b0240041d4030a00104c401006480802c4c58024404409a0f0515000b1104070700c0f10300502c94414100e40041101401c0351107419a01d00d48801c1019048824071003042120451480000310307503c0040407a42400e009000f501004420040113002c8580b040c1d0541a80c290700010584490040c0082d05000fa0068001c61a08210f90340c10490303810010340c0741d51020003051041c0002c4408500900c20140310316a2141c001c66026801401030080042c0e141c4218208181c50582c00700c0e011030320100e1200203005111001c628002002d410806889603044040005071185100368080c291a001c503204580160300d01102d9124551402e80b44c0c03000080d6100200414550440040c1d212581030700e0080203010007a440300180719050700201610b640300710b40e9a11603a60341e504140c0d074068105003c49000c95103003442a40d21088141d510103554208204422998016070030180340300d190001420140341c40311307003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 616113444 1250 616112194 616112219
    0xf0302130902182119050a170705030d0c09060f080a11040b03070f0201050105180402100519051c0b061c090f0302010b09090607050a0503151206011409040c 69
    0x40346490141001c10b070f00c43c0d44101c910703c0280c41140012203481e660860481c1000c10260400402c501100840c1000400024910358119003002c02140008100241418540300c3c569014040d80310204680024011541c04040449015260000c6943e6211b2068801e1100501540049007004000594901040d0009040440d00078800e0b0700d0a44c031894412141d41041c0c80c0c2d680095040000d240c0c546409108507405028111100c090706111407a09170242c00c0000c1c0005e0268a25002c0e05004a00507015101c03000c03080307080c00f4850300340c8503001800e9422015042d4441341c40148807140340c0150380f05800300a40b02404940c80c240348490500301c115120546e000000d5a0780c22103c001c1480703000708a001a120b58000700c3c846102034100101d290012f05105c0e2150031684c28401801c0d0040122a07802c0391130300742a500c3e42c4d2490b881c400c0542105003d00d80120501948041520300440c015040e9003090010980740c200650504c01c00d40c90846008101411a2000740403201c060741 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 616114694 1250 616113444 616113457
    0x316110f240310030c1d1b03010504020a030f05090f060a0e030f18060f0405031506221805061006020d021209042a14030c04052202040e01060f0302130902 68
    0x85036412821340c0d0741d882a20390003d030340c80104070a60fa4285004404071003900c02c1d41060305100c0417a12041924a10f41c0c6620042c418184140d500160385019280250042c002c8045028800c100c0b91500400160b00d40c800390008121902417800041d4281006105160b9250030340c400560515040c510b00200640c000b03150600101c440180900c125943d12000300000d0744641d207040e84651a02c02030500e0a04036030400544e12244608002c06901c07840c25540120809a4603483c0801f07090741142c00408600d03980002c04000b0105640c28004c2c005074550003906c0712901e4400c2d40340d4801040f44c9591403c40c0c22401038115080d05107e60030740202411b4110b4005000298100251034045155400714081800c0d1903515a05034200ca9000b014108a4015420417503186160004510400c2d1180303001d03551043e40001491142100e1a451025910b051004115940c1d61514514003841c8024071030315000a0100035403c542c14841d000303407501414609003c1c4131003401c085c41c0002940001c07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 616115944 1250 616114694 616114711
    0x160f0311060c19060c0f0c0615090f05060f01020d021009061b020705090106090e190e0f07030b011d04060c02101d1015170316110f2403 60
    0x9000c91038901606000c80d00182030020807500001d80186803a406640e011940801841b82c1200e5100c110b0342c02000400c540b55002c400082e40c507917510706044503805140c200d180c1d40c1b494590100ca03411419800180100740480f02c0f040707186010001240e40e03c80d001c840c1c01c0140c129521000c031030310180e08182c488a208007400304604022a60780c2c2da803810910500700c0164003001c01000541800070b0103902525a0f4030700414801c3c1805501a079130725028240c51220f0010040020144145500010703103808074509980d12a0908503019a462800d8003007a500c1043e0f2000010340001100551580311540b104080d03559515503d80c9401040380c07441c031405500520031030502101c0148240b0800c01c034003c690440846808980d01e00d0990303404103070340c2441d18000c6c2d044d0403c0c8560f00c6003401c840d41e861a189030b468145141c603095002e0341030710656541d40d035080301003081039101e071203c40c20305e090f103003070301c0740d994050801004c8488a0b00041144194121070340b41084503600655019415 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 616117194 1250 616115944 616115947
    0x10030302150a0b0925030e0c011112040f031208131e02150a03061401021c02010b0a090204030510050f071404030210030e060702010b0a152f160f031106 67
    0x1e501054132224120b0341401103080a1a070011411088045408160341c2850208009514072440e103507034801d1408090705000c01e100ca07426250600b04036582c484005000c845407201c5c0e8800001303c00d000310380011142c2c00548440710410750b114201041c0f15000031140b401c80c4400c3c80e02c9007c1c6107104402800d82e515602101b43c40940c45010480f8480d000c0b4806c4695100b41e02c08008048a0391a00001c0302c2090352100c4031400c3e0b0340020100b109240c0500072040810070000207070b00610414480c03075045001410300040140d425805003040300d0154081e00d64030340c00d2407044821204100d0706034009140040100e40014490044801400041c2c030303070945403544940015230802c00088609d40082c0d25158440d04419040c89a1347d0400075900090002e040e603080082e23070540c11402440f007100030650003400014800c1c07020b803d224131113070404640c101c401c549242860400305a1183c2d540701e400164070440c20307814020000c440c0940b6040889031304550b03179042d000c0c190400c0c2c280e20150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 616118444 1250 616117194 616117211
    0x7080c01112a120a030807030e010e0c04021c060b1c090222091703070f2102090604050409060e0d090513090f140607020613080a0e150f1210030302150a 67
    0x107040000c4404c0324001c0d154603038145030810004043d139900b081c90445a034100b50f031401038401c0000302a4514501101c000d43c8a46903a40000c0d4003001c4039203002a00790900200045c07162501c0003d080d25061003024517a091030a1400009841140130700940288050f010026081c8000341100a0304c002e40c10041440c000e140ca0700741102c07200c0800d1243c12003001050003203c58000000443c0d1082c01c0c109a000c2512003070b014940c85801e00140304900c1c2d0005210700c0c06a8405040707501030240108200021442420084014201c52440485500c1404038050f10300380510003d0044540c010070390301144407162401000391615800c229400f00b040321002c00001c055180584a118070304d0010059443c0580703000b40341080146c018400d0b0030b05d2006000c0440d83c10740485840788007030b00b042c2c00d0304e482060126296425000c00c0004018001c984492401401c2006000d8480c144040342a0341c0c480601c0d01008005030301c8020003603480a0744002101c40b209800c0c83d4040001340e0005003140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 616119694 1250 616118444 616118479
    0x7050402040f08070617040813030b091c08090a020f04090c0b180d020604090e12040620030c0d0f17040309170a031d060c07080c01112a 60
    0x2003040d00003409420880b64280100c12082185000512403031034210503420414200361051003000e04040d04001000450f0460380085109400041d0360082802407685880a185500c1e29580710344100400c01654000d000c140c0305085540c0142c032a40c01411582d1180c2e8200402a4064150715400030b44494a11012070300811501c2300a158004800d80c0d1081c040c0c0080310305100140c0201c1c4981c92001e090005a01d461003a1025070b841c0003000211202450645440c04046984444500070b0025000c19a680c2c0101080c900f402c20b440ba40942c0d90840c1e51381601c90140c400e0700780b12544000d980c280b200f44504461b40540d00c8509024a100041d014403100305042100c0079004208550410001c40c800ca00d01d18a1444050000d4881d055617540d0003481c0258000440000c0500d0034210220780d84c13484100d51381c00002030204c0750955a41c440e150f0316400303581100c6012549042c0603580c00308000c070710450035400b64112000b01a00c41d038890101d000d41c10b42e0b450b0300544110840360029 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 616120944 1250 616119694 616119697
    0xc060a0e10020102070b0a1503020607030e090903091206010506250c030b01060822120509041a0a06050403080d0c030605030607081b0c0604020405090309090f010e0705280207050402 80
    0x14401c0ba400543d6036410380c14120002c01d0090050342e0304501d42121545108006c0341804180e980c105c0b1a2940e0b20741c641400c44220030b145001e00d5008030344d50140710b1900e81c000002c01c81442c060300d02e004458a50106140c41c1c041c2417040c0c540203002040503450030307a14181039440602d0a140c007a01c1240c100e03250300386a405603070001c4449185007801802010341040c0e0159025110425107010181100586260440d80200043c00a4581504254000d0041066030305110016104104007080081010000c80c40b01040c18040c00f02d020020a9140c4110120780c00d0382c0d0001119490803000403000d0300289074802251082555030038010170640e5013400b1045c007910182d5074900717140c200385802d0742d85003034040440740359240c00b004800700000c00411060390094045900040342e40d2100405800c42c400c50526a074004400f108014400d0203225002d41030700ca0700c4076418043da1b64000291954131a081c44c41503094403c5054104046d1052900031003030481d48103480045035a600850240d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 616122194 1250 616120944 616120969
    0x306040e07030b0a0f020f070201080606040512031207030c050313020a181d031809060a0306090503180102060618060310020c30092e0509040f0b030c060a0e 69
    0x1d840c5030401c1c403404c01900d00400020348002c920841c64020724110000b05840785081c002d06026030754000680b01e54500d070945d4010300d070280c220020f100341c0300d0405071694450540540c0c00a220000300d000305100e4481e070800c2000c40d0b00caa038a551102e071140c0740000c46160049901028081b0041140640d4890a4a5551400c203010440009485001c1c0329100071140d010455801440001d12101806100300103000042e40c485003a500c541000c16070303220040e040941405e0900010008118002008154002c10094014180802400126102c090603294950302c0039116010807203940881402e1904900700030201d507007401510b03400d14180d802440503070307445402901c0c01c0b030303800200e5802d110281e03506007000d8070b07030714214040c00700103401a100c12030301552006072104009410b4889803500c028443c8810705104a40340001400c40d0310120b0b03407a004074200001140d03c02464081c86d001410028082d002500b4400700780556908603141c0c0c5020422030fa81986200d03140d400d11441c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 616123444 1250 616122194 616122203
    0x80606060417011e020405010e0910140406090c090e07030e1203070507050a0b1b0309060109050603150f0103140118080307051303080901031103070806010f030e190c050609060d020306040e0703 85
    0x1b1034610700000507200c1170004000314041c4030074034104258003501405a00036940f08000e400301c05c2c8817100104009003200e410220046140c0700303042c0b660729042520300e0210b4406101040d0160f440072000c9042d60341034001120742c2d078099050110303205440005594001001c0c40e01a04004040e1601807400348030600075180c884040040c0880d4019400d441c0e0720845001e10001d20303508208a0b4590b03034020522400030841c2d55031020030b45558062001504c0c0301c0107205100541c1c1050107606030486030030301c012200180501c0c2e000012050600915403071949000400d0f850358400d071a00380d55135000800319003c1010411141040074000b00560026500403c225070f180d141070341c0054201d50054289031001d000a108000c26203030710100c020b6100ea401e2910700c0b82101c500101340c0240c14680342040d001c0c01030004008200307002d01c016040d9203021f040e070740b5050781d035400a2149900c1106159034010b4810411400d14056523002145c07c10303c05007000481000300e191701814600590030445 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 616124694 1250 616123444 616123447
    0x81c050a0b10020111031303090b040905061003092001030e030c07031e050d1103071a0402151809060d050303090d390c080f0f07080606060417011e02 66
    0x2001400c0802c03101c00a031019000800044801078401005804018202c00c44140007030b454900f01403164000b040140140c0481c0f81e110707038035080300c1d01c0500300c1183c00c02d008140022200b01c56038441d005032035040390000060720b40410520707028041d850121000605040e1100c04c905607040003040149001c0c4c0100e4040c1c1101303030a40c6400d00c0d110f4000140f940640711404020f402191010402855814141c1003407100810100c860030b00314042c0d4038000d400c4410000b0820915680c06805030302c141c0c400c550400340b2482c4104082c8241c054403043d032900e1400300345141c0142c21700c0701c1030b0780e040300c001450b400640c0115a245459030784210764050701074100d506511155600807032010850900d050a24220342201c41603c0444140d01400603480c030b18504610040c801d003c40340801030100041600da501d00202c40d0750b5a00c0102c181000d09510840701c0000b1403110118449029210041030245814901051102d61038205078419505540e50b5501d1441d40a00ca8510b00e19410300b02d1015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 616125944 1250 616124694 616124711
    0x503090a05030412050105060d0b010e07030b210d0221130e010303050403021e030c0402070f020d030203090a0b0c0303010522090309051e031005070c0510050103110a0f03081c050a 79
    0x203007583c82c00b40007139010309271100380c1100040100c040141550300c000100215079940d01005c4014280801d05660403c091000144070640310380043d454081149040320000310350034004a0351000b40403203410007600c60400000c0d80184a0006001d0f801c041d82d120741c2c442d51035502c9240c0030318083c2d00840c0850000142002103090101450b0869005448580c2103072181c030001c03036154034000540034401c56001802104004031491110459900600140807060003031401030342d2a80511085482200f01c20f40000d01e6480c000c003180c0c0840415001342d415a482c0c0824402000c104020341641200080c5812114442511800c1801e9002c1c0e6598503070580b9040c1840080010410822490303000d66000e41d24545000611806425490b000002c8644d51484c0072070781070012142c0100035000300041c03601c88220075040306050b80c0c01031802c0e600c0408404104880f12800c0e205584003044a00da040020501d02c2c4042c182d040001494149185110011401102c004035400040d02e6990180c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 616127194 1250 616125944 616125953
    0x8030108210c1009031e030608060c0c12070507080d09090606080601050a0c0c1d040c080a0309090e1002030106050a020c1507080d110304121409100503090a05030412 73
    0x84444264060000d610707140c01641d0320790f02e406079031848070546500ea181c1c01c01014443c02c1032180d100b0788107a0300920791a50b0800100a41940d100d04910340c0700741c502203440c442c0000d0403206c0000300388004009405070f802903220f0380d1708041d1058030300e8040c0c03100000e01008180040c170003851103030b629a00d440c0c0c06c041c010800c44100e50000c008002030303401006816600035044404080b060b0400501d4000e25143c040d44a07090b64201000181a052140c1240340642d4422030050b4031603180142e030503489041199881c002c10b2805400a00500c0381000f10300f02ca0f90040b4042003d810075941c406098601880a1ba0320031780c402c90006d440000c014601c00d5041c010368904200840b04050110b00514883d0340074020f40c50064080c01000030300313040c101c541d9803040e690207105401d40f03a1645414103040306104560703a0461b0100d546035554100b4000b04c0e108031540304600914841c004e0181d200c04540d580c0009000b022540715039950f520203c6c5040001c0c0000308a081c581450190030f5181 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 616128444 1250 616127194 616127233
    0x20708060f07090b0c0f0f151518070e0a030b1602010c08190e01141008030301060203030f0a141006031104050d02010c0f060510210b01030210050708030108 69
    0x600c1e103803000c00244004103038011016801c0b20300030b5549544825440c56418205620080c02d02900c1c810003d45910001c1f000c60341028030039521112510a50f81d421801c803003001180b020390380c082d403110180ca000000d0110b41640000c1c903850084c4a2030f482201240e4052100c0d00b058402e0002a400c022030300c03103840d0880c282841c0c0c0b40300a0110300d40101010f40528030241440b003480d41d4040c042c08c1451515030003e070a4105000091001f8150b100c8410034652040c1c9106e000d1603080c920106108200104881c12105158010340c07a50742e170302400915000c0098155800f264071030241c6080101000c0140d80a000000c0284041d1441c05201030103c811089412391289410300081000c0c1e40c0c0c00701d0702904070346c080c281100c085c000c1c0e103400a88110780f034900034070040c80d001c107100031010080e89a0098820680755100903100450031000701588109004003000c80e40c1005100506040130025400d080e6410170030708100469035007000c00e030000d1f0407514040e4014150707440300220780c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 616129694 1250 616128444 616128451
    0x80f0a0215161101110102030c0304170301181a0301091202010b0a08151f03030309061107020d15021c0207050c0a05030d050a050f18010e041a01080c070204060602070806 75
    0x108941c500b281c80600b0201c0e42c0145100500f5001030040d4400f0242d0042d0080c00640c00b00760001c55807072900d2441d15949400c240d40591b42c4003200900c590302801600102e0381a02c248800584a11902c400401e005d0084000d0f1020b01c0d00400800003c261400d008180a50f44204086401c403850510020308542c1d2482016100ea0b1f034905041150f642e0115144c40348001c010b202021950f50039400c440d001d6100c41902c0401c5050100000030b056155000900d094072806060001d82580301842400e4007503264003940c45000042480005110801c050b54440c010b607201600300514586004070502203044000c1c030766500020b40c1c1d0208001800407050301c42c0e041740c1c000c1409041c580440e913141a0095014180280000c28030710050242c02a1550382c020800c181d6030b1010100e940300014030450710104c0c04207007055507a581c2441c0c50300940751205108405084d1100c1000c0044445920107420100b000004200b00e10258450380180c101801058004040c01494940128039108006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 616130944 1250 616129694 616129729
    0x1a0603240a152303030c0d180902040b2502151e16140715170f28020f12180102090f04050402062205010f02072d080f0a02 54
    0x24106100c81003c828026401d544005251600c900380303c1c3c082460361156002010003441158458089a54403400e06c100540c03000300d0400500341d98400c0c1c04c059008502442080004c10f00900300c1d025442030b203070b007101003150b04041100800e90b000f16079a204030b054a040c00d140e0000d5811070501d284500304598202c24080645030001d4041e03034150250103040000c04403500080b030b171003a1101c100022030140544000d0781280101503c009021144c490b00c140c11462803200000e00314801c001d000c41e1040700103a004040185c0080130f0755902d00051402c0d29502c903400c0c405000c0714202507018004000075110301030f09506011010810a071600100c0c2043caa004001628054035286501458144203075800b00b001d485a100090340c1e80944481d0741d007a0340004a18000d4904c480c250071003241d00a13243c94403510f074030440480e114102c4d40101004588042020055826401004070b00003001b280b1074503503d9210540700c1e06000c03030010180110ba01005c182e0f0709610f040700800c4c0c01481c81 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 616132194 1250 616130944 616130981
    0x20c070f081b031203090c040b0f090402060a1403010305031321150605061801030b010f020a0825050309010201060506070506070305250c0b070203071a0603240a 71
    0x4196809070366218400c0392400155000303124128540f0100400034140b0401c484003512032030f00104040c4e6402411401d41d11403401c06603101c0b09418240c802c1c0609540140859109640d15000e011190b0710074220a010003200d074180042d22070041e03001e9400f030341c882d101543e80c0b204008500c180d02c8080390441840440f160140b541300d401020500603090b45d0000307500000302e0207030906400030800c9034800364029000140000500e02e40004098011000340c80c00c0025054040044034000000006100540d02100c0342401141030303500680b041200406210740b0201c0222414200c402c1c2101085445034804039a0340c0710707580c0a010780005040103031009030500341d4580718039954490203270440c0c06243e580c00105018503504070005449a1220a81813181e0b41c10303800080800040f030f41c040c0c61316601d03400031072012071012040b90703080d41d04804514800008540401400400508001c1e414803e0041039401c81c87c0301189185030000d181d030f00216502e4110b041c00d0a07a18810340440c10300a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 616133444 1250 616132194 616132199
    0x70203040602032b02180a0b180d050f030c0a0c0504111213140a0308010e0903030126060a020a030e01060506030c07080702040531050c060c01140a020c070f 69
    0x9002050300c2c215200d181c4102142c9204040303402c48500440100138600340001088803199055070703130500f4040f40507519242030a41d107040c0d611450003142d1441000c2c456502d0200c1c46441c0111700580f5044c011001da4201c1d071044042d07a859a032010380c2c04140e5400050000f001e2001c000c00e44001008103480078030110b010300c00e02c02050305c03900f940c4802c000040c0c4040341301d641c0e11450312030758240d119640c0c480b041e0643d549030b07585040000c0e00701c0000c5c03100c1c000030510350407110115001e000d00030019030650b42884048505150007400000d1700c0d07842c600c03141a01803810006240901880c41005984050440e0000c040d10221011800541c1c1402d0003009142c8a42c411241d014020090756600c030300c43c1d450700c910300e8400c6440c0a5803081c109014025030b158032669203e0315640481041d800004031805628240010b0400a0b01c00d81000403045014288000208682c0070184000034013400310448a013441c070019070306420456400708404803140d104000d010007401810701d080c4015407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 616134694 1250 616133444 616133447
    0x9110a0807030b040611120c180d020d0602070212060c070606080303040f170904020714010507081e0a0f090f020909010e10090501060f120c0e04020f0d030e0d0b09060702030406 78
    0xf5000341000301030382d81d41c00e02c2d1802c0c2e282400645200301429801010780c0d0822a102c0d00c0700e46c1210a911010070000051000c542c44c02440724444a0741c007424202611b003058036490025040510180d8008482c0310142c02510402c0c4038052003010359212003625030900c0c1c101030088820540140c0c0040c0e104005000c0030a54100d0819001544501c5d1940040704035241500c0e0b9001e1042d010750018004160001001f12a030702009820382041c008110b036030b035484d208448a06054800e0302c00c0c1c101342c0040080e100c80786103246a01020b0420041214181015141e04940004105883e66007074801c900e001c41c580700c0b005a400810b103134001d2105484030340c0080c0c1c4031460010304c1c8900503607620780300041000a41000c4000d204c09130b842d40c45180c0d00c144031026000c044034110b410030705880c03000c121114902d4680303000e2a000713002180444420002d1100001225005609001226540d14603542d07031044029085d5100f04003285c020700304145510318040002d4450019034009200074003c0d43d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 616135944 1250 616134694 616134713
    0x4050c0f030c0909160f080f0a0c031403070b010e04020a05060c100506030a050f070f0f14012f031e0403030c0b070309150e0c040b030613050f0109110a080703 70
    0x81c022941d01400e92514004149040000c0000b401134400400001500c5a0508031b000119020034040d6010510505d4990340c03281619103005250000e803910520104800c0650512808900401c40740381140742d441d4564545400d0b48000800100e1804110860901c120300200400d81650180c1c01d000600324850380700e2031f401c5c41d440c45203569400012000d82d820024a280d030754014090351007003407100540b103844d00c40a008080f29141d000707400140c1010442a004100d403000308081d043d07170855100441e032240a556980c0301c0416540c105a001825100c0c50000d441c00d02c8006550f1441d90103140540160448070442c0b0180d42444100007103904900840800c0c0d07400f004440066844d00e006900070302c00040003501d03000e941c0c40828038014047d07104003042100f88046501c800490340402c03092314640b106042d05a04044045052504000704001086100d00f0a481d001e5000e0103117030382105c207001c0307003034034421084c54034036400b800c002d600f0801410446000c0c2603240d003591180b5514 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 616137194 1250 616135944 616135963
    0x12030b01170a090302030d151502160b0a23030a32070215150913030e10050403080d0207020a150806010503040305070f030c140304060c1712040b04050c0f03 69
    0x15280c5034000d03102011700c20700856545000c0b00f8020040245120070f6406020758901172008101c0c1c0d054080002540005405a4804942c58034480302504001d50b03090140c1201600801b0300c007003040904070700500c01503005a290441c0b40785585a00c3c18002d11405d5a05070600140018070401207946611100d0000001c4e400b04100d100c20142c5070320038128038010149800140300c1c0e05610a0080c0351b200882c8641b041c0108598909181d12040c0500031740780d13400480140030485110a1203400d0814648012080250741030032410165aa11103a0f1280d00010340c1c09509a40000d03820111703c0c1420b00100501048811419901d442d9140a0f107080809803080781840000f000090030584500d007120405580a07503071841650443c0707000b900e40c01000300708a0300d50180d07090000c2c1000c800001c1d1402c41e8615510b120040030991a035240e01400b5403a420800c01081000c00446a080d1040c2d6005034861415901c946c502410302a0400182070340e6a0301c00c21380d07a00b80c02d546540005040c0007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 616138444 1250 616137194 616137211
    0xc17012f27060310030201030c05032202010917010501051f090b0f09040f050702060c0921100c08100f1202090a151e091401060809011812030b0117 65
    0x118007a440c0702510700d40340054207180e4014800010440c8100c0030b0509082141d2003a2001d1050400d50441560036010031168100f401e601c00303820810709101080800c008a0040c100320014a8071003441040580c20302d84003881c84e81d116001040036080402d80030031105914110912414000200184070250074400d80c464bc1d180881c400c288240e20740111400860b000b401080500c880c50034580c06044120f40c200c2c054000c001c00188a40391080c102c40c0c25480040070360030004402e4401e05c5c41100100e881c91010310820031480c0081d060742c85500340c000700a0329603400300d00e462800162160b116030024055031240341c100300200c41040115007852541258108959a0354040b000001c001840c01c4501b00807030301c400010300720040f0003403100c6284d2603185060119180c6502c441500c074101c10346200b12400c0001005600d20412540d6003240681001180c00b20402c44d0b442c90404841400303560304040c030102000e40c3c80c0c0620803400f50305d07021300b016441c007107803840120420714004003880c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 616139694 1250 616138444 616138477
    0x4231e1905030417071e03050d111e0f0d020f100603080a210504110418020607080310150e01030507170c0a030b0a031515030b0c070c17012f 62
    0x300c80c20014005c60014201c05000340d8500300c0c9035544008001524481902d03c1d004810b000c80c04584103040e94031581031400c2c01080200b0707010020080591007642c44010500800401e898204410b200303403412201b05074001d101c00b4180f86445030a050421003550f00e120f10b082410030009228006076503002665003001600000d2414100100210320040d241360686001d0410040010102c03030319845000541e010000e110300b4420b84502403140c2407020f54001c03020b2012000141c42c3c1030042d40d105940309005106940e4a0321545c5000100040d442e0125480a000c4440303540c0c14802e00d07078041c6640c50501040b0311107414000c02014040d020004003a000110086401e000790091600d101001e00504040c1e641ca0a11b81c0d40318a103c0c0e200c01c4200c0c1441c0345041204100c1c10b60700103880d0071a202d0b103603607103903120005150781c40342c2011241d0795805200040e40c1081410082281c0007401c00104110f80d505040715010405030042d00c2e0711842c05060b000584046400303590707072030003110041c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 616140944 1250 616139694 616139729
    0x20103060503061e150d0c06110307080315040b0a0b1206100c03300b030f03070b1302030c0603010303050c0708070f0512070503030c150c0a0804231e19050304 70
    0x81149829640d0b05500301d11b0104600d0108106100e0800c103d6241da60390181c10547c13904099207901c134080025180d01c9040c804141d00c0c4540700c0e045412000300400015901c0c1001c000f01e61502c91507401404814030105400345100d0450b2071043d400301b802c451440d4420030052029200b0514544041c0401800d2110425415047d242c42d55568220800c0d2078040012040c110000e00070592009010740144113000f14004400819039050b107500980a0840c2e65611081007041848030f0700a1b40d15100b00d034802c0e0705c0d40d100c0500540c044c43c0a561425524101d43c80c003941b600744103a0210030141c0c040201080b01b95603007800a01990400c4070071040b0310700001005890710b80680c01080c1c2c9408001a04000a840082e050803c1c01445181c5100d583c0c4007208190344d801044844c8011a44450002c1e00181e005a00604841170741904056140b0400070f080d4503060400001d800344e030b03012082d02101048204480c1085000b040f00440c0c1d03060701d44c0d5030300e40c0700d0055200e218446058250341 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 616142194 1250 616140944 616140961
    0x6050a091e140601060206011e091a1c080912010f1a0a0608070e010e011701301211120d15052e0c0b04080403020103060503061e 57
    0x10900180c2007081850841000004803007007480c5a0800c0b00c0700c800348100345401c0705010070740314102c2d07038550007405460780307804020310340c0b0f03985400e402c03d14000e00000030400300a54810144400600c200365030304072801000b03000c24503e0f0114580013242c420f100480000b0480822070304100802d032004c3e41c4521254045501400300400381400080c00c0004050058a41824880c0320f8002102c00311201c0e5a03030041a10058016a01080002c00c009403860143d4003031710700d5001d40003040c50804060101c84401310300024081c2c001603080f49080c002580ca2070380070244800b1000400c0a05410040c0690701c04001e0740405007207406201c1c01110320b0b0301a140074401603400ca651030b00702e1955800804400c0c00140305845000c0070b0307800c0d070140210300b40c2052020784060003448030b00d144510540f003201c80c55244000391a06c04014180200400052580041c280500d20074040786446604510000d410f680c500e400040c0a0342c00032040200c5108201c041101c2c00c49640421501501d03180741 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 616143444 1250 616142194 616142201
    0x90111011431060b151204170d050f15040b012304031416060906020a030c060f021602040506060f0708070507031a0a0e0607050414031c0203120105010e0a0306050a 72
    0x40100b40701c40550440000d11800c0d8010084400c1e0880340800502d80e00c0146800d14007500088014015007840040d0019448000c400704000c001c20090381022403403400981502d2080b51444043c0090405000d107060b520000100d220408840601c1344817000c00008140065600c3c00228003039001640b421003810070402c0781c0c0550b400908038000a100311107120b5443c00c000c1000ca0040c450b4480c001907a501c52205281619120b90180c03c120030b1984003100c1d4002942000e5882036581d400142c002038651000301405103500850190050742030041004079800141003600502d010040b6144071200503080f50388550340f0a007515191400d40c24220328166041d080240100c008a40d46014612114116449002c144009010101c040b4000c00c0d2a19401d0380c0b0040850414070042c0f001c5070701014020016903019080352034042c03030303200061448071180820b64003603000010803460344a030144000d8050007080c01c0540d101c101c6480498072140c3d442c4406840103586201040715410b0540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 616144694 1250 616143444 616143511
    0x120e1819150305160f0f06140c2506030f05090a140106090c0c021e010e0609030c090709031703060f0105030702010212090610080c0a0e071103040303050901110114 72
    0x49582204c541030416540f071401d40241c07044510f28442c005114400c011544055401d0740c0d4440392106002e182805980d0000a85010f4a0041950020900c003140004c6400b02c041250124082c5150030009422140807a080d4000300d4104420010070010001d10243c0d0030f41d1100c4039041a078190007080380100350303640100b81c0b0305081c030005007050740e8014003802030b650007211521100e000114084952100054416003c01d0401c290b501c01ca14207c1c000e00054007015080d230b00b08800e808001401650112042e0001c03809644080c811300903440181c03082511201c22603171035400d01800003104603402c1c40055042240001c00100050720030f40503141c7c01440622080c400f070810107001511400101d4901ca00e4010f0b40800089507a00001c4040b0381502c040e041603101030600341c0b40c2ca0281c5000300f5410600119010544041c90200020030007036000e81d4071141c455075214001089030789003040408641e8100b010004020007525982500280f41c6910054000011480c4415a07081c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 616145944 1250 616144694 616144703
    0x140105070c090e0a0c0b0c071806050301050a09060e06010e0c1e0a0215060102120906070501020f03090102070b01050a032003010e01110409050c1c050c07120e18191503 74
    0x101202c20011800500311045a1044000c07003d00c945600031b402e80e60064807030102195100c03010412120041e00d04041101c4503d4001282c0103484070046401d40303405a541102003503a0302c80800034001144200400c2084400c042e144652401079400040c81c0017070b0402280313000c001420b00002c06140346508006060081e255250a440c1c3c502940380c2c06841c4e0404043c2040100042003584081803c05c48610469038031824402c0a4043c403032144c0100c03030112450341d03003041640c1e0342c00149000745d4800c0544000144c0c2e250501c0c0741c0740610340e070b0603030007680035010030881800006c960000a03d441c0c44403c1e441c00013209242c0010f409410203102034411940303800c1c464610707084941e0040c015203500f10014803003038680010448851080d603030000f000ca20394440c51035107240c003900855000380b040c0c400c041c101041502c803400c84e851140403640216a00c0080819142410400c0811240484104403103603d801c4070098007034400c00d0041280280d8031410f40102c1e6170a000c500004e035810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 616147194 1250 616145944 616145951
    0x5131104020d090f03080702030f3c04080c03030427060315060f0b13030b19022a0d0f030b0111030307170a02090d03030504060209041103010519140105070c09 70
    0x507810303e4204c0c0301c8410410360004480381c0000d0340303c2d80000104d81d640e8079220392003071500d8041c5c01440ca105164240c3c08905414401c0200d800300c11100403010b2926400e84030075519881e143d151032400024040b914001c5c1c1092000b08214801d00c200101e4040417080160420840c00161074000e205507000142001085515507800500540c08101075900004151705240d03161310035041c03540190032081000011079842480056001d036a010340001101c020144a48261620303c0140c0c2c100c1c01085e03061031442401480420f803c61070f68a00500320320080c0241d6038414600030882c100000c0c5107014591103000051160b40300f51440b14a010400041c1c0b5140e0074101300090004012030040d41041070030700041903406c0e90a10032079550540007421750302da410aa0f54240c0140c100103005844503a0300303000d072000741e448501a01b0881000750701215541d604042c100118103034017070107101015116a4060100c0800b043c0b040d040b10000342000780d100c030840e16203050868000e0b008640810308 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 616148444 1250 616147194 616147211
    0x20c010e030a2117160507050f0106030501090209010522020c07051e0f1918020706090609030f1809050c090a0608040201200c040e010e0313031505131104020d 70
    0x11107407800501d01056901d264984e2410301e40d281210b8000c0d40c4a68080c2000010860103501590040480781e2044003070381c850303280d07a4160f1405c4a1407548241c500e65142d07094407085281200b5150b0151004681010207040c16007003d1141c5450f00f041c210340e80b81c2c00503000d00800e6040002d80018100100740c4044e6070521129104402100308005020740c01d465104045460b1a0304104d0f007120420b0b80c0e08003154600940034550010280d1105400b650800c403a5010039080d01558035002d0144001080304400f0303140007481608a0000002040b0440c940d4101040014000d9030031124008030101c4c45456403280c405652182c40d00300b0f03520400401c40041c25a400200641c0b0541c003d80350b2081d0303202c0c101e40c0340c1c01008552500d09000d403c1440b101d822072400307034040718003130100100005441082400301403a55000120f088044424500c08208000310001d4172090701041c0802400701e810031100d6401500b10070b010080250600168002c0341d500c440c0d054a140304050642440b2000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 616149694 1250 616148444 616148483
    0xc1009030e27070203040506190318030804030e01051c1a1906020c300a0b0c1b010b09060d03050c19110405010f050111011b0503071b03020c010e030a 66
    0x84442c00b003440d100010700028541d1030000c016501258006018945406580342131104d1040c2096134000a040d0354401c50718055540c01065004d541c840e44540e40141880c0c1405414103400da10300c5070412404005000d40b0f14003045500326444040c14000c58460707500c0392505076000c4185d42c502c1e000b4203400980304141c02030039903100441c1d425800b40e890103074610b01800300c00b0402c110342c480720000c2c10300c1d0403c1e1310420510904007000300005940135001c9503515001d20001c1960100e202c200301040d000b03500c12040a00c0c2e031401c203e810081041c1c06105011400c8c00f14020f010fa4444c200d075005060625004000715030f00a081c100c2510782160300c1441c1d82511050404040d2450340081d81c081300181454814941070701c1d0046101c0c40c20328a0b1000440e402a030b490307003c06082d503d54460030a807021001ca024110a03172521042d889180260004000b8001e5482900b05514648020408070342c011132181140442880c003100103404d00c002103803511100013001081c01c040742e80b00301c0070003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 616150944 1250 616149694 616149739
    0x21f0f0c20011401030b0c09041b0f09080a06021b0a06200c101a04020d270812070504030f050d2007090f090f0c0f0b0c1009030e 57
    0x15840d14070303400030324021070256508075604092144054012080107001041821400e0356000110392041458413080700f011405444006000d007504981071000003840c00d4012026240c0d000d002d1410203a420b1a182c01650307580c00b00c0001030a031960000350300041041d54441e00e407441511500302e9140c80310318502000104042c0c280111101d40c1b50400354103420046040b54040c05400d0000c5c15052010514a0002c01074500044002c1c11590901c0080341ca8600152044182003c80010340312496080680c0c1204005401016034050415090015a10600740c44010b8101d800098042e500c04406643c0c6100c0c2e608050154103113107500100b04000020704251504081d580c55010007088401480140b00d1803076100c49a4005013018082581aa4410900150450b40205504000317807210f40d000c402d05501a100e2078104181407007100e03121a02c9100528070384000d40d10703010200c8156a101c130b080566445829481c0d03900c10080c14440d0800310f0000200614400c0c05001808680050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 616152194 1250 616150944 616150967
    0x3030a120f06060215060418050a02030f0303090d030506010903080d020d0c0212040e0c0f1b12090a060503061807050a0201060509040201050a0c060230130201021f0f0c 74
    0x3000e003050112411022280a95421203200d900202403a100041c10f441000308000c0026404c103681e20142e0006103001c2c050404024015005419441c40c2401494108820039002d081c07a035208100b40310b0345c024001000120701e803c92a00240540b59500100c64100c003543c0086c11482001c1460b510000c0340794006c250081100d102046401040701041e41ca406504044060240c010700c02081030890243e0002d0f4454100c81040c1c2c13615280080c3d2190716000008501c1c1c6095030000848074103c81000f5024040c0d19410805090113110b0002401103c89405100b0800401101044c003603200c007000091807114a0740404114070340004001c01e282c02088449006600384500040d01e41042a0b12a0050340c044e074480786415000703403096031710728061041100c040c1d60030005a11182c0740020f81001503002c02c030403011f00c0300d80c0c00e10402c1203940182880304184c041c0105100140c0c0c000505a007000c00b070050500c0a01070764201038004045c0400302800c0c080c01d01d14a9501e20b680000d10300d41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 616153444 1250 616152194 616152227
    0xa0e040f12171302060a0e040b04021b07090605060304021c0b0a0b0a091521050a0302010504020a0b03061008100e1009060608071b06180b1b160f1103030a 68
    0x105503803000350701e182100f815680650417000c10404096010f202d941c504900131800360000c224080c6a02c0450101e80c171085501c0c2d0800c49064030000000c0041c81b146000303000210003440040c2c1040002281440080d10083c442e201c0c1326102030380071846804220102e600820281d5480c90303c01c1502c40a840c4022074641b00c8c111070440030404458510414050720400c2c00f800c42041e05144c030010b043d56500d5000e022002c0c4c00d1410900089081090902e140c0c4aa030020805051074414401d8020701604100c20b41c079001c1c000c0103441d4540400015042c0c0c400d103400700c00d507102c0381c2a604040c0a290083e000041c50300007084601042d854140303080758000382d0108909580d40c042281c00d41c0307090700c50500182d40100e040605800c9080707558034503406070400154842003041004040c82003608100d54030385607441013105e01803c8201074007200c50500009032070101901d40c0441b0010300510014410401000240107001d60000b001d850b140d0044c0c200e0ba40c0307400111029100b60450030f60307a032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 616154694 1250 616153444 616153487
    0x30301150e0406180f0605100207032003030c030904060b040501080a0b0a051003020909091c050921011d0c0303070201050c1908030405010b0103090210080921090109050f0a0e040f12 80
    0x609230800844c415540e285a0307010709509402c0d999640905500074400030101a000e80011000e540c00744000c1486403151002103039201000401c1c082991081e030300c0f0412900d41880b04101c1d80e6000848258000c401000c0050b080041d031001030b4010440c0d03000303180c10101101140101c9905903000342442e400032121f480e21075888030040c80d5201a02d1102d240405400090b084985001e07001804d200c01005000c414600c103400320b000c034178846400507604180e445481000c84d40f41002c20030b64040e0708400107414081c0003440400c0d80c80c410108028104000022501e1603003a0078000051004100b1100c01401a154109124142c2003510f003590554a090200a070542c041d01ca14040c40d94040c0811000030040d0300143c81042000305045204e004075010a00c0d17103030900761040c030741580400807592902d500c1c0000401a004582216005107012440c5a555541354900071044030320380e80f0300f00703d282d0ba20311300304212818917070b40186a03502140c0d1152505402c50032040c103d030085040c12 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 616155944 1250 616154694 616154699
    0x1603030f061202150705030d090308060315011203030b0d050c180114090921192a050312040c05040b060a200c03120301080f030301150e0406180f06 65
    0x10304907401072080c1458008440c60b002c0040c180b14050b1650140c03015120780c10f00102d5105d0a0039944111480e21280c3d580b03040120401d500040d0301504890160000d000c014140c134a103080c07086040c0125807907294403010b03107030800d4425004580d802c1d40c00f6200c1d0321100c8007850130950303400c001228641708595032400010302e4a8030f01900350480341a00281c890207110082030202920003c1d101e50b4440c091107030030802e08922207144d40d5907a000e0f8207983d40e40f4034072041e0401c103e04a00702c405081041d078240c0c071603000e40c604130401c2484403404c15211004000380381680c45c5121307a80300d02c4c3c3c07658081e90810040c00b80c1c0290381e40440b07070181c900388111b91501041000a101d16800c59010540c40c05419007811040454080d00000c1d50701201e11303501d41c180c0040e00c0e02c2c2c400329034a031803004000014070100c41c050200c030400e114000011030455050a0603105008180302c43c0000308004005e10011554070b42e0803000060511551210a03040f40c040302a010340742c5810246101410309800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 616157194 1250 616155944 616155971
    0x801110415110a02040c030906051311120a080a2106080106090209030607121d0f010c0e060f030a1e150503060c0f030406090b0906010e0708040f03051b03160303 71
    0x2002c5203007140310b001c0d01d03120790140c1c2004000e0802820200406940d40e040f02c000940e68410240504c60034240034280c00001e00d84000310410850519015905408080510940001e0207200e0b880d480200f860300c59107494802c4820300b003406032062540c030032080d0000c170181d41507114200b55842540240b0450b5151580081a03101e4011141c2d0160711400000b4902031094100111440080002040003100980c04280000c1500481321880d00018040e0408440c2413054034240320321801c00d011a1448940020100e004400302124860b50000024500700c01c00d40c4401a400f030400c0242c18a8042c1d43d10781401882415004080001da040011602e4500090b0701e52080c0000c500c00c501d04403540360440c4081d040600f08542440c0c96041300c40018601c4494240325001c10801040198501050360140d0103019001d6003e100c5140d083c0804108400c1114a01c19010300303199075183e10415072500042e180440c280564040030840e841a06800c0f0b040681d4240660f6060001d660310500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 616158444 1250 616157194 616157207
    0x2100203070509130b030f01020a0306080a02090c07030314010f030203160f05010302090109030c14030709060308030601110a021002100b03070506070b0402280303090617060405060a0801110415 85
    0x30307490301240301481030a40e5880c140c040302903e20360b0003001141a00010000c0b81c5054248054406070b65004607401035003030307450700c10003000b410880300804c4580e505801041102c0310242c00010300394000144802814042d8200385807915aa210450302e569680c0e0000400303404900040b0b20034040d4182441c0030303d42078542c54080d18070710340032140b03024680401500254406a0300c241400b54001c00000410320080499000340001c291424076055010201814011143c2242040c280f5016003032010480b5413041d00d90080084c2031020011051005403403038010f1112000f544052840c142090345c40d0701103066440c5a50320b203401e001c00d00088007019282d501c58011282c119009001c43c2010410380311403150003d00282c00d201d80070b01d08070f800c00000503048000d21035a9116107810010507a01c52401c0d401000c10340350240c03e0021010000030480c0c4003500041c42291540045401952844410002005120000c001032080000d02c202e003a0464414400703080001016440c2ca40c0c09840c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 616159694 1250 616158444 616158451
    0xc0602211207080702160e01090c0801060c02300a0b01060311090d08040803030405030403030e04110706050402031911030607050a200a020a290913021b0304030c0602100203 76
    0x404141041da01c00c02c0c2221000c2008200008501c24200c000c0300138000400820082c01b0303030101d506002d60500b00c2a000703842025625130308010701c420040141c654840110300030107078101c41300c030980c2c804c498800d20250100c200c040405d26000e00e0003200c03d400051542156031144120780403a81c1c3c0d4440580440e040d290040c03e404070b040046189514004c800754641c0d0b0b1007013810351b0500d034035915084d1464104407011603180c7d100040500a01d604050300c6482c00c041290f045c42412507144202400307004c1d8250042c0f00ca51684042401c65909014081c0d07500140c0c0b000c3e0104003c00e0a00c0809400c0e49030005000c3d020382d40208100c94894001c80300b454019883e01904107944426041d00381400202a0900d40582c030b06200c0103a4401201000926105004100c910080a540c24510351000c090740c045000c00c11400059844880d03143d02111505400180c44040388500803407500a003c43c1d01426010005012003044100700c40c0c0c0b81034540da03a0032034141c2d010120300c40302240b0059 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 616160944 1250 616159694 616159717
    0xa08041409090c100302130e070804152901020a12030b090609010506030c0d1104062a1e021323090c0105041a0d0903020105060418021005160c060221 66
    0x13010100c001c2e02a8008000c402d00d10491203150304e40d11220340d944c030a401d0303c1020009480406000c107101c5016401c3c100b040d08490100804d05101040340c81c0400030070105a10002a0b06614010741c0c028010418030640050001110000d086401001000416029403140001002066607414a62403036410303200003811541c65034989500c4100241c215640c041806034a40c0482118101c05502a02c014100d80e10b83c448540c00308844102d4401840410300c1311a00c5450380c00c0c1c08601c00708422240002c05c0c0104000040c443d0000c6014900ca080c040484c160501b6140981288481c90f9100e6040e00750802031000d407503984078943c07a00508609035000507014001404410445c4000079461202c0f001d10310300d003c0489070080142d801604054001d40d550b242081880d0605006000d4a015800b15018110304964001800750a960003001c00300500810f0000c503003005441c6526540d50009480c0c3e18065403030800a41c3c4001b5940d02c815640714083c41402c540ca03400b0192103138038214 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 616162194 1250 616160944 616160959
    0x1d031305062209050a051510052104050d18030c0504020901031b0e01030b030703420207050c0409110409051911030f0f0304170a08041409090c 63
    0x4120822899030001c0b2110b841e40c00280082072040c80078030410a0003051001404640d81c40e214400c10125900103044940f0841c1d28424a40540d4031040ca001050f8000d00304651103046c441a00c45001003250030000707500390501e06000c2071060010340520010155034540e840e0000d484130f01100b12032a8031009003051501c0d20140f0541c64550040e00100710103150024841a03030400307466465000c0d1008402207989501100c90b40e5074940a00e46440310103400400030640b465171071821044401381e070940340d41b0081491419080c010018941448601c160928044a00100e400001c4d8028281140e103482030007102010780c20980101a00d044c0c100c17148590050854084c04054120300034121004d000c1c4041c04403405d180003500034040e600034005203400d40c04100601d0326112014013040e9a035800001000b180090000c11a400d882c28031440011104504031500d01d45007050302c0080c01d51a020401040004200c1c03908080b061007156030a44d039403038019030310b512292400c070841c2d0042e58 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 616163444 1250 616162194 616162199
    0x81315090318150807030c120903081905070f08060a0f18050a200c0109210905030109111005070605041202010c09030210030b1207090603021206091e01140a1d0313 72
    0x1f90300c03402000d8080d040080d4030307200c00103208040701e26500088020072800c03030920031070010602030011b00b0030082400300321070b09001d140500010032081d03010f0308104a0000041e0f0584440300d444009110300c0d400c5001c0319441d01d000105c4400900e18182015140000040d034202131402512810061b480c0501d0340e00d0380c2541d002d8050381c04180030003983e40d251201c400000b1000e0040103a000c52080c206014418075840062050301c050748058442d070b04108020011521130502e0300071541c0c08030b031016034032001c1c0d10054416015400010304003a2a010400c814420f034011000385004483d8002c1014180200040d41c1c0100607002c0a50040c02580581c40c4e40343c001e51140405040c000e1071041c8540e800c8607001c2c45c1980c103800040f0025110001002103041040107413944003031324800381c0200c0c9062030206682e492268040c01d0401141d4032008100f150030f40c00480d40d03140c81030700003901d03241900d80c24024010340861941d50200f19901001001c0c804002d94421108501c9907060162 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 616164694 1250 616163444 616163447
    0x8010c02060f0c300a0f0f1103060405060d0602070b0103030e01080420040b0a0305030c010501050a150516060f061a07170901020c06040603240501081315090318150807 74
    0x2a41d44804160410040c03159044030303400540040c5c814600c0701000708049808a09810a45000401500c1e80a040083e05441c0260130000d49920100a0b64002120340c1e07000d00189640c10b0900001e03203403e200264901c14041c4100e01d8a060780c5c0203403641190000e0150044a90000440340134040840802d4200d00b00c0c040c1c2d10000540d41c1c0010408260f84080d4030001d400c50701c540c6e20031189a8800580031801d00c00a006450040c1000c546110106140c0001014440140610b020401200280300e281100121006a01494000c20104416419220944010a52409401c1840080700300c8040c0c02200f1104039809164084c048118400f089100e0613001c3d000140713240e055003c1e03120f180038103480c3d80300500300400070b5a40c0032030300b04c40031104c0640039032100301410702000c1043d40130700240e60482c50b0390743c016580661102d100d1285d0300f0301c01d0011015040810310182050703240c0d010300d03501a8801a070030300b2481b803543c201c950703d07400136060820310000f200108440600003403065 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 616165944 1250 616164694 616164727
    0xc04060c140c12061b1e030a0f0617060c0a0c0b090f01230105011713060e03040902070b220320012c061909140708010c02060f0c 57
    0xd04034208840721071a65000003030041c1c10030101c54000b0340c460405c1107085d454030541c60810044e0f03084101d00c1d0030380240c48000080110040e00030005400408100000c01c2c0b68030004203000180c2040105503241d010791000c0b84078290000406110b11000318000303e100d0004ca0300b410542e41c0b94000d40300c0e00c581c0c1d40e501352040200718403400e005012640720000800c0c020981c860041c03480011100400007041282d0943c1a0803150402141c0f00039010076020003100036801050101c4a40c08001c014074020020701061030741c03040301e0f000200e00003c01d40a50b802500459100300740201c0c0e5940ca90003115140030014598800449c02400814042801a0403480d140d28103803145000d810721680d038603401d42e1310701d00900d00800a2a9035906130395852440300440d04400c5e1002e81903904060300000801000c12140e10500780ea190018000c0004100e5030808045c001016103003890b5948045030b000381001846800035019540008100109280b90503100e002005001c900709901500300d43c070070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 616167194 1250 616165944 616165973
    0x10305010b0415050f03040b01080f06191a040903081909020d08070201050c07030b01051206100911070219030b0c030907120204020d05090a05120f040b09010306030b041103060c04060c 81
    0x4c1c00f1042144180301c0224a00540c4554004c1e0702c00405175140c45005854015070703003004060394002a041c09580c5107220240c10801032030343e0020500074585811400010101c2e07021943c020f1070032424404140d00b0007071541c4100d66072240c0543d800c080c000c02e213040d00e103d0803009605c50101ca1060000070030043c042c099450049c0340c05030070070304040f844602c2d15200f40c00075602e102e5250010001440d10360405c100080c040c2c00036000d07034200700110240c1d0600d43c0c02510f40031501c070049100f42a80d40401c1d502c0590300242000203072080d0002c451242580b50105a69008d441000100840440c43c104d90244600400914000d441d200c4004051b00c40103c00f00d038030507003c0001010340c22a80c003482d03000790140000742220b9803851800c80d1424811038030b0281071a03400c0c00801200c0008205480403140c80c5880c4075503d43c07280004078000d04964000519002c0581d082c001840b88210707004820500907012220b154445114800c0d0390b004602c2990001100c4c00c0d40c0400103140d0340b0b0350610 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 616168444 1250 616167194 616167197
    0x1090b151b0c0a0f090b040e03031803091003021e040501090902090a0905011401020f0f0c0f030106170319080f010303031a042d060803030f040c260c010305010b0415 73
    0x541c0d0b0703030800100050703415400310b4565040a1014850341e400c40c429151030140c103e81c1044171103e110b0340c1c140c40303010003003600e2592016848a00700c0c40405004031a81400300600c03140480030f0a40d0050000e410001c1c1150301d141007000c0c4013000810751000c460641d503058403070414880c039003038000d00a9400f0740c03000d80d0407981c0d4204c0010a110302e8003030315018043d064101d04030206024002403030700300882f909401c143d005880c5072020200104601e80010300603524403c8454045010a014000743e910100c1d043c20742544517031800001101500380c2c030035420041c4002101d00c01d42107801d004159560054007071b0300401080082e0195003c40e0340345400300b1200c0c8200789800e000904460300006020407000107a20200344c000d004200300008034200880030001c05083c01141c40e0b0341e01005118403404905030010a091001490407180204458045090700d141c1d15007041e001c81c1d08803d107040c1030f845001500e542541c083d0045030306a64004805500b0b06151610614074444124239020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 616169694 1250 616168444 616168453
    0x90a1802130306090b0703050c03010b071a0115020f030316031d120417010603120c02060c06010b19051206100c2f03071a0306040e0f0601090b151b 65
    0x5030340161141c5204000c60158000044d014803a04008907060801442c0c101098600f100300b22844000405517410340d640000b2554440364546000500da19421000700c4000084400004540d4002c0e1200c0b0800f04d525801c1d141c0d070107018402c844d82c1340425241e5841c1203a03060784446005101303900242500850740c050784204034481c03400078140b1168203410f500c180c41c0010184405401c0b00e81c85802d104000e0002c200580ca991a404924402604204c041101c03a03015901556141c40584003200d001000703031906565541d101c40800d50054000800001c4513a50480e00340d4014025540300c13014100b42c071030701e0360b481c1c01c100b2803031800710b020840c02c1c05002032051000c40d12420103044d4030011460001ca00a4508000300121403041807242d100e07500c448400e101132840d0504c8001000e2421003c10b4480e01d418001901401c01d030450303003150b441010504044079a001071901d040310000101007100c102040c040c803401c1c070302825860324144810001800c4400702079050398441c9607820b0665 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 616170944 1250 616169694 616169707
    0x402150c060603060705070309090b0103061a0901030c0306051c08191d0301091203020c19060203060406060f09031b090c020a0b16090512070e100e010b090a1802 71
    0x200003a00a10192912584444104442c03030904010b01504207183d410003500345110740c1c0e00282503103268050030307401d10380315500800e03664000d40280c80a0242c500310710041c141441a920b0035908480d06090003c0e0815020a403407074024031402c016100c024102c4829041d0521a110240b43c0202040320703016402c10072620108031035410a11844100c2d075600050224400e81011004046403200d486070345001c0c2d00000160711801c9030300001140e400d001da1500035035044182000c240500100d81c03040c840e0b840404120003640194403880d41150101311654851504950340700c8960300c82008035840c0b9a050000c65400701850801c003001c800342d01d50083d119850b00090b00c41545820b0090f030301210000042148412220350b124440c2440c1d004140c10b04180184054003d11902d0b00481075180003448000050014802411000007004d640b03040054043c10214002e20460501000780c20001c10846400011074128100060540b07040c5401c01c62641c89045104400e03c45460f0b003000030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 616172194 1250 616170944 616170979
    0xd0f031202031012140f0f1c02210d0507080103060f05011a0c0a14030703021c020a03051b0706050c0c03120a030b0a0315050a0c0503040c090509070b030f010f0e130b0402 75
    0x183c0c00280140ca0141c0441c0090828091230482d414154403094080301219202c8107900140540030f4044061100c402d001065202c078600d40b0821a00c5040c00c2e003070200300074145400001d5181280e201d280c0402442c00c03220314100495070b083c02038101c00c541500d01c503140064564064060a8a1a802d80b07114011950340c48940003d00301940005400205001d0300f0f240e01441003060308411039104540042e01303140025140e0405034030060521502043d04449074441c002840f001d1000b44003298030070384c2c403100050802d0b045003021584502c61403200c02c805040208150781076003007041103030341060061a42580601942c04845400940710704001000c124650b0003003805001c9058001201d003000414a42a240b000140b0004e0010410a00c400035004030480c008035010004001a1317522443da1301d03810310b1440da2180c00020790220903c9248012928801c0c12a4000318903002036030f60700c0031054203084003200c250036071980b070f85140c0340400e50b50031000c0e40c00b03440241004113044e11401c0c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 616173444 1250 616172194 616172203
    0x504080a0b06180f0613090b0a06090b03030f040e1f091a090415091113060e0a1e1a0603070201090204050106080603120d0b0d0f03120203101214 64
    0x1800d40300240514140480e82c10000034043c0c010f000712826031010f1500c441c5804a101018007400d02500100c0d0070341c08403640990055504030350101d0080240d0804004e6400a0043c90040074022450440011840e140000482d54008282c0495908040c0b07012620400020300501c091703e020320010505813561f85000c00342001c1c10040f400050380000c2130741c1c8403603004a000c1410b80200084c0c3c041c803000c80c100342c4a000c0c92400441d00424035060903e8a503484215450060b44c001c0942401010b1000c02500f12400340c400c001c0815010799a480c0000096036205181402c10003c2580c1d181280003041d00000302c85102600d00240c11085440818100c0c0e1046980500503550351600701e04600c0c0c207006003030060059282c45001d070304207100044e0302d0304907200220095074030000c0c00a404d084140c01c20074910307400602c0031005000909100c120203410110032070005e003003281452420a00303403003035038012007860140e4000f40d4100300c02c1c0192001a00d00994460000d400071803d650030401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 616174694 1250 616173444 616173463
    0x4020d02040603032003030f1302030a021c05100b06040513110313050d030b10030f06030803091c02011e020307030f0603051f090209060114130e15010c0c0312050408 73
    0x43e211005035080b20031145c41841c08003e5000c1c9a0000c000340b10709105081c0140c2c0d007110501d00380a0440352a0710003e0314000c0180e100a40251007003000e0003100702c402d11039450480c090710503250050b404103414001c03034090b02070540d0700450502c4203010b0703070405d0a45042072503005200010f180d0010454003006030400c2b80d0328903981c40c070754a0403810004240719400e000303400c80c24107003c5584020001420f90b621250306908041d034450750742c122402e843d00320900850304000c14a640e07060100e10b21b0f4884400046506080070b044542c3e480c1c0314070521a0324000101c17140e4484446078188200800380d031015110701c0c10946c80d56403680203100c141c030584005602c500000c0000070401a010b02030000340c41c140c0300030306250103400805625403111483d80108241b80034400b04200c4820200d03940501c2000400610307079200041003074514401094000c1000b00d00304050f0b01c03005401140c140000040c002c04010f480401000042c45900d413071540c1220745c1c1455400c2a03151b003010341c54281c514 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 616175944 1250 616174694 616174697
    0x12030a0c0e0301090c09050c07140f0f060f070c0317090106031101020c0f040f060e040501060f15050a0f120c020304050a05090f010b030403031112100b0301180504020d0204060303 79
    0x10a2940081904240e000034100c0701540240018121612031541208a912a01c509984c8a0000400d4100c00e1300890766030b80d41c01003a48d120007107100e0309241c0d0365146a0741d2124520400c1c030304420b101700c0080c1003407089100e8a06440030303a0300c800044a85087c240021030500140c00007003109201102c1000c0e2180014100001d285840c5040407680150304505180c199002428070141c562188403408001c0641907a0205207103210b64035140041c03007070fa405030070712030b00d0b240505c000c0090640204044405107010008444d85400070652624007201d010004500c0c10015a801c0d6070149582d401d228045007442d80702d00c81c800c00c40c83e040d9000e5151110050f0800038080c00340f49000c100f0340000d03050995000f43c00e032800482542220206029884030b511004c0006000c2500c01e03000b00600c1074006030503e4a42208003007040841806aa101d584940092008542c8131864000d4078100d41c0c00c078040303605204030110100700800e0043d00a80e0410701000150340540c40300d00810340118442d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 616177194 1250 616175944 616175951
    0x1106120c07033915020f070b0f060f090703150803040603050a20031f090f0e010e0606010c030e060304140d0c08090105030601120e010506041409120a0212030a 70
    0x8034600204480c041c01c440c01512103000b00032610403245450002d10704484007090401403d942d080c560362010f84c40000702c0005000180b020750341c0002c04050900544542034002c01901e2741c030b0009400c000100d0703001d6009605104040864079205103507035042144c80c24009400442c0101c02c02640f922138205000d80d0380b0004040107003c0d410300ca01c66022889031070810540150314145029541d4481c107824120801001003040840d03c0c0c5500f06100280090900d27030f031aa202d22580203840b6104c03032201c00d6454115400c3d08040d06004481c0300c0340c50711000c0e000c507980390303001511181c0340c0348d40c1907040000150f441903040c0c4074bd0004600441c042c1e144900c0c040541061146022214080e01040009015a0f100040e25120664a01030400d003041a1070355100e83c0101c0788001c40c248c612070302505000c2c1c088071101040d441180900d809641c20b0060350101c1310b8011507428181c90301191680401c01480f408105500500760040032072050310f0180e8821081c0134040c0e002a5500c22280d0366 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 616178444 1250 616177194 616177207
    0x705250c140f040504050307031808031306080703020901080c0d060305010539040e15030316030306050613091d07080c090105010306140f0a0f080a0b0c090307031106120c 75
    0x1880c2c40c81c1460024100c406000364981a551107890303014082c4003c050043c01c104011000e90355014031341c040c08602c0102c0340ca4852600b443e2103140e82d50b01c1850041a109000708169911a000300d07140d600d01030712841c1c1e681d200c0e4008160150300c003021031039043c0e54609003c0b000910030f004903402400c400309030000304810400f00d035407000c1034410344094549010118501404c0c0003010796080b20381b46480094507940c0d50304a02c050610340c90f034590b410300000810089403400c425404034071301e0007558208940ca4943c400d00c8090310412600c11054562881e08000e48a00e03a08070700001c0302011690900707c40214000c41c0b81c01c04642042000340c00c4400d00c080b040c1408851180104400d19043c010309280600c5141c0c911201480d4038040e0303e15101044454039814100d400400c054a40580301c0765031108007680b6400720306011668400c00c280030038041402113042d907241d6134004000e0312000f80780d42e0b210450b40000d0402c180e00401c0a00501c00c8080c10105024814030701d110034982d6510 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 616179694 1250 616178444 616178449
    0x5010e06030304060c0b040201020a080d05100f05010509133e0a0e010804050f0d02031206031b1e060a030204150903230102040905100f09050705250c14 67
    0x200000d06050003030388140000c22010b6031000c20240c0e190f802142030f5640d6141c43c00102e08091a25002400c40000002d411400140ca54800c41c441c112112281000700d4855a44260b000024420240021014060280c15107400310b016901102c0c0f000300014019018107005010003d04030b09948011015182c101494184002d20514100d4903120380c0d150406840d80130b0700100720258118100701481e400102081410041d944120319a081201c0c201742825400950f03c0d80100d078100c00200042c0080ba24a080c001428941400c8142e101614010500140511000ba003a1203002a09015540c2c0d203c90300e07444003e00e95034010390780269403a402d00a50690b02c0c0142c620070010051245020070103d540c08040721a840420007004642c412011a064064050b5400151042c3d2407c000e03c0a00c1d180c1710280350403980011120101c00baa00c01c44c140480b00210303503d01c04120204015450000032052005820030050744d551003500c000e8031280500c0700039402c46002d42c818120075240c9032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 616180944 1250 616179694 616179719
    0x10207030908010c2c09091c02150103030807050403120807030b240c0c040e0c0909071a07020616150501140307170c030a03230301140d030e03010c030501 68
    0xb09901c20003441100c000080080c8240108000318054504c00f800120034a1105407144190303600090181244d800c0480f20740d6200c19110001c1d00000780800405820103002042d10100d014030100030540c0381c1e1031900c043c1d40403c0000c1c003c8007044410040480000c035441140000d00845075200c0304103250032540501211203031001f440c85440c4083d14100016104a5220802609250321503103a64040e094249001c1c103034501e03194800d06240031410312031000142e004030100116407260b07983c1c0b01d49000b21744920690081003030000440390408103441c4100002c0100f188040d10721403a0800080100c00382c5000e10b42d00725036102520304e400050000500031280074000015811003100110070028be074407011403040070b04c1c20381000e20341c0b1104034050214815508002d070540d24202241d14004121f0b820455190310041d8044281074001000d84054034103a4242c401c80624008031241000184400308000300c04000000a01d030300561802c0c02418202c50b55074801042a50500c4038580c0070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 616182194 1250 616180944 616180949
    0xd060b030a1e050c1e1c05100e040507032909030c0d02030435010606050a031506091202150a051309020f0a050304050703080403030e01020105060a0b1b0309120102070309 75
    0x19410700c000d00003c0c040c590110f9042c2c840c5c0800c0c10081849003810180a4006ca02e0308028400c6802d01503500009140c0205100d52905400046a280c03110b000800c1c0000039500644558080d001c1400050042003c90501586800c00c0401140c1c2d0a94285540001125036460305d42020a250401d070784104110011560680091410141400041c280c1d40810100803240480c0c007029120f400c9842800d4920140040e0000340300268a030840507046038030248074040000d1030002120600101c41c0c0c0c403a8103842d11035944202d09843c01d1401c65001004404c180e80c82042801c1d0440b502e407e440c028191520203880d5191100081000040005540d51281041900420801120381c01500c11a01004254100203403680c896080ca02c3c6400042e82009003100800900031041c16003002c0c040303601080c241d000f80302680d120000d01540608920918182640030701500e0281502404046208210081104d040210620010b0b000c0d9800c0f81944846950018003c0141079120900901 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 616183444 1250 616182194 616182251
    0x30228021e0d180503030708040501080f0f01030204050601032913021810050c010207030e0f1c02040515221515051c020a0905040516050f0d060b030a 66
    0x510a41c951401900c800344030415004021100031140b007002c40f01543c0d20701400340a0112521034603640f60015182e031190203294041502980044d0403501b4003549144a182980080e442591959003440060300000c1d007540d041c962203043d10440c06000100d44503000418940030255404036006014842003680510f6118500400c880c1c150b841c400e00c444004002d065070084181c1006200840e55170243c50100b80f515400010700b20f052581c04000040003040486088d49400000820800300310218501054800300c000381820148c82d15038410b0f948001c0c03441101500c820343d0000509072040070103c9002c0b44040d0b0640080c1c44650340711342503801400c2e030b0070741c04200d040c085a1010404e0880c01d400802c440001d011500c0300c40003005542410644d00195154104050090b00350f45441c01765070b014903d0880091034605181551030010549911010300c1c1a0300c05c184024158040e0044e0b050a50322258002403c3c0400c000942c0f01d44491100041c02c0d5071081c0500c600e86901e40d50609 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 616184694 1250 616183444 616183483
    0xb0601030e0a0203060f060102070b04080714010309051f020904150806060102151f03060509030316050f070219050913060c020105062817010c1b08091003022802 71
    0x1d0044e10005070844d04060b00f4030348143c00c0d80d51100100e1502d0380329000008155004940043c0e43d02c0e00150340030030340c0c0741c240c2e80f0b45030807003c18011012510f68020280c41030707000d0004a48042c41b110240c25404218440140c908221030300410700f565410041c2e4150301d0003c0504020040c42803101c1c0740c020000b44041c1c4080e06002603003080f070000181c180d4500440ba801d0310714550403458144402194130044c180110305d020141562260000c40b19959000d20702074840c080d140c400c00c2184d51114001895034200741c0c8a13028132001029954050149855503040814186c1d54005407910411110800703400403001440d02c1400d640c443c485100641e0f05000901495a45d00007511101580c518040ba00100c81c4c0190b003480404168814003d01f41011000e9420b500c1c103410008042031141c4485100041c0d8425030300348803960790b00c041d01c1080c06100407012460701c4d80303401d40032002514016042c04c0c6030500003131101c1da105e0951103134034540035000c0c0ca201d40c0601801d01144818015031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 616185944 1250 616184694 616184713
    0x240e01090207050d0f0203070f0b01060806030f030f0d090b010311180118021c050c0406020f0705061b1507030911030a0f0b0a1103091b150a0507110d0b0601030e 71
    0xd84d01c1d00c08036161001e00c5180080800f01034800c1054900300303500240448003460850070006000e2400380900f034002038084001900b2401c0001b1001da800344000011803400d60844064541034000d440d0000312540c4802055010400ba402d995005c3e500801c509020340d03484108101562844419140a84100300010007230310080d06180c145440240c0e07009603880391014541c03802d1154040c8881c420a1800d428096104a4030028005a807803e400b00c40c880726031081030342d84c3c1c3c051034800d455001c00708106001410300d24011030521011740004480c9003c0b8841d0501450000484512000030f07940d144840a005601c8000c050740b02c410b902504900700d45488081030aaa500c401400b008401c0010030069500ca034044138141500c1c6000580700d00f0404141521004848a007071011003103802034100da440c0c806540038201c042c20075694034182d0f51000a071840c0e00321340c505030b86041c081c01a521079500c400e0440b0401c0c0d0705c241003521007480d0020025040728503404485119501c414200c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 616187050 1106 616185944 616185953
    0x1171006030b12190615090e0d2609030d06030b090c0f0d0b0c16060e070801020301060c060908190f0e100f080604240e01090207 57
    0x80c418950598104641103408540d40e20040d0071200038502c4c00569046401c030020304c90381010401c0c1800011380310214105602c0040480d850301c00c030364080030f001d1050a1590420f030414003041050103142060042001c48444070b080d00c00c2020032070a080410544032400881c0b2828010a9228a08485a2042900d03504103134440e8a0842d0344515115854240003c80503084a81c1103007280c540d0b4901d1003029140c00305100f020441e10340b10440f43c8000c3c02545028010216152075000a9140f0b400103650145200f81d105000501c9655840746c002003c190b000301000c100b1241c0d0741000c9201e44584030380e400c1500782c5005d0841c0321039001080c510f0400203e440c0d80701c504a401090028005100b00c0c414002040600e2000c034040c02241705541000c40a440095030000e183d91a04403103084008046040100f080c003040381c01b540149a03409400c4502c410b6051500c2e6070758 = true := by decide +kernel

theorem cover : BRFrame.Cov 616007194 616187050 := by
  have h0 := BRFrame.cov_init 616007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 616007194 ≤ n) (h2 : n < 616187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
