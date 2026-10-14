-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3287
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:13:13.176143+00:00
-- url     : https://prove2.me/submissions/bd3c7bfa-d29c-42df-a466-640453c752d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 591007194 ≤ n < 591187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 591008444 1250 591007194 591007229
    0x1020a0306060f0c122604060b030d0203121617310c0504020c0a02030d0f02010b0405091c020708030a0c0507060c032a2004050c031e06030c060a0504 66
    0x10941c13516101030381011074040f049a102c8812a03c0030706824081517204502081080414540c07000c2c544242c0c01040005980c40150381018100b200d401c0d5103600310351003071164000c00c400c0b000c01035800144c4010600c0180103401403c1c0c404d15403801101210944210402c4924104019041c3c2424114100301418a81c40c404805543e5640c4001429040004400b40580c0c14a43c0c0144034001c1914102d51442d511030340001d02d01410380c1e4001000404072a0903e0b0401c0e024000d0310034039a800c403001e02491600d09003040c0c0e01c4414854600f40780c0c6002052859003070007800319001400c2d0510035a43e40d0844581c0161000d00d42c00701c00c60f458800c04200142142c07180007100d0b00b86d40c0c16502c00e06104401c10b40b2640070003d200d690300c094a24501d11800140707100c1c03040182c0d190264260100500400d04200455100400e4828101810000c00c17041c41d444980d07a0b25410b44c5600720300780e29210075020a01c2c0068421005400010024060202d99084000b5100315110900c1100038a030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 591009694 1250 591008444 591008447
    0x102060108070609140a03050a121403061518041b121104051504080604111905060306060d06030f0503030103170403031b050102070b011e09140114010c0501020a0306060f 75
    0x2c8035101e80000207403401e1051141303180110f0002e40c0c000006281502c1c050b225242c95051012002c41107404003c10200684015003010034804154511360780103003145018804242114413000c1030300746100c0d00041c55407000404141071194400c0240041100b50710400304000902001c2d04803201040c00c544030031001744500d000360b800309034040030500c2c00c01b031401c014400701e400c2c60f050190b0620000e0101041c01101005003070b2040e8061069942c110034210b083c06140c4014840c04484d03000042c405000030380321402125000304003a109540d07503800d4000400010200341d0002881c65428140480c18000000701130360680c0e0150b0f13841d988070480410500054807a034880200460107610a6140400074900480b40d42c80c00f60001500d081c01a540b441d105142c00d8000c480013494a20b9400a041501000100030b4052200e08104c2d400004610b0041c1c007a0500c5220011000b07a0804045a4442c4007909d500d07661040080d07488420f042400303405440d480c0502c0c00010b0040c0d00149005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 591010944 1250 591009694 591009703
    0x20105091201330312110f0d0906090e090606060309071d180708060106081009090501060e0114130b18040308070e1005031801020408070605030a0f15060c020d0b0103110102060108 79
    0x3240c1c042102c1d09066072178641510b4032210030f608410300e0b0080601310f440604040c041d2400400199440001c100c0c10150f01502d1032044d0f402c03081441c1011420440003074000140990000380440d0200d0302d90b507030312800c0740c6014103036048489110821881c055071004008055030043e22800a07028041400a03040e41da600061700c180314179031b400070004111035802004015007108016407030110380c548406a03501624070140040707403188e5403032600f001225a4014618050591255498503c1a41400040c01500161030000c07015546442e40b82181c1d4a200b000400b050f64102070261901c1c0074140580a540d0440704c803c003107680942803c5e01032428280c03100b120003103a2140741c215100c01078002c3c5102c060b0f141c00380e66036600f0000403401030303c1046028010300c01c035500c040d62450051507400039284800c003c0c0d100f9a003816215013940c400e41078420180c8a070b13860305240c00000360001030785240c2c8880c0c3c00f408400c0d40200104c140402d904005600345401e8080310030990b60784864540e90b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 591012194 1250 591010944 591010949
    0x61e0f150516150c020309090f0c1b031e0c0f010b180a0b121b030c0303090112090b041a2520010c0302121003020102070302010509120133 61
    0x14020041c05441d80e002c0340892446a0080304a820401420a804021140a510000003591020038141c81c1450b0105c10035034841d910600f00401400e210781050018011482141c003540d24005402150190800035602a5005008110403c6000e404000e0190344402040c1260303000d4085802101c0c1414002d42d124640003420442e1040481c0c0ca030420ba00c40080d010303500b03541d2106440e45c041c0c0c1e070718000004004c0070319000c1c11060080b2880e01705c610303041030031035402500000c905480a0791b010068900725402801c054188032150191070b802040e911300d0003807440080d00148014008007103e41c59032030100d4400700c0c0c501d48a84204480191001c207003950f800340040d15039440f45104c5c1d15000101c0ea10440340f11a4850740d00219070a40e06d180900c800002d0380416224200c00c04058043c2d00301039000500302c5d9240c20340c1c0000f500e0b0003840c00041d0503c01c00040095894640200c03c00001c2001e00c020000029100c00703100f248101c4d08054014403160424600590401d11041d0f001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 591013444 1250 591012194 591012197
    0x9230402130902120a050c01020d0c020f1018120b0f0f0402042f130506040f06030507090312020d030b0f091302011b060504120903110103090501061e0f15 68
    0x680750745820082000d0b1012050490300081301c08105494000200400c125080c42000a0000600348900091074114009414000c002003166008090b8440072020407110340705441550980804410070f031040502900401452160304a0006d811080d003189030300301c980f0855030800c090312600502403042c1c40c181c03821440088031101260040c5030903405200c000903003404607044c1c070b2000e00906220700b9000035400c0d82c5100008003010b240740e22039019000f03080116801d0781001d09003401d14039640054080d800038113030f44401080c400d5008210401c0150f07405a14103103034881e60f0100945030307490440d4000119040c0140002c06281c140d0840306548005030030100c107642c50f144c0c0305181a07802c40701070f8140035200038071001c2d0100d080e4011080074001c050108050410789021444000c80603004000c010001d90180300103121140303015591035003480d011079142c0b6942042401480035520100e4400790181c50b404517012070701c0b000000c9603201c0680d0790069640e40110f80060100128210 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 591014694 1250 591013444 591013459
    0x901150e06040f1116060b03030a1218140a150e0a0314070c080304180216110a320307030314160c030b0103050d0e1e03030c0709230402 60
    0xc10078202580009645000f41c18045080c0001661461481d4070219a500c1c6090365a1100742c103002d0302d1b018a05580d0310030b90007140381c0281200c0080451142e40c0d100c285c565165030784e80b00607202040321800c99642000b07925043e2010420032940e905814074048884880c030555941260106204000c80d42d0804400380c811410a9501140c081e042e03003581100c00c100510288001c41c0802210101822051005540e40e904104032454a800c02540301004140100040c00c455031800080c4540c0382d034800c84034841c40a941c00082c61a00041c4c100091140a0603160704040e01d0305021003981c1c0d007920320150500031052040c140c07500214040900400c41002101c903603010030381d000300041c1104003484484682e1903622040d00c407029600c2030302c010719100e0051040c071106100008580c8014146110711610710400324500102100114101160103403c1c01c0b240e8030700340221407221440300305580d10a034031411454001c05840d00d1010804c07004051540c0400200c0c090b1030f00444c1c00504a5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 591015944 1250 591014694 591014701
    0x109060309051f091406060a030204052d060117010b0f0c1213030303050a02130605031506040806010e07022b0306081006030b09070b090f1c030203030901150e 70
    0x2603025000e015000c584510501c07001071820509100c9800c0c001c0401c05020070103d0103414002e1140c005e02e003820b1200d4211100b03008072503840c06103420460f9030694004c5800d644074120b440c68003640b101d00704005041c0410b04212500c1110001c0d10501098a9460222110b04682080e0090900548140c92000c01141d0214003070900542030180c0351504565400d400718001e500f054003d41340f50441e004c0c0010090080503003502900394850602c0c2411030030b007801c50f4000e41891403135108810901c940040440d0b0302c040010000300c403940018041554a5980c0c1e00701360b0780c40100b4411803110382110f40205034080d102140001100783c00190601080d05400406462400c491150340b00381aa28000080c0d040e009001c400425010a600081c00600e581000c6440e0f14004000d100b158000c0e800601c051101182501c80103170080da17648400b12101070203d03c0302102582003156041850055004241c0c0c000001c501ca4040e00c002070214a8100c1502c15a085240c09440100007080001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 591017194 1250 591015944 591015947
    0x304061b030b0f0f0f030f1f0209010c030810091a0a06020309031c0c020d060e0d140409050c041a041502061018150611070f08031c0e060a050f1302010906 68
    0x4110002c500400e00400075105ca000a46810810f042c05001c581020004848111a42607021040c1c10720410a501d0074040e030b0002401c50100d02d40040c28000440081004040c1790140000601303c0404c00f0400b41290350100304070513000c100a0346c82680103440100c1c80030300c080f00396682140060024103020325190410761404555084400030003413a05280c03005a96480130034038290340141d0f0005603808102000d5400c0030543d408030300602001080e04501000428101c9040380c0840b000003d8640f00d044100c801c03803156610205203035001070030700d1070903a0301200104202c41c03180c101b00c17141c499102016621384070700b26103c4014071140c01c0200318401c040c550080034600030000008026005400c810924451078020f40c00094201d0101002d4410800c01d61f80038103848030b0600902c03444d090032540d4134800c40b00e0003c18002d8149288201240540208186074600c009403080380c074100c51507e00801080300c400c4168000100803c2c207182c084500c500c0e0142d0180c0d5002c20b1030341000e80 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 591018444 1250 591017194 591017209
    0x6080c06041512020d14060a0f141f08011e05060d0b040b040c020f0c04150b0703020f0a08120606090d08130f031a160206011e09020304061b030b0f 65
    0x4004040c0000b8002c02d0400040c3c0e840200b0118805500020f910204900524010080108002e02400f80808140700014005090340e04131035208211420800302080410500f400d0710300c00002c2002052004892b0941000f401c42c1681d60201126084460401c00c0000c0385000b8400c40350400790401104043c0d80b0260040c0c0c0c0c41c0c440250022032092148008a000c076080d000504005070040001c002000c0303800d100d0b030014940211401d004401c44100c250b41c448103607106003c5000710000c3c2c031104150085c402054442d20f01c405942d100c40a0b400c00b1400d607131004507505035004841c800039100e0300c2c01c401a03904010300a0104c3c82c0780c620310790341c8000c0c60340204000240708040443c00244030f414501f03000040c503c02c00608a140c40300158611080d0000b41038201c08070505150785028690006e0014110317a150042c880c0c101d603001980903140380c959000040d00d540000200700c180851a003141d0005820000c024415030310800c000c40440303120035081913200c0200815005503107085030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 591019694 1250 591018444 591018479
    0x40303020d081308030606040302180402040c02010c021c1403070302030702100606170402010e1215090c1e01090b03090c0f01080601020a0609050115080d02010b010806011403041103010f09050106080c0604 90
    0x4050a1900e82c0b00c0e0001420030100c490000d86001c40c80c0103300c1142007174051228001100d000922484581c040c0294990641443d25043c015400c01c07002c150912502d140101c24221a9480b0303079a05080e000103000c2e5208540f04c3d00540720308480d8a008194a201d06400c98106030b0302c441207036001860001c00e14070064826410041c03c100031011564480300e00070645880f41c030051540700c0c1112821000c0740c02c02040038103140c0041285103400d840300403802182c0140d5520002a0b03440000c0180c2d031030700c1e00d5000516161400b00030030149100000708070055003011240601c04413000c10044403101030894480703006030400000c070400207020341c100e049814491400072860311040f030000c0d5110241030b4420000d40d40264420034249030203100c1c00031000c04c01e18002003e0715120001030010f00d10742a0082c03040900000060a0108901c0b5880000d20000e000b44a094551040c81016010392030342902e26500e80200080c60f0400010046507080c00908810f040520742040c502200e140c09 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 591020944 1250 591019694 591019699
    0x30b0703020c0f0f1f0605100c080c0114093009030102040305030310180213210c082109030606211f0b010f1403130b0c040303020d0813080306 63
    0xf10a1a4405802801007203003414408000340220421504d4812442244078208074a66292001c01e001c0c1e92a07400520200407120b0400c0b280004103440c04d211030784208030140f00c25500e081c0325041402a070b00c200a0041003040102c40620242011400e58104400b800115180f443c0b032209141c902c01c00c0c090640d03000020001414141d8030b1316024210f0384100c60b5200902528103044c0400700510714240e48000003120218240794003441212200760440c020b410120001e05035488501d1404c102c4880c1035940100341425442e5100150747d61a00407100301582845000f4028460300045c8090700c0010034014001c00144d20395000b40020300c403110b0715040c106424118103591110080041300401515100c1103181080c440c50f2071030807540c00840007410420b6560703c0784c011035803040701c0d88000b0010001071a941d440b503c5441001156075500106000556010058401081d1010b80100d1740280c081d141950400034048071120001c44291443c0300801482102064444000d141d001802 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 591022194 1250 591020944 591020953
    0xf0b060a0e100c0803010e0108160f03061116120e011805060c0a0b0f100902090108071d030f010f1401080703030c0302031201180b04200d0605060c0d0305070504030b0703020c 77
    0x1544ca5406866209030090000800c1c2c7c240100300c030174010065402c120b103205000000301c0341010703c0c555041e1220301c4050f260707645407845d41034080780040898070309014811100440740080d161810a82d0358400c500c80218000041110740b95004007282d20301c00c00c0e9988840001420441040000d0300001440403d91154050303007000030f45c400c510540114958210301001e450300d10018103101c0100e4012841d458014808030035079981180003150080114140721f0300c1e42240b10002c18201040c850119498441c2d4590b0300100c100650100c103142003c3c2c1c10130712803550b2001e882e4031000700a01c40c51115a01c042c4080001c64441e14004591a11074415680740c0615440b030f00c09030341e0003030300f0a0807a03500d480c45c0c04540102c0b501c41e040b814401a6000e024403011443d651320b02c0109009840c2400348000f8000010070256400300000d410000c000e41d48800002a08aaa0b40303400c10791500440d2805012941d0a03000b80d080e50122030740309003212100c0d640e07250201c2c069040021204400d124 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 591023444 1250 591022194 591022217
    0x18060616060f020301031a09121602010c0503030a020d0b12210c01062d080319050403230d0903081b161811090a0605070f080c010f0b060a0e10 63
    0x20329000a45c0210b02540b224084181d04504142c9040c50141409080b0b9000300d4003015512078000039a0f10b1b03040d00145001010401e4001a524800c2c2900010308038000002000b0600d10b8550191003d000e200c0400c210544d1000b042c1300c85c6102101c801d520742c2d40522078040e510000d029120361402c00c4113403000d05041007a200395007520040c1d000311465040034010701c1c240035020903030001a0600b520000b0885403400f500107889204080303210111002c1400b1500f0454002c0d0b04607401903034040310383e0300c0c10245280e183d5881040000d5100c0c00340941c040042d031403446080c0700c005894105001e5450708000000042c0c1c40a0040841c1c256405052215040e500000120200030140544039050071000c1840080c200e40b52904003900c139210502140c00c0070745480c1400d106a07206400d01507500e9445061000601d4010711004169140004050010712010b40049101210030a4244501d100000070001e503401040500790020320b5003d48900e480ca040203070340c2003950b124104000b035242d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 591024694 1250 591023444 591023471
    0x40902090a0906261b270c180111061302040b0402030a1410060207050d1412040906090507080609420603010506042310020c1806061606 60
    0x30700c00d81c0600b4014501c2e9228402104c40f1308483e10034070071000042d19142001c2c0c0c010b00c40c05110504110b0140764003c00584201c171007864030001402065034004c03a54036241e59441c803184c0c80001980d0310040803000c0c0c00400d50040401480d800d080d2000340c03c90366a42c0303082c2410f0030314011003660701580786c07030b101030103070722a440118080d400100c804103860080500c00046080f0103449000203591340003080004560118a040907a00102c0d004640300407a41082c00c5019001426100c06008071500f108142d09104002e20464050340001c2c0081541d070380311601211403c584480219070b1500000d10b51303240c46404560710000b2484888210b885001000919080500c075106220b00c802040504a88111040c0d9501c048111900c41c135643c1003202049403030280f845171b02c0002045c04a848949206036416960743c41c4040c0c2170108516003618000d640e100b440b0040c90040303034802040c658002107080013031b100340d4006c1c10561421400840c5100200418041070703601030766407003400d903544 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 591025944 1250 591024694 591024701
    0xe01060b0a03050f0903031603090804030b16080903031303110f070f030209010807060e060c0c060f041d06010f050702060d0906060806010603020c0a020f06090a081b060f040902090a09 81
    0x4001a5000034035442c0c0860700c4900c075613010348480701c20791050040043c0844488000e450703600f40c0b860045a05c00c0f151900156600558000601261240e003c0150307110b84504003600210036503031101200d40b90000c2c078940740d102c203482c001032580c2c1d10000c0ca00440e008100030801e01000c3c00841c0c481d0204854280d0030908150401c80e00525100410019032406600080c0540200800782810510300035000c1c2244402a0502e4001c0d403000c01c1e003890400c418001e1005021020700b00c0b95503020102d41c0b0102d5540503004080c4e03041d0341d803240342400314260030a09125200613110f43c504100c0c901000d0311107404c000e900301d81c8440e0403c803101c942c0300540602c8001c00e10550b4003060f01420706010b981442c40c1600302008040c41030200c070781043c000080022407603030142c0e450851a950b14010800900c40c00192a800480d1900d0000b880040007401e200070112003030b640203818440c4010000c4a201e94040d0780c10000050009100c81d0016600078143c48000505c2c00c08115030320310030002038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 591027194 1250 591025944 591025957
    0x317070201020d110f1209070b0c150a0515060d060512070905060d0b040f0201270f080d120c0309050f0303100504020c06040b04050f01060314120a120e01060b 70
    0x107075000309804203556400e001380c501c102c038004040e43c1803030038001100c503060142181e000c4400580b0f0011070302c0c1030003d21115001e824031070301d0b180d650b0039410b41d0159242c8405071420121204100015112256403242d58011501c10b6071298070440048100300c16908407414010f40d859880c000019981d80c0d959004e03c3c404400400342101510742040e41c0c08507440102068000c100380d0403c14002080044101e0788503912501c1c840800046000485402c1102803c40c5406690b4140202000e41d00741c4c4104115440c40c541d5101c066102c211032078481d0744950030b07040403902010214007d002281c0016841401d24a40003940140d56220b10b89005184618020746030000024800101c0c0102c2218016180a0301c0551512907420038865507048000e00251101020364046030402c07800f40708405800001ea002807140940302d08045e1a1056141107070034071813184203481c940f0b43c65803000361a0008031fa5103c00c0c0484405108c494094684540045c0300c555a5403c08114111a613010300300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 591028444 1250 591027194 591027197
    0x315120d021f060503060109020d060302040204060c02030607021207140a12082a0904200c07090614210a02131b02120f2b0b01270b07031707 62
    0x1e03891401008504184050b100c07450741c1010020700c415100014828110740c5000703801a5600100c080c414004c10540c2c000070b40c86800003c00117003c076132042e08120000d00880c1502c0d525150b5490903030b542c40400304070030500102440040007283e40c403100e10f170070b103155141520091052940c411451501c40711000021902100c00d0003030b41c450a614408403420003500c40285294000e40038600c1e070089039500d6210f10f4a51850002480070320a031002e40344140c2400d1038640032100c40c02600c8039040d000b1034214501e0200c0000310f0615960300e83c0f0741001c0140113200b001c10381226291513001d241800440a100341d003422070040e00e0314000d002c1c00e841c0360b140018080c40c0c2c0c03600c0f5500a581840d4407d0455014981c680030b007654800440e00034114501c4c102c0d40e0394040c91400f903414400600030010b6440300d00d4208202e1609904455003e1000366240c0c4246c00382e1b0403c980d0303100842c40801440241141051203201e041c100186000b0340242802002820241e6040503101d004880850 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 591029694 1250 591028444 591028453
    0x303050705070e01060c0b1e0106020c1201090f0602071e080415020a03021c0e0d060b09010b03090c130212130b01121a070e030a060207260315120d02 66
    0x340401401403801410fa0b07070034455a254901080100b181c981010701800c8100e41c400410600003080c007011054a10407400c1c84520b603520b10020303485500b501040b40c040c0721400b9101d00250310610441c0940e0354000401c00121a441c0c17610f500079000400e0841e0380b14081d0490404010042400e180480c0c4592916591a81440d0280c81d45500e07000520040d54018509000000e40210311804c0c001c2c0030020300b0420401700c1204603408541049140d40201001c0710080502c95250030142400f80149c840035096603a42000300704500c0121945081500926141c064524241e11a01d16600002402604064584207120913004c82541c031008502d0307001e8045820460400c54143c010688280b034811482401d48030038a071a110100105541032081c0005664680158001c02d40910080c080315091006454140d0003540300d9941a901035800c41e08400c1d901e52044005400d140b00c6182c06401c4d5210155003440c5510f0111000e980500c0c4009a504040810001003202a207c1da0050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 591030944 1250 591029694 591029707
    0x307170d030603050307060903031107050304080d050304030203040e101d090d0323271b1504030f0f05010507051b030301030f0210021c0306080f01151206020d06030305 74
    0x2a49031042485040d8240350914200300045071000c001d6868864220700c1c00702e1500a02e207011030003009880021a008003000c10b81200f0b1050010262050784c242d2000c69403140c41420b01030b0303210701040700c00800503402040207200f641004070007150481c0300748a121301c1e0103494100c0c4196986103c230842502d040c486003002001d400410612000030601e00b010808427a55000d4204d414112a1010400482990109003002a41c0500030841500d01212015512403585c1082c1c0b500d145001c0075100350404040c41607580303040c5040c10208000e54403a185441e146a4440c00420f100700d00c00d4896405022a400203c0e10078000c4912541c0240d4070103584810b151300131803001d0001c29030890540d20074001400014075906191440301e404440072950100c4240d803c904d0001903426040d40240074003160340d08240c060700803100740c0da50300090f264040f4920038110708071162583e0901624444000400018078030304180481c0358040d100c090315000300516104143c44c141d80c8200c0002d000041d04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 591032194 1250 591030944 591030989
    0x9070507110d03261014030c0306151207060c03082a0301090c030b0d060b03100c180602011a040e190f020405011508061003020d0e070510020102040f03110f0307 71
    0x1c000c0102d58481e000c0c0c07074170300707162030642d0300010b80f805054566a0719042000080e42e0421044c01d045c00014112496480c12034408041440c44040d464000e03500f80001c82c0344200c01180150603035149580e56203110781d1b182c404403200d0102a1003e4580c00800b81c115050070100b03c801920700703021049055481d49031260b480200d030700310b0300d01d001018a0400035071059911701c503400c481c540c0c2013503000c03d4030090040040e00380300000d4468100980343ca0164049650050941090340307001700424611a580c40e4000e82c262188000b1000c0c8641110071920384c680345c44d5010407610300e110001c0781c6403850042400c020f005015582940d003500b10a000c2811071503c0d0007000c1c0901607280c08231114803101240034000e1b0398060b044a2280140c01c00108031a8484d505803404550454820300c04c1e0049940300c41d071034440d5400b400780220441ca20a800c42c03030050003120103d43c004c107182071000e803468075019410341c40c00b41001c0d0b10541240d04801555020400c10020b041c040c61419440502c0d003a1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 591033444 1250 591032194 591032237
    0x9090a0b0a0e030405040e070f081501050909030703031a03030a03050a0c020a0302030d320702060603010b030c0d021207060816021c1b120c020f040b09070507110d03 73
    0x140c814002d0810b40c1c03058000c00080151012034000382c4000ca82c54a6060382c460900d0b645030003101d05a03507003480c001001400000d40200501d0710090781078003640c0300e2061042603074048400910641c410003203140000d1099108140d0050711140a0b81401070750300c0080c3c2503500c210030090000351a6420b10101021ba81b040c1d6108044600042a03440a940c0d0080d4407400743e8269481d0725681e0310441386498480c0c0d0304074002c120a0b03104006c00d071305800c4001100d000d02070307404500501c00c041c0081c456040510984d200a40d00a009102c02402e0ba000c002c0702d407003102c1c005c81c0c00607050040d030f40c5088010010207025010540304c3c0320f03943c64170f030b245400cad82114605030004541c1b02155160070000c00412409003e42d10345400082480c8001810382e980301c0c1c04100519140f502d420005d80281e0241920110360310807100079907245924020230050340c0c1c40400c8554420140301c003085ca818054001403103030700e1252005046104000c0002440025018003e8010404440c01a103180700650b1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 591034694 1250 591033444 591033451
    0xa02120a0917060f01030813050d03120f150b0d09020402030a0605150304030e090705071b0515030c030f09210a032703030f021c060e180d08040c0509090a0b 69
    0x42c0104820301d80840203c4400006220181010000164511031544000a1580544409010b1035440c04140c60000e048555202240e079100740762625600d21007103107004600c40c0c40042002d14031814184500719103907503c0800c40552140d92080c0c07042c01621180082d6100e0b0042a40000e0410300d0081803007e0f240c0c142500c17440e100820010400001e400282486a1040584054405944010b0b0548241c0714002c00500702a030400781c20800035040145250644405880701e5000e0f9024407041c3e24140410f941d650598801840060501500070300b0040d8440d00340c400f2148100d4465140c0b10640d2000d00e88151410710009044850030b4050290711580c10b844a501d4100c2800c00d4103054442d4901d41e0020105600d6a013a400d42d4423958040d900400161400c210400a00000c400003c041e103101e004103400030500098040042e4030700740c1808001c0d1802801c4c04848065045402c50002002190dd1015502003c03519403180300c1058811901480242104c0000e42003a40c02580e00a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 591035944 1250 591034694 591034739
    0x1101091a040c120b01060c030c05031306020c04060308040905060f090a0506011806020d080910020d05010302040e07032004020d020304140f01060f031b050402160b0c09150a02120a09 80
    0x90110340003944e8001c5880c11030300c00746442284000340d440c0445440c8031501003d48644004291090030384c1526044800b00ca805400b110710395540181404162070036488003030040b010038442005980069004154044001081c0c2a07100108100256000c40280d50013080340e5175520810920303503046403c500198480c6260b024109141081c0255101500050f841c02c228601c8007046140c0020843c1c01c060044104023551500c006101e8540180000d01c03040c3c0c421814120400c002e84400f05071b140a03240c000e0000b090301c2614520300204110030410064000340d00300600e07040170110344090f5001e02c1c4a6170308001d0b006000211180341050320030301c41d24503916041c000c012102400c20b8641c1100e0748000751190381c41c3d003d09082c01443c05035201c5a00700c0d000240c0c964145026039071610000d4465000200d15469040c80c0e40898010b40348060742001c1c082d984960032034040000f4003035030725107071045800e0152108480710494028152038404503c01d036000f4441c54940001b0070440c001d48 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 591037194 1250 591035944 591035969
    0x80106080a0b06090d150e010c0219080a0503130b16031b08070e061b0a02030d031401061209020301060639020103020714060910060e10061101091a040c 67
    0x41c2030004243d40715039000c0c0381c812000044840e08102030075a54808440d140d005c10003e00c901c0701010390191488841e43d00050003450300800c1c1d400048031103085060b030400b040f1420300820b19810382d900c3d4005404c1a6910507071740b80000018034055040b51041c1c0e540c1a01c280c6004e50f0210240607100240c09a000c0080c41152009425500001c03040c0c2c814035070316004c0350100c0c0d04408680307a0b100f211800000707040c03941a07011340100005902840b89200340c1c1150004c03441100b04404807040c2e01c2440d844d06005100411036a80309000182d41e000c2440b1002900c86c000c4d500080c2190803586c0408085041c40c010908495800000e0140d03160200200c0c83c05004080403420b19450070620083c1850360110b940d0003840b00010b00d03503407c445a14210f40190800002c002d83e510786150030600706900300a00841c0b0302032004210b502684c1d0b0040102c081034206003007920740141040b024503580d940c55241c0000b054000489005080d22209203050700e041c01d08044604c040950064000c00f02d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 591038444 1250 591037194 591037211
    0x5101a130c022a060d200403050c06030a0e011803030609020903030d15180e010f0603030816050f0f0c0613231218120c0a060e04020910080106080a 65
    0x40100d00c0c001c001140307148090000600450740d11040c09000030f2a81c00010104211030005134603031000c07040b40b1442c50310407405a80920041c1552040b40801811500b11a0440405040010107181c001402c08404110750300c0c80c40d101d60841d2503919524090701c1c001c0000e2424950148600c102404502d4015881d111301c1c1d030042566441000717550312040b41c0c1c42c014241c2d85002d0040d410042c01e050707204a000d9001c141c243c440544828000721300994a4051202d0020050b44940c01c21641d041d15011543d940b5281020009030415440700d051140411025524815541c014600c03201d00c0141c05841e0000315061503d801c5000f07010f04047d146150b415004211246020080c500b070419507042070114405401c4c3c182451415a103982e8140810140c00800364041c08e24008a01543d1071050700c0c50450509541d11503031894550403070700014050040a00c96506118444400703807015285c407032142c000c144407412080781c2c280002d00c10001801029802520f0175040350300c041c000c0c041d944 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 591039694 1250 591038444 591038447
    0x50f1918080705060337050114090406020c1e070f170a0f0510050a0e010b010e100e030109020a09050106020f0109020a150201090c08060711061603050405101a130c 72
    0x65540c001d0612030040070002441e9000c14448021090508908582006046d0700e02002e548a152600b0550941040004a500800300e01e0f68441c10300d00400810704c40d180c03030701c40718005c0d0701c5459591100c0c00b81582c40403080c0c02100880d80015580c4000300009454491045840492a000050f40780044802424501000610034190541101409a0381c5d60300b0700d0003030700d400142c042480301103060004000d05001203a2003014446d12040003802001c070400011900c400d04924080c1d413281c505464400424813403807a01e1441c05007d0000102c5a1841d0001200321b00386034815401c4c262240018403489074144040d070502c2074090024000004190b002552209440c01411924540c81c1c1103500428403d400000d11a908080980e0310591112380082d00c03620210f640350041a034102c4c80121409000511503c51049a07055103000d032540c0b14210081d2902500a071254030400303e410070502c49610890030328424005400003c8240102840340c407134102c00b0444038091410213224444d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 591040944 1250 591039694 591039703
    0xe031206101110050712090308010e0c040504091101020c0a0b091311160203060c040f030f050c10090e010b160b0702010e03070c1a1e030403050f191808 67
    0x103084609411031a1a04030468a20030554002041e512a6004010601c0c103d5800700d80615160b82d560790318201030743d201c20242c40c1410300080000f0900001001052044407240d50002e07444000f07a4a016510000241135464000042d40c41d501c0c0c82c80a58031a41c0c0400803844001d0082e100c0501041ca003403a6404103000399240980654120204081c0310070140d0310003840b0242820720036803101441c10b44060302085a4008174040d03c11100802c0c140f103000800e41e8100c0e02a000f40410b054115500e00407c41e0002c141101c1c24441d1000b00042651800c40c21f040d0f0031816958486900e02c0d19010b10b81c6280107070300440d0248010410007003800c1044d48040c10140e004503000700941c40b6290304900521020382480300901000c80c98004021402c103a140132100314030350700a07156980c403002490078030540c0c002031102d10200e42d00150342c00d1b518000e5580729029080c0182460b5041c810b184141c0d21003005001e651054082c046849500040301400761900700340118812420641c09d1a505c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 591042194 1250 591040944 591040951
    0x5090703090c0306110706060b04140d0618080d050a09032c131d0f03071e0213050624040504091b080606030f030708030c07290a0e0312 60
    0x415445001801c00e100703060410000030360344810208501a20002c2000310340c0c000d0801118aa41409000205144001c09072401ea030060109002400200000c0003000300003010101c3d24952191500e448182c1c800e1060300c40390340100d24096942c084600b00d04200c403c01007042407041d2401c0300e0000881e610002000c404410480910300390b05c1c0500c04540785c991111800c1e0f0f444070350016075150b0020250031040c901c0c03050079000d43d100040c01003001e840b1490900a1240d41d07000f408004d0105020100d52050001e814100d0445031010750085a00049112680e805442c0c540b010b01c041418050344885a020328000340d0004810b4909140b00a4880d52290a2080391151058002e002d860581c00074100c0c6a80c02c08030442c3e0381d03118030b1038450300f0484600d4445e000b170441032270a201011040700d0400703030302c00310b2030346141d882c0000403d281c1c10024054803400e800074a030a00308242403e107540616100c2c10010002c0c82c00764000c00c160b4080e9000d0443c0c642042c080502d00e01080040c40382c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 591043444 1250 591042194 591042197
    0xb04030c09090f06020c010f0f0209010e011b0b0c0c010e0a02090f0415022b090506060306090a0308180a060504050105060118032618030c1806010f12020f090f0901050907 75
    0x2071b10025040700c5130151460507002c2c1c644034609120001204459801021000c1c02078984446070501e150040d11145001401c02030b1041c18810b85200240740c41640a0340310818a10190600c44007041d441c1c00c6440729400d1a860f0383c4420f4240c4150320f0482102079100d100340c44c0e00522840c0940d1442500b0702a107500242651300440c04824200b4210712924030a1740c4804c1181c4505442e1100e417000d040f000c481905c0d130b405400e0120b5128180490300a102d44010f000901007113007117a038111a22040103001c060210004407903d480520305204961002d0b000390400b00d100e0403d41802421204050103503810310130096648545000340701d690400f2079070800c20543c40245440c1d02400c021284003500801c0c40d00c001160000c0c84800a0700c40c801031403c0c4c0c22520040c00c1c07001400030300001200515552582480016110742c4240c1c00c82052596610f06403000c0d040d5581c880042e40c00625083c040e9a6005ca040b0095007030001c0340042500341268005819490803000c02c80c1000701405420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 591044694 1250 591043444 591043447
    0x5030d1a101d0d0b24010c03050d11031f0e010f0501030f09080c0f060601020303060913050a050304091a030d08131703070c1203090b060105090301150b04030c09090f0602 75
    0x1034600e66180031244550002800c0c2c412143e03154a000121050300322000115400704a01c1c0d061010109032407030111030410b8489401400f1651400d84040e0020101d2403051a107d1070002511a0441c01650091410701e0020701103160038641c200303212049070004550080d04100401004e905d596560b000c40b1800e0030006080040c041c00480544001640508400d80010b02e5104055000a1400e542041001900c0b81a00c1d1a0012a00e910041d07610343c3c0c0c840165030201e810490144004803100340708030102c6906c1c032541d544441c1140c1103944003808141e40c88405400b1110055480e800b000003c6002c6c181001d8004c0c1d01410707540b8060018000c580107280751038204101e00e01c0607080880d001c2c600a49074a0089401440f4a4040030112404c2c90034030310180c0b01502a005816031154064140c1c9102d031b403010011202504411841130b807540d00c0d04011300c0031b000d25190003030107003d10300c203ea0350719420350600c110099025031001604d18545041e24021481056403a000c0980c40100503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 591045944 1250 591044694 591044717
    0x9020c031b0f06090a020a0b0a1b1506050a050303030106050a0203040305031c0f020909010b0c010f05090c0108060303030f0604182a09090507050d05010e0a05030d1a10 74
    0x600e107000d05200e2510344241c85181c4191903400103a5402c0010000d8100c800540d1081040340d16141030b440c1c020741240c201c900501010700030b10050203501c1541d28024051481c2800c0070720011200d61026030340d0302c00d52040000c0000321801940c0181100340e0304030508600d05000b09942c2d02c41442020108580850800d00c01442030040314002c1da003100440e40c4441d410200d074110388011103c0d00190038030780000500750080c90b000b510b000d410000d142ca0840d84c0b0300a084500340c3e010450303501b15175613108000302c90b94955100e01401000c0348002020741c2500b00001510f640009480c0503c268000d00070803080c850301e09082c0b54020010303030b0040344a540c6e4850460300585200c0005001a0703d1106004070807202121165030388600000c20a4019a528603200407038508080c094455005039406002a0030320901c0c12141512510000522084d03003090f59080c00f420901c1290b65400c00507403400804c01c20300910b80303030816012a081c1e41b034440c0070009101c5100301c0901d009100060041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 591047194 1250 591045944 591045967
    0x1b0e181c020a08070614010614070b22050a05060609040c03110f090403030f050606041508040f020402070c15020105070801060c0f170a03241701020409060b2a0303010902 75
    0x56042d400f42c5100e80310300c07280c5401ca01405040e00c0900c4c02d61480760000515034424403941d800c0f4510f00728214a0094035449010b121076009084420038400343c081d0150510303c0b000384443c542c2c05040030346045280392601d00c0c1000c0001e031203a0302c900756000500000c112080d09090440364032880008004160078045801d034900090702d50351002c00041040705268142c2c00500d48181c0c0b800080200ba0b03a6042009580d000d140112490003808291481d07150380a00036440c1c115006a1480b11000d40581c0014240c0e40081011a1152065241081a640c002101d0035055000340024800b51502000c0101942014400e203003c100f0802d05d40020b0100c1d2000a40100e81c00c070a200b4504d408204405500303501000c580700000346468a0400201080c1d041c62441c0b00502440c181040d1621503410000c20110f072402059550802000801c0d030224460000102000c44106440301108101c00881070100001621460000400c080c0b45000c0441120706450000c0c00042e12172591403403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 591048444 1250 591047194 591047203
    0x6060f06031b0703090302090f0106051e041a071e0f290106032019030507090e040506060f060903060604020a0201061a0405030115080a1e1b0e181c02 66
    0x80c2c1c0307081c00700009214007071591190140007541d000b6184500c281d1941c0d006002480f40902c01c1d000084c2060280100707407080300050402c0700100d0f421141c140b54542c824160054115440030200b8800052042c0410401401d40702d00c6c2e00c035060a0049150694841802507400d903440207018009451900100031444640c00107040911070245d1141e40c0c444402400170a8420780700350941c4400c6210500040e628011a44001071003100100d1300c1d0b07210380017a005032070050200e405111000101148030603010f401948264000c0000304014100142844a04000b02185070300490341000980b00940307000428a4000c1c01c14ac40040e640d03080c441d4120700400158219403044000710592901c1485440081c1040e17a100320020060711180859403030500007a4460354045400c10441140441e8015100c42408040c0700032401c80c407640b0741c0d10506403030b480c01001071185610900c107101280f00300e8403181d8400c070315624003d16002501c2e480d6a45401550811070745480c0f5140070b800c1c40c0e20034031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 591049694 1250 591048444 591048481
    0x6070507121206120b0108071208040e1b03150a1a0316030204050d060e060601030506100f03091a0a0c0207050a0e131403030f0a0614101107060c020a050306060f0603 73
    0x14045405400170303d00094000c40a1140302c54030b1142d01004100341e0700018108820781c3d48139508500e402d18205691102c0100240340f80b10034580c0000d816400c0614038021071080e0101004121005041310412103419003d80054403400686280c42c1d000320350a0080303a07000400c82100d0700e6901c08440382140030707120319080190000b0014911804010842c1c2124584121110070744800b80c1d01d100045048401c101e50469002a484c1e0000d078640d4050242e449543c1010f03d00410b461040c3d0f21280359480301811400307070070100001080f91101c01d52180c105855041d1000e0064a4600000501050b466014446042d00c182000c1094500c00004010b01c6542c0655031080415000d21040e46941007218450050000c5800141011241d88203940988024000c2d0201e085071070018000d441034800781207030901c46620103a079046c0508001d40e50003005580d5508101034000e2047c489001140e50007a4026407041040c40104e030b0741c0301000c90742100241d661940b80d82d0f81e883c60350380c06810340 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 591050944 1250 591049694 591049709
    0xe150c070308040602100f150b032d150a03030e040c0201151509080c011e2f121216020715170105061206040e071701020a0206070507121206 62
    0x30f000680b56401061409080c2075400c0100703d50304100e0100000d0b0b554104100701c15004c091070501880301210059904002504480382c03c0155030600c8400c10704160100c00c1c4480c06070070402541215460008400e0301c2d0a556006e80f0074036607036024042d400410751003403082ea11150b00900e034034401d61003050f507818503c01504800b036a44c01880d0800328126401c600040ca00b0101090361400000d41c40344c0f12a042c1d4505c01500700320b00d00c2c1c04c840380020314980100440c5800350860605004104400c150310401d003804c83c0b441c0303003580b20301c0e180c5a101d29010360502804006413440d070700041e590f40580d03644404051001c22040032420b000b510380001d000e01044110100e20340e984030f0311040080140d22840348450762120100807090140182110b401c0a18074001042c506040d0801c00b903d80d05ca0b0b08a500b41c5031161489610f25103a030102074030980d80070a1400056904020f4550040d2460400501e0074401c0c3c2c503002d00e90011150500103004c0319131250b03a92019564010310042184 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 591052194 1250 591050944 591050947
    0xf030a33090818010203040b031314010e0601061b0302150406020f0c01050a0f110315062b050f01030b070c11040c020109031229030a050607050d06060e150c070308 72
    0x10340341000a50300416581c4442986680f003109865000000702c50a80341c40c40c1740c2d50700b0342d03130f6210710080e10b2024190300302c0e480110324484038181c0d1024082d2840303030240040a005c4560400100400c4101030003698010843d58401c04400300750040b45001019132580380d0441d0350341e914100301d006031080790102c000e4103d000078407654510040d40103c0c051823070400144590700e14001804260f8403162400c4041e0041000840c114640740c2c1209401130314040d0001c0e0424400c20346180001c4405c4c5540510007450703100030030b00710205104d11170b0f0200314204400025411915100212003004107500c0501a03440c1c2c1c00f100740401200e00d003440700401003041c4103210003098000c0c040c240c1590101c0c0425800202882d140000c1d009810007544601400243c4150f2200780e000b0080c4058242501409410180c0001c0344040c00341d140316140c0c90302c406944030340111021003107541561280c000c0107034441c43c0c9070042e502c440050715140140310030145c82d0840103800c035003028810350008155000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 591053444 1250 591052194 591052211
    0xb061903050c3903040311060d0b060309072903071b0c120308070f050d090213090b09160b0d0507170f09010c050301050a120507120b060f030a33 64
    0x3c0800a100b181d2081c03652540c202503403000d120340e2800b0700c0c00010140c1740407403030510250501c1400760405160980c004265070141d1004204140d0090310310022603004400e00384810300b90341081c0f1600c1102501d542c3d041004044217811140000313480d03070f8100024115044207180c0c0d04203800303604076000080849605da03502074007000c03500303600300403404a444407000070a40750240342542410704a5840e010b241c0310010364603c000340400c10049901112142c442d01c0d030200c0510521001501c40c2c402c501c0c6a0030300c881403504c1c201030742803802c05000300181d050220070040c0d000e40d803c05407000c00c04500790301c1d828015910080107000e000c5182e14003c04003c41d0500140c5001d020300f4420008002c1c0e407803001c504541600c001d004036500034400e507a0420040002038400c011041c020004d0b078a44a4881400e4002e64545060036078051800005111140c0b500d25040704103200200c00810004070503948004000005454040e4071840c191019000c806250310a60040c4400710410081c094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 591054694 1250 591053444 591053497
    0xa051309020409053601020f04080d09080d05070b06040e010513030e0d17030a150f090b091e060102122208030405010c0602160816060b061903050c 65
    0x10000d00c500340303c4504210108900c080404240750081503140110499a50082c00c842c501e40c09013007003030780303259820004041001c00c044080c00c083c001c102c005c0c100240c1c242c0300040c81324845030803811071a003024141e81d4503540c1182c00c8482c0c4661201d160364065507207000040040c20998510140c950030a000c01c480706040b60074940e1b010b4400c0d291a102e403c9250207104a4a0805100a0074400c000c190003940c1d08900340a990b118800d0312005c102a4102509035075260400c2e40602d00f914003203c03051183c0a401e02840c02c0300c002c1542d807a01a8600381c804501d5105400448040c14a000000f045283e4400e002021899200c0c4005c103a4860036106140c4055030003035001c0100e460071741d10100340d9081c040102c508660f0140d40358200050941c40b4072009602406001c5040400140c03c900064040c1d0094990b405240c02c01e520b08455506202083c2d4807030f00a21849010100001c0303244888000c00c0d000c068106141c0000d43d80d41e0714466001c0c0348a01e0003c0a0320b0a0142c00304000c0a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 591055944 1250 591054694 591054697
    0xf060309031e180603150312191707050d0e061017060106020a0b070903020a0e04060c030e07180b060f07050d021917070609050601050420040501050a05130902 70
    0x44506400041011482e092a50702a026401c545103505421a40c240e4440c030f8003001641d00260380345242548007003800700180c0303000400407a08020410204842c0c1d6900c0506242c907032503400e2420010703038154001c1500c003500b44004004005008010840a1417040707544d0003003a251401104841d020304200484030741c6908248108100440c061828840d06500426194101c3d40c0b03d0f0000c01c11340055584060707852800505c00d0040011545001000da1b64000050700100908018a10607091500b802410337140d2401c020820f250030300a5940b40700e400000d034101182e0001101908100a212000000e8071030681b01c00ea000c1d4010610b50000c0c246207008062282c4039401326268020603040c00e0742c4a84485000002c522404d00d101c2e400302d2000340590b420b800503c080f440c03a203600355a8040c11140c03a01e006880a42c04800103110340e040610030842c07008403420350f0700d04514245410000b14130460207801e04000d408624000c2c40c43c05442a55040e00380b01d000b01b0788050300c419084000307 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 591057194 1250 591055944 591055957
    0x11b0302100c0818010905030405061b01050114090f06030c040e070504020304080a081303090b090109170f160e01140607050a0501020c070b0301030b04020f03030d06090e15240f06030903 82
    0x21404004444c8031451414402c1241455102020b582010710b00f008200341c6410a180c2e01c2411008503408603000403003881081e0203882884924414451044c040c443c4018004104d26001031001c804d020841ea4002015502c95074100c0d80402d010004014140c14600b0755404160014008402e0008220400d405400f105899a81d031a00690710807607080342c0d8910140020f004290400000d01180071000000d00440c20181800a101c680d41c1c14650034a00401c00c00203490b40280c003080d4840d03181070065050459010611141c04c9003013880080000106118405e16140a0340052145444000036502a25002419540d03001a10700340a4040e6015014900d1180075908001c242c0b050360000740c0341a207811214245544d50b5030b0b424407410403005001c0545c944004d10450045100d50300038030028000d080d4010807144244183c140c41c1c03a4140c2c4c030062094142004011459482d60038282041c110342e03209100e0001c0b000d000c02c071003011007a8030341d8200c10000100605018000001c1c0207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 591058444 1250 591057194 591057211
    0x8070e070e121902012f010c034d0d0f02190e030f030415110d0c1203060b0f04210210270306020406081806131b0305070302130506011b0302100c08 65
    0x92860410045044030242b899107c00c1b64840c00080d41c0f40395100c0400c1c500a4165002ca02200c00b0180c9890030b508a1440c41d040d10042c001b031140f031a01da0134094003500c450611815410709034100d5222040c181e441d07501e00d0801c10b014141c4c01003a50100f01c03603c0381e4480c00b8162991980c5403114001d0451940d0303130341c0002c43c901c142c010481560005020004030001e5442c001005042d0344e8281706415603c96200406448200200340100d01000030500c5110b03640186580c0c81ca007210700c80c000d0068403010411041b50400c107078090389802181e42d04550341c03860042070002070301d28241604100700f8441075014000e0b00340841000a95070042c0143e13506c94841100301d69840c00d401d080424107003c1a502078005002054080350380402c0c88648510504403890880b48502c003807408002d6507070040e610b07644000400c00c154280303d0410700070901005000e00c0207162a4001924205100c2c8002c059292514400424580f091080300c0310032140074401d1001c8101c00c0001401281e040e0350504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 591059694 1250 591058444 591058451
    0x4030210020f0d14161b06030c030e070e0c07020105070b0f1b31031707061805120a11240603030705070b1308070e070e121902012f01 59
    0x1510a402413100300c00854030b0b541c08520380030078209020910203942d041154402c074040c803000c0e1020b1075050b07030401a201d5550002554040c8903401002d80c0c51a400c4840c2940207603100f88503102c0b00043d41e80d401503400440f59901c1c0c0003440121814813811402420015600c4103010280b0306040b10345002d80c1c4042d146031502010168001c106200300c1c1c50700c8183c00354140c511146032021f00a09412412201c0e001d2100075541e4541301c01000d55080c0880c4426800612002040860722841d000000340340c801920280342691a190f60303a425800681c8803620210f0313800384040c4100d0743c0c0d240140b5100c0568400406507410a0884010a040c4a11a5648100013103442c18000144c0f513000390003034010107a41c0d00e020b001010f66444020a000e40090700500450010304c1008410b0040680c0101c6c0b209034504404020f0034a196811818800e8441c0006100200c20010300004c004120300703480c10f514036241c401658011074420f510703641d403036000c0d500641400d058a48201030b109450002d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 591060944 1250 591059694 591059713
    0x2060a18140414070e12160801090b1b1e090a08010209100327080d0e07080c0303040b03010302211209010219050d0f440411011404030210020f 63
    0x22080f40f011500040020410301c2c0303009080c0f03850704d8244200300b0318500f0b80700004d520004406540007640c005e500c03030340c3d103d00003001080705a0140780d80c4540078810000900d100c0c1c2e080a00c031740c441e202a4182e82d10b0200c20114155001c44121840c88000a0000c4825550350b04c406020b9000041d61a11801402041c0f407902402800307031081c25100054201c0d4540305c0308106400c6d004160400346c416060602c150b582c111564818440194503030070061100c0b0345030480091400e400100c2440c025007040c0702c01c00c54904540306584c1940e81c126181d1a05c034850042c1c281c110403210800700604d10840840c0b501d8002c10714010418200281d00307030351403a0070f003600040e011182901c0080a1754400309030380c0c100520542c0c1c0307203d01140e980381000d1010b1019042132030103074031840102905110002244200f0600880b000c6042c2d0081104042d07501c3c0a40f40d994002050a07801070502003805000070720501080d0441c1c0180d0f81c01422001415a005170081d40c40e086a60510140e100d02000c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 591062194 1250 591060944 591060971
    0x10e100e03061602010b0a030804171005040b060306010b040b030103110112150602010c1b23070e010e01170d051c02220f0b04060e18040b0a050106180302060a181404 73
    0x42504d4200b48400cac502480c200e55403103110111443e2803001d0241000c40054880f00b03020320750141c0d00550790005035040c038504040c2000b8040c5c1c4840740243c4100300802a5194441c1a02e0442c3d81213910840f51814660060307404e107504000107902c1c14500031003080c40300c5030904640c0a4031310740d030300030802112001010b840c207420401d54451101540408400058000040640c0c40c0825869059014046804442c5040f1a94005080030401d420044c402d52213440e441d01d004010030307415402004014840380340c070350a50703031500c0d010003000180912504011001c02c0f0161810500e045548400c0c1079410039981d0745942854241501104001030701d1900c003030718801035641e1a164186490301d03100c8150f80c0e03c464222072503046806c43c00e440030003031082c00b032040c0b056001c2c941000035840e04148a01c01c0300d00c160485803e202080501443c4010840d80724416242c1c1900e4003555181d1610702680d803a042c004840017003140210003c41d410108a045201444003520180303c2e02c41c11440c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 591063444 1250 591062194 591062209
    0x30a1a010e0112090f0b0a060617151e060d0f0c05040f0920040303020c131505090c04030501020313140703031403060f060f2106010e100e03061602010b 67
    0x10700340000c482c0c1c3c0b05984a080703603600c9040b0b118401e92007116107042550f10381c03041c40e004550220501d55201c0003004042c0e000b1652018920004e8030307003101032401600b80386042c4043c0300f034a401340046041e2249031504030700c0c864001000040280b034617020014010f8000e04507141c400ca030150300740300440c544540140140d8080d03840c4804918481c6061058940090856626004d1056400f8114401500031131004102075400382d400b410004040c4014082900c0d00c1007030402c4018602400c91400e01c2d10800700708150b8208030781100b030360b456034401521607015603040a4960f51000040c0088408020355012203140f043d0005440d201ca40150710703850f5100e81c0301c040c0c0440c84030a070f00d5038243d0b8468001d40d8417850040c0700d401c4140c03404002c9095500b00e030303441e800c06050000341c4d14200809c40341f81a01d01d41003500000c119240000000301030304000d000781c0340204550364200e08502d0254614000708071000d401c1b140345282c4800030381d1268940d1082a000f55103085105046424102c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 591064694 1250 591063444 591063467
    0x10c09050a0302210a0f060c080f010302131d0102121806010e06220c02030406030e010506030a0b131406040c09151a0f0310030b010602060103050a26030a1a01 70
    0x90a60929030840d510003413074001d030103040c2c2d0b00600800301154005108480c00503403a42c0544000203101c40e40400192070b00d40060280f41014420074010030060341e4012089208543c1c100003c20301c90b250000c0040130341d450300500c0d070480d400070900310045c500c02d0884502c5113061100500c9a030744079691068403500300f0301400103040c1c18000040c4450401509405c202c4402d540d0000c60b040c2c030300700c2c0c043c02c07103503041002e00c010303000011304110081e4075001d1844040c0501008001a0034400002561008228030090004100c1030002d440c00c602c202011003440e410440f521644030b00c5180e1161070320f004440c2220801902080072640ba007451003074100303040740c00050a10603428038110b0620961780d1510071002c10300400c071945603074039808080e5005881410102c9a49030861400102c0300b00140c100c40c00b1988024010008a8800100401c109401c0310030b0140c016804202d40314440c04103458620185000411303c2103e65071030f449107402481c5200007454442050004484421258 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 591065944 1250 591064694 591064699
    0x121d100b01080727080f0f07090212010504050403030905061923151306080a0507050616031823010f0e0604060305181e011815050402040b040e010c09050a0302 70
    0x165002a421014a0024000c009400d540341302c00b540d40302202d00c0c20000c0c8000a020350000ca1240a42038000c0011001404440b03000b5420800904054484d400051090394403482e1180701060a15009501c1288241d81103000d640c82c0c1c0c540309110001c2a401402921101d5140200b4460b050b1341a071800240c503003100c00110081d8407820000f80c07141080300703407003940200d02c0d41a41c42141100e206a6000b040840080c1503945880d0a1941c1030103e81e0b84400c1c0120410002c0d201d0b070890010044000d01e90500f004012440444100940131070503801c410020001c00800380c002110450741100c0c0c0351801d9981c00c00c0c40d817403074201716105140102107980000c400d10090200500a4004e640e002c52500400010740c0000034016240c00c260a01d605c013082d027036102001030203100380503042c100d60051031010041c080070380c2e802da6200140071882d035420740e40d61701140455803180c000c90194000100103200d0300d001d00031040d000f011400c081c0710224101080000355410070952190449800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 591067194 1250 591065944 591065957
    0x318030c06120e0304080a02030c09041112030f040609050913020f060a0c02150c06100b04050f04021306051b06151c080a0903150219121d100b010807 66
    0x1030403415592210800d8800062640f1443c4142164004001420003881c548006080c140080c3c010f00d81044044020b00740200d15000400000c15040d8110654004051f1090f40001741c10104050841c0107a0b03007000040000058001015580989030780c3c2982c0c801c4031411250307181c480441071168049000290402e038035101200309842d0680152082e103009040c04c01c020000756000525031418240c684606034004104810700b0341007004508d610030310b01810410001c1c140303140700e0440d000d24030545214103121800c0b00d4940d22150140e40441e000042101030140d00e40748090700581000c1c100c00032554045010380d030304550004a1501074170301141d0700380608000c0c4080c0200e41c1610741200304800c090401090000702c0110040a060307440342c1e14400a14198a0a240314000c0140c150503c030340188040c2c078202c03000100b220000002402e0804000141600742409003d079200f01c92020321401c91040480170300425403040030481408104800e00070700006443c440700030b44141001521 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 591068444 1250 591067194 591067199
    0xf06010201181b080a05070806060111191a0901090318030309050d0203010207020315061c05060f09190c0312180e090a06020d0f0501050f0114031b07030c0318030c 72
    0x2800300c618030b080c43d410402d14101030b10780c001e0705c4c0741400200c02101c144e40f0012040108400902101d40c01038424a0404031134404585025035030015041045c1480420400d0401003000000e1941c042e00c825031020402c41c6010040b0900030004e92800f90f000c100511002581031103002000029254075865105c10075041605100e00c240e06043c0482e00340d07500300040c8015903000c001410034083c0b1122011510703c4d0410603c501008500c058403030b02114950742000085011071600d610050b40300016002c0d5032280b181c1440c103085040b040c91284104201d050900041d000b204003580d004070610345c440e20348000100d41300004501d010400c01000b03023003804420004241070b41c21580c2001200c805c403060fa1a000d04903403110341010242d41e568000c40840403041d0040c40d0060400311011035510303200f038001078101392035103010f000c0d5401d0000010f41014419078100d41d41075007001042c0c1c3c0360991071a003d44000c41d01007050b0b02280307508195505950142164500303490b1311400e000802c62 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 591069694 1250 591068444 591068453
    0x603010204081905070f12030306081c0e0a0905011205011103060102060105010c0507050301020f0408060f2e030b0108030a0206010b030712020904180606151106150303040911030f0601020118 84
    0x14030f07102141c040c0180340d40018000b40080108025140000300c401c064051890f014044600540c0310350010b40207401c0170b01160003010600102250380d401c1000342d107004e0800203411098a5003118104624110020034880811100b0042162141000304042c0030902c258410034002282c0a50045c2c0c411001800707036500c10008402c400d88034000b1034003501d45480000c2d0a980007400c107101135410100b420000100d04020546d04410110071601641c180800c290818285020215120000042c00040e24a807410008401150000200340704c80d40c50b004042c0d141d0b8418104c00c0014442c400010841040c040d084a00a09494071801c0c400040844008003a4100c0d50006074800e40e00c0c10302801c0302e0050891218601d03c034540c002291814a80c2c0ca41800010058001c01c04c4220050515028000110039412402000c0b4120b8500c06041c00203156200c1ca0308403401c0b02e410401640415a141001703180130301b070581615291a654440120300300c030f18201c3d190f402450115240c0b004603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 591070944 1250 591069694 591069733
    0x51503010e07080a080c0a060203090105070f0c020f06090f0a1d0708070c02090a18060b0a0b040501050909040c03020d0b04050c0105030c191202070f05010f2a020c10020d08060301020408 82
    0x101a0416503009547ca529203a0491f0401c640c0400f20b44d4441c02040301c0203608c00307850000c00745503090661450206130081303521200b101880303901070306002806aa45558415a0400043c401440c40c0301362a120074600000c0100c00c004088209038510200300c01d01d0252134a80d10844071341d070700c14840342c103941c00301f2500030000307800181071380da0f20388640c1000d83c800d40040700d2050041c1c501180108a407802c3c006c4075011a80507600c03d081c1408144003680e400000c9540e5042e040350059045e80f00c2d4140440c0c90307891b941c4000e6104074200002c03410801d4200c3c00c507115501840583d002e013040c1c80015101844200c5003030346540f8081180c2c0f650080480249821400f9600c2d01901d04150180b800040781d005080548072405203c401e0001c0040034012140300081220090007141101804800307040d16540740c84900396044840e6100c100e1080109625214008204000c00761400f02c3c040c0d1213168110401000880482c000340c0181414021141191600402030200c04141075000861 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 591072194 1250 591070944 591070957
    0xd0f140a1505060a053006060a2c070804060e1504080a0e060a0309060b0402091503091609020a030b04050c0313050a0210050a080a06060c0201051606051503010e07080a08 75
    0x10f00110030118280c0c594552401c1c1002c144011001100c88401c4c2002074000311495400e12035000f0380070081c0c561500305107032086a148a610380904030305000c41c40c2b00310f141003141a840c03600c1c00d400c100150382d104182c03030702942c003940307040010391000307110701c2e071120312264414030320000c8840403c00240310745006040c2483d8615007840d5400030400040e040b0780c000c8149500181c2c94031410f00c18072155200311180040200c8013180340c608202c0c00700342c0002c440d11040f4014203000c0005140b84106022144400409003e41540c103038682d80140000c0d040300070390700001380c503240c0303c00103606040c4140c40c0190350088200c0d04603590400d11803c1c040d141d070710031100360013002060401038171242c1e9400c0e481a81c2c0d4450311f4075034203403001c000c0c000b25008154840c42c50403d00c0400005030405a4200155020301c0d0241e47c8490203580c9058412030450020111450134040000800340008d42d0362075194101c0c0240b0203003502003c00c580e240110301900d5865004141010001004040140324 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 591073444 1250 591072194 591072199
    0x9150207031b021020060f06120c0f0103090305040f0b040f060305100302270c0406020f060106080f0a110d061a0403080301050402070317010303020c0907080c0d11090d0f140a150506 80
    0x181c0705100c03680c5c28207144091310f40040441070a070612549250a1201b990084c1140340203242e06081e00c03000880500509000e2418103584103040000d041c070582c1290b0191075080a100b00302d83c3e84240341c10650788540300c0d034040c00c2012113000c55018402d005081c0600d4030f8076420103061b0308507001c020300c4401c00300700240312014104580c181c01c458144058440d5200108032501d441c82c04001034202840d90100c00c213540c1141c401031201c517801c80d1100703801480118211a10340d45001e2031400500303050355014400709002c14031a40c800d03a035030410b0083d0f69032030003180d514680d1710310030440f00d001d03a020041c14140280014007060a150307015103941402498115445c046071030300d0043d00c01c801c0e001900181c12144a08010f0706001105a0700640349207403050303043c50240e0a00c0c25502030441c86000320390711031981041090300081600c141280040811458403031500d00911400041c10080711f07140740c540b0322104803c0c1c01003034078100590807119040081e0000c0d10080000c1ca030003401c05a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 591074694 1250 591073444 591073487
    0x7020f0415090609060f081b1903050a030207050406050a171905161a0706051008061905090a1109040312020703030b010206160e060d09150207031b0210 67
    0x24150070490340e1a40103150003400040c68500b0700700841c09441030398000c0c0d02d001e6001201080041c0c000910603100035401c858800c8580308071000907000200104030741c031030052264400300074402d0225951204130701c01c0e002c8071101c03944c400c2030000307454061045650106550400b002035204981c6064400c100310780544040c03c000d2200051640100750064075030782d00048140802e000006610009440268040220b002c02d03001401d6861246007801045140c0300c402080707416102405280107050b0701004c0e6003140c80d0008000100000c0080500c003001d0601d800319100c04130206c1c0400406402c50100c41d9150441010b20405810282c000c60401580300048551a0120310207814003600c259008140b10381c0400009117404006405010100c010525918105070404420703440c40c1070a44025856200d5405554014059400c1c09450100444408240424035600800d1524401c0d12000d48d6116454861b80c0704859404000303400510124222190782d0240d800051a00040032500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 591075944 1250 591074694 591074711
    0x106120b100306050901361b08060a0501081006030e030f040b0403060605180a0e010b0d0506010e0c04150c0f08070b0105040506191a040e0f0708150607020f04 70
    0x12091001001e422000a68072101404646001205140101840144495005005094061034a201c0e0915103224500241000202a840e0b0070050f00400400c02800b018440c1c0800517010210498101e8850f03192580046078560084207410700a0000c800031060302414100e09030014031081c100c880451100b4418120720303900d600d00034000351146042480c2c54924528040060315400c0d0803591103030b0006201003240b078400741051a400800d042000c81d000c9016511180107001c803103902a0080e4440746204203101001860504039045030f112020b01c1c0c0c0e10140d0841c0e1500460040d640c22148905004106a200c0c00001031458028a01c284106095641b583e40c0d80c0c1c005002100d1100390000100f14a261a00c03a60798407200c240d40a100214260000030404001ca015140054203605007c0c2025440001074501602d10202c03998000c0c1441d07d0542240301c800c86080c8002509080050140107826440d204041005064281441c0a43d400c000d0003490803503082d90001d0f0380c1d1450 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 591077194 1250 591075944 591075949
    0x50607031e110f1c031e0f020d02210114010512100e0a05060f0118180f140405160f050111010f02031303020f010204030f0b100e04030f020606010f0203030106120b 72
    0x1d1407160300b143c000900e50800d5040c140c84071050301e8501d03041858580382c4032a91032540102c00480c01c0540c02d00c0024014006c408010080c010000010101407011441c5600c0c9001074880104c1405c440c541082a030ba40d801e055204600311a060340d0003d10107024004041070b0040001d40c01940c5180c40854880e100c2035600c0440e0008c41d200d510407602c860901901e403e04501c5010740720028a4040f07061000c15000340c2c8a68441c0c0b0408041c11000b0540b10480901603112086001041c002400b1800c4800d40e24207504100799002c0d15036004100700c410507040e03031030580c5044900004a80a0b1913140000548194500807174848030355407600c04019100c2090f10086100303920403c50b8440300d03025404c000745800c11a0040303000c0b0340e00c10401800800d04e41010f240102d58000d00e90281a035032100442d0b0001d5243d0b00007047e11402c007050108041d005081600b90301003d6007220000e039542c01c011581c0e0301000960300056041040117002e15071003001c0540003600710120108601128002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 591078444 1250 591077194 591077203
    0x20f0d171806040b0403110d080c0903070b191812081c05090601061b150507020a0f05060f0a0504030c0b0603071a0a02070806090601121104020a0315050607031e11 72
    0x8080710a903101c101040300300b42c0c007c1601000c8003a02c0008050b90f515002000d01600317000b5101041c100c0012a03907001c180c0d02006058081d1072981a000c1e01c03003c0f01508030100c1050742c02c0c031501003005800000c4840303240d01488400c5580c0d0042c40d5211034001e842d0070707620b41d000501c6108000704450035403440348800d014041c000c1418400800e1190700d400e000a00d24511440c82c25529813440701d000c0042401040c50801d84400281d00050b6611011400e925114030050000d00e03081c6501013080c24800302292140c03150700850038100b110b85d80c0350803020454a003102c004010805038610314000c2000d01055a52001010303049543d002c6e01c80409081d40e0001b40d01640ba01080001c148400c194148103031001040d890005003064104603004903126401405040441020410210184078035010010b107401c02c060011580c40030000c0300100030b0400c1c200c3d02c5180c9045000005010708000c402c9800b4240c050346c8051030001c1c120881141c10f80401000c1040000d203407003203804a2410710 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 591079694 1250 591078444 591078451
    0x70f02040f0216050c010f051314010e12010501050406050f100305060109120b010302030c0d030c0b0402030106180b040605010806130f0b100c141501030f0507180c020f0d171806 78
    0x30020085c01d09000001014980c10240c004100034082c42002e00c503c03030b081c103203c042d02c80f04502c2c0000450388100494481a1412034182d20407403199400e582100107511860698100340c2d01070042c283c03101c040c00000100c2c003550a401c0005903641d100300c280701c0c0d40103640008051404c0a030860760703808a0780d043c6505880c240d400c030300706000400441c81c0802c0030081003941500c4272091201030752005800c039500558013030b103903100c3e020024045590a61080010304401040382178900341134400d40c002010800c90700d6000340e02d80040454550b00036409a4884e55008165403041500c4107003003c0a00b5518544241507512207503480016a18461080f000045a030b4401c09003112508100740b41c1140e640d0680055000425020b400c940e0b903200003410340350042c0403070a100700a0301d0910702d020050382c071419051030150a0402009542e82095103051050b03401c8a40c040b61408110303885c3c5586d4140000452101d040e50303c0d8642c0598621503114401c0300700c0408206013091051308119085 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 591080944 1250 591079694 591079703
    0x71505070f090b0a030b03011e0f0e06061c02090103060b010f020703080f0703020709060b030f0a29010e0904050c1201060b040512070b0d06030b090a0f2003030706061703070f02040f0216 82
    0x200e09d280c0151420380700700001c0c0013242000707024102180d000d440d103484001d0003080c042c42446011800301d00e1903030b5240041f181d004d000455550ba403030415400030103681d1801c4e40081e5009540c3d0001d14800502c56040c1d0350060032562805d41c00024440a503030200904a0079030003540400148214140b2a002c0101290142c2640d245000c0e810328013516030040c0000c104c00c1c50100f006844405021241101188441e1007500c0d504540c00103885240f1b149413400e034001c420700d08102c01c018005c52410030030101134135170680e99181261400c0c26a041d80c0924441200d0034001044103180c4080701a8a6203e65002d0300c030550f07129a02c06180768410341c04403203d140c0700c030b03030030030070024281050f0380d22050390405071445134010390b0760422449000c240a847c00390810307007071503005070349a0101455840c010201da950390710368a070441c050200c1c1e10540b40040328003030310b0701c2c9203850101c2101c050380d9105d42600b56201c0594200401403583c402000c1c43d0320303400e02416480742c518184110803180035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 591082194 1250 591080944 591080981
    0xa060807301d0703020d1a100611031204150908040905060316050915040e010c0e0a0602150103030c11210610061b17071505070f090b0a030b0301 64
    0x4912401c0c058404000c000100d45002d9003445086020104120003a40d81c1103e503214840b58900340000c01085525031005020464400d21440341e44800703880e8121041c50716003003d5942c0c003a03c070703981700c2c080c1e21040c030f43d410840400200091390700914540140d411401c00903000c049511030844d50f8101d50061301d0141d030b0740e03001c0c00103030314003007002c044803850011240c0f4482d4101404500301410261038000000c41e0542600302591355900500e01c0c9e002400c00030080048951002860421a00d80703446c0500700d12000498aa48003080c040c0a16401125188481c1d04c3d40d030b8114cc08000154007510490001c2c0c000d00800d55985034002d0090906000d60301054060070344543c1002c001070048070000321000c0301000a10342102c01c103800b10045500c44e08103041076003862900030340c649501d21010000055503004001c0201c00e1010101852242000030b0340e01c6881c160384e0451006650383c00300c1c1000e40200400d148000c01002040c2d02450040b4016040502003403d41c1d11003004402102c20703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 591083444 1250 591082194 591082277
    0x4050912160b061509120a0602030703091712040f0c15090314010b0102070b0f040e0a0603050f0c0f0603041a072303011401080c070b04050c01030b0603060a060807 72
    0x1140b22002d60021822138401c00c0c0c00c0c5a40d2810212440340884290241c40c0e10748810307020403800d00c00c100390300c0d401180a5560b0b182181d0b00800800c8050801c481544030400c00341c1c40011010b040c0c1c0c0410000704802205903d69884a0400320701c00d40307045031f605010b450082107207904201c08061044c65601d80906d903905601c1c1802c551075030070f21110011380c5001c80c0c0c00f45681e030010702402111900d004055507148104a02503062042d500034003981d01c071110911481c54a10f0780180200c03405081500c2c080c0741d06d0311000741c03103280042149600208031120b005407403070103500442c1c00910481051601140004114480c281d0866032040400ea130008401e00201c0b000300300d0b4144441545909140d9810300000b0b840c60141364201c2130400100b0000244680c0c1c074041115482a040b40c0301581a1600341340c40c81c0d55002c49682980001c0c01c0618550700c2d8241142924001c100003003120713035640e040c69411282054000c01503c00c02c05040e00d481950410314025080844c50080c1440d0002c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 591084694 1250 591083444 591083453
    0x1a06040507050901090605090a09050112030311030c0d05060a032a05030a0308010b0c12030903040609050f0f090703021b06010302040e030403210201110a020a030306050f0f0405091216 81
    0x4200030070640c00d0000c2000003901a80c4c0c0f11a000c0c2c2562002e0a11544401400d808031792000074a40180c07960754a09070010400d0520510290051807007036509005c1864540b2410070140025555070380803181c04e12010380011081e42140b40e0100003d0f140d4900950340341c6800da0b101252680c0c40c07409502d80c0640c04039407c0d20040040242c4402d40003010744048a50303000300748140512404003a80400324415044c80010b02c1034005c05030341400c04ca9106d00b0185a0070742c407070303020b0700c10540401ea94000000b01402c0c00c0c0341e00701055030010109201200600d023840300da500020f03c4213041641c03c00c0803129000380c05001d014402d16810040190f50b0440c41800210343c43c0c01c0c010f4405a100740810000207401d8583d51401d40f0021040e1644000444070690146c00814000c1d0030a16000c02c86400e0503500041849070903000c0c1d42e007400a680c3e150248803c020402007201d41003039030350032204400e051980010f6000908da0f402c032004140000c1c1e141403603030401701c40510b400661070380c0b200c02d01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 591085944 1250 591084694 591084701
    0x1201150801050f0f0402090a050d030909060815150f0a170f031e131203052218152409080f03070b0c070204060602010b03010c0309020303040506161a0604 68
    0x1803005589465072118843c002943c42c85003074099510070307500060101d0203502c0e095002d200902e40644981c000b0f894a183c09040c11845000c0c1d00401071601c9000500c0d20310020717442070080160b0400d003105444200d40985101341c0f0350149074221000c101c1d407000e07940311402c042000b070a2541c402c403204d8200d41c4a00d400e14142040e41140341c0d0061210000d960b410f6103200f07041080e0160480c4e50b840e1840308080300074649034001500714112480d000103044e0428001c0081b20211400c4011440f101076550400c0180f50142c3d041000d07a0046201008005038803a1220700c1c00c0c100c14150b00e40c1e8030303005044104680b1000b030801c08160340c900019142c20100c00f0740544445009000f42403c070220480d6070b406515006084591b0300000305034000c000c1c20440b940c441c0c000d00180036141c0ca8440203030181c4142c3c0000c5000790301e072040b0009554131a200c2c905415034000e01641c502442d02c0204012038200e4040441481d900d010348500003198180c070302442c0c1000030359071760b2245420342c20031044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 591087194 1250 591085944 591085949
    0x320091816060809100221060357150d0e1023040f061812020c010e01080f090705030307212a150218030616080a050601051201150801 59
    0x1d005104540310901075010041ca0007400d00310901070f42d5100d8000914010300000c0c07900443c0301c1c510440b2056240c2d190f12a4080c9100d80a403542c0100c8000c040080e000165100c080041e0481002c01e040e02d4925008080140002d1070142022906040807040310dc3c0c00d001c20001e83d01c0034008102c082990b0151012004400a148031011507140c100406454000c0c0020324030320b959400030041200c81d50060f04e42680700c00d0700d610b20322001e15103030b04916120002d0380050f10981427620a50b610501c80f0408260060352405580c0d1a0280207010101010f02900d11500032000d0102d602c3e2400c001910420b80a00d45050114080d80e01640400171aa01b420f0b04021582310b03505042800444100d001c44071022040e40701403003909045251010011b18000d05e0340c00001d00074890030f01c0000784002514124103403a41e541301c5442d582002202c281c00e84c00070520380c030005000044190b002030b034030080c10305010703240c28104443d0500c402e001340c004013401c001442c00003241a0707000c0e4a0034003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 591088444 1250 591087194 591087223
    0x6161b060c060507051c0b130501030602030612010605010c020d050f03030915011a09090402040f021602120102090a0515070f0b07110f0319030f020409060320091816060809 76
    0x70304070300306507000100d28008081c000f074943c071043c0384400c0b602c81d9031254078023401d003541c200003c0d40c403464805c1c003070350081e101c003886401d40d0003030b034041d1110600c58881140c0b0142c6a90302c141d0400e900b400300c110503030141aa032070b0160044401c1d01034400e0000b1407180c201580a0040c0e0326114068005074007068010720070748290809000840c07061b41c0d080750303128403044400d0305443d40c5900c009006000800311482040303002050441d91410b03100e04661003d88221140c0d00c03150314044040b4200c2c0260402d69030f00000414080006050020860382c0074102600450f10f011815142c0c0500d42106110803100306203100104101190b0180e0103003446103a95010381003802050240c81c2d920b000c1c050304c00d5005092802d600402074000d80c04440c003641203170070a40d121981c400918009000901c01500e070074018a007011003244442c026003100714001030110303641c2e88841d1400d80100d040c02201d00031700d10409081001100300d0501242c01410f80d0741c0e85105500e03000c180380e801c14000d115440e5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 591089694 1250 591088444 591088447
    0x7080412120e1015080a0b012601390c08300405010b0603090d0507020d0b040b0712020c1b010c150203060a1406161b060c06050705 58
    0x2480800c503440d21a0162514000391a08000c07040000c18640c484880c01d0301c20115410300c06525500500e0140160061a41c082951280110f03201d002145c3d00030300030b048004c018804030241550301840d148103c001500c034040001c401d282150601461000342c554040110b4002c4003030341c2c0c940d8032003035001e001e0204120102e0300081c01000080500524a0901080d07002034400d1035519208a020b4411031074043e00c9607a5400301100c0e000703a5054408d5400e190381c800c49418160103d1707009440c070714018034418110100840c2c4507004040201c0c0d1100c0b48440a40102d094410003d00943c0a00713244403540c202100c02402440d51808080d144600501c0490003c00c00410249007034000201c070441c4075001d0030012506881c01d200c1c000c04e84003c007548150810742540c0654410401940e0069801c1d84880141c000c1e41400c0740080d500885c00c000c80700242001038540c1100c240b01d170046c0140d00700710815160460080341c0084c0c1c0003a280030040d900b03014090042079004500d0713051a5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 591090944 1250 591089694 591089701
    0x613060902090114093601150e0f0a0501150f0c0602030405010203181218030a020405100801060501091212030b030d0f020c06131203052101051338060a050901080708 73
    0x117190950900e101d040c00300440100103070301b440081d00240034201c00103040c4602d40e03454402c200780344142a02e980038000d042000203012002140b0075135040e80c10903c40d0012460780030300201c40c0c03100b50200c80020084400100400500c090018500440c403400001d83c407403810f4070001d52980c92803a800f118540c00035003002e4012094100322080c481c01400c0132420700c1c0c056000300f4504208803e00039003181c074260070404c2004078a0030f000c0595402100920116507030710011a010440c40c02140e11030084100200006200a40042010092400d000c100b40b0041d07000242448800061540480c0e0b0f03e014540613154103120343c1c140803001729449814802120740000c02007042d405492240c107002c140802c1854090000d8481d14039141c03c06140c2e984500942e0000c83c4428800c45000302d0345001ca0002c078034050b01030702d283e109e203162040342d42030011a454150480ca0610000381086001c0c0d20120300d80302c00006140e811062384509aa4514070707030005001d040001d00301010485c400c01403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 591092194 1250 591090944 591090991
    0x203060a0c0e0d051c030b150a1d041d010f0c05120403050304240c0e010804050c06030a0209030601091a030609030f18100807120e061306090209011409 67
    0x5401440b002916420701268a5103003103840c00d60312840054a00703945c1c6240007085e5a25422107809030724140c9010045840c4020b0005d800d003d0800c92401103800d0141140710041d16201c41034003040c006101192505080c0c9111000c0380ca00d61040c14265142e01d2040f04640803802041f442241e580b40c11031401810b0703c0c41a0598802810040410038000045801c1c4860a000c69028801c5140100c0000b00d803000c40a000341404140d0002142d40000001c1d110341c001d05140f03100301e130410081d200d10b400c000304224080d88010311f40744030a5400c0c0b0184403140c80c01c00c03070207001e06040c0500040c0c5000c3e0483c003180360741c070503145140709a01c40c1080084d03010b0f0101c240e0312580035642c0a00e0301d4208101c0250301d00880a1101900309126800c0040380302d40c00f20303a00d800385510b41c0b039010b01110190803881c1513840054016500d523100c03501240c0115590004a00c0443c007030031000074821000d500140c041c4030700b80d012900d070040803900910f03246400a20981c010a03030800e0040614042c918 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 591093444 1250 591092194 591092207
    0x30905030d0903080306030c090f040203011103091b030f070305060a110f0a030c0302040512030a120c0e0d080c0f030a11011a0d0f120f020709060e0609100807030f0203060a0c 77
    0x2c0200301080105c0401c0413a14200302d40e00040078000d20340b01c02440c3c00007103241503c0080300d051303200b9070800b981c0d45080b03811501202e0150100f1005450351810302c04003d03a4440725104815003511134030ba201c05160005000c41e1010b03501c43e070040d0029040210380d010943e01044201f041c000d108015221441c400c003000c442d00e01071182000714220741c0c3e29030103034024040e55001a40091031012400d0700d4201c044014882c200551701c0f00258048440a80c504491016a000001c1010140169814a0007210706c0041d103214042a40c40c155144407024103004550007003440c03661000c900c1c181100c0d04403428160545401000304040ca42d5070081011414120074603d0260140740c2c00902072128451465802a801c01540c0c0344140300580c00074150408003204900500981401190620050203080100c0c2c20508050406446110030841141c2026120310200b95903400000f484110901001d80254010304a0903078400c0c4900505040c000014161140949003034403400c4800c0d003084 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 591094694 1250 591093444 591093449
    0x6020c0306010b030f1816150c08090105160639080105121509030405180108070509130c061715010207090b010201090c030b010f062d1e030504030905030d09 69
    0x1005503d6200c3c1903401d520110f4a4413200000d011f00c482500011390b00d00c100208513505603a8900b0750107000c100468000080203001412540d0401c80c014196101d000500703005100c2142d0000c80300701c15562038044410b8181101e0703030841c80c01004040d0024001c4001c440e50204040e002c1000c92002e001405100140940c0340f0404c0400c0f49025140401c04c01c070708440115030340d0341081c1c2c20000318140c1d480d040f6100f110305c18507055150803081402c0c112203d040b1103005005084282c248401c0102d2090014001107004010321004804101c0f210051401010301e0f44811540803109040b5120742c0000074a41070205071410024111070364001826011920750b82400501c060105004070701601c09c00c200a0444030b00d625000c400e120400c009a81218a04000c01ca1007540c0c4001c140c60340c02c01290f90303c0c0c1d040b01014596481026080c0d10302036133090740c40c000c0e002d1681c07100c542c01160951510100000c1e51901004105504000d0010107440220024540d20304002c400400f134610a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 591095944 1250 591094694 591094711
    0x11011107060c08180c2b0308010509060a050603060405041e030c02040c0801030f030c02150f09210a080705010b0a0801050a141b18040207030c150c0512130b1006020c0306010b03 78
    0x1070384d000d821080d0901b2220a1001e8403d4040982c40c00c074240100f0b607031030030f008981c0b086a00c0c101158492800c0c02c01c690803544068540d42c21940c03080100001000d000b4401d40742400f4079069034141012848003042014825120720300c104006006210440788050120800d008a110060001c1840c04c078820303a6081c0e1524003d1264003043c40807810403949020390104128001c28421040104100074011000042d22a41d40411040c4981e4400c856005060701c15600000d5038040420309441c0100038007409000040340080e04100495551081907002180a9544005101804120703004a0f02c91400c0c0d000840d416040030401800d40c920104543c2c010108009614000c00c020181815407580d0010003c5403100307000e040103004855070200807540d10340d941610f1150848544624445d41d10141e44480c1013500c0460f82c44429480a8000342c10740000c821002e0000d940c0d0f00905100b403884240c0191242e1408502070f1410200d140404c0c23103030704010014084000da00080d6a4810001c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 591097194 1250 591095944 591095959
    0x1605190c120213060f0501021009030e0108041a0a02030601110a031b03031d03040315060b041701020c0106170f0a0b0c07030c0f0303020304140607090611011107060c08180c 76
    0x14400142c1d41c812001c02d441d03c0908101d00010380c076200180300d800311402a001d403603488041d84810400c0300c80c5500001d010404030300e030422095104410b01d980c0a0300c118403402403600201d04d0082c100c5812180402240d800004000c00340d60b0107da5400d40743c4d407090040008003902c1d43c0c003403c007500c01c5202c41500c0b12011040c1c01498800d810484691503884400b0f120400c070050603a071079502600007903a0464604528031003104491250781d01b118410040d150500307050090036210001010a10b034240c2d07409005008900c2421b1141c4c200400c00803401d071150b10b400d0101c40d42050303c3e00301081d000c0d0300000a0140402c010000655000c0c0300b400d8800d40d00c0203a49800d07222204003000181140b11840034860402d0b4066004502850040c402c0c048900c40b000f049507601c400403a00780c0c0c0007500d0340388108001f074068882143c007041d00000100c1ca800c100000350850b50440704042c1c03802e0b5150b40243e40c1060700101c6090300035440b07549448004855102c015903542e0a5101c050203410b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 591098444 1250 591097194 591097229
    0x807050d020706021204060e030c0d0804030306081b0a0f06050936190b03032205030a030e12210d090213090215031902090a0b1605190c 60
    0x280381d04580c0d0060340031800b10748039019981c541003684422202290814544080d501d0080000826078134820840b4004116140440c603084901100103407040b0300303043d00c4040205e80c925060204820b40d4107014021501901404200030312451983d200d079100e104000424003400c0d81c050110307805007406880110403581e070300c88018101d40701c61101c07008280299484c8800d0f007c030600003901459041803012030f08204a4400c0007112440408150306078000c01c0344521281c9400c0002d403040200c50070407020300d90b035080030a0412030304407811400074400c00898419403801021540e210344c542d400a001082040c05101c0341400340360041d291811000c222446120580d0300044c2486174086c10319002a008030040d07002510652608a1107102c2d901d048018000601042c0c0e8440c001c0c19504040010070036080d40300039442403000a8001d29444c4020405803e00c6000b403035441201e645c2c602520106051950805a803040c00c41c03860030300303a5202d401088400c0407480580b4254000c81d2a40c0f00d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 591099694 1250 591098444 591098467
    0xc0a06021f02030c09010309051c020a1b0e040b1f06050c15090c010c0503040f03080c0c0d0809191505030f0a18020112140a1a010509060313020112060e01150f080705 73
    0x110ac3e8801140700412000c1c0585502d580402d034800307664802d07603800711820201c2e03000d092100214001c00654040000000d00462101d403030703041d04081c604c40007007240312041c80e6191803087c454010304040f0304005548805041c0c104034031001c100c1806500c40700390412410b056143c0080744d8205040008070f0703412805124062044900402d482111006072580d41d01c1e00d04203507042500840e429010700440b804d0581002c510040e41d141d0b024902038a0a03002c14200300342002e103080d1035494012035000208115514403612501041682c40700340c1c80785070190807001c1c4810020004106141400304241540544602e182c086660900381246211900040b0600038a185041c034a08411500117211544860750300c48055127408440420300c4000e81401500c940c030400c00c042d46c014508000068441c3d64207220010103a1052504032280150348510000756036841d007102c0000c0703500c0c1004100302c1030040c401070382d24040703803c000142e0000c40d00c01800704c0000a108601f400310009140d01c1c0301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 591100944 1250 591099694 591099703
    0x4020a0b030916090b210106080a08090306060d0507050103050703020c0d03090605160804140f0a03081e06220209030102180406090621050c0a06021f02030c0901030905 74
    0x401801151680341e103030820209644140940208583c0c0000890104014805020b1845d0340e41e80a800007a050a03041201e4074054118980300e10955a0f4542c00300710380506016602d0b580d4060b407209500d6240c101c00f0181880e038003401d01d6108864400b2545c0029074045a242c00712070007400e000a0542c0c410600382d001c2d09c40c0840b00c00c014010f401807401c0840e05a80302c006918001da0341040700350784101e9290000505c18152002286c1401c002a00158403043c540c0c03410100707101902c0740e00103280392140c40c2641c04807007140824420340810142c01802c0c0800c818007601200040c0380d90400c640800e41c03400080d02c1502c44d10340d800181c0d50b107290058044500d0440054021559501340c11400040d0144858945115500301070002400c0502c40c09248251031100d81f112403040c9000e20700001e00240c00e00d00320703140c0c011551000c1850fa46d00036400300a2550f030300a40702603400001901c58100e1840c50489510b407041c03060141c1803400034142d07071f0105028200020704081030f09002d85007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 591102194 1250 591100944 591100949
    0xb041d04021f08040312060605090d0f0b04150c0302030402060304080313150f06080a0c05010f14190201200d1a12010b01090b040b0a051b0604060b031e0a0b04020a 72
    0x410068181d00d640c696400f291040c030883c065500d420405491036100410307940c0030312441000807810702545100386080c6040315400d600c100f00c0680444c207a80d660303120003d42101d003514184003034400004000c0b40b07409800740032916454210b145103010b500289550001810207040000d0100004045030211a541c4212981000307070505901601028403024000d80c40140c0300071800d050b00022804800580e03000700035032100e5501c28039410300e401126440d603a043c08008100d07150741c40794540b0349480000d2071a00f00085042403011f003610006825240c98158618242500810039000b0b1101303c0c081d9144140010008220f10741c440000078401d0b40784801140d4450b03410b00b48110310034815404503908480a80754800d22680c0d0700d054041c0c80c0541d00c01d1040e070300003c000c802a40743c441c100414201c40141e4203008601484040e841ca040003c030703412102d00b5655000ca103035074038003000a0400e10002c3d000075100c9608112645441e02210f2100400803424280440c0c115600c03071014002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 591103444 1250 591102194 591102229
    0x1d130f150b010e010314040305031f060e0a0821030901200909090a080403110105071202010e0c12071202010c05030c150709081b0109080f030304020a0b041d0402 71
    0x20000c560640c00c0108040c00e41580801c2e143c11240c4500d501130700410203030000d0b003103001e400d60781c940e2401e940719800241181100c249049105660420a8004d0740c01340155a8400c40845030000a025035611a6004102c1c00e50040401a6000c0d5911581da03400d0943c60001c1078a0340c4806071968050201034603100c113901c81e034603440f5a03d103840402400440408890180c1d00e034850783d100c0e80d00c03524841800307030815004100910100d00080c1780c60980381c0041c03401d5464800c468690400310030200600d480181d4441201540d010000c00c001816054205d5201074040007c100c1150703a01098071483c00c1540c2180307249810341e0700403402c940c921034202d42034940e502524042941c0300c15151080354100783d040310110b403056200312010420386a1180007096410220800207601c95001d0310114108102c00d40c02041078101845810f040348101802151030b42010300c104031040c41180c100c1c003445001070100b0428030760b0050700c44180b40c003084012007003038986001041c19025405007014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 591104694 1250 591103444 591103463
    0x60103110c0a080c06011a0a2a0b0405060a11070f022709070905040c031b0b04081e03070b2206050c0d0b0a05100f02070f0b040f1d130f 60
    0x2c007409980700040a45030f151005807030031684c82d210102003042451150100c080c1050200e101b05900a04002c900540018280c0b040c1c2089100540f00700031a408040340c05849000a07c0304104c4c0412030304d50041c03003103070701407110601407003c108090140120107410003510224540a41d190900f4151901200c0c400400c240100c903141c00702c88180590742c0d038403a0701c218040040c0341401c038480d5600869210342e0702d0b01080e1a40d00c441c00c00c0c4c3c0400329210340681030b61000140d403510420050000300441fa0151070b0520b1a502d42e00c0f0801404040e914240d00200100d000027080d0b02c0e140f56000b6200180b10000d18611081d00d1544c001868008010b6403800003031001d803000c4a0094803450307800030801e006118005050005401d114450590840004c0850641c003038060f22a40c046600e10340b049a00311507407500e075010100c1070350380180c848050009060041f68200f09000c03000e0f0051101c1c40402420141c90412202402401c0071007541d8101417510801030601d2807003007060707001115038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 591105944 1250 591104694 591104713
    0xf1e030e0a03051215010e0d0602091e0319050706031d030a120f09120e0609090f010e090a050d2607020624180703141e0705030609060103110c 63
    0x606a0362010121100411602c00040c0c41404188040c07800d458061f950100241c1e18007040c400740b0048044101c9038a5000d0107880e980740c40b075200300304248600501d50070074030800800341070401410588100c60080000103c0303012503000100901207070a10314002548220b0b40300040700c08030303010b004000380340000a19a03c3c00c6a01001c03c4450b82d44a450030440e0030b034005850000c40300074039001030550b2106549040c04d24003c000304a428200a4071003450481c0c03200001d03000c2d078021109042240c50340b000601000048490603a0300c01400b100a11f09500c0301e445580d40d41203040d1400003048002c50240c42501490264400035607010b1280a085003401e5401139103420b0100d680080301101441e8158100503522848520000060900c8680101130740034150160b00040c07020003499192650b00c46800d684901041c0704688911349079013003641c40c50303180c8c4440d400a8103441c20400140300f03210099680b41c0f400c5401c0f00003401c2c001010504000040d1031801010344200290050004c1d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 591107194 1250 591105944 591105947
    0x30c09050702010507111902010219080706050c0c0a0611040506031503061f0b0d0905070b04060f020601030c050f0414010f030c090e0712060b04020a0e01030c0f1e030e0a03 76
    0x258001d04407900203000c1983e4120b400c441102e030160310045a64004080d41454204c01403d10325040e006106a40040e10780900ca601c40004110080ba41e40e00002510010f1084a100702500900c034021090300e804c40322618160f454191503405003070503a072120784c1c58203010000100c03402400040c1074a85c5920f4010500c01c040000042c009020303028050004103e01d5a400c240510921902420b0303070814104814000b440c0c01c1401e0f0038900590703421400011803400c102c050300410541d1071183d569030810000401e42c03c88411028155803240380103000062a00340341105588042d135502600360705000000b0050040303805e900c1c040644a80012500c1446000346009503400f0310b000584035695a28203078220b8100003049546a0041d0205008030450480c90602c60fa00502012a8080c04140010200d034800751070440440d400c4011014956018003031120b0010050808141d030183d1024090040458800d04c00c130f5071032180004c40f030130318041e1f8402d100c400c8519040f903481c0b800c6842d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 591108444 1250 591107194 591107201
    0x60d030921050d030f0b0108010f060e0303070204020d150b040819020616140d0507110409031403070c06061202030a03050f120c0903010509030c0a020609131503060b040b09130c030c09 81
    0x1542178094203051144c070481d40148113203030482d603008511140c2c01c0e1070691704960300c0e10942c05440d8180402c105050159850340080d044a10f2500c0b000951028000300000c2201210307848802240c4003440204101140031901191101c883c2140d81c000302030510016056205800080700d84000c1001d808052100b540c001080400e203030002c580300000503860a660601030301302c00030060080059400c07007a050580000354514442c1c186130841d0307800021000003d400c2141d001c1d0005603401450700510107540200401440007004c0b091032091690042901e850701150054103000000071000c4401d000c01d0102c60520741e0000003401941010b0310040c0c801ea005403401ca02c01e40c00c24002c16080c04010003121000c034021001080030600720350030300003190444618280d004001c402f445542034081d00505075603030288048011458218a0300b40115900311081038000c45c60891111420380300d800d0384d1a0001e4803041c2c10800c2c810300d403401040d060015040140b800c01200c0000406240c2500b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 591109694 1250 591108444 591108461
    0x402040b0d050705155512060506030417190509030c060901020607260f0702070905070c08071e05060a0e012007110303041706060d030921050d03 64
    0x981140a480800344100e03401c1c0a5104d802a0041e4442c0b00a85c0d0040f503000c0007502e00c41900604115600c05d02e00e640c034403500948441d05242865a44c0402c5554441d051107c2c00200a0f420880c0d83d0428004c6407060000400007400c1003040f018001e04c40110b00150b8030f1001d1405008000447c40070340003012504a080210700a114080e0350001c149015416120920810390091000b980c0307008084034038250710380720203100d202c000c02060098000002814801d200000840d0450f040201c0003e20b060582e034800c8510a14020610034001c0e440034040080a0b00b249465498102d0f5050810350f034410048004262002e4090040420902191861040481d542c1c20007006003a030000a00340e030903580200329004440211480391040402c09082e825001d58074000d8010783d8034001c01d245a01035002841301c882118892000d004041000940c0510306440d0b171000080680c0e8081c0200602c1c1c0207060846c8807a0150042aa404070030558286030000200c1750920f413072080150091a454 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 591110944 1250 591109694 591109699
    0xa0c031110061706010909121413230915010c0c080106260d020303010b0d0b0a0b03101a040501051e210703050601080606030603010e03030906010807050d050a02090402040b0d050705 80
    0x720002869007050b01c200d880042d0042c55208c25100d00c910100d174622140700004d01c1100c0d00780000b0310840d119402c014041c040f400448107581a008080c4e802222a0540c054441c44403001002103544d0f090f9010303000301d80300b82043c0810010a1502441c1900f054128004c03961a24100007000080209912840e696804612500b40c0c1c8104030310752150412001c40700507900400c010050074960030001c01d15550010000100c0c1d807501d000003411803031a6404400b0186002c8248035034000c0b802d00c0500103215014845c00102d000300e02c0301659006501c6842e040c46004030741c01250050384400f21840345016440351781d0756550050202c0850001408030714450000c600002c1c4418000c1c0710341801000c05840b9054035950b180c04018259100900b0250155200c1350480030f0b42100704041e40c0510a01005040d496041c842e00510741005030740b00510480b20b400040010410104a20082c40d030191076510403650b40b400400c0c054400903010b183c104980030500014080007052010985508 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 591112194 1250 591110944 591110953
    0xe0f0f01050f010f030305031b0705030315011409030601150507080a020a0c06030b1c060b18060f01170f0c0f0f120108061b0c12070308011a0a0c0311100617 69
    0x7111301041d1801440d000040214104001041c2d1020000204c3c001203003049500616102c2c1d15540c1c903003140c0042d200c1086080340025442583e6800603440441206e521100e10b0400da10311000a40e641018420b803600002200084071115204208540805030014006175a62460740f000950301d0241030342c02c0d40c0003d000000803c0c014400d0051408a800041c503028450700000750350f41f01245075200c00c80b01c150365661b86026584444000d0040c495428106468601e01001400510f8115180480c1005a00294881c42e054140e0350560403006151545050740e88508816120b4840c001000110a401107110000d004600b0002c0044a581e0a29140542d0f80d88841960f0344505850a40305010b6204201d4500c2d10b010001d011203001c11801c075a120b2441d01210a0a588403c00a0740081d01c91001400340303d060f44130b00e000d0828214003051402042c008001c03c103040007000107080241c1c05403c0c0307641240400105010300550f000800040ba0b881d00c018041c90009040b0039143d002c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 591113444 1250 591112194 591112199
    0x18010501290403031e110d090608010b0f0304080d06090908030a0c0201150b130f030f021509031c021e0f0d030b030d110a0c0b03060108060906010906030e0f0f01050f01 74
    0x41d1901a2001c90390300d6160700135074003108203a05180390203a140384d000300700b102e5030040108601041b0a00ba0490240c44426549041c04402000b540d8143c010008800f03040103103130081d44084048030340c09500200210f89804a0450038009040250300036040706007007000aa0034040140b0085000743c240030b60400c18410038050590903500d030b540070040c0c0802c044404100e01c418441c02080740c014a10502904291501d507001d415080581081d11002c0240c2040411410003089410009044403184d90134004224000303503403501041c901441700000369100c113440c18000c00048010031500b1364400107106020481650310480307208101220b02c2045203100006019210301049544050090100d8200b101070545a00034486d9405a00d40705041881d00450407000300740380a4100c2e6400c0030754a00f81b44c4001040c4c00f81c0038050390f00c1041a90280f09050380c0110820049030603504011407014000c5003103500300f5a8071001c030f0001d4005d03140522103c440661040b8402c070700c1000e1040c9581d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 591114694 1250 591113444 591113519
    0xa0c0c030206011701020d1503050f06040f061503050102221d01030209071e0504090506061c090602040b0a080603120408060f1009020c030c0606040e070b0318010501 73
    0x21810009005608000300602c1003015250340b155002c4100300026161111400c2d9a004844101c00600081c400307088052080040c14445c07240b203900c0e80b800400981c21f20343c83e031541c081c207120001000b00f40c0d0742c1c90010900011301c50040045820000071511394000c941c20024207181c5458885ca070349005140030400b03800c900c450b403a90440a401214550782590700b030009940016001b08188501035141110125845400b41ca0300c00c0381da42e031991514035181080c000d0f2207001d0941403007008240000c203500285400c542c41850354400d8041000c030f113030f070401c10000e03c02c84e004071020541c00907074010500e4104075030070301816059085a4030b1080c2101104594040ea01030408250007d4000c22a8451100c040035080108140184801aa50400b503422644108280d41440e040842d01c0314058005104042c1e12000c141c80900071401107404041e11240d030750080c030007807107404000b10b903007624120400080111004001c00c055615042c1c0c140401c0214423150490241100110303440c030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 591115944 1250 591114694 591114707
    0x114010f0b04050f040b2709070b09010309030c08032418060d060b030d09150918020a03061d0f01080f070302010e0609090403030e01060b04050d0b060a080102120a0c 73
    0x1c4001014103401c1a0801003049111441c1003021644141c40380c8044003556520040581850000d15216105a800e80c1c9810b40344c413002814a10150842907081205170320b0b000845000c04000d10b40040c1029251500791404004080007508000b000b04c00c0060001c07405c900080c0031101841005030310f4035014100700c070f1a00040004000180c00c000402d80034100120103046191089402103807260782c6202203890501e0202d050000215060010880c2c2c10a0300080070b1880800e182c28030701e040c24404d491146013544114102c841e68002941c69443d803103039009002416402505042103540c0c0c0c50440440841645c10403062040c01c1c00004a004c000503030380c0180c0d25010090541d03546150010354188102480d1560451400c01c50308501c1c0c2e480b080403030305c51031180e1000113004042d08500c0e42100c105400c5480d601104100511035175542c1e0010b1031000c1d520041d1030500b95101004203403000a1a03010807215800071412811444c000f500072481809003610820941c6130005d0116440c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 591117194 1250 591115944 591115949
    0xa110604082b050705031005040903020601061808030304050102092706101b050d020d0f022a0a0b091008040b130305090a030c0f08061905041505090114010f 69
    0x140d120400440b085024182c0c10041e84040e0402e92401005020064000791241228180009800002003142482202c2c0024001e400190ba08100ea031200b950003030350303508040c0114418098240c2c2001c59585800171043d000d4038904081c1ca4590502e441c000c0d0207500a202d8052050f802113450701c416040050380e0a240a42d00b1480c02c1007a1200001d010714040c0442c0e2003020005001c403c6041000003075a12500c05d0b216000425480c400010300a05103080c0c0b020704401c11245010000d411a40042c40102090200141494014800002020340700f12050160781210003500002000741303902014017510142550355191988403070304201c504000445004005031603402c042603031020051150318200d171090601c03030300d0003c880300010507415940d48112964948840c0601005c103001d42504020304500c002000c050900301c0700302c8040900300b00185985070b540c0c40040d0074000d2401c1e0820f006401c0800403c55418141c2080f40601400080c3c2d0b09160404800000d4023084a00d00204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 591118444 1250 591117194 591117203
    0xf0b03090d11011401320f010509040b09090303040b0f07050a0302131707091d0c090405071a09030c01092706090c08180a020108220b0c0a110604 64
    0xd0908180d0103a5010300c00c81020b119035940c4070303070562200030081040c5000c0c006214003000d0740726890404005401188003900b810000460507001c1c140c0700c003000c0f20320081c02400d0007500c4500300c00111380140040180359503c0003d59040c49003011000c4005d5000d103020b42d40410341c0d555190790010803c0420703609080021000c0000e13000c201e2003507014101a078480c4003031019156032400510f4080e10301d889482a560818a801c1201d0078030340c07059050038600303c3e5103200ca108042107501e8440151040e40340c004c600801c0020100b04051002101400c0f0003060400301c0319596948401541004500c01e009100b180041040b0398001d500c0c49084900403862280340610180c0000c64001050b004003888980342c04000c10180628000c54200d502103542c1c4079002d1916000c0c4c0403480c0341540704000c5030740002d0403900150340e10035403580e40041e0f240c0303203149020802910200f2003c01044003130080710600d81400f040d0302641c00188a07001c0107603111021040503010302a00d5000c140c800a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 591119694 1250 591118444 591118453
    0x20108040206030c1612030c030504080702100909050a0507091d0411060d02160201020607050f0301150e06030a140a0606050d1505190302012c01120204120b010f0b0309 74
    0x300185800c400071648000481c03485410180b010f034aa04e01c41505030403c039883c400c440a8804110f5040c03280c8200400603140c02c0c407603820581c80e40c4c0c4113481030041c084c1c01944c0c00d40280e03203550b004144102c014a2055020003030b82c60a08110f500504041d6404000108840400a00c0c0b00c40c003000c4a0341140c40110701c62454466a484101075071990a07240e41010080c8041d10351050310388003900322202041c403090302251840c80024100b003401420b03c002e001051001000c0151a40180e07815101d0450a6590100d013080040e91405814052294020707000010440c00d0320040c1c0103a50344410071000040c280d00c1e200381600076a0028001d90000410030300401d62800515044154225128404840e0880e01d0300d020850620400914880e204030441c401c20440d40d005020380c110003a510820b501e0700c41c3c2a0640c180f1951550126410011f2505c2c4200d40001a0780c11580103180307100c40c0d01600c9a06203401c8401410074484c41051400107080010b80d81040022613210302c04020140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 591120944 1250 591119694 591119701
    0x307051206070e150c03040f080703120305060103110c210c0c2205010602060f0a06050f0d03030b120c011b0203070e0a0906110403050c010212031915030f02100903020108 75
    0x1141c0c3c000d034205010b40c3c0f00d40282144070903080d41e84001c1018007500e0018582c2d079803d02280c0e9404407904c0d030000c80103510070781040010801030210200745001b0351074041481e886081c0100c1c041c011036001000b5140000030400c0b15148001116850200d00ba40940c0100f044018440100d028610f80e003546034019404000a80c501464040d520710105011040141c580109501c21503400341c1100000d40d2080d13051128818001c644664000f4110310180042c03400c1001080c20384103890b00e0300340500480c90704001014042e400c9094600d0f0301074072100803600d403008415641c17582c54100030302241c00000881411080307080c1d01240c2e950040c1c020075010307103011900d03c01900001e042c1d0714260755500a003400034036140940110000302c1c05c401031312541103091041c2810b17928180b00741550f200303086800b000751800081d65071095207005041c0f03c012001d41d1090280c110f4069880074111002004400c02488849002d019070080c0c41c00d0310a031141c81801e4642d2202c901019001c01c5000000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 591122194 1250 591120944 591120947
    0x210306040b010903060906020901080f04020a090c020316200604080604080702220b090603060412030e0109050a120810030b01140f1008010515041a0708090915030705120607 76
    0x1403941a4040c5030086203d40d60f0b4442c50202c1d00010783c12a403240d00011340e01419a4081c82e140c0c0c000030f040c10704081604007580024200c850074850052010748950b14800e00030b0082c410381c1d418140342d10003011071551524003e0000181c420010524020030032000011f41018400d039015601c0d9000101000d40322500c0319189900010380403030b84840003045900495081300d110102c07061401d180030494071080d20400920313103001030045000b5440103040001283d1211403110b00040181400141403803c074104a002d841c003000090254405c0072140c00030000c40141e054003e4055540724601510346c1100c1e0300120700d40388400360402c0340c88001400141724180318109100740c0100600d907c040204003045408401c00482030114000c80d004102d01c0c00d0084030b090110044403440d47c07a080c2022085245900c100390a104808008140c2200301306420048440d1000000d02c03940180ca000323605950142190b0301618000d00079890000b84609260030158014070400014003000e0b995040c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 591123444 1250 591122194 591122201
    0x21006030c09021e120a06090923030f0418060909050601060e01030204030c061d0f010f11030d05090d0f08010b070230032701020307030507211121030604 68
    0x4d0f141d007a0010340c3e03840d60242200c005001d446544406010149060304c0180c0880c2c035141d00600909080c030300048009548040d15041c0c58800d40b550f856201d58507010107107580100c0308000d83c010f10000780880d04100104a0000c0007c5110041c4005030721040b03048143c440041004002d42e1208006100c00c1d4004c0100300c0451006141c0142000d5813178682c1401c070400355020601080105802028600c04d8a41c601d03d140d0f42560800301072081d01d40020140140d80c00304400308080d0f0b155040c1d0101c1c080c4129118000000c2081c03002c1c0c14800030710b0341c56030240e00310b24011428500c10b040e0820b000c1c0d003086040b107054004080c10301256030240b241c490303c0320400c0c00c00c1e80104109204004080620b09465040950080d5122a092034460300d4200160750121202c10300010035420303a80e400000c0302c806a616241045c3c490f0a24a48081c03048010f5100e44004460030180b070610681c80100e40e41511045000c80d490500d40210900444800800c1407207060380800000d10103061030340 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 591124694 1250 591123444 591123457
    0x40e070305031222060207030e1f050906073008010f050f040216110a0e040f03050702131a040606030524030c03010614040518032703031207021006030c0902 69
    0x13a1060b500080d0303070840b2071840000e28403c480655010600c40149507116490101400040c0c6045815010f05080c480d40310a0b02185c03541000000254001c40c4d44884081d2a100d9501401c0a140e04103000f03103a240c078420200b1413101c48a02800e001f54201d1041001604031525270f01f009218900b40024022001c6d809141d094006400300000e250f00c480381010440c4841c005c0750901201042c2d0740030441c0b480802e50101100c1d1181d03806100c046519100f0600703801d9814180344e5a10000380c80820f41d080f885045107002c82d40303007545c0340e40d1040110381080803000003258100312070360f207496054045640550f6040d010052800501100d01d5000c02056038a01004044440311002e14000078290b443c2030b0803080407590b04004038219030415008854010b8070154070340104090008a1503540e004440c030210029420901c0c00d9214209080b212030785042c0a401c3e642c0e500140110110340027002c0d030305507005116031800c040c00c140c1940b1a0109981e40b219607001914507001c1900065080007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 591125944 1250 591124694 591124711
    0x210f0507111c110405070e060d02070f0c0e011e06021b0a08030a2f10090f0606080a0201090905060a18060803130e1303350a0b040e0703050312 63
    0x1c0115401d010006095030350306208200344003070301260f0b2003404282c07600a002001484040c050341c2285683e400c06880c404200d000005803221000d00304102640c250303550140c1107101c82000031a07680d00c4003644078140c560002c0c0340020144000754444a40d030080c407d03000180c2088450041c285107071280501d500c0b20052138600c035681c6451209055602042500002c0380110300550b07841000d04050240814404000e202500b125a003181e4075200031481c0c506609a03581250000c100c6440d01019a89401400c00c004203031322003000d41e80d1042c110300103a0115070401c00020f52030080b4003503140709080141601400c00d1804494901880e000ba5080d05656190000880c8500e01000944848a012140406003070300c1c090b00c0c403c4440000d8244c0301102c01d15002c140100b508a42c9121214040a169200c0b0a0480545071401c1e5013240d48162140341040c180400048103800500c1081002ca801f0400046000d0917650f40f20b8003480000c1c200d81040c0800e454003054030b2605603215861 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 591127194 1250 591125944 591125959
    0xc02130906090606080705150307051c0e2e0c020318030109062c0d1407140d120b0306040b07230a02010204060f02030903150a0f0504210f050711 64
    0x942d0700e100548204d07400c55a200e91101070300304000d140c8816030781d400c21000d002003450b500b82980010b00d07a06c201d5005004010641407140d0b241c001903444900143c642000303643d68034030010141c402010915405401504800c0d94480310814188030b0340c2d8040c05190000d518042d015030080e00c201014407402d95141d56100003031404545903014403140d56500c100907071080309200400f849180c80c605100092030340058413b0681c01d0300f004103000d00880c043d400e913407144440d1411645402901040d01800d003c2ca4034504501c5da005445020307400d16080301442412510814181e94180c129405000c9105110100b07100034012441c4400b0411020161504246d5801002d103141c2d04c04280752006039800a0104600e0b41e00c075160704803560552024601c0d110340d072800695600b92884070010110244000320742040f481c0e51150605008981090085203064108103030007280303000e00300d482070440807002214203100390030f00f131001283d41d01c03181d04190b9580c0303500c03204400080c0c103076070030548 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 591128444 1250 591127194 591127211
    0xe01030b060d0905060604140106080403080402042301030c05030a03020703080904020c030a2106030803060946020306060f07230313060258030b010c02130906 70
    0x10b40c041c141605002d98010803590400c00284422900e944d00030041d5000b0400040c00425440001981c00c203826142940803500c3c0d5000090042000324821620b018140d048120802e80044e00f0074103c2e4021017946100a5a410605840312413591000340182c20001051001030ba10f500508060040a000181409480140030f86982e004d1002072b400701c3c541100b10041d003130301940c8001c00441118000d000091840c0e86200190001500d16031142c025080007803081c0291090b802e0259185400300d480d40c030855418252201c0c00403881a00c00b10302d02c1011808404a40200d0b0702070807010b0985841c00c0680514640207402c41e000886251f0510500440d0340c1444603210b140154020025583c0d42c0c00590703031b20481800c40d6102e50199005a00d030349031145080700207007100810301c0085600004440c000000c404c0200d0740403030b640300c42c1484070119550745400c00c0c2c03000e10080e480030400044002e006495201d0242002507104c50400807440c0c2002242e040100403d20450f07000c103400a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 591129694 1250 591128444 591128467
    0x20f0405030106030c0e0a140c0309010e07171c081305030c030d060504150b0a0e121204030506130f020f041404060b1c1112120f09040c0f0e01030b06 66
    0x144a40d2054170704810099050000d41c021b4403003160017000c0b4500401011024084400b0400b81c02001204000400300000e00c140d8002c0d0041074560340c1c2c04d03040d1038069072503041c020b8003603209040142591141c09900300c180b2a2401e03040c0003c11507511000815034410301c01c1d205001c00c600c8112001d0000788011910713200100054260b0141844010a02d5800e10f0207000407240c810b02c04c4c5004a9840f281000307213603c01401c50300c405407240f0f011841c083c506804200d00620b4403c03500d400d44644a072000c521043c80018200380c074802c1c0c09a0b0000c1c0c8601045182100c1c041b5406003100401100000043c6403050380c0400c600400341c008541c003030455000c00e5150758100c805036100c0351110985001c81c9414840c1c00c1c01f0f54814804010b090140307848000b980d040140391179000d41c0c0070030700080101504100101c0b00c0100c1c00500c2da55242444d0180005801003009c46008a05118003001464090904446045890359034103940c0c2041c000114040c01203071002c241c001000300403124014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 591130944 1250 591129694 591129701
    0x13050d050f0601261f0b0402040e01030b07030e06330d12020d02070317070201020102090d0f0215030c030403030f1e0e0c0108040b01090b040225020a091e020f04050301 74
    0x3c000d21300c20728614a2908000748018080c0c40c1d0451459080100c48003014144244800406650300c41c002800c400d0785408540284141d1704008a41a0040b000208100400f0743c600e2040c86603035814030240700900d52840c0d5030b44c0e055801c05009924100f5252001c500c4c800801c82c42130381702c610805540200c2c4041002a4800703142a203e80e400c0034400c803c0390f0b804001003c020041403000300320743e40c82e6843d50790504181c8221440b40c41400210081568404d40558555100003002038807200100d03d00602c07001000c1100b240038550690b2a09928183c1c0d2003070781e11034003484110528641c2d0b143e404400400d244034a15038000e6907540e100c3d00540c8200c8025035103160115000440c40d00c0c819109250054101b12a0b0400044404120000e003203400441e04481d900307000404d45121100c00138000e8003902c0c0c29810042c04104150044d0a400c1401c650414029900d8403403580e280c54030701d03090300d0500c100d038444c10200325048040b43c50184d0042407002c000c5038445003005c3c1c882d0002400d5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 591132194 1250 591130944 591130949
    0x40f06050c010228020f0d02030901050702030a060617060603030a05070605131704090f09051e03070b160e01030506031903140a0203030906150904020d020402070204060905070f0513050d050f0601 86
    0x3d02c4040c12a038041c0f10380401c900c40d110046e0500410b100808014025aa0311036540450304204000c0392040c11524104401c074903460340400305108180d1107208001c4034040325011076400344205000f1540c58100442102c030740001503521646000c0c10381d160940680001781500c203000181140320008100341e41880030482110107151551a403134050043c060300d612200c95028146072403c9030000400001d490003000442c1c0c0003505504041c0e441c0c040c00c0d401410303000751800d0ba40f8801c0003031942d2480c0006030105040d441d442e030300c0c1c1c00c0c10b0b004604660b02141c5c81034055000140000c480f82000c000059400d120346030084000c0c0030920b805402d40c2020440d000507a2000c814040341d680d0034001e00d5804040e065441d2014480600000c42400b40580003038043c422224150042d0349994045035542d07038028000740000ca543e28040801084121240800104001c820008452054040303039032420054000918090401080144010b800402207540d4850803000e00681c07441803022070300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 591133444 1250 591132194 591132247
    0x609050f0f030a1b05031507080c040902030103030e0a090b01140d1d06010f120b01031203020c0115052b0204020903010b12070303180608130201051c0f0b0402040f06050c0102 77
    0x1c824107002d00d0901130f020990040ba100c0e801c586c02045650a8140345141d001e949442e00398040c3c0c80d500b1003404144255007021340da8030b000100100c24580c001032010303040d40082d5054540141c0c4d80d41d124040f00c00c5c1007890390004025001078211900c2e51806401c041126a00000d42460003040d0b03801c00107460003d07031b40d854102000400c02c0c800c0341c10311580140742c1c0300d18590743c0305201d42e601c01c488030050000402240c60b8050001189100e40d0554055004240007040b1202070341000480b601d401d4891980f15980d40e4541c58148050300c0020440100350040d607403843c200c15030070040a5007280f025507070599a00c0c20111213550722407803066450303041c442c05071475000e082d4240100b24580181145581d40600f820410105510550841d403040c002040380289010510040310144030784c44905088052545813800d151320140d105410080c200b030740800000b54100244810382c001c9100c0e07a1100100c2d10b408000351409a0010078081c00010f000614040020740c05040c41600301a0030070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 591134694 1250 591133444 591133463
    0x40902040e061008010e040f0609020a06050304060b06040503070b180d1202070b0306103e060a0903050702090c040b03011503360302010e0f0102130f0609050f0f030a 73
    0x502414694603401c200c50743c44c54040401d6042c11000442840003a000500c6090258000d0042c8045548110003566004081c00303a6980d03560700017400c60704207840565815107410520700c03031890400112001c0b1003004d400380c04514504904004a9004001c1d04c4c0345a21400c615032005544203c01c4d9081c4500c20041000040e6070311400929080082d003042c412084100306014007903544051055075006c461820301001a4042d454503140d40708529400602608443c400c01d52050010401401143c80c4044980541c0c994142e10243c502c0c40b00c000c0e000c44c0040260301c1c054207200b002c3d01e41c0a803000c101c00f072030300350384000d003c00d9503100742c1c030540c548118050071080690741802075101181424000a680e140c6529244140c0d0b6110b0f1403030b019124031110344d81d0402d4000c0d0440d00314000311506486c80c00c094410305901035800248005621071040f400480c2c2c2544800c0800280e85903a90b0b0ba90059082c00140100254000c541551040258403203549a07a0204604001d4901c189100c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 591135944 1250 591134694 591134701
    0xf07232206021603030c0f060b0310020a111516020f120304021509220908040e011401211e09050c01081003200d051b0a0e01080a1106040902040e 64
    0xf810700304140708408804403203076001c0001c01d5020030106e8000703410180c80380060101303103482001420841042c40c0c141c0288440381c010640543d0103014030320703181d484000800d005650300d680c0b60352004206440d070b42e000703401169035400008910086c404e0140111283d440044010700e10300f600d001c45480344000001f0130041141801080b989120301460703120307428010240700050251101c480c26614007c8503400800441c6256008032020a800c001c0c403d0791645c48034034054010000340228070326810040c43c07a48003075100d00405510a00601d0b036050030142401074401c080d0085540d001d6490381d140f0a01c0504e000b86204061400d0303c110018065111880000340441100410181c180c40d1804010000310700844415241c98090703600e001052070031480011200003003100060501c0c4642440c0401807610102e140b1800384003180c254130341d180d0300c6842c000340b250240190005a080401c419001502960162009440042c14107043c541c442a0031412a000343e8002c000c507806100a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 591137194 1250 591135944 591135947
    0xd05030d060618262508060105090915130b0717180304030b0604020403080415390501060e07030209150712051305060406030c02060f07232206 63
    0x140c00c00f818042081c030003c0c40c90329200756000340c942d03403c01c1e85401045070f000300302a105200005420706101c602a03141c200300c044801440720540580041132180c0c000100d10b52a0109031140319640e0b41c801040200115110320040f0070740a00403c42e2040390755000c0c0300248410408a2068917a1340d101c01c1d5101c2c00c0c003484103680c43d0280c007080c00c1c074408030b101d1718071004003004075070a503a00444503200580300c40002c10001c0c4030310ba10107480344d600400c011942d80061540c80172000d03110f56541d103641200c240710341700c928002c000c58201c40c8100c50030301d40d60f88004010400ca01d0701031400000c0580e44d500c0d0804007d08100d0b04000000d50000b061441c41c43e18a4208811340d01103c142c9007030038000d54800c1441401401c01c00700340000841d81000004008049001421016042544540ea24940900901544034025025014520014070b402e45108880361040da8a5030310b142158200311026410f015044044d090b20200420a80d060310009942c04100c1c40340c940b922401c19864141e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 591138444 1250 591137194 591137207
    0x12030f0a2606060a0f02030702040f0501050a140303041403010b090718171209150f040306060902070b0f150411040608010b180f010c1a0f0a0b031002090d05030d0606 73
    0x3003164032071240c10911045031520002d8409007052800d180c1c500d078914020a07855405400c500a40c49414100000c1c40150a50400d904a90040d104a10802d8131521211909120083e945405238018041003200300c200040c0709466480150000a44410346004a508281c00301c690002040700c201c00e032409000302010010083c40109074100403c9000350840340c031030b41b0107a02002d0405c00420b02c480560f4a081c40c00f4454010140240e03500c5013001d203219419046480140d4100e442e003040001c080076680201c07240c4c40c3e40400602156a100901542c2c81d038005044441c031418002c142c40015103c45c41112280d01c0403050881d02c1d01e00d03000e070003401d032030051700856203540090014003500d9000b5080031315000012105113520820b0800102c621000040018022048228213a0203007040c029405000d6a03a212041e900c87c0d840b08018815a014060402d4045d0b01c840d1212184c651294045e003824040200101034601e0161a00c91454002e03050001c90560707280020403401350002c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 591139694 1250 591138444 591138497
    0xd0b0a080f190311070e1b04030f03030f061503090204150317030408190503270d45050d0c03020909071809110a0e0612030f0a 56
    0x80c0201680752112040c65100c0010440410030604024a0101094040c6441280d0000164200c450b01917440242c1c02d00c020050b2850109034400300f02451000500b20111029240c0164559492200c6568110010500f081d00c1003030807543c0d13800100311800c200080301940041c665000c68507103464010402100c4004068075004044038908200040c400c2148480c4000b04004064907a619070070500f0300340c40742101802021092003030982c1c2c0b07d5001400b8602a0b01c1c10800500050000030b42081080c1800a8060495010120b8503590b5441005295121244015440b0052441e445c0054015054400941803401c01c2c401e090000c4147c4a8040c1c01000200d448030900c014545a90300042d0f001e000103401081b403070002072100380f4100000d20081c40e455165000e1032802031080c0000f0040c9142c11580c9179045061542c0d289458441c041c15181082c42c01da509885041c00c000b409180c0040d42d81c0307540014000c01a1504410001d09003e13121603c1d60711511030441203144400004a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 591140944 1250 591139694 591139709
    0x406090c1d1507060b180106020f0604051b0d0501020d141b031801140903220b030a0b011701030f0209070c0f02040506040b0a0b0703020106050105030c071101140d0b0a 74
    0x8031107207592942c400c00001030030828030340400c1d912501c600f0103401500400390303029000b8581d40313001c89007151002c070707964100c40c5a98291081c000505005644071541138070081c1890f0b02c401c1c42c9d45039206241c0050250244014035481190806580709400d83e0455185051041c0d612415121002c8061000caa40a100710404994030820082d0b0007050f404040c0002d1000b220901c40900c0803803003548014070329480455a054140303080c000095480d40010501d19441c2410200d008096070300302c07080c0098800d502034440c2141e440d0400f0000610381114050304002c2e0088045031070020350382103103029601074440482124101e0040c0038004c08090845410801e03291901404911180c903c80102c41e0f0446010505807103500000d0b000e0410412066800078516030001500c01e000e2000b40350b024031a4009001c480d6589005490764041140e00d000c080b00c0030000e80b400a0185c000810540704141400f058440c4c0175180c1ca100343d0409035029120660b260a007000134501a401c10b0000c0804 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 591142194 1250 591140944 591140987
    0x15040602090f01020d090312030603050313051302090306060d08040339060215100f0905090105013606090207081b0303010609091e09030804410c0406090c 68
    0x28180d004000900701d21018228641c230340c010281251080c0c21200c02503802c141180d403220010f5098a61620140c130801d885102860000714141c41c03036000b80d0f500460010003030030503035641c4810b20140082a40040f1040001004003100060340c01e084a07070541c0c9060041700d5400300c10240380080740c40c0c10121011041c00403404000302079000840810010744001d14031aa602c542c499540c145015410620780004005000b2821a01d20380c0000d2103200d0400007401141da031510700003a00980300e0924803152000544101800300100d032100844d8202c440b0001d402a603480400040781c00c101c0c8101c96444000805104120010805c0144207600001941c6076500d403100107001c5491500c01c0b00821070b21460620048207400f400882000f030104c0060082c400940340c0100b00c020125011111548808039404101e4030703e9241e5042d01118121004111044040d401110080e058030685a03106080c110500e03505e450003148000e24800b103020600780729101002d00340c0c090301513402d08210030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 591143444 1250 591142194 591142213
    0x6140f0106111b010e0a21230a020d0312060b030106020f01060608160908030a0507210e061b1006150c0512070804090212040c06021504020f0315040602090f0102 71
    0x3203180c0000310030300e401d08259040c2c58807800840c10340700e400e40c1f102c03800708814482c0000312404004903c8034544242e481000c0c401da441031084841c60b800b003540e03403503909c919107000050905003c0700d15a28002d0501d0305540310b50125820543d81190004d0303c0c6080040300410560ba01081400300c000d1414009000321350414200a0103554001c2002c00000c03c2c00b851200c00c41d002d01ca07840050304840c0c0980b6030360f00b1006d00141c61540305042c11641480d18200181d41e13071031a1130f44003001c00141d5550b207540c001030700d0030000190020702903900008031029100003104800c10002c03001081c822380102d5541d113400003601c6e02d207080c040f07502d05004d00882142c000500224015001040300030030b040d280e01440c02c04022030300481d000404032900c0095140b202c3d4440c0c5040500c01d0b07108603040c00d40d0319100c0004a880d0220481ca5100c604d2050003c02c00600c0c010700700c6503121801508030b503c4680c150880d400124400c0c0c2c0c0035156103a00003242c3c009424411a002101002030000303085414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 591144694 1250 591143444 591143473
    0x309050607080604060f0e060109050613061206080f0a0c060e060405040509010204050d05010e060a14061e030102130306050705040f06110313150f0819050406140f010611 75
    0x40c4000c0400081008041c000b4045a68507400040034080040c40d01ea0141c1c0c5a02140390581c10a407a0300b4042820400006480e1030071408540040c0403182e20100100c2c40c4c00000c0d034a0344000a11464103d46508001c594403604220748200d9603104001001d030410241400054041160404010130003500c0e0000c00a0f00c0e004100c0301140e0082d00c001403150b5072141624024011078200c1c643c000307000c0400605008054102407100d2280300c05a49660702c2c1d4403030000449006580c6502c08004c0000090403525105001c0300c00095080c000d28403028044000901320780c801d0a00c150150820541403040c040b90b8440c25a11a03910b04209150031f04252a52140054a11440c420040e0440c01a050080b0030700c00e40d56540a140e0044038446c0e01c942070755aa034202e40080d44006542400c40040a41c490035002e4014600b1805071380c2c0700c40010320001c002d484000d0042c3c41311034a50b0510300c4e4101c2520103292183c1c0462a00310119410114014200760305c2003105901c80d8002c82c01c403102d1f01d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 591145944 1250 591144694 591144703
    0x6090209030c060c0109050f0d08010f0e0c130302040c0320280306080307030f0237030c080d050f0a15050d03110f0304090b0619050a1403130201030c030905 69
    0x454080700c20740e807900903a01380d041c090103040f240244940200740900b84143d60000d0800070402c072230b44424080b40e0300c0d076130080340010407407140800040c0060041109089900c0080150080116814250075101d80124050301d41038555540001d60752080a4001004107040200e850a034480755440c01580c607007101d50090400c004e035100308160000c1820014080c0d8000e200038807030721055a032201442d0a0140104200340040c10143c011901c0310050080d11100c2d04c0400100620034413a403e44003040c82c030604c90303a10002c90601494904400200d260100a840310383c040f814086510300d0101d42a05040390301804c1804d00600340390900c0d00e023790401c0d81c10281e0f00c06844510041d00c0300c0c02c04842c1170416007030a08050060146980c0c95020100040064858602040c01140104800c0c44614462a103102c041405080c40d9003044501c60030080501c0e080354036280400c00514949000b856006540000b164004d6884110442d42c06026800528030241410080b400740c1da11025200e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 591147194 1250 591145944 591145963
    0x20601050a050114070b060a241e020a0305030903041703040f0b04060e0913060207031106060a0b0f0a0e10020304031205040819081b01091401020f0a0309050a02041406040609020903 80
    0x3106d01e1040055010f40ba9642c02c0c00051501605c80300c00802401502c40c98850281c0442d030010710950500741c00711501140c0003800c0e2000b0707401011100e00c640c03400c031083e42000e0200301103800200070000e405ca024692601858030140003440d6aa07150849034981c1300750170351010401d000140b00801403a40c015413502c10010040c2c0b82d141d020303682c0c810a050140c1028000401940c80480c0030703c10f266000001d6803c0c2c3c10481c0c2182c1c100d03202c4004000090b5001d110300350f01c00c00c0410003892041034010181c104c02d84141010362201c440c4100051090103181c07411401a0700104003041403012035500403d03525034a04080f07107000d06108140d525510451000041001d22080003400c0014030011a9018030391250100554186403101c240a402e401c903040d9100720509003016031420043c400c540400702070018251611800a07000e402411321010309031600d01a210f00000561594020300702e44003040d01c0d4400c094a40300c0c040100f194955003000161354418814954a61000950b4841 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 591148444 1250 591147194 591147203
    0x80c240a110909070e030706300e060903031005040c090506090d060e0a170a0504270f06061107030510020d06050d1a0a0203091c050c0d020601050a05011407 69
    0x241c8040001840d20948950440180c014000700100b28000340d014022078980142102550081079031030074100d491a5071840908001d03050a480d07015a415003102d40000c51024020105001d8400e045443c101401110341c400d039900000b007040b507100c24508030000904011501003203800321185004203841ca0500500c1d000d07210000b49282c03241e49404414499640c000d0043c45402d03010b8108070740304c032100714040310b20100940300d0782c40640c900819104990310b03581d00e40f0700b45407504d55920103809045c0e030030315030300d02c2e041e10345001c40012402050040403520001040013890300c44000c00a1640300558005500880c400340300146003c220490311055000000d626078680d400098000c101d60303445198420940c5128901b00802d04080180620301c8000380606e40d075032909443d050348021141048581c0040b50018142101d200704070303001c04180d01d045402d1400c846d070210329000b140007607000503910440c0104828907180d10014041c002c00e19258501c407017015000d400901070008000c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 591149694 1250 591148444 591148451
    0x6130305030a050c1e0408010b0303041206051003060c0f270603050c04080708060a0506180406090303020f0a0e12010207050c090a0b0306010902070c09050c090d02040b040603080c240a 81
    0x1c3d0301c2e420301c4d0107449801c950b0865220300004e0b2203480515581c000d2140011550030004042511b24010003650111891260104088285507036000c0050a00401002c0302c1c07000c0250101c0461210b11400515103040d840e000d07039045421401038141000424a5041c0740800c40700d0400c049000d1142d030049890500380415662108242441c981c00307160420b00c494410001d0004645100040c400d00480320b181c410030064484605000c0c0511140000040b448440710200e0000740300ba41c00184813900a150060904000500716603456220b110300000103a20421080250302c5e00d4900c1e45041c07a0004003c40c03400c1c2043d9503541c0c035102e05001c1136105403041e50029075440010b81003180b103100b00500396170031907842d201c8450003904821000c0ea02c2c40040140030407458168414a0701541d0340036030441c203080d511002c0148104c2080000c031780280c2c0713881c400030761900c8a0054101641c843c100f03554544000c0000145003000c0c154030302c2c0f0403841041c030700003e01c9000c024050f0011031040c80030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 591150944 1250 591149694 591149701
    0x2a2301020106051305010f0602010c09030311070b070605150102010209100c051c0f09060207050a0b0a0c0b0a0905120a0e1201060317040303231813090f0506130305030a05 75
    0x40c0e00410b842d80c0700581208402039000c005800369407100f07042e03a10442002c0001d50b00c0b810103c1c03c950941800802044040c9828070101e4001c0b0804861074550b60300b00c641080e03c1e00000d140ca1340001e02c04848035511401404a007a400502019003150203100071414001810000b8001c2d002004015043c02040e00c221401e2040920601d148401104045044c2e180340001c01080c11001007640e0001400e101030118100d84049508012030b000201581b82ca0f50400c8406001035100445d164180007400c8034460014103015506446008403000015031500103086c6107041c01007518041c01090b4041102c41145604071200045104d000e84849403411a120350680c010280e90304040c1c1144030100c6804c205960781d0000380140e0f40309036600d0040454440f810400001280344042c4001d40c1031140e0044104000c1080c80810001440c104010802c0c03480f90048030010941919400c0b0319483c4a0207008041001c1c94003c0e420980c641c1c0001c0c82514010040d00001e8207144005440c2c0d00071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 591152194 1250 591150944 591150947
    0xc080109090f05030f1e0910080a0e07080c01030b1c0b060d051006060e010804051020040b030f060607050d0c03091d07200a020f010314042a2301 64
    0x91070b0080d4014110fa41e07030741000002c0d80712a0044072000c4180140c1400084030307907004009803004154003400e146003c400d07170322084da80000010408075640341c0d1900c200e540f8440c00c000500c010400c0b00050700d20302c080c540004081e81c07a0900c00c075000b0034215200c0e840c010220300b0403601c000e030041c80c2071100e6200d07613000400c00b07030341610003070300c40e22a00700f92a0b0781004a41c00342003200c0c4103880c0c056400c2028001591001d01c11074014110380c0040e015101074041a401c1a110b520700041740c03b40007400000c0715201900540c200500e8940040100b107101c00241e01038941120084980c5410b14045a841590f1174070014001000c00002811100030540180c40c004c0250425a59401000c058000d010580c030004270340800c0081d000c0d101201d9010000c41d65a030b22114081c000d807040301440e8007032200e500e00a00707120b0b04260b580d0002e00c202e03200d1102001e00035441400e059031180d800b005a080d1201c02c46035040200154507108010f50b010320303424540441c80d03c10845d0751181c442e100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 591153444 1250 591152194 591152213
    0x1f0305070507050a02280306230613050622020c06090f030a051c0501060c1109070903110a0f0b03102301031d0304090b01030e0a020a0b03180724030c08010909 70
    0xa001c99030502080101c10002250080004c0d05000a0440d000180c1540c0000b00f103003041e40e4143d0044004bc7d6000405507071900540e0340f04c90040c00d04110b5000c280380b44440d07140b0510b074910f4096400f2800d001c015206004480d044000f2700018074006280d082c2064a03449120a81e02c00c1c0440000c9154400076807440c00c010301c00258004001c0756a4460018180317004950301210100030450840c1414900b03140b4050241a8030b0f41c52a6038142555108003003a444103814517445081741600080342110002c0c050060300441000c10b40301c1c1000f00000e1407540541c0c0100d150b20380c00980c07c855181c0100766007100c01c1c00c24603002ca84120b048240d0320780c1c1c1c070b0000303002042800001000b040442150b0419001444282c1c0c04014044264407150345a4006c0c050083d804412188100003249041001c0c1d43c00080041139920000c2d459014185081d085130b0204000e030385c0600344000707250b40c40c01e2103440421141c1400d12803414030810003085a40140510f15506075500301840500c44281c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 591154694 1250 591153444 591153499
    0x30724020c0a14040b011806030218090412021911040f14040309300204021c0c020601061e02122113060e0307080d02181f0305070507050a02 62
    0x14503000b111500d4007940c0c2c604180502c00c80c0c0c002c0303007018a04010355100700c03503107000c031481e442403500c01d42d0401008070040c2d4040d15120019100000740d1309119a101003070b00d8000d900c24803102503100c600406c040d0414080641f40b0007115041100e441c0800d2044a10414442003202c001642c402c040c810071008204010300402c0300d030348101c1003004040d0010380400c103a032a07900b2144084801d4408100c0440d03002c1c41c000c0002050315014100500301354000d0009212030300c11990138000303c18401421119440b56800040c0d00c0803004002440c0c100e08442c1500ca00300003080c0071184180b802a5694824459550304020009003d14148030420001c0c40d00c034a001d98041500d00306262018403109c8031640a58235249850a81c80b0210703000000c856009030300148807404e100c02441c01100a40103003900700c401c000c0300300c5600c5060351200c6000b11035481c020300000c402d0700e50b164003d0807184018005024032034204070301000b080c80040d5036031400b82d04035405204050500701404040c40071030b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 591155944 1250 591154694 591154699
    0x8040318091a04050c07020f0f12030310060e09010e0601080703200c010b040207050a080d0609020301080a11121f0b061c14010605030103021c02120a020f030724020c 73
    0x52103100082c40c400c800c040d1810300440d000d0219444003081820075220340300d002076102030078440e64003407810711800c0c078924050300810086007088480c1c040d03404c540c4225540c07503081e1401901800070a4009409079009a816030740354802d981007100010f0b101c0c9020341100d05108140002510052080c1c10011420f805c5440b000351080e448407140c0c0a070f401000042c0c2c00781d4241415001103003454405d0314400313900038008120011098403440000d034009206010125194840401c034a4902c0c0001d40c000c02840b001071911410f1400d0401261916170f6500c0d1196401030503286081d20300042040c40d298000b0021010740300055807002c0140044500340d41c04c0100800c4035444191184808561071100d88000d001540800302000c912840034010500440c01c10300c014400f50400c1d070035105a01c550807d211461000302d4000500080000ba440c80481d8081c402c2602141050005030103c2d4100780c00400d00342c0d00f0051041e0000c50001030001007001c020207450a84d07442003101e0720042802 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 591157194 1250 591155944 591155951
    0x207140f0714030d0806150c010c0c140a020a140a050d0b1b040b0d0c020a060501030c05030d020c0916180303180b0a17060402090a0b0901020706020d0804031809 71
    0x240c2956854110500c201818804190055a028140030075050300c41c0c0200d6a411245548600400c030440c0001905a42441018800301c40305010074898009003240e151115000700440d8074103066441440016500c0070b41080302da000c0141c5403400401c040d01c041d4568080340d0710485022803940b50031903202c00e90060603200c45505000b01a80000e003d20300320303000e02c0b00c01503100c2c0d170700300c27040c840c0c1e00c142000070108002d64400d0210a0740031902e00b41c0f151041e14011344241d154402a12030a8100b9901c080010324100030515040008074203e240c9400944500041000012200c00004002e212216401e1305441002841403001040308003080130f141c4031203612420010601c0400d8400001c240c0710b01c0f03002145000e210b4056584402043d910b03003801c0000b80400703034141c007c040c05054016400303000307211451781d410399140c01400503005066100c0001400081c6000680e502000c25500904440c00c0d040340d01084903a0302035010300780f90040b49a40001803014250f16440304030014038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 591158444 1250 591157194 591157213
    0x60a1e020318010b0307031205030711011a100201060609120501090506041208060f0d060f06211104060609151e050d050c04050102070905090307080a090f090209060a03020714 77
    0x540544510701110040013000344811181c203040d80c400c050300011700140301e100ca48000e5980301d04000c5a12050516142c0c548071600101a820f54007810001d18540d02c0d0944d10a00905215918003000d03141c1e07100a000c164601070001c0c048078030318040d800d14100900340800a2000940001200a604c00211001464181003282c0817a07040003040c0000b40c09207020601502d00606d00e05000c400007041128008503650314070b801842d9078000107001580f586000140c0c41e00e00444000135842c0145001c00003203003494060b0602c8120010f1601c00c0d85810401e0011303c1e4030041010507144541341300406008075000603a00d14141d181c810740f003401808008280c990b44a009052000d503444020301c401c0c0ca0340110103000c1e020320700400b03005034020340040180c404150002a04450624152890100e140d11216841c0e4008000e40c0e010400350882081000803031100c8000800b501281103041c044040b000036050700c0303028082d03030415070003143c1a8140490542c040c90b40c50440012912007a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 591159694 1250 591158444 591158461
    0xc3f09140a08031009020a0e010f0c050d0509030609060f13030302130f090f09082d070f0c0806070c03050a051c06090e010b0307090e0a0506010e0115020a05060a1e0203 74
    0x180104c0701039030300e4004003200040600c20741c0250344404a050f00d44040910740c01d00111003003080d11140781c04002d000302000300802c00a0016a02c0c00090b0f40e1565078625a0400f818501400503122055944c855020003d44140303410f54a600300f003030410b0500c1c4803113050604070064014808030004c0d03603001c6240000d920b02500e03504c20480380e1801080c848184c03ca6224001c031044801c002c2d040040410071160b2500100500300c007000c820402c041100e03070240f0f80403c1e03160403a01d001c4411a600009078003d110702d0580203801400b44100511940c600640014080000d41c14000d041c4040410400c803202c1c0a28195140003000c5d1074200c0c61a410524000c0241040d4800c26101c60300d03001802881d07640c18069107508002c0903006007000781c500b0010030001c200d10010402c1d240500c02c03880b0002002801000d00038400c0d0055060594108003010b04a0682c1c000040195403003121100000ba401050481d442255418002249021420001c02c019034940340c41e0f42d040d200008201008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 591160944 1250 591159694 591159697
    0x1e0a0201020913021305010305060402160501050708090f0c01052a0709110405090c0d0209100e100e0d030f0908010204030c0305070e040c0b0903010f0c3f09140a08 72
    0x40300d04441000c030512800610f002248240b2114003180c2c12442020f125550007034000d60b42000c8043c000603d00f0440443c801d080046824089540d81d44900030320155a5001d50215041800c480280102240a07840166103070311300751185051101c0030490142450780c1c0d40b0000101440d1406000282d100c14030180d45a038410702036000f07000d01d001380310b00c448004841941c060340ca02500d010740310740b20009101e0b296003040c640c0d010115001c100140550300e4044241881074040d444d01487d540b15030041091080500e03105408001c0800f007038141c180c3e01c01c0b1491907e00c0d0507060480c070070300000c102100c0c5071105d900b1a8040c0d60001500004000340018850708490062041d00c20903601d41c0303c580c130418415134025200600a000a00c2164100c2d8001c003200382000300009000c03445044500e041d50f01c04036012001c100c0c02c002094042c410f1310805a00341c3c00071000c61007a1006103c0d0b680098580c0120b4190b0301d1ba0300c0c007030b0008010307402c000d880c0004074501c03c07101c0000c034502d01410b9a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 591162194 1250 591160944 591160957
    0x1401050315130c082a07110a0b0a0513092a0309140703030806030105010f0e22060e011404150908040f0f06020706021903030b19060e1206040209010b1e0a020102 71
    0xc04912018501017898911918050715501e0418604541c0b525400400101c030740255501418403e4001640c1d1804030007450029070b5900c0346d948518640303900c4640d803c42d551044911500f08014100c0041d61040c41102546000600c42007490141804400030b0151100082600005080200201200140c2c0000320380c0303c2c2d0303150300c82607454405260030388200307120303900303444420710703414004204800d440d168000e0b24040c820041e4495003500030350580758000e0a0b03485980e5803612204c2c6141c00c0c050700104904100c03403606030b0708040da20b020883e42e1042c22031282941e1900d081d0f007000842e90403035005110741c100020180d502d070040c41d500c0d4440c0d4440e00001d81b140307610000d1031324004070302c00c003490088610f01c107107251150702c09a02510980d80c2c015403200440d02c010301c0d50203100b400100036066540d00c104078030b40c1c03113002d000340b610081c0480b4200ba40580c0c204001641c2d0030f00214191155140c4a641740d00c42c03240f2221400303c861403500f02c1c940b4003185800300564154094203a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 591163444 1250 591162194 591162211
    0xb181003050a150e0a0504051005250c170a170a0e071203021510030f050f0115300b0108060906061002031603050c03070b0f011401050315130c08 64
    0x2032000001c0c420f0440b94014410243c0d0301d20305500090100c240d80d0b000f154045d0180c8241d441c00e2814540d5601182d50840d200801c83c0d14840c0b1600100c13080b10841d0005805178107050b00620550b49418010034803194400343c46075400112544050701c01c1c0300d040e100221394116078440c4d007071840861014001d50b1724000300a2080c1d500000b9007108800d5484c1d02c681e050380142802c8100c41c0840f001d040340042450101181c104000070000303501c07030401c002c801d00401c0900f40300f0507040b0016007551030300c064110f0081c50761001401046510450040402102e001c00c0c10050b8400703000611101d200032004d0141070b00b1300e000050781e440103e0010310620141080da40156142010072080e034105da2610f0380185d2080c0301034201c6042c15401c0c0d00415000b41086410065498100c91456110020032a144041282070029103261107914034090560790461502690722400003c0c05408001c005400342e49010400411546645c80302001d0075612440501107074100e1040580280b4054500c40c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 591164694 1250 591163444 591163451
    0x4060605041a030f1801090209090615042304060f11031e0f0103120c020916110102160813050d080702011107030203071401050f0c010b01090e100b181003050a 70
    0x2141180244100c921424011500007180e8844681640c41c01000d04059210303591f031840d041026a84000700c051149500400401540ca017502013010f02d014600001c40c0203504000080d40356010b00300380311400300840104403440e540d95040c410023030031854107180c5441740383c041210320a81e000d00045108031409078035420070b03a8421982101010b000c4520bc4180d040321303801440003c0020342e80c812140c1a0340f60120300308a8a030006110f500e82502d001d5000603403251a800301c2500b101c045261010201c0c021810710701c0800c09260100c3d030070305c402050f0072000501012049a80340800001c0c02001c0e0109400403590318280c020b0750311410040c1d000ca9549150108407000024024064907809000352592510b0985003020006800960b20f0501c00c080c017181c0151410080030b40302144091001013030b0070800b88005007082c1d00e20341003041e8424642040010541e88180d410040354492456141d03200300c40e10405034140c1c03240040d03903800b0311000300c03042c14640d140c0c205038003034840141d007003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 591165944 1250 591164694 591164729
    0x90c050a0608010e0402042a020706110321060d120f080c090f01082e030209090601061d0f09040c030c050d0309090c1b0c0312080601050702041a0406060504 69
    0x340c5540c10301340b0959280034000e400107801410a070300310038104088003c000060356500180c098a20246c425040c0040c1c2c07090804000c45948009100b42212250703024510744003010b8008041090b82c0007211044c40c005001052480c1c407102c420108158001540d0014048081c400074101000c200301c2c100000d01001c082122280510101c80034028003c00c20403108041070019034181c100100600c81040d0991824201c01d50030f10b4680015000e82640c86440b02d003988108031401c0c0380039285224550042c00103206041c1c000d4005155204401c5604804030045000268144a107010305908a007640c4140400c1080d5000118103603071044d407207100e26980710024032040c140d0043c03018000810841c0104120b008640c0842032038001403074400e001d02e0b038000c10500d0181c2009001c4500c402d01031003c005009850039050711390764841c98080d100382001d4000034000e000f0700c0d601038420380d03441100760303458042509a038641c2000a0021700c511642c8880240441c1c00030301c10084600b4165461 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 591167194 1250 591165944 591165947
    0x3070b01091b0e060913020d060905040c140a03120824010e011206080613050606030a02090103120c0b011e0506040f0b07080f04260114061e04090c050a06 68
    0x30401c1121910071402c2c450300d0004011120308000c2644035810900400c5103940c0c0c1d468003036a200300420310610140c2e503507500f848204100c9245900510445143c48184000101c988032100c045501040078070800704c03012800101001420384c4024048800b800002e600542c1080c8507903c941c1c20826800007117001010030010b00301c041c410441c001200354200000c65030280461200f11030741c3c00340004600b91140d011900e81082035a080061040c91041c07101001000c202c0240c1c4808150054144444540c0c08a407203070006000c000c040781b50300818090418071501034400f4890700682c540b20359594403083c501400c04001040f200b0184000340119445c2042800c480c2200c600c034050748c107000d150803406820b41d000000308030380c0035001f00041913101d507444001c6c1c0085c003210400310200d0f50b2540700d00184000700c5100102e0076410080c00420070011618011345c808025030703543c8089001200d00080e22400c0380c0303130580d101d403a040060b0705000c030030054142074510640c2c0980500303864180 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 591168444 1250 591167194 591167201
    0x804091425120e070f0306051f150809030c01050403080714040b0f07050a080d2c0a120e040905030901110708030f0708210a060f1d10150203070b0109 66
    0x55580030521800100c503490806a1003c2c0b8101444015a10402d03158008040400a25441558100d40b00e200344038200c4039203c0c01444140b10703054644446498851081c2e0a109105d5102c400c1c4000360b0001214041c1c2030044460000030480204101d1805140160880001755181c400080200f100b50301e55940701d00869003078902c002007040c180b98900082613074551201c801286d540c022401c508002885003006403030030074111000401e03c0e0314240220110407920301c002e030009003c240b1600403001800f04041000035008a500e05074640c602c071003031354181d414050054000d4036109500c401e1141c040041c01410800b41d0314000303000f400c280d0b00c1d55200003500954095820800c0056100c40c14007000701101071055401a007001c04083d01e0b011102111ba9030350b20010200010002c0c411164030a503009410788603512503029081280b17460340c00c0751740b0b610200d018600d900400c00b05010034000400410100050020343c043c2403900a4494110001c2103e901e01e20740004940281c00c7d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 591169694 1250 591168444 591168511
    0xd140103060b060f0d1814011e090b06040b0423160206071d150c0f01060503120f0c01020d06030807050d14030703021305060c0a0c0e0c0f0708040914 66
    0x50146040c8291100c010008003903041b12172440c02446141440083d000e6030909600c4419840001101c80f02065a06c21403080f00382120340386850901c2c600300282c48480380b20340041040d54001051220130010400400c412020030130380031a002507440350050301d032448030320854405094426100040e40f051baa01c00f42541d0480c045903101e0546054224444104408148001d001c14100c2c40b801100c03150b294000f4610041c44e40044200c01c0682509005400042000b540101005522018651107a010f050308420008600250098881d802501070300c10100040d401000f50940ea4540500c95074009142203a150081c58190000180180d00b04050b03884808a06031540c2d49a95044000350302240000c3c041c0036090314040303425199a07003c0c0201000300c9009140c600b0302d6051070081810389505c00030310324029070104100305145600341c403c000e180003601510f4040301e15111216010301c0e040302c0500d600d0441042680b045003d40640154003002c001110842c481500c40078031039043c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 591170944 1250 591169694 591169717
    0xd0b060c07031e08040e01080d2c030705060a020120030f070e060705152e060509030a0803190e0d021b0109080f0a060c1d090403050d140103060b06 65
    0x30081040840d0020107250f00403210310901c4048003030560782d40709503174120390040281d034400b060050150307007001c11100141c90703110301307040d4007240d0074440c0318003003001e03400100e8062961018080c8090f00d08002090190400504c50380c5c4a00e003041d0300034006c210380c540008c80b03518108896001041c4860499019540c20726402c03000c4c2c1c1c1d8004050715800b100c02c8000b42c02c820108404804144141300340402e40e2a042c42c9590181000329042440074142600364098042500c031006406400c0750303d030802c0b69101e0401a4580036104000307810f100280c0c001402c80b100001c10032440580007500c101c203641901500b00300d140144004a6960f20f869162440981c0c8007588441d900305100100c040701038030514208034a10741b900142400c20303103078510030900303a0310100585c0308210090140c00742c0b00030355280c411410440641361140030700c00f02c00701e00d01a190740c00105043c10b205508864451880200a00c800325110080000c0034200344070503901360f450401c4000f0a032a003c8111602546203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 591172194 1250 591170944 591170953
    0x2030c071d010b19031a0d0b010510020705010c0b09010608060a09020a0e07020c042406020307020a140a0e070516120f08010b040504020315030d050406033813020c030d0b060c 77
    0x71500c158014a0400d802c00c4080c6d16404400120b43d5039401880c020310320510300b102a551508080c4250051000144130030b64002c40c1e024889640d028050444154210225176007039124401c0c0349006040320b420603401800364030304204504521390400c0807118401e6407002c0d44550364400c066120340084d180c0c000141c000a061030a986460f0300049800901003602c4060701115aa0a0221100b5640500c0c050380012400f942940f80825035079000b44401c2075618018204000010304e294a1409000401d81808020444080c801c6003910381e1102e40002640c01c3d030145041900d503000304800c076000010820480f41c2c4450f840b4103d418101d07503081d40319904150070300b810003021350070003441115842e0003019110f26590301000040008a038070745030107541c0c0c2d0a041b0000c1c01e179180c0d05048200484040400c842d260914032a0424481c0c155052040b0040700c1c80016155580701d461a042d0705001094800c10080040010021400300010401024441a0a2001c2401002000400341e0007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 591173444 1250 591172194 591172237
    0x51c021b0708163011091006030b04020f07030c0809041a091501082e06050301150309020319030c0b040b09100605030a0204090f06020301080705010e06270102030c071d010b 76
    0xa4204c00f41000620420702000120a4000400e4004001300d42606625201503c100440ca80520230401c6401c016a030940c98400d014480a116204850b4000c00b00182540903e05106070304080c1d0380383d240014402e00910340400c1e80100c4040c1d404030078502c42c010203404280081d9150310740c10784c0d80310b060712030520b00d60720180c039111950000d0101a08140000a0401c602c8441c42d08a0001c1d103200e03143d580e00c0b5410450321010840b001e2210300e091500d031480c00030240e500011941070740c41c2c030b00a184c50900001e00d001c890302e41c86c1030704c02040701a41304244000c000c0c0410200e40704042d0802202c1e01c00945102d40015100d16110b05a010340102c8043d10150926422880030301d4001d0803c60450049542d540d0220b900c01da0156041d40c1026800b8000340d82d001d810810302c40403c0f034003039042c5001c041120b810cd0010140c02600c00050b421720030070302d900900986201c58640d00c242e03026190303241860403142d4a40b09065440d801c0c104004a52011400107030b55038442c0054130002c4400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 591174694 1250 591173444 591173519
    0x70e0603130c150e030a050304091107140a03020d02122719030c05060a050d0c11030d02031006080c030c09041d0c010807051c021b070816 61
    0x610241046449001c1d200038200800d0704045104001c204102c90b031000000c40f04402054049501e43c00c501c0703500310321154401b15400100ba60f00307036041420001002d484040307107101c05e403003004001804010800051a03200e01c0c00700b4403200d454081e409452012031a604101e1f1618442d40901114400031b016054042c0103420b40c801d09210900c0c4620705d0802d000b00043e40d505816039000d400b0a210a4090040120241582c001803c0545145003072a50402d80a4164024440320032011584c0329000c2c0f80c0e00c4d2141d001c20710050100c4095a503181e20f04048d40b0081d60007260450310f4030056802c006103a07407041c5040d0b440b89802402583c25900e44400c6030106500c00e80b4200e6005031605260807544403066651a81000413400900005000c03000141c0010300042142041c00400e200e10010301031554201d002c3c10b95000303401a642c0910700304a0403130f001c4151002001d881030f004e0214400c0c0c000523000704003031920700f403086200b0b590340c1d60135440540080042108440c0155100c0000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 591175944 1250 591174694 591174697
    0xa0b0313050712060615080123040f06140a06140a02071d0a0e07030c060c080706051017060c09010e06090d03081f032604080607050702040b030105070e06 68
    0x4050440c1180c08912940c490038a000d02d40d030446060328000302c04182c10004940b041300001c00c01406d40f00c040351110075016200c044144102400044007092011070078404102207080d800000744100710304030b09004080c0003404940202d00408070044071a11103454002c24500c115403c59032981c44480e2030310301c0c05125030400884907040d4410444003241c100050300181a01e0a1200110005490480240e0054841d0044002c1c844e40080e0018008204071a0414054a05a042c03101900c5660700e8140180e1080031381c0075102d1445c001c2030002c004040007c134001c4806441e55100f8000d991400640c0399002581c1124000c2010409a5199401882000011140145070034109007201020a01006040c4011000202c1c040c0030802c100b108060300c90034081c40040ca0b030840504561b1a84610148480140c1901c00d90856504021403600101c4028110f14810740320b0508080c00003821603008600102c0c8a02c3c1003402c100d52038141407044610503c9103650b03c10017203002c01c0510005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 591177194 1250 591175944 591175951
    0x1c0618021b0703050105101d1812030408121e04020f0a030b1302100203070506011809140102040303030f0b0f12030c01240524090117040303020702010e0a050a0b03 72
    0x101d4418800380300714000240090b800660203480041403602d89000000c05404140e00849008144100948a02ca04150440740d10882a54400c04000306030200e06151000c0b602c000d103081000041003000704036081c005000c1c484140d809c0301d100c0c0e4444a5001c070711000101880b002e4103264800050151030010706d11400c1140c0039148080c0c203600e94803500b4500004941040c00b0003c040c42440444c00c2401c100090040244082c508160541c3d450307640b5801c0600c1900c49809004c29940b80c500341c180c3c06151415480001c412a050b444003144d4081e40107444141c000c40d1034600340c2e42c00c60546010300180ca500042c40c920410300202c1c1007142d0b10700c441d0345c05e1140b40f00c24403188400010910408000085a0380b1807400f05183d4408042d0388261900028003c1080300e02c0c0d201603c0e1045203089002507040f240d5a11441c4e041d004954941600c0d030030130365101000e03080c0700c00d01d41c041e8020b2402c28001ea8829085403c0e24083c020819058440e40d5048922000b04006120340040078640 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 591178444 1250 591177194 591177217
    0x80c03010c11030d020a1707030221071d031c0906030c0201020a05071506030b090c03100c05070b07110307030e10030c1407030c02030304090221040b041410060b1c061802 75
    0x1400c100790034481e047e6040c121256400300340e002a0703c041d9648004548850740c2c002410500c0c044c038003c04002c000e403184141e00c15602418040c8221a0b175810311060f4034000b020103900c0c1b40c900700003200401c420b509201fa240440d187c407885074215403041c001c4a07000442516006d00d000c0450361200f455081c1010040826913031601c0200020701a6420180118807040081c14284010020541403484c80c540040440380340403901e21380b4940140540716074030742006200300e503030303032410360598217610100d9011801d0f000001d00041015007100c41c51a64403001d4410036401c5440c12020b130101d90142d03040f0703c041243c451a558804052000522465100c0d1514622801c083d134007003803031900240c00a070301294001c603141152003501c4100c0354441003101602043d40c1000c2c0c58402c20000098005021298a902004441101085078000011030960304000082d40c0c0c001066071034124107034400081c1c0213864202000b9172a400388109a0300c024907000c02d40798a072201000258443e50192a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 591179694 1250 591178444 591178457
    0xc0d14010507020c040c02060613110c06040507091d1203092104030204140415020307050f13030c05031623100201140a0603030c02090718080c03010c11030d020a 71
    0xa01a20080c00380714080c10b1280c000f4148070141004110580d0400c0f40c1030004c55100b1800c12889030f86056480d04114121540050040c0801074552501d1040011903042445010244820004c00003001000c0303450881042000c00d41264030b000440d650324010418951145031300345c0c6c0071407015008503042aa80400c55401c15903041d0141030350311200e2402e003003020700800c0800544c02c0a000c0c40e511014104511800340c9802e41d6804125103c020030090038503408000594524058403c4070031003540c40107107948541c24080440030510345404105d031310007000900000e05040004013400c03940c2c03c0203010000e20741414400301d0340070010804003c03910350100340ea41e070700d4503050540c2000c01200c0c1e0001c560403090b08404142d003007002d0070380d8440500e401420030202e548181c00312069941110740080360380b20010f04840c01060741e5200000301326070900003da404d6000030a1420310406070024081451203540a949909070756841c2d0005410802402c500d4440c240d004008281d910b04010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 591180944 1250 591179694 591179723
    0x40810052e051003020310050402030c071e021e03120f090d08040e040b010e010f0b09010509010e03010f02090f031504080c10050705210c1b0a0803091c0309050c0d 72
    0x10f20b4041000c0303403034000310741d002060000c42c9002c0c81301c1501074403040d98150301c2c50400180101e03803031041d01c0c0c01500b9a414008000f51052815090100050b00100090b41d207103038452825000e400003003081d5100303200d2101c501543c00010401c0d50310700950200b05a051003402c00c2409008103511000312014a010040070426106801c4100d000c0d0303000d0b0b09515415030526805020386081038004c0d4048000c00301c002c01c2400b0034102110489502840d08540f03900074100140c800151b85482c4641c503501f4002200c01d101e440d03901600743d03020200c0b81e07941e003500f680041c0f40d296045541110400349a110001d004508610010002c0032294000c079041c6040300c80c121012030303c3c00c0d81e0200000b000000e4002061807a0301008103110103102c070f48883c600384010300c40e0707041c07280060706400510b0f20b1072041101b910a02c0300c409074039003269101d9030b0f03807030031000160311291051a03002d0080c2c6101002d0400501c80d01c03032242c0d020ba1113801816a41e90650401510786074808040311040344a0780301 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 591182194 1250 591180944 591180949
    0x150910050c160302011116090b0d060e0105061305010506071e060504031823130e16050109080d021207020406031b080601090b0603040f08130605040810052e05 70
    0x40b0a140c440580c0010032421840010045820b981140c24654080140560a0740f901d104072402c0f520039010010b034080d0507801058880302003250241201d4605404416407510641106100d503030b080b184032001c12851400a41110420301501da00110309004d605d0004040e1a940080701c0c031040140d40600b0350726600c80054450072142200061122981005806170710040d11015201d580802ca50310703949142100d00c1c0003103002c0031900c9140001c4403200c480165900290b0b4080101068a40d40703001180b44a1a00e00f161007040e00180035408001303810741d004a40c911116001344d000d0400c55030f600d4440500f036040b00310180d1380a96070701c800000089072590001d4181e4484d0f0b0700e014401d03290030119824800164064900b175801c0904055681d65060101c9074019440b001c0c4080d0300045082c428528055071900b801440d003a020049102341e0400081d1084841c1c1c2402c0760114441084202c041d941c0699070300d5500003403810a82008a04120845940706c0461900701030107a88000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 591183444 1250 591182194 591182203
    0x22802030f03090a11010314070e010e04020a17010503011e09021f080f0c0c070501050d140c07113c1c02030105060a05090705030c19120b150910050c 66
    0x407050144ea000c16800710030456104d03500e50040109080402131500030010b680c4213000000e0544003000700c00040d1007030310380c01401280c40041e40984115150541c0100203400d26201d07214014181c6854000041c0a15050049104041c3c80240f05101c1c1b6100c4a00d00c0040e049500c400c0b1390002030810180c00080d41c0c0e030075000702d44140c0d540300c002d10b0a041c503080c207201c0c1e0b028005540e2680208a0071800364000240c0c401100d400f031030300e1303503581d601da43c6440020300409030500008036440040c05485051343d0054141079001300c04044018503d2402c10080462045200401640e46280140c0c05c500008544030300c1413040c0004101d940001e0000b07010381c50340010320866004001000b10a60600340304a6503c46015919400e4807800c00d000503243c60001414081040030010000e0760083e19602640d14480070704900c81c01505103400041d1000e4201ca002003141840e007494804c99252607203000250318101c65501d880c0040b07400500a964994601440c1804410400040503520400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 591184694 1250 591183444 591183451
    0x709030605220b101a210f06010e121903090603020705120a11101a1e06030c0c070e071706010e12070308031e0c121611060f07080703022802030f03 65
    0x220010740d01c0480d840051b420b614a8048070309510848400c0001d646140d11015410503001d0070680700d010300000005540303407400601800300340600d02c2566405100114090fa06a04c41d8603480c0d00303d81c881108500320f01a2500180141d40b0000003580240c0c664001400389411500c0c04c15071020418440d0380c54100402981040d1554860348102d10b07042144040c80200400c4030302245000f0300fa0b803034004400d031101c40ca520038000040850424400d1008440818840b4000d4070f000035940d5040c12000300b030441794080891100d902c461030440320b000140c0c0c445c0fa0140c6441c0155498441405410521840f190b281441042c001001244a04024501c100319820303c84400496000440341c152002402c10030300d000b0240042c0c480e51040744255503201140700c00101201501d0042115901d20f0040a071901c4d002d00d005000041013101f884c18429030590f1a4941c0039220050100d00f01c0c880c00e01e90301c070922882040c107881d10401c80c0e004201c0b44080d104680c00e20401104499a80d402034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 591185944 1250 591184694 591184739
    0x24020f1b0904021323150612130f030924080f100f0806060411040e01060804020319030c05061501020d050c0f0102210a1401050609180709030605220b10 67
    0x70300212101c004090540d035401404441c5209141d46c0c0d134070100341c55010b1210040c0181010300300203200c0c0210155204580c681101c5601c41030040e60801800d001030760f0003642c03030b54030781c009040c51808401a0545010304460380c0f0644556200c15451410942c06040d808086220000005102c917400300300001070034065001e0803190400c8410001200c1c000641d007100c403d02030000b0001d0040b0791504604440301420000390940d100d20000c0e0402c42050a07815041d40a403021409040d40100505101c43c811011070b0711031b8a42c490000b19841d44900009d006070b00c840304c41c500c0140306001400b1007510b00030840d100a060020340509a13007090507030070500301d40c403a4044080d02a503041507400010a141c10015016403c1c14582078000500070750307000300030005044800fa110040380920756607441c2014001401c3c00407008211030314a12003035401a0030007010072000c154030b042c03070018107169950510384100701d542e0b1701c140190020703d199019880e0074400124a0901042c055041005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 591187050 1106 591185944 591185981
    0x6042102120a080403080912030112021207035c19090b0103050c12041b0303030903080c090307030b1024020f1b09040213 54
    0xc512682060440090b4400500341d11441e118001e0b4032030703503c0414030340301c44c4040395982516405103c000d100400040085908130f4200c1020184003400700c05425000d0003095040c8180390340180c41e1002d1172013003401c50304100c03500a90362007655030f80841c081c5150f8a4042c80c140c0b519408820841d11850484400c8034100c40699409400412035a00031200180b01d80c3c00c1c00562260314540360410440103d01e40c042e000304c51155a00329201802d0042c03001a0745025480030b4406e8071100e80d0880003102501041e184c50028601075240424220190310f002010400014103e40018505204460140d0303000324400c411242c000c5103000b400d8440a01c44050302005a001c20703810807000d40115005030b02d800442151004c0b507003d41e5251b00702c0020035500c1d034a155070403107040c0b0400c1c02d04000700d1074080310642e0085e001030300040d03c608081d442e6508982c00f5001e0706c81c91842 = true := by decide +kernel

theorem cover : BRFrame.Cov 591007194 591187050 := by
  have h0 := BRFrame.cov_init 591007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 591007194 ≤ n) (h2 : n < 591187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
