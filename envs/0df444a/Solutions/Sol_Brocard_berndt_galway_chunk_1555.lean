-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1555
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:33:18.613557+00:00
-- url     : https://prove2.me/submissions/c6121c5c-5bc4-4f87-8b79-dc35e58ffaf8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 279496402 ≤ n < 279676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 279497652 1250 279496402 279496421
    0xb1306090b0a060806060411030a0504030306170a061a091807090c0507120302130b0903120426030c0d0e040e0601030308100f05010e01030f11160c120f0b07020a020301 74
    0x40c003041041c1006244d900d041801030000f48290300305101c51013640d00c000216a0000084071002c83c042c1d84d60b003000d40c0984555400301002c1100740c0030040da4103078040348401c0e84520568040c020451180b5403210b009904c1c402a179400300e004008108400940074059005403c0c00003a54441da55840142c0215040c107407210020880c001002c1003000810340c180e04000744241400c6080040d04101114001058003440b44800d8000440100a54040298580c1e1103603190034a50f5664842d40002c411410403003003001290100c5a04c440c100e007022098a82c08500303000104034581c400b840880e443e212660250750081d40d15440154000e5003402294081d5020f5108c00c0e03103d040c04880d20445402d96444006100c801f11018040b6070f038803591b00d01c0d9520342440c01003002051001000000c01a00c0c181d0360035000001040b8410b07090196006410f98046c00740c04072502d80e90b002c0f0712450b411411006110160140c005d10001d199259002d07002841c5104884010300f0a0303020900f19441c0c4035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 279498902 1250 279497652 279497671
    0x90204060504090b0907080105150403060213080d03090b0606160c03080a082802030705090901081014061f0215040507091802100813020a030b0604180b1306090b 71
    0xd0910040c241d034042c0e034808203c01c3e80c900718540341000c001065460107024240c81900c281041c15003031890001039400ce0354102d04110364540c905402425454094401c00c01207001d0f004c8500744040c0a40700c2c0081c015040700c008040e42c0e03918420820194400c0342d860307010a01c602c90720700100704d40100810245115848050762411f84c5d14000d00600b00042c40394620381564000c490100101c949151082c2d4400e0710056141e0301c401c8015550350041044058100001c2c1c0300000d565100001c48244010008104000a10460b52013103850001100d49540090600f1180203404d9400d8041d0302d07000141c0e20682d900381041812001603000c3c180c0d41610198054a0184000010341c480d0780441c0d20700d101584802480c96011850390b5003032402610502c0b48602c001400c00100700400b040e000c0d4020a841c4880d40c0b00d152018409006580043c0190b01e00b01030301da030850341c41d0b00966000760080410308403692031640c803c100642c41481210082e4403410b0a0000961142006018070200b5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 279500152 1250 279498902 279498907
    0xe0a0902040b030f070b0904290405010801290406050a1d2203030c091802030115020706020a0807061508030315150d05180d0207380a090902040605 65
    0x500400c81074803101940306100f80c001600b0904d020b0000110300089501400240340c4804810340050010804149580410702c4081010240c44280c14000086400200d03010050b41e62503070050b500302e4003c510120086440114018080e001701085020405001403001c02c0840c0c640b000705001b40c03c0c1d94040ca4030071108080040007c4100d140d056403001d4a00c40ca010600340300c180840036881c014030302400b0b040d5111300382d0965600ca100f10102500c181000d0f2214039500814041c0203601c00d1042010442c1310104102906201081400c1120802d030700618003802c0c2500c031803419a00481003121880c2ea1111361003215281c1407800c00003051644080d545038540900600188000b4140b40d030710500c90380c0442c408030015481a15840302010304005007c1e40ea08070380701044005e041c1100400e01c280340b08150711944c0060710780103480c4241d85c0300308920707080100d5a2484501400052444c0268a4400760450340c0c00003600d0310342024903185083c0c0d40c0c0c0b61050070482e442a004000000e200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 279501402 1250 279500152 279500171
    0x30c21011b030e010903050a03020c070824090f0d0822030c0b070311031b070512042405040308030a020918060f220203040203031225081504150e0a 65
    0x502c42c00c1403d20400c0024040c204280d0b0b002810341c0f20300c4448106150b0b0104061013640402c01181c005094800708503000c1e00c10b01a04180b183c16a29065100e1240140008054200205480d204e03680e03007000070042c840506c0002c1d507078108018414064120a9514203e0300440c609465002a029480d203c5a110460500350020200100b0440c14035017050b0750488129071072802c496200405070801413007000c1c2099a103101344240c07280903000c0d114050f111514084003c0080007203641c000c03401c2510703480011031f00070b028226a851001044042c8402c0011030051001560701490780000145810300030b40c0000c1c27424074000c030f04211442d40d000400c00c990a05460b20786080000f11290b016000444040c0403040c2240d02403030201d41d4012002c101107407010416541500c240f0b03044074200d481c00441c007800900340c01c00c100c8190101071520004180c0030b400d1050040a01c1c00c2c50015480c00b140c00e00000c2d122880c8440c032850354401000402000103c1602e024404005021034038519 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 279502652 1250 279501402 279501407
    0x3090e0106020d08060111120d050609010f080d0507020d050604030306062a0206070302010b1f0e01030b01020a0204052205011d070605030112031202040b09030f010209030c21011b 79
    0x5030400301c1035511040180d01030301d030050313000b03035200b10246406240c169160240b03500303056441c0f08844d441c6001103030b028540710b610f800c00380c842c400a81e0850141c0c2e03641c44002410001601c41c00405400804c0e0340041c0c1d03440740c0010251507001900c0c8003051030159640328035100040343d068000a56610b414481503501465503c074a070510342c84044000c00417801400d845804030340083c420b440016072001058001e4002840822004000e0200303506c110700b500d01d01517124040c020007d4103040e43c14641d0360180c031a0340c1200d0010380c000c100c410701a5003800000c00001d08426a04921841104480980441c0303495141d4404c000219070003198003c039070b01d0914034141c00703881500075080510000c0c2d44501624119002010444007520381030030141c44070340c0c0004108234000d000003404134000003604000c090401040d0116055030012803025800c030b0149a842c55030503042390340d041910786000c001e11071100d600486c40e145000d40c800a01c1d401c6440c2e002080e4039200e40901c20229003034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 279503902 1250 279502652 279502679
    0xc091512090c090705041e0503030703090303020d1b080703020a06050a0c080c040302180a060f03030e030d11030a030e0c0d0303050603100905150a091703010906050f03060c0306060d090309 83
    0x2d509860f1000c55060440015015020b0703401110102001072060b031010307101d0000201e00070700b00903054958480207401c000340003441500083d4007600c10041c1e0705c60000e00c107001d00ca441100150340c80c4113001865907040031603841030384142c00b14400c102203c80400c0051040a000b04600100040c0160b021b44016040301d10040251070007200510040001d40c603154008444e071541c122640101c0d0780d0305d66826001b400150401d40700c0d504035450220415800155844d4a20002c5003140e050a8190300e042714001002144507030f103900700303210b00c1c00c00b28069000741010404007001c0e030302d80443e0140070904500103014246e002175202d5042c01118101807002c6c1c000000500b0007441031117080d03100d09690385040101e09168401100001700c07203a68a82c031034220650710521707104030404d0001d030b50311b6030b50803e000b5841c5041c60604000303400c0c0b52002c0114481103019000c2c1400356100d030b0f841000b1f41c0000301100e40241c4200700d45003e24405106101e000c0e03100c1e449003801d079401c0c65201071024 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 279505152 1250 279503902 279503923
    0xa02210d090510180f03080a03050901020a0c15090215120f07090e27060105010905010e0a090504021f0203070b060103180b0601140d0501090e0a0b0c09151209 70
    0x140740c40500503619604030342c3c61503464a0902d8018406404005420721403030343e10400005c801104003008009203140148400c03082503509001645034074401e24200e115015550700456040f041d05400507a1030052074524004642c000109442c42e40c0200d0301140345044080d00c1500005181040c0d0080040e80d290480c007070940701e00712407030494005005070040340103184c030400400380003c140000b030500304000070a01029036110b19901d0640240d4a00d420300801d404a8501d1401180340e510845942500c3c540041c0020b0045150852036002424080c100b81d80016016040d1100021005441c0150098030750003940d8540c090300f040c0c8000f01c0041c0c401410142445521010326445203110352049800c1b100c0c807901034582c2c00060b80e203800c41100c100d60300c1e0808114114035034841d50086040b2120003200341714600c4004c030119101c50420314010014507400300403403622500c24018244100c005011030038503030158015100c464100c0703004001d010f4400020800d03141400d00484815 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 279506402 1250 279505152 279505157
    0x3030509030f0a03050d02090604031e050601081f0b15160605010603050c0403020105031305060a0608060903041d070201060513020901390f0f0326060f120a02210d 72
    0x103c2140e5074010114400c0048007810700750086042c80c8241e40e20021100110b50160204e6092031000c00010100d220644040e6002d004810000650000108040395250302074503191207407032840700e103001c003d1915000440c4c200503611103500b200c0071144001c0c1022a0324120303e401c0c10240f40340640a40744140c0216080505000c240820300b9007840c1650b00360b9909080c40e544070f82d20200362060706101e0ba00b024005100b079000348042d2401e5544140c05030f036013800c1034a02964504680765502d1096105103190b180180c210b0320980c6200b50a001e130454018030012520a50b108001034494012000c91541b0503800281240f0072744c1c0160f01c95101070081c0030303440d003008681045400c00864214010302d01d0b5139911010801c100300702440071055031340440c0a262010043c18000d06200c60624044004c281d41504d0240c0102d40d11861440745100814000d11082c0210501480105420100c180d0307124190348000180d0715915003d03050904101c4020a044c0400003481c5040d2201449a05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 279507652 1250 279506402 279506413
    0x309020306250507201c0605103c090509010f1b020d0e180406060501031103040f170d0e1f0e0c060702060403020a06050d050709060206060904081303030509030f 71
    0x1d90403041c4045c0990300e81d1040c0d07445a0f90200443c51002d40c5100403000b4424040300d07503041140c5548600d01030381c15041000410b607114607020300503d13480b805c04808070003500705c8501c4034110213821485102407001c0c4400d0541c0e0ba40b08e002c05a4200f660506040d0b5103e1344503411700701d8180b0480c44900000c1d400024001e2003400d004c0d440302840c00815003004940e02404200d80c40b6241c0c0489109031014000405140c18108280102902d00501740040c0c10050302820b00720081d000d42e0f020342e410072003904034589503580e4070340a4521680a24482c00090042440c00341940c411501d0750388201d009010000341c0ea0840105d24820420203044040c030340b1080c0000c00e400096000501442510a1a0307100090b000007506402144d02c000e521450410340410320b00d9000300503080004038107005000036103d02e101901c03030118a000d100d0042c0e2041d80003681d24900f04c101c0c1500980540101868043d01100108050300c0a400980100324000343c80c9046040c01c10251024000b007801414 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 279508902 1250 279507652 279507667
    0x70303030b1f1d030304030309030c1d2208040801090b06091b0f0f03070c140c010503040b060112110405031002030127060e01180b03010b01050d020a03090203062505 73
    0x740034502e044140010480032401401428007000c0002010410050499441d00d5603440e0082c03103013906000441c0c401e68100b90001e10300031206440010120818070b1130b488c95482004041e6049003052025440c82501d6011201142030a00180090480e880000c9103071003071802e1002d0174100241c01c060003803030140b0030001654031621401509031416425580c0c0c82e2a5602e034040207019007106030f2000d80c0d001040c810170a800134a808205841001c900001e52191368041d40c6408c1446100c90104108000080010340b2910b5681e5010310141003958954001c3d03203400040358900e40d0164088030000400f4041ca240820650700281056801585958140339441440085608000c43c0e04002e002d0034015414950300520094000b164491006695402701080082c60400c242000c1c540b400315078200c00c0c00d040c0030350f4042c00010b03140e00303250840f002c103440004c3d070000c4074007404c140d550840c02005903018400207004101d00000341d81041c2490381108201c040c4880ea080074400c0401c41c0c0c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 279510152 1250 279508902 279508939
    0x316230c0303031f0b030a0c02120909071b0b01090606121a010e03030f0d0b1005180609030705030709020c0706090e07050d0e0d0201090b1e0c2a070303030b 69
    0x69038000006004000418130100050000140e96007203400400800300410418460a038013840c0103190301c1d4220707003a03000145542c0600340328212010b500820a140016030340c1e801001c072001e040c11401c0c0404175415081c1c07241c82075040c003a04a00212a2a5202004043d500150441d034101e5207400800011150b0080b00840305582400103040c0000300b4520b400c640e90a10580e40b1404080d004965690001d2100d50000c0a07401e504601c160100e83c2c2404c0704a1080c4140c580a050102c0f1040c2c03c0b02e01d41c0700b0850305420002860350300d40b1034840007080304d440920021000344144040980c0b01c140b107007282e9007440c074503030041000c2003c080300270420761003807607a4a0303044142e82c24099903d0400d040600094820314440f8010352007400d0201030215815448111360700c1c09107400303038a00c0e110101d800e41d200d9a103008105c2c1922a40003c60041611040140b07190504900e007001007602e4100a112040078000c80d161040d04030341c80400507d41c0501607591000c0382220f18169900150302c3c030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 279511402 1250 279510152 279510157
    0x501090314040e1504090803040b1611060601030509010e0a061a0d051e03270405150a0b0f07020301060303080123010c030509010201060b0d09050f01060b1b0316230c0303 75
    0x8191450018130340580c9a5210380c2e100c4000c080c3c110441c0b680d00e01c4c1600b01405c3c815000d0398000801c071108605042464401d20502d10170b044000094441f540310b80b4011005031402806108980d543c504010400580821200140b94800e2101007200c580030030511046c841d0310340c3c415010b01002c000306400181e01141301c060384142110700320040b000e4002524698012030b04102e00d900036007000619a2844401850182c0f5000c079001d0007a0b540e1141081948810550a140c21000504090001c011000060110700e007040d20311a090031010b400080c01d4601590054011601c1d0320010b0010b41c8404100d004200b00e25504007240d40c111000080c03051000c0304001d420000003142138042c60b8400c0d00100020300080d6035458648000080a00003001d840404036880d128507806060000010300480f401c681c5c1c0301558030700b84050200c2901240b9840140785510f40001c00425501406040d00c000d24940a200300300c50710360315507a02644c0010072000b5403c0f250310000c40c11501c0d0380c0000c01c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 279512652 1250 279511402 279511411
    0xa020a0207030f0c15030204082b0c050f070b04180902130509031b060601120e07050d0503041707210f020f0103020405030f0a03030522061808070501090314040e 71
    0x2e54800d441034034200026072125a170840f800d107506149030808120b81c1074018005541c2c45030180d0300006596071036450390a440c58130609c5c00c0340d42203014044050007008130003150b0303001d03200352120408102d00d01c0781058081e03081000c860001180502440c4d42d0360828034080810030004114410041d000610070b5084c001600300001e440e40700144000c001032090b0351840d54203110f240398803103100c020292909412280784d0f00007100d00710440c182c9105400b8070020b01e8042c1d4090070003641002c1c2131020440c4c0c0f801c01a222880100302c00240d01591903202d90112003044050f0000318180340020410f0100415800c090103c440c1840000c528415001c0c12055411a003015070000440c0058001c0c0c0903960001da8503010340700400d0b080880210789044100c0c0b10f40d408014650f10955003100010014401c1444c4512400317420380000c486034030508000080414104011105a07a101400e40c03281400f00c0e9aa5110142d42e0300b01500080b000d00840100c90042d4102410680b404002e4100140b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 279513902 1250 279512652 279512663
    0x60f0c0f0f04030f0308010e1b031305010b0d0f0201230a030f06080106091d0604030503160309080406051207050c12030c1303050319030b010503060d1a16080a020a020703 75
    0x6000310880c070941d01180d0003140e000d050005406190300303015100080903c20401c035075801900180e0040441c120a681c541503420361541940c4400403890706e4180103010071165990f03035195400075a0764500440303c049224a034401e0f07480601c2c1c40018080b10081c00580c40ba0354201d180c3c4100e142e00c0354242e40104859140004900c52a1240071019210940c4130020a51800c100411462480d400809110050b47c481594020200c00c00302d90328401205c02800165050002c0303500c0f11041c1a254070a0040c038540441e00007000d4076424440c0e4082c0e071054001c0382002442d92013000c514049607074801d410341449400c0801450140ea150029501c01c0da6144130008000b403d4420085c0650306904050b5414286a42c1c4914025550754024440c01d801e40c0300200f8003102c901d00c20b0060400242041c3d40300b5046807200d0061181c10307000240d0803601082010714a0080c00c0250b0205441003106045104d4803000f80f50010307000c5170740a07007143c0e0218010010450015000200d84003141d5005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 279515152 1250 279513902 279513907
    0x130812090f0601120b0a1d030c0111030106090b070827040f11030a0c0221090a080109150c020114070e0a080610210609030504051507020f04020d0e0a060608060f0c0f 73
    0x41031140001c4c1000c00241c5007030b201c81d000108031031f50000090942110301c41e0007004510350000100c4954003003441003600240c090f24052000d400071201400495202c5c0c40d400d402c101c02001c04000421036203100d0b114002151020b02a0b91900340200c140c454212802001a400c2c80d116050f030a01c00103100d4a04aa101c50510070168400c0284004200003040c41d41d0101ea102e08802c0003680c02039885502c40d49455001284c020010b10501d04140e034404041d4001081c0d280c1200083d002041010055540e1b07101303158404140c0f0a21980314864a6031582800c020f600100401c0342d949801c030607801c0e171100c000c0110051780302d21081e040d107555942104900060446501000200080040042e1308154001c1c00305904030001c1c0083d620100c560003000349000c00c0c0788080340681040694811541c0ca4119214207143d4020b0034a030703480810200c5e0508054181c249040f800c00001c84140d0f9441c0380410100409210180d04041c010f401c2d05042c3c00d00c0e0f41500d206000e85a41c012050900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 279516402 1250 279515152 279515161
    0x303050a11070e07080f01210c120b06040609020c0312152d0d030c0303050702030d0e0705040507020c101805120f010501050a05060d05130812090f0601120b 69
    0x1460108118203458000c455101d0f403960f024104000081e1205004508a500458080c8000b080100d0607140002c400040506d0041e00000084c580c030401611404026034001c40c107a50710282001c0114024004440da604054041c0000c0701c02d90b41c07140000383e1040c0946900345101004848640d0030300110500642c0707039a0940090702004076411948034420380d0550350104091000703046e282001e2184402c1011200080c4000342001180c0180001c0304840c150000902030342c059a005515403048a05090318000d17803e0407035140500780300c4140d000700c4040000c0e1034240035403a40070305280702502c9100070384000724101c07002c07000885080c4014500800c4d00700c00002c0381d40004080052204115440300320ba500e8440304c618824554650a0000101d1035040c4150321004403107026160702d2a00c00d0141c507034001004090000451400156855004102c03160040c10980798640402c08040c20040c170910300e4034201005070081070704410010050182e9102006e490a50800f01e5100550344 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 279517652 1250 279516402 279516407
    0x3030509011119030e1c08150a0b09030f01020702090f1306020a0306080f0a08030109020906070f03090501090603050412030f020d0c090f05010c050712050703170d060b130303050a 79
    0xc0c0142c60100900c001c610075040d844802082408002c40361410072010804581079034648210040c180015101c00d0624096140b090240702d503c4444218010440c500c0d900c00a000021a613000718141000411080020b2034240b0218000c140380100862504200740d001c00d203a03a400802c079458100041380040c60f006544a82601c2541d4040e000f159200d003030030f0b00640100034501503140a07209265242d540e071079001400c0c0341550b4000f40c404d800c42c3c1c603101c10b820181d44143c0b08280c000700c05101d10340010f0396242c0c0003003c00c1c1c071a458401d00c0600304800140300640b5503104008060a11091102003549031001907c041c44c149030119030707a02c40141d03000191241080400d601445d1413410700c1c100b940300000f04180c038403070f490042e115a59000111a41d00003520060302a0300546410816009000110041103104000380d891141d517944414a510a0a0280028100c400149100b00007032602c120400741c10311000b01402c01c01210708180c000042e9000c0281480300000e0b45804160 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 279518902 1250 279517652 279517661
    0x6090e150d030c0821010501110c060903011113080f0303071407020f0d0c03060b0f01090e04020d0c0306060503010b0604060507060b040b0301020c070801110a0c03051608030109020c160609030303050901 89
    0x113400403d0540d035092042e900407100c00d41442c1740081041601c00100751907100e07010071180d402c114001080d60810000c1048a0340c4c2c4506035a5905650380e002c0d240607000c809020303002212090380e442c815941350126650901c500101c0d41d40050b0070410030012083d80000c1c00511078900209503640b074420a101048007140d09809460780980c41c40301d0042000441032200e81681d124100500c0503880010511a000348541000ca000c60b044036014044402c01c0c95103994000d0008084492274200d549500580f0001600143d4002e070700d605050107241404d015103020a24140d41003460546031020042207402400340041041761240700c0301e61281c0c0c80d0307040006a1100100210b5507926030b0050301e136542485102d422483e508082d501c4400c404048251105e034042d03074440b880c60040a80c4c04a40b035078406281c0514030100b084c0c024011941c00405107000e4010711000580d1084610526403909030040301c80c070004c00e8a0300090080c907600c5000082200c0d4141400300e80d50b1290041c407405003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 279520152 1250 279518902 279518927
    0x803150409060c1103030106050f03040c0e04080c06130f0605070c02060a09031e020604050111122a0a03140703050714030405180108030405120f01050702030406090e150d03 76
    0x942001551401c2c032109600c2241c0401e80c5898000d1030880880d0026140d001c248240004a407045c0f00c034003030151f48440203590140c031501e10110295101c1da044a16030209a41c00c0d6042480850140000c0d2400c1201c5c54114a9074811040402201d03607031200400601c0200800d4107480d407005c560894000c041060350707194000c1009480b209007080007412a081480183c59054051038081c4d44500c031a4441c0c1a6180c010b401c0b1450709061400541c0c0781d240d48a030201b01c40c8a1108030136040d00c07900340035042d1a84480f09101d100100c0c1c02034140c544001011319041a0008c1700c4940000ea04484001079406200d0401603e40c045814142c54601403008044c008040f022403050040e00044010000e031001210082c0c0188031108005d6172044c02405a210940e10410050210307250a07006852114250022548100030703840301d0a09441c415143c13040541c0c0085001e06c022600600088040c03c2400380301d5002d407500ca440700d50115002c1c0c1d00c45000d01010700012003458400c020b1026527 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 279521402 1250 279520152 279520159
    0x90a1a030703140c0f0a05040b0310090c061713030806030a06060308040e0c0a02030d0f0b10030504060506010201090308010315140108030a09050405090607120b1c1101090e04080315 80
    0x2455a00d082c0200c10740d82c4201c00f24001c0c0101c3c2c8048902d4a071801202c1418034020f00940801c6060205100c018200d4924140d411300c1703082074100e0340b100b03180512070640d031289024449917841c040014014480d80700c0b4101c10f8561134401c101c1d0100e003604a6804064051a00043c0b61715008086400c1800a40019000c5428103d010007445440d1004104441a550220000d41e40d80001c28446008001d04507005810400c1486c3c03030500c2c03d4124082c42c501c40440001c90300000d00001d480d01072141e00c004042510b440c204000d120b603900c5581d600c0f180a000920214210303a500900a00c014080101104240e00175840200c50310307881072600c180070000d60490b5503110219141e40390801d60324200040c80c4000d011804e404c10340129400b071310a0500600c020340710b030784080e90900101c2c041007000d1603503900d00300540c1d170342c0c2100b07450342842e40b00a000c01501c00d4200031000038154840e060510800910411506030b4180f131071a4403030780141072544c40b07843c0c0c0c1c6200d07210706410000480e030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 279522652 1250 279521402 279521413
    0x3060d061d010c180b03060310050601020309100e01080c041206020f090406080a05071e15020f060a0914010c050403020d030302041a09120106050f0d0302010e010504060204030506070e090a1a03 85
    0x1034a40d0040d8000303d5034009244406000c40d903805e041d0466120481e0099095005120020380150068102d80c2d003101c0e050043e80c1c14a2511004a10018404880140043d804401c0000325581015005400c807544072001841d0a00704008101c030051007640041c541940010b20a6107403460f6029280642c0d0010824084241e6070700ca600d0780c80600074419502c50107880c0300018000101e40900b42d0800b038a40d95088054900356540e20384102601c00c6070154043c1d40c1810217000014881d0a12032460b200c400a143c6e60b480c18035410359401c10300b2400b0980c4c54031032403182058000007541d04407030741101d500000c4400b5107411006401158058100110550400070111281c0c0c0d021f05844130701070381c090418402c003280c91400c8e144248520342d004550324080341c81605084010000142c001d000218245203241e442e6400c6590444003034410303a50104003401000020b004040c1c12100d1380c580f0304900c4840354002011144040c00d401a110f9031001000400c001d44280050403a0004066a5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 279523902 1250 279522652 279522671
    0x70f05121207050705090109090201171815074d01021204060515091603061a1306110705012307030e011b030210020d02040f270203060d061d01 63
    0x541d2132005015003071050a0303d100100d010f507500d1092a8049805070350b80c2160625281c0911031034103000d08122808180c1c20540412568100311083ca6001e0107100600b0a20b07001200800104608101c160424811492040c001644440c050300201c2c3c50f80b201301a80300c800304103868600e030822059075154004104030030b00e2501c0d45295407290340100c005000c5542c54803060300c921401807414640c840320100c089a10a9114402c528880d40b80d400c0000304e0303588800700c0c3c402c00c24410b00e01e50000c100000b0104040703200038456000820950a11104001285a01c80e4850030103014450400208a22104a25640121980381151100c49003582d8020f070782401010140030316155808180c0c1d402d03d00681c01003003082c941100343c0650151003450440f11302080a9401070703200034a06a001d00000c03c6514014170214000c1011182d0000c2c100e072055001c2c7c4003012500b805500c000c0c4140204505910f5460031025007581c4884002400c00e0b0b440c102c3d0342080440030102909602c1d0041d0803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 279525152 1250 279523902 279523913
    0x302040f090603030212040e041103122a03040b16060902040c02060a050105120a020603150319050f06010b0f16240506101403130b130b0603070f05121207 68
    0x43d20302035400d4581c5c40c0c00700c011b404064801c40c410380c00032442c0303030001902180800720088580701d801020b5951b02c070034004008283d50402c0252030b041d0740c000b904045030819004200381c0c0d1032100030083d608080c94082080da0a010f2040e50682148815142c0d004100080e442900f42c19130003001003000c6e40c4843e000030368480040303512801d800d1a0800104042c03070030f1181d87c40d10821400003054101010381c00d21a09420151000c1d03800050540f91201c296070500101d2200119170103450010f50003410002c1c6410f01c980c0b41c21a050b00030400500c0701c00c4248080f10709090500300f120781e0701c1c0302140c2c00002d9056001405003544503080498105a40d084000003007006504c5014802074442c01d0030003042c0c1c96021840f502044c1c480d42e1280040c551800915485251100d4002e140007140d25000710a4104950300418119615105410011003500480d08114140c0003000940e041031480c055080c0781d070045e6071061031448205400d040c1c0412420703010194003800140c40d020796103401c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 279526402 1250 279525152 279525161
    0x9031b08040306050a06090b0121090201050f0412051203040c12050f0607030203190e03121e190c0e01020604140106050a08010e0f03211e0f1602030403210302040f09 73
    0x103441040d0702300410858a98031502078840480c0320701c01076900300c00c880c20a00004112160341203041c860284030f180c550220690117031000700f032004500c071a004280e03d13050f41019840740c05014200010700c140400b10307407090000b605486092000700418007035810150f1500180700491540c3e8810b1504105200b50325802860041180c4104004242d800c0340382b56042d0391400d54841003d07402448800280c41c8102c40840e0040320000039503101002c406a6500200c1c070440b030001240389e01025804a14020b0b20130010034001501d041404a00c1000000b5110700c0080c0000d04003440e001c8500002690a40c0030400400000f0458158141c0c3c0d90006400b030800040e15820078010140f1107807a8460200840d114074840c0402040601182008400e21500c050590107048564584100ba261300b5529010b008003500190821103150880312941041e40e008070701021500b0901041000444000764000c068403100000c056080e00100b00b00c0080c080c9038403880d8041038a54002072050100d511 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 279527652 1250 279526402 279526409
    0x20f19170603010603030525050f06100f080a11010219050c12030a08010308180d03170c04080a0206030402042a1b020117070c140c0108010909031b08040306050a06 72
    0xd0300c03159078010426088440300d110140c0425420040301c00308803000c084c6508030200c10300d111407146407946c50381850701c5480141c440c0c41d0350009050104101d107141c0714100508048891390186406c184410b0b4540c151504018002580440018802c3c1c1c0280241c4170024201c800c07101c001c012500f80190755039107110f5914050f000740380701da030a1030b1000f104660104245444e1000c459285075500242540300860303100c208100905001016640c404e810800e01e0b00943e192050b030421155040c040c02005080945101c108010400590f80d02007103070301d081034040f2080e94580e03440d40080350103001d10301207140c148010f03403091030a044054044401d00100c195190310030047d4405120303420600d00400070340071540918030a460f608030391007a540e0001142c60042c804101980d00d00201c00520002010540c1069000340c01ca9603000903c01c0c01441240402c3c044a04203440c081c004070041004420300c00207590321501800803c00888000b0f507030100382013140340380405551006003400d01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 279528902 1250 279527652 279527687
    0x20a0f0e0a0306290a050a06110f06070f030c0c020901230901030501050403110a080d110c1006060e0114070236040317100e06040b060d020309060c0f0904020f19 71
    0x44010380b003402c100004409544010b41f02c07164003400c101056444c11201d085400d590711420915100e5130800b44a181d0082c1040d8130b80200c4070702140c5e809029980c0d0399518204120100d15507901517038900107440e044481070180d00c0345a03100e4014211242d001d1000e6242c20421440001040010551100b032040b030095688060004416a80740e0701d520035a903001e000310505210942c9042515400749030f4481200301544c6c648544000a18108004980b0300f0944503a6040100121604494807201e00301c02440d00c580c10350100c0c20401c2c3c1a003d20880680210b1040b901345000201d03482000780203c040d40c2840d288150b1003400074040785000c60301280001d01700b102d0303020360845240307003103000701c1488440300402400c0c4410f410031050000d09140d03101e0345a00311103190707440700001098401603005000d42c0c1c1c0c0ca0406015450240050000e0040740e60810071850352480c0c0600b500c0c40060300b2940507907264090b07144c501487c0620340c4598450000c0324102070358250041c1900d03500f8171001c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 279530152 1250 279528902 279528971
    0x408160905061c080d0605091509090c0913111305040c0e090a0b04020f150705060c07020a09050603070302121e0313030f02060415110f01020a0f0e0a0306 68
    0x82040c0000104030743d07076540000c1503601c8410300041c000809071001c00d013100d8000176440da03920001001d1200a42e001002480f109845210701e060603001903500902210040040c4511038000c00d41c003e0004001d02158401403602c14200324440c9044004000020702c0d000c540185038440c04000c1209071000c0b01d440c00381d640300043d246007007240703070f4424440a405040c00e10441c0e100c5000c038000092080707a10040140c81c030300c955a40c483c8040e045014460f18151204850310349280b0701240a03000d040f280e0310030700072140180d840c14804015544006030205040e10750501080c604603990700025400342d10b10403c98a040400200480407550b400d80081c101a00c000c10a0385901c2600026041c00e0a54401031020902e140c030b403c8400c51001d481a1720702a5583d5980c546d07a41007040d110300090050f03188100e803800c1007190200303c083d410001c529102500c038000e886580c0024081045c0020031806201c60740d102e10340d2400854005c5828001d003800b03990102d11214210700b0171080d41a48 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 279531402 1250 279530152 279530161
    0xd060e01170703080403021908030307020d17090703231915090c14010504030501020a360e07230306042d09170d09030908010203100e09030408160905 66
    0xd00c1d10200e13600711440528280c215001c0c455400c0c420041078102c0303030a800c000070300410104015440b50b07001d54040c081a6002060081010f400740c4203a900e582045000e2203540c08003c40c41c00c08582c2c1c400c0c8000b410f81484544604001c40c2046120a01e01070414a1140566150110107640e885144030554081100902d942100c0c00315001034013008581000344079805102614003080c1d801410481e0500740d0300c1d9145400e9070b1082440301c0000740000d100d02690f030480d4200304c07050280d242840342c0a02c0d102c10f03201002e0b6554426210500300d8400414101400b0b0344049841c3d0b042480800c01c9000c07003e01c9140c03a5402665414041d41c9804448032643d4441b030702807915040540240f254a03049914003001070485c0880035100b0b1840d01c00114078940c100030051000e02016080490740c50300c0350501500300503066002640c41d9004104216103001d5140810040d20b0000e60105c0342900c0386401c0303a00d140035581100c5801d00c184088011800c040782c00000440c1e110100c01d0000781d54 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 279532652 1250 279531402 279531449
    0x31a0303340c1202092212110601140f0111030a030203070e0306130b18100b15070b0609060402181011030c0601050301240e060f100807020f0606010215040203030d060e01 75
    0x1040003041307140c51400d40e040710006014003103001c01403d061030318914288e10255080e0420340c0a03032284440740e1003000b44070101c0c20409001d00a50000b400d00c02c1c2440e0b038241c80c1c80d44a00c640300e62542016030000010350001d0049003141011407010703048038060320708980303510030150b8610303015551590450300203061300610342076403030341c103407403480034210007100380c203450019100c1500c0450f400034102c45000074000702800a040c025000d61030415813810018180803000780042c0c0b100380030b580100100ca00064071a20307042210901039400c01c0059410b0300040390301c410100c0d80c0c0400b600001609012460002941c0c0d030580310114000c100300c0c00c2c0745115500403030040d540848018480f110030054001004510780c0d00c10030141c11107034294200350004009101c0000c0100c042004c0c0000d202020b0340c10811001d110000c40020304885c100000040d60320840011806807416503030000504540b41030050300c8010041c04414404c8030340740d940034240b801e400d0040703c400941d02010540c0a64 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 279533902 1250 279532652 279532681
    0x5180606010e040207080d09050706140a08041407182c2a0a0e0a050708061c0314030f1603050f06010c050f0706031a0303340c120209 59
    0x214140c5664402c1811079043c08080d401c03200040d140700c0c10500c550080702d184c60082402c0b0500c40c0c0b000d09050b905098001e440c50050001000c054607051100010181d0400d0a694110750130440000c14110035801041c0743c51481e411842041d80d9491246014007402c3c2c000c01e00c1403440d0f0100c8a02e10103515806440304a90780c19007500e65020300d418488454400405c00340324001c810254000340c0610001c140c50f01c00716488110180c29210410151801911500c0d40214142c80d03d04d1803801c0c9500020360740c05210503020b070a4207850405004141c0200700c1e403071100300250403003a100c0c60100074402d159001110b4041e11804596018003895100b44030b10b03445000d40000001503a02c500004482c0852522000c0303509100d1891081009101008244000c003000e5401040901c0b004401e20348100014030418026441404289009060307121034402078400310540c00140b801a091180b071140b40f400c0c001e802c031604a180880c020071110010070126000390390080d19030325a0080d0011a1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 279535152 1250 279533902 279533911
    0x7060c050408240612191b14010e060c070906030503030106020c1c1b050301091103010c030e0c040f0216030f0813120e0310020408010504020f0402070201140702040f0f051806 77
    0x4042d080001101445c003640c01514441c03020040b03d0310301c0d125501c0c40d08003901e80d1005440b00c1500d256988601112803801001038a0450a510700380600500040c1076031190890b034a00c5144082500c0194240421691008009024007880a641d4a090041c2c0f40c0e032083c01454010700515034421201e0803c004c07000052503084c0c032001070740c940c01c0e110f10650b07a02c404031403074424074003440005540e50b090081c40300b004c7c000d081d00a90318a12408160071034106131006402d26040109904402c0008240c811b500d81007601c02141d104a1840c0a41c020701c41d601c0903c82407114180b00605050380b01081008031409500d40758071a4a070180d80001d1061449070050100741c0e016030880c40c191181c00008100d44014045504100c2d000c038003641079070001c1d0080c8080e0f03992103041006510b0b28402031503034411b040d1400c51602c059900001c00d1040140f0720711880c540300085000454850794081c004128800320100034031640490a40040c00c8240c07030003441c4100c00c054801d141c100103c0e405004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 279536402 1250 279535152 279535213
    0x200301050a0e060406030210020d110c100503060328060606080c0708071b060201090219030c0b0315040603060506040b220e0307050f03030103030807020f0604031407060c050408 78
    0x440b40b9018505081803802040c00303400c0358a9840c00001600d44031074500741859150043d02c0d105007010002001c164a4000900e03184d4400785402c503050311840004858480107242890381c07699030b1000310f45401d0344407032140e140c45124200e030241030100b1140d00c07490340d00c035600a2000302e9407010300301c1d00c490050b120001d0354141004540001030041004107905882015130101d401c0089038404005d0b00360398000c0d80543d44400940c070841c80c010301c080c6060303050359001c207210b6411500c0d00e900b00303003d500651011040000116070128403407545d0b4a5030100007081848a1622460018040c05d400d5800e540210700740b844400c060b00d086514001004901882e6151860299030248050079840b000c2c3c540300d010800426001ca0300c2441050303040b880450043d5500e500d54980207200308d0004240e6421500030070004910254007013291b9800982604d08064228009540c0144030320030b420004103014509800c00c400075400c800500b00b15030f07410b0281c8480c808141c040020201e84c06031072004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 279537652 1250 279536402 279536419
    0x706090302030c06090f040f020a030b060c070e070c1202100605180402060d0902040207061a010518060d110d060303090801141b070b0c090f0130020c1020030105 71
    0x3d07414080042d2400c079800070320005e12020303040045011079040002500503150006800c0c81c0341038050041e0259200309503400c904d051040360078a5201c0c0c10034003506240300741d000d010404003031280010811040e00f042c10200f94104880029503514851001e11540c2c6041210024061909111685018140145043d0300d40d680340c0c2002804d80c007442c49566299551940c07800561580e10107454024803900f000541c03080583c4195543c12405000c40341002400c11031180795030001a100060340405490750b03a160f401141d00b5402a00042c075503c16a510301080703030b843d041c01c26040001124081d44541c03c0749503c80c5e01c611b080c1c40350100117000406503000403524040b000c0307290b1a601c0400c1090a800c20383c3c00d07501d0b61841d010075600c0c200c40382d4004c02c0f10425854036890020743ea80003400c01d00d200b6510b81008501c40801c021140880c1040341c10303206100003864040360f240c1c4455500f82c401d50300d8001803440c001c060086045880e800c1c50740303441000e1002ca604907816600300070013010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 279538902 1250 279537652 279537673
    0x303042301090c05041104080703111324050105180f0d0f0c030c0504052511010e2116080c01020415081905061c0201090510030c02070609030203 64
    0x10315089004040c11034030301055054904030030310030095003034402c9280d000790030b141100304800d5440c404101c00004500700700401078410b00186400440e94008540040c020b01e99000907441040902043c40365130070403012036040d210308842d91500e24440c03054182100c2d02e52004450b58003841800d20000402041203481c85c2c9000c00745c00b00103a4006100c3c0c082203a2564400d060515203560440b89400403042c140100441000d882000d4041603c00700b0542c0750192050076080c00240e400620300010407000e045140c800d4011951101000f00244080c0c2043c942007a502c4048040c0c1003600f03604140404002c8a00c07008540115030541e40d5000112295243c00030076034072200707085190f903500b0400011a15a101e90702900c54110ba00c4a901d2071501d042c0c10003200140801c20056146000c2c10031078155031f101c0304010020b00861a1640b0b6a1440c4016110131805070403099116a0101e164142168550404c0c001280180d007540c007009d64070b6505942062031804020f41c540c100c4407003407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 279540152 1250 279538902 279538913
    0x30521090f03030f071a011a0403110f032a0904020d0b060303070c2601020c0d03020921010905070509040f03052104060f20070f051e150711030304 65
    0x10610000381039a2904409505806a90b030080d032013101c9a613460b24103004a00c42e0108128010123010702403016101c070041b1320401510032130100509403025940043c000784c03221391803c4a00c40016046030003a2040c0c902202c1129541082030b03000d041248210800d900b850300b481c600603a4090091040303800d055907007442d000c000902254040c4000d20104000c0380c11114600c0081c51340700254004035040040c505c030101285491070031030343c0c01080316100d01030b030000314074092802c1e5160058680241c0c5000034080d00003140d00c89480c45510101003450901035200d0446a0b0ac150212a03020359108248441c2d40d0303040301d010f454800f0142c05200070a0158008007041c01100405980320320208000c08908802650181c400c10380c1d404206411582a1041e010a1034008891307604076002c101c034258203803040d800d004206442c00310305c80007004010050241000e4078201840c81402d41c004845641d107110145c640030340c0401402045c00d003030003103004001c2e181d20040614619038503601e65 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 279541402 1250 279540152 279540169
    0x1e09080301051e0a1217040617060103020906040602030301140a0501080f040809040504030f031103090a03140f27010c02011e1701150305010e0903070f05070504050f0103052109 78
    0x4146920044114240d83e0b40c0c0d802c0308080182c40d03240d65401c640300c01428903140100c0e1014101e829040b04000a01c0000d410521a000d032124803480d100da190b83d01c2c00100c020b070040160640d00302038040f80216070141c0100243d41600c070810356030004071100d0f008004003200c1c00d00c82c1901181154002c124000101280340345d110f4002c1c1001c1c0d02d000c09840100741102c1d0210b034140c0018110b10303004d1880c26410f00440c001070308203010035030640c00d002803080c0d115004241c00500344044072905903408140b94080d01c003540c00302118180c490310069032111800f50720f400100b12144126170000120360180c0806400c0da90182d507003907101001c13070a040540322110440d41c0280080700301191842c0307454074025406803c40c190b60101c407a2405401600350780c4181c001961840340b41e81085410000001907800d03407500b184644c02040194105241411203d0f0042600207051104000d0780800c060040d030704aa103e0800c480c04c03074003250414a13411202d03130a00008000f003044000440d2400c0c050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 279542652 1250 279541402 279541429
    0xb0411031b190504090b0901060927060b030618090703030804050a06061707170a06020a140f0405010e01030b09190204050301020d050109110f03070f051c1e0908030105 74
    0x218035141c0041c2c030140d442c1608602d2401d100180001409000800b0a030044010400040d03d01800550600c1d038007810306c482130b0041ba110034091011038045d5900502c0c0345030100078008030400040b5128141051103900803900180250071a4294019410440c64094400c03900c240141541070b0455504031384144001e041038550348039001f00600446c0240c03013400e000702200280c840340c02042c40099410241c8a9120400c1c09041c41c4154165030703800b06204494550000c0010390300c80721924141c8040c00c1000f004a9508000f0a0540c04600d600c030092065440036210038101140da0f400440682c1c0320b035a0701c01d411007820404a420f0080140d41d80d0300d4079900d003d004d41016200c03030100b42289c10900c1000c46458070b50b00104040029885001c02c0d00c190404031624050810100c5045440060280300c200a80138600d401b503c1c5c41001038501c4d43c108039107c0e076144102660b01101508030b07d61084084444010703920a03604603441080c08240e40700d0000b60444e031030b140c1044001e110740398 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 279543902 1250 279542652 279542701
    0xe0402040e060a0617070b092b0c0305010528090507120b0414060603120a0311160c060201060f03060b03070e040503040305060c070c05121518010b041103 68
    0x406001412040c00030b0380c0318442403440050640d20300740d0103e0b14104d4241a1620329045281305010032070303a04046071002d0005903160080e0b00700c04880d010146040491510540700c041c3d005208001e0840d40d1034003164041c100034003064840f49000307407007504034460100b821085048000100c051300d8000c40d40e9940900107541425950311340c0029072042c40f0008850b00b01c0380d0003c110410050340745103001c070000e22005007950303c0c01101082c0d54041d0b0030541032802c000403d40c07114180c481d0300041410f08041079200d880e40b00e500300e8803159003624070701203410b86000078020a10b284140f00364411a0103040c0d0284145241d40c4903140100112803000c0e8250081041c04035482c1c4003c14071500641c440d800075980d0311f146080141c104400546091013048041010001290754a0f5118050300c0044440a040050207840a443d101004562520345191001000701200c1200712100f07030b8240034002800790001c030508000403240000410030b000b080a1001c1113034040c0304040101d541c000c11 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 279545152 1250 279543902 279543911
    0xf0403030603080d06050102160302030309091504021b15060f10030e010608031908010302060409021b0607080109060b030405060408090a081515041b050a0509130501060f0512010e040204 82
    0xf6164100705a10001410f01c401d52945010000c559041001ca4030002089a80c10f40160039030307000a48900c0f0f481001e070710500d42c68001c01d1440c02c1c2d40868403502a0001c0c4219610b091000a03d4102d103a42c8020302d5035070081c00d601045c01c8c6070f1110a00d00c1401c00914050f40b0100000421928815024022040598601c045a15a2801d114000c05011280e005585400d01410130400d5181d51035003020406c10468010001601c030701d4162001d40707101c9100581c9425800c11000000b840c510b0f44404140b0800043c44186604001a54140c3d031b1090828400507850b00300c960802d10007510001c00640c441400100410030b0000541a1301303038000c090045880e0703500b000d43d10b0000c8404546002200c0c40c1d05009100182603400711013190256020f1150751350402800113030381105000b0900707120000500c05081d51240f0101c0714a204003c2c0380c0d014282011101d080105005d024150105820301340800310540201e003030f207221000004100b1042e0b820440042488400a0802c0f6045500e9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 279546402 1250 279545152 279545159
    0x13170705060f0906010f0b18060702041e05240f0a080a060204060e04090503070f0c1d01030b0a02070203280b09030909100f0605131214010f140f04030306 68
    0x9000c0c2502070709010502d051a802c00043c2d00b0706013101031784116850128054108445081d05d0140c400008034410300410f90000796010030301a100b05000203501600d4500c0ca00c651180452080414880c80d500410581e9200c2e00300f0300308030b000300390181e40061008100c40044e24010034500e001c8440900800d0b4a180d5684025141004031041102d9540d00464240081c2c0e03800300050282c0801101c052103004007640706c41d5101e1103030b03420250100360500d07003c2c400e00c450381240c03c0003031070104000c2103c008071030422505440207001c1100c10007000804145e498540e0300940b08100d4005022b0011408a000381100c2c000d19580102d503040c04440000005c0303aa10800984034060304009107075a403620f0020064001c030020600c0c1103480382a00107000100d06c11000200381c9416013081507603200320b99803031495001c81364850008201403c501008004200c015000314442100090200242e002c460005803029a0851f5061100722400101007000b04482250014003038280029910348 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 279547652 1250 279546402 279546413
    0x41505030327010201050709170f100c09290304030207120309050f22021305030a122303040201030f09200a0911090411040b040602060f0f131707 64
    0x6500141c01003003000680b07200000c1d6000e8540710702c2c09100810107840d14082c040c140c1700b80d41c020800c640001d8041550265000c210000d02d03404020222002000c6400000f40504075580d0403800107001414000341401d00e121044907201240e4024200142584000b01c80741c0e0401081503046200c0c401c00015905980d40307291880500030744e40c80c1c41403070602052007110407848890381c1c01010360001d142102801c2544000e00118000405661141c2074003454090403c10380210b0340c1406a401c20104101c0e4080006051913a03a8031203d17074441d900a44d109e0501c00f10001d031260301100f000080c00561280d88051510303850784034002120342c125151617070310054084514001190011810f440340c94085070131001000c00d00345c240846c031200084000302c0d00550580c54003660710799240705801a08182618050701007038a1454560342d407194002d540303420a44450004010601c045030100c100c00074a00d10803035821524080741c84007550f03014140701d5020800451514180001800102c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 279548902 1250 279547652 279547657
    0x307030c0f1e0204050f040b0f2715010602030a05070201180e090c040e0f0709091410021c06030b062b0809190303080429131b140415050303 62
    0x10300b03008040340e040e881d41c418002120000340c84003400318114020070000030000d0340c045603c540320110f405203680f01c00c15410100a103400015070f0b10034410100d16019840003031a003082d030403404900071850b681c515042c0e0b22486109848000284204070840140d4003483d020b803140030011905542103580c070300c0d040040b544182c0e540003950b00030040340c10261410b8041e058880c0071003005850030b131000c1040c0542e559500e21658a43c5501c0304d4210302032203a0341079201c1140303448200740c5010a85103c0280c1c001d6000350322022054031000300840c03040203d84111401d80c0d41c010380d50500740c1c44d05000c0008820640843c445550780001c0c805580e215525114070f0311300e114200c0c1945034109a01009468010284244000a040780341000420707407040645030080d4114001c0e01000301d0002010b2070507482c8901d6059131240c4131082c00010010719202101c005c0c02501002c55055403203680365900700741842402130b012000c1c915180341d40ba01e54841c80c180c043d141c18003d85190b503480801d0454 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 279550152 1250 279548902 279548933
    0x51809041203060b03010f03170c0f0d02070b0a0801030b060f040c030b0312070c230301060e0106080907030b060f0604030c0905040308100b0304120315350307030c0f 73
    0x502000380d56964075901805101c01401040c000c0608541c10544100c141004a10001e0b005a090f220b01c5840c50b034000e0101c40000305540140d074140c100001c0304a0380ea105800441005118915001942484103420340310000c800d070307451002c81e03481c6440d991401d0f80301421050788030f684c06041c0000c1da9a1b600c1031500035145034901040000015040504002c1c140c420300400520800ca0100022409680c0d101500e0b0100540910021841e03490040c1c0100710544541640c60f02c8004107403a148110b1040c101c505554502d00c00707a650141807921a00a4800200071081400106d0341520b071025989c0080140680142e0a042d5281c42c2d1a0b1564400d0b40100e0704550b803107040c0024980d0042c0d501e58041403841e041c0c0c0a035880d04888001c1e6104c002c0002d40784a80320030002c40454441d4008001904101c40b2504c1059101c83c0800303001080c0c1c0814820100807840c200b01d00000541c00a003a105282d000385040000c0d0b80c506840030010190304640d4061410b1030400022950031081045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 279551402 1250 279550152 279550163
    0xc031b0308190e182212052b0615020f07030605130206031e01050d20040f1508060a0608280813090f09020306070309080918160305040f0305180904 65
    0xb00d01700f000340400c92242d200d0302513031020384030005c810106e01204200c480d11510b51030304a40d10f4050701080c1c9000a041040e2404a0708800781080d00f280f1943c21000a032424041ca07041c01e40c6c03014030141d03540e0180503440103176904150000c101041403075011541c03110818001541f4140e0641c009030440c0d008031800429503101d80184a055026020b003240500006d80320103a440d00c49c0c3d1155611740c60041d02a200107400808000d10303940781c17900660301e0039130701a0081c0005c44469440303601c40030b86030052010b03030302c41c0600003003625030707180120000c64400e500a01150004568071011481001c00221990f01e941c03e00c1800250500c0020101540915a484000780c142811402690a8440b0a130401400c082c03100000d03030b07030205443e60812010b050000324103002e80f0780f504642c0074110000380c0c01a180b06c900703c1120314810720303130788521624800311109102c0758100760126002a036002d019024010306403c0028000c4d401410400360085c0b04694402904001600c42802182d04540 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 279552652 1250 279551402 279551449
    0x7020f101506090e040b090c100203090310110417030f0c06010f150e090601120501080307170a0c0210030603020418050d0e01050d15030b040c031b0308190e 69
    0x4650344100000000b81400e4034041e90741502c0c081c11501c10103400740024010403192404250031520400c01c41c110200060300d00040d101d4030800180d220740107040d2041c000d004880c84c5c80c500c11280c4c0b141c00d1200c0f802c0280c1e181003074100342c81d124110504100b00c0320188002c101c03003595283d1804c0940120008107000b002c2c15030410825048260440d400907128004114004111542007080c0000c8050140c54041480d03407043c004071410808031598000b41c1d0315240021031442800720044c02c00900079078804032070190b1448441000c0c4034001102c000110007100350001031505c580d900364001250300d0b020628a407641c00041c11160f400720042c40000d00d04803038004208051201d4030f01c101450070100d2911a080001810a11949610180c25503603245504080e0f41001500c41c0a55040019050f00b450a454040d0300200140026100205248085011a14281810f1055980c80a03005090601141c0d451f04900c05e0b19901c0401e1000300c0c0e40e5220207071200c01c0c04c0985424144032580 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 279553902 1250 279552652 279552671
    0x614100314060601090614160302280c0504090f0b01080d0e062d04170a0c05090c09010509060c0a0b070f110c06130b030709050f0a1d07020f10 63
    0x1a000781c0340d0810746241c0e04050100030041c1e80006000e000c460460a00111003070074074840c100944a0f2031011003a40c282c0b140d0110905a001840c0c13800042d20200740c1c01c05030700c169140c0e80388400b882002004030700640d9092005040540050301c905100e401c01c100700b0a180d070341e100e11090702608840300c00c0d801031260100c0d1a41c816270b802412103007034030a686003100c01c0145101d49501c940c6105250710511918011010317615003101e001b0f140f441c5d440706040521a090945072a6000410340e4154000e000125481c0342030714000c0d0060012140c0700f0300d08045100151159006030828540c030100c18482c000b0010001d01000c24030511400c5000800d140101014000d019085020010404009100002460001026401c400c0c0484000fa00e9011280c4840103c0c0041e41100c0b041c80004020b210046070000c4c03650b4142c4000726801c468483c2880c080c801c0c500790700c0c40b4150034891048400f840080000c00a07940040b113901c1501d0f03011216080892800111a008070b689550fa5914030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 279555152 1250 279553902 279553913
    0x9061b070501051c0c140d0b1f0207150201060b030702031308010b0d020f0a05150a030f1b0e0102010b1509120601060215070908060a090b06040b060f0706141003 71
    0x8030054042420034606110740c01801e4850181811125001e00f40d0302d4000040b028020040890070340c030079032040b65031703440da62101a000d08511401035014640c95120340000c056500706d40000740d2010b81c004d200941c50064548440c0d030018821806555032144049a8403000700b00a5205400b913800075569828483c1945a0b01500c0d0780c800390090345000907070540c81d5140c1d899028400c0d0115409035010b00d10304002001c890440d03020b542c6c00b110000c442954140b40ca00900011380c45520100324003030218603c4816948160700c0c030304085091540c0d80d62010300640300c2c107071b4000303042c400003d0800080b0701042d00d0f05e090b00700300f4000da00085070400e07a510b0200c2684030768000810140425500d400d0002e96a03c5132505410703c1c5405400c00110280d00c1a0070010040c602e050427910641811448000200003c010940e0401006400200541864000c3c0c0e1540b0602500341407400c058220700c03140c42c1c0c10030041142c8a58445030914078107044643c040c0d005001c01815404401e2844c80c2a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 279556402 1250 279555152 279555163
    0x9042a0905070e120c040c0306090e1c0f020a0f03030920040606050f0f030402060d0203010306050f150307030201050a0219290103031d010504080d0804050c0d0819030209061b 77
    0x41c284512103116081304410700110780c0740740c0080b0a9a0216500040e200150054401c9400c4015100d10f001c143e062207210010304105425000300c2c2035030702c54000c48004c4444040044200c009a4003d00e4401b000580c1300f2080c1d00e01c039009160000b40304c0390f1aa201c2c0c103402800c1c001c0100c045d449010001381840c1c076106410041003d07040240c60480c050070411014050038581c0c4a540c003010000506545888013101c03d2501000b41c119034035a141c0c501a0001c04068403040c250601e0b03000081d601c00e29405081561403002002040360074034550044a19a0260101400b180a81800f00c440401141b5200c040369119025880030040b40c0080c0e108055480d0030400c200040344801080880d0308500e42280e030500c11418015007135a12401a02c0500c11503000030098030400c4004c01d034107a8817000903805203114405550320640080c0410050020540c0043e0849030100103215141103200303d0600b902070315007005801c00107100000384c829001074101d131010750f001c1480c01700b0001040c4030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 279557652 1250 279556402 279556427
    0x1b02010606020f030c0c040b0a03020603041a0c0a0215060f0a080a0501051501090603020702030307021e030c09060f19030219060311030c09010f0c17040e09010b09042a090507 77
    0x139400c00307541d22030490b6202c4590340c001d0b000780d60703c540808854842c41710440143d900600010f0ba41d04140c03070701544403000c1220400401a544000c66a00c100c002d086416041a070f500405490050910b40f00080002410090303000d503c0803010030458a0ba6200c140041404c2c001428000055041403030035100f00a080c1c221074000050380001c16030b00603080780c081e6805880c0050710b91140d0f2006c05d00d50b2054800180d484070000c1c0b50600310058221590f0026502078054403001c205510070300c1220b810946070264002c0942e4800c080c1414031a5111200d80451440c84901c15607d4012a074200c2040014543d40441003105000f072a42502407070402e0800200340d0b600e98500b014020802e80603c4c0304460400106031659070015110701c00088500741c100340100c41800901d10071300115031040c0700340084a05a94009803120506210f201410200500110310300d42ea5076407000e202107180141d046500f5981c3d61070046a400c144d8800c00a007200d40c100180720305110070041c1100c1030900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 279558902 1250 279557652 279557683
    0x50c0c15040203150705072010110615030703140114010807050109090207060b03121308150103060c12020c0703020906061303031110020f0904140f0c0901031b0201060602 75
    0x9000c0140c600003412813184101681c1d4a4041d280c0c1102202c8520031185c0113011402e0941c2c0c4040543c40d02054501420002c071007441c0c8120545806075800300004040c2c06d4203420610018180d2a40310b510000da882c1c0080598410750380b41e03a9040019215291a01d515039034481c580c0d04500b40608015014100c034134000c0c000c140c0b904000a040000d00d014042441c2d40205a0100700085a0840381c3d00d10070060030fa901d180d240b844440c0c0580c1021414611091103e40001b0340040d000c030b02d40145410710f170135420050303080d07440300700c041e2850622242c1040040144508100220320107032069416490140500ca499801044000c0002520b182d115000402101e1400400e00151004880e414206400000030028040307003001c54100c00090a135000290050440751140000c084602084408000a60340b002c80381d03210500c2100c0ca001004441c0d00460780601402000d0454040149800700c2c12002d21040040444107440030040542c1d140c403402e02155070140545500c820200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 279560152 1250 279558902 279558943
    0x108030301050909060f06190302041a0301050714040b130e04060603051b0f010e01021f0905010507030c0f0c050705041d070b0c190c0312020610080d0804061a04050c0c 74
    0x40e10b0b00c04d1b004007410f824428405200f4003460174405403000b60003581c0080c01040300f4100c4003008640280581160fa20035482d20002400850007005110120046102d61a05190421444459070340c40301c82d91101038808241c0001d80e401005400ba4072a611800340454114590b1400926100750b1385414009070050310100101c54131004208407a1000174a041c40d090024080140c2c2130480c90311400c5580e07906800d424158055940200c0c5215101d14003c000310b5850407000c41c2240c03401111707600090241c41505440c00d110740a907110311805101a00c0b00c02e5a1000090100c8103030134542c1000500c61b9002007401e60701030000100400e0b06c1142d01d0314210b60110015102c4401e0700c801c4002810060700c040501035100c1590001d5640031140d80d503048038850000e5601c0b0012901e401c81d6541c0d203d008102000b01040e2944540c070707103482d5120562604d55813100a0001d5440d03510115002c0901d04290f56528000c880c0079940d203215159070703a1901c000045c1014420303101c0c401c000700030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 279561402 1250 279560152 279560161
    0xc0602030f0a1214091b0d020a1712030709051e061b010f051305070b0c06041502090a03110f0a050604030b040813060206150d0b010b0c0c09010803030105090906 71
    0x841154082e840a240c82d00300d5282d00000c0300c000b03080c46000514046070403010001580741c00922840003c0f4038005240305107181d83c040210a01c13441c0c40094001e241441d0412140c0c1100344850b02c0c40400310250350202e0800d4002c0c441c81c2d0000c5425400003040010f041200b42008402070009641c000301c090a01c144010101c2d54910039102040706030038038104c002821200a40c484420310341c41c0c100a001505002d0080c603c0300e00341903002c2e1903d010b01180059860b0340d01c0120b0b207803100e02001030052a51152030380c0b8020200e25030100c2e041ca030204900ea4040ea981c2c01441d000d148920185c00d5003212035802d00982c041c005c441240210314120781400740e035660354140c500b200d42c070070301c0441c65a5661900b0000c5000d02c00c0070307070103180070b1090100340b0300d80204525100340d07000c580b50b4040007498400c00004991000020304000e004600510000751030308020405802481e0071118405048030100703850400c240c3c0b0000807500040014401032810110749900a0300d03c0380108442c0c00c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 279562652 1250 279561402 279561427
    0x209090c0a1406040302062a06010305190f02180a06050402090d06050402030a0206040311010e0f010e010f05040f0603020d05011d01210614041b080c09090f0105130c060203 76
    0x1000e001d005035400020740441015070b43c00c3c1c2120041d5601411803078880007941404204841a000481003551400320b4500c2001000100c40b0704803500400141710701e00100070040b46000f41caa000303a44442d0080e5130b11001d610341c0b0000c000440c5907010b10b5040d501d0120340c16411034503160040c1e07102d01d00400008100380d8030440d15100c20740d0800c10000b00798882d072001a01c1c206060360020f4114201203000400d10005000c52a881002030721040110043c3c6410814020512422240030a28402050702c0c9035116402100d01c0d4806802c0682c1b802d91140c00b00280103400364000310001c2d400082401599041340101401400a005d8a02d419009650f6080c0c0308070050081654291900c0c000700150074019120f4507050390858420044e0741d400c5129862185001c480558041044494604020035501480341c115004400682600c80e064020846800710240c0694000c1c403804e010b00114101c00c1c03055500954200101e08c122880740d15060006880c65031002c0255081844007040700c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 279563902 1250 279562652 279562669
    0xf02010905190323010c17070207050d0602090a0302191707030b010b0d02130603020309060f09070501030e030705030d090c0603020a050405010f171f0e04020d0b060a0909050303040209090c 83
    0x258816541c456044490300340c0320304000c00400b0700c07000d58240804025080c7d080030a003c8401d43e00c1c100c2e00d003d559000c01c02d03a6035085030310419030888c0c4400000b5000c101c095010307160500e4000d010740390003550707500014090704501c44100c03586501c0304020003220240b180046040c90018018040181c40c5440d420305070481441910021100011180c00382c500135411503c052803000246443c00742c60b140020001c2d04200c1d0440000d100d180c0c0450019003071440390324410900e1310018180380741007900450190220650003002848248210030000b4000e10190601e0101c01e0740c001780c2c0c13417620300b0400c417800b065920030400d16104001c0700512a5004048a082d29002c1c00c1210941900507001c5586110003041703440c030390001b0780c10300010094100440260fa900300241c450307069126001e09242c080151070096004440c0d0b070200e000158240040f591020000f0444160369907103246e50030580d00708060881d0031750000400c000452400d40c046d150003000c504002c0c0700d00e00e110008551100c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 279565152 1250 279563902 279563909
    0x801050904020108061903033f1107021e0301050606030c030601030506010c020310051801060b070f03030b0a0e06011b0f0b06030f030a02010915050601080a09080403020d0f0201090519 81
    0x88001c0c0000361882d284c00c0541c0b403018107a01b480f40c0c0402d559003002005620000b1418004d500c400501c000c044c102d8503021141e2040303c0718906084804440180010a0a03240c020703413912046c4420800f5941c1c000e80380f0a8400c0009481d00701e00300d085c00309070071214010305452050009105100204405400f0769234003000a00300080e142d01c8039030042c3c0300c45000c0440294940309804284811100f40c2d0840d50068604842d51080105c40500850036603420f030180304020360f401e01c010701c0803032080900145141e00900340001c10020300804aa44600d50741c006080c0c40d4200d000340142c550380031105000850381e83c190b0b04101003569961000c410070b13a190151a074482107010640f2980c00303104c0000c0c080da0960031a81e0300d100c801d9020780079102609042e200c4000c203420080800723070700e40103c034440c420503911404c2541d03440320762000500101c0e03815240c0103014040480107840e100701019203540180da03d00c21914003840010300e0582203030440c0e40110441e40854440d00219009403058 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 279566402 1250 279565152 279565157
    0xf0905010e04110a0302060315040b0105161b0b160302120304150905010e0d09030302060a0c05091909020708120a140705090d1e0302060109020f0d09050a02092508010509040201 78
    0x640e0f00003c0010031103a581d80019501800000c107104114141d51541e00f80c50000351402d0080d103100300010740d860700404030000b03000341c0b010007100d00240913000e054424044602c416490181c6400301010150080c001030340c3c9142002078110185074042203600d1500c040d0b45425861440d0991f07403201ca602e51303548040c0e806502d03103040f070f01044406c0d00100030004840040714a450081c7d0740c005e02e40013880c0f00540c05400f9003070200c1d03000440d5001c2c0c1c0084081c00d03201c44c0d240885000c280035484018064040607098072840114544105000618081d40111303010342d286c00b0110080360039030002a101400d0385d803504441d0022014030105143d03003c4511b060035600c2d4152803002c920100b0710210010b090040080446604c080304245801200c0c2c040d42c00ca428903a203503a00030341240705801003091402401c0c010301101021030781181d4080d500c600181e420441555020441104050300c1c031100d258150301400c07031940454003012501c40914078000032a5407410022444944000c1e001904 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 279567652 1250 279566402 279566423
    0x1c05060f06031302041406010e1507110a0f06020303070e060a021005060609060403060c02120408071e030b090c030c0a061709011404050c1804050c090a0e070902040f0905010e04 78
    0x85406071441c0e000034003a006802409503d075080201c01c613140081f9080c41c04180346032084c04050400f6103400600b042d21022062030f22000e0b454a015807003001108a0b8003030444100030a9403820411010010800b075001941c1740d0078181070203860000b1005015000d040b041c0403d5680a0303000a8550300740242400c0081c0644480000c00c110344210003000340c00030f030001000010014640e00c050b540c04066030984884003c2c0c1c000c03544161049200b9050a0380c400001440b41c0002d506841c0614082d03203034807245499690741d400320540002c5030303410b4040d08180c80b40c007020300f000d2002401c1c1c00310481c0d586c080181481000341006002e21401804032100000141e00c0035000d50101d00d0b0f11100402204840c545441c19555601528a03101d015024407007801c0003108204502038016948180900070400e00c290520103008001800c10103000d44410400031a05014020200078000c10b41015960740e040154a10005201d6800311215030714000c0100906000004010742080d4805503046 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 279568902 1250 279567652 279567661
    0x30709050619141e210408040306050712061e050303030c0d020304050724030b06070b0a0203040614130b10060f1206090c080f060307031716050a06021c05060f0603 72
    0x907214003440080061280144284c0e44440005001625480c0c106808102120300c81c424505c2d0b80000c2130b240200b844e034051005100141135071300070b90792010340c914240300342c10131240d0021306940e21540502d81300714200c1c0c080c0c500c0401001d441009054160b00851071401c11000c2c12a8501c2020801190382c0d50200100c2e0420606202190040c114603403107450b1000410684010b059223294114046032501305481c1d46c0d4104141607585a0350004080280d659450301660301a52004004039680c03540e030352002d80d21020003440d1a0041c100170041d03510307900961030f080c0c548040180079040000c01ea4a000c1161603404a0030010202c12494003c6102c0c51404510000d03015580207413010505001e8580c0c8403030740c451406803180c003009001141c3e41d01c5840915807109000c4c00081c0480000480402ca088054001071400c14444070301460008550344038103050035130340c00048030300300c0c0c0001e032807001c1090308040c803900140070301002c00c41400e10500151415140c0404030f40504000300008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 279570152 1250 279568902 279568937
    0x15090b0106140405040c0306060206091504030c060b1e010f0806032806061202040f09050c010315050603130b0618070c061e0f06140105040911071205030709050619 72
    0xf1401010050420701401d0501000503024001c2070103101c00502c50140000c020b060300141c0b028004604144106031134640307803011038180070104000d803074582c1c0350003800c002c41e04c80b1007441c03807800708800450206400c0710000604910900058104001c090000e1103c00d40d03004c100340340200c0c20f861403201c2c6000d00003004203940c00c0d44a006841a450980c00040c44c0c000079a690f0070582c0b007245c04004040c244510340e801c0701c4103c0c0002c0c0055009069403080c9501aa2090301c01120703403010902407540d2140082c4095008841030120b6081e1070100c2420800f19504450304590b08035000341030700c0c80c0400d110507039a60040c00c80303080042840f200e5040c0710b48d030350100207aa0321130b40c86d5554028910301520051b080800011403020328040001402100c2c0004441800e00141e5034189450314081030000034003480c0c010810030500801081c0c00095410140e0010070300e0741c0c1c9561b501ea10701464007034145c1c0007560005004c2d0b5000c111000c40d103000e1030010480c5010b5030825104004a80212 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 279571402 1250 279570152 279570157
    0xa02070201030b0303070c240503070f030209030a0606050f0907020307030c02010e0d1a0703020a0f120f0501120c08030a0c02240d1401080c01091a2515090b010614 72
    0x90b13018040002d4020134840d0ba40c50600607034182280d403a4461f038042c00b12612031800000800c000030024000f240744244600712850701800e1910300036060200d040002414807208810407500c0907510130042059040107103401c80e900c43c0803625001c1c03a2800c030314069100d1041c42001420801e00a226108682c0a620b424025843c0078002030302d0b4030b29510300001281900c40348100c00e801840700040e0818400d00858003040241d81c0d82401101e4005029242051540e51010020b41c48110f0740c2c1c500e282e5417080900038659102c0d4951401160300f03001001c43e029403c601e0441e002004076004003a0000c20301a0055415112030354800ea400040303034038000d404400c8101e01000061030111442c880e80020402e0406040c80101a076a621360442e9240c440805443c0071891800c0100100c1a07036540d218414030780000c842e86051001c200d1003100318103003001400f01d10300382c006540505c0701500e6001c0013003007080020491040c10361101010340105114100800000b007800d02c0000e11000203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 279572652 1250 279571402 279571421
    0x7050d06020d060e010303080f22050a05032b0506030c06090d0507080d0f0207080d05071a01063902060904021c02040510080106140d060b0c0a0203120c060a0207020103 74
    0x50410100d52160313140d6025450a210540006a131840407515500c41d04060b18010240802007803c10b40d80038041d0986940c1a050543c1d05000340c401c01c1c00450014802041c42c0c1141c01055003120080f0304100c1e8840c2184076141e9240340c9031204012071910002003800030b5140484581b9201c40300c440c0001c074020009840100f03140144c03900002c01c0301e00018a45031004290f00c4504a41811010403a07861800d071007141480d612007041040c1e65805203006050041c0150511900d44aa000404e8040002a840840000d0404500a0310031850000d039400002407200c031a010001a25550ba1072005006406403140c100011003403481d550302c0d41121031100b041e0b04422010144481800b000307411520529005842c00903100607010303c9800017038141e51268540c117100f2440030481c2e015541109240d00750250703a9240101d84003a50001a141404004004115054582c414981010b0410300c445106490034440c0c6c400041002c10050303448a400700c40107869100500049014059000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 279573902 1250 279572652 279572677
    0x1510090906021b061005040b0f0d06090c08030306031c0c030f0e040603110306010503030a0203030f0403170103080a020f0606010504170717030c0d0f120911120d12020c07050d0602 79
    0x14101410040483d0075480f85e25035040c80d04129036140c0a200568000f0702c0290344c880b10a544400591a020000034101c0d40128400910300301642e030351540056807904500c0c20380d84084204496464100902880420316000d0050043c00c3d4840141000d80004030003001d01110b0700ba6050204c1c482c80403075283d080c0040080c072446035070f400c10603c540e0804500728043e0241c14004a40d03402c0c00003c6030702c0600203038021455a5507801250160710750260044042049034105040c091070300034403e80c060340c0100700140e5a98095940640b800400d0504500c15400c00803c002d000c0e07030400196000c55102d401d88020201074032840fa42000302c281c12030b1340c240714495400150210000302401c82c40580c0d0080710f0010281c0301c0140d40300d003c0d407681240010600030302c86d111600c60346c002ca03103801d206a200001d0140b0020025813102c80c91002e02d503060303026028030103da83e4054004604425803120452400b01e01300000d54130b505082c0035080c012002d0348407040410003254100c90b030310718000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 279575152 1250 279573902 279573937
    0x41e030c170f1e0c030c090712090b070302030712050c0d020d0f0c020d0212040e01050d020f040c0e0f0108060901030308060a0f061206092309031b06060102151009090602 75
    0x100d003039a5000300c5141259214444c4003200e511034240090307000405034009188454690328020200c80103440c00302400a00f90303c0d14030490004014983c0300f405203c05407005a00d0746050580102022881000c0c20356903030500b000d11044001c51421140380d040c3e035010259403005039501000c05445009110031b100c40c80c1c40e00d95000d00780c4c04102001981c3c03a550994120300c01c515a0301c02c16006900901c60b220700d40200400c42c44c589182c07100300092015005200ca0b112210014084421803100103000c0303445c0700102c401da0310307000c03183c2c207071501c2d007424942518101000401c1504005000050500c01c0b1100840c6282c0e640d00c00410007450340340c0c00031840300e440c2c560081c41c801d0518003040d595400c00f9004640440340b80110000c0e20f1145d0080c00703140342107081d0040524000390184403640000c010301c141e86500c485030340700d1941c81d000040075581064000245403442d0300c05d1000c0361040040900100b2411804000308a4591070b80200307400e0310b2810400024444c030351350000c2a0668 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 279576402 1250 279575152 279575173
    0x60e0309090f0a05070809060604021605010213290304020409210906080105010903050d08060402040909060204030b07022a18011403010c021b090c070602040308041e030c170f 77
    0x1000c40883c40f601d40200c1c14042c9440d011740c103484003142682d03a40080d410450000381103003025406002c405412a4242d00400e41c1c1d034482c81d003281e01144c0314220802c105c0500b0b100122000c0d0241c00c0d60341d1052030030318910300c64001d04840c03800058402403246031107503403a90501502c0c1c92000c0e091060101302c2d080c0031045d400c01074803200251240b100854600b900000d2a07601822040045a0b0440081c084240160000712916100200f0031507206070b003413002042050303040c4940c12945200f04801a640c900b141000200c070798000b08507104640c00134821454111485240400803030045420106aa044a00055824560250541c0701d0556440001804c09840703d00160001003a00200005940e6030b100700d880740441403501601d41211a5000f04900707240030150b6200300a00d030640d081c503c00c0d0380d03440141e920540c82a903d41d000810140640d0001300d051102d888911407a003941c1d546950f4404107403142c0307486480f500b0364410400080d0144144031050241d2008819208070105 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 279577652 1250 279576402 279576421
    0xe01180309120809091b030112053a02190b0a1803050316020f070608070f0504080703020904080c01061502070605070c05090c0714070302120307020904060e030909 72
    0x12052060303001038050746002524048845145014a403c10080d070303d42031100b401e11821002c050300b200d03001d40326100c038010010f0b084009540130306186c3c0e44000803032100307040091502c0007154014240b01110b506072106001541d400b0200d4050030034403c0d610703000d1b8a00c1a42030248941c244261001c64101090400c069004200c0c0700d910740c59010403000c0000f051419000c4003052006003c81c100300b020500c0340080100031300950813a0710444d41008040040c00782402d06079441180441d500b201808840b0b9006040c8410000062419a091074a000540d684d2501c641c48040e00171104400440c3c140140c500c21034540c10001402445215500e0b1288034242e201101110b00501855001007503462080d003c03191256040070440c0c04007810602082501d1502410320424088100032510003e041181c3d9117984001c0740000d042d1042c27030b500501040a41a0031070b440c00307400c100b10440050347c075107038001c1c4c220b504000c4c00242d103012402d159245115071909281d1001125041284002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 279578902 1250 279577652 279577691
    0x2070305031b07020f09062404030b01080d0c06053301080a020a09170f0d1701050a0b1801120e1011030732031306060501050c0706030f0e01 62
    0x1408260484459104501c031070b401c1c011004003e60008010030b0700b5a40b86010001c854110100130041c24032400c40c601c480840340d00311070020b41c600c1000702d81041401100640300d401014100302a04c42008406401001c1c0d03821050010301260740d80001c515405c00c0305500705981a90301c96800f202e01d49803108502100d100c180c0d4a4001621940020322203200d42c02074802d071003242d0b11880344942c10311080f8160100b814080700924421075441d006403172402c20404030310044507100d03250f890242c2441c0802c000c405800072402544a084104406007c403c2215040d601d81d94031600c400c110f0100480d03180d0f5003200303c6c03c00d0a0901002201c000390100d02020404c84070141005201c1000f40078000344d01007120351501203040c51030402401c01142001088001c0c00d4843c1d2001c10300e8030b5031000400d0300203039608201c024541514804000142c8900780c045c003401d09004d820040b183e00500d50300c4501d030090030100340d1620000f07092039103280c201c4000d107001400240001d407813443c03811a202c2c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 279580152 1250 279578902 279578911
    0x1413020a0503010b0d0807060f02070b041a07140d060302101d0d0812071e200703170c0a06090f0c0b03090304030807021c050601080709050c0301060e12010207030503 73
    0x30302600d440003900e031805100d1071401490141c51440c0311000382c0c46080e219089540184d44450f15581c41200c1007441d480180a907e2268590010a00f41818583d1004551540380c400001843c8140070506411038080549807050300740140d82c4000d1030140c1c00103081d540d4002034000080c0380510b1185c035000007080000b0b1101c03403a47e0510440038030400001205450025010910800c02401070113426810f00358401080d04101221111600010455a91242460000500040c0401c40078007120f6102d1803841011300040c103c02c1e0854488920700d6162198034400c6c1c0e0380005014011100a103e0301038801e4201c0c504003c04100740c00c004030b0355212903208440c00381003040c0218647c0385540076280100407400056047c1030455844480c41c0d48005810380e40103180204c8068401c100e0703107410900c1403040c0302510305545000d48151030020103030841e003002c43c10b00342080f5a8092680c2940d044507000d24003a166580e0141c04101c520410880451855000141c11820300d90400c0046006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 279581402 1250 279580152 279580159
    0x10606030c0e06040501050919080c0a0501030903080a0b01090503060f101e0605030c040302120c09090d1e1e0305060f040902030c1e100c0c0501020f030f0c01141302 73
    0x60751803400c4111100c0710311208040e40654184824803907035224002800a850003d4a020385041d441444e054160480341e00c00c110b2580101c10964141c01e10301c1d4072000030b08003820300b440121025038000d00244c100034211240a55103074440b1400e0703072080d52500c00409002d4184c507031790f090280b80820903e8048605190b500340e01040007a0000002401036125800c11144100b0303141400300441d01688003030003080700032000b8000800582d0300c280c150f0400100d000024400041c20005121040364001c0c5850196080454010311881d04410a0000f40200303690140b044094243c0035203840d203e400341900300d0980300800f409004d425078005c600410007120360b01c40d140c200c10300300800d468045400a4054120001d124203900b00000e000079105140341c0c910700909000c20119401d40c046031880710010f184034903080c041c442118600307009808284007816251031040a40341d540d200c0c105c6141885440000c811411030b80030351000608480c8511414254242090202c4d980307210389405034030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 279582652 1250 279581402 279581411
    0x141915050c03040b0c0904064e0b061203070c060e061c05040f0b07020114010b0f0415030b03011409100e0601120212100204080d080105060304080c1e01060603 70
    0x200005140c10b481c400d5910611105007580ca0b8170400b0f42e503030414180301e80c01035121200425044201c070b4824028210b0880d50745161030844ca605004440c80032100305c440010704a594031000d08100e41075070712540280da41080c503200c0700007195a400100f44180303618040820300750304002400f1648021145d0313943d5410044400041007051a11468401c00210b00f0700b0042e4000000c069001554410300070070000b400f840003912040080003041320b403480180d55070662401c1300c3c0d01c0380d2042409800d00800d89400d01940701c1ea14892489980034071001c0da076001d040007181c548290480c5825400c0500244024544d034031289407160411f61b8100d459004008640d410004035106000303155412000400490342307071180d80e048400d00c98000340d8020201c0011107500f0201002060440c501c04040182c0e1545014050390a001d601c54450040010090040100740d079208181d0382c00540040189984001c03a040140ca040860382c4101070300110041d00030040b01040d8401406c484c000e490502 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 279583902 1250 279582652 279582661
    0x170c0d021002030f070f021e07180209031b1201090501090311010b09010b0c071e090c0c050606150d0f0902100e090a090606050607050102090a090605010c14191505 72
    0x10036030000301c0c0c24441a144040005541031b115990308296000b041c0142d50341201d120141007891401440c0d5440c0592014000300b1040155554030750780f103803200340114108580b200c0000d4031407070106040b503404541c1007030030445642c03036110001e41c1d25104402040b04429500c1c10700d01910703040c0c1044d40070600f0184602c2600b0018003883d0f2210000400d05940c5a00f0100035072010382203a41501441d100b4a80d0200c0c001c0c1d19084010003481c25001002501845c2810403c02e0740c4e03510743c00008120104543f10001180003a0042d0010412a80c0412074400c003454080c072401016044542103080548005503401c03181d002c0d41c4464026100600200300654041e2203200001d22540d070481e503540c0010309608030301d90140d14401c0c410b4501003030a0390703602c001401c039800a01c4207898031303540010785400528003019000001c1440c48018045107181c0310018014602c4041c01514410381c8000070f40c650780341440300b80030384821004442107441d22402d0585030a4000c0c1c00718140c0c10b1412003c00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 279585152 1250 279583902 279583933
    0xc0a11010e01030b090406050c0d090f0b090d09060e0402070803131a060d060902061210150801050108010303180803031008070e090c011d060301090c02010c0804050316170c0d02 78
    0x44c0c06040020348002c10300d407290b549806c02080028400800310703030b060195903106d0b11140582160240a203185005400c0d890821140c140006412010154803a0981c5545160810069812a410350810603136078030004c070118000e0b00c070300200100155800000c001041b581c109104407074501521039484220685491179088107000d641040e071000d0030709010000200c22fa041010103500c0580110b080c00d131086501c205442040c0e50309806085544014803882106c130030540b80501e164500100154074250028221420602018041000d022181c0c04240500006080207010302c03012a640ca14140c03114101c020000e000d0b968550040a1002072208901840140544160300160264026000064075482e020070405482e06030659850300aa42d00d20340030758006e110014001c00c10440e424002400c4582414941c010b0141010a20001c180d0000c1910b106603200c84103040100803e0500e0880b124815011700c101d00000659810544004180c041845003130390200c406115910255 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 279586402 1250 279585152 279585161
    0x50307030f020606180115030216060501052b0b090a120302030106030b0307030203030406030b0a080d020d0806010f0e01030f0e010204080a020a0b0a0c080306060408010212071806021b060c0a11010e0103 89
    0x1500007041c281801403280049506040c7e01d5501c0c075040051801894166444c2018160f860540d012541c5800411107805c02800c0c18600e20142c507081d00c29259140c50210005080c40030140c0035641401c0001c1544c0405c00400d00c003980c002296030040440110001c003c1e6009008940c0041d0030920045a981070010b414030940754002c01450400341041d0f021402401c20b54440c4c0e52101010f4000200351a09103c5814030841c10f038080c2803401d0b561170010b031060034041c20081c1001100282c6030810342e404a002a00000c091034003181d07c40b03028410a000d00440e12904160703510016001039111000a90038030006e109480c040d003144d56400f1640d0050080c05150004210800610000119058011640b181c8010441424140c0b07440c5101d00b26004a5940720703200c5200d41c00d000015030882854810208042203054440d410000d0007900e0f5095581f0407000c05410141031b034003d03502c0b04150741119101204580703010040e800d00c050509400e850045c00301341200c409039202e5200303014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 279587652 1250 279586402 279586429
    0x15040e070b090117090c1c0816080d1103180304060c06021c05010323010b03100b040608030307090603060501141801090915050406050414010e07020703050307030f020606 75
    0x901400c5103064031281e00ca510024500f41040f001d8920040300d1894810182d00030500d140c014015504120300b880480d000c540d00f1a4414650011050300084045040769003c2294100d103d004205614002c01503010300d2442d001280c1c01d08101c11400403904010f58410051661007400c45181c02200341d890384118084c240029921940142c0802e016400800502c00358807400e007611303126a80c20100701c810a800c00c580020061841c55080780741c1180541146d8080d4000704040304200000a50315480d180d1a807262079180c00e80c290107a942c5510038002003036001d040d80c2e9a440c00702001460710140b400f8090120b45028408542d035413042d000001d12164440300c41d450b040d03040082d6031510b4200304000d410000c112a0200c0c4c0030995008079040c00022540880a160411041001341c900a400030390007185000d1600f00300407030f02d0b0141411105004031244c41030b00c0d0b410040382424100e80014003103104c0040c2c2c241c04c243e0300c1905416404995403d45066460b80810861000c1d02d0300c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 279588902 1250 279587652 279587681
    0x40b0c0c06041401180e0a0903021c0f11030f03010902070b15030606060d0e0d031a03011404060e070b030705030121030c120210060801050108070b03090d0c03030b06121504 76
    0x2243c445540140c910f5009008040e40034402240d64030040a10380e90100e58809000ba10b50310704a04060f01040041d02020529460b18254803404100400e504035040042c010070007442440c038011401401110410305514440e5a03807980c40f0000040654480070084446480c590700052140740d0544074150034000c001e000c0c000d15240e01007004440d4000521120718039a846040f02c5a1030020040c50001f07401d1500d000c60702220544a110f0110301e803485190103a410402d03070842d14054040c1e8507038480d5110100107118200c10b184145820b800b50418800420004103014090307030000c020354100d500c2d500c01c04900d6203044401e040c060640300e02c020041500702c0e8200c1e001403000807400d10085d03043d10449207100c5c5102c0030003040c2e51050b40810550703550790313005109420003408620060014440710354511704002d21415501c012a070303c0d4008006010b0002d10030503110350040700702c401000b060180c032514041000800003406680300702e0804a91806940c160525000e001e45255440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 279590152 1250 279588902 279588929
    0x1080c070b01090c050d050405070303180509012603040608010509060f01020309040504330c02010504020d03050d020d020d0e07060f020c011b02030a05031e1c090f08040b0c0c0604 79
    0x10400708054421104134505000091203001a0000716105403442140108020401c0c0c0d0314504019000801803c40c84928540111052003117480d10301c8490b0444104880c0e08170902c0d10b1384200c880001d417007461902e107030000003000503031240c0c0300c201141644d07000c41c1c01100079203a1004208010f58035003805400340c0c1003403060181901d4903501c01030f4018020f28008803500360711005a0034940725003400c040002c41c0303441c441d03c1c6076807244160085d0060b5400204154102900011801c2071108001010410000b40400c500105a01070754240490140c05540310301c0204e010ba000303000e40009421040c8148480050f2081c49901c04204c112030703640151228002c0c0c0401190510446104d03191007104008041005032003c0124611107805603003d1900d404013525041d0007100450401120101c0900c0800d00e03120140080b041c000019400c00111003043e031500d00c010103a0080090404240440c1c0011054140780050048440d00c0d01964061604d01040001d0390040b800f8071240903c1c017 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 279591402 1250 279590152 279590159
    0x4030903140106030c0801020a03061703030f07050f04090b100f050906070606050d030e090709050117060321030114060c032d130e0601020a2001090801091101080c070b01 75
    0x10001800141d1450000818010b889484401441c6816403200000da98000307081c0d485103a0501c41d000113801039006081003070000d40042c03943c9010151034091641c0206003c580310740c0c0917404841740742d20400349541c0c03103950321008480180100b25502c0c3c002c1c0300f203104030249203205075850140c40c003207501d5413401c107042881406a143c0040b68121507a9503500408030b020754900c0c4150200d140b09030ba0322441e244502061152454001e420300d0248583c00741d081c40305a8011403070070000540104402059030312040000e1505d5101c40e045079a2006203080680002c90000040d41601c00d5400984005070b80310701480014800c0c4082c80951741c00070b0211107225800e01c00c2c1c003603005e94800c148a2180d400c40ca4072a42035440030f50a00240c502740071042150a4544900d658020700c01d00290507000d1a81e00e50707058035008200e03801d100000c0040c16001d283c3c020801c04028140c01402003181002038a04030311030314800b020803804030f4905000030b52070850000845107a5503102d40b01031070f542d01e0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 279592652 1250 279591402 279591413
    0xa12020a21120c121401030c0605030106020d1b0209040606080d0e0a090e0102090a08030909280b030715030509071a0406050a0504051e090a0213030803090a05060709090c0804030903 80
    0x54420404080055400d004c0300900c420703010b081c0b80314503982280d8486501d1407802902e404100c0e4400400c2c0402071004024564010460f4100c0d01c00320b0603d50907100c601054000070304805000290b121742c001043c002441101d51015090301c642804880c6030841c802030980d50a005500e450fa40000c0164050203211040d03001301a28150740ca001504141b142d0001540c044481d8110703080550002c101001c2901e400b0030020780040718640050004a10380343c1142c01100d65020030998141c0300c030f1144110303032000c1100800921141030040610101010001e02900003950307001c045200341c190109968031f488003481c0f407684040031260300c1c207890614103555940204901c40140b100c11b1000045948035000ca20001000d60407242c01d14800c0e450410868101c0030f0b090b000310034810702500f03006480e2054140c1c01c1c1c035000842c05407642d4413450494134080410304014040e014200501c44c546405c030403400c0903521031000034040c699044c0030842380300100f1100640000c890207000c001090 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 279593902 1250 279592652 279592661
    0x3070b04120602040e09031215090a051305010e01020901081509010e07030e070e0106031a15090f0409030c05070911040905060f030604200603060a0302120a12020a2112 74
    0x14802c0300003508043d41d0344108516030b441140c01080c2a0000110980d810a0314804140d00c100303c00507000c600c0c014079000c1031095400030030003441d083d030368401709030b00000b40c07036104103000d502c54005d0154100440d080390107900401034540c01302d84031002040e03404880740040521420302401d2081c0b181c0ca8140501100c0b54041c2c10401415650100701100050500c4413001411403907200d10000d502d00300c802021128110020150f14104c015015040d941d02100440c01100101c00c185d111400740c0002a13104401c1d111240d44030749028402000c268000c6424042103015030152650607940300380c1030082c0c0301401441d50041000b04814882030f05a80d02041e044900602084140403550780401c0c98681c054805903141002c1c07042069030301034116180303289500140c3c0e0080c110300706000482d002da43c050100901c00c02108a200401c84401c000c0b070290144c11168829808288040180d100e50740184d040e01d56485030401c0000341c1c00e0200c6a5010448142d403480042c003206c002040040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 279595152 1250 279593902 279593939
    0x3080d09030c050d091706060a0e22060e010c0c15110f180a06020f061b070210170c03040f0b0402150d0b0f01080402090a090f02060c061503070b04 65
    0x11102c00303048004502c08025000c030344c80030354840091107418150160b61052a016030003078030f0750001c07041082640701c1021603001c444800c00c0141003512440d40d0246e2404980e51000040d2203e11014414400039400c003c5c13600c00600001c12a421f82d18008403880030380d458001e4041520614140c60650455108403042611225050300b0000411810250383c7e10080400e6000c0311000c80101044c038100120744020000d13400204031440c0280011038a81d20024042c124404480101c1107004401404581000d0360040c841c1e001c2c1503001101418800648029126000c544400130340c0707141700101140d028581100344058120300b60f50700c540400f200140200d0700034009010300714603005907034003900c024082c24801103a00c11a810600c038030345d80d512014a04220042c4103000140c0c0b81d402c800e50b00103001d080c0100700e02c803035414032220021a01c07030020b40080b00021046100e00012071094028130040c6602c80e025491181050340d50a041d00488807100c50030031003000b00280c0701038840c860 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 279596402 1250 279595152 279595157
    0x30a0318080a0308011205120307022113060e0d050102120703151d04020d123c080c090603010e04060f060503030a0e010306030c060908060a06080d12020715021306050403080d0903 79
    0x141480410f108401c0c0c2041c2c5809003d3303030200c090365036107980380a51400303040c00603040c1500344450702007000c4010b8100d1007104140040c90600ca00c8a4550700d2451019981000c025950780040800381d0412581c2100c4400000b4946200c0301e450024002c0c0700c00c04c0352580c4801401080d51181d00f00344850001e44100c2e4404409000d1100040094844980d464082c2e10b0349141c9030300c00e0a060181640d0b52000198140d40d0316000d80b402200e0582240c1e070248145080f80300359981101d54072841c4a1036442c20f622a40120000614980d03c2a925204610901c000d2010b004120b0010059031214000d8a5158000b8005400350512628102c1000720051501150309603486d11107070000302c00b03030304075034001082080705001041d01000102c0d00604001c4040100d80d150100f11303601d45070404440402c014840200180242485d0180d440f125004403580130400d0300c1c05400d40096020f8200c1c01800345400030b0000342e00303008a01b62012242c002d261546001b94580304000200320001d012001e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 279597652 1250 279596402 279596413
    0xc0a050a210203011503020c07120213020309070510030b0a06030b0f090a0c03050603070f03080d090803090d0915050906090301060b0d0f1406030c0d050309030a0318080a0308011205 80
    0x32040100340080c0e01d10448820050342c035414071500130808080348410105040c01004501c07250030000030381c501115481600084081d4051000402d00d01c0100c21206031140040240302c04100f0219100080340c1c011503289204503c0d440041d0141c4070f990a0480d40320048800030010300d4000d4000c1202003900400b80348801d500b0000150090a041e140485c802d0341c4d401038243c9007901840740c1d94210008500501d180c81c64228000c03c143c020b0300000304200d0001c41c02010a0f805070b0000010750b540407120b01e0300d030318091403484d6454107490780c031b0000a80712500000b0280e03402e0b000303070824600710b940d03691800081c4e07014403020341d02c204e411a03010340da200c3d00000e24602e440054202811083e00c08900d0000864580003500c0e07030300c41c0301c084031080f100070720600340d800052041004030b058844205251041c100740f41503000b0700b044a6011300070081071104065015041c1d8241400c120585086141c850204590355a48544001c0c08078000c04014002c0d524200c0c0c80060b80c6125004448 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 279598902 1250 279597652 279597677
    0x101a03190f0e03030103060b0a03020303040b0a1e111c05180d021005120604060f0e040c030606120611030702060c160606141f0e060d0b0306100303080a050c0a050a 72
    0x440d064150700001d0343c0c0000c401401000854007506500103000c55034001a1829500066124440c900c520a500c10002801e0103076140200700786903001444031000d030321007103505801034040c41700080081524010440d449020b00002c0545107001c13641560f0792420450149442da031541080c94585900280703610844005036a041340c4a017140c0a140d84081d120700b21000009219040900014030583c24800c00307020f407803801c00e40d60b0116810461403901a4543c0c0c100594819555003000d0451418180d0105001d1850141455580d00c00e60040021054210350f9040c240402c0e0348560050300320201085c25a0043e401801c280c0304144500a070b940c03221351300d8404940041d405402a103800300e07410940c40c5000d440c80c65000036080c481500070032181c03000800c6071001c2e81c4014401c410116400582103110741c426040090b000c2c0c1101e0640c1450076400400308903512085001488407030004a00450310b00440d80034045c0ca4149500f005e0302c8070400d64030cc1d0045c1c5542c101b000458803210307 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 279600152 1250 279598902 279598931
    0x5030c0d0302040806090d080a020a0e0a06020c012604032102041e06020d0e04021b060103061a0307080703150f05070c14071a03250503101a0319 64
    0x508210040e01c005076103034600300046003400002031048002c0d402c04121600c100b504600c070396500c0642c24070b005903039a412a00503510801e94200083e04240f00d00d40c04128140c0016103030007849802d80700c51001c648452020345081c0c11200803454205210004240024040c8000200b44a491115002039200101280080b81c02581c03010161070f40c12114681c14062020800024000e036101400e5404460070f0042c1107a1a001c080c40c0c015135000440303040c114244110301840d03070a10b0302500e0750342d43d5070300740080a04800304449080c2c0c5066040324940b4a4001407001c1181d155001529a0503c0e589652240d0600111b080800c1c0d130304c3d00c0c24110802c45901c19a4400d0040c6d07240c0c4001c0300b109041188060303501c010060070380c0e840340100f4443c1804459244e0924290410603640c0c968a410380e0300011514101c54104041107000408513030764011019510a880015941d000155a200300300400017000d40c4880b9100c4c42000450351004181c6c04406184801100102e404007604104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 279601402 1250 279600152 279600163
    0xd050a0b060d0504030e0d120e0f03250e0103031d040902090c03090618070b180319050f010b010c0605060102010914070e060d030915260a0b030a0c050d05030c 70
    0x503252003d40d51400c110805070070040e5101843c0b001d84a40300d0800c520765130030886002d00303046507051040d414040181c590395007072668821380c405420307614007001c0c1c004410a17039103040b898042c042d45040008150748101380041e9040300c2d007643d80e50700b0700030713900301241000c1d01c881d58201d1700503403200e003c100580c88002c4000d008000080c0d4003a80d07483d03d5801a41083c60103013010607281051100780c0da65100005601054820201c00150ba4420844031200c80688021706150903000d14009204802da610020104107401076003507034882d0705000140c41c203e03001c8190550111745101d408102103919580880c0e801101800001740f4110903845412800c0b040400b05003860b0b0080d00184504400682d0168000070140c42c14020407842d5903001d0322404590084260500200100d100031512601309580b0b4580141a650341203084103442580d12241244c5070f1524604249800700c1504001602600e0b040e041440e440b503180c1408200088804140700c140c985200034845200e48400c01d020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 279602652 1250 279601402 279601417
    0x3081605030f121003022101230105032803050c0109060f0203070f09050306160912110103050609150f010e04050f01150f0909020a05072003120c030d050a0b06 70
    0x654a0f1a0f500118103240c11820080003a810b100030144100016144c10a86c07074000c80c0c481e984041d000d050318200d10300421141c84460034541c1c1d100c007003850544400000794169a0260306a84005015840004a400050005034001d900340e0b00303c0130100b84104040c00c03045040e81d0000c103142e11750ba251803003510044040c0644055000041c4811103400c0300041c0000481c03400c08031621850040003a03114070000781410072000d0110f0300c40300c1c01d41c45000c00c40040d141207001140b20305018200310f44221890307044140460718040118143d480d110071903610400140e40c0710420050380c01e00344000c2c1908001c0d06070511840301450b162565540c02810f1169a043c02448034541c9440341c4541d005404900b10000d1020800f112040680c2c0881e049040e10841c20b40540d41d6808444101c0b4a0312407140050301c0e40f511828003112846142610020fa0401201101c90720340d055075144220f841402482c494a5108118400741500d160300a142d10080346080002d40c1115817010030703881c1d40302c500c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 279603902 1250 279602652 279602677
    0x609021305040506030a0503071101020304050a0e040c06050301080a170d0903081504020f07030e030c060403060207060509030a05091e04060f181a010804020a0b0d06050103110a090308160503 84
    0x10702160400f0320607644e00c110200c00a019086054646a4980c800d91a0190070004d00002d480081d9000300f04540003010050030302040c06680340e6190040f0401550102c1d209005980c0000b01070b4814030680e8180c42c3c02401424021015030f41b80b60b071340c803000c1102980c0884180071049800d4070758030a100026000340c561642c0c2c1e18041c190b115185c008490940d101d140b040c4179145074800c0d03001c240d9040c1681824181c02018950780002e00d030501210550790700800c0064084204540e80c3c01503c26240700c0c01c02071005d901e4000a00b074880c06913482d103c000600a01c1121034510300714050300750403298001c0921240003204086019240f198102110120b80b244040115240f0340c0740581c440a4800400c001200080c042d500c2c0c0b5401847c0c15070304110240000ca07065581e003010170000bc14100060680c0e610850000c00e003c0d108a10072035002c2854407503030365248032840088510103419542ca0182c81421540c1c2c0240b580c0003006940304a40c46c0b11942c0000407001c100510303400100c030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 279605152 1250 279603902 279603937
    0x4060f0c0c0e0c0c0106081b121906020715050402030d0c060f02030106110f03030705030610120903090609060215010902030702031309150501031b0503070c0b0114030f0a0302030a050706060902 85
    0x4c0c0440b400d4074403d0380100c100d98400c800110008408001c02180c1d03078000c07200002e912a01410351403405c24070305030703460540d24840000f000b0000203500074000c0710700c10301d41e28600c842c4400041341150340031500a0b4258200060f00160144120364114850707102e49000241000c01c0d04100342281c200b40c100f10081480071148401201e8204550714038146440c0096195207042540103009000c007130641c5028140b6000e807907001130700800c8212640d0540d20400c00c0030658500b4000d0030071402c0d1042c103000c5079014202048081c8045210440312000b485038806591a01d4400c100a42c0014403040841c0014008510f40040c002403074001880c002c85c0c0460704442446403280c2e98445584001e040c50b18000c4648621b45c40034080400d11502400c000d62039546c0c00b481a5004d4150010060003130446800216140315100340d5044004804d4041f03a0701c0031140d02c131403031f5a2031407100041c0c0540d0051081c00e56552180c001820251703c180d0002ca2080d5036440002c0a0341c1004030161000201d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 279606402 1250 279605152 279605167
    0xe030301080723010e01031e15151d0a030c0f0806010b07031d13020708040f06020c03071517091c02070b0f070c0302090c03090c030304060f0c0c0e0c 66
    0x10031180c0090403401226070004540c3c803d00c5840440b1006003c1d041c40840340c600103441e8000da010901c1141166251005c1c0b10642c04140014019840c002c038070035010300000300b4040008104400080c1094503204810658900e600704a502441c0c0441c1d40404030b5140400044e21851600f0002e00c03902a022030785c541043c4101d42040d105800a10b002c1c0001d00166001c0380d4031141200501703291210000c0d00900110108642a82e041103100410340002040000c0041a01c000d01c00c680606038100c0f05251180b000704d0b11003603030420300340c0e059004000030b010705100f07200569002c400360b041c19036407003d845400c1d00744084120f50709050781c8c201700345460481c43d00389113040030148648082e003481370801802004030b004070510031845807400b1170164100140000501c001d10340040c010341031881e2840c0c1001c102c0e481110007000a00400803019070600f4000141d80c20b460345e64807a46020120341c80308503900b103101c0c103054070040455000000c02e8080300031014003840b015007100e07540d86034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 279607652 1250 279606402 279606419
    0x2030a031107060c080708030a0e0105130521040e0c0903120c0c030627010b04060b040305071d04080703120c0e100c11040c20030a0e1002071e090e030301 68
    0x210398041010300c410010142e0025002c0340c102c40c140c2d5030001c5825101c3d221140030000600d1010070f2240ac40d0b20704020311880300007000f40c0071201807268003100c03014501001d9034290442d0031001110042410300043c42004200700b1400e61210a2000640c203000051001034506050700131040136600340046c1c00f100d000780074400700d1440c4d2410341c02001135080c0320020007442c03a84409440e4860034015403140b02080d003034100301c86a500c010800c3c0450340d2520b00c18080c55005100450750780c42a100009840c10501d007980c40a858000c2c103241c29540c1d161603652003603002c040c0c100c04000c1500703106c0111003140d01c036007150181640c2c1d40742c0c042c081030b405010294071000d00700424031846149030030001e162803801c02220b687c10345010504182805060364180d4040c3d10041c9050004034102011140c00000b900100709195591011032188109000c0300071400b030760722801a003050f1010700c0540c60825040480d40b840309500a58942c1e21211001100c00e9800c0480207908000010060b844 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 279608902 1250 279607652 279607663
    0xb120d030605270a02030a3201230d0305090d0605160201020702090105041a06030a1401050406030218040213020c0604050607082e030b010902070309060203031b0903010902030a0311 80
    0xa840d03070080040d030704001c112540301440c0145946155a00040080d80440150304680b01c044900c49410f50550081501404c00b507244803140145807651078000155500210b0350481c0b010100ad00c0d14a985142c142401494040000181d0a210080124000c40d440380350784881e0140c020400020141415002503e500c1c0300c1c0303100c82e421680103001c0d0001603515070031541c0c1111001c031000103c000f4a040c83c102000c00c00d041c4103600c4140482048101c007204d820246100c10203007da0651b45c4c0c1c81d0310410040324024003019400134205a4200155140500c10302d0b00306000802e010100f6a04080c043c003642d010301c1f810b5030541c0110041c0420443c0800080c0c0d04030805003007400e00ca1400406c02551444413408820300c0c201e6035041c1c0740c40f0003000d500c203101458012104480640e11150300e04007030752006004400040c04403400044540c408010740b1701504600e503032903031082204280c0c03000d16000b003409603a05568405010005030b4040040142c03940c4030b0b4035080045c0f41c1d000c51850404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 279610152 1250 279608902 279608929
    0x3050901031a130506030a0b070503010303030b150d0b03070b041403060a140402090a0e061e160e120705120717010c0f121506020f2a040b120d030605 66
    0x503188422009240d603c22062074808100c0f0381000030700e583c5a1000901c1d011302d1000160820070b0b83c105000f4141d50200045040ea03000f602c0034402e0000d0036003441482d000c1515481003020050050328114800740d0801109148005c0c12190341949680011503590700552000c0700150110b103003030500c1e0505100240e032000200804001d10f42c1e00d0052110900b500500c024451802407002441042003a404004035818400480c2e5403132518050f42116058001441100e40f101280042e071441750341c4080741484006680c0e21032240031484284410300743d0128500035140540300b000b14090300e40c51a1920445005001004d500345001c1040c3d1401c440840ea040c1c191f41000441d050594103d460502e000500c2e203032115140e0200d004207030041c900b2004414407000742400008072141e00040c454801c60f5501c0c1170b5030641c02c007114085070006110b0081220b4000100400940385481d40c451607030154003900c040420000c0303000260601e0522032072040425641d40c001e012608051080d034445 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 279611402 1250 279610152 279610181
    0x31f06020d180b07080c030403080d0609050105120709230c09010e012303060a05180103120905010804110103020f0c0303010906050a05090406050a0608010c050903010f06030f030f0512040305090103 87
    0x100e040030360f410814070800b40d0180100400140c2c0030350241040003100e00039508401c806840d02110040c4c48040e0142e440750011160400c4d0001c01c051509000c007000412902c4000e105407443d007891070018004400d44031004600d070060404002e80e4090000e48910a030710070003903440d101c5030005841001c10704461810000c083d0096031715401000c050951000070201110b850340d0700c200c005a481e001035000b4136044603100c860082500b1076049400c0c180c074481c25030600b0744400b1010841d0100c6142c8225800600d0620200f008250100030640c2002d50614001d0301d000264601400203074040d9005c1c1c1e445910010040150398a24030a03e070140c08211041030400d443c0000068051070050806000c1e41da459011581c41e0303089a02c00700041401a000344001c84108002410b240c0003011340ca40254203102e10801031141034410b2a060303030b51000c2044060291510100d9200e400c81c4a408244101040308042411a04c0341e607611070f610030398070180c3e54412321000500b0750340b0041c0e20991 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 279612652 1250 279611402 279611447
    0x304020f2b0606080c01050d2f072303090105031e040309080d0804110909010f050c0703110106030206032d131a09061501020316291b031f06020d 64
    0x229070303a07c10211034500310030100c04698a1024800d601c080c00c032008580000c4000f24004021800c0190003500d03003180155007840700004030b44001200003220980c0360500d500700304000801580100c011b540c020005242c001c245600d00c54584818103000e9405074045580124200a40710041000f2405000039280c40b00241c2072542e114a004c0400e81c01a6100314040e070002a03099100350b000040d5945850b400b8403060526203000c0f862940403002c1500014200161140d4148050044030112603010f8403052450303541d04442c030354010840d042c0110030807070700c0600d603683e01c20300c441a40102c90341d8007000c40610305849d20703044003070001c1f20ba81785141c0c030030741040080c00b00801d00c5540082114544400f0441000c0100d0452090042d40f441e00750142c0b1500c01031041009242405140c00c00e400c1c6880030b440d41c14000d10050889202079001c40c606240242c0d000382002440e009102e10005600e4860842c03c41611503119411240c010703441400f41c0301030154848502c045100c180b400040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 279613902 1250 279612652 279612673
    0x81e030714030d09080a030f18060207020a09021306030e0a1a09030408060a0e0c0307031104091e060b04050703060605090909031e0405030d140304020f2b060608 71
    0xa49a008581015241c02080c044041c8561400e004403582d8841032002040044000d25240c6007036003080785610000b030704c0c00c41c148643c1107aa11400341034500c0908a03400400d40c0d507403200040d50060f04120381100d5820800542c507035542c0042c1104180074916802030b20b00f007480040446481d0440d58406070301c802245408140794401038910700701c440b40c0c00c20103a0390350003109281d03110b07907407000d2100e20a0104000a02c011503101c2c011807040482551041c01030311f42019900c20301400050400030045907030f9801898241e01030341801d441041940e0300c100d01041c001000c500c2c100c43c185c400944803004884580360900c2015406051405c041188904000300208540205d2125901815014001c03480c0c5107001c201b5942912560010f00070445091841307101d203070300b040c4500e500a1140c016501d0142d4003d1130700442c0c44005246903421176807640c00f04864220300800b0150441001c803204040e00b5910004054880402e004545010695180004c00c42c0d1140d44445000e421107061807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 279615152 1250 279613902 279613963
    0x21c0219080d14061c02031606020c0a0b0c060c090d080d0c03050612030405011107030c060f080108120d09110402042606060907261303030506090c0d090f020d060608 73
    0x400314011074042c1700b042054148041b9160115030340740c0d05103444403004002540c50b4006844800e0800540d000b42c080c1d50769000141c0103005890b09191160010000940c414001c40041d01c0c030420300400f16100c0500b9074880031450703841890301d520300c10307200e10000350a190540640d50700440180da08900b8001c9407440700b0385078051070288504020b01c0050044502100f0001480612b4118031410401540c1d00d0001d03243c2041c8400b0000882c843c2800000c100302d0102e6040b40c0c641e042580c6518056500b03240c0b0303000b400900000c03501c002c907403c43c07001140c40e20310142019288414101010314100003211440c0c031641030f083c64850348290104959a00c60f07000142d006042d80c00e1003140002d91800c01c070240100000d0082281c103451b800c0020540c410703240c55541700d0103074070704010a80325281030105032042102c00b88400c91081210010300d241ca513204810042c01821845205803042d8005080400a0314040d1289900c80720140807412042c008400706032250001c0010f200d4001e00359 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 279616402 1250 279615152 279615169
    0xd2307150f0311030702030306090a0212040b06010c05010501091505040911120304122001080403081906080a051507050301121205040504020d050a1803021c0219080d1406 75
    0x2420100300d034207421031008034001d0b041643e501854074062a02d918050307400039502e8104030762aa210340080c001184114540c1d208842e0407038401451411166030382d860b8040340c0030018182034100104040a80d012501c00c0c82071602903d01e0352030104208403c01300912034a440c50f000740b40710340d00d000c0c005000640c9400400a101101750f90790b2010802e010080e0341107008990050400d6031b00440f8040410450600710f10410704882e00726411480702000440344210300301d80040c08035088402082a0f284520902c05003a805030102003103858131401c40754100840c101d01201c182d4018004180340d0039a50241d942d000c0f85514055045600d80382500c0c404850000307011b44001851710019114510640440303000d40400342c400c8d95112420010b520080c1012902024801c1c41d108a4540c000307180360307444c800c1c260158000c100e0344030003007194184846c4d45d079218010351180b0022000c4242800d452550700600607138005482e04010020b20065071030041000c80c1d040d0442080100660302e04a5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 279617652 1250 279616402 279616439
    0xc031203060f0a03050d0905011205070512091e0c03100c090b0c0106360605010f030b0a0305150405060912041e030606090b031908090108150d2307 65
    0x4120b01c5102c82500407a0f8002d01d80e13007018140f4010320b0301e1401c0642d08026040d00b00c581c2030b41e600c24900c1c0b521542c45e045400a44124002a0b030030000c190100210818407600030400a0594015095420300811070300d000101c0c1441a401c83c22000000340b8090060310b05d00d06070001c00707014000401d00e00902e01c0195005044500c1d101080310601d019007513000d80d001d0645034400a5201680500740810984518240100314401c1500989140401e000f8401140c0341a103a214100012440903800303841f15080c01600943c0301d0b0740000108600304049103000c00c00f064451a51309041c00c0c6541003080c001d0520896038400400e090305400306d202128129400c02e005682510899016000c820300950b00241171281400c074041800c04281d030102d842c040c8124110780031701c8401080300c16034a16954001e000e80d001840340ea201540101b140c1907001252100040d0340d2031035040056091080f405c030076180700880600002d5a410030343e00f03402c7e18904c010000d00420307152204200d07800d0010817 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 279618902 1250 279617652 279617659
    0x20a09030b09073606030506060f1c080901110d080a020703053105190902030402030f060a06030c0602030705121c180c050d0b16110604050d020c03120306 68
    0x10700104018000800980381c00300e069284003041c10201c006000b0085181040140860310020004413184160740c100c82d80300e0041d080c03980c0c4042c10049101c6038008801c1d00005041c0401c01d000c1013103030550b050f25226800d80360f10360440c100010300d00801c0c00c0381141c060340310003100071655800201e00e50740040a00400369449109180c105c615000d41c81a090000520030f54070303010090070261107141e040d07030300ba14403220070760318001c011083c007840c06005c8201c41415800e0243c0780c1c0380d40055501078005811921005d2202c2c94152030300340d04845039800a03070348110500821100c5450840200000d1009500707180079a100c0310b85605822100c422800c0001030542680600603038005104d066007401044912039001c41c1750744441c920401110440d81c0044003080f24034108440c41d40741c5802c00702e501c07060364131000d11060351803403100b0b002c007400070210f10b42802400170040d00d40b165120780080c007402e14462402074030344440c00110034440d41000b204514410f030704e5402d03286e01100c100e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 279620152 1250 279618902 279618923
    0x30408030403030605030607082406071506050604030605060901090501030812060f0d030201052a0d1104030c030f0510020a0c06050c070b01080d09060207050d021011010608070602010f020a0903 85
    0xb480c041c0c004003c03d512268043c001c0000f005051030b00040c00510a20f40701a03880050201004a100f68600ea150300c69070206007440a800444c5400b001800820140741000889035106c4001a54540142c0c2c4210b4081c0c0c0c440701080303500c2c02c2c1008001c0c0146440407040c4455415a981c1c00d8650280d00e902000d055080c10000701e860fa1082c0140c40322500c080d00c1000800903a0800a0184c60300b1a61480c2e04002d14100b01440c20442461800315011071400d00c5c100349842c50210040d00d11034513080b4030b00382c00b0301001c40441c212042c903030000c5118001580210541d860103609096100d000b04100510500103001001d800004586500d50b1081d800909a51034604240c020b01980002604003100724001203038450f000266202581283c0c0c031040e5002c0d0360b4090480e075132a001e0081c10703004907024418400600340146900309110190503ca40c2000c00201103d00312441c5611858035640200ba0410560f0b80a03c983d8187c201d2840c409d5180c500411406888544144402005580e00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 279621402 1250 279620152 279620161
    0x301080d050412060b03010902040e0c0a140f131512021212030606070203030403051c020f03040302060a03020c190305090109060e03030a14070c0807030209010501081006050c030906120a11040b03040803 89
    0xb94030422119500800c10400311014000c41c5a07280030100500c0d0041c441cdc0c00010403041300b2102076511a41c80109007d0031034103404240241e002c1005110407190f601c0f0a0940850b04610741c4032000f80078941c2d0440c90070040c600400142d81d61010750001c180d00000300c030218a01406003200e0b807180d800e4403203e81d18a80c41c804a0300e1845541e001030440c1c010f200000d025031604030080fa10f950f02907404c580a40299004e69910303446580710081d07214208201c00055503000f84c024101d00081001a6410b00c0500320f01110980d2001c0320441c0003810010307140c0c14940e0802c0c0340c400505614903140d2105103458012a60700c1c80361800400500100000c8102d00600b188115410305501c01d42c0c6051043c1d40324610b980d25442800128031400c0c5000000c04c80354070968045100e048510703100d4400720702d0110291807aa001502079400c0d0701003005403508984034400204071040c0c80f2840d4002da85080d22888080710b400c08045442100f0800040084d2006003003601e800903042192903559889 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 279622652 1250 279621402 279621409
    0x1a060a0b0a050729160c0f060b0d0b09010e0106030510050a0b06040b0a08070f020a0b06010912030905030618031c0f061404051602191403040b0301080d050412060b 72
    0x26140010400c821613a10280141840d1a5400c1c00307501045440c565610b6205031902601d80102c0361200088020f82d07901c000c2030240748445d601c5401030f100040c0041004000c0b4040290a031003da4080880174184807100c0c10910450080c0303500764000704105d60441c1e41d480c2d101c4800b086203269071602c4002080e00714801d1b0340191204040101200d41d116a1380c60031060035084440c403403000c18417090000f140203014206015848600b40e001c0c01018116560ba000c2080010300391504000421700d000c86d580c0141d1002100940c0a52207a2520514010805143c038000a048048040c0c440342c50600a4000006807207100e8108034206180c0061003a1400c0100a1300c20075030360040c18003000052003076404907018641c80003900c09110341d66441d150b0f40c000400859a04005030b008075074000e00f403010310340907207115840b4080c3d51154403070048070140780d900150400c26110100200400c110358040000304101c04243c20014102031403d626800c1c4000090780142c2902d484190ba11a03668 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 279623902 1250 279622652 279622657
    0x11010204090507020a06060e0c0421051608010608030c0d1b0c150305070c05280203010c11190309060f022a0114030c09120a140a1a060a0b0a05 63
    0x22104800b080300f8500020002e546110340746050700c9040c94a100401e02948419540c0d100740c10011401d40342a1070300341002d0300f003031500d464100c1d05200d05880c02c000800901440b0045200b01d5540034680b410480c0c6903003110160780c0318500c070342d2003006030351801030007c40c40d5000360f41141031007008802c0c50b05030400c0c030944480004000b081c4c83c0402081e08501e110039003004031401da03010811a6180203050b115080100710180c640d6102c41e982e80b00584800503041e03074410048188124001c1d6980c08203003540c0482e00c6003000710342c1c820464110030108000200a080c062a040da031a040d00342c84c00b600a200301d000d403d0801058084c2410414020001e0040e10400c040315040343c01281601400d0050001200f030740000e907800d0745200040b071400e055a0085a500107050302d071030b280c078042022030413980c4030054050103925101b20110300041214117440343c91201820032403116140403c21500140d5182c1040007a4105021360342d01c45482d00015075120000d029601c80c6a03180546190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 279625152 1250 279623902 279623909
    0xb0333180706180b090f060a020a080c06010302010e0607080304060504230d0e100504052112070b0a060821190207090b0a0e0403140d0c020a02010e0102010506030a020111010204 78
    0x80c868030304000b0742d1a50111107640a1000564005800c9072243c0d60780e545880341000507a404002210100307814a0130307100422501c403517801101e000da286a640c3d44155003104000d021150002d90041040d96041403989144c0311040700c1d094070f0004280c0c1c485c2c41c64017002c1c00c050440c2d596000041d08002e050307800700031880032010450040407a55039009070b0710300654143c40006510b4507203013545030800b03805207044501261107041c10103040c042400421480156081e90590321030b14200303071a00d818400500b006003801a11641e404e42030504c13190244002e0b080d5011140703002c000300b040520129078042d0040480b140c00082288101c0c4c0290207010709105018050410040c05d005290005254002c0701c500e420240400c440942c1081a0704c1c2c1c1d24401c0018014058001034002841817030100140c4034440d03040350410283e51210381c211081d1050b42409139100340520b00a640e042030b1112003034403007440207103d6440e1441c0425220740c045003000f0f046c054611440041340301c0c00c2d01a500034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 279626402 1250 279625152 279625201
    0xa1202070516062c030304050a12050124031e0203010203090a02240f07030306080307080702010809010509071a07021e0a08060f04081c0f0b0333 64
    0x1600300a003003441e00e51508141d001c40c4100c0071040010194051000c0c00a10b00341540c2c0351540b0218010b292805840e080303600396041c0010007004c2410341e210a180e50161450469040001003e0700d4a6400c403095200114494617801c0c100b05801c403c2e1180c41000d90b9404020044000b401c0a602d40c221094120005c0d41540007200b0001030240000e014480603000315101c42003001e1041c02ca00c0c420a6000d84040300c9201041140881c1c040d0748014052076100e454002016a44d0320742450460300851002ca0750103400044503000d560344402855000008900200400e041401c1041c0d501d283c10700c0b5299210184480008504100c102500e86068010b0281081008850310a031100b00b4580d102901c41c40c045240880d004400181c214490b80190448880315200c0761141c02040c1c0112030f04644900c40d280e1300b520400018010361130817070160000850003c81540030941400b88030054101050088001540208101e22000002d58a8002681d40300e40703c601d5401d8070140700c5003a4034107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 279627652 1250 279626402 279626407
    0xc03071e060608061e0603030a1817011406010e030601060810030213020d0e071a09120f0d020106080d08010e061206041203060e0c22090e100e01050601140a1202 71
    0xd00f0840850b04d6841000d4032a68580c481d00e0280380e1140800060300d5180d055841400580307039041c040c0c114056071448a804034141e050340e66940705420f610310710f0032406c540d44600e104001280d0810030680c008609003401003402c412000400d81c0d9000500c900c00420068501040705c540c005840f20700a550003030486040c03030301d02401410207540100b203050091490100403204000c0c020518030260740034919800c0014103501500c1d01030341c21120a241d40442c10407000301824008002c2d40319401e542c0d401400c070b00300300001d01a007100e005600840d540e811001301c050503264400aa54192203c16007508219104e00c40401c90f14403040710348042c240f040c0310900c0b0a1080d5a480d210242e252030b07506010041d02d9095008040c8002d40f41041d45000034041c4035174281001201401c0680d01d103803841031003035070340060b5019038240d010028120f800c40c0c541c5018181160054401001c03001009004500300f080000348030444140c820035281401142c802c08862041401c401d0850304c0d48400d54 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 279628902 1250 279627652 279627659
    0xc0106210627110424030b07030509030409020c011d0a030e100909050901020f2b090b010303201605120303160c0807020312090909010b0f040f1509140703020c03071e0606 75
    0x1200a10134002034507070b42c030447c000031001e512900a580c03043c5507840c00345003440d01e4041140081c2d00305004040c81c3c0d540390001d0f0105650144a40d102092030080140300c2c280080c10060000303110100f8150042c025240810407141c2c01c6075095040700c5900344001016500e2100003402401903005c601001c210001c1d4040d8280011000e82a604030180100480c1e102004004422110410720083c55030024900400110f80140c080e07401032460034810704200b030040540c01d4100440d541c3c0801c9400300c0f0410070300041c142049241821038001e80250700c1c500748400d0300074012024000b180f00704000e561501040001c09015140c1180e03010342241c1041f042ca40114019400c201c09541c000e0300c5003000070313940c0403050160400c5014045d010304520300440043c00b01400d0340c42c1200e01e07102e03214054080c0000b5900840801010326440014502c00e0070b1840344c00300000902940c0803d1b00520441078000008422203190582c821900441d1940c0e800036580c10001468004d0001880c01c0c0000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 279630152 1250 279628902 279628961
    0x604031b030c080f0c1219050702060c121b0109021e01050c01290603070c110f150a02060709080d1d03010504060c0207080d080c0c01062106271104 65
    0x2860010188815255446d00715900743d01c01d405803408601c4010302520081031940e0150340280341550010b82250b262400c801d600034586a21818029401c240c0080d1050611040702200900076a09000074000801e160300000c0c000c1d4945c4601d507980102c0c01d20100ca00d80e008070111094444080020300400c4400c14250034100243c480c4210010b00021103000c1031710701502181c0c480d103150340b1122400c074101d840d40e41071000c0c0920760640000000398511050340d078211740140000050300090f583c2c0d56a41070001d040903409044041400f51460080c0030306080407400c0d5079114890b15014403000c10f00701c0ca89481c4030402c01d03900c0e09546050107102c24004141c2180c0145100c640032a0b143c1540c814107103070b031481c10922001c0040c20300d60204018000c4440104030550f8148004100b50741c9420314201c40c1d8010b4034400c501c100c015440a0b00300609806210715030240f0209d1441d004130740781d5421024800d60307071008140550020076840950fa030340e44200700040034844110090a43d20b13011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 279631402 1250 279630152 279630157
    0x90a021606180f0b011806081c02010e01060b040f1e030303020306240706060e060105040b0d140f010f150e060703030603080a02030c010b0613031e021801090e0604031b030c080f 78
    0x814036012a46c40103404000507078003d1008903030990004207051058150515281403c00e45070001315500d801c00340c40381c202c09000d02c030064464000502d60b1945417030440000340c50254400e5158450741982c0c008081b440000c2c45044a0705170030f0243c0e4958642002580c507000304000c440145050f04110030600c4210f9019000341e0340303c0e600030054141c0355488400400b00459030b640c0064020042030105082650140044e080e1485012580880030b0181e408081c600b02c0d000100710034820010051813448840000050500742080b10358600d00a10052605c4058521240120380c0054040f003018407c2e40f112000390f8000100070b0310f49102d2800291254440014040c2942c01c00300011000d00d02300e03045440040340c252000414501d5542c9281d4440d0302c0c080c00d8548a0307080c0075500090784a0320080c00d0503810210220000b507040c501c0d144c048034090468041e03183e00170001c1000181c1c01003900c0784101c0003018041800742031850200c4240015030b00042840c0c1011407055a440880c902 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 279632652 1250 279631402 279631409
    0xf07060f05070e03060117030c061302240706111b030315030c090106030507050c1204090513020d020609040612050a030224150a080a03020705090a021606180f0b01 72
    0x3080c0501d445403401260307946000721055515810040041142d640410000f1002c4851802500e0030070780129a43c5040c484200c1d143c00e4044030302c0d413140003145000c0782010b82924030301b1522018914001720420310740c00f80d40b20040c1341950700d00d030300140a4243c5090350704425064214100201e01c00c000103480303810580f980220f42107809694100e03442d0104002c3c10b038001c0a0030440d541e80c6086400c44c09024091310750002d00104104120f0344250600800c444458045001c0e0b60362490701004904072140141040d00c40c40001d407500300142e503050800500c1c141c040340c40c47d864000050000c0c0052009a10070510b16405400c0030041102c045241035140340a6000d031116a079201000c0350503402141c1e00b8040e1820b46600140031401d858142e01c41406002d0700a000507600d42c1d102d030b8609156140d046d40580e0102d14200540e2400050140c0e1090710010154141400a2915115480c00b440000e101c181c0395801101858105200d807c9a035810003d8040080013a05001102c07507802e00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 279633902 1250 279632652 279632681
    0x303140c1911030a030801150813020d0309091a090702060106020a14010b062205030d0e0103050402180c030a0b0916030903020f030a05040501020714060403080f0f0706 74
    0x94160104288000546031100103800141005010341446402541c0031060210352031810220a95580d407401c12103041018807944a81c1540d50601d238501881d000b051002800300300141c0b0030800c10b451a0903400c2784042e415500020724036080d00c2c042d5119082768000e00c4101b0319101203c2c29004041380e19580c581c40c00da030104c1c0c058941d9102261945070034002c010252340000064400100b17440503213901d82d840c2900004a8144000001c1c6803079002000c2d060010505041d511400840302051000408040f002444d840c0d1540b10040c1a2a0740114014185551b84002605544401d0b81d9040c09040c0350122803545d107444003160079550010340d11440290320b0004040024140041450b00031a1040c1031441c4480c403030b000850140580030030480450082040480d1500c4082000d001c010340ca45c0c0354036498a0070803000906d00340156000007603480d0012580702098a4043c12142540d4000c58150741d90351611003803201034071074900c00c04a924000207510f0140440c035400303200c40c5030000c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 279635152 1250 279633902 279633917
    0x3070b070e030d0921122a02010c0b100302060a080601030b030c0310021317070f060305040305030606030408071a160509090a0b06070c0305010b1c02090c1606020403060507090b1e070f0602130303 86
    0x1f01800c0f2062403902000902160840025030f0100341120715440d84544010203c0399025100c1e0702284c5150409403242011801f0b1780144042c0d9030b003600404007040d00603001096040c582d20002039840c062400d004085950025540c4810a0740d078034120041d10b140340503c515418000109581c5420a1080c0180c1010404020900d640f081c00380358000c84e05540c0392400d640780ca400700903040d84003400c1203884890400c41040055000d04000c403182c0d40d1008002d409180c04002c40c0e040810020903002040002c011000381581d5004409400c040a0440016101c0c04280416214031440300e000d000002d20b40c000008010054100c1d410310301054450440148030141d0760703009104080c00080d8001c000b400003550501041e8054588400e03540111000c0301b04a8584500300d0340280c00513103030355898508012006030003030b00788070080a11425092800faa695200725442004405400158500203407400030310842442d4045810340004085603242c20070039460702c00341807520040b40800d441 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 279636402 1250 279635152 279635207
    0x2120907060f02070803032202100c150207080714010e060c07051b0f01081009020d020c0111070b13030e12033103020103050a0e03070b070e030d092112 67
    0xc00c203501200c3c4035100030742c11929980c4140d6528004440c00d0409100b9031403108c030240e540e940c1c00c40315080e1140c4901e60420340c83d04101560245880c140328249004004200001d60008201c500441d08070301104c600e04000c1103030a0150910b60b0000c000c52140b8001c1c0041c80f0b02075401041200c1c0b0550441e0300001c4c1400b090001555403110481d845003140980c0c0280f5400b601c1d030243d000a5581c1001401902c0300310900480e085500a00d101e01d03030205108030a00c0d0240304002c50350361400a09810701036543c1d00c0c0e4916000080c55040001c0e04180c0c90410140034403419a1400c0e401440640c411940c101c0c255901e07048941145420b4002c4e40ca0480c2c011030081803864206083c4600344c0780d090540c0c0054026220140002c1e007100d07640c0514009020040c405450101d10690195405040003040101440b00f01441c0358400e17008910f0001c441c3c0d4011400300300f1620041110868a019001e604509040d107900141c5030801e03082492504c150320000200b4100660020007042030b15 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 279637652 1250 279636402 279636407
    0x1060e01080d080a05151e090a0b0a0f0b270306040b04020102010c090302060a030e030c0f0307151116050f0105161701030c060e03030409090305040302040501050d1104050a02120907060f 82
    0xa041e00c03131882d0b070211003c206c900b0342080c0120011400c0d001b000540050f0768040400c80d401e004544500b407540d41d03400c0a40303a9241290507a80100b000d01e0111801c1810000010160301c600707800d00d01c6200d408141d255006d03040c4410783d103003090000d0983d011842c05051280319100c0c2118100c0c0103500e018100d4a0590040c4068030989801415190400000200941c0100000300522000b44010b00c0038140c3d4041c104564001003420501468035802c0f285070001c4105101c00c0c042c50070704d040803641060182c03100c0540d01c0d8540c00c042c445643c0c4026040c10ba00b400300e1003460035407079403c000c10017041103804502110040c01d00c1e0340702291481004030205501000780401803030300034892410411188034000840806000030305803440c09030740b038801c3c004440d500b15048000c01c80228003003096140c07500c00c042c0180740030388804802c40642d5542522900351a0001c0388255600e40110b2000e04c0140d059072085101180d0040c842d0074240485a90350101d486100300050703142005040a030b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 279638902 1250 279637652 279637661
    0x30213021207110a0b18010510060e0103020904090812010e1b04030b09031917060d050606010f030605100306081e0613031e0f14250501060e01080d080a 67
    0x11844030100c1c10340c0c44550040780d4006901281000798400d44a20201003840d1a040d10701071068260903c441c50080c1c50b03110300b5158001e043c0d80381d140c2c541d00f04001240c1c20404100b80c181c0240380041e52201c680c0000740c01070602c0348000d0f2040d200031812002008107010b405040e9240480700000300e40d51001c103002c3d140301841c9980c040c0c2da0284000c200182c201c0340d116401141c08001e980c24002035000281b0380794489505180046c00070200c00300404080002181c006006581641101c5200d464041c3d03121000b812290400210700f84400009100c0d40c041400b8017002481c0b21811340500c40c008000d0141c0307000b400c13050b018031810801c000e441c2402001041150b0f02c0500025910305c0d0803507054800b6a40705030b040c00300c011241080c41241d41549550004e841c0c41d8141c1da44070407800140700200d0356141d18070400e001c01042001302c0c55a00740d0380000002c1c85038000700c1c2a540ca840c40c0034246a0f808502c4a0703130010008101f210300882d4444141c1100e54802c0200e83e1008650000d55 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 279640152 1250 279638902 279638917
    0x90e150405060a0f0530031210060507080a0c08210a0e190f050709050405100e120c010b060403050a02090c0703080403080903070b0403020d021501240903050d0903021302 75
    0x840307455504100c5820001a41c10010301080c0540c00c2c3c00f1103c0c01801b022071110fa0307031461250800100a1010201c065403190020300000c0c002c00f503141002d00140051154030b00c05004d8002c040b648100345882803070718520703aa07403003000d00f51201003541000048102c41d101d03e044c070917074000001c4e6250203e40300e6501065140001000e503d40c5048080000e1207081805641ea207a409513080089401003007504001d081070762000655103081d0422074148000340c15520f0026040c012404c00f6620300040c2c1040e100d01707480750b0564031804103040034010241c056a850b080382d0085000002d007c400f00756210114000d4841c119166203c011107107151046c0e42c402400f1445140104020a2092841560000b44038044a00d07080c0c40b51108074400d94119030480060344000364060083c0d60510080c0c1e003541001100150550601c4400450300801c0401c1e1210b081c1c0070207041500d580300f558981d00458004c0c1c2900c07611814942c00170082c001d1400141c0c09110f02c10544940a4007a01c200e0741c56 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 279641402 1250 279640152 279640169
    0x7060305040203030a0c03091d0402040f0b011d06040e1603060b13062a0c0501120207020d0f02061b0102070201030b01050702100c020f060406030912080c0316090e150405060a 77
    0x1801a0405c05881d030701e000410507010800c0703000011980c6c81f03041080056455108030340b82070514007441000706807036030002c11101c080d0824444200d2640c020303c8036020010041107030210300641d0070100303645010b180d000c4940300c4500000e000c043c2c00307441340300f00d941da04559040c0304075616020002070501c40c2e1110741b00101c013808030400199200f030700b0500111001460505070142812258414510740003010344050240310020086903820a03445084500303406401e605121540d000244e400384140c00150055803204203a0703045558400454241c0d00c41050360420840142046500135003008d20b049003c00d10b4002d402400758000c03030035140ca55500612074041e00041c0c078411540200c000c01d040741c10410104120425503103850140000d408944d030001502d60032410131a140c500f0621041051040c04420300100781c190030100c950142c400c0c0c90320007004400da4400c4414092541c071002200150000344a4001402c0c0c40300c1003c0401140e041c0103d0f1940010020048050f204a250 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 279642652 1250 279641402 279641407
    0x31110120c030f0c17061207090b0f1908062412010b04060603020d061205061f08011b11070e0a0902030304090903081b03090316020d150507020706030504020303 71
    0x194802600501c1c1d032900546408901540f29140c010150340e09500100045141204120f003521008500f16501031002c0700c4100300040684046601c4040500484112940b259034010703890301c5030a0304406100d0017038149178455848100da162001c1c1140220840e9000d0b28000c205500301e6044508900400210201400501c800800c04000240b11441d0361954851340401082d541e90b1098000400060320007607910020314408034121900390700701c80c90245406c49203402050000030200e6024038050306103016081410703183c5074102c0756944121308940c00c20a0b007500540c15400710203e502699164141001c1818000584400440c02500d070605035810016002c682d0036085981424000b4050305d01d85522032264806882d00c601c402c1c1d0125854800f8441c40c0c0d584220412207040c0c01894080c2103041c8224004e450b0f2141815507281c010340800c20b18199075441c80044032440d800391f5070410950707040f205540035141c200e40f040c0140c015000001101c0780070380030b5140b00b15401000b451 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 279643902 1250 279642652 279642677
    0x18090203030a0c03020a0b16020f031905031801060b0415030e0d0807142703190602030a0e0d0c1101021b06210103081e040608062110020301031110 65
    0x1500d03c00401c07001d03000c51140c02041000324454243e480e01500340104c80c1c401d0310142003406031410740c03003002e10201a48200115460f4288a004030003d00d01f1500d08141c3e26155038040180d40420300c0012510395103030401c006009204040207008460010082c1780d0380d550303060802d078200c400045002059030040190034019034418500ea692100040c07c00c41001840c0100c403504640040b140d006210340c0c50b0030300600401a0b0050368450740c1c0102c008195000c0682c1c415039404072280001000a5004000314000312680d4005000640e0240f0071502100c6400e0320003400b00420220550713150541542c00982948085248801a040300741c030f1600c007100240a21006a2115242d1002490702c464102040d4215842c040c2c001d6000d1103035039450b8a04030000f9100543d5401011103001e0041004007c0b0542014210707500c0201110049080410300313040704030508011252074000d004040b1030700e0264040d580a58143ca0082c01d00d0550180b0103c1400145d42c903d10300040031500103034500703 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 279645152 1250 279643902 279643907
    0x6040f0e150a020d1410121e02041d0604110603100527160f0e010905100e0405070c06050604060806040b07030b06040b07030320180d0b090718090203030a 68
    0x10380148060900518150840140000315140340c215507095105e16014084a280d1841d001c5001d815156910140046140e840b06072803000f035840340c1c0c1728140c080703030140039503a50f0360200c1c0768180720058004000d50201d140584038001110103c1c0c4142c408150381d2043e04052091341d1040001d260150b08541c103000821585422001100000007054001c0d81142185070980900030f041c204c00d8458440000a8054158850960300c8800c0111502c0d030015a42c0c0d1044540c0d0031110182c95030051007040b15011541c403a400a8059000f50405080c401640c1c0d120203103600440c0249020801d98072408100b0040d540303240714407203040d03101e51f000c1400300e1100280650030040390b00700000e00b02c61a01c08540c032904603502032f906614001c40c040302495014015100d00000095580a13040201d801403d014003810007a00701e042c07480501e001007030b1561032044000c02c2c0c01c0703e402d480368600305420603074407010b074001c111311800844122680240359015072000c0c10342c014069410264200b104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 279646402 1250 279645152 279645193
    0x110f070501092106020d050f090105150906010c052509020301080304270603030f032703050f130b09100216090c14030405061008070305060c0306121506040f0e 70
    0x85254003c1c41100040c00611944018694030b9184400481c084c5480e1180031105003004002400d20b90501041040e4514800309569080c0821640030500f40c91741070040fa83c0c6941d911008095200b000039032034a4030192004060144002d58901c008243c40c0ca80c29030903400207104074012503105200920040c40040c66801200c9601e030240b100e10030701d11510f4025204a54810f80104030701e10946811580c3c1401444842c1f0402031071003100300302c0f021140580000840300070342003040103e120354042d90b0920403100b4400c1040c000b06242902c4880b0505943e02c03040915128001c081c0d104800c00b40041007001c0420385c8510b46900d21403038080c405014268000b80241000343d480e41e0022190800701c007941c06540150300901140c80c001048014003071098101410070f07807100c2000c000141e000152603610010000f54140c403519100c000c201c40c141580c60002e564092002400580c03003490642c03c0c80381608030340030301c00c40456005c1a400c88803407806108694000940390044500712069 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 279647652 1250 279646402 279646439
    0x371506140f0c0a0512030a1503030e010e040b0315060907020f0706050a02010605091305060903040b0a03021b0a050a1106031003020103050403121b020c0f061615050106110f07050109 80
    0x151480a20f841d80c1d03060a000390600c1000d03901c0c00100070f0090401040c4a41c4d0302c402c00603001000440e045840240c03d0340d01c2001b106040011f0144004007903101d40e040130940c400068100e03000003030100c2c09150680d0049032407030701510601c40003030111480003a507140d030300450758050308800d41401d03c1251540d001a980106540d210000001c8a4841140d0303540709540c0c4840910002c0014601513080c10009820400d9962040c407040c890400694225480c17028913050060359039800e0900412950403a1807071000714023455100c1000d210004c039411007000d04caa03000c03031900706500c2c04009450200790b80040429182540600042d4000d0b404903400c1b50113824aa0040035006414000740c48800c2025900c480b04d0380d282c1c00010b0b80400817104103540444120350b1101d0108007054180c0507052900c00c2c1c50b10800e032807506000ac82c4c1e60f07128140c01c031040c0a012a68403070038054913501c110782030804244100c0d24030492248001c6420000c0e05c070165100b4200615001f54080c44120919 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 279648902 1250 279647652 279647677
    0xe0715020c190b1b1204031b03080315221410032418030f0905040504020d06050c190206150d02090109020310080102041707050a0b03371506140f 64
    0x40c1203400d1004c1000074441c0b0b0038490402980c1c541c01c40c41c0c094402d051001492180d9010301a05000107240070040c0e82e8848403d0b8030305040c03075002d400044c051900220900d030030342c800d040800080281c0340e048001d0f4074028141d003a582d0b44071054485402081440041c2019240507a0705040202e40e04815420300c1c141903002c1641000711400c44100301c41007000300c1c0418920510401001c3d0403021484c01407804a408108902d030540200e1384c001c08284008204603030314000074001003d20700c290f80b0746400c921101c641401c5440c1c000703950307504261105241c0b00854560a000e07450302382c14908030941d028003103c9040c1d281003100d9020790405800d040000842407008034000a0074805080141016803130540d88400381e0440c03608100c3e55070002409461a40301c20311821840c84226900301c02601580080100804d1407181d10210320540040c02e920744000494151032140c01403801c0c8e008807210300b000d180da1030600b44c179501c12664282c1c0c07500d0f0040c42301c40d100a41405c05070101a0502 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 279650152 1250 279648902 279648937
    0x20306010905100908061f120f080a0507021c02010e10030e030f040306110304050a0f0201171503010c02010e0709091712010905070e0a050906040e0715020c190b 71
    0x244002920300b4402c0300802c0004000580402c07050b0800c00841f900824001351007451130f02d00c03100c980346c0b5180a00a00e01b04505d0103020701c08021515200340c40c103030780041100f5110024610300604945c8100d00aa10a045030b02c1010410700b0703040c075107a1083da816181d40c6a01444002484900403e1442e10003e166440302850311041040c00140394015202a20075645d505602c2c01c2c40443c2d4030401e20307068500c414001c10000410000d0440c11154009921120100341c03480120703103004801381c030086501490720a2000b800417100502a1788a01140244050f080c240c60403401c0300c80d0240d101030154070145007000b00031025440042c8660141c03416005101014500020329071080602040240b40040100b0001d01715200c1d86030018250310b4107520984041c00040c1c13458a460150505c100e00c0c50f40840c01c03d64030707a4020040140c080e0162151250346502c16901074400642c40005801485004245413801c54090b02d4610b010010440c4030300d06007049501c103504a00d8061900394905c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 279651402 1250 279650152 279650159
    0x117031903051b030a0b090f010302010e12010b04021306080601021209040f0b09070503010815090706050a120c090602010b0108010b070f0807080c0706140c060f060604050d0c06080105061602040203060109 90
    0x3d00b006501c074108145002c0342900c501424401850300040c036862a0840420040c0700603a401540814641411031344034500e10022102c0701c2c0100140c0307034140d503c244005040c0c140844020444c0d0101e5400351240140e564800c8010398030340c00d150818140300c00e003c22114a9914050340b1004000c81c154070000780c114480d00202e00b84490076521600403540110040103040c1c010071220f0100400da010810817800d10101c0386544440324080d0300244a00071405a01803482030000d03402c001c64540c0b081c041c601d003440001d080c802d0913005500c01542030491511003540200c1e1094100d0345030f2002586404042d40341d030515010200e0045440005c20029a4003198150000e010200d0440d8058003402c2d140c94406411400d040070382802031142440b02c440201c1d07002c19881c0c1e1203140104044116583d501c0080c0d071170710450b000f59620000f142424428840445078141c1511034075121a21aa6254010805107005500d110829610410a401e00505094010315000382c018100083c41b00d45 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 279652652 1250 279651402 279651451
    0x16050102030a1406010903050d081b030709091107020a05060309190602030901060e06060909090c060a03020d0b010207030f060f060513020a021c0207060c050304030515011703190305 80
    0x7095034039100060300c8010007000a000c54054503044802420070344c1810f4656916243c40398103d071048400d0001610000300c0e0310007200038004003d9032808840340e0307900c1c2040c07010344003030000e00403c09a549005414003c041c00d01c400c4510054000307202c4804189054104582c59100403c0618680171b4803100b14560794001c8000d0521511584001d41c0300d06d8030b10851400c6980a84c01a01c12960900c00c0c0b00060722510103c4000e08015510142c42766107104130705240250300882503402c4100015100810780c0d0581c0942810580002c00348800388844c40126036540c024000036000b41c503000c41c1d010000d0103582c0080f070000c0248501144403039171003002400300c1c55280d011015a030f400240c80e002d03450f418014000561040003c45800340d6014400a6076180c85000e21003d0280309019201488010000d80f8000e6610004541c0c17100c01054030094902d600b841203038480900c8198a1a965001005486002121410714440c020049100b2070242c0b002502e0301d00c401600c0c020000340e01a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 279653902 1250 279652652 279652657
    0x10618080d14030c22080606030111040b0d1e090302010b0306041208130203070f03060f140c0c030f072a080607080c070203010504060b0117040804050d2d0201080109020c0a0816050102 81
    0x100019101780065251404d920b0030131100a0459100b6403512211140103040340c0309407000d540103825000d440d0030410724a640100807052246003107006010040f01d404090f03800080486209034001c0c01302c5080001419a182c00035500100071400311b004080c5854800c0e8500e07503200814503054200112150003007410310308036410481c1480c0604905009000071030240507019088007204001c42c4680040a501101000d880400d08180c00a1401c0f4160020011790300b440003031403440359441d6510b29040003440e8421030070501120141050400c000032290062080380c00a070b0203064a50786140c01102c40e080000d2601040300da0501c0840096142441400d1140348118400a10b0241d8040050100b94406480b095181298820000001c03c9034050718100d0300c050f54058580307070203480c00000d403201e0841075400c0e440009000710480c601c11110280c4c1075000780c8452a160f45c031028060140d00c940880c8440d140d10a020307510026590700d0040070003101c9000f0042013040c00d0740e207007070a9a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 279655152 1250 279653902 279653947
    0xf100314060a06050108070215060307030c080604140d0c030c020a08010c02010509010b100e040f14040c060f03090b133306060e031b0a0e010618080d14030c 69
    0x41e8000700420008038107500c1054081c0c030342402d229503145880e600003550303198608001c903440f104103c041503203514204411005154805940200d65496100380c1e55104402c0b14107607118200d050f4490003015000c00c2600640c025a610110301d102d40d5107040d40c80e8072090008a80141003200d00041e251070a01c00c4008144840e4000308803400d122100d1130a640030050518800c040480e4140c0240d600410f903c01145000d44010500400714000302c0014050055541c20190100c01040b00b0801056501e2040c0c03415a1101c003400f4806034030031003c0b620030041c010300e4140b003000032801d007004020a0181503485003c0100790112040e080d0a4803501071800c20310259518000c50030a40c8190081030040c10052501280240641001954451045215848039840700e8600030740f644904082101411110034840e0700b42d6500d480042004204070002421035013a40030204403640082105d440700081c036911380c00b01400741c0740381c401d86030701c0a0720403c003da400f00140344030849406041460f4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 279656402 1250 279655152 279655193
    0xa0b031f0902011404060507030809010207050a0309030b150a060e0d0503040f03050c180708040501090804141306061e2604020a0806091c0509030a0c08190b0f1003 72
    0x102181c0c0b0002d400381400180d64110148144820300c0181c0d0704c902510601c0e0b806250050302c90f1501c3c81102d009104000010b005802a83c5560040c180c00655000460384104d0546240703903554040300c240883e503407601c4c2342e021100110403c815481800c8142f80e9060042144201c0700b07183e0360705491580246c0c4a0f4810040c0c222040092003003c3c01120401300b0155407088024071580383c200902800101060180510140801c060081c00d41c8130b42c04142d4448950350382c03580c440c407170a1081c01243c071016210b403422403194140649a80180e0702122080c3d29000c132022080340a4500e2601805040c10402500712201c600804050300f000700d02403041c003034074140d80c1003500500c01c05903082d400241c4590710080a1100d9040009030345086000303400011550082c031040d00f00da580c0b0414400796454810f03208001d06010f00500440c0840b05a441210001224820710a440341c0340340d5000707003541d01c00000180e0325060b018110340e4082d410b80a541c4003280c80359920f82c244004072a10301007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 279657652 1250 279656402 279656411
    0x8070320160503060603030304020d08120f0f070c05100f0b04020f0c0c010c0308012c07030c0216050d021203090a0b090307091127040e01021c020307080a0b031f 71
    0x103481c0c0908604009440d050700600807528003c408039540344000742009015a0f0b4220780302c0b041c00715800030344841d0b003166841056117080c00c103216403903c4015122403d503c1c41030300102d5880c501841c045414554000090079210f0b14103200e000c02058601400c181c0310f5101d0740c401d00c05503154802010086002c80c1c0b0284ca0340b00000d111441e00d010f42240c2810721030032800302c00109801959490444213007000d04c0540303c425480ca9150f03904004403684c0c03841016018843c840c0d8040c2c002120020480e800c85080050a00d4104241d0b1300f54440d0541100b082c044140c05070510049090040e100c4401701c034034190046000c21f4440c5060b9104003508500440e000007a4a41440b1040c001c00c0342040c180410800003020a1061098400e03042d001c41c0e000d106507200004200820140b044024800c01107413210500070b0740030f540700e50050b9010341c514880c1007054500910a80c0e009510f26520064541e8603240c203100280031200d221903151103059040c0c030b130f03000e00e14201c040c0100e0000c8000c00e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 279658902 1250 279657652 279657673
    0xb150a0803071407060905060f0313020916120501150804020607080301032003030702090a09060f1b11010510061d030102070f020f0919020a0e060409140a0501060c08070320 76
    0x138208203898210004009103100100002e940344c40070f84070003011f068452a541c1d140d402000100d0040c000c002074120460104202111038103c1c0124032111554440225a02400e459502140c41c240039078419444120401c0c0000c80c454040603070322078400340040d0314040c40c0751209076098100764002c40741851012808010505020441d503000f030010b60081d42032500c603500003806100018181400184c3e1910300b80e050080c1500700803112041c40c002009001a51507440621611208140380401c0a840d402002014140300d000e206008004aa4005d241000c01c1281c1d02201e042c00c507881c0b100d22001a8000c0d40e420310003050220311900504250104600c18044540700907803038288104446020004d2801c100c410700500d90840c500d0059840c800d0b050706035040017604150a810080124000c034140c0740c0d036804401c003414500440f902130345c0e903200e182040c0c8000340146030004103400d0b800e00000fa1441c0180c80b8a91003810b050034010790020791aa0b60280a5003c01c095511240480 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 279660152 1250 279658902 279658943
    0x1020a0210060503060a0b041407050a1b0f0210090e0703050114030f07170a06140406150b040b180402071101030c0e060405060304240212060105070b150a080307 71
    0x5100702040c0502405401e103040c00203500e0303400c003c180031303585919000c0191403550b4942c040304114204840041c46400e000d100100503400012800002c0707202c0d5010402c00c011031218464803154040001b000720b42c840d40c24014022941c26408081c001504d0020886100480070140700b1052507800284d59898500400c1e0304280404c06a4044c0e04010000f013024800410601c4c10394262104c0414085959240d00c0e16244009001414440c03411052004140000f80014002c50007101c0500548481072510f013440c9196200d00708801c11b04120811041490b000981001e1105401e0300a60641c044046000e91b400040c00b200c3e4043d0008106440c0d680512030000007032031500d04414613490180210382c030b9102c4ca002d100d100c1e18010001904111110441c0401c90591700082d00b1110010800318020303402c0b10707100031103120b1804002540d0b035208806492304d0541014160310360362100b8044050080c1034440440d001080458041a05e44040000f064420322501d1409003c3c045040d44 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 279661402 1250 279660152 279660163
    0xe030a020f100c02100c11070815090d02030a0c020402092206091b1d04061715040b070c06090503040f030302010506060702010e12030d060b1206040e1c0c0f0501020a02 74
    0x1010b8880c1c1c50710411000c11640081ca0904071901c12100041110030001c06440801040d44408090b101e43c1c0300104900e00d0118100420703a85030a00c104c0c07640c407510405a1154118047c400c0103a0040c04900e8025106c0c00b0006001070016000500d0244282d005c18001000e15068103201c1d0488541038220899074400c0000507d203a1070b040004a01102400c00503000da0f102c00c0b4100302900b494442d010340c12043d4882071440040c410054135940300304125081d000380303501c0c01080c0a8843d01368600141a040d05104640c000009034442d5100d0400b40d0b8940700c00c5c407095440903078480102c0c00155017080100054215800f000c01042e00d0340c6402800e582004240c00e01600091210b01c0050341c210040c01c00c141c504440c00c0d000c150180140e00d1840c014204201140746c1040303000202c1590388e40090020070501c0a0030b0100750f071140280070645418102400869102a000ea2844907121201d60310303035030152416500311042c0380c48601c0c0e9654040010355060358000340321900150104071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 279662652 1250 279661402 279661423
    0xf060405010501080c091504150f09060215130203120c07060905030c01030507050d050a1505010e0a1502030904021c050f090601090b060405040e010603020a090b09010b070201030e030a020f 83
    0xa0034015503052800007003502801510550b9003440200348403035584e4483c80705507000d0303071540100c0ea1100c2e03460341c14044d2044482e0890b40403030946800b51003c00d206845402c2903075501c0e00207000080300c031200e020000c10003d00d28030840c0c81c007181d400c1c0169018403801ca200c1c255882d1880e100c1c94110341403401c040300b591107281440050a01040076440109204c00189402d0900003199036403000182c401c0e01c9103200f1403403110700d04400c01c42500b0155210200c103d261540200000303031110015900ca0411a91a076031008412000304802045c0d00745401101c2c5052040c1ca040c000014042401c0c1d0b048102c9040381c809007800c00d2692a100c52103007a900030381e1f107200165142821410103845007410f000d554403881d1548494421516503c04485c01054064000c22140d98074451030f6000741301c1404203c0c4140d07100940020f0803010303405205d00070240202401c020382d203408001c800319401900120f0601d5190030f0058810346040c40a0241080d054001c2c1620804690205081441411 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 279663902 1250 279662652 279662659
    0x30e0a03020a062307020303011a0c0613061b03020c0c01050405180718080105090d0e03030f07020a0f0f08070509072f03031f15051204030c0f0b0f06 66
    0x94591000c039a00060000c0065042180081e04e181c00082e581d11980b801000c1004200e501010f1007525540000158100c40c2c10a415220300c2c04100c4801441d445904a03000581c0d00c030001107840d000c10342050f83c041c503218000000b4103072040c00c900580c80316a900503c0103c0c0c0c0c040303150700401c002030028001e01c000c00d10b4500c0c0781504000005030a4110000302d00d000600500008042a01503a07c84078420a0b860b0b4503903200e81d03245e0715030340a0b16040b1141c600900462100340c081038000c5070725030f01c0280000c01440c18901c40048030300e05500b100006a078020000c0d039002901181c0380191001818005848001d040e04145c00140391061a620a034002c18401c420041d000c1d44c0a031114421008804092080c40414008034400c550342d1232034951180800020b0001d03081142c0d12040ca613080364401142d0a99507203012020640321204170034040f620801c000f00d401890864000d40c4240f10307061100c03410095071500e2a100c2031802084a0300c101407801d100043c2468200c00c0d078845000c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 279665152 1250 279663902 279663913
    0x27030d150518040c0306050103060b120c09130302030f030115020d02030a20100f0b010921060b13020c0105060f06090d1e020603090703110306040804120602070203010e0d030e 77
    0x180801d81108040840c030310560450b20100707040102400d030340c40055810400c07c1c030007940c4071300307140c0000c0c0000c1581078807803c031500c92900e05e2400440c03e6810f0540046c40100d1550319000c0c0c2070b41c0445844803c038214013040090321500704400f0b010b94060b000c00c10708000b40c01550103000c0c0c5090b000b100700d84195071051148048203980120780c50f180f41c0034100c01001e02e2039100e1080340327052032002d14002c1150800101001a5040e54004c0401c07803000d076140965507603121003600002020f411401c1002d1400300e401408140c06e9040880c0302e180142000101003070102e810300403a00501c02c0c54060380d45800502000e49000e94002c0c440c88404c544007440c20744003a0002c2c0008041c000b0080c00701030341c800010708a0241603d40b4065980141129030b9074901025260b0311242507004c01c17100c0344000c2119501c00c1c18001404c510560f40091480e1800d400c052203001c06200100d02216482c3d02000b9041c01a01d0a000d00c1104c44203490081100c0d8111640103000c0d500c9013485450a03904c032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 279666402 1250 279665152 279665159
    0x150702061f050f010912032706080c0703111204090b0406180e10090f05010e0c030a170d02190e040c0c0326090d1b120827030d15 57
    0x50101a104a070380454581074114080350041e0b90300e64050340282e2000441d1b881c0c09081c136811040d4100c0541403180c1410f001c030f03150100000124414042c401c0019030b01c0e000140042840002032a1280c002d003040d40c2d845007a900c410b450280f442c001a0894a008a0200580c88c1140504904010229018402c4905028200090840f0f0a005580c1c2e20388819058400ea1018010205030110030901400a42501d0030328036001060990204d42d15880d0241c4940e0f110f038041407401845178024007a088180e443e0311068450300c100b6001c501038101c02c00480080381c01510007007507482d024078002d210388604030790b02402000c44200d4540c0031300e003030070803c00c180c2d0b911030b0008402c107900d800d1544003001c0900420440b01580500d90f0800c50908090080041c0c2c00248901089829a66152000c0e8100c400c0c40720038a0f0300c0030040809070704401420301c16019400541c0d0200c02407100346015001d5100002150003028004007098000141116007a00280103080c1d6078148803031402911840d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 279667652 1250 279666402 279666451
    0x60406050d0e0d0c02062802160504020307090323011406040c08010305060a0e0a02060705011b09030c03020103180507060e10020f03040b1e0d02040905010e060f0103050901090515070206 82
    0x1340500070700c100000910260014115900080380e506902034079816050860b402070365502a590001000100512000400e40b40c103000720fa102d101d8aa40c1e2840c51880c564895503115560b100c42c503500007200070200000310017482542c040b10301d04240080d03513081c600144800c580070b0484400801038040014170200d040000d401380c00c00d1650b480080d2401c4d07810141380c1088042c02e8020b60140000904005100054100207401008800e03864080e41c241070301518810311620005004c01a80c9004002641c06a442034181c503031020f07030852401c1d4a0b81d80d02400d0003130300c0e0400700104203007100d5580a810200d19000f800030f0726000074111480345040050303890003203100b46803241c280000e1a640b084880c2098100d01621042c50701c1e04c441d40301c026000070b0f400c01c4c00780c0c1201c2840c1400008861070b0003241c082c090180070b080c0c241701034a4840110050303c0021701d0040d1545d25111000300117602005016880000440341240b6800d00441c02401c1040143c01c80c003403011489465140e129 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 279668902 1250 279667652 279667667
    0xd1a1315090b1f03141e0303041a15060c0d120c080411030a050303010305060105011209020913060e030a0903020f0a0f0605030a1e0903031b0219020f060406050d0e0d 73
    0x154000d9400151607080748000690150f50700000c050130080d0142c0114458001101e40c410550503500140a12803903032010360383d0000300c5001d0f01d109082051290545100c2c1e0704030303820200c09214500080340c8200442c14640c0181c640018039441003040460282e401255181c000203000c8040c40316800080e0010b00c3c07034001810241c005020103101c0180d95170b00308240343c03940d94040296510b940e50380c00c026131540c00c00d118090128244840d095110501881a2006c9941c01403503035000b52170740c0c508145201124042200d50640e0751400e500c4004041016044486903640c96125a600710710500000c218504000350180d1000c000902a00c900c031061f110940b00d0702e2030031944035591a040c0304041d0591005c0c0c00c1103800700a80d0004030701c200350000c04000b4003d840510010b06014076419802004421020050300400c000a8031903a1940c1624034441c00209103103030041d240d000040e07142d80180c3c800c3c80824800214554075030710a001c1c210780c518520018140121003a4006041c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 279670152 1250 279668902 279668911
    0x503090f040c20012a260411010905060409020a09140603011a12040303061502060c0f070f0204050702030a12090203060604020702030f1609110c0c0d1a1315090b 71
    0x11003003e03e890150401c25400054602440c00032500b8107558540300d0306209103020108070000d00c00586402d44034500036010040e0b0003c100707031141d07196543c2d29840641100c21107011304218025000140303903038036080074101800b00c00031700603a29081c06c9800b500c460603543c810089a001900b65120300d0340d500c0c080d41d0444440c00400d0090048450800b6014803801e0308030f842c030303401c84004c0c003007490ba1561080e020380b019072205501c2443d21000c2640d40394001c945011038800100b01c610b1010400d200a001da10348100e42d80d0714441c08941c0060182e420840300480140d0020541203050b580c03105e00114800b001d41c03000c200321542600401d8407640000c00490240360006026821900c1c20000d45103a00c14400a81e1031402d4440240c0480012078450051090304016803072a540c0580401c40d004000c0f410300400c4126515814002e048410710b2081e0343d0a0308203580c03042e40c510303a071481d00d00c21100311690300c1501d07006190004c984502407100c00d00443c40c0030050320004003541c041a800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 279671402 1250 279670152 279670187
    0x1401061202030a030809030d1401181424040e0d090b0406020a030507030c0f050c030f0d0e0d0c03120509130905060622111306080603070909030513030503090f040c 72
    0x11503448a1b40c492030b6100d0001d140172058030745001c4211880b1b414004505076400503031540c140b05e500d03864103402c0e01c4044034a00107101b179032000305803001c00c0a4410304003a00780c628081030600030000003804547c010451481107400104805024507030040b10b000c007400340f00507036600306424180b0003580c3c4c50300c2e200004d06100000232204181030049003551030055120185003424803440c900b0f140c80c2c8101c0b2007894003034412010401484803000c00c5100c3c00a10720b5441c1e41e030051000b030400c46a090024020b0702c200c6034a0b0b0000c00494580340c100120080360b61261652111120148106007810424142e01c603490100c40b800010f2000c42d020384c00c09003c90356030b44400c100b1103200901c1c00d401668000b0440c80c20300208168218800680000c0f90f60b94180e01c0032554418003074800080440e80140d0580040009111105051b801116068002c0c6419410008500b403141280c030240d070810f440d00c1c0e00124261a461600d0b80c0705490a840648003130100c440040030103001004007030501600d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 279672652 1250 279671402 279671417
    0x16360b070c0b09130608031e03190f1404030c140111120901060b0406020c131b0f0c1e060e1506010c02010e0a060e1305070c020906041401031401061202030a03 70
    0x3101c2d9601013022614003108581001016902e851b02566540720706048094017149800005941d40d234181a00d03c40c64014201042500b007001039400241496030807070314007550301c1d44021503c10143c010700748564402d4030b1b01d00604905081c140d40d040600c0b000004181e040051158901d00080309a41360342500380307405c80f0680c03121a20b05016017480c0d04012850a40850f00054441e4005001c0300080400d5481110600031400400d060b6404804001c0f00040c1d912101545584108200d0002403013a10303207551183d40950f00d180300b40c1500301517821b40303c0480342c08005100c1540310311540d0b46029402400b06103c03840c1500480b0078001e01007414002c176412102c040d640250b0300712804181c001c041890b51601e406020340b00b60460301c001170140301c2900440d03e000c0d0881c814280113410648030320790102c4c107541c2081a001d00c010103107a009500c9505000b0090209006070b800f942c0301e0351075084d4400101441e1801c6900c5940104040c1012608240250b03d010442c1c0101c140c1500e0a80c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 279673902 1250 279672652 279672667
    0x1505040312090b10050f0904120908030703090510020a02030703020603130b13060c0f090302060904090f060e0c03070b0d0f021b100606140316360b070c0b 68
    0x180c01c806685000405542412111000c03c03500c05840c41c4114140001d0311350640d1610203102011701e90741c1c04203030040304072004180030552056882c100361003580740100c0034a440e0301c01a070846e04007003c03c1340480c0400e40d091050340b405880d40d0700c0c10001031000704280307001900026540d014503c401780c05518000302081009030005200c904064000481ca8410b080c90030500c18050382c140350641d41c40b440c01c2c50403483e091080a00f101c4404159480d00842400c6400300205c6903c12442c3c207620555440c08c0d2000600c102b00744200c89401a0800158641d0075001d00381060202509540300c0d401886040c8181d04002d0199802500e10041c00a000c54100b0070300802071003920703040000f4995803403460104c480009032045078024031010901c802a6203003410b480603103595807560b500c25028000100c28601404400303026054901d81a90080c031a80c4180a1585d414444510745801c811391044c12511040c540720000d0041654003403400d0b203103882e44050b014030360099440146001540e01e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 279675152 1250 279673902 279673907
    0x6070804110d080f220b07032003091c030908060c04030b0907091b120c14070f060c0e03010506031518010908280e0a1401090b03040c06080f0415050403 67
    0x6603100f0100784102d5a070b8900e0940d404441005d14441180080049140070801801d95000d5403000380c0d1648882002c500d2030303140e17500ca00d10980f004c5070b1144028490714110355204485c0d41d2041c81282a290002111424010020061900075004507400f1009010200c51484100c070101c0e0303046115165151603c20b10075050a0169001d642d596040003101c0c1d0385104c41209200d562126500c2d4240d045091401e10360580321903180e800c0200d5250300032192002d80080092140c54032817003240340b148000d9174400044642d2249074000044281025150504003445582c0d088042100181000d081c4c08a6035041150010591641141a074804a00c030000075080381720392582c0450344075251226400402c208003082d40586c0f196000b001d503883d034128011803d241c41000c0c090880b60351a4105011044000c6404804074100403d2010016111584902850165105a0b035145095203058001403c140010703002c0084801440140000919a2840104020a101d9010800d0380d9075040a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 279676258 1106 279675152 279675157
    0x70e01051c1410061215150c15060f090905030301030f0f14030901200604080309030f030109090501060509010e2703120103050105071b15060519030506070804110d08 73
    0x501c013040401c81e6450803a07c039400e001c3c1e0a00707500c1c0d565000d50600c20046103241c0c0c0d40c8940511410504c00c0f2000f0062600100610440880740c40e020b85130301c010311000f04201c0c108009402004010400584043c0e0000040004909200e204a869030300001103207000602650396486401700d121050090607a030103000f13040036a210b03034842c0503951015104045611051000e140114031400056000c0c0c40d52040100780c070f030341a140050030344116400c03081c8909032901c014031074400404140b030342c0300b0080b078040a940030040413040034592100305900118080003c1d40c40d80f000b4241c5006040b20b220358001c00040c1d07185070048031000d0403107038113040300106200c2c0e920100c1d8104041031071201c980c550008000e0760f22800900304e5035040450500c1c1040100d403c0040c008207000840c0c0c880b00c03a00b01100e061601350741e00101c1e2443c542c804c1e84500013a83c0c8107024031031000207 = true := by decide +kernel

theorem cover : BRFrame.Cov 279496402 279676258 := by
  have h0 := BRFrame.cov_init 279496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 279496402 ≤ n) (h2 : n < 279676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
