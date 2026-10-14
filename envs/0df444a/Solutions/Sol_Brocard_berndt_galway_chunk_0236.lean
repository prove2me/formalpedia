-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0236
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:39:08.99746+00:00
-- url     : https://prove2.me/submissions/6356004f-8304-4533-8ae1-94a9c9c1c33a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 42266191 ≤ n < 42446047 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 42267441 1250 42266191 42266201
    0x2040302030304050d03050f030906060108060a03020d12032004050406050a0b300106020a050127080705070509100906050a06050405090901060803030702240403020d080a090516080c0f0603010504 86
    0x6c60811105100d1990036075a924040c40c0150003142c0903000500e452000100350910060003a442520400810800341c1c40e9a40d40f9480c0c5034009210045003920003030140e01900c20010f60740d090080205500c040704410b80080d100390361088400340700440e5910f0400032080410300482c400180d04100790020610490400305c030030b03c0491020b454441d03c0c4400c00307450810984c4501c016802c41203805d003c01000b8442c01c41b00d0482d481d14090751040b05070300311844501c5044001c2c60407000203070900511004000c203e0040c0002001600c0502c0c151800ca405d43e20644110910b803070402d070700882d881c642880a10182c51240e52801d003410314100070030044402c080c041841a540c0e0ba0000301da410700501c001d5124000b241c00401d803a103401d0600c840c4605006400540419a1000307000000c1c0d4040744035003d101d001c1c500b45a41351205501c0c00000e065100c030040081c40342e03178510386502e41401221001c691a402c00c1da01620001002d220341c0d01c02030310f1134543c0040204018070403481c055000d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 42268691 1250 42267441 42267443
    0x90c0206060111010f020f0301061710050f040f0603030c0b0907080c0f010314011e0603060b03130c0806090a0b09010b130c17010e040c120b01091107020415060f0302040302030304050d 81
    0x124103d05c0c40700720b0380b089074070102a5600c0c50302e0000041c441560400342c0000b07258545801d516851a0404080002001c03a0164601c124000e5074819035541d1030f40c0200c0c224411070301d000c01c4455500e1030042c001d000032104c202c60030350b09140000c1c40040081040c4049413041c5018003581c0a14000b00850b40c140c1d820118189551404803601041c0002c058a01800e0f00309090f40303403803000210b56035503c183c0754021420541040014880c658510040d42c1c1c2000b40031344030002c680380301c2c50b000e0801c4980740c11544542c81800100316844600144686580303001d45500340303030f545994004ca402c0c2c480391140c5030b801c03054408195040c1c402680c4000350f1038411f490000706d482d074003880e44000d481082e0300c007013044a201c005000502c070036055070100800070040c03494441402941d812600590502c600f28800c1c0c3c1d58492102692204000c40c1c2e8081d034000e0042200c0c84040f89035000c284250301036500058149107103685200e00a20031078090781d400078002d5003003a143ca400c020325000b00b100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 42269941 1250 42268691 42268693
    0x708010e040609081801020c060a1b050a02060c01020a080601032705071e030b090309090a020304060209060d020c16060909020c0304030807030804050c0d0b01060f0c0209091501090c0206060111 85
    0x105900c00f05203200050710a171291070740e603a1003400104000a1408078041c0c5e1051080e08200a8800010340258034099044080b844001c41184182481411f0200450020707400181c0040d40040e49001980280341c6032a1907100d205107504e03440011401c888280d2000f409030300c4440c400308244103c80c1a13049203984603000300c0346400d817503100d80501007020380a4110b139812040428010011800f20b00d640c0086c5100046013858600c0c0c0c00503041c80000b410140c0515400404541800003d030112015408090600ba60310010f4070360802c0258007003000d8400c036014076101901c0e19401e5082d2a0300b1a0340b5642c41180f05410030301744100940c055071800d041c91000300f0001000030b5080029102c0d07140651034210452416013001414500d551351100e106100140c3c1c1a80002c1142c0302041c15035259103442c400300307a41c40d481a01c102280003000b039840003581c0c082040030200006c0d000054505000c4101041e40d840c28010280d070040700300000560001c1001034443d511480750124131001c1c81c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 42271191 1250 42269941 42269951
    0x703061b0f05071b0f06031a03070302120c03030307050909090c0603060f03070e07030c0207080f03040b0703031404140c0f060702011b06050a0c0806030c01020c0907170a090302010b090708010e0406 87
    0xd00c4e07581001400c0e0300145120b50b00305010070040c0d4062183c1800a45050342d80c103504001030340020f4540d21180030003403042170040b11160b00c0c90307400c01c00484a40c00c0034040b00c1d602d0a245d00044c1641e005408481d11a00b01c0c0f100098903e000401c2c0601c2c2601c02415060035900e4000c10132107911071882480340c042c0b09030307140020580682d502c0c1e0342c0508440e807000100d074a40d07048000e0070449240c001025a034810300441401190001c11102211003000155440750054078086014185a04204000800180c03d21061008100c41000b80c411100c5c22a000f00c1180c2050113903154405409541c4181d050251902550140b0b10f44444c2c0c803070058408024028982c0c0300320494805131064510990f6401c902d2001d2074114801c142c0001c81200100f10940840b0b000039624005414114004c440640104100c180103a43c03506c1c2418000c440342801c0d1078042000d01c0103007e002c0c0144c0041d0f00f080a03490003410b043c40003d000343c0d0740fa52046090383c201200c911184038090b00440e4425550 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 42272441 1250 42271191 42271223
    0x40207020306040f0605100612091103010905010b030d030b090609060a0305060a050402040b0a0308180a080f010519090209070309110409030e030c0102011b080901021b0703061b0f0507 81
    0xb4049907119074440c050721034015082d410220304a980085c0061000c039a5520305103c125003207002a640e812101c034020405100a2030b102803101c0300718120766019802c00980340100b18040d0020314180031305804441c4603101c498005c03015203d81440e91034101421b6000f10b50703a803c0510f44140d1010340030340360841c1c00b07659036211844c050741254140038183ea20b4003404214a450700402000c1602210814422815600c90030042d11402c400d100742c50364520320100751070301e6040103030004140b4003050354500740f03903d81024041d11048580b60b40d03000c008100c5d1440740899110703e25045401500b02d0302c103691403080a40081082480507544181400c030107410594880c0101800548030784c2d540c02400c00e8680178185080c2d00e0035a864103690400302c88a03007400c0300e5600c4044071001803070400704a8448489440c02407198807140030291100400041c0c2c0e40400140100840c0e100354001c202011103070b82014020024410800001507220041c8480f10788541d000c2d255250003544401c4c0e40c1101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 42273691 1250 42272441 42272443
    0x706060803070b010e0c0405010f0807030e06011503050a020301060c12020a0c03060e0f1b0d020d02040f02040e13080d0209061306030e010f0e070510020f01060b1b19060b0402070203 80
    0x300c0078003107406074040001800941e051545c07603a0001000500c0a05080c140300018069455040c008010400e8120000f12410310a402064004c1500c0301583d14650310348145054418080801e50007182c00e100115004071031610807a4101c50380d035610200d84240b03030b81d6003c0303081c0800e00100c021881031041c0d0402260103800c442c00110311954001942e005110072035420070021681580c6150410880c0700c4000c00d48100c0c03c41c401000f02c5420060b42a24800220510002e01c4003075049803411001c6694044a42e0040040e04e5000c911180d0f60354030328114299100300c0002c020056602403108510a90b000c0d00a003111100040030640be240c08880400120707201d030380c080000030b43c0b210842201c10030207105d50341c81e07050017803014000110030420052340d07240c4622035280545016600081c01e41d100340411103211403020000d000c41991480d0001d080d40000c007000c0c01d09200107807106020760000403446610700c144189460305000300e45902000344520141c598025030208011001071360 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 42274941 1250 42273691 42273697
    0xc03011419111c0c03060e0402010e060f0d0203090601030c0b03040804140d080c010615090305070509060103091509030206070f080f0406020405030d091a070302060114010302040e010b1b060c0406050706060803 92
    0x5003101c005502c030351000b40181590402d511848465547d0401c0c000540da000d02c1d0760b041c00c038055404a940b000c41c0580341d0f00c24802c80a5a4101d18404014000c0c3c002010800c02e0480b8003070000303080c15a8541c09041407070700c010341e001002e040007000b04018900c10342039030081501005000ca007000c0ca8a8a07080c10542c1f11102d01101a55121410301911044503100800100e5621b40f40c500a8103640c1d509a40742d07400d0003041d2090801200041d2180e201f90841030000740c2c0040115051b95920711014042c2c01c0105040b4094001d08000030301c0b040c8614501000003960b0380d640d10a41d143c010540b070382c4481c0504103035440c6070200030119150310204040e982c1e158956542c8020540750401d41d1401c0d2005400d43c40e0014003c2001c4000319600041c51410350b60940055000c690b95540141c000b071007039510680c1e8405040000040100c4048003034010844030303040454242000c60201511484102c0361008000b40511060281c2c52282010703040182c4100c50000b0100d0300d130320016156030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 42276191 1250 42274941 42274987
    0x60e0103060207030801060f0203090d0c0504290603070e09060a0305070828020604030305160b0a0b09100501210f0203010b03100608040506060d0503090907020c0301141911 76
    0x9a0001500c3e01015480880640100381c9441c0402c0000c0e1005002501c030b100c0c45005600c10b000c0c0215500600c142d260a0f840200b100400030012042e008a88401106c00c1180c040340811075000d14610a090041c1120710424030340d40c4604d0540e903d04200b0080207006403060b908010a180b000c400940c040100c2000742c40f03800010300d0450264100e0002200340c020003002143e49a40380000162991000d48003525231500b80181c56401c0c02c00382c1d003441c0400c00741c050b00e20041c0506010034502140c0c40b9144448043e20500d2036551800d65103a00c0016a108040c0011003031490400004210002440c50340741c01d130b00c04510300400c180280180c1e00280c02c40b441d402000000d00c0740c034035034600d4020010030300390600181c1490a41c6505480f0480104158015080d410140c7c04100c0e040c0300f141c0d0412002030000c203241c01e107088000c0d40c1d401d442000a020350319108065512801504e2154822500340140490b94a5a080800d0151600c2181c070398103010180580c41c0952003c03149960b0074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 42277441 1250 42276191 42276203
    0x40207290912070206070809010216061d09090604060c0c06020415020609070e0a02250506100503010e030d270b0702010c080c09040902130218030607090e1504060e0103 74
    0x90608500160401403907034460400c02c0c404200c00c40040c0c50b41420b55290300e0300941803a403101141c0700140e09016401301a070380c288416902c041011a0042c810150380c0520000801d1b851701c21030b00b0f00c001c042c030a81d00700e031143c1d002d000004c0c0000c2c81d5411800070800c19203890b0070b18100554a83e0f0581e0040d80184c249001078005080c0c81c15810808164800310003801440b0075898082c3c1c4140707043c00a0207802495070001096400c0c842c2c21807114000e00c0f54000d1400c0d00008a080c0302d600c03040165401810000142030004492074140034901a010f00140a1881c256498502c3c01c020000300d900b040d040f000d4203112138a84c0205000c40c1c001640120702c50081450303c460002d00316505103010005114455084c41507025581e400e850001200391000140028113000043d980d085070440d80e4011070000840c20b85085207100140036100003a000c9480c0c0b62200710050743c0002c0d482c043e21101e40c00400008100d072552511003041c560001d4000100c098031f40111030b0b0032030800d070030917505 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 42278691 1250 42277441 42277523
    0xc0902160212030a05070b040f080d0219020c0307140f041b02010c0302070b061c05011d0c0a030506070c0809030703080c0d020105090303070f0e090414070b18040207 73
    0x10340c10000c800e4410042c02e00c01440c0b50007692400584107000c1d1305006084148000300203020441d60030010501c0d00d820155407030711881c0d0400100301950190080d80d4068071030001803d0b4060000603a100d4002008020b4101541000701181c1c0d950040d00e09543d1000312000e542a01d600c96105042090012a150a000e400c40d008041c0c2500d0745009060100f5104000710004140010785a07604400300302ca40d5076911755040004689060098405081f030b5281801128000058041420b40d400101040c0e030401c0c0c1c4040100440c280c070034032000d402500240009071036548030700e143d50401845002490300b030103d43c801080c03818480c0d40044900c0790000458100303c440070407641c0005401407000b4442c0c0d103041c0c000162640005407410b4140319818541c065500e00a41c0500724010f00504032824615190070501c80c00d0580d2a501038140c0248100443d5030002102100d44114100b683c144c4110380100601000f580304000550344c40c4048084961490f10102000355540c48101540300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 42279941 1250 42278691 42278693
    0x210020604020a0b180402160b0901050711010e03030708100e04050109021e010e0f01020109050f060703051008191106180f0a08060a09020d0506010f0f0f030510090c090216 76
    0x481c0501d19001344070120f506004011001c500f004020304456001d136000341c1c90300a100740744041e9542402d07000300080c3e44e010402a01e01c00560140348502d00035076030f06080e000c00d100054202c0b000710342d40382c10a400c2040028440d50256002540001c280100d50782c0b106e948008085600c8000d440460b0603035150014a130030341c1380054820107800e003018038010011803950000303048001c03d020118081d90700d00c0d4018010380c0c000e5004050b1640c00c82c0c01c1d20350001c1e10907032164071044101e5044001c81d00c0c00000c16500c10105d840ca801360762440c0d0050440da4215400b00c003622020a41c200e80d111014412441c00740c58000c00f0381020070a245141884c0b40d0070f0020004044210010705006900c0300d641041400d9001800e41c1d003186c40e00f00700081c0a078450001c170b209500d010401034240d02c2490000503451410015600c1111400c403d00041c1580300c1081d1105450030744030207010395018841d075400783c90b03141e0312851849110740b400321030580d51200d0f00c100342e030400368050800519401210b4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 42281191 1250 42279941 42279949
    0x30703030c09150804020d060f0906020301051f09030308091c0f021c021009050102130b1c09030c03051308070803090901090203010308030f09070504050a02030103050f070807140409021002060402 86
    0x2c0a004001c0d0740010700f0803014402000003100400c003920403034500448038280802c41d40140340307807410340c030b020b000c0d48105050030000707940284559400391590540a500c2c800310120410301807641030b9a482071462860301c0480e110440a0912030780c60040c0305028500b02080c50b03400c00f00c02502e442c0d90015080d2808040d04046514006212200c080221300c01c55540c0811915820307954140b00194a0314682400307402801003a00c006490400e000d00070603007500000282006103541100d437280d400d084241e03101a500c1c6104020702080d2511601400607010340701408003c41440240b020607075480101d035140220390380c8441800c2d000080c40140350b081c00c0107043d0240c251810190700d103524599411120b444018a10303003401c2000c4012617480c510611074800201b1006109000500740a0602c034007e510038841168184911640c1b05c5ea2490081001e500300c9803010302501009140191054090290a08040e40715950780c01072001030790340c482011403441441c0d00a10442c54148188 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 42282441 1250 42281191 42281207
    0x3230604030903050f01090c0b0a0207030618021e0f0108060d06140a1118011808030a080a0c02060f040201032c060412050403050a020f040f02031e01050118090e0a05030703030c 78
    0x25103542e410722102e0004100e80c44008c00031a6032070102240e0701d00c20201d0403402c020b0340d1741005010034100f60100740d0500300560180152070084034000c040740507031038054404044150500e50001040030310521a5070140b444160f0280001c3c0458251035401e40e40e8001300d9010750006605002c154092085d6842e5030b2003041c4503043c29107005890106c070140301100038a445100c840c1000510700b0055000901044942c008000c1c9500302c0b5240c000d0044007804403c807c9440080280c0b80010b40e000d81b520000d605402040c20443d40310064846400440150400707001c0c0007074066503007a800903100360302140a1003a800120241c9590308143c80d02c42c0c1030444003030103582000740a00003400410408070300040030b90341c100c03240344c42c00c03510401050282a90a205541e002d10110030800c0c0c0605004030100c0c0000f24443c140d07503d0b0380b110015554205000d01800da201c42101041c070010001e90300c1036600b00c3d0411b04881c6282c00d07503964280756a00c0300c40e0850001c0c1c2c681d0001e440a98210040f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 42283691 1250 42282441 42282463
    0x80415080103120203070b01030f0204110a090510030207020906012d020114010e0c0a0302180918070506030c091509040c0f1b330e03130506040305070323060403090305 74
    0x40c4d4030381b6042e80c88221241d00b043c0406007080baa900d4000046684960101081000360f280d011380f28004076201812072403c0e40701e0039000f0303900703a450082900e00ca4800c031203107503034000c019140c00d8581d200111440c1000408401d00c0584484a07841c13066071030600c1410000d02580082002292542641e03001d101c107901025620200c5818404150110070a640c083c105d0b0780342c0140c407052450368091002032903007000c5401c14202c800f80300743c65030078540c6c1b510034910440c00c40c0e0005549c1d00a20120348000c03a2405007008082c0b0402041d031425160075100d01c45894482130505030000d0000303040b600e20784441c0001c9108540303000300140d00100c00e40d91074580d142400800440c1900c8600307094a110170408040300d4040b0500810303d0701200c4003500c0c02800038040003841d0a8042d02c6a4a40c06a81c2070f100d00044a03000140a1509204540680303600c4005803028514582e01d41c008400d103811441d0b001e591451502e040d40c2001c210881c4542d01030340c0c1e105000c41c550708103203003014201c00d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 42284941 1250 42283691 42283693
    0xf040507080403110304031208010914060a060c0201050903030f040509010e07020a03030506040e0a050106081605030a0b060112050a0c080109020a0f140d0f020307030b03031204020d0804150801031202 88
    0x800c000000d07800909a5a00a8043c1020146801c007184124250701c51500000d010452036540321049540c0600b159050b103c50403020400c1203042001280c29a001300e9030b1a5220088544c00d010b240d108648144c82584103042c118180740090340004e0441d00294003000700010081800c005030700d00030315440d0040a80701100484c0c0c0c20581e00003920f60f0345811001c1c3c14181c480001c180d040d2950b5011035244000141540e81d0240185092406000a4410400c00d0703c42c140c0d1000d24031080100001c11144014020151070308290b03540784844d00c000b05210f042c002640e040c80f80310803083c004d007031007035444001c00201d10700700e114050181300044c1c000305103203481408032201c09500301441141d1015030703046c8a560350142a06101e554496900510211800c105048810a0450300558019016030f2400d00840c9002000d055907401110800c10913a040000030402504202c0f52011043c0d00a04031a0b241680300d06400114040c003070807650010f10380d08010414010000e100d115070210750b00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 42286191 1250 42284941 42284951
    0x1508011a060f0301050904080906070f0c081501090c021603080705070f0e06040e07080102070c090501050f060d0c0201061a031006112d1c02060601020a0b010e040c0306060f050f04 79
    0x1e0035200382e03000c140151401100c1c6000414240254042074030800c0380300030310040d542e4440c0d01c0c0043d280c24966004441c3c10000c0d00700401d45240114003004003280070006000310f6864030500c031000d45842550001507000d080f410b12000c282d214200300c0030318091844036036114040c0c40c109140100952108034200801e4009105240c0350f25071054000a0488000c00c1031210340400341d0401c80142d02c00c640962001a044082000c645410b20803501c02e80000c10440c2e0340c880a10042440c950030071940004200051600304000d13901c44400b00544e440002801078440c0b0300015180c0d00e07140c49055919001c020884101003065070100607140c0c0340b9041e003e51401c100556035502c450002ea05401d640301480694016403203c042c2c48480c0040212480d220b024664046070860740e541010040c019203001544a5000140031400303250b018054a2060b8a004505070150b400070740100c40035088400d00201103601800740d0009010740c0300940011034500401c014083c403209030114003070b074102 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 42287441 1250 42286191 42286207
    0x60201050f0601210606030902090a020c030a0c0c030807080705010506040603020a1a070b0c0408190302030a1b02090c0309070906150806190f05100e1509041508011a06 74
    0x5074003036410801c2800c040c1c6296514041c03450280015151040304945031400024010703030315400070404070f802a6508881c54503200c3c512020391240046600107540200022510300d403061503080c001500807c07041042545035070780d15240b44c0c05010b040d50a11408034150b42800030038400d25410141c1200e08002c294559800703c5d80d11290391081c03a00d585100c00f400c4e0304044841085502d902d90043d4401440c0ca03108000089503000b5004411280c42511200120341c210922200c0380543c040d00150709240720000d049035001c80d40102c00c0f0301e0750700081075040144c40d2a15080d010b0000b412149840c0d280400c4854a0300d40543c2c0075a8100d4201031040010846410002e00d4149003460090b20320f84d40d00c1c0124201900101c442c0c140c00c0501d203800030700030301d41d01d05010030707250300b101c60b882040c5c0400400c88501002c88482d5500c0000c103040340350400c511500400c2015801760000ca82c62511034640e859150f590351100401c0e9440ba8104d42c42c0050405440103540801c03100c2d01d00f88805 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 42288691 1250 42287441 42287461
    0xb09040203062d04081305060a050304060507091203080103020909160312110a06090b0a061503050601020f07060206090601050108011d06010e06040801091506060e040218030d1806020105 82
    0x81c0c00c041c060001c40c0a0a00d42c010300c0440719202e42c2940f200b211843c01c01d840d01c1e2426602420b60303108803030b40c074000101340b030302e01b2104030b51407040b580d40c03007600b146c07616104c110007040d001d03040340700703001500d4800204101c2c0451442400b43c000d40710540198514010b120140704014030201207600300540c58104800511401e805803a00403941401071409004190742d19404038049003054030400c4034950800c041390300038600316803003007000c80240c2d11038610030400e07079035540600b00040720441c59071002d00d48a94417981c0d2244052042316000914001007500700a00c43e0041c60041c2c1040c400c204c4146010000c0c940146000c0c40c0002880d031401003440e0a14010b2880703c1240a00140440c2c0c150b0301c6a800020740c0704005180c60742d640c0d5a074012500030201c85c0710442e6910b01407070040143c085c170351250707034100c2c0d2160b110b4030400030540c42040000d500150098915200b98071030b52030309032010082680034051070f4503540c640e010044004132644100b85e01038421681420200701546071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 42289941 1250 42288691 42288703
    0x606020705100e0a05150304110301050709050f01030605040509210a022107060501060f02010c0309051c090f080c0909030403020a0302010c020102010e120a0306060c02090708091009080702040b09040203 89
    0x4452400d00707540b405400011324680910b9015640c440300b01562606c503020184002d6015621507100300c414010203005243c207842c2e044841c600410134210013040a41002d08111801410524001407646d0f21640020222402030340e628500f5801100715507a0018004005405040c4d901071042c107010403001c0c003c1d592009502c2c0d00d203901110f40208603c0c080a0010380b4200b6030720103000e01083d82c490000504450f074501760400190b0900d03014914071030003031041a10458011002d8440c030f0055a0403c0c035503030104910719080245240e000165048603405030800780c1001006801c115000345c00700549244040e000c0000d1760070420003000103a4a0561000071a40d080c24040840002c5000503801080c64001060007405442448115900802c0040001c5d0700d050301c0811400751034420032a116120010001d4210519501041282d805241d81d81da0001c112012100711411941c1c41600f9900740304422207400b035011481d4411850301e070080340801107050f120344286c2c2c50145c001aa4645c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 42291191 1250 42289941 42289969
    0x60f080a020a03021c120c060c180e0601020304080708011b140702010813080309010b09070201020a05090f03030c070801091505070512060a0f0303110610080303041b090906020d0606020705 83
    0x2c00710302e0f0020014200a40030301c24070781d00803c151b04000c4072400090068200d081045903d540b800500d400c1181c0a400c0407150505032080b050002070a0564100c080d5001a0009055110600000030b410304104089000307131050a00100304140000000300c3c00200392800a818842400c0714034075103114800a641e102134091a00c0e0866840300c84202c03101900060700a403103050008100445a94150069070700e1040546030b189055a581c0c40890803409900740b0320700015800c000d074044502d440010107440007802000d40b46003615602805250440310350145034a65140c5603e1000e00401c00351010301d0586600080c80301e450b19010043c86445074100e0300032030880605c08107032940c81e0000b52102610000a280c02c28544900340544001240322501d00b85104000000354100c16101d00c0400700c4034904002c5066449690f80c4112300d4000c8100000e0600d035403400000c90001c80d0040c1c12180e0301540c4010f9035000310b003e01800380c81c140d422840c250b40c0311803000c110b82c0e1601c0c0c070790020724 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 42292441 1250 42291191 42291199
    0xd03050703020708070506090706111b030708011b08100e010b0a0c050601121e0b010e07030f020301150f030902101103040503010e01020a090e040201020604060504060f0609060f080a020a0302 84
    0x954800c041a4028011401c0103805000041102c0c01000f0001481d14012440c210842d4800ea035149421581c5000d4003500740c0309030f08207180450b440d100f00e015035104010014140c035012034544650b01d00311400c1410308103184c0280013403428125003086845800074a1205400201070419458400300c00b018030902960010016203042e010344613061001c80300381e222059640e1540d44035090313003d864003010141d803001002d4a2092071214082c44442c040d0b581b010302210aa0328181100000320346c014030348802c0c151145019020300c0c2081c40114082e002d084050520364210200003002d0358480d00d840390031325180003481c0000d039440100c1c500c10030b402c0b4906541c0e16210030807640d007507019030307440203400d503081c5030101e0603904045d0040d049007503059a99881d0f941c0d48010942c2541015280a40560409000302e008a1025080b07140e100303001c1d03c2c012602c8400c000d41441181e40d5944948815a5100c40a1043e41e1081003600c004000d00401003140c200d02c3d400058051040d0f21009100b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 42293691 1250 42292441 42292451
    0x15030f04030e0d02040905010c1d0306070f1107150806010c03090b16080f0a1107060806040203040c03051603030906090528030209010b1e0a05030403030f15080a050f0102030403020d03 81
    0x69503101640a1203c82d4064800d000c03e114903d441c038082c042554441b008515003020210032201c03400411054500010002c2030203888542090303401011001c503200402c2801050304610b0071040012038000e0035000030b403c102e080001c1c0d004000b101c000d440d0300d040243c14910080429413200512054454203c0c0c40e960f240d0b05c0c50481c450141d0209001800d80c0000302c4d6040c110301190300640211405a01d580c0390940c282014992a002d042c061400481c002d01c1c08a15039081560113140e03c40d00c80e090010282d500c9407103071841c0c01092101100c2030544803109104141d03100c400000240000c3c2441c500300c81c1085c001036090280442d8110403540d0440c4c01200010380b0300c07044001160050041d401c44c2d40c482c04181060346c410804c222106002c402c1451051003110105c40030756030345a40c0d640c2151660b13601200607216000710045065129502c2e40c0691580c0100c4800074199080100410186494100e007804404040c02120340d1043c410000881d401081a4426140e18030f0f00140c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 42294941 1250 42293691 42293717
    0x50607050a021e04150905090712061104051c060c02031317160f03050c060301050a05040b1503181006120209070201150906031b1406070501020912010b15030f0403 72
    0x8007040740c0343d1055031160030400c280c1e20644084401e0000d6a0b00d52900f80703e40e40d00d41400983d40c09c0d51f8070075000c0c4480d0b02091000401c80f582e21108000c012082d0081c5095a1540041d512040c1d0302d4401998500e910394000810403580f1a940076000c0c6400030354181040ca105002c8012114440e1803000c0380002c0c1041c1120605020130034640c0c112154040d2503649031440d20007800d009000844591052000d48805445c0c4031007541d0403030f6001061415544e0821041c000642101c0c04850741151400c0540d0310600c4660700a18841e140c3c0d003260a90102320300c48103c1c07a20a100c41d001b14114504101031204030b8500180d00d94144c0c041da0602c2c40303515994000ca0061400416501020110000203c0c08030301c039400840c212801291030590304000407005a040e240d041c85800209000d03900a41524203051010704a4540514001030500d402c07000070450004107800e030200642d55602481300d1501d809004c2c0c15503000314424003402d525144000d08248200644060144030003112942 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 42296191 1250 42294941 42294979
    0x1002090301020f031602100207120e040e060901020904180206070b040f06091b060302090108070e0402161b0803070b06040f0905031612050a0c0803040821060406050607050a02 77
    0x10701819443d40e01c07140e503403802c601031070326800c88101d04078018040e180c0d80401030401070082c2c844443e04039819240e06180d228050300c5a440d20f54003d5002034a0b500000b000d03400500616119890307140015035202c035000c04100c216074035100144e4a030b5510591620158442c40242c406096100154001940312410402e09004038000018000750070860076400f00028070090007030444051040308441a201d54040e000d0380106125180003664500000b0348003880707070401000c0c454020340010326042840b0304804d04803034020401c0d03404040307810f00b8100030b000401088000f1700c0700078055400c0252039a03441c00c43c01c0020300321a20450311a040c1c65034654461344000ca0f4154898116a5200003942c2039220200162509a440680b052080081d19010380c040300c05004140ea00d4920720800ca5803500015000540291000c00050092080b52000d22000c20684480c00120841610b8240308101c180e401c0c1c1d400040c002c5e030003404030b0300000d07000148a890740d0354100d5a40e05d02c043d10903a56 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 42297441 1250 42296191 42296197
    0x405040f050304030302030702030c0a0302030a0f08040906080105061305070206010b03150402030a0b040501091806110f0c0f0c0a03020609060d0e060c040609050d050a120302040518010501031409100209030102 92
    0x2620700d01000400008060300000104070040c0300f541555404404034080018030103962001941680103014010000744d401315247c5002c0d445002c0180c2400e8a6031240812110030b5007081180342c2d520003d0000c503180405146da8503081d00074042c00145081c550013525504180701340f501500c004400724003107450a4641d038400b410060411034480c50141c0d00034005c2c140114031140030300d1400e00042406c12890041d1a50480900000080407116580b960014201c01c820b40d42c035400c0601c88194812000b40052640b481c0e01300c0101200c041950b012424018a86501c5124441050041005840380810b4864048041360b440c2c1d00c400600000101500b224407500105000e18420005881c0700b40b0003038010b840e25a0f80320b440403501c5806010000a0f001d2002d000341c0d00c481a00f40010b003c0c1030101402c8146441c1c05400c01d81d9407408115221220310b2903108148102c00107101c0e0b560b15200e1f150256940400c0c0000c1da0030440030780d0f03880b03900c0d640b4204d1440340c0028588409890035011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 42298691 1250 42297441 42297443
    0xe042112020a0302030402040509060103030f0f020c030f0304080609030301180b01020118061a0d11280806040605070206040309030602090f1503040201021c05030a0b0a0305030a0905100c0b060405040f 88
    0x20030755886458030402002984112400c0b80b040d0320f04408103501c0782e00010024140ca5040d11002603010004a041e500e800340040203800f103200d0398110110b9602c091240c070385041ca105005503200d505090182d07051001c002c016046070392007840100b22100c0288900c40c2039514404c0e00050f80204500101e000d44107000300f0a04848503000d880701040644e600988000d8601c100c0c1054071182507040000126002002a03e00c42d25052000310f03910b400100a8402152441c540181c4030200e130540400e228254041c211a0f00700301c0c01c001c00c2c01414003c0ca07904c56406c0c8040c5c1444e14055038050a004090300000d001d0320f50100700c2030880e48030b202000c2c0c00c54800134581c1d05031100614100f8181e034400c9070124014010300074440e400e0303000d15400c01000c200c20b8480d6421942e85000e0040201100d03030816601c042c0c041c0e00003000c12030030300c010042502c8070307562000558142000d201864501201da50100500b0031032840115090008168110108460119403a1074900b4100c012405441e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 42299941 1250 42298691 42298727
    0x52409040c030b1501030c140301030204020d02070203120703120c080a05090304080a050102180103020304020d0f03030b04020f180109080a06180c060206040c06030209060f0903120a0f08010e0421 86
    0x4140b081c4492401184c0036440401d0780c1c144060842d1304422035683c0f030480420780c0b44600503c0103100516046d001351000403507003900107040114a0b00082d1810f040005426040d0f83e000a00d2003d2541c00380340900c07491400c2a0900070b000c081840100501c100811031031465580c0c0c0042480c02c9018421a401440d40108607a1290880e0410074000e6002c0640054207440d500b6903540294024002d03640314580003031100011f001152a01e29804140c620110101907071480e500c0829a00c1c3e1024051240c4040c0c130203620340842c10315544c0105640044103040c4507103284100f00e903900011314150469486400400d07548100c000407080c510038080001c25680110780d021a042d0b500040722880f89028181c0200069030742d0000340d049121300760080360400e10810000c0d00b9060700c107004003d1548090100c4842080468441483da040190803000081d2501203040e101d40c3d01801c0700b4058071855040c0801801e16554928110402c5051414415504c0c16603582c1d4a001e02054110014010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 42301191 1250 42299941 42299963
    0x3020607021009081209012a1203091b09050f09060703020c07031208091902030c0607030215040503030601030b010201050c041401180e0a1802030c0402030a0603020a08030a0201052409040c03 84
    0xc0075113005c54005854050000d400d15080b50340c10702084a50009071076448210190401d819151502c1c4124800103140c103141c0c072016a80c0010381041a02c941000307558454080e07d500300b104031415076502800180301d01101c1000e01004c03240c0480d40c01e410542d10300380140d07110403444c801420910b9540c00a000d810b50344208070a000d401400c0188140c4081e000c0d03c4040f41607903003540307800c0c11055021f50036500180c0c504595041c1040103100c0745010707004031078011482089548200b60211003c4909410200c248065545c0500070b4200001c002d00007130007240f07407500f43c89150f4010703031249440242d140c60718070000b64010606051910801032407008a203480701c4550186403016920045d42905d040c1c00769403459584910240302075030080c0070f02545404002040042c0d0009069082d28a03078038a0000b0040e40c0309602c50004004410155440702c24000d806804c442e80140f0390f00c16601956503a1060b003802c0048444015030480d000310307185e1550308013100869510b41008112501030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 42302441 1250 42301191 42301213
    0x1020403110a0e04030c0b1b0304120e03070501170402040236060306013905010f06050103050f0c030415050708041106130504020d020d1e05010503070302060702100908 74
    0x1c4180a118100203495600c003a540e5246040b00b806400c031400740000d06180700c00700c00a9120b00d103c03500320b5100c0b08490b03c906540e420003e0a5481034404403003035200c1d0201004500d81207600481603507001c502a1449516110019260008426840440e940504006421569194107039a501541e0048600280603481c04824484005100e401c40710740071104074015515140048030310660781a5615001c4c1c0541510700120001700520ba01c54030422a011641080d0f5000003050031140540c1c00450801d6552090030204e0310b49070040c0d4101401c1504003e4840342d0340c600e41c0d40000720340017280d549075980c0c04c1082c2016015200410510b0030702c0140002168016a81e40c0210300600303500d8017a11003002085400c2c0b05030740710800d0305081a00208458a481d502601070250040d40c050705e4034000c000c01e18100c0306103505580380741000c1d81c071070000c406841c03207140d001d840e081d0000c00c1d800d070441c1c0001e0b040340100c080c000d11440741948540354162240c0350300d00040c4042c1c0e04036100d50f801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 42303691 1250 42302441 42302453
    0x5030d021b0609011a010305040204060e0a060905010e07090302010c03030f02030c04030b1e0a0c0c021302120106030905070302060f0702030609070602010b010912030503091c020606010f030e0705091801020403 92
    0x9041c080540748940c00110300c000350103100344480141d25107240050f803d40440150041c150052003a40d105540c0d640000b515002207a0452003103203883c20001d03402d030614500340119036040c1c0080c1b40c4000301008003c000e54210a9103c1540e07024200050784c4030301032a086007e41440024806a84d00100a1201d1000315030040e10943c2c0c820100141181d0b19100c0141c281c0d4954070a0074a040c03c40804180c0e1060a6400152002c00c14540310303030019150380118141110081d0741d030301c4007940043c00e100d125840b244001d016000c0791800703000101e00b0361541c603540c88160102900c40c1c000001c02059881c0920210354449074050306a650a00d046044a80c07910150b110b400c015509103c3e0a8074036620031150740003608c40d050030100001195071801c541d00c1e0001010407280d0b1045007c007030304101e03a480052140b50285da00409480c5024000100f010403410b0f0355405041c101501032801000204400b4107490701a10b20713a8140d43d41c480e105e030400b01c000384018225440000d011052001e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 42304941 1250 42303691 42303727
    0x6031f06050703030b0d030816050c0a110a080d050315060c010e07030c0b0705071802090306010e0601140301030803150f0622080a03140304110406060e0109080c0609010c05030d02 79
    0x100135201040703100203403814044004091b6800a0026040390000b4a0101091034800c02c0c0158a241030f0b4101801002c81503e4400c4914055031301c1c0802940b103164500c0c010300381c40c019001381805808501074102c4040d2490001030303c090b00181115080450755155501070720200a0120001c2c0062000f40604e140c960741980070075a1a5055aa03020400440c403100310350008c0d41c04001080301a1510381c1114109000706070206034290200401d1081d50741c00c03c900b601900c4070f00201d006600340000003602e0300030000e03181d0728002000c1c0f004101013a4440d0039281d002e4039205000da00c0d0b8a840000030b43d4400701c003076299441580814804140d02000307040e4090210241c1280100b00c1d00c2d6481d00da941d030090310000b0300081130028107071002c00c1ca01001d95017081c46130003180d040c0900e150000702034500681150780042c62609061301d031507910109050007064080060154020000e011403d5842021400303410700c99003401c01c40c108581001210459440760704210740b9024442003c0d43c00b80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 42306191 1250 42304941 42304943
    0x4030806010206060a09020c0307020a150e27040c09020a021b0a21030309060c030506090a140105010e01020a140d020d021f0902030309150c0114060f06031f060507 72
    0x14442400060316540005a140d004800003071040c6040703894150b4420195000c21203440003400180b01c40780c0140c44060200010f0145140f44800a04003040014200440305940da40302d401ca800c2c038106e8441c0c101c09510030018a400584440e540e83e401d10001c60310031903001881c014800504054803650210300107000c04140e407000300c1c1548030007040200c004000c0c051090003200709150f1001d12102c14510070021032282c200031498880c035880352400c48030404541c1011a449030304010840ca000460701d64001400141000b107030300e54100c04141040b05014281c1805050b101000c5c0980c000c005428179254406811250b034007002e0303103035921016004044d4001d4810b56241c051101e0000c10811940240180b0a80d2110b10002e4540c0160aa4007000da070036000c1004105202d03120f040242000222082035555102e140d00c01e003038211890804030521507400c90050000c2659001900785490208540301910780e1102d207025806a07100c1c0501c4440c000e030030000024070702c0e00840500525 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 42307441 1250 42306191 42306197
    0x1204030e0103061a1b120406020a0201080c1218030c10060609060503010b03130305040506031e0114060d090201031812081e07120b03010618050603010608120a140706050403 76
    0x2103136990000b0303607410b42c6108001c52004801d00c81c45c441c0424030214008081e1100c821608100c0d00300c40b1b0b18500d9030040e00b03c00d006810030340803d0259600440761503013141c10780b9013082c600202584081b0742c420300680000d60b50001c0803050808040304209580e9904071007000d07503042d03010010210300140010321801c408035440c000005070450040040c0d904a60f10700018074659030710032404550310301d0f418004a051040900000c541c1c0d0700e918000d548190105040b440b2400d0312000d41e400b5a800580c400104034012001c50455a150303103090b01c07003520444001081c94a02840181d0240881d101100164600d01d19004203120081e150240300c11099151482d00342c44101c01c070802c142449030451100d01c211804644042d00c40c42c400580000107150004440c4800000207095468a5100803119030324048003038504e03006846403030382140c42140200000780c41e2180440d00c41c006460100780701c190100300c0004a0b4000e86001b01d00d50f07241000c842d9210fa41d860100000c0c60250780c26400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 42308691 1250 42307441 42307451
    0x30d050f0402010801091e05040501021206030102090a090209060f0309030a0f1713020a09020c03070501060b210c0409050412030e0c0109120312020a03290d171204030e0103 76
    0x445994828914025501070391002c1c2a6801c100101c40507180c0e2481c2100581c0811f181c04070604294881c150040344100f00169840040c042c0248031000d014201d603109901c104142e2a07582ea036a1205da045031030a41c1c0c05603c0d14030034400281e050052040a0511110000402c00540c10202c0100b00a850139104d9001e183c07000d2404a40c107400034a2078504807007203680840e45030b9801c0c9a0b0900340a100410140c22941c4600d0844143c0c2c0155841a010ba48082264030400c5028021540a0220051083d0804010800c4c0c1007440c0c10396440c64000e140320398041741000c09400e08541c060108420144070b41d0030186020b14001030384001807000a4a00445200a03c50105140821550503955807800e1810803829040c103403900c4070304406100b44511000d1b43c581003800030380030b4260b064a00090040500f07410b0300c2442100c2e9210340c006118810080100da42d110103801c001ca0b04005040c24410b405800c551a9203d903454100d004418103041104242c1d000407522000b900a03602442 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 42309941 1250 42308691 42308701
    0x305070b0405090a02032203030501050a050103020c060a0b010c05120409240303030b0a0e0c0408070b1606020f0c032a0102070b0609040609020a030303090308060a0303050a0c050c0a08030d05 84
    0x803040c0164041c282d801940200814585003007030f009503420078120444509003281c0c02d8101001d00203810002c03030200303440714010002071a0411800c0c00404c404c1c04c043d807400211280d516160140140810456591260a045181d10840003540c00990000c1115642d00c901c11001c90160840c1c0318090714a410300743e4440b501d448119a980d92000c8444861054a086139010fa01500c102c2045036081400460001000d215868403070b4000c2020080e1555503509198519061081e10b4001e015511030070054155203030040380d2001000c0780c00c03110058030303000f0915503a42c0d81c1c4500d114a02c490300c80456481c0a100340281400d1500e05000b240006480104003054240d005200c03010700102801070001c0e0303990030104480c581c00ba100c2c201c0025108400c0c0d000030700b810b24940054000075030741c0940750300300b41d044000390707030000011141442c6180c65a90003e00d6403003528501010001d0040c4108100601084180b10740c803001003125552540f1450302030ba490b00611120b85071a801c0c100411 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 42311191 1250 42309941 42309959
    0x11090405100c09050306040b0a02091c110402030108070b0d0204030614090c0405010b07080903121603030b04050408030402012303070c1104090305070b0907030501050a0c030c110303070e030115080106030507 91
    0x401196070180282103d55608d40b112030040c4402841201d20b25001c018114080d5030f00e6480c2014580904031080e40321400b41000070540802003070f0307580110701c1000144540030000a4a0086039074020819503a240404030001c041c0c09076038001440a800e20081e1a40480c0301401c1c0c40c4506c001804561440041d9020070007175800c20b20807031829040070441440403520440c001c111424000e0b045079600c001d1904082e82d540d102540c2403258060152400c01010341c1750046c510301c01e81c221800c0c4801c0c1090344480300e0300c0c400034200a05001c84058500145000c012100c3d0200d01d00d1a4195100d01d4140c0c4003405501041904071901c48880f100500e50340b8103407141403812a0180e4880d0308000f81c1d0b98500041440160010402d8480c83e03800100240c0b0034003032144103508050011802c045142c03c082c0640b441502c0e4001440440c41070f58615910000540368442c03e80d1030b0021407a885400441d005140700d00c5c0190110201c40c5010402100c1500a18100d0348a682110300f00c0d90b6840ca02 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 42312441 1250 42311191 42311207
    0xf0806160905100504030f08041e0b03150d0b09030a031113091d010903051201050d020f010503070c020d0609170309030702040213180b030607020102090d0b0411090405100c 76
    0x3203804150040400c0c48103007400091502c0f1a2528140103182030303142d40391381d940000c03028411214404001400e0160003c481c0c0384101080d4881d0545a0780380c1802141816408010213840c600103540e03d0840307036550380c07100e59800355402111010160406140f03407a04da80c8084c018101180c1400d21660144040500321524900301d1400e00003030a080c036081501400004488908c00d80054404c2d82c011042032107650000c5201c0d031145130350742030100ca0210b001c10050317102600c41c9044869090141e211102d804070700344000d2800c2584c0b03a6650105039100b14051901940181081d41400304012043d400071144a000303d40c0f180b40e81c402541403601074401114100c82d1900103004480c01424140c01a00e8021070300d138400c01002e0f448507000340c7d003280003500d4084040d03282c84200d00309080512984d904400720f44003d501c0c00707043c040421b0702400700c0304000707040c2074082c030001c0d040c42500c02c3c101c4500d4000500251007414141007035035035030340c0991507a01c025142c0295070f0981e5000d0104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 42313691 1250 42312441 42312481
    0x30b040e07051c050a050d02010c1202210c0f0406080402040612020a030f2618040203071b1a0c040e0702030a080a05180304080f010b0406050a26070f0806 68
    0x4a65406402a40c807108000f902802200d061240501000026005108150802c02c0d140d000143c5083c043e00c00a0802c4610500300c1000c5104010451490f01c040751071160703e000e030072266411500ca03250f140703080780b144201010710204041404601e040e0302c0382c080d5002da40204c17002e00080d0340b1001400d030f4a00681a00961149481004200061628091200301c0e4000d0f141414054050a04498820024810030160010005085a090038507001814031074000792011801c520b800c5001401d06001c3c000d44500101c24400c03403c04100b400ca40300320441c41ca4041e401040d00309507000540e503400501a22603084441000200340510000c140d603449296650b070202c058850810f09030041c4809070060803580360120211605100420041000300043c00007001907103030f646152801c42d01c0c0241e402e4802c6040440401c0307540d46100d261030a891400c00e0980c2d051440050b002c2c000048510340044500800100090100d0b06003840c008540c803e00607207055680e16a034401b814864614 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 42314941 1250 42313691 42313699
    0x11101140402010c050106030203120307021e0c0d02040213030b01051302030c120a1b02070f080601050d060507051b01050103060b030102070c092003090106090c09060e0907030209040507030b040e0705 88
    0xc00100590311035000c289400340500c3c00041c0e2181c50f03801190070504031218926800c28000103000003154100090b903450a102602c1c00084c40303280920540341c0510000740c512500410034032005543d102e5049075002c0c80d504a400507031035a68604095012024807841e40300e0715842e4100d4101041b140200d034072942c0d00420980c038022000c1880209140d018118070f101d141c0d42d503c0e804010200d000c441400303003401d0f001031071007519000c0d12001c0424070740c21142c001d4020800422081d11414058400c803a4840c4010806950302c10382102c2ea030217601080c030759008088000c81d4401c1c4040d8400c0f4107a900642003401070702d080200703260a03485082c0380104001b44e055010803207505203a0024240c00d1516100c0d222003000c02c0c000d201d19400503a0300401c165503c45081280f03002e1482092004041030900c07080d903d00d00384010300b043c44400c040f20300510381c1d80c0004003940d101c1d504640d01803100620411441c240484007d00502c1e5024442e4000e516201c0881410300002030b0300021200c00030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 42316191 1250 42314941 42314981
    0x90b03010609030204020d1107050604050d0f0509060a021908120c16020d0512070b1503070605070605060301111b100614010e030a08040e0f070306150507050a0203030406020c011101 80
    0x3600317100080d40a0400c80c0482c6070303150728043d90382d08050000c121a600810084c4458101030034401e00f07041041201c0d105100e03d20440c8407866400c0003c2d518400c0302100c4080c3c03281070f455002d0703041080104a0700c000710740c2c01805004011400d000350107010040c141504560f070b00d001002184d44640140d5401540c0d0215a1000620b0100c0f201b0140354400e0041c1e560700d046034010184241c004080444200031030008200c1da200c0981802c0400600440040c1b5642d49800c20280c528406c100c40a481c098441002501c1c07078500350404c1400d039800818640c0c2d0f601800040d60b0085941070b05060060040e402007a292500b2402103a040e141d1600c1070701b10000d4a0b20040d90403180c540c074240d405000740c070000804030311a41c0c00350005002050180c00b07035180c00104030440c0c40c0001c1c00704042c145440c801340f0054004002034102800142041075441c0c200741002c5181c411400d000941c10b100c0014040b6405501140c1189001000c1c1c0b5040011550503054500740ca0b84607547e41d00a0b0909 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 42317441 1250 42316191 42316193
    0xd031e0902030106081609050a0b09040b04140a03031a010905030706050d090b040f0201090603020a0f110309040c09050a05030714010c031106010602030301210c0501080613050a05040201090b0301060903 89
    0x40c0d10198080384014000105a9942c21040e41090603184526442c40c036410340821107100240a51039020004080400541030a4070005840f6080608094401c6c40313a040020100860880500c0181e54181d080b10b465403040c1c980100a00482c0c3c511100e82511851030300c103d07500920030307402030b80c3c03000303002d4403220342000c1d81114280c12001c90019a1503e0760713100390218948080107030090f40120104407242c24603000140c11284103510000c1090310402c0901d080715801650030000d05900d00c1c00b07003100401085558614021031001c160f01602c0c01c54421011600180e46d6001c40f041914080600390b0340300b00700350301e600b82c1d0310070071048511b001460040396200c0c1950b2020701c0d20900340707507402a410340c0e800b034a0310100360006005644004014041c00401d0b00040068518401c0540e031040c8517640d03a00240f000e6403054a05200030710000c200320342d9428407051580c100c442010052864011074000c05040d05503800c2c1c3c040b035071090b800702d0510001411281070350f0064403582001455 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 42318691 1250 42317441 42317501
    0x2a09060103050c0909040c06020d020d09150e0418051e21040308040608061903050d0809030c01140f06090c0a050d02040e010305010506011403090a02041d120c0d03 72
    0x20081c80440c80f82d00811a05803141c2d224880140128001c8071882455800c04002903d840310304981e84055500072a040c402040e4001100d20942d042c00664103d42103d2490603119001c0f0b4441c2c0c0740d40107080040c105102c1014000c02d0190714040c03c02c98840c05001c3c080c444000c414409550080d0b00074008000551f40782d5152080e001000078180d5241c603540303488909190b040343d02300d040019010800c1c05002d01d040340045081035050707000c02c013031585982c2c1e0341c941c1c60111511031414094004001844900140140ca060b8801d6100034040070b003e0a505103102e040403107180300582403180c0411018140480040d01c00c1289101003450a00141c20680d80d90704140e90340f8200d0744d000c210120709105009800ba00951080c2e001141070708044001500505e01c0343c1a1003030300f2005100300200008002008a8582e80644000030f401c550601905d516840c48501301c10f641c0304d56421a400065aa4007c240303c1d1590f84c02d9031044a151b8808806940b0f0441a01c04440954040c2d4403190307079 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 42319941 1250 42318691 42318701
    0xa0815061c050f0c0a050604050103050702010603080c0127050604020108090705041d0c0d020112180b0903091011070b0307230414030a051203040515092a09060103 72
    0x1402031180001510326020710100200344407003210710b03400200303415002101c00c1018a4419104540c920764050904002ca083c1340203500c80c03241095120408070384000c3c000e5200d2000b454004900d680c0e20402c101055000c1e258090301000d50b610010038040c040100c414400040681c840042d091980319900111002c0c48040d1403c81c0c0f50103a094001381c9a0794a10550011001400c00008545c4050b0001c5007850064062075014244140c03800006030303484580c00d40ca034410000006400c245a840c500650141e0700c100804518052050000c0d0190000140c1030003503040711440a011440c000446880c080c0440340e50060744880020300c01e101c804000356600046610704084034030721401c802c91410922034100034113071400142c02e0200740340200008146070340507070007403448050340e559044d40c440b200150342e031322140c0200c007003810800140b040d140b1500e504c9203001f40328109030310a580c6410301e452442d070003400d0707204e01102d1200980110141300742c03000381248020ba40700801900540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 42321191 1250 42319941 42319951
    0x8031305031902100501050607020a03031805041508060106050f04030f030507020613060206090f070b0d1103070201051009050402090601030b0609100903020a06111e011503200a0815 80
    0x1c08107116100340c07008041c000c0d81160406a0040000c00d0303080141030110f4006070407545c000e00302007040401680f01c070481c60084a0303042c54030140b08114803886003c0e80280784c001c03580c071500b0302c0441000c07070907041e04100070380b002d2600307603030899a07036a0054450344111401d0500f1160240810404103492000c40c0ba922030181c07c086185c9a0103074001601c0c1c0c1e010340304000e80c10b21702d04418407109034104011079002032410001d2200e01018181140d03900041d204652800700001103003030b03080030160003010036180c21034a80c0d600d03401d0049000c0c1c0070b04411101800c0404840f42c0c0090007411600640d4006c54000c0e210010f0350b180e400044028052096615030462420070040700a41c81d01c00076181d21691f980e8600381c901c0e0130341c070400c4140009680182c0c100310302d0716290640a000030900d02d04000c0394044d080c0e884220b01404c0f5025280000c0185c2c14500b0060f000030501524003c0400362170941c0d01c041103a58150000c001e00e0071001c0c0143e101550110070308210000501c2002c98102e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 42322441 1250 42321191 42321193
    0x603050729070309121a0a1503060e030903030415020f12040501230a0c050c061206091e070909240b07060f050403170a11090607080d11090f0306010308031305 70
    0x20780d49a2900c404045c6542c1401ca42c503e00703041c00c0b510035034090102a074000307003092030500c01880c40d1141981040c0e142d0002401150f955130b4481000340c001c1045506d000702c00340689841f160f03601340314080501e1651494000d40142903400c3d00e03074100030510a4030303d64810380140c01d01d800d1200440d14169140300c4800401888219a009002c07901c0252244800310f566114200905103042c90818842c0c000c1c86000d10700602003010002d08121582e0340c06002910314400c8ca650708004200240008040c1c140c0b0740714480c1c00e110920f42d201081000740c07203100400703011480c0f141c20b00580c40d00c03c12080d075074602040302e410302415090788020058180110f5001c41c030214140200b404030350301502c0031030104040c2010500040245c05a03554040da00c2e100c00c01100142c176040100310f02c900c0800d903210300300000303e040800000c0d20580b01b9a41456008002c2c00c03901070041d110580c0f04840b01807050070300943c417840c00e10700080c515040e40e501940c0c90b82140c940001740911000c5082c82140c003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 42323691 1250 42322441 42322457
    0xd080a0203090a03060b031e0d110a0602041202011b11040f0e0102040801050106030b0901060903230a140f070b0702120c18011401030612030e01031e06030507290703 73
    0x100f41c0c1e4004420000d54042c07940021107090810400d0703c0c004100c2015110f424a180b004030444d5408180101c201846042000070100712843c0c00703040036030000c00101882c0c4041400b0968414194103a110325100382c9590503015044922036030702c036488070802071051002d10070000c00790609801c24440c060380c0c0c62010070b0700c4110304411826a08560040c44841e90b4030001000a2070b414000e007108400103542d540c00a50400000908020881c000904400a03428411080301c0c07480604d01e00b6943e070b2a059079000022407905000c000012900e0284901c1014801128a480410102d0803502150f2440385000f04aa00388000051800b0140e04140503036440d05031980c0f00ea03035005040d006200780c408015030404416520050700e046425040600d03055041c00b50400e84890801c0b940d81604058200d2522400101c02401c0c00f088050060041c0385004800c0703080360b03040340301904c0c428416070350010740320f0302014985400d4580620502c03800340100400040008001d1210f03d010b4680804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 42324941 1250 42323691 42323707
    0x90b130302031e13090b0603070c110a1716120f060f05101809020a03021c021002010f050f0603031b030f1305010206060d02130f0b18040314090d080a0203 68
    0x10190f18249401c440200040e202116401060350035000e0050718008201050544000c9000c84c00010f100000307100200311002c05202440c0382d512002c070401803150500940310340c5030000c920042641c203019480341091501120b14aa15010300b510b100c160030481070301340c0e6140d004250402031410748040c1e943e080031f2070a008090286901c18a00941c0001025107401303044c481103400085410150781c41c003861000180c2d00c10303812104990701100e04114880420415003ca401c2845009600104070000c400400c0d40640118003001650340042066a860f004d161660140403a01c072a4035810800c0307030245cbe805890f46150314a2102c2c0d01141d062024a41d030040c8594025210700310b500030560410045980d04110f101c0c0d01034401d44101c2c400758a15404941114640035405240c0c503100c0348140e0304100c09500461313640100506c00342c580c0859400311002c0d440c00b96400c0d40003648102c000c21441c10a401210904c01e40545081c0d503a14081d25611155000700041400714041081510303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 42326191 1250 42324941 42324967
    0x20a09152316060c0905211c0203090d06060f1d06010503100905011410030c020616020c06030c0d0c0908100504031403040308010807080705150703140403080901030c03090b13030203 80
    0x9150406807940101242410304028100704000c50746400300580e0030343d44400710310208059109a205046800f04100341d108c01764254080e050145412488032140030040c00f099421640490714a20049901e054464201c10200c140040300c0422050814021030b4aa510a600442d44044001d9401501e01c1d00e4000c5007058880aa00800069808040301009441c000071040305a82c2c2504041004c4503a007a400380d02e13800001d110610714550550082c44060090040041c80640100002d40c0c0b49040302c0382003400c2d01714504940c0c09510b8130b4040380f003403030051241c03400b03035140b4074000c143c0382d0f0024103440058400140b04904000c003440100042100e440043c0d8000c900c07d4564617010742c14041c24518190b6070b94021800b580c4151410007058407078100e103600032103041d20101c0d510300c41c40c01d00b920f1400440c10b0710069643d00050000c14801450040d219040091ba018003031080098002c42c1900e031510000791019403010040345190b4081301b210642c2ca4030038010b0341e081111082900c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 42327441 1250 42326191 42326201
    0x209031911010903020d0b0901020d0213090b030604050a080304080724050604060b09012003161a0408120702070306050903090906060c120c010f020a0915231606 71
    0x3600820104626100400c400c80e60308110300701d002e00c0c01da0511403851700001d0010440300c030b02910007441400407803003221003901150103580c0512400d660310341d035624201c8030b024810f1080b658440d290031f040281d10b1401054160256820100a000f03003207254850045940c80900112604002041a040000d070000070311001802d43c2d0445058015020044006403100100310314825441c190050209518820503035028100078a0b00214001c06195003030544119074800b401d45100c089012a4240101c011020710380e81b041c001203894494070f45028591a50550300180006014042e00203601d007100e04081d4451014130440340415500d444041c04c5560070740d01042503800004030b500350760030800d108581000d000c0c0ca400b4035124141e0101d84d00d5045482c0d900840110001c0d011000440075000400d01b100c040c0001c44d50b651007132034080d001c4803c034803984084085041032020344a00820501d480d5898256000114117102c039a0499280c6c428001c0c81c0c24a000240c0c1e60010501d98810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 42328691 1250 42327441 42327463
    0x7050904230603010c050315030c030109110a06030b060403020d15060b0c0f0606030604060c02071a040f060302091005090307030606090207032304090b01051c050115020307080702090406020903 85
    0x2112800ea0808000c0e1507a44005005600076030405400190207503021003100e9100c41e80e83c05424480107614006801e1010200c036030799056007444090b409020520158a6006800311011494039a5401c4103405407100f042095030f0120083c0020005410704c58090a241c1d4400c202214000140c5c038085800c1b41e03402d4201c1120200080f6082041c40b6003005281034440c1003200601c031a00e00300d40001e81d03942c001440180713443e460f1440f01c44514006c00504014200c54414a04102c8901244060503081841544c00803240c0c0440010018001e100b15070000c40007134a41001700f5614001a24194814040681c05100d03011002010615511400000d4042c0c4400540e94240302d00b0300800712500c0034445510003105007001e50b59000d09404840c111109004080380034040240140c1d004e000f0f030710911703111220444140e0124003580d44a24103803104544092807095245078101d03070b01c0c087c01000400040302005401d0152400c03260080d402842240b0141c94031000c10042130500181c004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 42329941 1250 42328691 42328721
    0xa030504050106080a0b0402060f04030506090606030c1206070c0507150507050c0f0105030103060b180c03091203010602120d090203010606050c010c0806130209010e040c20030403120807050904 85
    0x106000c20030100380035031402800c0c881c0042002ca110b681b00d0380608407019000a02c9420000350059090b000113081d98000c54100090764960701c0c3c2407502c2c6850319402c5170050710030b00812520748100e10340106031024008007003004103803076036960105031401c1c90781034800c0c0c03442c1c41400f03000a81c0851805100103458541e5662076120f9410340ba001d854403804c4010a84502e1a030308480784166030040c25a411a60801408151070000c040070032800c240f000b4083e801c10380b4030b00803c001906000015802005401e04072180c0b2144101041c1e1640001e024a20043c1c02c02c440d0888a8034400c40544001000e050b000101d1080d140d0010303003114460ba000310082130b80800c1400049a081c4950304405074181400c2d4941e01d041c800190b81c82d107140603100c1089501045100990348101c2c21400051406403081000c141c1c02c000c00f8025103200c0f0b00a2094200c450100e007d808004020348085030390018441010708207502042d00c0340000102504200f00040c03003022201d03a950b000d803c03441940700b5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 42331191 1250 42329941 42329951
    0x402011707170f0c030402060f0c0d08010509090624030c030f0a1a010302010f350a200304030c0206130b090f04090f060203060a08010501030b01150f0f05031b0a03 72
    0x410b01d1103404000a064404101444041200820020302243d81c0b0550499040b6994055900c0703458003030091002d0444144260620310305000c0d001140360b8140d50b821107050010743c0d5840401035440d402102d4040b400743c09a641d4880f4021b004035074404500c4010184c407100040130000c2480c00300f08651203545540704901d04c2c800e010000361800e0700004203089001c601d6040d90006042c583c03242000900b0400030b21500d0307201a0282201000b20f070640c0c841c200020b402150124014072003540e000c000341d4600090b64002400702c1c1c20600203041c0076005141941c0d40d40c2c40c00d039041e500959007613030402e404101c2103849034010310804d0081c0c0019000307180c4650b280030600c4030708001031540034043c910b0115640c000c0b40705401d1400c7ca0543c40399003d0703980c2c2e40e0b0101080b0200724035480340c0074560030280040700b00031100301c1c0c3c1416161003500c00009106c41842c101d544048405000010400dc4c3c403601d41254492070046078030a080c40362000183d00200f075400700a5001d42c1c804000245c1c0c0d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 42332441 1250 42331191 42331217
    0xe010c090501020a0b190b03010207110109090b0108040f020d08070503040608010611100c030b0a08030c06070302040302060307080c090d03020a02010206060a1401030209040603060c12050901140109050402011707 93
    0x95204015203820302c01440744c940b05585040e46014040c1c41010000790444041d4a00d9007190000100078001400a54030380840d07240c04074040e0540c031070301400704c0d08032600411410014421070084100c1691610302d107803919120310108555060050381c100410301120f030081881c6000500c1c0c298402c40045941c5e070b00e0010024071400c8181c0002d41040076580c00000f4903203000600c02031310503039818002040e0400c40f1059000700409440c00c4d401440107600001c1c0c130100400603140c07202c906000e40e90326a03501c0004500324400c81c00000d41c0074205201050303209202701560369001490001071464032081400080030840c404204500580c841e0720390404550f0706011441c3c1010043d2800140c1c5402c18000c08032005403030800c6810140d011038202d10503642c5170084001140c2109007000420784900000744109400f040101c80c140c1450017288950381c05120b107003603c860703140c500070803030b401d000000c40030b000003420690411200e02401b908070784802c02d0a41c00f83c1c8454540040b0742c245 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 42333691 1250 42332441 42332447
    0x1416170c060408072d1103012406031b05070305030c0d11040303020d0c1e08091305010f06090602070302060a18090617010e1b0a081506150702030705041109040e010c 73
    0x1032217220f1802e5041018804803000140348140d512240c3c000340c09101c2402e4000428010040c0b6074000380b44070728001560b02281c03900c2204030165582030f5030500885451001f1407010340307441140391000810400c01d29011900c40e8001d540c210385c1a14000d849c090b1070240540580d2448100101110000902041096010072000e1905e2240e400d00d90b101d040f040d16960200c0c03042c07100c505c16101d40c0c000a00d040082d020100d99640e013004000c1c10100544140810040109000d944074002d022400800c4080c0501c0d00c45e000c0706c10b43d9004011490541c0e09000d0f554201000e00410300c242445980c801800c0035400402070074030150006081454118030f4220900404090703482a45800f10703000707084501260f41d12040c000451080510040c49000c50045c02e81d50384184a103008101351480a00344c4000c030300b8003c1000f110084030b507551801c40035200c0d10803500700030740c1a40505c00401580c1402d40002d101e81034203070b0313020b0704068105001c2001c0c0c407104116043d850b50345100c1d400c00d00f90 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 42334941 1250 42333691 42333713
    0x3040b0a09050f4603020a0501020604240b040f0c0f1d0f0616030305041a0108100e12070302060f0f0105060f0304021c03020604031416170c06040807 66
    0x2e00302c0d51100d814642c0000302d0b0300c41d07082d0302100f203a0f642d01c1c140601c080c0c1401c9400e031007001c2c3c4072443c101c2c1001c8146210302140d000c9000c101d1081555010010f0103600c00901240a0380e0402184100043d00d41880307000ba021008049c1c1c0d14640f02c5480d110b40d40d03114850700c0b030329008140b004610141c54510092100481c144008248000d02583d280170b8215540e05c030103843c6007a0340f5081c81d0b450b040006070460090034416803262840703000300300405a02d6007210340241c0c42503524010764000d1001035a070f845c0d824050b9030f00300d41c13162800d62000015504000307900c9074079900395100803000001d040550b07849044180d01580c40201880307207820b180700034154032100d80c40e0303507003030550403d0002001d62003401888114800b021001c54103540d03804000d41e2584100d07607030345000c914031498080d407240c2080390203401181e0b00000d030310010141c850495580d10030003001815480110340e9081c840220080700c08030005014040540d140b00204420b6010741e02441d500d0740c84580520341031034000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 42336191 1250 42334941 42334949
    0x3031909020a0305031207110309090402060403060e0d030b030a0201050d150531090b07050307030f05041101080609010302030d0c060207050f0304180207030801140f030a080d0c020604170309070803040b0a09 91
    0x3003c2c481200c0d0103038000c4164ae100a800311401c500540b00d83c000100e09018681001d00072516102a81647d240700240a44071104192014406180d11500701511000250f0000c2d010030410092504c4403400c5a10201300d0343d680380c554010040e1070300c01040520711601d02c041002644001c140c140e40c0c615030492100501c0fa48c00501214402da99003030303200344000e84800207110000c00800c001d2070103034215484403120010204090314190902c00001c040518003140440c80705404140d80c0c1c281100018140c940140061010300100c0301c040320120740c5190107480079542445650f00042c81803208402c5103015500540e101d5003415803e02c001d860083c609541c10b4810894000001d0700001018111401c080100702d401d910f030340101e0351f802ca014101c61307490b0161b00f106204119890010b440e20b541c150604006143c45840c0503079071001c06441c040e050140700300e446402d00f0380f150010b56018401c82c05881c001d50b030ba007032803600c0c6802c2a00714001000e40420f003460002e5005016000030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 42337441 1250 42336191 42336197
    0x3010f11090a0b0f07060b13180308060910050f040221090c0604080d0302030703060803070b041103071802030c16080903150105011b02010908100209040c0302070503031909020a0305031207 83
    0xf9541d080031482d8411160001d010710740711f4044888941c0c4a1444500c01c0f00c429805002c1040e204411440d1000c005c4001c5000c1402c24000c07032500d0514040c4030b8820420b00f00249419801d0101304410401d1604603a54442d400b04504140c80b0f05000764000140000d40f580101d5040941800d414400c00c802060700030201072200700300642c0b001a102c07950f84100c4c20010780ea6154580c0840c044d007a070b904a2400b901c0006641020013030030b00c2da4144a50b006805401c60300d5504c000b0141c032128144a0182e40c1d541c442e19881c2e40c5e912a034010364100307590328607407403070540c0f0f001c074540d0072900405045c2d4413064081048403a07406c1c103000084070742c885c100340a03550b07604000010300691032034801404a007000307000110459008030702e0840540010001c64603179015000d0920040d43c8100c6060340164100b901120a550181c02568031641d489406076041d90341d500c0c503000c0d500c00f4610321101030342e0700e40080c41c01584a60060401a601950255a480410403170626110b80068800410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 42338691 1250 42337441 42337447
    0xd1a0301050a0e1504050c10020c01020f0304080d1209021002070e0c0a0c1e0c090603050f03130b0309010609020304060507030e0c0f04090303111602010207140105071103010f11090a0b 81
    0x10f11440810322200e000004180481142c50b1030a10500c1c00380c2a031031190708600b01c02c01c90301160760006031540061303600364200d5102c5401c0001041d12802240718401307166206144412540d030081981c810240c0381800001461450f580026980c244130700c041e100541c220100034043c40f62880000c0d50701c108113000041c600341040000030100c10855001404492000e640d0703041c00000d010040c5039498101c19080d00260b00d80300741d20010200fa05c01101c6d503100301116442c81280c08001e031010350190103610310f0302607c0c1444104607a480200402165540d174240171030709071194400b07140501d004800020349031038401e40107804c50752802c040001d1640150180400caa903842d511044c48441a0f50102e030b88031051a0a5019194029004803030210214100b41d54a07068907103048541d000364215540309546400459809217008039041c00a4001c1100300085481120909508003000e000085c1299076503202030115002590442c0203503000241440d03451814082d8200982059807420386 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 42339941 1250 42338691 42338711
    0x705070203030301140d0f0308061801030c1e170606010905030307050709020c100617120a0f030902060705010f1a0a0605030406090c0803030106180b040b07060906020d1a0301050a 79
    0x154030f000c1403040f0210100680c904014503100e02080c04021a0300402e00d10340303403031985000760480c08200ca60314081c102c0c00782400341c01c244021a10f8100c0ba0000b5801c0c03d841e00b001e25160401d1484002d880c0c408510310000100080d0880c1c6000b110000c00015003400d044c520b0004000501943c41240f01b90b1081c0011401f080001c030f0300c64200c4501c0d00005954400c00344049040102030310045564a1400d00000341a0b08405020405200890191500383d410b015205d0214040c42c1901000114405107100c0f810303010358042c107a140d00080169040146590780c0b60b0030340d44803800920029860340c0325044504690b42e4251110101204c01c1041c050034004020501e0000a001038006074450020b9414850220740340c3c0e014102c58000e80c1e58941e103620015125180c0c43c8401e1040721510480000c09090701e4040d0b500b81c6561040413480c00ca4643c132080c0141c22180015200300782c6c204400504066244a000c0c00400c04150044194610100305400c44000402603681c060600750101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 42341191 1250 42339941 42339943
    0x60105061c05040309080a060b0306070201090b0106080405150703020a0f02010209060a030b0a03080705151f03081e03090703030801051005030613020c10090516060906030c02160b09090705070203 86
    0xe072060701c80c900e0018003643c45040481d09041c8945c050059400351280da0000d10615070410203d0903800d030100c0b006030b12600300803803c80d00c0c03411020340740c07103042c50050020b1441060201e411600a104450742d5058a111100061200743c0e41c10010030307400100c218010750403481d50a49040ba9000850400030603201203080c51050746e04030001c01d50344401101c0950b0740d20700000003854009421710b846550b24684960380d801e03044019011440f00d50005004000300f00200c40448591495800c5042d14642d03d001e40b0744c010449100a0360140383d80c243e080f900f50707000307184980c002e28010400a40385060180184406800550045489414031081310b41c0050440703070800001e8444101c0c110380c680d52040203010b0244004098000c0318202e620f5000e10390801000300380203a041d0362403110035070740180601d1040d215034400315111410421031503010b540500b24599050042e80d10314088400c4215091545401c4040341034400314a01d940d80c01d1010a07a03074880c01c0b60070203910b8035a040e000a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 42342441 1250 42341191 42341227
    0x105040b01051210180b0a020f04090c0e0405091e0c031c02030705100914030705060c09150310060207050108090703020402090f18090c01051215030a0c0303020d0206010506 76
    0x2060007800304403694aa00903040048031484005a40200081d4004c03450520105071003407000d030b5040703186d8004034003103030030134400c0f1003041e208400400d2401b032a000e00c08000c1e120042d0b840c003e100007506803002c41e8583d4000c0c0d52040d6800d43c00b40c154000380c035007007814006007001068001e03400b000c0c000c00d40e43c13000107031007026030344030701440d602d0400d1402d04914511070490300402c83e002d050139038441030b00300360010403000d4400c0311842002030310084400c0c1e17070f401007460213881d60b40820b0110355014540001070056070400341152005070450008030003903a00a407902c60b00c24414141c1040901c2d4140040c4c4007401091070b001c0d4050501c02030341e5541c0e105601010307118075030004080c4695a03840f45002030300c55003c1c01c0701000c2c416104d0507180301c3c8001c0312400b45c1d5015200c1488080e41c450811541c0781c0150381c00040413500e41031035884410100d840c03400e8044c41100c207800c021030382c030048800095119030300a00406100071402414a00181d120343d0040b070003882500ac42180c101d0b04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 42343691 1250 42342441 42342449
    0x50a0f090201081302150d0e0d030c08070810091119090e2e060201020a17070504170304030222140105061b0703021302040e0f060d030f020111130e090105040b01 71
    0x151000080040c00050f09100050100c6c24142c8000a800718031241184c20040640c0025015107401000c16501034083d1000450458001420310300020002e41c02000030075082003505104544182d214600c1000b100c0e5100e4404021b82804078441083c280c110300d01c4200c0c81a103140503120503103401d4036030842c290060039004000360456203094603800c000c01c498641c600211110701842d555110007a0003580810110030001e10003c80d1074580301070341c900450040f034a07a0784452400b0711f0001000c06080030000070980303501040100001580c3c4500c0680b41040030940694224940d00c80800100e404003503c0c0360144100c040100803984e54141621103802c15460503402001c405840f060418101d500300a43c4086094407070003128295602800c19511140480140e90304c40c0340200300d05602c12140f41d5404850018440300003440780403030a00c88031041c0000b1407400c10010040ea80e030782041c014841045609042080782c04115080c4542001e0001d00801680c1081e840d22a500401402 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 42344941 1250 42343691 42343711
    0x1050a030308041707050703030e0111120a0e060408010f1d0703030f050c0c030607021b030118031b06050a151d010501030c020304090509030301060816090603050402040209090a050a0f09020108 85
    0x1409441e02e00e4100700c0d003141b40c1c414261207001da2227240241c01202444d0715640041c0c485450358048075000140c00507256a085407442c140705081d00c007110f01802615a036900070105100018207883c0900500d1a03880601d400440c100d0013044180c0c03060464542d01100c1c0e03500030081000803c4d003201c2c1d10183c0c4440340c03901c00d58903541144202c0c0340035514100a43c05208040401074426404221440d60092051264030100c00e128101400d0700d482c1d50920070146403503401e481c0040c4c09040300c81040e01e88171100c07003102211a1202021127108580310100c841e1a8908014950f009050031800f5000500080554407000c00d040503442a050280358141540c0d80c1c4800c02d4240200305807002440714034420f102c5442c1114007541c59030820701c103c1011803d54800300d0419401ca102c205e0035003419643d40d000c0d4a00d415000c8000c0c0001820503a0025400c0007204450349541c090988900003030040450319081c054191001c075884005c9040c0f0321403801240d500182c0e4407c002c1900164894 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 42346191 1250 42344941 42344963
    0xc020a0804051c12030c0f020a0206090d03031b03200412060e010209060a020102091807020d300b101818020d1503140a03141e04090b0901050a03030804 67
    0x703000007010850951003d0000c0a80c1000e8650320745c0e160300000403500b11503450404885032910240e80e601c040d014005d5205005200c50f550a00703209501d862018028600403038103000b81c14059806011040340940001d40721003c035039568031520070201800384110206803400b0310b055650300c440841080004e15643c2c0360002c103181c4100075010785545440081003d07550701c00d031141c080d00070341c040104140282e0b42c82504210240d50314018510604454003c1c1080080420342100e40388500b2180b44240c14209440407901c4001450b66140c00103421000aa5a040c5030200402e003440c507103c4108020f0380640392910410300c06406011206800360000c255400c0032080c1007c0c0c05640c00c00e03c8800e1410382141102c806040c514000c4a0094100360004081050b9aa480d020b9220b00500400d0030083d8503013005c68440c0c001d00a156091080413a400300003150060140d0107a0300000926850351460255464031036003a40c01801e00f15211925217155940c0501140c80041015240c03000c91 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 42347441 1250 42346191 42346219
    0x504061706150903010e030f0c0615030c010804050a0c0605280e0d0620030709080102070206030f1305010f050105100c020f0405190608060f0f07020a02120307060e03030105040c020a080405 83
    0x9402c03030000c6c060a0f1301660f49401c0c0245038400c042e0018185030340315226807000704480e42251060040e66401c054003400b48042c404c0010354505502030b000300d0b128800e100e41c003000f00301c48043c44000f8114658805640d00c04041d02c4503074103940c1e00806625550003085000f035660f0030611118100d00b0944030041d00d41200e0030003c1c02810380d03580e40030900d030700f030306100b0440e01c0d074400218818200350310b903820055140da8003c0e00301d0081000c000d41000c41080803440d40c4200042186c1d00c40c005040c1c52102d2140c582c0c0d01d40c06d4640c9020071300c1c240d5403079070018045882c00200310302d020720581c500209040c00329000264032224032800c860040341d5034804030b81d0300c83c0054403140304480d400d5028880b00d940d840d030345941c65100701c2d40d4124180145002ca001c00406c41621030103080142d00600e0180110703000c0140081c55141c0c2d16103148010442440028101e002d90480300551101668681d0b150409000540f0009103170301b011900040c0790750000030300507425103081d0b61050b5070b00750342d200f45 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 42348691 1250 42347441 42347443
    0x40b18091609020406030e0d090306020f0c0d090512120d020306041808030604050106030e0309150c0f0c0906041b0c0c050904050604020103061401120213090c0504061706150903 78
    0x5000400142082030000803510b090250010000c55140b0b030740403c81d2650402400d45c84401c2401c4000028607981e4081000c5007640d0082c0c00e0b0300d00c07002055403801c140040041c3c40c0084c5a80e22002007040c0f800d041140e40303400d20034101e80700e00b01000b0703000e100c0e0040c007400c0c0745100310015a20420b84c04004104240c03569801040004419600c1200655860510100540048408501c40d03801c182c00421054800d028510140001c4001503052100382800c1008083c074005a01c03503d46803d110304658001e04001642e041d01091018040300c01400050041206000b05007034055420010410318840c98140414150040d0b864981c124140300c1c41c0500e5001c0c86603100a03030101986040c0010b0000100f41c250249100342c0341040b00c035070f64012040a5900700080c140c01700c0d05400c0250500c0c00190010489000030f440c148001503200c0342420116900302d21140005070700400c052022a0b0880c41c460541031a00354010b610f4031341840040c000d0365401e103030b000c2d0007540800c910f005614 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 42349941 1250 42348691 42348703
    0x605060a030203040c0824011512020a02120d020703020c030d0e0d0507030602030a0c120608030d0906060308030103030207030210031503080d09140607030f18020d02060d0203040809010905040b1809 87
    0x43d1102071380c01a0710340e40710051f01384244c600b040c14a6443c450000884040154000c10a144540c503007200002400c541400290440d10304c200542c0100c0c40007004916000004003101550720b5001a00e0340e060b420001c0c500285640383d140a0703845075a0f100401608444c40d00307002001280c0044641c44185040743c146030b003590000f007070342d400070052114105c00d036000081d0aa03a90743c0c2c0c040f00401003100500030f0380c4403445505019001000112060061a0891000c00307000e020701103080703035a03a40e6056881d4400d920603401600b03d04001c0c41103280c1003090600b00c02e51340c40c00380400120704040c241c20780300c44e2000604400000a903048503c0994100ad42c041d07410010849007030065240c41503c4000c200d03040742c006490010042801500da00c0f404081c1e070044610000c1058460f0f087c00100e2411000076688180d042c4212882d503074541c0021481144a000b141d9110a021000901106a035030480c6106509141305107180d6200d5202c854a000310810009070544c0718001c0050800c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 42351191 1250 42349941 42349949
    0x901090c1106070305060f0d0201080109020c03070f0501061406030c090108060d0b07031d150c0310150e0114030705070b061c0807021305100b0a02030f0307120c02010605060a030203040c 82
    0x8003a0b40104100103405a0100d0b204503002d5030500e018500180802040c0040392000034040350058005001941d056405015000754880481e80b802c802900c420300c400d94812000c071426034450740c041c0125161509440041401502c4c1141107050162120000e03020701c050081c1044000000520681d0b00d000e9800c001d0b42c0c105204e03001c20704222070014051f01854188144100100c05010098603002034001e107403210340c070031000c5070340c5503030f1411121a840903250341e0298800341030118502c982c9881c400b0540401707403501d03e20703444a02c00141250b4002c061046403100140300b0810041e4010701110380596200789a03204503900c4a000403e1a04412201041107146419020070064850f00801015008440c0880681903618000d4240ca00440311000c6485c54100c0400100351a280034244034182401600c0c00e0400e049100340d026003003202e09000040848002c0c0e4040d025910802c40c0c240d82c0380c8000d00080742401c001c030700340b4171801c000311081607030020000e024800034041d00d60281c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 42352441 1250 42351191 42351193
    0x203070504090b130207060506011d0a09090c1706090f0a0b04020d03120501080106090b03011a010503070201021e07060b01020105010e070509060c0a0501020c100612080f120106020708100204050901090c11 90
    0x3806c450401000801c0111110f6022804001030410701008540b00c80009940003000c4d15480b40c02c142d8500040d100203081214403011803040810182c150b030040000a00d032070b0f00280064a0314041e84c914280700075405941540222944001203450034030000d42c0981c05941c0240c84d88040e140c00c03074100302e41d080c0380c6250502d803500210f4450b0b0306411030360803a0300c2e0450503c4014818010142220b400b05040c2803c0c580d0b113025541c0039405800034681c4101c240c000103040c1400c008903005010b500520720b0340c001500040150811010344600319001c40d0038402080150306095003440d01e483c2c0034042d20140800401e6814603640e1340c600b01e41c4e1030382a100a65070403403464602036000c0e4010208081c580d0003059403070f0407006000d1003450110b841800e1a00d40c10303a0561180d0030a9409403c072106a5901004080e250100201c0c1141c02050300d076004100c005c1c0b5102c0f0b042d0800c0001d1501c490003500400c810005541d41880c450b055a0305004009803084178914140c400c400d00d0a041005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 42353691 1250 42352441 42352447
    0x2130c05130305071a090f040b120105040b06130c021b0604031b0e130804090b010e03010c0906091e03110102030408070b21060603150f0319150203070504090b1302 72
    0x10040003082080c102c50441d840c0303440f900c3c13040c001c01c17156001741401c50b5001001d40c60000711b1840d068201e81b014042c0a00400110a4111030141c250b800464050722244100c4c130500070355080c43d40300c404041c0b450950812484854100c000d4850700301620080c9141c5900001803d140e0303415084900442e40040448149107801c14802e803510000e218440d0f40c04220342c0084c0c0404e0707403100080394155100d086c85160500304000704004041c0f00012904020715007000c030849840910481c40d080586840350450f0600e4001c0c01805910141c0002c07603911442d41e01200c03a01c8421031258240c952001d8046018045d20740101d04d0340c00342d0384c0084994460490000303807000c0200e005010114a8140303010603401c5400c1c2a61001c602030f80d180703070061010400101121015181940340c044010100010594102c00080c50481e07500082d440c640c1c003540b5804200607080f1040c1c041d010a0007070070f600314a4004400703042402103104203084a5200d020b00700d850b68928041a44a00c0d83c0882103413 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 42354941 1250 42353691 42353693
    0x1009081c050105030607020705030d08071806030519180b092e06060906050301061808060106030b031b01050901050c010b0d110103050f040b0604020a030905060708071b02130c051303 80
    0x301404003881014064014180840c040c0c5102150910a8400103001003040021410007100c0101d0300400520030000e92410490340c14003615890741c0100701c2541c01190a0a10f040c13849400c2090f280201c141c1494000007141c031058034010b5142032078100c1c501c000150340c0c042800d030922440744c40310941068080c5c01407482c0359005181c415044103201c000c10110752038110642d283d2540d801900d021440520041024070702c643d401001000105c801c100d25590340320441482c0c00c00c20b0304103501181c3c59411410f1103090800c00d00707a0460b000060301d007207410482d002030124401e001c2c0c00c9040090000d00100701107402d4100010340c00014280301ca440d044c5003490075407480303640f1202e0b0020741440c020032070100e110464240255003122041c0c8994a800c41004029880020100305054645a20700f0114106002e2144603c1180d2a0485189010100188221510314400d4040500240200050b0311001440071007650540740010f4801051207080c0d60f280142c5001800500a400b0084 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 42356191 1250 42354941 42354997
    0x30207060219050303060609030102070b040b07030b06041503020901170114100503070e060a1103040e090f0a0803040206030402040632010f02100b0d0c0e1b03040203100908 76
    0x14100d448a80c00d65030403800209500c5400d10000102400030342c814000305425141c102d004124440000b000146086020307aa240c9482e08202d606591000400e01001016501070141c222034204c2241c5d214601800c0862446081030030300a0f0300700300350303000c81d07920440d900035018081108040f0006583d00e40e541d82118280b199202c61b0280034401c6290785000740d40c003881c15a4001c2e0956200e203540083c2c107000348102c42c0c10030880704d02044901c0c4514140410144020000760260344180d13441d5240594926103040504125109650b04c600b14071004901640e0549402c941c0c125103c9589445071300018028240940000c10000d8204103c40c0c0c3d0040c2030b2210f0040c0c00f014062280c091101d10006540c0c4042c4004801c001d0303040356500b1500c044181d880510740c1c0200400388901c20307a59840c1c05042c01c1d0b090b040345040c0304400381849086103445243d1001541d04080305d42c071314a0140c2c046a00d494264003002c0d585910350a003c2c1c200704503a826140c05844446076403920000b03200e402 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 42357441 1250 42356191 42356203
    0xb130608010c03050103050d0c0303110406090f0e01030503070f060605130506120d020a03030f020d02030c1c02040b07110111030310030201090806010510140d020703030207050d080615070f0b040302 87
    0x1005a542c070b007401d00c0c02001c2c024050b00d8100c03500f01000e0008440079070350555800702014011020035a855000910080c00c2e1000b80c8098016640c40e10300035414045010f900c1583c9811010785000d00300c0041001401c000112410745600100c4c110f0744084514020003c4c1a058120340d078006010720008000803ca68801885a03100b00c0f11700c106c1d2030341c2c0c2d280640c13108201c016075030042e040010b007403000c01d02a41100340c049000e48801860030a0709041042240c00549a41c400b001000a8541e610307030340d15009000100e2454411490a850b10200c040725204406006004402d842d03140e203c01da0141c2d4001081000c0501030701d50b2440d0004940c0010840d0b400102d0102e43e60a101003002040098a64140d4101401c1051941a0325206a80200b011400f90310101000c1060310b08504031030014029182c4240c1b80940c60b160707140b40407800e11204c2e0480d078003080b45000400007140d0f0785581d444118081040017550300c0040b07013040324401801c05c0002d80088000000d200c10180e0005078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 42358691 1250 42357441 42357449
    0x1303050903150708060406081209030304030f050705190f180920100206090a02012003040602010f11070c05130906020c15070513030b0711010515030c030c011b060b1306 74
    0xa00109940d103108201c200c1d1f0f1203000301030841e401100c4080c402003104004060740c410081c222030a01d82c0c0c990764804072a9403410121041e03042101c0070001401e0403200e030100009007612996100d030074108a0280c910140c46192107440850074200d131403010a80c80040320540000a07945c024100d1070040d2090411351b14181e020301340c10040100424804a0306078054424030011b40b2400540d900111440f14009801004bc0c00c06181031481800c0c0800040000700003540001c2980e80302542101c08950794841050000d601c10005a4009030f2034490010030f542e011038030000031100c265a4800100a0700d0002410350307100049152000100140c0050f0100503074a001189e0b641c1c1c040211040d020741c982e10888000406801d20000340f18a440e241d2101152402c42070101c0c24010140c2501c42c140c0d0500c400e02240200c007980740c281488081d1100d50b050f0020020074000b0305c0021301c14101c2d09440ea040998403141541003000c50f400c00c0000100042540d03290440301342c1c080d00140303107900c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 42359941 1250 42358691 42358697
    0x1008070605090303031b040510030e01050109051302120309030102070311062d061f0302070203010c0503010503280c0f0e010f0b04050409140f07050a09020309030313030509031507 79
    0x802a1280307003112403040000d0040c5095849140701d0012030041e45c1072080d0b42000601010031381da2a2903a01c0305a0521950780411402c0c1040071440c2110307010780140c124941480204569407565420940c4016815a500409041e0302120309041d802030040741caa040d40002013609c149a44001d01022450040c019160192110300002490714200c861401c1800380c90842c0521060001d400c0d103a00c41c00c05081140200c8840703071102d191108507a030300e03c0400c1e4003140d041c065050074440c10103840058141140740d54100b40003c0e9171815029600348410100c0814100d024040700000f280c8198004420002c480c0c0f64250714071118024000c1c0080d403094000002071908000182504560301c0e03034051481d1900301407e00028000c850741c00c2d01c50503001c81040942c00c004004280c0c9448183c8050080c15003003504000c135034a0254003e075101ca0051080c005ca042002c02100d400520036120780041c1c5400c0c0c54189c070103014120b1020ba0501803020048051100c0c1044244504210743d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 42361191 1250 42359941 42359953
    0x32306070f02010509060907051903080a080a0f0515120106030c150f050304031706031608010f06051905010f020f010e060f01150903150204080303090304090509031603081e1008 78
    0x3172a0b80c1c40e08211041c1903140d0100c2001c000e181441c0412003000d80c81c580381070542c0c68998940540c0c940c00081c1c040001000320b01002848081e5100c1c0b4484020450414011420601151140b580d01501114070916504150305c4480c242588070350011544201211115565100c03111603040e070110010b40850b81c0d01d400740b0301640c8544202d0344150b9043c3c50300700d940010030356100038980004040580602c50804103000010102c01d10324000d00c07001b000402c0c1c0103c440307044000c1d501e595019078003031291042001a514007403628031007564800c0ca4a01000044044101d00d030030301102d411a00b5518104c2046800f0340e01240c2d8600c1581113400440c0d40c4c1e6603982440380c1860059a03102e00065021106200140302c80d503044400007002980075050903201c1001c1070a40d80140c4244480c2d520000d4100220041401002d07031001e0000c0203107060070004100308030b100d2050701008040055000001760301841e40c0038407e40700700445400210500d49004c444089440034040c0e81a548a45 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 42362441 1250 42361191 42361201
    0x603071d040203151b0a050d0905100b0609010504050402030c04031a090111120f0a021b010204030c0e0103080301060503060d080412020a0e010612020903071205070612050709032306070f020105 85
    0x95510500170a05100744040030f2803c107613000d410340c01c1a02401c04002c1304208003c440c004034090808054086c602520345007000c105803400300c801c80340c4018040c201c00d01c4150410f03a00070080e101150070544016a69030b88400099505100c0c81c1c100521204016280d00a40d031b1210006c6032084902e880200900460f1101515041c0910050220384404103030000354242c090410480e045400020050b0070328250b008500158410315400e07040e01d82d030105003042403101041151006015100c2044a2075056407681030451005004440030b000c170000118005860720f00418184c10780000200362916180c0541101492009105038842d208501010510241e000d00b9a03040710610b07142d03880b01e503141203403013006500980d180c03607418064040005483d084003603800702020721a50142002908001c0003600b00f00703903166a00d001511b81030070403200603004400c86003560f411101da000f06100034071500d40e4000d82060020301c0c9010346400c0c0044550031200e075034190324858000340301507924 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 42363691 1250 42362441 42362473
    0xa15060f0506030402060a18081515060a0c0c050604030f0302010506040c02061810020d0c08010902070302030706050a021b0d020d0203030f06010813200f030c010e090603071d040203 80
    0x40e0301481c2ea01c0401040480c006290250052400170303004c4c03c245046480d00c5640e44105d5885900070503e0f40c00c80141446166400c0803120f9001c0d201888880101d60b48002107102e0340220b02c4443c05020607400607009000202040c1d074020440104002d6445841e407400307404014103204101c2c059803e00b400301d0b0b414500781c05102c103a0692540281040c0c2e80d40900c3c2860f01071030111a03481802200e158144058440c0020b164244802d1408204601700304c500402c0b5400584c042d0b90898814000040003903404011507544540100300400c40e920303022a240000d104401e1303454000510310300c1106090101140108204031070344c0039988820b40f101d0707050341c4034030048542c0c00c04000c00400151481d0b00030416183c005c07482d0500c83e8a468100c0c0d0341d8540500c1190034107060b5440668000000e440c000c0310011950205802500b0030180102c0081e100c42e2040c400c0bd4441c4d441140028a0342c0c4003040300c4401842c5800e00f0311038403038020a40100000c1d0903501603000b0302a00e4100d1075070b111 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 42364941 1250 42363691 42363719
    0x9090e030d14361009020a060c151d03120405010b0a030b06040f0b09101401051207030504030e03010f021201090e12070804050a080f060108160501110109050a1506 72
    0x840c0b044201c0c005804054040b1020000202003210711110212144410820050500e0000c8038000000d07440899004103c2440380f40d03800709040000b02c44c9480d00180c8020300cac21700e080525050120310b05154030507507900c406800222076900d100111f481c5407000f5400094500841c0588002c0000c1030488040c80a01034481c000a0700b111441401f00d1560305040d401812850400100010003528000c0011a015015a501d80c020382c0d0881c82400b04004c1013900c0580e214003400e00d1890310106010341c128400c8000e0104081c140d803000080d00703040c040c1d641c0d00c1c07402c80002c0080046503644013030305c80250021100c0415280a2100101e40c0fa402c0d44120307540c01d0280e0008000710012050849401e1780901002c450000c824800044c5a46690269601400940000d8800006210001442c240d0143d01902c01c90380030b455071103080e070105840103050380c03401c1c40c120703080300c420003512401b4101507400280640f18218500060061827101561f40b584040f00611109070f81d0411064204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 42366191 1250 42364941 42364951
    0x70302071a1003020f0f06070c030b130c060f02100c0f08100509010e0a0b0402070804031407260109080309060709091505040504140109080306180f01030206030709090e030d14 77
    0x725a01c2e805201600d0068580888804014038400160244401244d03241c3c01c00c4104490590500a042c001c0086610f080f41d40f0881000000b043c82d5040d840d2804a840b031840307a14240181a0b004641e01442800002c0b1500c40704070080c480b0413900c91004006402411400340001c51800c041050b20b8906043c41c0203c607c001d00500180e401c011501441140c044c0c15074221719a100d285600710b494074000703004250f010300310264541385103084c124500e061204102e805a00105024848a11104103450b54814605044034031070005a40d60741c0180b4a03028003a080755804030410074030b440c00251072403181d42503540782e00103269240e80320b00903110034943c6c45030302e03203002d000520039800d20b540704581c40340c001e0100204502c020041c0c1e508540401206a54001d8000302b00222030408420ba10221108002c2d45210f40c9490140c0000007901804000d115500001c0443c080501c03415045020380301da2041040f0000d9003180b166580d512031070406640301e0074203003104031000c0180e003620300c60 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 42367441 1250 42366191 42366211
    0x10f0b040803032206090f030e0103050915061306090c170702060f10030209040f020f0f0f120106030b010b0403020a06030506010f0c020402040f12020301060503030304120e04090b070302071a 84
    0x168903025151000b804c019890300703482e5102c88450002081d0140200821240100c2001c82d40c4443c5040c018400c40b071022000c0c0c1854106001d20002e514000380c00c4100030540c20046d40a078079068001440390303d0a00d42443d4403420719101044c3d0160780d0b4081c2d9950306603034a418013031018401c0c1010501e5021500c201c0540c101c0000101c015100d407100c02c0d071191006101000d01c6441e940010003803042a98250380700c9421258200071810900b801d03950f1500c0460704100342140c2400069425441d1010690083c80252071403850301c4001d41080024543c012480c030250368440001c181c55800c40d2209920a0111000000c1c9441c003c1c0b08681c040c00040c2d40703003e07060203d5642a1860071404070100d23000f513401c00c40000c0444082401030060100d03155401c041d02040d004144c01c3d0750158120900c00d4200f00148000941071007402d0076082e4090410900d0742c0c2c1c19000040042500983c043e03c1c001c2484108101070398075a008002c00c13842121700010b00d94824251000e070076800c540702807013 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 42368691 1250 42367441 42367447
    0x4030b15090f011403030403020d0b070201050a02040b040b0711060403030203030403080c070309030f021207170f010c0207061407170c06090c06030705070804051509120102030411040f0905010e06010f0b040803 92
    0x807a2065a008071300c0250040d08032407070541d4a0380440c1400a481e130301a54035203000014004103603030a000d903581014a8110075400e150030091158030522451089a5450710000303480e80c10411343c28541e51200390004c0181c1c0d259583ca080c081d44903070040300d0440002e401c07171001a2244144bc2c041da1847c540541d80c2d81c82e500e007581e948039a00e102041e400c4c1d03440340c1c80d80ca0b0b5840760300c030400501d030141009110040100c08454621441c1105c140351550b61070b41040e1007403903a144c0c000b03921821148185003400d0142001c0500001621404001501e4504401050301c0b580042138010801c1d0300d40740085800903074480c4109600c03120269682a8814420004203011910440160081a003d003003842e2034561384000055056501600366500c6440102c0d0345029450000000c140d0b250901c00258078518042c2e94a5100c440000a100e203d1603503040d102f03c0168065120f200d17125808002001148030b140030051340d95a0900c9141d1011800c148086002c516880582d07084031407000c02141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 42369941 1250 42368691 42368699
    0x1c0c0b10080601090209010507051e0f0303010e060d020d060609020405010e040c080420090f0406110f16170a0801090e0106031110030912111005061c0c0b04030b15090f01 75
    0x40179500c11982c160401406100c0440450341c140b00508580d03442000b1044031299103811142000180c4114128070b0300280b004004055a06407202d0f8448070403101d80c03503c6581440001c29030403034154050300303081c5807850100b242c07140d0b50700805c195442601d070450089011320400040d203405c0800400003c81c50408980054040c4c100b404a514039101d64003500c0880e10007064441c041160b8200c40792005c0010300c420b0103054440e1a450706220030f0541c2c1b070301c0551802c0703d103148119005004c2155040c100c050602071801001000c40d80c20380b81c001d03a036100b4a1030003042041c0a014141e040c40c5000742440034808140b15010849510040c01c1200160b2001084262607907200356030145522a5403940009a50139903100c4291782d2600c0701103001285d440e00c24509001640d40c40105440e02c3d05201403a0354444940624801e501242c01c0c00c80358038600040e2002c10ba6104041041e00402d0210402442c005d10622686004010001d043c05a40030807038109415a901c1d0110340320300d00140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 42371191 1250 42369941 42369959
    0x209060a030c110f070312080f130314030a0203070201060602031305010507020609040c02160503010c05030a2d0603110904080405060c030f0d1d0703030f030b031c0c0b10080601 78
    0x160140e18209101440c407038116040c14254083c010740c0071a00024406d10400c111324401804510043c0741c040c0304c41c9000c6182c0b104c07202c0054503203024158003064860415100340404c00e1440d603078240c40750b05d82c00c042d02c0300c8001e50005e507144009942404e0740411064800000d4070769401141078018070035494036005565a50000748140e81110007008541c03030907141c5004003140030301c56038001c3c103501c08501500c00401c0c800750003e912130b906003c2c0f0785001e903074024107480d0083c04010f0002110400c011011640051440c54107078a40351144c0002242d013611f03030045045070b0241c5d038520000344a1408004240030100d034014008101400140040d040c800e01405c01035807120304407490034105001003211070308100740c2290616201c03414039014640b0a8072000720007600e0401030801a04583d0081e2034a0314000d1800d08051352613242004680c1c040118a000200c241800000c0c076102240c010302c0c80d0700944094075001d201a001c9444003903d185036500722080480603108590820b4607071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 42372441 1250 42371191 42371201
    0x906030a0c0504020c01060803030405030403021c0302150a0b0405090601090f0203060a031b0902040905220209060f01030902180702010b0312120a0b09090d0905010203070201050d15080708150a0209060a03 90
    0x8105a40d607c000c00f064070341c0104021802140100010758989140d40304101110b88500b41142c10208042500c90009400256002402c1040680d00c0699616101418001e1a030070b03014550207070820050040034840821100c0c10707114481c4080c4604d04e801c0781540305910040e110307282c11a064910800c081680d4100780148021640e0044504a07622500c02080e81c001d504221091a600e4050140a0004d540300f03404480c2000c145168000c8180c001880f0030304024005401400364807581144c581c031030b9203d02c3d952540101a82e80040044520304440c0e03e0455000c0059071070b107561080d140c680044c1100c02d008104a003e483c110001a240c001400090035180e04140c0340d529004055a402c070059108120840082040c0407420b50014034a40712544581d0540d001088902e002d41d070304c81d0403103140f6480200040f5102c41c502038078441d0481158005405405854008603055002150444030412004103580c07881c2c45884d4480101d10800881c503034801c42c00c010250b1064002e07045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 42373691 1250 42372441 42372457
    0xd051b0103110a02010b0102010b09061003050604180303092607060f061505121006050d020313021002030a0305060307050904241107030201050a02070804211506050906030a0c050402 80
    0x3040b01014401e01118903008100c1001c0944d458003068010340d60309100380c1e840b0b040100c0d080750060038008082380c10300c498202e84c18109600d5100050180e1900e40000340110880d020002402d2a503040c014006c142c185030483d81c40300420f5141c892681c0e03844109611101000041c1d140c0030030b40c2d880d4001004040002c2c0515a00c5a000088803e05441026181441038403a50f54840942c580e105000400a000988410340c4031400c0c0622940f1034146c40200ca10007100695030b803180104451900100340c0000e5118108441c0300300b031150b000c005030408800e2034800b404561214010540c6a0204e030007407981000c4900009408500c00744801a40c001c0190484000036490508030400d803000c0c200c50915100000940f40c08165091203120381c010802e4500f10b0402d0740c140e40f0404144a54480c5003402101c806110b125401e89209118849510032070002130420010001805130080c0d1203224810102e190000d0750504001c80c2d80d11a1507400500104d4007030038401040025040048 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 42374941 1250 42373691 42373697
    0x6090108070e090f061003060b030c0c0718060e01080703051903031806021e040b070f020102070e09010f06090e0a030305090a020a080105060301110a0c030804020607080304060f0b0d051b01 83
    0xa102c10551681c1c0d0301d180c02440b010000b00000d00e0650180b002c01c0701c49500401c200f5107015001c01a624004027665000107c0801c4241d4548000201600c0c015060304418456081c3d40010380440019903c400c08890310185251003c1ea6240c40b50398817402540300280c0b864100d07281d2020728600c0303100c0c017401c3d2920a050014010f200171046041c600c402c404101c03901036000507900302901c012035085580a0089241d5407810b400c3c0481040d050041e10801030103410341d09407603011a030081c07007180d002c1c000340c03001c00f10685807424080d8060054950320500032841c018002c100e00056004404a401562000708400d094a903411002018020031000b914022009140016035038050303220010000103001240a0170100d04041c2104c21074400010b683c18200f103609002900400000c2482c0d42504190401c0d903528008030f01a88110035000b020f541d00042084104a61503100012501409508201e074104103030a1019020b898000035100e80d01c6000d00342e512601c4c69041c103a070480189 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 42376191 1250 42374941 42374957
    0xa0b0105061c1a010206010909080d0c0509060304151109010e0d0201021009060f061203080708070c02060a020d0207050a05030a1104020c030c0d17010605030105010c05010e060709030201030e010504020609010807 93
    0x8416541119030480d001110003d00c0c42c0342080f5580d04100c030714091301c54000c00300310040c650340d02d226480c400c51210821841d00e43e02c002d11500d0080302078918040019004a40d203140500e003480c103142c3e401e80d10715156850090350170190101401a01e000c02d806842e8200d0403102801084003000380950200c4c11842181d0101e014889640581d02c901e41c0714610200300702c05e81c00d5400040d2101e41d00264011403417200f407000880d90101c5a1a08901c030f0b400c0681c101d40391020211249a00100f010350840c0c0c0000316207550301d600085003a8075059640c2540c44541d2500c0402520140304e110b641c6e1305610000d04000461200040722000810040c401842c10701e0080246003185c12a504c03d1449811860901c41d1890b00881d01104071a00d8541d203041c1903060030340141c49804103001c3c4a042044a0101c80c1c2000802d511042d68280c40800721101864a04001040046140412400281080003a640042050040d24080c540c02080b043c1080c90031401150800402400d43e42044070300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 42377441 1250 42376191 42376237
    0xf0103020118081b130921180b0406110c030c220603120207090b090a0905030702040603060501080f1207031b0c09020a080609130212101107140a0b010506 68
    0x4210001c4100c801a03280c1c03542100420420036910985c0303024942d124100801040003c1388254617092180014801a81c03e001a19040354060a0219403a1120342c8c002004103e10004001810803504113588101000280e400e60719107074414090919019440a14543e1840c5040001c000340400ca4191620f0800305500550040d101590f10a940c03810b000008001d4480d41031000001828409030148107002c0d0007408102800001441d0403207903590b402d0b20004202041c0121103001d43c004109006a03601c2713082ca080108800e00c00d0000030710880004a0b40301001045103021004a100741030308000042d20309944000d0300c0906540002c100a0604000880204010015040c400c80050303d0f002101c0703020b8001207000e451548900229000c0052103c5d5000207003540c0b55050310804034501c04490b40519207010604c8402a0351705180f03003651900c0000c1c019020407070180740030910400c01ca01c501da443e903c3d083d80140c00c4040c0000103200c0c1c2c0c00c4c050002c3c44040d076049881e406145070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 42378691 1250 42377441 42377443
    0xa020f09181204050f030a08030c0f040506030405060610110703110402040f0605030109050a021815190201051b0708030109020a0e09010306021206030304051e03030403020d05060405010e060f010302011808 90
    0x750040c84003242c0800304080c02181805920f00000c002d003034000b80f00494054840ca16180801415403c006074002030220440c005003040e90000c103006030460751a03007040d240442c0c403000e040794124080c82c4070400c000c0d05507114031483c0f01c80c6000400a44022800c54690948188050144542043d000c2100143c4403498880c007500429059031260307100e5040032814010b40d000170704201006070040c040080d042e2210101c40d083c0d800f04856030780703024410100390f0a890194201c207000d0005900318800c4001d0701074120f18031689002504001c090a0120032040c10b005040c0b0107489640244010701c10546294014240030300d0a08054980c981c00c0000580c4825098100715a0b15070085503110300409400c1040c1d0300050704138081d40c02c243c200004154045031544c0740e09031a401a0401d80c14940341402150041c6801402405040030241131030356603024241e904840c19860131803a503a40d90404034405015000500c01d411143c0d10719001190050f40300301400741d00c803244e01c400241e8540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 42379941 1250 42378691 42378703
    0x2150304080d05010801020a2106091a030c031204030f110603071d0a050f0409020406030210020127030c120201150806060f0909060103020405100f0b0d0e0a020f0918 73
    0x1c800d0196a40d1280516103510944006a015120aa0040c0420415640c1043c05a80a807000b00e1840400c031041042030006082c0d903a00081203649000c42c40111000700d0800d04001500680850b000c00b220001415914030001c0b220742c000207020f01040c000206c5ea0a141340346e0b64020020080c0414000000034901e52013590304001250b0455880308005103240341135001d4840c2180d20045032484d00300815038502d02030b00d13201c3c8555600c025083c115526580b00f01c001d1500a4404c0d1410081184040c1c002d2840c0d048419640c0a0311298004809001814007078465040e5903010141c1c3c0c4c56a40c90380c4048400300c0303003002c0d5500c0d001d02d0341d000103491307005100400c400c400401c103900700301c4188107400710441010382c00342c20318200700824141c1c0000d034141120f90684000402c2c3c3d41e02a51407690710095040f11216000110700000d0701400400500045a5039000c20407900ea01c07000c8166503001d00080080d00b00401c1c0075190400e240042909900c40a8002019080b105800342d884c1410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 42381191 1250 42379941 42379943
    0x15020a050d020703120806130b040603060911013c14030703140105190b03090c0603010618090203060108060112180f060c0f0203040308130e040f0210030c0e090402150304 75
    0x43d00008040042c0a00035100e180d841d1007500704036605040020124000c400c8a0700d03001e061a4030341d2440740254460742c2c8810000d60300100104918140f9103080c0f07125041080385a40041c48480080400380084064803a0003180202001620140c140d141c41d0841d60740c00101083c40350061039038403040100c10003144646240e960008032000c01c007846204030384040e008540141004c40d0301d104212140c009003019512032034406500d9a03900c0040c4c80c50085030390f40701504140c0100000420325001111110240c400845880a440c0c5800302c80c0100c0c00101d8081d8000359210000c500a540100180c40066802400c0480c000041076070900c443d80320300700200c0b99000302011090501c80035105410030281d1a00e0000182505414000e40d04c1c01540409071844030b0001e400100b9491643c800401080040708011462625091030f00c034507071161070141d020714141d40c20005103030f01c0307846041088000c54440a24594912f020710203400801402242c1043d2600f50b0300504e1114000958811 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 42382441 1250 42381191 42381193
    0x4030b0a02030a0608120405091003050d1110201b012904020712050a030204030501060e0103110108010b0d18080d09020a08060f07050d0b0909011a180115020a050d02 73
    0x3904044001404440d202e50101c180c981061b8112400003007010211011a4801ca03908101c94581d92004170003a1410303400104280315515101181c2ca1b006404a1080f1400304140c41e0015146080030065400c3c1c03e8148916034000d4140362070900010000d010301c6010680d285070b81d00a00c40541e401c403245441c90070b20004500d04a03002041d0030903021100d0070001e075429030901e1510b68451718019040109082803100210320010f04a101c5d6041e00d004540200081c4005036880515001c80f080c00e02003503030f03010942081c425031540078403299812620941601490520048000002040388800315084100041440f10201d41c00c2405001009441440000c603160b16204010a1680310760010005801200801202042c11180c00b5404611410040d940e62042d0a07100028520015951b52011100d41480482c0a055000040c558038100d0000006e614980403c089040d61540800880700b0420043c80104030b981103d51200c2d0041c011200144101d50764103003003c13003c102d41001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 42383691 1250 42382441 42382447
    0x50a020f0a050c030c0d020f040b1309060c0807051e0c120403060b1c03050403030c02010e03010507080a06060905090103060f06030807030e03011514010c02010e030706020115050a06020a06050402040204030b0a02 93
    0xd49000c5c000000c10b16400ca0b000b0303848031104c0e4041069080e000c04928441d0381d55224489041e107481c40c1e0b60041e2480740808100d4094249000c000401d6502c00440015860070700082200d4041c00441d0003003840e50800071900c036109a8241825802480c100110b4003564644c11901c50018002e40081d610806000c030312009a0000c1c08880d01003d02d210100d082c0200090000c280c000c0100ea0581e074142c9420f201c1d8400500040e1005000c0500140d0190700e40700420002e03070350040724917000c0c1c1000c120a00c1920b0b40e03010111040840e6000d5158482894001040010301d95400203400790810500462082e54a84451110350011f42081c0c01180003a0100d0a0b24a42031027007803620102192a50340079030820000c90200d080c01820141400040000c410540e80244919101e1100040480c0c0359152500c0300240078000a0b0031000044400b864089818071303008401105603901c0b54010302c0c11007400c1c1c4541c2c002e032001a0041c1d81290382088040040b0301f8100800d4031035400030b1b01c0565 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 42384941 1250 42383691 42383713
    0x40f0206160c0510090612020331060f0b010212071401050705040906080d0906030213090608030a02060112030c020625030f12060e1602070801090b04030206090304030b07050a020f0a05 81
    0x1c0075000c03049440742001720100d014813801ea005003028106000b418401600c07583c8a00c1c4c1ea02c02e201c03805804d010b514030000b582c3e4807140d4102c004170351030754441d480c10300007000f0000911042da604001c0e100d0141c0c21060801d0741195180010748000c40c0280705030055954070800b01400c544094800d02c0c00120000b41c24040c00311280280401012a40d0041580c032510904c002c04003d05400b40000b05500082c0a200b90940011181c025083c840c00400505a488225560fa41c4c0000800d40144c00307030703000000e0340404400d131548400e03400d51074110b40074906d6402c21000d80e00608400700d00c0c66607856010814800b80b031748a40650700c80e4032559200c6900c01d03005001042900403541e0a507041c08814000e40c038210416503080581c03100090032420555009a00300196500060000d44c038064106c401d016403e16200d0141d030081d029180c60b5120600b60035128030460001800f4401a00c0201d49587c1c0700d00d008024410091066a8060740c00c0e4181900f01f05c1c21071410380d2036a1060101d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 42386191 1250 42384941 42384949
    0x110a02160602070f2309010e0601031404020604150203160503030a111801030e0102070215030610050a051903060510110d030c090e0405010207080309030301060e18040f0206160c05 79
    0x290075280014403e01e45041408992010745002d540035000c411345400085070080440ea0607140300040504d80a9a100d000742013000d00211003440c0041e00f0824120496418403121a00980d0040e110505e05810581c03507105840c440c9019030114030041245455600c000f0440c1c3c24618880d801039070740c038142a4140001c0e910024001c201351074082120040c48207100c60b04500f51102130902198803010381c69210f0090103082c2020750440c4021b480d915540c0f600c0300085204500032200b0782000310130034000301c500e070103580034010110340e0030070480800350220b940200f0042664a40403c00039101c07400702e4400c0c0040f54011001c9014010400f08426044c064007138002e810b80350401030100a600010706103d0144200e8084030800c90210301802000e4048402054012502c1a034078282008015034a034402d104190000758102944802d610b00313185c446c0060000c0d035100840c151541c0c0c41d100045500c8080c101d0307015008200c1107110302d0040000541032405507a00003400f83c945411700c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 42387441 1250 42386191 42386233
    0x6070503010e04170415230307090303030e101806050a0c051b150c07030807080103020a0506030901060306050901090209011d070f09050d0b0601181406070204110a02 73
    0x50052210500040c4007640107000d5407a446900204031400640100030102a10300c100e4200300f07444140c402c402c8540942003c07203403c180c0c110003100c2580414040e00f180d07040c00152030030b500286608004101080c801c1d088420048044400e035011000d01ca4580000c0354140d03404442c641020006520a014030342c420580e00296402080c406140101e00051491054262020390340b0715014128007216000c1040c8400141c0740c5000e08031a00301213105800039082a642200050001c6002071840e5108481c80c5040b01d9015056600107814942045281d070002085204036650390400000465554000c0d240106107110000030810b850340140804100145c104000d85807210003441c408480c0002c1c150f602100c20701e001d0014580c0b0303105c1110707880b03d80d0340308940c840c0c11a0b02c0101440640314071580146026224411001401360301c892042c00380f8840d850404030105e0004995050007030003000124070090000a10820307072548261584c004450303000c0168040c000d000340748044490341d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 42388691 1250 42387441 42387451
    0x70b040204150f060c0809030601080705031006061b240b130506030307033204060801090c020c0f0f120f060105030a111c050109110109050a0e360106050306 69
    0x5102d03090034050264109640b00e00e40420200020780c8003441a072005680c42c0700310080503a01c0e00d50b500c080050303603071704940241c03486801120507200d0034518911030790381281d26580300d002c41d03501481c0d003d40090f0144403085d02d1a14006000d407000000140b1415a400720080c40010024411020700480d5001603440c106a076151905010702035a001003900c0c4030941c107242c2070800c51154402c6198034056050b0300f103021348868464a107080260b0001c2c006540d2503030764184490303a03070b40301d901c007981e0f030044180015801141031442c04d8103202078232136140c900252070303001800b241d80c0104000b02c0c224003c010b0a50071410b04c03414550020310000c3d0044ca803c4000b0207040c07007a62901c8148045902820344101c124400e110b512440400c0b118182d150000020840b551249c01c000c003400c90403000c2140081e400c0c10020807240380031980c050580c1d00c1b000c0003a0060b515102d28511541181c0f81202d140c0c40303c1600c124001049140303c900042a580001c60310034580400e0519040d07001e02 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 42389941 1250 42388691 42388721
    0x30f011502030405060f0c010b0312071110050d09140a0302011b02070501080a0203070903081b07150507060b030106210611030402060304080d090206130e01050603040c170c0402070b040204 83
    0x10041100d540d9190664501c8522040f030030b81e41f04807518009004000d40000b81c0d030940654080304043e5040480038141d041d00510031100c088404004010b003c000c040002c4c00460014424481401001c1d031040100a100350001c904500c2c070703c0242840e001c00c2d58000c800603034481440300403908a881114844101c640000c0810a040100207010000010705400046a01100080d10103100c0c140150055421588550741c4081341e50300210700c060900c000f00c0051045040015111096042240c0500200d5489038140010795946e6806041c2000c0a1945076489000c007184442590120766407402000c90111300c6400103103854426900103c1507000c2240090040201580703031003044942c800d0744080c0c0c079942c490a80c442e0a0040400403006500008081000e02d1680e0f603154840082d1989080c0d08421607980f42c0402031948005c940007001251080d40402a007800301c0424500070239180c2c251100180d00c0d5001c50101d82007054165100100042444150300345481490320b000403081d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 42391191 1250 42389941 42389947
    0xc110f030f07092417010f09081b0a05060a09030e03060f070f050712050f130f0807090b031011120717070c050a0305090f0901080604110a0f0501050d0e0102030f01150203 75
    0x350030443c64130521400486011100354400300200c20346c041c8004142080040000d01e02038140010a60441784084121251240900b00c40c0e90340001c6100140d544540148056034070800000301070411240100d051080182804505640c01e1003d10b22038140d910010000307141c9000300914441d5075161140602c074080001c400483c0740c2c2d07181d07007600d8415401d0460761001408851001071140000c6101840c01e032006c0030070120640b501c0f240c101e0301c502c4100d03944981c13914041c2c0b04550f4a2842c0303540c90381c81480c01c5410006c10350003002a1281c001c41780b50400f8070488010200020456030000020908808a0b5000040700c20894100703800d49001e01280b0302c1c660300e05950b51014400a400c3c00380118245015641d502e14008440784064131816103540d4418040d07640c1c00c015101181e44c20b8054240700e440f0b0414003400d0088500418004904600c3c080045d50142e01054081d580360740c41d5020381000180900085010362048070800034650326103540c005621030a02224400c42d0810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 42392441 1250 42391191 42391241
    0x6050a06090306090309080d18082a1f0e030601150c0b060301020c0304090b0306330d06090f030806091504050c0c150411090103030c110f030f0709 65
    0x1c400303001e030307503100200203030002082c00d040e40c0c200c40c04d60140420703104002c20748070680c4d03218407400310182c0b0301800c0b6082d054803088103a8484003248841070703001401c0310018400b050720b058203581c00100545241a000d141c41d01140d040104220903c2c04113201040b040b5103400c00b00701715030040c840c900c51100c207101e0303443d030040c44088603030400340c00729002101007001907500394119442c1d203403a8400c40f91342c5c507a5100d03040050001c140e0b900388a409007078002290707980500502c5100c0c0401a82c02d18614006c0110712108a46086c040754201010158003800504d4901c0f80010150103145c4050006003a4a4000c0090000070940c0c0d0041542109200c1408012070150110b9002203c020880b030747c1e01d0200690500414426104901c68a803200c224240c2c071201e41380c09540140a0070031941214428881600000e10000300040c007a42e00c0c401c04034152004010800304000e285100070100240003030f241c850b500c54a40d8030340d04110b00030041010b06104103401d8201840030540c00c0108 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 42393691 1250 42392441 42392447
    0x30506161b050c030304080d0909020307020a0f050c060304060209040c0e031b18011710020a0203030f070309020d0503040501020c01032007030207082d03090312090a0801060e070306050a06 83
    0x31900d0050281020340c100745081100901003416600383c0a800c50fa2541ea4521038190394032a0829018003162052078041039a024900030bc900c0740d4480e800604040c1071a0380c911107800c07202d44003955580908080801c4503a5040000d41c01180114400b580326880d01081204030740200092070b00340300c1e141243d404151004030709180000600000b40b14840e0200c00861302703201d0016049030318071015400200c0c00c3c00f0f4509400d080000c24100f101e602c00c4005207524124403901034040701582c03080c030005001040e064412079010106d8a00414100340541c00710310500800b0008544036040424148141d5904011454541c10300b403030705020744c0b0000440a010700e0040c0d80325121041d00040c41000341402000074ad40185584400ca40c0c203080007072a0440c8010010f07001c0c030104844042005c01001c400415150701c010014060040f041000d1004000d0b0350001c0c403280e8109800c8440000d59a801f803103a00300502c009107204042e4544044010103e42d03060308154481d1040c02c00c00d01c1308940c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 42394941 1250 42393691 42393707
    0x80a03080a020a0e1201060806060a120602090a0305010e0105010e062211091309020306070f08060d17040603061703040f03060c02031b0a0506090601060203070609080d0c0903050616 80
    0x7503400c4006a450704800011103016201c0c108040c1c00949506203041c02600551100c4110b0341001c082d2515601c4610070400b1013620b500c40c1280c01108900d540c0082070140d401000320010003002d501c00340751b5995031603003500c20b44603a201c01070755108010002003030a516031039442082111b0300c42c20602209003c000c0484140340200c00d10f940d5544d00744041e0b200c3c0d0201c030501080204001140003140708031901a04a42c4422030081c05044082400340e4020509100d5aa80c070f615031405949d0340b801807000040c800a400d41e214808074290320740038580100244041c00c4240d0740031400c0d908055103803441a290410303526036036204020030040d807a15084007205499010710702003a45402d5482c221b10714001c1c500c4018000078916890780e111300001580078a0f0380d104d103064a00550741c110103d40c8031003003442140050381007001400300180050740301c1105207100e1082541461510107030700040b00c81d258404008501e540000f841403200801002d0791096840450350030702801700078001d001c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 42396191 1250 42394941 42394951
    0x2030c12090a030b0903040312030504080304020f150d0b01140c0316060207021c12170106110106030503041710090c0603050c0c0604081b0606180711030d0c0306080a0308 75
    0x91010035854110741d5441110002180c0180004d8020f003000d007000f503200e903c544001c40d554811080d50801c0d0364002e001e03052040b40c010b0807081c2140e683d502405084d0065a848070343c040c1581c1e480440d5458a00080c1c0b05c558451000001d091002d840054000158518203e415410601030005443d800008881c0c1e110183c902c3d4603101401c41c6000130180c0500740009520003000c1410002c8501c69141d04035106003d121280b504541e00c030000e0702c45401c40d603000c0d01e085061000600c04540a09030802c54210340c0130000918903034036228141160441e400c150308407040014040c600801c10000b40101c68440c900401076160542d442907012222440360380103058640001a900580a200381d8400b003807032406171205480c0034075050685511066040080901c80c07400c60159400000d8a0b030b01c1000c003d00b41e01d4180000c284002c0106900800300340c10000401d140b103004120074800742c030044150b0840480d0082500b04090700343d8001c3d03001600c40350300251014002c21b50107083c845d005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 42397441 1250 42396191 42396223
    0x5030c03160b0a090b0d02090a05010e130203060303071a0106020601080f070e10080a050d08090102090312090a080d0f0201060611060a090c050a0b0c060f09030a030f270b010602030c 80
    0x40d28200b07000b504d8038000396004003458a000f00b105400d1282e150010225060300310f41d54001282c581006480910025030701503000a2002e1010300190001e6006541000c2c00900b240c0c2401e4103a80d9800705000f4a0108508014200004000b003940401155000d401c4c0b08010f807080c071003039402e401d0361588c1c0761003031011044410f0301007401c09000340304d205c02611400303040d9040708149060156a81105500f2000010344501c0010102c43c018400d8030480480200582104501014640d1325038002d10b100503402015070400007960a020880c0d00300c46800c90b00c64420b84503030014043d08540c85035200e1024400005c61641604138041103c5070302c003a80140001d011100c5007010482c0400715080183c000c1c1c244d03140483c68215002c00b5040c1e12000004648851b56a8080c07002c164030309540a40141d4801d11020b1085030090b082405100c00041c400516440400001d14a000141c4a0280000000701c00074051107103401a050262106000451038490b00d03000356035440701500914159 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 42398691 1250 42397441 42397447
    0x30a0308070e040c1107060e0d020103021804020a020f010e07030f080a09031218051002030f0c0a0b07030504050105070807020c011103041701020432060307050c01051005030c03160b 80
    0x201d075000380700390100304501038030400c01c207a100d2a0142820b500420121010b1282010005036144105113555034440d01420042000100b9801035000e508508a5034618142401386a039441d1940d102a00e11a60194000e001603400c0004a41c210b0380721203c04505c640203540306201103040c0b99248040d059214401c1903507513181507021105040a6003004101d0408400b8203215203034000000748100c004c103d4807002b065601e0003006030400c58030b003110015800030b029070013415141c40042d000741c0100805444008600f6543c68a030a10b0403980da4000c2540d4006100c203001b024418264041403130b0030185124240351502a42d070702c80102880e4100030020b2414943c8070400d00960300205500b011024500c14050a550701035001800b40e20707050f0780781c01c1346c4000c50b001c0c4240c0030154800b000355850450340d551085c052154002091141402000c10640502640c02d10401e4407420b07581d0940c505960510040509151074400420700ca6030108070801d00e024808040d03202103800300c0d001565 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 42399941 1250 42398691 42398701
    0xd020607140109050601060e041e020c030c12120606031e070c0b04080703020d0206010e0406020f0f0a030608060709060516030c0b1e07080c0d0e210c0105010503010b030a0308 77
    0x11584028001105142d400c200810b41003040004c0d40b241620910388841407042800780c180002c5030030001c0791603002020000803a145200550040c0b00066442d4240c0e441c024000038018640f201c3c140941020b034400050151403007541040e031035080360044504a01d5810520b403031a0907040682d114030425800b0b0f50100e20014000c2554480c40759015003d00ca2500d090b083c00406900040402c0c0d02500a10704241c0c0300b03c0c40802c05506903105060045542d481e192200d10080d00b00b903500a0010a0812072400160188001b8140c2040d05980209004d402d04403424240040074110070705000f44540c00340900c03900607040d5500b81d000200c41045540560138221004070507010054000000c0500748404a604c08040f04084845041c88042c0d0b5164000100c401000886107042c2e04201032252840c135296070f03003068118803c104101c0303c190f0b081c40c0d41140b50180503551848199000903040a640c9400c0c040c0320f00511007103008020107120f0202094540052045c01400c0101c0000021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 42401191 1250 42399941 42399953
    0x30b040608070305030913050103020d150f02040e09070e060a0504091a040812011e03030f020c0909150105100804020d030302120c1803120d021309110306011d0d020607 74
    0x800148140421107501c0c1d80c2c0d901340980c89511000f500c50182c07948040c0e009107800140240f50403240d02400012402925450700003511340c100440340a8039454032480e5010384064005400503011021044000d41040c1540502e44599035210b10803031440c4104008480d40e644e054101120000da60204500741c1615109142c0540040321482e00d09001051009201e1444041d100034040341c0700d00516030740c030303100c2c0c0c4901c03800b1085410001d1440d0301e80c1440000c0c0709200703001007038003103004a5404002c14000030b2a60035080312040c42c5a40a5400c10b041e0380a8206964010304c002d4419407840207401900406118000b800a40261742c6119030904040c4242e044402101c0300b03e8821203d401c003c204104141e00201e00c1c9200c0489940071208103140c003040900180c0040307420249441c898540d4034000c0c2d000b114081115184d101c0d00042c41d03000714021320380291000080385540385440300015008000c10303882040b1442000158040503111041180f41c0d85804031011a08c400700d13407901d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 42402441 1250 42401191 42401201
    0x1002030d02030115230406050d02090a080c0301060e09100b030a0b0403080105040506030d0804120903050f0601030308071e03050411120106090f0b0f0d0c15050d0614010206040201030b04 82
    0x405240788008000103207202d8404d008008185a0f59605001c54101e1212100c52030b580000d480101c032042100b00300a80c040d07801455001c4164501504104442001800c1035020b907100d00015040041c54040700c0c03800388100c00141c4004a03020701682080c2307540a44e01c20071a0f4030180000e80d10303040c070444c81d602006052141580181d611146103080d24005210180a100c1d00d801941001c0100d083c600d0045000c1140a24650f20f904055903662907001e5040d003200c40000c113021840c04040007042045c8540010404030300c000704101c1d40755180040c48e0040041903001001004000303030340003984126039a01e1a084618020580740c6650900d1030000d040072901c56808458110b82200102d01034000500701d41110104201c030b400c1440c0964280d95032041501e906c1908a50131400c0d900e070110303000920a02404a101d407054031660f40b601d8064903d101c1d40d010a02c081041c9030201014055100030f400001100309441c800d140020f541c45002600080c10703d91140f8504140792169444 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 42403691 1250 42402441 42402457
    0x507080d05130e1807060c02010f170609060a0f0e040c050a120602070812070c03020c0604050a050409050c060a02071a0717160c060f272102030d0e01020c040e0c100203 74
    0x145c0ba074559a402d00580f500003c1c207012030201e8141c00c0303411125401071210264034004580b002040b42e841c03208000c0d41c8600200a6a44030390055000303c6c1d10038040c840c100107440f24041c0d00030326041c107003400649000c0c50303031007588110001d2405002d0081e040085180342a809840581c5496191802c00b0141c0540c8050300f8400500004204501e640304403100541e074000d400795086542040c0900650713101c1d5014007904a90055010425414654803940015000c0c0007a0746820000000040c0c003503000b200d409005030300004061000092030380121100303403c00581e6514000a03665155015921101101c081d60340105040034000d1840f044c0d0548a030740030940745001c9498803c044d01c91420215448001400d08150512030082e008580c0324407030302410b05400851405203900b103003940700682d40050b521ba5521020042e18100400c0c1000b0b0400e44810040c0240f45000a160291500f846407080d420001d03560074944012684e0001d40d84159070160040d0740a04007030b4074500c1940700e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 42404941 1250 42403691 42403693
    0xd140304050d0b06120c0a1a040b040311120a020d1e050a0302070914061c022d04050a021315110a0516060512010b03070909090507080d05130e18 64
    0x20982e02081003110b2440c0c402c0904036a5000ca000e2040b4103690383d03a0030385401d99045201c111041c03240e184141c40190042c141c42503021700c2c254403920003000359001580216a004a413a4601039a483c0c0b40c4801c1c100007545000600400b0358a4002800c14000c124000d8140d00030001d0074420743e0f046200485040d60800100c801c019464074001350f95046504c035000e0201e05c2c028410440843d010401c50140c00010001e0700420700d080c445c1000e540c51120105d80c800e11415141e42c0110344910745014540c0400e15500c1540414824441a1750008010b5035803940304000c41440f090100e0b040f00d00b0348201802e128400445600160f403400b4031401c40713558a100c0d0300850802c01c8000908800d54a6010840d88143d903078641e4160f400380241c441c141c03065641380005100c1c122103c4041c3d07611030101c0c5451208160b80340c83c1102119a07421042c0c405810010742440344580402081030364180501d80a4540400345060141c2c0064034061412020b80070030205182c0441c00f4488110711103030034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 42406191 1250 42404941 42404959
    0x10e1003020d200409050309090a06150309020411070201051902030d020c0102030a0b09070f0e2e0207050a0f03030c11030d0903050d08012417010605070303050907050d14030405 78
    0x8141501403ca00c012200c05800c0d004030030451a0405008030190305902400071418907102000b0401d542c0e0300201007000041c1d4a42c4001403ea9600da4a13001c090f8481d10b00040b2450703680184419a1607003000c08403c042c0c01c119501c0180d074041c080768421400d0040083d0035650008049046202d400c8c0d845100c1d030f0011031407aa64000640c000d501442c0d00c0b18040120020340d40900168080417a02d00d00851010300c100c0300311394090001c0000d00c3c00b000701007252111a210050354900c2e100c04401c3c0c1107810b251241480181c0402001002d064103c49100c60355103442c80380b8501c1422030000030304201c0c03405031400c10852060035425810600500391498141e007804001c100000522003901c051254541803540c5501841c0c000c0d069400440114000c040d00d48500852010110550750802010705800d40346240c01c005c046000e8105965659a90500c504004044d150080d0040c021500824010007040e60f07200e440891040c1d20921044d1020310724034040d4154009d079848180c01130703074030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 42407441 1250 42406191 42406193
    0xf050a06051306030302030306010c170406050d050a09020609040b040914010504120f02071203021606050c0d050c071a0f030c0306010f03050906150607150911060f03010e1003020d 79
    0x2540041003030390010703121052901019211207090380c0c40740c880130740540c004201141c813a51084042c00b0b412030041c00058107458100381e8011040e4020f60200303000803404108070200e07440364051540c11441346c41051090151039000a0308500c100c200c4288159914000400b9a0f01c50340c201c2000304c0e420083c080c00826120707060b9400380c54202c81c1125a8010078054018440c001c422500c0400e031658014160036003850351075004080c030a242a82940f050500c9080065064024580549055541c081d1035801340506645070030500c0c503950040c007100717011244a0110000e85102115550808000400e003001c064000380e100345040740305968400800c00c43c5c0b51451200850241d0030a98810000310b016600440c00c591044d1068060b603003240000c0b51a0740040c505c0c0650198004003ca450311034550354400d410301c0440403114000c1d44416080050145202c01c0980303600d0199000c62400061b01d040c013802d48814003c040c00c6501d0b140201d040342d80140f00c1ca001440d07010303022103421005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 42408691 1250 42407441 42407461
    0x80610060e0108010b0d05061507060606020105060a061d0111030c0a021c050c0108071206060206060a060302040623040315021309060b0a050d0b04060b0c07090b060403060b01030f05 80
    0x698062000403400c24188001e0700e510030789842d412207102e8101c8905152a450110f405010054002c0e540508179407044103841c460740000780449841130a000510303500e40f8a002c0d0039900002c1c65103103d00c4100d8000c0020a80201d504c2428018060215804417015030050f030728104500c0c1c0c107040703911011034901090000040c0035507440b4021039100c40141841482812000c0000400511a40082090400075401910301c0c64000825003400c19102e5014410401114a10ba229a0044e030051046c4a86820210a0030000d0003441c0f40a5103418103150000d460850a0141e401c1c620700c0d034264030440c4840c8802602c02450f07010810445100002c060390010303401801042c1d540089030080001c071480c0c980b051307a045600480310a81407030300da40c0f401d8490b0303044680a8198a61150007401440e581c41c0305440c080c1124441c52a11494a0240646080c3c0d03190841030065103011242d1000b0341c0c03400181d03012680c2c064800308a144065004074061f06a204005e0318130740c00e1406101b0380a41e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 42409941 1250 42408691 42408721
    0x31303030b0303040f0303030b030109080c012304050c01180806010306020a0e0a14060904060b0a0302030403080c030402030705100c060c0801062303060f030a050304080312010602060f0109150806 86
    0x4040d640500180711654100340d200c0c8154070035400403000d404410000030b4081e80041c07c0701d4000070000101298503840d040351a60252442c0080360355a4858022040c0064201400300c003059141d813800d40c941a5200f41da0b541da0394004a042c45042c800ea5814013840c0380c400760140c5030700c0003984c459580d00e2900501071741105080d1701c0400c0c020015500582059854007084680100c00424a10388500510044e91b005885807a00107450701404545034040000030403100702c440e07400594a1410742801004100e000d003034080b18010400c144030142e0b0740020480300350307202188c4c01480f41b91418002e40b0502c4019400414503030405100d1604617802c840c60038101e07017a6440320b1000001e0394400030300b8402050b840c4d0300142c1d0144049079090a048100780610100075044640030401600e8052554019a0020300260700c00902c4514003209024010b0041090b4001031120f800d000714460503581c41400b860122550303d100c2c00d18a82c19074920903008003861416100241001508a041a9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 42411191 1250 42409941 42409943
    0xd02090405060303030415180807050604020109060518100e030a0506150102010905150601030e15011409010e070c110411032502030403110102071a09100801050d0204051003080313 79
    0x90701c1c04000030024100401160701c00c43e071254504100c98003c07000e0000a05200034040408690607411000180070320008024090081c0010700c0c152826100040000310507411010400c401403102c040d0342d04e840300d4016481c40c0100e484401d11164640d0071503500e442941401c0d0f051041a00c45414848007203076241c010181c031440e0112034605103005900b681c5a002004010f1b500000504001d0190b0700025500704005142c00b1500e2510780441c24600700103000070103440700005004001041c0098825120007000f0740300c050041d0b15200700041d600f0001410380c070510410900c050200700d005c50400240500003441005402c1c45105d0b11040c41e001102c442e4554098455100000314822400344071819895004600d42411070b42c1707001158140701001030540c414010013045941d50520f11248041034003482c40d80303e40b0341030300700b082c1071030106442014403960b08010710858403503c000000b1f55405940c08105034803145441c00c4c5082850307001920340c50b030103c28024440e4642e81615101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 42412441 1250 42411191 42411199
    0x20a091e050907030201200d05030a050603011b03090204060302100f021207020a17070305070b03061e0102030f1605060a091208010b070b18010905071802130308030415020d0209 78
    0x804542800c0c20407600306850100056000d40001c0005610440c0e05485050008903011400582ca1040d6454001008201c1c3c010030400300401510300a40e200e25540520106c000b404001c07159029900e142403d414040101501c6400e401d00355211900300d00300855001e03100c2e030a40703400804000c0995142000c54001405040388080610f10014242e861046d0001c081c0c2d0501c0b0710b81006203c00c910300d040c503001c00f4002c01d40008042603080c060301700103000b0044040d9803032811000300026012080e140704c00195030301059016990780001600c0002c03403942d4000f6a60f034540c659154900c54400070043c02481224204040380c240c42d0020001c00e031094207460700005001c402903449001c2402509540e180610100c0d001c80c00b84407005030040c08195901000c854040c7d0224291481e01c103040d18a40d01100041002007a000303403403e072014a81d64114117003042801e80b054112624400688403600100c04642840083c1c1400b80e01c2880d13000045644882e8100848043d4005003441889 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 42413691 1250 42412441 42412481
    0xb070e032b05040b09010c050f010c03150801050f010e07031d0c04060e04120305100905330102070b0702030304080a1b05060a0807082a04030c080a02010903110607020a09 75
    0x70a0151003901c099841240801c1d003001c1c0b098004450662800405603950300c59a801f038429a03d080c0304400d21001e0342c1d50b022038408001110900071142c1e580c050308a50303160070304200c00f881c400840749044d40d203a0b0000745d1050329045000c5015040348108039544810708820b4030040500045d00c90943d4100340c40c240040c40d543c07404d180392001c04440c0509219900d0182c10100782c46640031035804508016110030b807981f0f4100600c210340b42114581020039042508a03100103030b520350a02c400c42d007841d01e0200b581036203000075141c50107845014582800402c8130700442d6000e006460191401b82d084070203180c0c0604010400d0b11145003420b40c42c3c0060b090120307140c00c1404c04c072282d040e200e8036103c44a40300c0400840e41d2000080c43c0c4c880725040850188080a402c1980c00e800b4441d1640840d10f0f00d0660914215407240395104010030307402091302c1c0c00140d8002591204a0ba003014891200c529194023150701880b4071040290300000d07800c1c004c40c0001c4168011011003080002c1420 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 42414941 1250 42413691 42413773
    0x105010509010b1908130803010305060609060f0a1e09181509030f050c070302150703080a0501061b0501110409090b060306071e0302040306020a08090d14070b070e03 73
    0x51613115808018140281d00fa05007040c550061002a810918044030f0030a50482502e912482e0380003070b0421901e5410070780a1200502d0304000964000d4011110110100c0780440060300c400034611545170000701c04004060b00c2140030610400a168401003032146e540002e01d0b100080b2001c1c2001c4030020060700c0b81240040851041c4410b607981900d4081c1c640c204050281c41503041041034400d5886540c0d030100060b215030b042d000f06c001e00e00344281d44801c428074000c1c05540004100029180c50440100403880c1d01044540481d4804c0c0b400c10300001031405e01078003621446164a041e100b00250020740241103520148605000da440e9a50070345980f410107032504411303200700b400a4402e880c0e0316568000050703603000060480c2170042c502580c0b9a150003e98010586d10301c003040b1900100420081c043c841491b002c0c4c0070340340200c41d2070703c000b50541c6103010310755003d02110803030000185414015603243c1140c01c1c006046504d03c00980325250250684865a00c0d0b0812451301029 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 42416191 1250 42414941 42414959
    0x609050910020a0f030504020d0c080d1704050c010507020a09050c2a1b03010b0a0b0d06061b0305130e160e03070b04170102040b03010f03061107020306160e0a0602010501050901 78
    0xc0c01020440e0f483c3d0a0000e13816008601900c1d0107401680d20007502404400001c40710454540100034020107030040c0740082d800175054540051500d00d02614010410000a0f00400e21580816003400d00c503448000600209018208580000e05031600e444144094540003001a00344284825007011804902514548128400000300380712584440300b66902001e8003903462001040140000072044841000201c400556074440d1020540c009068400c094107401140301800c0d142c02e040ca40d6401d5100380e040749248041000c2c042010124800564403070b1a41014010038034031010070180e0410b50001c1c0700e92555070b07003040c003c1000004000c2ca40d003804112242110b0003202814201880d102d5a241c252014010f0107242d175500b000040780f0007050101841c040d190301c203001400d00b815450420201d859443c1c101030344c01400c0c440c107130059500090081d4072007110460003050025514040e00c131a08100e044607484103c1c0c07500403c129070305501c55412107800721280d0b03606980e60400301d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 42417441 1250 42416191 42416197
    0xe030f100c0e0d020d06112b0b0307060804050319021e010c14030903131701060b130302040207030207080d030e060105060301080a08030c0d1401051e130b04020d060905091002 77
    0x260381040c116010f00025190486021102c1c902070305c070100f100b54107661280c0c2294009100c0d00184880d0181800920345141e51000c2149a40c0c5010000c070a81c081c0060ba807964144201c000b082262400107041140038025626064400282810808903080010b51205400d40c0c40c180c00801d03012040b00c00c0c1c2c42c14025a03200c085d4035101c1c811400b6032502001c0603135100034000145488100f102481c02c1d0301c01c40080307004003510001506d0f1340c4950039195007950b04075440300300e40810078003001d103010b1840f07801d841c1280d40c12200180e56039100d00d4140c1c00c01030b4550188155005202c503290216404d0b801400251014000342c8035140e88540410240d80001c5c0a41201544200e181d240042e06020046401c00f00100820b42490800c4046001341c441c521944507000030054010031103418055400b24814040041403500c035001e00012031001c0405d4141c5000d400d4441c0305404103919980e04888102c880c08809010706901c0b44d0702c01c8041d08095955050f18403a00c6400b01c60000140f0070303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 42418691 1250 42417441 42417467
    0x6050f040b07050a050910050a08010f080606010e0103090f03110705010305010803180114030403020304090e010b130c0903060504050705100807051207050c031c0b030d0207090c0e030f100c 83
    0x100d15840b1000e04035aa038209080c070398184a4200004102035031401d85500912401c0e584050741c4c0c0c0300c540fa0040200c40e040e886114200c1a1f001e060044550205070a0b030700c40420700e001c0d0a2070506000407000780141820182c41d0043c100304007402c0c150702c29807000c009403410044a007040e903128011401c03501d0074424205160024080f07084041d803081e0f82c040f9009030500d04503c2d030208076030001c3c0c555482568100e000da40001410020065240158000380724404020010300c001c1d04003250700041125201001c881d80d91040300349250090b40311101442d00302e075080207a4902481c10742c0e80c41202c0d0040c54811111640d081d05a18880e502c490712648180e034900341041c41070403a1aaa90300301170140b100340801031040d06a0350004001900c1007060102d085a070441d03001030860110349030441070500a41204002c4402c3c03e400048000c01c0381c1d408100004d03040e07015841150403410f0719502e01c0d45030007089101c00300342030300107031040c4040da0a100403c40403001000941c0c145580000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 42419941 1250 42418691 42418703
    0x80a020901180b090109050601180b1605011e020c010b0a060c1407030609051c05090303220306060303090609050d0c061b0507091a040608031204030306030b0a050406050f04 76
    0x180810541c2080e050030b0003102d9540403500b0b4040000040d000c6078240c000701c1082c0c0d82c1d00d04102d180d41c0d10a46030480102e0544420002c24280f030100d503070603c07e218664000441e02e01090301040002d602002e40c264900d10702448866504404902a52251115006d00e608045001c0900d29050106004440807038507a080c42e425142d940c6c05a18803400c2910700103005000001000c110940103d804441c80342001d4028003104480000000445400803002c01109202001494a0010441d5120f440d2811a180181450364010340d20981d41e0704020310751030519000104040d0401042c42c162030785a06c40d01c1031243c80d0810301203941401c00003d42040081c0b51304006060181d134408409903843c40880c0e0702c4039001c3d00d6052a2a6296109840072a5140d02030052480d1582102d0804c95048906100c05403601c0003580c4c0d40d0099003101114001e0704008501018040e038003c9008660103840c481e50391810103110402040304950603205242000005840d01c0e0311400401e2040c0e0f4045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 42421191 1250 42419941 42419959
    0x6090103031b0501110304050d02060405100b030a0f03110615030c040509030d090c140609090f060a030b01030308060a090b0121140a06050315241512070207080a02 72
    0x14608076a603400401145a002800000300c00219000780540e003003111148040640d1b03810300b8542107241c420400da24404541000003440001680031511951004008034007245103070a020020341030030310411000344603002c03096182042640016603000d0155055055a406603580c2c8120b0304030087e513105c441c0d81030b00400c01d00500f91a02da031081d034101002404490416080d04540c2040703279901c0c3c40c00d860b80000e070842009a52603101c0c4c0410380110940b11381d424861030b280410414030000c0c08560306500382c0800621640c41d1210088011500300166012a581d80d0030060310906059444a001e07900c481c50110740316419010701ca050944c185d40340140c0c00c0c400168220300303070b64105201d14030a8450100c2221042c014480c0c0b40540d00d40800091102c1c1b40c00c0030107240501c4090420b02021011040000003660381074448150065403003140145100d500018407140f840c103401070340c016004200c80b45602643c601c1a48a024960200c946a98803148011b81d10005820020b50040b107031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 42422441 1250 42421191 42421193
    0x10807120b0406110706060e071407080c0c030607030204050315090a03080a110c30030406050406090b010806041211071e031e060b18060405060315100302130506090103 74
    0x21151141e07101e8000e40002a00140401d980c0131184d101d01000c0e124603841d14010300840d42025125500001c1c1e60400030b0103480d1070b540680a6000d8028003410080e404100404407510520100c0c600d0302d00242901c00618001d600a8001c2d000b0340100744c001c0c442c0c0e464115100c260070140038080e295800080003500b00c0d40d0340c1201c02001c02031001c1c44140c1c50760175244050f56810068180d50811401801c040a040d29004000e0003e4191520100307068824401c800c8411008480c2c00981180340450541c2d00d50804c0c0d400b82c03050b0140101800c66290000550407004034005000d82e00c02e0344649010984403008485d0f006000b81c80324034580000c181048014600c40945150241c42540c0d0003000755a5242c1040c1081c5690828085a510007a0340c001c200f943c0c80f80000c0a03000329500c0c0e2003803040d00e8506001440040406001c0c40d0385030301044840d40c08121f540804203c0481c441414503108847c00110001c80c4403c0380265192000024800585d0281a210706005400d0124a07865 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 42423691 1250 42422441 42422453
    0x160f0b0132040207030905090702011a0a0609030b040503070b0a0902091b090d11030a030e01020708070303090e06130f0b010f050705060c2206020307020a050d0c0e1b03180601080712 80
    0x6070860502449030000036041d08c0300580c080c49080190000240c80d801e030303040061002c00314002c1c54841c1d1101e0f030f400d003e0680c00c800e01c0b1080d00d4000da841d4017107680c1d030b140c010b00d18030884102410910101c4c040010020583c1c110408080c400c1d200c0c0c0005480703017134544218501e080342c2e10301e15090510200540d410060201c602d16402032011010349211400880d040103400041500000d207a03411215040d41c04100302c0c1b000301400c1d0014240c0c0303461502c00411242d498050203221444a42c042407031961180000d010024800380c2c00c011002c24111190000c0c0b1034040d2440c040b6800300740d0b20a1090103007065503005908070014107400d41c2e0310300f50300745180d104450103941194160640b200080030090200041c0c10141c00940c1e440c00d450041100819042e07000501c01e42100c1120000074080384141002c44082c540c0e1a0001d80b134101000404118100521296260110030041400c0d400c681418a0001d10010f035042d59803208001500d4620900404604242c4241c002d070009007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 42424941 1250 42423691 42423697
    0x110a05160914150301090204020f0405040b060412120e03030a030f15050306150111060702010b03060c07080d090602040512011409030a02070b0304081603080702010c02030a020a030302160f0b01320402 88
    0x8004e00004400116500040c200d8010030035548420340c02040034032480c2028801c002c0d055a04440031400c00d864481000058500c544c0002c4c045542d8281d4501e042e4000c040700345072002c0040a49480b0448104014000c00c9402c0e16400750904000d298402400c0890405041d10340c054050481d41e60345101029001034001856410411540ca140b032103400305000e0f079800b8400c2d990011034501d4031441018a440b4000c4c15500742514100241400a002d00c0e044819141c64100041502030b01410403c009001d6a0300c60364020b42d0541c0b42102e00d903410f60005072007003501c0384003e5551f10b403070620071394a01800034441c0c0564001081030000099040c040c40d8441d206d080900e2608902400e03000d1280784100c001c40c0480d4924062008507502030180c0406d11180e0310040d418200c203000000d5854101403009002d242e070001d1065088442c107002800000e40040403000c1540f075030b142010f03419200b48620344510000002d9082c802d03500542128080c2d4412520700c000425a2040200940c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 42426191 1250 42424941 42424981
    0x80309011103071b0e0a050709050f010909021b011d0309060f04090f021207020a0302070b1c060e100b0a120203060d0b0c1317030a030c110a05160914 66
    0x120050100f4400105072000000d050385a1000d4020040d10344848458041000340503103100307505190401c000d103a40320411008440302160b544980ca11900010794041c07049400106281c2d00015096641d01e0142d0702050400301c5020080290000f009105501c01d400e2804642c601e0b00304019000076441c000c009404009104410b80e03207415079403141e18045842071650000d5880d00402d45022054038440620f901c1607040c001382080742c04a990094561042e805118503144011480d20150034442d096503002600c0e06a040001039250000c40c1d0300341004846030144100c0115010561a4601e419620f40303c0c065101c602c100b0f2030000c400c0019400061105030010502c41070000840d031030132581d901448282c914070f40d44009803a00c20303100403903903000f28200000203d03503407079501c82c000100d030890b240c0740c6800103204c4110581214480c1070b000e0040160301c2001a903006016012604065035402c51410b0800c056440f5041d400740ca284a030029805030503000000d0302d84070300100000c440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 42427441 1250 42426191 42426193
    0xa0e030d061d010501030527010b04020301080a020901120308070309030e091f050604030201050702060d06030203070b0301260303070e030c03100905010c02010506090408071109040f0501060603060803090111 91
    0x8640003900c81201e140e030b8081e610100c1c1c4022501d8200400d40c4485001d000286000d02c1585040342c1660201d156840a006444c14442e4124030440170030340c4825400381e0014415942d030751352101c0d0640e880a0101d0183c2c0300d9142c1600000c0d1164090744041e0500d54507468415855440030810750081c07038031141c01d8042c80b400e413a0b85c0b8072942d0f03822282480f41f624000d6500b0003200c40d014401c030305860b035003005000311410481400580e0b00320b0140c540c100c1e07044414542c1c075040c204044010305038550009400d88a040008200110304e06c0c00345045e202444244100700804a00420100807038100e0181d41b50000c201003407150b0301c1540000c4c00300101404803004007010301b000c20702d04030750301e140c01003615514111003040180c00e018401841021384000e108506041000419258020304000c0410a000036048201f00d08440c2c0714106000041c00441c46203081c5c20615602c0890748401c58855183c80e0b4049407490003846030f5025664039a0082d8103007504140191800c460340d00c001601 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 42428691 1250 42427441 42427447
    0x60c0804050409030518010207050d08090d080705030a180e01030f210c060e06071b060b040203070509032401090903050903060a1e060506030c031509090f0f03030f0a0e03 75
    0x1041e1540e016503e000d600c81d65903941d41d92030300745090381c243c04c012440c0382c11900040741c100201d41d60a284043c6141e000b00c105551401d0410005810484000303005050002c049060030a010011001c0e090304001a00c0b00300c00750315800e1000303802090138002c074910a0024030042c004030743c503000403c00305445041480c0d041031007604c0c5481c070311040185040018405008600403c4218000d000809184200400590801580c0a4042d041424402d000c2049014405041c004150803100e1241e0001d0800c544c0d904240c01c2c000c000d54041071f00d00b4068400c07801c4e0314007903c1c1003081d0b40441300011903d10295908006103a409000d2080050f810024240880e600ca41d03410300c0b0703c03070080320004000034501d0150061600340c0078060044d801e101c0e00d001000c2040f91118021030340e00248404040d95aa0394980c040740c450b1003001c2030700703801903040d00c1041101d100c00144c0042e00c03445c0e82c3c216806060054800780d642e00c400c4034941d64060021011603007001603a007140244c0e034030101c16641 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 42429941 1250 42428691 42428699
    0x2030910050907080f030c030405090606040b0a02070608060f0108010b0c1e03030105032a010302160f03111608031204020406031212060609030f02091b070606080d020610060c0804 79
    0x82a14400c1c1e8885038143c110a204105040c010040c0d0341a41003d4000f441c100398030031003803a890f801580320380342c094458800002c800c1d41e11031049034081e202d505100c80d12418000ca00955032515405110301040a01c004140a032900c05000e54044105030b4900c28642e0a040d150b03010b58000e21040384e418850045a50640620209110350700c110880041d6240d6140c842054039140072107080900301e5408845e5800700000380c1c00a29246502800c0169450300b4500030005a00248200500040c4030404940c04050340b100c2c1701c0301c00d02c0da0102160902001800302c03a004003641e118440e6141d108002204041449035032480d8040d000900c0010040e41d00e895105a041403019400c000404001c0b0400c0c8000c05407094001a121a2411a03640750031603032480a09a034641000c1e00c2200d100c80091407610b00880d40c00b0b644440c0c070b064903850340901c4c548507024008a004203801c3d4020550f5140b91070f480080c04611035400b452000c1002c600d420400d0b21111042d40303090b10781650810000c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 42431191 1250 42429941 42429973
    0xf020903031b010c0804030903030813060c03090309080607051c0b0904050a061a09010302060309100e0d030b0409030e090712020f0a020c030604390b030115030905070603020309 78
    0x803000d2081582c0b165910b01080e000d641c00c40d0240040c88013803040c01024030010962110000307040da941800d1070802500c8500c80c015240c0ca442070001c0410b403c1c0f20120301070507071540002441c2c6100c0c0e210300c1d18868581c0005600c4000071030701200080e1080c484500d0701d030380b13040e01c1c2d100401010301700040078188507010541019007103a00b90342c0c2d68004046c02e0704220b510312404203001304540108800d0070203000002c02d01c21040c84041e11071040840462a01c000910074502c815a90b09020001480c0f6009040d89a0709079904c0c03400840d00d032052810340350419004101c100e551560707a00e50030152001c10004107090141031030080020b403006d90510160184000c04249a000314055104d806050000340303801103903001c19000b500300c3c1d410301c070008114000c81c030703035a40480070f90f400210750340240140540102d80a18030045806d030000584d860910707000b14183e03810b0460312104181c01070015001d0340e0b01080028031640c007161040021a1184d4055600845080c0582e031545800304804 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 42432441 1250 42431191 42431197
    0x1b031103040803040303090e04030509010c060b1207060f03110904090804080105010e0109060603020c0606060a11070f0f0b07030219062a090824071404151416060f02090303 76
    0xb40e5180d900014040c014035402c00b2041c00141684e249003032030340c0390030756005281e07010300c0315120f041c8080c040d01e0508101207608400302001c03000d880131007094801502d440e40c03500e0600c00c41c0b000c1a860000c00c460700d0b11a0040c0c0585007000c045041c5000c440000f484002c00d407944051f50301d56010f00001c01c1001082c064240242560406011303d54108450501183c940b40d00442c140751042200c14106240030540fa80d0140c0c049444030f0322a01e501400b03444068001c441c00350300d40280b9501180214000c0720840550704400460f110890300d60658442e64880c00001401591000301c004000203101c00b100e900303443c4150310100b00c9941d030041e642103400002084007000d615600c00f00d883c20345c4c0f00503030000825482d40141481d07402d2120034101429410b4101040b031814100040703519004148810348801e0892120740c3d15503881d0760401641c00c92143d240c00290403484c5214980c200030090b0307642e0141307201c00488125000e80e542c1000b460110468001c480d0280280491a0307028809 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 42433691 1250 42432441 42432449
    0xf0812070305010305010b220908090d060e07051008010b0c1207030201090218060d020f0d05030a020601090c050405090f0604060506131805010807050603091c1d101b03110304 77
    0x4003042e00d5041d86082d9094941e4583c0c030700d004048880304184155803903240049401c402c10400203400c0500e040c403048900c41c101c070907500140e2080a50f000c000c0b0385e5000e60040048103043d40c0c40540c4490402c00340c001c0742c14a45000443d00350050040c240400d0051031103c00000854101c1d45111307594044d681c002c9001a40542d5403820100c09505000d15040000b444d800b106841b0b40c42e0030380000c1c00710414500040d0283c100300b0000c1449840c1c20318566001070b0020210703510740b020000000d40c3c6035002d008100c5820706100c1d4501072a070090081d0b81c25240000c0c44401999914042d103900d0400003010709501680382d250014050f00c510004080c0c2d107000d00c010862440c117002150f542c400c0086214401b1915081c01040201004540401550030494074541d0300e80303910541a1400702c20164115202105c04820704449400030486110258248041d81034008084e080156041c0e030200c8010201d102c1ca407507460940c080d400c1c156142403003420f14032540f00ca01e204030380c070b5038016807c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 42434941 1250 42433691 42433697
    0xa030513020907110c0a180510050604090e0309030303010e0105150f0d0506041b080a06050a120204050c0d0203010801020414100207030212100218030708120712030b130501030303050603010e0a0f081207 89
    0xe07c1300f0b1103003034055030360300444918281c1d50399407074000495001c0c0304070710440214070343c2e07005c01422440c03050045645210004040325102d58450840c91400031080c422540b045803103070b03010401030b0810030a4030414003030030702440e00704a28200104050040141000e44c843d0356403080001424010816000079105955070032802d2411019650407140c16403c114842c0120300c0d8100940b2410449040010b41d040d58040b07032a885800c84030215006020f032001085002100100b01e650f41540900210b400c0151492919a090400d00a060340300c00010001604620401d00140c101034008a1001c0300c0c0d0000c59003020840c00542c000c9800002c4a050029803004441c1c017a0b141c100a60f80142009801800c3c004010010082181c400c08000500c008401c80c0b03040c038814060f50060100d804d000e4201c0d001c06881c42260300060800340400c4002c40c1c609004200036040500c13036956007a80d100010402d030ba03e6900d50035060702c035a000494800c901004032240b0f011101c48001d0003109030761 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 42436191 1250 42434941 42434969
    0x3150f0d060e010515090a0207140303070e0a0b2505030d1802030607021c080a0204030c0306050a050705040b0405040f0f02040e0103030806090408030f0406090b0c0a030513020907110c0a 82
    0x200c0c50b9800e440300900041c0c0340c2e9039290314104113550f4000d1b03c1034004447c0003006a4480f514544400440c0c000e0041c6500c1d80004010000b086800c407507542c00c2e0403012a621880c10b41c42d0015079005002d407120003041300a26090540441c03030707590300185400f4000e4048904015100c1d00340c000f030f5100c8020403032400c1c441c40c680c0011070a0401200785c1148160000e07004400c01c4100c040f082c01740c0c00d1841800c105843c3d022070b00100742d540c101c0380603542203000d01000c3d9803642030010107000e0940341445214544400100c60703d1190f41074909444640600c10f245c1443d001c1004068458a07640d034114659519000000b10304901c002d0005040c1450040384942c076506000c2e203501d1000f4045405126541c0c100310020340c01004aa5010074028401d100d161514240300e00141b0a21100802c081d40301030600c080d03800100047c10340761045030790520960b40c1b144004552103900800080d009510035021400d0b20b401090804c05607501c5004170b0f040645a40300083c91036003194013994101c2c03130321 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 42437441 1250 42436191 42436211
    0xa05030f07050f0d020604020d03110607091503060f060e150c0d020d020a08030604050903190203180109050d0b0705120106030b090c07020a0b0310080106080106061b050303150f0d06 80
    0x3848000e000b8424800030388013400f080d03500a5103400005000902c03d5a09100c80310405006183c03201d40c212110040740c1c0f41d46010310b0003401040050044d8074401001d003003034684c0203200c0e000759001d0300c1001c400c04c0002498503400342c80307007440806255440078080012448604410700a0a05940707000028240ca1078440300103030411100f0f00525046401100c0d9400c0401d64400850703803c20000d8400050680d59a01c0090841c05041d1000340c01c440180c2c010300d500c0d0750010150440340901504003100100180054440446a10aa58111400316035182c04100ca51010715444282400e00310b203401880c243d89003100c4000d070001404603650300882440760030002030321644070f1100d110703261601e6030340e0300013880060461060501c00070000000800d6642c0c0500084000e000c040c009108840d160401540a001c540c003a03079000400844010b05103418440c501001c03a50030001441c6180c81c1c124030f00348510f50507080990019280c405c1010243c0755607541e004254081c03031000800c0010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 42438691 1250 42437441 42437443
    0xc0702090106020a0b0f0a0b1f03060f0501080a0b0a0b0703020708060703050c070f06180b0f07050403030906230403060b18010510110c04060303090602060f13140a05030f0705 77
    0x3041e04030108652224000714002141c05420907004044180907007210313600c800e401d10184c5144810719400c20320b500310004c1d01918003110034041100781c2c0c80510181e9150450003690144620840c0c1c0010051400b059800003242c0c4030b0007040c800503180014580e1200c415040d1540801c40480059101000c01c02c000b110600c469038000170145010f120500b0608031181c520b0150080141c0442c5007403103504204100303644550041e003d50000300e01b090079039040800115200f00c0b2280a00034090000900b040d204008490580341d1603103c544680d03040c10300854003882d0403000c0e01e40e07694491501ea0102113508019000641c4510804103406d441c0740f0038071405c1050b12003058400502a0014071450340c41c4030012418001e203141411103200018043c07443d18400000300358000d443c20700b0100606a1048038141a03c0d126021117907240c6615040c10307807a00c4212004200c51401d002840c0004070308942401c0a010b242c0100d4800b103100d80c644d1070039a0b110284186000c400000c4080800c40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 42439941 1250 42438691 42438709
    0x60406051801170120090d14010c0e040b0a27092f09161205251d010e0414150103060902040b03060d0f05060106020a030306080d09031412030c0702 65
    0x3010000e03c1500f40340803461705041010301e860079031207034017041ca44c0c3e0907280c0c44a0b00b105250011514007100702032600540c001d28008510800051440211115a09281c00380200d0b804014141004251500f180c180f01900312a01c080e00700748400000703d08442540c018806003034001c5e44240d0300c18420305000c1c029001c00c200d00b07204980b00d80e142501299621030741554000000d154629824a8240d001c0307540146000590000b01c0c60041407204003005110b100344580d200d0b00b80000208411903066500c41c011101d442d4546910a40c1c2c51029403049440c3c00c135103503002e000800c4205100080a03c18001200c043d40c0c5080c4440c64640d05690600032130340200140d070f10031440d080c10107a10180d54072009104900410496803c003007003010012416070a43d4225040da82c030355841e950002d44481d4030900a80000e41800b101003810074011540b81c81014250702d0706540c0030700d1a42c0b2043c14064500928106016214680c48203c03601c00003144901103806e2203d540781454410890100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 42441191 1250 42439941 42439979
    0x12030c13050f0109030803070201020c01090804050f06070b01090209010c0614060906040603050c06070c0e04030806010905060901390b0414010c09030303020c03041a03090606120a0803060406051801 87
    0x400301c1890b09003590708945a03000b500c0d00400d807542e4079640c160090f40644a0444620295803902d09698140010070010700142c0f81c003103501d85002c00403801045128041d000c00038020492120040040154542c000c00c508035060400a8800000d500d40300c00300e0b003803d201c00300d0064035102002410302d01058108e0340894111002c102180c29500e07031550301d90540c0c1105014500001d505028060344a944c0c10090203810010343c00c0340f426107401070003442c0503034002d0b01244455002086629001060300c6940070180d4584c1d007c5c0e503119620380c0c80142c0240490b640200007010f0325075208403214032407440038081d03c0c0c407904600b000d1070f0198901c0010072040348164944a000e01102d588445400d04480d090f10b405030701c400c03c20b00c0240c1107102c1c035441221014034060744076200340c80280141d0f100d12090015a2001d036101020710880b860029580e41441c4c11000c0f00c1d00002d040360307016580203000640300103a1580c42c0c0000c01d48501c80b40a0f203500c05044500108203010100810300703000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 42442441 1250 42441191 42441199
    0x3030f1d07150c060504080415180b040b0307080402010e100c1403160b090f0303010f170a0308010b070503040312110d0216090c020f0607031d19080702010212030c1305 74
    0x844204a0b0091111820400003050b050701c5401040c28001d03104142c0b005402e0310202e0b1449020043c00103010751440045038103400f410a240080c210304c1c500107580860740b01d841c09901d1a82e90040c00c41c2c481d1b6008008a06116000b01d1205450311214440542c040041c0c40d550140402401c14811211b015021001164010001ea0050947c0d42035825001980007190590b9038440d079114908100c030081c4180060b1002100004021182e20809012500001c4c02480340c40410240140c0322001503001030003141c0020010801601d0345002001214020816607041544940d01c0c85a01c10303a05044500150348070314584c003105000e002031800c000060004090241005c0100450000c40348580313904140d07030356a02c41d051030080c41904800400c4100351807403407403e41405001000340c020b003040c140412006200185030b000030625062058124030b0014140c443d9503a0103284d1080d1003c030304500035041e000784c00d0707504d1201071406407805442058445e455600203110004040c0d0050f031203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 42443691 1250 42442441 42442469
    0x90804090b0f030c0108040f0b040302011d0a1106030603010905030d050f0f070207051504052806090f15020c09011d060a03030e0904030207120503120109020306030d0c03030f1d07 79
    0x1c036543c0014084d8400c1000e00b80300c02c85507201d05008041400c0481c010701081d0001080000b00360f410b6000d051042134401e0342d00c180f03481d101400d584d9802d072800001c1041202d01c104400d285400400f0f147d00c11402000402e0b0130040c3d0740c860f82113401c41a8070308002500c50081c40030340c0c18034280042e0320040100d486081131824980082d174030605482a00c1c092061081c10641207000841200c02400c0080c00d085028500c0038185008040b010200c01c00480703511201003075152107808050226100c018000c0b040a0a2101d1042c2d00000305803450294803a006120110303440782041e9034020b00c1e0300248040c22100010031000300d074000800d428030072a140481400000e4101500620032401503d6010700c940e01d5190a81c5090441c2d00000404c3c008a02c0d01810008000006c006c0304030700d000b5600c01d0b0303680c1c1c0c91010168001500c03041c1e4541c00144038081e00903c900c00d0600e0440c0685004200d0890150f11602210120950040440050318482e03280d82001c00201c0003e1441000d1502 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 42444941 1250 42443691 42443719
    0x706020307020915061308060a0f0506010f08180706050c0c01030204030804030b041a090a02011701030f0311030d09060e0105091209040f02040e0705040305070608010b07081c090804090b 82
    0x3003c0c8200034540103019500d2603224407292036500a440d05102508070181c4070300e4888105666954081715070101c05070400c603d03c1c103108130b1801058000e175011b071118040d220b51288103407040f44d402480800019503400044038120010001c403401003000b0707114280e4985a0f556441d0030200d05403152410b050040104000044c1100125011170360061018801c50310740d0718054440c40d52001004100c40740c03000500c0170303d20703000c115030076064403d03251042260003a00440c00c0e0b29409100c0944021504202c7d180441d003c0c8228508001030b00c400d880c80c040000d50070904480d0380340810740d00c1540c1c94003802d400c01000d2041c1d542103d10600102511002c030b41500d0480c1c895900c1c2c2d5400381c0e885040112002c070058040d20f01601780308101e07000600d04031400400913041071005403031503c14100001003850003503560505a4072840381841c0b4054454645a0056214404002e5202c8440f060b443c051992480b07450081441402c4050751946811024020341d00141c0e01e4504c43c031405101d0310 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 42446047 1106 42444941 42444949
    0x8010b070212061f08070302060409110c01050f19020315011818021206010f0503070c020109080604061506030b1804050106051c03030c050a021e030c0102040803030108070602030702 80
    0xd4070060355282501ea54046d50310019411210030401480180c4480d0481401d40c1e110301c079628580150b5200481c01c41d54100e85600031040c2d480300303114003001096124480294a12411360a508203000641c00d22020240780a040c0007020804074404a03040c440c9500510f07038038111580d10018180410040d40c0612801900c1030003840005d0015070049920528059895580509680c0c4806040c0c46000c010541a410321600b00b00c0003501400420615108078401c2102007051303022041010108c5155401103000d160404d08100c0c801c1c1c030b0780928620406c01101e11485983c40303d0130003d0040010381c10041c0c119070310301219900400c803071400d5189584aa03400700003451101c00c042720140100c400c0707900183c101800800031040ca5a081524515008080c0c91900703440d4910182284c1c425030080d880c681002c401045000e009002c200c00801035400503626101c91780d8005 = true := by decide +kernel

theorem cover : BRFrame.Cov 42266191 42446047 := by
  have h0 := BRFrame.cov_init 42266191
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42266191 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 42266191 ≤ n) (h2 : n < 42446047) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
