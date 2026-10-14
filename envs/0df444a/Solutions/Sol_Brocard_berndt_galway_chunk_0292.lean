-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0292
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:01:19.506079+00:00
-- url     : https://prove2.me/submissions/29aea522-448f-48d1-b8de-3a0bb072034d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 52338133 ≤ n < 52517989 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 52339383 1250 52338133 52338149
    0xe01030b0a080c120d0806060d0f020703091a07030522030203071203090609050616020105041d040212010506010804030c080f040e0f06030c0102070303140f0c030d0c02031603120e0601 81
    0x542041030314104102442c0c0b000030f84070000c2405175498070000d051440c000b00350034041c20000c01c040c1102411a004480140031081045541d004079090040003010b0074082d00741480080500d0b0302d044840c0504036203803243c00d80c1c6c90340d082070090b8010090200501010346481c5100d00004809030b9014440c0394001c0c0501c402c4a960100a4076000d030414610b507028600340a1030003420056915144200e82c000c180c841508171203c03000d880107844500640c2c1043c0540c0e940c0c0410b1404130040d03064880c1c0614001c94042c1c2615810480c29426110b0440d1f03014005909000400c000074065210400c0721441106487d04210780c1c110f82400c070340c2007a8003540d40d5a4039081442400c412010b051034101c1c600313801400d011011200082c0d0755552500c001002c0101c940000c0800140c0d40d420354181d004400340c929683c804a4428a03a203411032043e0f00d24136481c01c01c0e260a8a40000b046030a100702c02d000324035401a5a4909523044440100c104000c681c0301c080c185811602400703014080c010708 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 52340633 1250 52339383 52339393
    0x16020f04021e18010201060e0103030507140105090708010524060c03120f0a0b013002040305030f13060c05070303050a17010314121c05100b0c010203061203030709060e01030b0a08 79
    0x490f402034070b004003800d203a043d640360910605c070b6500b0640030715055a4050602640c0c1d50341514108603903200001000944d9440c01c41445140d600104071036045948800083c04262194820350760002080280c44c641e102c10000c016260f42170400150140e61160402d0f60304085081200550b28042129065803209442d07040107628011032180c1c1a0300f0100703207850301c0001303852140d140850b4503541c1180554191542c0c0c0d91280030b010b4044501942d0702500f0b032038450070001c0b402d40a81d000380700e50b040c0035803112030b020810702d119091180940d50804001d02c4040d01d56141591558820741e6818101701c0160482c005c06001c0c00909802580300301020b61107504c02c0c4203c6400c00c01c060141083c021010000100c8100d804c03502e4182001e10f6400014981e11801a440490441640407021100020444081010040d409036200c2e1000380ea400038400b5407185a0f640300d2004680c0c0502013200c030362040c090248140d404a82401060500041070000000081c901500e0340e0f000c42169400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 52341883 1250 52340633 52340647
    0x806070309020a0801090506070513030c120b010509160804032c010206061203041403070806070908060c0703020312060a0504021602040c08040b0c0d021b030a02011116020f04021e 79
    0x40600c40f002452a14020441c18074903551ba10303142c01002d020b5104000e40841c15268100b10b0b2003441008580c884080c2c41c800703a407a16004046441804280c1c0c042e100c1000014082c03c003025118030800446008580640d070500c0141c5040310054000d41c00c00500c05200a4072100c00c0750034a140c440028028140c400e032000009150400041c8094060148400c400c3c40040c00081920f0030340b0400402e501e481c0840d0400b003880d000c02ea45c0096214030542003404805608580f11109980651003034540d19170701c000c2805503900c200740000740181e00030440303102150150500181c010800400300344505644d0000101680c0005013031070505071118414100314a800e104209092215050252452805440c0e01ca00d4002c002d0240c0d4490304002100b2040e024182d04507482d800030000d40710418042d10070140d81e00d0300701d071100e500590720f011040054a4400000e4030707a101882e80c5d01c0766010000c1d509001c2e0404951a0300c80e0440e0302400000d5196410300050901c0b1200010b1f03076074075010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 52343133 1250 52341883 52341889
    0x70b030c0409230108011109090405010906020f070c0503030406050301182901171006050309030c0d0e01020f06010e07030911090c2502030309040902061210060315050307050415080607030902 84
    0xc3c041c0d200250701c5c1c0c0740000c5868601100400c0d2140c002003103e4400595a541c2825405420740030b070f00030b1140340f0010f18414074801030f00243c20400d0003002c1c0c0740d20081d2aa814075139640309078001c02000c50014001006162b02e04001900d01810440001c80e400e110490702c8604104a04110288032800746e03820407803568000440f0000c06143c0000600600380b5a0001c94030300741c0350203003e04001e0000000740280104108807045c0c0c0941c1070450f0b0700b2445002e001003020190440050050045e0301c0c40300c2d00b5000000d0818180c030030318410105551201001034000306403140b07044400c50444102c00440f65116030000d4490b81c400303003da65581c039601c09002c1c10940b40c41c034601003402d41d540092015840010a030342c4900b600342c0300050307107400600002d1414020b5095074080484850100f010b0740c2c1014610400300c9011307850521a481c280070541c40780101c076008282c2c041d48507240070003142c038181c1c00050300d03001d20040300b02c04151030705030083c01c0c43c904841300c00200392140c4d10002103003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 52344383 1250 52343133 52343201
    0xa02090c0406020c0a0f06030b061308060a050105030a0309150905150903010b03150703050406090605040f0506060307081203100312030902190501020c040b120d080405100b03070b030c0409 83
    0x62045890071791503414008454010440c6000301c0042668842c01a440c0b9140d5070200e807801000100c645042c156200825551960110358900103141800000212070a0010306a5455903140e280d0780704403400c1488031406420303203804281c1081944600000c0e1500d64400038034030590b10001082e91202c4220501d03084d83c00c00e0014038001d520142c01c114030640188501508500c031445c002c5081d480d40c1c02c110014185840c00039140c07514207801d01040085c40100c110403948903000341c80b8156545410503458000ca44a04586a003148000e130b000041d42c3c80c0250f502c403040c2c02d03030700b50110740b40c0c0c481e450200c10034081040426074940d000340c2540781108443c0302041c945150f42ca15142031400003501c40c845510301d030740119140c0003949100ea81e2030203c5880341400c04115030701c182c08900f000b45040415238003650240a640b0101c0d00f0141c990280b480c10043c0035008008440c584001501241d1000380038400f180c03c107220119042d049400b0f4261401644420900c11060307000254880c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 52345633 1250 52344383 52344403
    0x6090c05032203020604060e07090f020a0f080108030901080c070c06020a0b01050405071e09051e040509030313030804060219091d010501020d0f1704080c0708060603060406020c0a02090c040602 85
    0x701d0b1101c945500007640020203942c016032205020030403603001c1c0066440d1801a401003941c0600746601c0441e0300c4c40350b078080c002d180001e5440394401441803500f42e0b15100280602d0560703800400c910001035014440c0030f030308200000262841c01ca00c0e034071002070800041e041500180c2060384a1414030411070451400340404450401881c100081c002c5e00035241b04d41840141b10030480f80628103030141d1084001014003401c410220341000c01c1e07a4588103008034515108611b404017040c407507100002913900c46c1018405c0b0030003c0040343c4041c4e81031000104204c44c410740800800580d000000b0004481e24001d407603107110607046c80490100c1202a8984408125810004110076a4005400c40c0d01000905100210040080c41103c0c041c580410380480c4203056810700040005080041c507030b03501131300c050b540c2003034130b441095459007401e44409905500800214001c601aa40103051003000402250600750195010803100c50302151444286400420200900c54040c800c52041d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 52346883 1250 52345633 52345681
    0xf07020a091103010909031101050103080c0d0302130324060e0609090c0901050603101710061508071b0501090b07081501020a0b072109020f0105030105090610020106090c0503 77
    0x202c40c00050b12801280014442d03000c2c116100c817a440706050240d004440d580e500c29000344103668507400d06545d541e10124105015104070f2a6910b06d0300c0c400d10981e00303843d03030300080c0e00103491039626034850050000141490040d5694604030340c0000134412103006000c01280129140703001010440c8000700104200010f40150070001125654000c600341900c0701110419180d40307031607119031908000c1e60070207603600d919804011a4108002014407804090711402d00c507580d03c480e0181024000741040c1c501140801021880300350081c09070344c1078060400c4c0c5103400b444e40c1b5152182560002c541c207460a0480c5d0303042c411038903070014509500c04035842201929a0281000075030b13440751148040c0c03427000d47d10040b41c01c0900c0f0707080085200c600070b07071040500140d280b2030300010004000100c3c400d030302c1c5608000155001c0c0382074904a410041c1201d90685d41c850031701c14081c405421a00071550380c0c1202090300c1006200c4c0401c190f01e190b03506600c86c0b03481400c8040c40131a800c51200303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 52348133 1250 52346883 52346891
    0xc030402130c11010204090e0c0d0312090503091302070303050609011a090a0509010e0f0a05010b0304030507020307050406090213120f02100c0b1e0708040201050a0c03020304030204020f07020a09 86
    0x1603115041ca51924034484030340014100940366044442607001c0d01022803039400000c001038004a02e402403070300380440205039041000341e0401c01c80c0c00c0c0d149643c000c000c12000c4641c040311070707041d61004a90038025825240382c032501c0070020b050800d03900110101c03940d000c50100181503151042c1c42d4031040c141c61943c0346505000c40313240c20f6002e1030420118081c0004410310340b6155245c1000080402401c2049603586400c140002030008a07004032080035070500280e00021140a824101c500c4140500c0c610f85568404507410b0780030000030307038152103501c100050a413250300c2a40004c01215400507220707044005c4e1010050390a03400300300c02031450312a40000c14002121031106950480350150580303c0d10340d080d07548042c441e1005d0428510602008410707c6800e491a030325092152404071180d64042040ea2001c105480c0030380043c0342800150219406070101c440c00074000d00490307081036640d600003010ba90007584420907031040070a040c4210b0400d4041c0d480a0502100140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 52349383 1250 52348133 52348141
    0x4140d0302060114120304090212090118020906120f0717010e06010b03130b0103050334060e01020c030c0705010320180109030b0403030c080c0f07060209150705060402090c03 77
    0xc0d42c800d810300442d10403003805a1403802ea95501d003c280d500425001c2580c0e100c59a07800000003e40016400408140992000030450b1070184615800d054070840c24400b607034861b0b024022400c000a06c0690055003013a51440590f00c2000308400600311840103016480c00c11642200710f0440e50f400c030446d60304182a4804561002c20860b042d1017801180a8480c0d40f40410072a01c5001e019002c0d003440c049600105c00d011011004011960780300e41c41d900b001c1c0d4642c0280316100c0c0b80b2196100b0b16050b40d015540014103581080315882004030000d8140481800e001c2d04540c40340000e2032066001e18010400355070540200d11480c051684a110b502420046921135849480a80c0450b81d103038038202c520603030007050403201654004810b60030301d184c64030f0040c0040558070701e00b03400710b40b4140000c1c042442c118211a003545c02c203102142092180d50b20344000e50003803000180d1203009400c00c00c04201032940a0940d003401240241101e00705401481600c0343d016000c0c0c0c801050400c208 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 52350633 1250 52349383 52349387
    0xc1b06090d1e050d02071a040b041109070e04050901020c0708070801110408060103031b0f060203041a09030708130e070804060c03060308040b0a09030b01080a0b0a0903020a1b0509010b04140d03 85
    0xd6003440f00c100301c0161b95100903280085a40d040190140e440194040c18882480003a010036442030303105d440417440724503400007005000401202d030303000041e290120001c4c3d503040580119402040c00700015060800910b00c66091039242d030003403140ca9002c807800304034400c42401b0300075140e40c0414500b4a0f00d414800d80355210740e01400060113022442d0441c2d1040e40c11452980c00711504425490b00d1017100d880d24030040d5205403402d607400d400d0540000301491a100b01240142d50b044015850702400d5543c0c1000b50b0400c09203c0c02c560502c260010b120b00209000d1031081142e07584252851919141c584221441c02b001c0d88101481c0900030b000240030602101e0031f07a051039940d5078980c60644411142c1f204c0700c3d0401844102c915000088403000080c610301a03a20038141110300e60b40b4510f801080710b03010f103009030060703100341c208402291141c1d4503083c43d640b204640990070380d205c3c00800c000304001e03800080c2d141d0001404008402d03100c203080000d520104d5080c02414681d40700 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 52351883 1250 52350633 52350637
    0xb1302360a05151215100f09061b060c02010212090d0801030303020c030d0606021006080313050d030507060921020d0207030605130f0506070801050a030b0c1b06090d1e05 75
    0x40c0c24090800f110503070048900300c0e000e841450124030410002c500d0011080a00e00c26a000c0e0540100c4c95640e20440c0c250142e214078140d41242d6407050368a80ca404011500203030a00012150f2440c0c00690b04041400740c0296100104590005070b51150b800d800348181000c0200400c00390b42092501d1000349600c00b9000381140c1d007500c2c001da26105000b81c140d045114540c0142822440c0c403000017000341d0081070303041e220b010f190380c100441030b80c80c80942c0d01c030311070f0440038006c030902d8005c240403e1a281c5010a42180246001418040070382d0700c3c0030032a40a110143e030040240c80050603210308104000b085401c103403015001c24048a48080d40d03842c9a8000248669181c10010307019015035003070700280c5900004422040034550504544885050322514006810b0800100d2a8242645210b040300d520803c3c2a009507601c1d1101041a0000c0000720000c00c920940341c00749040401c0311030300503030010014001d040122100607092000700d03201d0100810070080c0f1040304a402c541 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 52353133 1250 52351883 52351889
    0x8070303050f0a0302040806040b0a0f0c020703061a0303030709030512041401110c150712110a03112b0905010305070507030806030703081209010c0c0804090b1302360a 74
    0x1075039150f40d81c580041d4083e000da41c001001c0d6100358000c210601088441c0341d4000c40450a08002130805a00a9019a00b29043d03040160380009d500700000752059100e400b052a2031421603482000000c002811a802561f221000422031042803040c80401d2001c840403048000145282610b444488005040140002418810b400c601000621024000f10400d050000c2581a00d0149644c801100ea0080d8409540314143d00c003091451502606060111380360060040c1821030090b038017102d0302030b109519910755010f002c55011142001600e41c11a42c0c0c0f81003030407080c03544800001010658103900c80ea040600b03080502000c641c1007012110081e40520703003060190f07505000704c0d00d4440700d540010703c1c008000900400c402e034650001801917108100078014014281d804071140064203030040d158040403c8104800c1441d980f0141d4001e0025100c152030600b02d60b09035040341c01141e007040507a85426107440301c80d4a030302613134900a280c0310000c40002103040f0119203010b00c580 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 52354383 1250 52353133 52353157
    0x14070201080a1e0507020a03080603060c03060d0302150106050403110103050408030105040f020c060702010506090f01030506190f0617010b1518010c0c09092f1e031b09010807030305 80
    0x100f90b0540044105242080b6803500b40f401e00c050706100c0340003580c40c01540e00c141c1c00911030700c01042a40c42c000c01d016020703103816513546065440d000304000e60182c9148048096100b4485010b081d8160310b8060b90082c006503c43c291120300c0d4bc14000700e2520781d00e03800d40c101450321003013200007007010040d24155107041c0d400103440d094181c01c0710001c0c444c2594894103449441c0400220650540190340300352001c0d034116003030707486048202800110a001c010200d030412400920301c1a12840d101c590958100d8000c01d0613544843c110b01280c240d600503408110301c040d03101d10500400d010302102c015081d40c607443d0141c0c00104554207402001c0c00380c07000703070000b10001c460360f0300c542000c044e0141c0003150b011805543d10110b40c0241403055080780c070300d000c078510300c2d00300d8601c01070000c80c0b040c144000280802001c0204914110300b81d09080c40303022044501c20041e10100406036000c4031005a00e0f2465801e40d08011015070140d00c0703a017069000712401e02c0065445003c0c1c070f030107000030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 52355633 1250 52354383 52354391
    0xc0807030c11120301030c080601060e010f170a0c0e0102030a17041b080601080715080402040b0a17010203010905160504090209010c060c0c02010e0406140607020321070314070201080a 81
    0x150802c403000012020244024440c00c00e07988100740c440d034001e40c1240e00c81d503480c0000c84da8130111240c940380240309000100f8452420200b955010b41040041c3c81082d2030b192074000d0548852030441031040c0c1d14600e03001d6913100c18800b0f040e0004520105106e003400150f080c4080c7c554000c26080c050b00b2800c81194000001c0f508200801f43c2c00c0030718012101c107150040c0c3d00c8070341c252768540091041c040300f8480c42c040090200c0f03c0c0c00d6212048002980c1c2c4150550300e075006c0c48081e041c5400f03195000618400c00180c244100008036050191184c0096502d52500403610240c0340c002d00502c051241c1c022200c80c10cd40c0050840d0119188e0110150710b403541000140d0301c26080400182c240d074180440e540440d94003810712100745200f625400c0b051502c41040c08119000e5000d14402c00c06c0d256110781907031a104002c0d11206100508494030714048480e41c06214800d201080407a03031004c96040209074000400000942400707000a0406040d0f400003040520082d0201490940e1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 52356883 1250 52355633 52355651
    0xb03120a031a0a060f08010e040b060918010f0603020f030c0307062d090305011a1e0d1e020a0803030408030a05090c031209010e0301050f0c16050715030509010c080703 74
    0x41040c0407950303202c0042c01c51400c180e0b00e0901508890291540200258002001042c0c00d0313062003155000b40c0c0c022403440c1c4296180400d10404d0308028054181281c08800d654070004801d000d403003910704080340b002c62503038071710b205114100100d5503295119402248224001ea00c0000b4101d045503c240750400b40d00e00041c40f90016060150034a01141c651420ba107598240c00061040489128900070408404690701c50302409000c40c443d60ba008043c4040c0710081106510006281d81000f0590074100344141d0302c080b035400c2031408e910302140321481d169055103480304554000384400001740d403451400d0343c0d890b41c040c803004200581050362030b00801d000c0c40c01003021388030388c0e40003408480c0e1400c14000f139140c0540004030b54500280e07004103411502c0c141805400c0c0200644200e1983c903803201c0c286140180c001058054481b401c0074083c1c0c0200b0401c0184100034504021b42181c60700b009040203064860042c088212a810000d90702c0340d550713001c10b4042c0e000c1103038500092403d81d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 52358133 1250 52356883 52356911
    0xb040b0105160b0619090911031c0807090f03060e0706170103030804111905040513050309060a0509060403080c0d0903050a11041b030506030c0f01140d090b070809010b03120a03 78
    0x4954005c00da81c0c1004140080744079221940701402042c01083d8290300c241c001c0040550b80e09110080c0c240c11030b100f10780c3c00700d0035009400d0a03401c00c40d54144154429201c1c11040003441d2168421f40700240c07985500d48501006100300f5019003110320703145030070f684e0340242c000c0102c3c41840300030b0070048034000080038846803000540b400c181c000d001400c0307000c59501042d03040810380112031040d454140814460039040800c10075051b4808040d500301920001001140d40000e80100d0510004100b002110b0743c41c1c0d0300a001440c41138075403a882e841503a8003503140c104084030803000d1217103010003400800c40005428155903403042030640d40440d9040490013401d070750000f1021301c20122070691109501170300058410300042d400c542c5a09442001c003e007900b4090309550108581c0000a641001c40d200100803581340d82d4004a04d0308101d681d4001d80110441d40e000c0051081000d2112142007800782c44e00c0c0300800c80042040411464400d20148500c0c0040b0040c10b80c3c88641248081c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 52359383 1250 52358133 52358149
    0x2506080c090609060a0806010206010608070210050606090a0b04030519020612060316090b09090703030905090a14010b0702011d0604090209010306080114010509090610060507020607060c030b040b0105160b06 91
    0x414040c0000d6100c85403140042c01c450310642c3c01c680276000700030000c18400e108901c141e10581180d401811582c0c03407000c2400007400043e2001e500050108003a81141d00e8201000b0000c1203c0d070300841c1d0701e61643c00d00c2e6040600007143e0b0705014010802e407001507980e21040d510030250070040c1804680398000000d10b000703a91812101174202c134030000108200c82d5071154842c00c100380c030642c410342e452a2489031140081d000003004075520078030034000380c20007a0303000d40c1c44041c100c000188110310407410300c083c3c2d01c240d000200403400001d121046580c0156184003200315040700745c03d80c00d54200002c005000c1e0b400381044860b404a2030314260380c0300740c01010042c401a4001c0100c1d07650901039501e0000240190703401010f091000c034801c502c0c005031407840341521500c68000716080036003c0702c80d58060a030903a4001e406122a10200d4500c0c03090300d40e81c2d011354a00140c103a82507402c4c001030396140968681072010900041c117036080c0035032120507190f5018143c00d58135035691000603084 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 52360633 1250 52359383 52359397
    0x9010e0a0308091008160c051002030f010f05011d0105030a0609090b0105040c020a0512161202070f06020c010207031401060b030f040507050904050a06050403050d0c022506080c0906 80
    0x200c100000001489110300040c0890b02e0107a6614003201c1c400c503010b0741c51107001d0310107425200785038414555462142c042e0380042c40c854010780d6010b4100115000030391700b055030602400041040100800011500b180c0d004003001c1c00c2240c0a034042c0c20a807031092044001c03150600000000040b00f285907548500007800e1600e20402c0b080c4a1801d00340340390582405a0360088d40744c01c1c4c0e950903e500004030501e03916803200080ca8806010b5031903c8031a0050102980f941e0f091080b900006000c42003128801045940100749051400900c48801222035104d01c081d50820408202e01ea640030030360360300b504d42080f25000c003103261810180c014030312a032141c2039002c0c0110030700440364100540e070b6009a0160f02140ea000ba2078070100854080c0689008029038409030080002501c241c0090317138007a010b801e000d82040100700c90794043d1034200c820b01c2d0040e00261466a4a07a442c06003072200590740740d00c0d200c0c013142058000f4000ca60041c0802c0000c0001040740c250307944d0b4260489a079 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 52361883 1250 52360633 52360639
    0x70207080a030e030c0a051c060207080d1407090803090613030f0c03030909060608041104090b01140310060b04030311010e010204170d0806010e0f010309020d030507030f08010302130209010e 84
    0x407441e1414020a03403004002d4142c402c0c050550141960700d400c481a00644030001c103480c8010440030b038140c2d840c8615a5080341d03841d80a0280c480400c0c02100988a0ae8814410115001003816102e0700364140007402e41c81409900803003407213050130000689114000a40360f41c1d580b122040c0403007110120503800105441c00c80d00d548001c10228a040d42c0c00c4134442d8485801c600d40300c5d80c840d002d6403203600483d40011418000a00441c40005003894040c60240000800300c0f02922001160802600701e0019403480c10419002400c041003180d20030030a90600308043d6085c81c19644603881584805020842005174035120100291300c003003441d50002c0b008654440da2001c1c1c011000002c040f80030070318061080c0e046881d9005614803445000d0580d00d800313400741103000300b041102c2c0d904050740c10541e13141c1032880140c0701c5520f103000c0c090203a116070307407940d503d031900900d11180d00c802d038030070030580744010001616a020591298400c100c0b002d038803050b0f9000101d4200301200c0d00958 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 52363133 1250 52361883 52361893
    0x8010504030f020f030c0607080703020c0601030c1809050601050607020315070e121606030e0304050301020d0902090105181b0906030a0b0a050301060308030f1512060f06090106021507020708 84
    0x806400c01d00c12240d6001c2c54094640040e000400e0640342e000312282c410f1650009400280d101344207110450380580181001070a1039040c000b240d14204090f0001c503540541c044007488000000c07101000b410080c0c82086c03142241940e80d49442d81e10600c503207802000e0102d5070004541c0c1c14454400d121410840d400d45902e4400c41c01042407481f03207203441c06158070141c20101c0039800329800c840703030001e021498007035881e100f01100205070800901300076020520003ca00c0e59001c2c0000c0c11a040244030100d049542401000300654042e07104622690340400d006e0161050740c10502c0c1d105400002c20880c40310241c9030301342544101c1280640c440000820040d00c88980d81c058007559800b550400640382d254405c0c10b0888034180409858200b092000401500c820000c80358090b1070003a04446402814000c2032034002c44003650743c21500300000b080f03140c03503540b50650f60040b011183c44455500d08040691108802810080841801800100010300810201000f4903180080390 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 52364383 1250 52363133 52363141
    0x3080d0b060a03140f091f110f031e09150a1b02030c0610060c15060518040b13020607110d02030f030408010506060301061b05010f09060603030201050618010915080105 74
    0x3d00401a134008003c141d000000440d090355030880b00c440c419098080104070081d800016010440c56403440c84420f581c4a03891441a14120f00151074010041d0440d03540380e0411007041410311707600045958072450389004101204d40000b4036114030a080d180740440940702d0480d442c1c0030300900100c81000c9140d041e005032007103a00100420121004500b550700da41c88100d9945802e1500b0b1041c04c0000e1002100e9030042032060030400a2030408140000e8580d5583c0040f0f1808007840750790180b2600c0c0c010070042804600040b50f81d002ca02d41041009041096000030f10394011988054403000040902c40d01b1070300c0e0321120301940d640041c04c881c02c082100341002d9581e131141c020504c165080c0301c00318819081000c1a203040ea820364171081c500030540d808507072404d6200082a20b20f5903c9500c00749078540c040c4580040a0b00170000490101d080d800c000c0d00f51400038000d98021f40d0012480b000b02582c150010b070540b04800000318510020200f510840040c1c5d4000c0d1503135510703101c180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 52365633 1250 52364383 52364387
    0x509031501090b030a030f11100c050304021302030108030a08060f0d050c19031109091609060608130f0209090111031008120a0203040b0d06090905010b032503080d0b060a 75
    0x1441c101c0d08200303801c2c08240324090074551244107806000740450711100070040b441d4014960700800020403812200c04291181d40c02c8162003010030410040b0304000284015410061000340714a40307016810742c0b842d45410300c0641d41e441150400c0040012190100d0b40c2691070403c0003d031803400030414925940a414a2a260025014418458012000360704007040710b00061404aa030404c1141e0300b03104281d810300c0029070008200d58810b000d40400b10340308100341c443d403001070701e000790b00000c2d098184100031386080e00180c82c05000b20504c8242ca00010442c1030000c550590542d1004103c0c2c0307503156150702518050040440341200801001000c481d014410400c850241e4211030a86c011400704070010300c106a40200144c0080005000a109001c02400c0082c175a00c0001401991001d00780308441410718200c8080e5100c00600180d032a08120200c2e04201082d01d05c07144419101800a0306082ca1000a14500001c9030514a41b02c55074451520100044d002c039a0700c241034980 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 52366883 1250 52365633 52365673
    0x406050109050109061d0702031306050702101719060503100b0a0605030603030a0305060d0804031203061509050103091a040804030b07020303041208180d020d020c150306010c03050903 81
    0x9207100d814a030900006040c2e44c0d601510084881c3e5500c8841c403e1001c82500b401030000a042809500c810050550021402d9181100510459440d10f844400910410143d01090402c0790108062155940b00800c0c4521405070442c1c04002020110440f407074502c0094040c1e58032295041c0214900b0b84001c0300142c00c6455611403c80d000c3c27040c02c2c5c94900980716400180c9803030ba0164028003084407101e000ba8006500301c48004d00c1d034504518580d071181c44e0b544c46908102d6900b010b4610b80300e20140c00d80146000303030405120704000d00104c03100c0102011b0b0700d4420641015201e03501c450600c0b5810407110580042845042030b146030505046111350320a00c400c82e49203c03641c00040c0074070300c0481a40d02440e80520507500f4040000301c1111746281c00787c61980c08030040080e541038000d04014003140e848440c4c0103060740d59003030800681450f640c451824000e04600380c010444940d8681282d910030024200002c0d00511400c00f200c03203004500e115030300b6215107104800c0c02c20f07031880 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 52368133 1250 52366883 52366889
    0x3030f0608030a1202030c0403020618030703030f0201050603011e02070602040e071107120c091d16051809060406020a12020c030702090a140a0f02090301020d0e0d08090d0e0406050904060501 84
    0x869000074020070b102c1004070f00c0210707400b030007d08050005000629103c001004d07840314514001c0744503004d601c00a41017110962040340810008040c0720900e580a00030142c0c8040110000c0161001000020081140101c3d4440b586030340043c04404020195041e24081c140300c400040042c9001d01000d00f482c864254940b2140c403806800281c49510b0707001c0146525401103100d80703254a441c1c610005000100e40561132003008220052075050708000c1042d1030780c0150410101c0d01d18000074000c8001407060900b4880140310100016a46c00040454015500c140016a0b802218104880341604072002c5054031b0300000ea00000500d000000d00344182c02219074651545400390140300315a217071285058880300110000ea50640d45520045d901140890301500d840c40e800006802c83c1e001050b0785c0041595080103040c2e20380208a05240e080070341c00c10b46080e0403e0b2048603a604040c1000104005d80c001c0b6070301464a8940001c002001e0107050a400750806180c031038042c0400740 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 52369383 1250 52368133 52368137
    0x90112060b1201230105090f061204060609090515090a05070608010602010c0507032c040e010501090c0e130b01020304030f060b010e01020714010c0f020d050a17121303030f0608030a 80
    0x105080c40d0841c4000d1881907000004d01c800700090740103460b940c00c180308066000070b00e500121215101d040040c8080031040707071650300078507140c03502c0801c8440903002810740a150815401c002038001960105011070440310070480e64903003203102d00c0c0404541d0024040c1c01070401c00a201031308170034028180d9240707400a200c520184142120f0b1409103140182c0007401c0300c980e95144560700b2030141804002c860041750031801202c04034050300c0f0300c0c0082e010142e541d103004101200703c0d8811035002c10310600d05200c0c400103820004103d2404c4603445d4141d50b50750b203100ea40d141c0c000c00480d00115400404410251440d080c144010300300049914081001200188103e610208000082d540781204a8410100300e40044808000c0341e5400c5400201010030301c805640c50181c0000303218444e500030140c1c407240340362400d4400d0014956034213403181404a50403000041c00ca403640448442c1188801e201300e420102d000d08000d50803010740900d81040840c01c6031011000f800700180b59 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 52370633 1250 52369383 52369417
    0x61005010807050319110a0207052b15090203011e1a060414010e060403260f040902030a0b09010e16020601080309040b0315010603090b0105090708040206090112060b 73
    0x8000650304203070100d541000046041001030441513548402c9040d0001841c0c0c00240f1140800c0d42c1c0c00301c0d40c03158910700c0141e440b04100b003004d860b080c3c010413003110001010004003600b200c0241040c89a400c0020320b050710106848415a505621251540350000c00900181d80301884020741c0c5540108805019401c1021700c81c001c1d8042190000740c00800f07403903585814a8101c07490707500c02441c070109041200301000c0401c160b48000142020310701038420a82c458480c084041002c8585e181f211100250a000496545640d0002e9078102c5010180251750703a0b550701c01d00d02c000d00301c1e00d9105900c44003660020409840c0c800d4032620070030030305e40284110f070860581640e0301c000921032038000d50720130001c8010604241c0c105448449015040318840d00d0b40810300e031440c4400b608400c002960700c00012083c0071541a4860040000b55201d003480e081400c0f000b0850b030b40041019004003070006180800b80d220310422032607050000400c000458076161070422a81c01401d40502039650 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 52371883 1250 52370633 52370639
    0xa0504021b150a1404050d030c0207050a09021b06040c0b130e0a0b01030f3b0303040510060902190807050912030408060a05130b060103090c0b130b0f090d060605120610 74
    0x2008040c90050340c108000f0300350301f0030452040f8003600174621044110301800400145d661124160134028001050700940c540c0c20313050002603000c13070b081c8540341694040828840801d150004540c02d481d040720b440fa43c0d401001d02200e032010040c1d80143c800d090b040d010070055003441e900c82aa444002d03038003806504007240d004010746840d1704114a070386500c0c000c4040111002c0a18001c2408011045541c6002e600303222421034004803401e84168010306020304600c1c09a00c41d040160141b02811400d1031610181d4010301c0e603141090700280901d0348003040c5520f004000355a0080c070010040840c80c01c43d114400d490390400e100d010303540d02c03a050200301140064020341d4841c3c02c48240782421118152038103000380f10041e1426050655640e00440410400300a190142041c1c118661340c803020419240c81504143d400032100103c21321030b55140022480c03c99080035421103409854a0030f0381410740c000c201d25800300741e1082c601c50380111021004220340e40308820704d100030b43d840c0365 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 52373133 1250 52371883 52371911
    0x8010e0d020c0109050402030a090602160b060306041208060103090212070303080105060c0303060d0f0b040b04050c01140409020d0b0d0b011a07030203040501110f0a0302060916050a0504021b150a 86
    0x4080c8120318007203904c6040a001d02c0c20668042d41d1702a910010100340518141c40300030032640400d01f03d00c01c071b143c6190028240480e6000b0940c10160680060100e0b280c946c441a1400f00e4003003001082000d008040b0300749038440e4100803841600100014a000c0c14400d0b059170b80c000c0f9120841c04140001e000080c0c520b42101544c115802c3d01000e1480c0d60750340410044150a126005c460f401c44095000303010a03001500316100742c0c17081510705020308040c1400f91034124280704a40c104a610814000d4075600f05041d01c04450705124007584070200c421425029015800b45141c1184c0e03052440824000300310f00190486e20012186040c440a90714485441d100d100400b501581c4100000c2245520172400c0354005550f09007610604610400c0f414100200741100340c4c0103901c06000c0c030581440a00c0000c0c40d00c0c3e241140e000c002c0c4c0c1f601010500100c0c291040ba480f50380c0c00300f1010701c0c641085690b01c450825080075181021400604250040021364141d40450b1030b00012100c024 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 52374383 1250 52373133 52373143
    0xa120207020f01050c03040306050109060e0a0c0905010320030c0d0606090e07050d09050d12050606130b0c150115032909060402040f091b080c0415021608010e0d02 72
    0x10360090700c8001121200310044d02e440e4400d035a03108881c401004000040784961040502030051004007146e418600401505021400b50070052401d1400c4803c0c55201d4100c0b801d00225a402e0801040110318000400d0f00e00c1000380f24103c0b40c803000000c0040300c4014000500100b01894010060aa26140d044504a60500034905541401000700d03d1060103074020f07040421a101c070210701401d56075a07007424000250145000b1400307180409500031203501130203911941c29900d40b82081845503118032030f40d1491140d00309020300003800c0030f40ca0f0b000340000c07400520b050280380010f580d1120303401008022003c9000c00a80b0340402c8001403003051011252480e15040c804840200d908204070300d00e40080c2500d640960300300000108120310b4071105009200207000011002484011841400040381d0a941000100c10030440400500019502070350340e40c1c1d081250b00f1610400680c909008460100700644106400040c0c0c0c0205410800c440c2c241c1400399001240b14030b000381e80c1c1c2e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 52375633 1250 52374383 52374397
    0x5060108060408040911040312020312060f031902040f050f10081203071b02100e091806040b04030306030203120309010e0d02030a030e0304090515031513030c0204200a1202 76
    0x44281003000300044075240e004040b500048450386e91078280d0700d0340c0c0e4001d000c8210721a1000b503040403c2021a5400e00c1d41619071000040e506126041d208900081d00c4d21215282600c1c1e40b07000e950000190b485562005001c01d00301317401040b050409030f64510742c8030011105252880c40c2800c022034080300104100410541841195045031140f040035540c512071580401160000440250b0140e664003001e04603012503601c0b030181d400e01c010140565442d00504100746d40c81c0c11005000c02c02800a14680d006811919451841e195460214081d00c0c031a88041c0d8144528440d03980d203000c004000703500420411008000340c1c00031b80440c5071110428208a40981c0040c001400c1581c082d4024840b1840d81034156854661526127510484900b41c0c1c2003000c40c09110096241420104035a031000200c1f45c15500c0f140ca455540e15240e0802060f0003010414100f06040454559030002c07046400b171a96520b92142240d440301c0203a0700b160340602d0008841019a140b42001442101c1103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 52376883 1250 52375633 52375643
    0x20321220320030d09030816050403050601061b0c03050c1201140f060111100f060e040b060402071e110906010c0305040b0f2a070b0412140f030f07050601080604 71
    0xd90b500480b9100c80420420552040c0e0f404100401d04001086100f4601428825241c0e0f0490b81080c154110f00d01e10160b1042d030a01004200070302c0032490005545044448601c1d0100d5020b15034081c0c0b1444242d000740041482e44158008000c1000101da099406032003503900400d500c0c04032150700d09984c001d12103124040300990215041c07500c883e44c456407112041c1480482d604210081c14500b0440c4403041e030b40c00341c0d03500c0a10501c1e03440e0300921005101c06101c401050500d9190400e54150140965200c0c590014a09041201510030b03480c51418110b8454401c0c1003a09000c007860b0f031441d03452440350b00c96500107100c540c01140ba00710103540665034281018201200c000403507200c4110302482305400d21022041e40072400341d21840001c00c46641d46421400c10041e482d00360b080c0c1100b0240d810a10003441001d100310743d52a0034130340001c13510040713008141d000c504141c9016003980c0180800901070354030f00c004100800615115804a8006a07130301c820040d2514010b84004103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 52378133 1250 52376883 52376897
    0xf010507030b0d0b0a020f12061302040305030a110c06040e0a0e0304140f0301020903010c0210150b0304060207060609060609080c03070815040314040e01030b0f04210203212203 78
    0x403440488000303174400a00180145844d010740c200090302d4201860010001c0300c0442040000d0820b40007040d030b09000648103504280c290ba88868490046011800811540c2070302d04078501c004000540c010030020702480e03a41d545400080000540440c1d039202e5a40c00e103018060b0090340002200c04a03105100c2c5200c001001104008070804c0e20004a54150b4003401010304079038080c880c235001e14501c1e1b00205000b05001880000740d032022042802800d0002c40100580d410480c11070368007607400640142d4489081ca0054018062030700107044980c0f0b411004500c1030b40000c1524240c411284c1182c0460f88944101580e8599601445025130000c415503155949504c0a03607030480d03c0703400d02051000c0e200d09500d03c40c0e000b55106465002c43c0000400078014003505094210112428596145c84c1c130341c40319a60110b00c80d140c10655080004a003030028420710541d402c4c48540314624601e1440407600302000c030740a440c01a426080c0714035890455408000244190740c0c1502e0b01c103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 52379383 1250 52378133 52378159
    0x61d0f030d0209040e0f070e0906060d0807020105070611030a061a0f0708120c0a08150307170118050c0405010f0f09020a03020d020a02010e0f0a030909021303080406020f010507030b 80
    0x10080d40018500c1c0b5000740d1078130300d17120000c48107000d100480d40c81c11000b0706407986414150b141c1100c02500050f020380001d0140407164a88140010403e600401c02a80d148a81e100484440c85600d6001c0c0519150024410381e031118000210b004894200043c05190303251900407c21016060030540003010130018414071400c440e01411085000c1c01205050050384035151a030a0001c80c0c403900c0d0b00c08002003c1e0340403030704100e1040d0040e07030040c61403210381541400300796207280c9800340ca104071600605401019400750440442083e402c030701900c031243e05103000380c0d50340003600403584200d04000012503c030480d0080d81013203c42201c1c000040c0c514203684807000754844a500002c1540030000b150b04880940028449184680d000040520341d00000c20700304042b100e86a00c2030740060f040300d00440d42c00798004055031f01762500180c0c0c50b005400c242204440c0d95100800e840030100e40000d0642e004507004102e01002d42c000d0059954954048041303e03206540c055003d01c3c00c81c460 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 52380633 1250 52379383 52379407
    0x6020d020d080105090709030b07030f0f0b0609040e0705030a11030106060f08070e030118080706050603010c1d0415030b07020610030c030b0603070509150f060921070b0403061d0f03 80
    0x1541c06c40e0300f40c10940f00c0c090721380d11030301c00c0904100c9801000c44d45076680c0c00e020310014850401103102c10701c03040103025200b00021380301d44111008207200d00c0c0c44845191241805000040061900504844c0e0f43c0002c5d00d00b28840c12000a8018400d51030304000142c801e0207001c040724150419540c00509030b555080503248001c0d541e04841d05507580d0b503285004404c0c20410006903074080c00e8020344954452400105940380101058000e0741440f072020451500215202160007142c585c41170070043e404040f0300140b40c01208038460340303a00700000060040a080c12801040c0c20382c2501c929503134100e0000f100c8140c0d4070008000343d10038501003011400c8052029044000203055851983d40c400004045040503210700384c0d2070004844203c2c45180058040c0c5644400b503840d070303081100c400c00042130030103440860039100203900c01c01104d802c3d081c81584081c18000c0301194503140c907401c00c18024480c0416000c01180c181954050703540c400a08000514042d4000714a40000e207042 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 52381883 1250 52380633 52380649
    0x1140c030a02120709090c020c090a090807020405010b0702090a090203030a21060f080c1503040f03090b0c07090506061303080c030c01020c0a11090c040b0703050708031006020d020d080105 83
    0x5046181e6828410800b101040040c10790296030386a07070300c00c1413900340443c0008807011101c1510a548c480358685e0000d0700d907800000e500c828a201300003200305541c100441940306007103000b940a450480042001801d001c00340586038003e070740e000b509a4131000d0b070318110b424032031020707515034001c2c0711641c0d54911502e407042800703401a103015040c03c0141085010f0301c6c0d80c0d400942c2120202001406940b1082102000d14003040314040515200071281e06c0180c8030291000e041d0400e0325090509260041070898000c04420008035501e030103c052090302c40c0441d014a240d43d5061074081203080c075011091300c1000c0010114811524030310742c0d43d04910340c4994407003a17090106021000144c4001c2c03019011000010015008070480d500e411281c2c4650013080714410300415041c028142d07a030a0a817010360384075188150307036140070f4101030300c00c0e01407420000c21003140001000706c1e90400f000610200c510503002c85429005608069880f4010b4141581c00580c039400104040d152040c6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 52383133 1250 52381883 52381891
    0x702090402040b300c06030a0c05120103080315010c02090609060a1503090501050705210402010c020a03080c1203060f0108040f06020301080f07060903080313111905040e01140c03 79
    0x880040d000c1202000b103000101e4204900d00350700c1c00c0304626500c2c424001c0c20001250420760191170001800300c0081d025000203024101e0b40b43d520305a03145418080c0703045542d540486681082c4541e503900d041501079000b00c0ea464080301c18484c45000341e501038100648900d81c010b151a145941d850203121070700d180284140d41c0308100d00800210402c0b540c40e10122071180f0b98000c10004401d0504a00b52440a0280d40c00c204003040031041904002d1144d012007981c0303030030101850301c8900040f9004030f124400070390b000024400000801195000818851510f074080c1d82107050242d220f00800d0000701e44050f0004bd02018501241d031007550610751140c131401810100b0181600e0f200205d8200f40c0060b03a40380d104a0340301c100903500b044400024107861030440b8609065590b4500c40c0e0002410110925000c1c002030802c224100d00560400784016060b06020300c010000a04d06690074490305020358030f1b040c85044100c1040c0240d451265242c52040c42e00c0e100c9106a003401d5000034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 52384383 1250 52383133 52383139
    0x30f030c080408090a030b090f1c080402010f03060f06050706050a0903051b030c010f05010f15140c1906020a090e0103020d1416090614030f07090b030309030f030315030307080702090402 82
    0x189010001403c41e80004e40107a00648c0200021080001218a45103580141c51001c52001aa040c1d00503880300e1080d0340181e0a1a086461803640d5609502802c6260040a0040300c41c24001c100c10340d00001402d10140121b0050020f601d611000310222102042e000e00000d008000045541c614403e85015071701c0c1c00b104507403800b0003218406003100c0000c000c01c44415200c0c801001089680398542001c0d04142240c00425085114058580d80441c008140914070102d440e14540e034050204082004540706850340003051490104001d500c00c80b03070350380440d4031800c01050320f60b40c542c0b10030705890f07018044c1c83c4001100e40380e000381c00040c42600d002c03901c5212140e203644119030717210704010305003140007059181c1001a280b0b07405039440700d030601940c44050101c0483c800014410112031250b8000034500c5400030100c9d04600c18050415007500c6118412203580302d00000035482650311107408101d0044040816440b40305240014000000c00d010300b8001d442c2441038550064402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 52385633 1250 52384383 52384399
    0x30e151206040c0c0c0b030103060b010807020309130902060703021c02010c1b0606120501060e07030e03070201110c1008190204030f06050604060504050a0504060c0801051507060204031e030f030c08040809 90
    0x103a4906002c3c032070304e8000d46c144650200c010800c200d054000c00d101c0601c2403d0069a40c606004020740c1c80c040c0721483c40c818103003904040d00105265000741c590300e401802c855a244064200a559200d54200215092803010001503450b441171040f005143c01d255501044c030145900c0c0d40102c51801d43e01510219a40d0100081d0700a8196801e003c407485500003150440c40c041a4450860340140100706243c1040103102940070044211070503180c0c2420503030b62041030f281c52180380c0840b14680c2e50304200200710394071109400c0310f0914400d912514014a04501241208041e405144001442485c170550500b0003c0c0043d00000d60289010340000b459a0b0390703600050640b0b00944042c1c028503560402c0c841889000d0042a00503807031070400780100e501d050080b910341862840031020698001c90081c0c1080728503011a40255003010805507002039100186034521003851080300800c0312040221032407802400750300c24183c4652106001680c480d1100e803150380c00f1400d420390003408 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 52386883 1250 52385633 52385657
    0x306090c120c08010b0406031a0411130e060c160308091218180108030301060e03010e0f0c03070609080303010608070302070210091701090c05010c050a0c03030e151206040c 76
    0x1e00ca1000c0d03019004440411480d840c050743c036403c5036182c280c0280542d040480c28800b003216098119100e039904d24003201e19903102d040042d00d11583d040125408543d110428403003030303040e40000c4840304000042d1003103038030f0b000c90842507480b5803180d01a6001d002c1100d000860b002d80c40b0b4039440342003402a50306c620080f000d6280c10368001c81c4101d6a5070400d008150440c1003281404850300c412510308100d950500404540e81d020521895040000031103400119031400e4028017540380da120308a50324850810743c40c58441051010880c024031a81200040c09031103030303042d030088036106806149540d003015000c07682c0c500300078021000d158080000c1c40050725562010041d000d0705581d0100c00d182080b014032440d410349401e004c0568181041500400c1402a907801190024240070324000e00a18140781840c480c410081d103082c00b04400081030682002000304050780464141001c7c490090000301c2c42c1c01401c00c46602c20005d40000303041ca04166208440920381c5003085210021 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 52388133 1250 52386883 52386899
    0xa061e080403021c09030b2206110708071104230703090804050d030810082a0109050a03050f01050c030103031e03110a020106051201020f070305030406060b070305030712050705040306090c 83
    0x411081240006445c00070800500892048003070300560345e0b0402d84031000050140c44a9046d100c080503200d60395840d80c41e800e9603002400c5503000e40d804a00161903030014100144103072980d20391540520708014040c0e441c2408216030000b036180e003008a64054031401011401403841d01c0c003c0322400300402001c070b041da851722420311300d19100340d40d4050b081c640703d88201b001c6040b5900c00b1850b9841801d1000720701030300b0344949590a021071013068059103c000101d58210700340d4061908040c05080220a0100c042202c00a90000b14002c1c001c5446d5021410002c2c442484041c00040000e000551103199008180c083c19202d0719001c5031002440141d0062680300461200160795a08030401840c10070089010f044880600218103008014141019903c10000000e00300400000028100185a44801c02900d00d070084a900e4071a2460041d12070342c805d680c40f0000c02c0810351400507490301da0040324400c0e0216a00c0c40c0c01c1c02c0c9580d803080080c202c100f00860b6100e54508011071410 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 52389383 1250 52388133 52388173
    0x2092208030406020a0906020316080f07081b1501050a090203090c040c020a03020c0301020a0206070f090f0905040317060102030409020c0715020d09060809071710090803060a061e08040302 83
    0x80e029441c01659264040400703040a011035100384199042403102540180d40fa84a2b20700c1550000c41c040d960340d00c204641100fa100320714000702068004240007251900c4a00306460711150002280c511410395900495944000d2141552003001c158003070080c02400e401840d046035960b42180c82c00350000000806645020031000010f92003090a0001d26a040084914104095008600c2d0035511300d0004e4a40100400c9001880f00d413841d0700001c544901c0380c030b1004000003240d0481c40c549519141c00a0700003528284d0024440301042088c0400c56280c1a00800058004520f032901e41b894940c081c2d0045542601e80c1c0c002c031100051503002d090b03c0d00c0b0329803c0950180001007940000582803900c50340142c800c1004102c01c0082480c8001440d00958903032400d94007000d280b11041900c0e1080c0d100000360582c3c00c180d8070900300048a805940079040031203407041c20a44542c0c0c115650300d0344000e00e92150911440306103442d0300407048250010702030310660b6022a042100ba500d61 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 52390633 1250 52389383 52389391
    0x10917090301140c090d02010c050f0607080601020c090604050a0609020304050c030d050c060403080604020f0c07170c0d060e0a02120a11120c100203041509051009030209220803 78
    0x80400154508149020f00c0385804040c075210b11008242061038042c145406607086081c09400d5803d1000306580c0141200b2084960103000c0700c060014825403561030329812f640d01d9011444680108a0b0703580040754070804020050700707104c0b680d52140b04100150001a0040038111754130000824041014002140b00301d002e00c00900a0140340014180751400a541d240200002805491708070180411159041030309450825500e8803442c000070b0080c803d40c2010000c0e5400010006440d48010400c1800c80d0300c0d10020701001c140c0400c000b9183e002c0301044030361140e03240380c4210000c0c8031640401c03c0003945c0e100300c42d4003550b1603001c600301c5150b210049043c2c0d80800010b034204002d00c2030460300c10100b607a9030705403910b201c0700040e600c1c610022114456240841c0311a0003d100300706540041c0482c582c21400c2c1c2d45140c5004c0c1494000b4010a4014504d410710103980c107001c1c20030041140d07405002242245d841548414242581400d02030102041000000c0442d842d40c004d1801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 52391883 1250 52390633 52390673
    0xb1501090902071b0608130f020312190207060801061202030903070c0303020601030b130c05210616080108060615070305040b0708091e0f04090609080d05040309091109040903020109 80
    0x12908544480a4901040785e0010b002c000c0c4600800c06010000c04441180320b07400099a28209107600c002402d1500c041d8490550410124600b03c400203560060800c0700059000d44082070f03181c5601311050a024007032180414001c0100301100017103036000b542c3c070603d2482624100141d03661000951410f0350700c2500147c0c01480144117000304142441d4010f00d80d80e00301c00d401c88d02076880045401c124414a4803038840700302d00f181000c003150002d1400404580660b6050325003002e0f40301060b035284442d075000403001000030501c00000903d490107141d0040440100b5140c8050400159124180840402c8401d100000e444854440035290507481900840d40b150300310424420307200b0140801001120811103000703110b8968000081c2c61850580d0042050010b42c02c007a0050000040000c20030200020f0b00c04080c8147c1c4d20041c003c9110f96241000243d8072001c1c81c06845042400c1a8410320070441102c440c98903501141d8220b00c42d00010403c004951919135040205081d0341032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 52393133 1250 52391883 52391903
    0x40302010509122b0b040903021b010e0d121205101a030f1b090a0803070c0501170a021809160f03090b1602010e03031e0f01030b150109090207 63
    0x2102480621200c030b4104010030340d00d0700300280400c0500c00744e24141d403a8000d845507900720300c01d0380c03030319402003d81075001400038043c441c0c1a00c0c0c000d645402420503e401e140c480250110a90702c280c150451800c2e00400e40420810552950f01d1006207808800703003449960708500d012802c9600074a40f2401c55601c158100300d103004128003c0103d10b40114200400070010001040d40998803140c1142800407861580081040b058000b44a02e00e0101d03071143e011000001d01e464000018a00c0521840c00190350a6981e0019a001c403040c01810f2046075000b000180c00c65101d901800845503401003130300041301d2030310100d0b403012400d41e1100300301d14044120792401608598441070ba20000d260410000b21603490b13082c030008020f440805124486c4c81d24218440c400d4020003521408030b0140e035981d080c918181c40440781c48902d0580050300c0080021000400e24040320304172508210034407038554414808002d20858026094148181140f0104003070000784003504042d4405c0e80d00035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 52394383 1250 52393133 52393141
    0x9010f03050c061c1a031b040f020406080103030f05090d0302030702150a05090d0614070903110402070b0a02090103061505040623190201090812011d040507050f0102030f030403020105 81
    0x10b0400300040840d0740560030030868480004000315051030305142c00c800004590000d150b0101d60713aa00c0e18002d5515100d00d0015a0700c900702542c0041d0045e800b15020403400d0302032200c000590147d03208003008288030074010030200e80101c40c0c0200b40c501500c0e0091600703142800103840f82080003030650040c1d20201d00341c411410200840c00340540110000c0d4107210803204014900c0c030072580c2490180c42040e0511040200641210030800c1c20510610100e01c1c003071000901e003908620003034510400e0201c00100300d0800e4030031209256000104808150342d445c0020000e58440e8034a00c0c1016580ea0340040e409510940366000516550f68450341e60f40b80000c000c000008250340500403001510070406d041c854503040301c008804501243c090001407103010390044c02023140144c0541c000203845440424680c5895050b03c1300c603e0180003004400500c0310008404450041c05a446140c0501862070500b121100a400520480e49046900c6101c840142c00039202100580e460724140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 52395633 1250 52394383 52394393
    0x120a082209050f060d0b160504090e0f070b0301120201110f0109060e010c0305060901030b07050c0304060201060509010902070221070305030d0603020a060507120e1309050c040b0a052101020909010f03 88
    0x3c29042501115400c011a07010303114241c24100203800c100903040c15114120007280180d00791401450406001c1000345d44a902c45a104c402c102c4900355603000712807010503510303522020b503410f032552420300050104103680156420b040b10700b00001306118507048018002c100b4016030458521480300414031441710450785095452017441c04042c541800d0030004a0740301d04c0c804504590b0440051281364860b50300940713681c482c060031401180000100170036a10b405400450460304255042100341e070b41c0f61103013400c03030095074402544100e00e040d20002c046c000d40c0021204140d18400d42d04520380c0c950300c6520310343c0b005102c82c250326103070b440c20405d41c41c1c00c0407944002d220900340303507250504d5a43c0702c1800d101150110000e00400c1142c038207198440540c0c0c00288001581d081004089600b00139030b0751b0303100d41c0c075a42c4141d0910000d0606418540c21b008110b40c4050900440f28601d0280240381c00040700444407650750174040f401d1207a80d074071500da00a00e0b6103410214058214201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 52396883 1250 52395633 52395661
    0xb04050604090503030f1003020a03080a1e0f0e0102010b0607060f0605030303010627050d0b09010b040606021f020d05010b13060c150c0e0a0807090506120a08220905 73
    0xc000c0c8194502079060300800c9011040f0f80d0f1042d1032900740340440da00d251890f0080c03005504065003011501101008100c0f1500c010000e103075480d19001500d202000042c1c188284c1010504005000195503c132410300400c164915210305000100d43d003414035002c121607030032081c0180e035030903116407080d0500481445035038060306041e8041e501c0c540c140031010303142c1040e41441d10326032515034152480c52001085000058007000b00070403100d101d0b1f41803100881d602510b10000380d519117a280038607454644520750848801d50090003a0041d010f07800c07544100501000081c0c00d400300891481e14045101d040e02a1814100880c3c55869142c0c1440e000d00700d80c0c00c030409012150034010b020848500d440301e01d0f8220000085035503400c070702d000c650b903048031004603030043c880d04804900300030049410300c1a0743d1140b4081185503244001c01581844004070041d01d07400c400c40348008546200300400b499405211081c01046000c17844070700b4003100d5444100710a40c0d404c1800480500c81030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 52398133 1250 52396883 52396891
    0x3020904180c120510050406051f14040e12070c0614040e01120201020309100f030c0e1003020c0307120804060b2d030a05070909020f01140f03060a0e0a0b0405 70
    0x30141c140c8469a500390056031a01401030918000d2203210100031040181404011100c01c0c140168109031401c2c101a00040d40d203007922600c20081e50342d80c1031400400c801103503044280b0048408aa0040c4801003800302c0b4201401e005081904828511600042a0242c41001d240013900c0c90034200034502a0300786400f0035240303002c0000b0803040f43c01ca182c050548002e9600d9211201140c40180d00d540b26045025412401d84203540c0e200c16001030248144214644090044401a110407640c1c401d101c80d032550702900c4445003961141c400e070f0107044912a00d108491400003183c41d0000702e0984018250001034400e8200f204000c100d014100c2e0501e0151500c2c8030b085049111000101401901003442202e4420341c101d10307650420170740351360703d82000c1034a180ba03032902140340c081c0c44c820000741d029101e10350340c40c01d055125000d2844081e03854542c1608048640e0a03040c038a6201420103a80705e03005c2400815081714051390180a9200700d40c0004041d441c0d80c044c0010386500038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 52399383 1250 52398133 52398161
    0x915060e070f0e0f03150103061d03070b07090806130309060c021c030912050708010b01020c061902070e07030e0105010603110906070c03050304060f110102070201171008060703020904 81
    0x3400340070203641c00049210b0340d040c0500f45880303024031603008030342911001c10342d0540c944a0880300400441405400c0360599008000c1030000d00000500604099084c50385001c140d4010040704000c41c0f0400140c1e078004025140c030200050341e881b9468640b80b42520403901100c011031b5610101a0070807580c0c0000c0010703007411641840b181e000103000f18059144004d003142c9040320001050311a00e24440905424603510b00945928200b66581d01c8943c000c0c60303c1c56281c0038500c0c074198000902508680e030024440c80c50801500102d41606c941104d860701580f14405010907008884a0100d1140740c080c0e400080c00c020f5181d41c5400c0d41c006901c090140361030302c032158181d00c1070101101d0100c1c2080d41c5060750f881607880e1850740d5003140e41c4080c14a01012030301103000d99004e8400c140c0c10305159600800e070104070751001d080f440380400090208817841049140403070303800c3d10f00303600521a5113101100d07507079a4101c905184c8100c4070307500042c0c3c0c0050481c2051610b440b51a0022100ca = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 52400633 1250 52399383 52399409
    0x906050c0a02240106030903140307020c040605090f131104050a0c180308040b091f17010b0c06040f02010e0301320f010504052505030a05060402030403020a0803060f04091506 77
    0x60b2003001016081030044100301a03c648a1f03005141c040c400c41c030000c604804d00155646400f5030000c0d100d10403541c4540c8554141000040c084ca0f1659070b0502841454203031410301d0710303002c8011401c1c00308140119030008003541c00c22000c5c0c0c1c892141d64800e140c14080415001e18015000302402418940302c035403011040c03414404522540140c409803024401616540c2c41c0640020345061201c640b00d0352044003008024000c15809600d50020249000381002c441c0d80340d080b50000d03802034819405044e484180010086034800b5041c41c4228010305004100390044401300e0309460340401d0303c820380c4403d041210b122080c3c1c00b0312542003c458408501ca24100781c59915002d8806100b00d511454950010420485a880c80c401207000c81d044504c1c500c0307901d0080900326400403542a0340e010320f2b282c0040d40a04040c001c4a10982d81030b0301920202c01c05543e00d4400790406058039030800107284004c0c4a58031944103940429000c0d119000c0861074a54038001500c81e10380090809440d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 52401883 1250 52400633 52400683
    0x1050403020a080a1107030f0c0501080115120b040e0a14120316140d0b0102060a060b091018090905060a06080d11010207230c030106060203070201120906050c0a02 72
    0x10220310701c941d0760f60246080c0d0b40c6010031901220480b01000100119004140b00081000032003000081346070b05c1060040c8909a88100646600c18244034915480368107a502c076a046100c3c010107285184a11070025140200381c000ca411240c030031189070030315480641c661041c030003203500010001d003419000300103144521145041030700014007101c040005512180799200d00558650580c1c44000070107e1300c40710751544000c007420030011281e001d0302130b8401181c0b451019014041c10f0b54042040c9a20b0101001c05000000000f40c038907008115140d04240c512a10081001d00100f90802002c10103010506210b07081a0016003004051480c000080010307020203d66881e00b03026500307101e0b8554841b103810030b000e0b10910b01c00a00035001c4146101c03560b0011400092048016812501041d15000500d4200c62709402580056400bd1001e0001513120f048840c1a5800b5000e0120b18101d140e40d580f4156101030794903c0201c0008141c0030882a0304016024400c0c1c0c2c4541c2075403140f44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 52403133 1250 52401883 52401887
    0xc02070f030f14011a0618030f03030103030f0f0807050c121b071e12110907200106030c09090602070803040c030314090604030807050313030c0609060203090f1215250201050403 78
    0x201264446c010721020030342e8100c072184035180001c1d42001806a482c0000000921074880c0c1c0240011408220061b1041010622072492070108071450f807208043c03511100700c1031340d60350000f440c6140144501c10f1000c6841450001034100c040440302c008017200e00c88400641441200d40203c02810303848000d8605941801040708100c41e40e00104a40003032207810000001814078503c1c640003ca220180201e440c1c0c0810000502c6102d038062440c0c07082002c1801d8262581840041c0985410318420710071359040f644000a80e901c076400051510007541c1da00b12103500111030940e00b03e00507800c01c01c1803581061112100034003003101c051600c1e00712000641c26018500019081910108400c400c2040030002c607202c0c400c0c05440f01c000a99686000807d007007850054900190324080c1c0014031900000a4803020350000b44140341c990000802d1180302034036089406100c1c455074082c00ca81f00e00141105016210740898034a440d2825000300b0b007804001001c031000c40e890001004003080d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 52404383 1250 52403133 52403171
    0x20f100b030a020103020310091103101203020606090903040801050c04090b010f14070312020711040c03060501080408070f0c0603020304120903020105160809030f0318030f030301090c02070f030f1401 88
    0x40c3d42401c0050316038071002a01d440700021034101405c0780f4607100c180054070001740b003e10320a08208102e92426904c401d80c1150404a014004001d0fa02c26400b150031071514400c83c0b46c1c02204442242d0502e6903400c1010700b9100c0558100340d1616000600f441109522300501030b0802c000e080c8000305001c4c8440083c406101c0d1000701c00e00c1300e008035100c030815100d02c0e62209504401d4005540320340351410008a000f21004000d0701c181d2902d4403082006020f8020681100c0050311010540d688a4a800c280742d48001000c440140f000d101d003000203100000500080c10080e40c0068803440e05282080307910803a5a10101404542041000142e0b404021078a0000c129070134003000019034641a20540140d05000e680350081030710408121000202410414161201ca1044421a1014507490b80d98001000009403c00c000611007911690450300380303000740d0701c111025907a55500204075a00c0581049515400861240080c040552641a41031080d0b0000300084c451241900c8091 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 52405633 1250 52404383 52404403
    0x50d0302030604061511100515010c0206190906090807030c061110021809010f06050901050307050904091103010c03050f01060309050c030105010f0e09030405060a030921020f100b03 80
    0x950000005402d035101c2d6040354005080c80e000085600c100d90703001030954080c4080d80c40751489622404180d08006001e0940203072800c02c17040710300c1e03180e42004440d001c51808040e60880810022243c130245007046480fa03980035035546489007414280e00905905440d80800030300e0788640c0c1c09001162400350310780e08540b1182000b1031024202041607060940b41030034016940d1012a44c510301c031907040f135512013802e000c1300d11b40d1007683c88181700314101c126406485c000803403e000241e0f942d4021402507401140c80d01b0a1400d090100b0000b8040d1503212804031400c0181088a042d01d040034090224001c019060500c03142ca4a000300b0b900d81c0e03805104007402c040d11740d4424024400184044640c80402600034001907071600e01e46e0002d8000ea02c0744078105a4048002451442d020003560140c0308000d26403490030313058000c110080c0107c13980940c1c2500d41604c50000c03010078030f0000300600384640c000e855000d440008080c248555022800c182500b0982d1041d1103507000300750003402d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 52406883 1250 52405633 52405637
    0x9080c030312070216031b0b04151b0b01030819080f06101709030a09050105070c1a09030105070c020310060f09050a02120109020d1a0904171908090c0d050d 69
    0x501d80d00c01208901c0e00c0011740d49100700000d4203001100303210700c44060350300e51860050190a42a503540100215129511510049181c640411110a84258601c104042002083e50106005526040d0323218501f070b03100b224003050001706c5001d2216500b0010440001904010700546032010714480c5841d00180305510850000b444d941640d401040ca1a010000d1640d114181d46132444426560b079014804d1a40030460030030300002c03250700c10301c2141c00c0d0590105c16500e0180c900348180c0155441102c0c000b84040c0140803d8400c0d480900c03555110700140d9030303081d0704101940141401e2a042d02c40781801c607402d2080038800702c40c403120004100c8540c0e43c4001190341d94029030304000d0180f001d100d804a110310000041026454025001403035141100b0840090050142109484240c0141790084c00c0613001a01003119202c004504078074071041ca9182c03070072000c1c580342800260340f10000070581c000c00380488040200000c488100040d503802c49a08030700e403034030b41d40c4003415108601 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 52408133 1250 52406883 52406917
    0x215120606161113060807050a05060a021e1e031308010605010c1103070819050709050708010918020a09020c100501031e0309050907050c06060405060604090b0114040305010501030309080c0303 85
    0x1c0743c407040349480111140131030402585840350082521204c00740704240c8a036005150118051800710200c4040e16610b400804400501c040c031400344000c0302d070382c24215004968801004407503c0419199845845000e1070340c80810002c81e103424082d43d081102240e01d004000d00043c0d030401089000140c0000044255001c01c43c0003a1900400f90801c1e201c50054004034010b90042d209005081da102c0d6058509141d180e070203c030704a13035003203448100080005004011002c0568000301c0781004000811800714400d4001c2803010740c556016079a8607900164500082401b80001c044010755500107005030751440e2191400d510380360898540704110040e015041501071100440107105c0030b81400e00fa4940650044c0c0180c00012046031180113030000106d8525051040c2449010b0050220b42000e05010400c401001c1c0d03003500c54103008884004101030403154000e00011882840049115070652030020300034000e65000c00025405041c00c0610340e680841596180ca50140340d401c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 52409383 1250 52408133 52408163
    0x70513020f07020604060f08090a050d080a1506080a0b06030c090f0a12030f030c0206190e010b03031b010e060f0c07030e04140603070501090617060a03021512060616 73
    0x1261441038000080d40704d03000060003c0c800350044e0940f00d111035142c89001c035941d501005030340c03506106103004101d078005503068159640581285a0003807643d1900256074480b1710180d00c05c031030503500b102000c1040802080180e499074040c01c031034541e00365106801d40c14560b1120295018560b001881618001c400d940c07a521414002001404900c21007940d1030424203000d046000d8400320b02000a08001c2504050340c00003554502880881c4410040c3c0300c110202e2034002c10b142c942d03c10881d52105100c2c81e003035070700700003510042440c0141c0400000b41d903011142160b201428000352a000360080088040e4101111907000d00326868040c0c0d2452540f0f002c540b03d0131031154980d4094907000400300c070842440103107881242c05804450540351140c005564403042c034403030340c0000b510840b00345143c5403095000c1c503004a00544202104c47c0c03a61f000913105403418010001c1e4034400308106112172440c130410398010600b919154506a00600809001703490203601038002130403034001c9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 52410633 1250 52409383 52409407
    0x5030a020f0c1005040c09020a1e050c010e0f0f061603020c0c060d0b090711190f0506010806190c0c03111e01020a08060402031015050405090a140907051302 69
    0x50b0080c4070b2107829101043e10001ca408001d15080e101503501d21a40040414a9030303480c0708480c203950458070b50712002c410000645403007800c0f10390940c040000521041c54805024040c4480903c03843c0080d141c103140303142482c2e181000300d41220003607920040910804c54600644003d035190300d86070243e560010030440901d41801904d0940d0072240c005410310080c240359000b0003126008484065550720780c0e01c0b00b00d1394100011264201600045400301d0802d10000c54544414851a00c0601056160f15141c0c105982607020f107070940c01480400030111000c800000700141c446c24100941c01d1402001007100c032000c4070080078040d2290207840035910812501c0054107840940004000d42d05900780c0c040d4001122640201d403000c2c01095140c90a402641d01c101c02140c203080409203420489100a500d03100c0910900400b000080344944820006501c2a00908030104800c014030003260b008030b030001e00155442d00915414001a42c03416030b00c4000c5204200096181d5175040c00f2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 52411883 1250 52410633 52410637
    0x1b03080621120309010b0307050907050c0a060501031103070f18051e090304170c06070609080f03070306030215030403020a08090112060305060105010306170c21060405010e1006030305030a020f 85
    0x100d040d407807256502d04020a004000110720075103c0c00000e104102d00321042c1562a09940102c6903ca50f0810000e445507100d00050320500080c8811910081090744800c01183d00a0704107844468071f1700480242030904100c008002e0003031840c8000c070307145081c01e040300b0848061062264191108003003101c2c41031500030007108010200703403180c0c2030402604071aa81c4d400344c0704103d01207034003550180000e18089015900f000c80680003515040161741d40e08002c0c00341c00c104450303090041c03200581e10340300070b0017440c4075400715140003451500714010406007105000d01340000090030810003001039400f04050a031a5442502c00d0340724003c1030010703911120faa100f5030003071600d040d20010030f000002a01e18100d8000781c130100020350316030381c10b00c061b520500110781d0207a22a0b101441c0f1428041c0e856401c008190031364413400e03028a20994140300040d2810748072a9104c58500215010501c92081212810700080110030310316074000d802400020041d40c052640480e40d14241d8000303a003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 52413133 1250 52411883 52411939
    0x705060d0621060501080705031b010c08030703050109050f0915060121060e01080f0a08030901020909011707050105160308060d0b040302070e15060712030608011503031b030806 78
    0x4007104040071100c0300b1080d40650380401d66985040200009585c603000c41c04100f500c81c081d002d0007450b0040200c1c044040200b1802c1410066001e41e24000729001ca400f541c00340c0c0180d6004601545070a4440c415594003406c0f00603000c0041090240c50140016900070079a5541401c0301d1603600c400041e03d0b14408131028034040040050303401c00520080e8070039010b03142511003900722643c8030700b2610b42d1110402c4d041203180e44440c400101145261001e140d00c0390350301d400517142810701800300794503100a07800404110104080504800d00600004014110078640035040c901400f10a0810014440002d0140702e251000b07d4141d460f0141071440340c035005900400242000e2070000d568440500c81d010800000300023041d02d015041c43d000441d40707401411103050401d541c880800030403440d10740c003041c075a50341c000245004080c0a0008002c8050703040d03441652a41c00d000e400b01c62b41203440d000b03122402001100017900080050707080103058070708a800390100211610f01600f104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 52414383 1250 52413133 52413149
    0x9140a09020c03070308011208030f180706030903030b0102010515130e0109080a0f0903030503070f0e0d0503030601120b1507140102030a050121050c040e01021b01020912060103050705060d06 84
    0x14480b001d600c4000000c4c199107100e640c4241c103581e66204a034000ba490703d0030080001900f040401c0c0f0802d10f0500143e0410711712803206401c0e0300f56506036458401035510503c0440c2d1205032312030925070036104110184000780000c0c482d03441c105071300c04071101040e410325100b01080c02c1a101c1c0c254055200342090344140e0000c0140c8149130501100503040112442c0001d0700650782014214481c1000d101206e6041d1110390a5444003201600c0f805c10001c44071040003030340c6158102c0382c0d982c80c00200c2410b000c0c10196540e41410000180000101054940e1072401c051980c1c0319900c54180c0d0564001c0c52194050319082580b416261700e03828030018460035070011082c000092001e510060407030b016042042c03626134101c0d410b201039000c04100646141c000d1004040c8604080c0c026208000c42c0000051030134104e840c036001400e452030414501d030703035001c40c0c2e610950800e01c201030030b05800706000b0452989142d4540307507642c0046c010540210b50100d62010700324219002540644221 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 52415633 1250 52414383 52414387
    0x30210241701020d02040b0304060e0a0b0a0209010e030d09090e010614040b0a0e010306020406030501050f01050306210a03020f100b090703020711090901020702030d0504140d050304030506160f0503060109140a0902 94
    0x3408044c4296001560300780c80e0030f482c040c001000d42f20300013840f1340240e6200c20307807500e29512402003070001c1d0003102c4060705000c08440c0c0c9202681d014800540d200c8101d48500c4000b0303060116010031920280b1003144544c1c540101032040c10007034509100300c0102140c3c0411400e50403004908022581c0d845a01c8019503540003204005250300a841030b146155401c10190785e0300c0c82003008051803400e1b46c50229504201240c81418040110b5401c1c00d61041805c9800d07003954582031520aaa40090340103800c107081410100b00103001044010312000380070311854810340700088580d0340141c03100c0b050503400500705c02000040e00d28222240b90043c03131b44101d890300300d0300300f0301030361140d48220320a00130010584070640c01181a10300b511600040c00d038034903503288248800880e1800f0161400d200501001000980c1049404c0c4200d000b42400e1348903a01c0c2c0500a402c04c000c02c21480e007071100030300c1084110b980c000c0a03141110400348a88100400000102e24150100e4110100c4a400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 52416883 1250 52415633 52415639
    0x1090302070305010e06010b0702060706110d09030806060406051c09020d030801051018060f020c04150503060a020403080f0901031812141204020f1c030210241701020d0204 76
    0x20031200304076400f940092008034028400c65885000034010202d01000130320041c005130401340090700396180f08000016a08800d0401d10b041380e0840c801c6200e8554039140b080d41003550141c4e07019005001512a242003500b040e1b00945030303005012140e0642c89104070350024a96098200421054001d41600100c1030141130003820f100e000d000d524000c40100d10102903080c440c44400040c0c031580c4200321101030815008440038550304104400b144a0318006510598651080c006a41419400140f90340c2c500005d040c101038004003106000c52040c0020004101c1d9101110342d4004180f859564a244400040c0e0040103e905190350615003038054100f0000f401c441046c1c510202c1d180e07041c84031010f0a21224030b201c0c0503152800c2c0b40600001c0760040c2000c2c1d032621410384c8001c0a42c4203085800c00d99400d8051580c0d01a8016401101c02c1840c0c00010b00c29101e40d0000c04040711981a40103203140000c1d00a84146102c2950140d04004810800e42c192150403c0246003507550b169 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 52418133 1250 52416883 52416887
    0x6130315060906080309100f0e120604170a0504150923010905061c02210903030105100305010e040209100b0c0616020d0206010b0715050108030d0c1d090901020408010903 75
    0xc2c02003120380d0340b03060b80100d0780c00030010958107941c00c000c00000c280781c29014100c8901c1400020321043c05000703076028605540302a00003402000d8503004200c00d03c0c0c98240380460707042c10304e81901641310811010424940c410221002d440c1c2c90101140482004941110799000d45c3d4410707d400300c00c550500b80076201c4401000f070120000daaa48048a846a00704640c2e0b01c25004060030300181c003000444084c00719000f40c0304031103005418561480c031548220b0749400d402c880d00600341e000040180642c0c07034100c00001000169240070890356041594a849943c80907001912a01d6840c002411a1030782101840280910394141901d40060000080d0b80315400d641e42a00c00104040000d0091310000740080019003590080046919000312441c9a52150f034041d80c2483c82e8a900600d0b21069002d21402014404011644e800e2621108000c4580100b401c204000010415042da4034480c12100b036007400c00c888541d80c03503c9034502c1c0c500a11941d48200f015500b00800351b41496 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 52419383 1250 52418133 52418141
    0x30e1305040c0b0f0a120609061707061407020405130203010e0d170c0412050106030602070b0109050a09030206060f01031d0a050d030b10050c0109020a0f080c0105030103050c06130315 81
    0x25100b4040755040c0d40c0c4481407810f050050800504507418180040b0000502c5181490381101006500203a016140e40020050342c00c41e400c0b180042c04a21148082a00c0810101006240b14540708000c144c503041d10000e107101d43d4070301074415034503840413400d152203a241c09540d542d0300800800c040104c2590194650003509655004540d2881c007080b0440d082101e0644160300c0310400174503060601701110020060900c040e03840d903680d9400800002e80c144008d00b405030049074920350540c5002c54107020b032640109121191410000c00c100040e0300018000e0701701703501b182c42503004098040128000c103409a07514858040800342d035a9490790110360150040e01a00940d40007503401c1c0c0041d030954200e000710382d42018030200002c000342e1041014102645410001080a02c0369400103180d41c406500880c035400b401c154100090301d820040d060503180d003802c0040c19503255803034407521403400014140c02030500089200c0b5a2562b0307a4800b003e1075000d01440031761014030a03458020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 52420633 1250 52419383 52419391
    0x5010e0f12100b0d02090a180b07030f06090e1c1209060204060e010908120d090803070908010614060306040506030307020612060a0f03150c0e0a140306010b04050d0f030e1305 77
    0x46072801c07a50b0489810084d901e0300020750040c1c0b4250854a424805800400e5245411402c0349404800880000c079010034060003520790740d401182e0003103402c841c40308544180d03000c44560341c54002e1035120071802041f002d02d0110001121095034a61b179a09a83e5002da9082c0304c00045c0c540f080c84810000c00d98090070075962213a460420b48000c5100655040116001c1d450403640801c01000d0184851030090125400200002c43d42c0b079466940c000c11130300161a4100450f8254500780a404000d110382401007100804010306000d1020110300e05201c00b070100b80c003441e03d8000003200c2d510100100c0d168290b0103441156035200d039002d80c07208001c064944911a00c4010400076442526601c1c6000762600405441100c01071040800c0081005588690501000c00f01d112603d58580420000404c2040000d81381401d9070b1007090b007401d005130811019100280401d00a07a00c0318504172019641c000c0545004460724202918022010900140d01840112003464241003a070003403401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 52421883 1250 52420633 52420663
    0x1801090b010503062202090a030b06030f060c04120204060e1306141e04210c140106060503011503020d02130302030c090c0a0302180a080106150302070c05010e0f12 72
    0x2400c03503803800458440c4815144603a1009035812108130004100608100703021201c0c01c014076001300300340803c108013426130003514032012201c208501802d0907c59010003580701e5001d40360341c3c0f80c10181103440380a03500a1a46400140c18014115219640003001900403501c29000c64500070500c2504059501c00840c1d45506000c0e00700d1000b48101c1c9203d014124075030340b010342120300c80c1c00b00c481088003d02c152000d054040c480303a43c1a070a000322040b0400e869691000384c000f18140400d00c40000000280c0903072401904001d201d5000c003d1b40d054a20a444001d91a0701281046001c1e0180c1d002c8100c01d240f000841041c42140000d001d41180c0c03095040d03841002d1080100309101c18200e4154515100c00c204100170513209a00810074038801e21100903040a00303002007808204550030449460b0355a44007402440303140224403985400e01d02d0f080d450420f42e644d40c150000c0142c81400c2c18000d0111824040e550ba451140745641e501800c904d0b40740e0304564419036220107a00340300103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 52423133 1250 52421883 52421891
    0x306010f0c02130c03021e04062a02090c0408100f0c030212061219050a020315010311040207080909130b090304121509050d0c031805010f0f030209180109 68
    0xc038060180080892032030b001000201c41c80b00c120b003040040e28240000c0010158201304240030102c0081900c2c14440b0444002500c6506054024087d1041803c034204110700e80f500745180203030501c01c1c0308800c0364142d440c10700f07640314080103110b180519000032146020703081a0b0020300d909640031150204d10307800c0601590385250001e03000ca00c6134208040c49501880001405401c20007800422010b43d00300311080d005058601800d198607a22085070187c0110031000113518080111038074040303011b00c9580389540345541344d905461000c8602e07801641c011403900c1c14415070409480100c90043d0814809103046400c0b6800c1d4500c01d0300489900c4600d002081410800006560a4407112410038200c81030360b072209a02d05400c14000b80300b2a8840c0c01e040000380c000c0c8600c4404c0c4580e5100c0c141d82c00000e01d800b4004080c0c0340d44028400605201c20001681d00100075411501d142c284900014040340c1d0031400b91080404868104e128000382d90030b441d02d5020100d0403512a000100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 52424383 1250 52423133 52423157
    0xa020f010305012102120d02060a05060604080a0f0812040f03090b09210708070612050f2202010306030b31030203190e131e0b0307121b0b030601 64
    0x5021900c00b802144e06090b0202ea40c0d404e100f02c1c9600d03240c24640000d25405925510301829840e00661040c408011f070413400502003645000c0c06100c0e00b00070205c030901e04203401d0009441d681c1c40324100c040c104114807501942841803090487d004400b00c4075080720945002d080a0b098141e00301c804400240349184000f4011007224296502c01000420103201804040a50600503c0d42548801e9070300400c20005540f210402a00300201400d45600c60140414428141211001401000c0c030185450400c003d203140c0500d845640310540181c0d1841007501e00048000b03020f240c1000741244031a50901080c50301031100e00110040001e2035120140050000b0a018841c404000b40036a00601c0286001488148001e585410074605901035071041d0f00080c007440898103a050411f41d84020311b6a07280f00c01c555083c030a0288110130b102c0d040010380841d6540b0326511441e00c1414031f88a0750010002c418800c0a9420966012031040799142c1c84100d085c5d50050b00c016010668080b460 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 52425633 1250 52424383 52424387
    0x6020a020d030911060705100f05100f050108071b061d0706090b0a08070212030408070c060203030402010c060b01030207020d2a1a0f040b12091902030c131404050a020f01 75
    0x88190b03e0b80c44000214084c12803400d012a54010b02da0071502809001e00e415078034015031082041210700007034007013558281038900c800d04641c51703080301400c103020321414040b50340c100500540041c0c1505c1c1000842600d2a0100c001c2111b10200404c1d40d4201942c060203a200b40784901d0010080e1426140e031240d0f178100c00c1d40e250955200700c104010b001d02c110061540a01061640709030030740140c45100703411200707180f45580101d03011282000c002c41e4090030b100401078a2805000701c0d00045140d81451b8001a103e400380c5140100840d88903a98904980d01c65015592010f40c060540704103004107251558010f8046520400c4e05a02c3d5010300101c001d0701410700c0c00301c0700c0e01d4598258030b1b071a180b0609025030054000d41400c210411000403844101d100034441041c00c06404201c904142403040d04005011a0000301800c850740c1d8003000d40d40c046006080702000326a03d85040c0c001400002c0688859010580b02d0a1400104400d00901090000b5142d00c00c03691104036028003001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 52426883 1250 52425633 52425641
    0x20103060f0323070e100915080618010b040c0309051b090403030b030712050a0c08010501081002160b09030d2304141203070513050d02090403052506020a020d03 71
    0x40d003400c01c0f844044085040107400d0764078111507071094895076034031401001c3c4040302c1034803086103100d00c40504001c2000184546145c034181c800541031400d1400100596a440203801c1e40d00c43c0710300621807040c0c01403d501244134000d000d80f081c000a40d0165000d401000c42d0001034809001d40300c2006500c02d0901c0740b242c000070b4000d0401c0250388564400301c00802420754696018480e4000200c0c001c41c0044412410a10800041841500c14030f00032407142680c0d4001082a03042c000140500c8002007280c445040c40311900503100e00700b880c05060990010007000e0256003c0d0410300c03003180008002000c032280503d60601074400d071494520b00265403d1150300d0790421200200340000c4083c0c986170038a850440c02ca4008194030741148005900030b540b07420106400080903020380c4480c5207190300406040742c60100c089038980100302000b0006200a040003000110281221180b040381070050340910214041c400242c60100c0080d400702400b0000342c420880f03d203090501c0303402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 52428133 1250 52426883 52426889
    0xf090b030609070810080a0807060b01020a050c06070602400501090504050402120d03051f0e0a020f0f0712141905250501050402180f220b04060504020103060f 70
    0x40300c002c1c541e48900b01282c40c110090562038156103003500c0040c0500d020481070950601a00d510b40e6100740a150040031211540102410354014286080100300080751151200405442941e13440c01740e4079140c0024480d0048410901100400c0410303007049a00e405004200701800c0c050b4144903000b111341e4401d419200e82800a5001d043c00d10490070300c0e4000d01d40142c400b400481102380b1041e640c41c02d115080031a03500003582d40e41000540b000d8012000d4500c01c0c00c0e026020418109626418080002001080350640018583e58034192407822554280000e520207a01e580c0c040c030b09100070b00b100301d0700000080d95503a803200d01014260100d403101c5225402d009102801014251241e400085405540c1080f0009001c80803500c00002d0841c00d10540c000111441c151040040142289081610061842040202c0c1d07803001e0030840e400c00c6006800c1200600c20880c10301007801c0c405401052003012206220070415650003090207280300740c1302071103610780326590000900c61500c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 52429383 1250 52428133 52428139
    0x1030e070b2d18090a09080f0304050a05030307050403050601060f020a12021608062502070e090a020a0b0a020c030d02120310050603100303030b010203180603070201090b070f090b0306 81
    0x101c80488980d03110b24041c41c0300d00000881d400d406412203920b081d04901c0040a89420b09081060303149460090300f50b00c81c1d00d016003008076404944030320f401030040d003140d00f403148000000304060010805c414280b40380c0c04011260359113452035004000d03400512003200c092240c900003203131140c0250306031039800100ea80185072110082d00c84040640810399690107502500c0721218140701c070640f031480039041c050000d01150500b8045601c030ba20514214500521600131044000c0354080f510b5402c407070303011143c0a03603a102c201c961420400c00303070002503000070b07902070004581003040c01034040540c503074080e13840c8101c44005241c3c030b5450070000200142c1241508001c3c01c105e05000c0e40d0420322860110511380c0d1182e011440d15030041d40c4035000d09003241c008000f0994140181580c0c15020f00c040c40c00d00c45007103840846c501c0f8445115109001c00f00014003124402d6012000041d004142850345007083c843c003511409104071aa00000c00b48000420600500c50850380584005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 52430633 1250 52429383 52429387
    0xc0509090411090114010806030303060609060a050d0c0f080906010807210501020409270b04030e01210c0e0102030301080d0f0903170d0b090405070512010b041a01030e070b 76
    0x1441005410303100104112510a0074601c0d910507629803e103030f41c2c0a80381c80030344c1480c0744c8003081c00900b03402c2c0300a03e401d1003540100200805d44d150305040d50031000e006c0e43c01c1c0e03842d4501d0070416101030181003240389425181c4483c07030f1021035100030003000d0405e00d40c80b020320540300c43d4405a181e040c03d010ba5042d99208500030000c900c40c0c03240d10030065200c01c040c441d4014803640c4490036684940c0c05048615111200032605e40305d4a90f800302c210b14145400002008507607541c50011000030405018015004450806130f402a60411481c00030305e42c11580f0000e0500c800001001c0440703030800000d0841c18198080e50001007280c1c143c81003100100f412280e1324204441004c10031012108003d01d5110000000310b40640c444400c0f01c44512094480d0015182c1030119035004040f0340c40351168106000100c0c40109202041c1c42c0d0907507604041c00e504401850240c105a0f1410340c001d0b01c0c04844040d040c100004048948400741e03000d10030710f000c150034140c3c0e80d0418003440c4505541 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 52431883 1250 52430633 52430647
    0x5040c080f07020c0a03050d0807020307051207032d080106030b210705060c0105010602190308041101140703120515031504060906051f080d050d050a0b061b0d02010c05 74
    0x10703080241e80d01030781620445080c2c2d583d507408903049003016402154640e001d2203004042c0380e04413084551040b82e501c011410b040290700c0d0340741d0301d08182d010046400000075020050603c0381c003805c1e0503a10341c0211001a1880003a6042242500c0140c0100207045a000442c990b803290040d6a414030340104130000e501c8441440c0c460001c10400501d2b0309100380c0c24001500e450386800381c0040c148904c0001029072400704085d04125282d28904110400e00b01c0c985c0000380c00020031341d04940c001482c1002071a4001c0181c0d003404071a840d9038103109001c28900b0825903c0408011014601401440507464034101c25110180a010055140d0080c00c82084400c07181500c040c1d01502800300800c0011864440a0403070708141e5108101c98003100b0301000b02e02416030640300801510000303008c010310120000380ba5020303800764001d0103500c0d4400300c6c036044456002410b020385c004205680e2a0062999042c9440e0480010005030094a00410301c40d8018031803d01c4100030744d00d0f05864149 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 52433133 1250 52431883 52431901
    0x20307051803010f050408030a0b060405010903110301240815060a050d050c04020a03050f060901060e010f0c05030d0c1107060203071103010e12131e030f0c0b030f060a05040c08 78
    0x406007100c0380c1540da180744035031900a450141d64043d80c011204030b5030301e0900f5080e08003031f00c4022800724010789082000308041c0c5da001e030481040700e400ca500c19030303034004207400240909001c9402c4082c0c0c0c06642c60100c00030583d50450781c1160f22550403103c0000d10380341c0040b103010003101c2d040d9020700c06407030420603401d20690001906104909958042c1d4641000404a0700304140c1c41000940c2ea0b01002815020000d010750405803c40e0151400e61411400500d01e040207001281080310810440c2d418074011800506040e9210003541d8540d00100c61081c01410045190340000c0c08a54a0324440301c1c0c04a5001d040d290a54040c510b000d8160312035001e4500e00d29a00e6170159a10b40c1c0c8241146414008140c03007441c0c040955039107521500b0301d10b42c00080ea400288081940c0034000301c0c03507501c4901d0303242240c1d40070070f0200c40d035001424030703900c0e0b1401c03030f403021036034000010800c805522200b008500c00c09080342c1042069440e80c00707110480394848942c1010034400404214412 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 52434383 1250 52433133 52433167
    0x6060810030f02011b200105030f060f030709020d020a080c0a050a030921030f0515010912051509010501030204060e010e180708010f020711030604120c110a03050c01020c01020102030705 82
    0x180181042c49650302e441c201080c8000301701c103090341c42496410b00b00c10107120b0318401c4005400c0919202e82542402015021030400180c8420f10452940301d02034015181801a50010154444110b469440880303040d0b019505c000e2050000543d2180010340788a00c42e000d4034072284690356003504004902d1001d8006024054065410962a15034460100c2d4580b45c1c541c5034150701d6801240210b13102d00c1c80419110081d00d280300c01e155000a00006980c418218400c44158899803010613500f4100942031070f49030076201c060302c0226410058610350540280d4100c034426902000708503503440c541807a244081c0290150a030106002c6000b07503000b544d19a80c40d800386030035031b8407003035403803050508449640103101c00b143e030046900003d00400403040107070b154007a405045680392903a50495070494041600d000d10400383c0c40d440c184000d1200c41d01c2c03c640090401444c054590a18582d180c0c1c0c55005140148600c0070a80f070f0551060003524010384213a196603040507a03103044011030b4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 52435633 1250 52434383 52434413
    0x51b010302190c050106090b3a0c06080105030714040c03110301270209032104051011160803090f0102010902060d06030b0106110303060609031504030f030606081003 73
    0x5409010010361150001c81da11109425a20b0f900500c203034a00d049030139508594000b00481e49006824040364030b90708410b110f021580c041c0c0324402981ca03d01012100026030195000c00c140314004804c20000c1400c11090f542251110301301aa612010142d450800d80240c0726405550309a40280d0b041542100c901c0780071505012400f05404400008260002d07800034550391240c41c42c1a03030380e0001a84205080e107080605518000041c000301340c0d16003089581070340d401c0301c001960ac60784c00c101094a02411001b03090784003003032a0400050050002003c17001c003e000301031002510180c1c031070044007116481006503090981103820007001c241c1d140b00c01c0d41995207070000000160b036100001c0001e0041c1c1440080c0860031400c00c12080041600600e003032008080d00242c2e40e000010a480e030290049504954036894080428241140209609461844c4400740b2040541140394490030821a5030304000480c0d4808007160107030703801e41d07004046017604801800072408800c040008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 52436883 1250 52435633 52435637
    0x61303030507021509060a0f1503020904170307020d030b030a050a02010f030204030605010e090705030607050306090a0f0207030c051606080408070602040803030408041a070816060b03011a03011107051b01 90
    0x800113061410300c030030303908031902c0740240c002c2c1c01013010b660079030301c00e4034440000d1240411000d000c0641c0900c0750000d9020107403048042000107401c100000c41290203003940780c1c02c1682c590030982030182d656140c145490010a04010300c041d124180014407405180d040002440540100e800640707141e0300b510704d42c008064007004084013240b05070285034001c2010340700240e540d203410420503090607420f41015100c0d801c844140b103a1554040107407500404112619543c40c1c40303204408005207500b0140c5000c1d070f400400c0f0b2038285904011070070341960280b002d4800d03203008a1200300240c0041e00458010508a1021030040354002e17011300f4042e40300d0328005140c04d0b03d41001038036542080300c1c01c1740c0c503800010701030002c0e000c8641025030b0311180342c4115040030116502da110501840e00d4468903101c07403450040600c24903420940401c82c002d0001c110444500b0050b4074044d0b0502010f81c00f940c2800303070b207403102c0e042c803402ca0300c3c0650060f000e0401801c03400710004641200e0403102e41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 52438133 1250 52436883 52436893
    0x60304060506041104080a02030708010c120b0303070b010801090b011403030409020c010221010306060e0c09010c0314040b0918070206130515010e0114091b070f0609050303060306010806130303050702 88
    0x44013861940100003034070000005051110851040502d010001d40000300633904042076100e0031600310349040b40301c40c2e00081c0850060946c1c404a0b1a50045c000701802107443c4000019203c030041d400304003810f00070080320000340c0c0c0b02e13001c40814012401065415038030800040010b025154007910025a55000240c070380000c482c544c94a01c50340c1d14510001c0b082a070010001c01c00b09124000041c11030042c800510b00d081200e558460180340301c854180919007080e401014825035142c00300a031043c00d4561503584990f143c00ca50f4110440c441d0050b0218845148a41c4c5090714080c0708409503801450207580f490080f56102050042c02c54141c4251040b660000c01d0380310780c0ca8080c00304401503105941c50b1401c080d28030900d861504e802000514140414030b204492500456520741c3d01e080d60740d2900341b4141160322100500a0f1515103000038101c2040070202c0114003c8204034121481643c0340e0410039104c510a03502c1001c06200c48200100090203900081e6025600e030042c1ea07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 52439383 1250 52438133 52438151
    0x1050103051506040b0a120504080306010809061b0d140906180604110613090905060f150306070315120c0618060503011e1721040e04170705030703030b01090501050906030406050604 80
    0x47c041d03903021380e03084800305408420880c142d40d224a800f64011a10342c002d00d4541411204a240c03a607416104407440c0034009002c68a02d0745642081170500901d048400740740ca8041e0318180c0714181658030310f51088124560080c4008005400d41c02a03400c54180071100c0016020044594800c02d2501ca4107e81c01c1000548018244140c1c130046010710064210303031030010101e01d14400020072440030154514107003550381d2000602194040c905040c0007807070040480003400d42c14000d50042540800300b810940402480380d106da402c480325500d400c045144940c1080150500e5030103110300040713003400100b1458102c495031030148003000110360762940d202e40940c203081c06018441030440e80200115503c440b007801035070000c03110740304060703007407600b0031680c910101d00c081d1015000701540868a07000c15100e2044030142907001d0100c964070340030b515000c1c024003c4000554003080c1b403d030000445500a000f160800d80004214a20b195520f9070389000805018080d9604290f5440a503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 52440633 1250 52439383 52439417
    0x503030406080f0c04030b040b06011b0507090c0305010e0c090a05040f020715060b0f1e03040309080d080103020d0206030a1e1505040b030c010c0f020a090501050103051506040b0a 79
    0x108080d29190750741c9841464681100143c0b080058030059484104010030004076800210003071f0400e600421800c1d064948900403100c00c075121603030010410340a55480100540011400c04507030307206400b449000401a001d03000c0325007d204e60038032465080009074400051500030481440000e2504880d203442d80003080898040780b03465101554002410001e000c103038008503401c0302e4554828000c0ca4100323410040d03180513240074502c07000c00101d0840800782401801c61500003034405801e45910385400c0043c01181c2070b00c05c0034a64046d14400301c2c0d0480c4108002d5040e0380e0003500c041d034903021039400d02c08998001007038200026607030007218204042c0c20300b001c0b040d051b04480c00f00765110085e280c10340344106680304c14803031468084106810b840110300001c880600342090b0001800e0307400c00d0442d100d0340d4200258416003540d001301d05000715038803050581d0780a0780d00b00b04c695112600c0c0f40080700c801014a500103406d100c00c21039000d075400106031042980c5000d240b461204180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 52441883 1250 52440633 52440637
    0x209070c060f1103061c050717010204052e080108060f0a0b09090706030c0201090b0612070b0304060903080106050304030903080f1606021222020906010c050607030b091e010506070c050303 83
    0x1444240f03400000901425241a03420501701402010702c48034001d40c59502d003596840244145100c0c01d009005d4031241d901c0a6064500511025142000e8808079222000501a402005041040c500c0b805440c0140c420b000d1541079031410001403249443d424403001c00c03064000c202039203103526456001721a4444d5050380703001c1c049002c02412503d080041c0a410360700040e0700780d82160325042c0c120010a82406442c0d4000c40c095912040c44410703594414206442508107190311007001051104102c00717544600c003a10700950fa0b4483c1662504030440d04c52100b41c4018001035495101130010548e94802840300035451310100d8507000f18981e0f2401011261403017950f1049d40800ca10340070301504101c0300d5019a444190380c80c1c5041e00d80f84403481e200c00c0d050203405400f4110000b196640600071038035850350082c08889161901c410001c3c041c00e120310b80c0c00c0c082d0302000082450514018804000b4031400481200c2c20307820002485440c3d00690070668103044842d100191907207003840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 52443133 1250 52441883 52441901
    0x70804052b0309051002010e0303010b180a0e100b030105060316030e0f0a05100b030d03050c040e09030c0f0c011b11060403050304061404030305030a18020307060521040209070c060f 80
    0x9408400304c0c0713040200441d40800d03140d01780541e41450004200d885000c001c0382d054501c0d82c03698a0b240d200315039081b0002126050283c0d0410300e044000f052003101c0540091090800c100642d1401e80c0720740000c45940020b00c51a80c10420520200b60002d0410a40d1400c0e820203250015242c2285401075207812024084201142c01c664680014414144502c0840707880d10082440f0f004080b101096864070341c0c0521008041c0d40300041044805010f003120000c090841c000c601c5c904003070101680303990144c0315070706d518441d40004040e00400407601d03c8295105864695121001d0500c0f01040c505100044441d40f0000b2005d90b05035481101500186000d04011501c680c20820042c0032140c48120400325003006000404c000f90341306080b80d9000c100380801040e00007200d00380c0c0d0314000603030030300a40c14081c040c0c0203d00654401c000d02482d03000308245500b5044172072400c100f1034070140c1c1d010390082030b42c0c00002c907004c1c000c0440b18012480385000155a280d00481c1d0030480702003003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 52444383 1250 52443133 52443137
    0x12010203071206090501050918100c05090306060103050c031513050903041505030103150e030d0603031101060501030905100509030706020a0f12050f0703050613090506040c0b070804052b03 83
    0x81c4102c0c00010714031481e005441100400c101a50500c00011130000000340201ca400980703485502e50f080f0b040c001e07041841400081400300f8010280e01800d56005096002d001c3e1054100260040d8401e000d098042d095410704907295484030300806192501d8500d0194200c148031080c13810100d003d200340c500c5559404061600d85080c0254042d0039100d5080d80c0007042014001400850a074807001c03082c0c0045407000290008500110785c0c21801061070342c01300c5914105002042c90740010810355400b50240080240d941c440c0015801c594848034050840e600c41c480c800b21b5040658440303600030545004480c01c0442940d00c0c8404d0b40d21544020380010890780c0b06100c5150007040020030b801c0c1d05107003405246080018040440d0b801086801010b4460b0045010707911020702d0800303ca0840003082c401142d45041c9160313112801e40e022544c20b0841040080c000c6091000d565805512071030261406c1e1408040104540388103e04000c020b0b048000c00080030007100c072003010907200e9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 52445633 1250 52444383 52444397
    0xf0605090c0705010e06010b030a0c09031b090c02120d0906021e07030201060506030f0f10050a031a06010c02150a09050a030308070206070503010501020717010f020408031e09011d1201020307 84
    0x243c6801401e54440324918103d503070003c4e006000200024098030b90000f0780e07040000d9000c400c003030100d0700004a6031010f400c9420f0345071005c00c00c0d60028819400d481440c1c009001d1052210741c03c994800501046904406c41444209070301034441e0050b0402d140074070005070514003054402c4200c241c104640c8a50352900150303840c2019028041c0400622080710224158605590324407881c00009044408070800000040c0301e440114802d01e020b03100140090000c1a141c1c5020960a001d01d50b003014818084000150258800c1140911055000d0545802141ca040f1503600c1070704a50804020b001d203a01001c02d1a8030742162110042d40030f540d90284030300b0310300f40181c00c000014010b0000c00c0403c01c01070101340d80024049049070105840d4040c40440105018010807201a035403075014000900024442d800101800044400300c2d94008001200c0a0110701440394005e104d003c5003414111107002d03041c98200c46490540503003001c180c0c16400e640542213910480d01500841c1d20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 52446883 1250 52445633 52445647
    0x1704080c01022d0f121933080312131205180a24030f090609050d0206160c080d0603030216050d080304020d1a010b0306090901021303060f0605090c 65
    0x80788560760750f05a0110503071034004505001646131042d0020b00c04403004003400b2812609040850310b8200150240412403000030407040419005904600d03a51012410300c1004030b00031182c03ca404440a002c001c62601302c8a03039218074800303001010070240008030200c550201d83c00000d400314041c201e40d1065a188ac0d0b000006107005183c1e50400c0c01030015501c240b00d081075a00a0700004447d15174840c01c0700408101c220007078a401c5050001c25802c1100610421100b45c0044010364410342c2a00e40344005030f40102c0c4d59039011901d003416129018000141c0c0d80c041c800c0c4880b4180139030000c5240100d8841a141a074410344e100b00c00590100c2d41e003107245000200520068074007122035591058a03501d600d503840c040030700080d214482d004502000c1052800e020401d240305094544115030303440965488035042140d4050085000900082d004607040c402c880804000c00d20304481c040c1140c48040050500d0a00e0b40c12040c1d4801c404242075568082c0d0502c02c08034507036242d680725a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 52448133 1250 52446883 52446937
    0xa12080307030c0804030f0509240d18110d02130212060103050105010207032117010e0103030e0609030d0809070f0902070507050402040501020307030e060409050106020115060e011704080c0102 85
    0x20b500c8000f4040107002002c1c40000b99000e5601302400c1900c0c07a00c0f980340c851840c002001e80410003e070014500e901c010180c0329501640180c00c407080e02e00300402c9200c0261048011350351a000009049820b40f5242902c00d1810310401c052190024143e200782c8540c005e180c070100c1e44102116004030b03507450100101076070b050080901402d001c1c4003902d0700c035103165649450800318644546031403042c40d88010032203200b80128180b0024410700007086507502c080c1c84c240620300b8081900000c41394403c4d80814100703602142c1c16480c02400901c40c14a03251400c4039400c0001d017010072940960040002d1f071982030b1b0703030b00406404010300040e6142154a0040e243c6091a0701003802075005101c10840c0341e8012050710b80241d01820040d5450038158000b940c0b6108a811140c411841c040000c240c055055010b28400c4d980c01d03c14000041d2120010740d06940da0504660021780031502c1034100d11850024190403a03c1401140e013022400350845003640c10096150312192011907410752040c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 52449383 1250 52448133 52448141
    0x2060f0703090e2e06020a06020c010908210c07200102100e0c09090f0309011b020a12060506030c06030c09010c021f0f0f020a02060f090a0b090312090d030804020a1208030703 77
    0x130741210204686160140c06034035240c0c001405084075901041c1743c00007410030740128940c9944411540d55801000614083d48001e902045000d90354001c00600d030082d250b011641410b800c901c2d10962858800440911540c00205890441c020300c0094000c40e2441c0c003902e1450019900602008080003040c4140e04000400d64207555000c14810001b84401104840d2005800e107050319081c2c8100f0084100080110301c000d4100d10728140020f03884035800615060396128a10500c1543c039920101540c80c60010f8041d07500c01c80c2000401c4104400c100144250300c0c040c149110214001e4002601c041304264031212119400d03094594150703070024400280d20146e041042e40c1c004140302c02075071603a01c0c040003801050000760510b5405648810f0302d85814000300074000007a2104682d88644d009100454028403642c40000000400841035514400024103030004285003500e086490b203002502c00c0c4d8000001d4000802e501501c0e0145050560181200c540d40b8201410010120707 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 52450633 1250 52449383 52449451
    0x180507080c040b0f0907050c070305060a050c13060e0f090103110102120414060702180a0f0e1506150c0a0506160905130507020c0d0309031202060402060f0703090e 72
    0x60b9280804012240c0d8420005020303840c010b441806240e43c49900a82d410f1080c0c03541081544101e0200000b0041c0004102c1c1c4203082e101c506000c0740c0c880c070300103c2a5014012443c50031590303424050260a1140d2701c030700946e21008007030040c01000600440c2d0000d0080e00191006c8010903460021940c0420400e10710042043e103080c5041d14001f542d5015000d640c5c0e0740f034818030b800a01d400556075230380c01c8800e0041c0c07840c0c918001030400e101c03040010060599104100c0703080c003c500e03400510110300809080107149a5000a42d01c06003001514051241782103100c440900c6641d03d0280c08005044070548140001c00550825480890321000301984920401202039018001c0d034803001854490407400341c01c0880d0907214801e099050241001600d50030515261002c014913500c0301940044034001c040403040408075040890f1101d800301c40203500481d04005112032018020000c104090107490001c100c0f640301d000310301c0e40d03080a40b02280403400a003904400c0c4c0c1c41d5400c40b9160703 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 52451883 1250 52450633 52450639
    0x3012d06050a050a0306020d0213080c01020705120705010c0204110715050a050408041205070302030d0e0a0e01120314090301051306050703050610030f060e0406020307110d0203040b0d180507080c 86
    0x2003e29000020340003605901000f40819004541611220800e405403450303001060140d10f0485d407605d4005035201d941d03c0c1c0d02070062180c10000507050400c0180700c0b101c124900098102641401d0055954104400d4200d8019039200079081000d1801d001400004c0c0c0300324070860014030b10044410607600d010b08001c0d001c6152105120000b110b0300304a408a8009912401c0300d007030203042140c1800301d00e500294043c064100d5007012254803807240075441800700ca400d05e00c161540807802041d00240150301482c0d0965218002003401207500800408817040c80c1d42c644480000402e0a55805888005801c50701c2c010550420a407030141c0d0f6801411840c00300040c4c1342050004032121428000d40342415542c0c5001030303455805812490141c1b030010144c90550905107403000095004407000d1000078182c11680888400101c2c14040e0390b10258000c5042504040100701191321000d030300c10b0100c5d45c4115140030200302641402c00c0b6070160380508000c0c0d24100712a400e0050309000e440c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 52453133 1250 52451883 52451899
    0x9010906061b0305070507090b13050412050912010606081501030b0307090506060f0c0d0201051b03010501030507050405040513020f01030204050d0602031b03090d0e0904031d03012d0605 82
    0x9160ba01040c41e1040c0340c901c420290740782020341016180c4d0f103e030460191040c064501c0100701966580c01120081605440c2c0300c25100c1040034103400c98030301ba10006c1c00c0182819103141441d1007080504920305006141591100c4e20b0941c00d4210fa055a1154020030818001c200c00108580c0700c0d28201d103401c0c20140800d6540c40c00094842c0c48030700900f0300703080d51075000c1003d03901c400083e1101d4070010000c081e52500d01c98107099841c0307100c04c0705c88010741c20403000450710503282c25451040e150a10100c1e08590901c0019009010000d0031082004020302000546585d04c0c0129401403039200c2125000708500d0052008000c0703404402c0d030605004005c10030240e103524840594070340c6c000b400143c8940b500c01c04000402d40711014040684004402e00c80c01e28008150540c1c05903840e152460303010807100600071190002c99024012420030b07201c40602111417000282510030040000408074080200009500300a82c040a03e1115003003000300c0003115442040e01518044500030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 52454383 1250 52453133 52453139
    0xd03020f2103071211040e0609090d0203040b030a021204030c021302090a030f08091018080111030f0405011103010902070507080304240903020a12020f01030c200307060903020c09010906 82
    0x10b2002500e10000c112aa0084084c3c20034140c0c0003080d83c19180c0c1d0480c1d030ba150390740140e6090744000c0d1020348c0320700a010007249416030300280d0403000e50388640142d414149410450101500014650704140b90204207882c06840c00032a1980709034840e4a82c7c0c08052200d00501c6800040040a901c0c0d40b84108401480c0f0741d1004021422240c0c00301011035401e030140b500c5002030103150300c0a50080808206103107220b81045005400406a1200759000390b070b11070000303080c0c039910104584603800c01c102040d10390b0040000c9550160141d00042851001c0810f440b40340c0d80264001c803807160b07012412100b0040140014030080c080c550045050906080043e81001000b0042a04d5032080e00e070400380480c0948809002190020110407145945091a103002626060100e10aa8074040c48515560192043c1003078205a9030700ca400c0c03a9503d070340200002800400c5001188801c1c840d0344000307140c5005044089102c0d601406150b00f01e80180030070140107030403a81c1002d0038400e0134 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 52455633 1250 52454383 52454443
    0x1080123010b070309081005160203041503020c03092101140108071203020f0609071701150510030209030f030403020405011d0403030c0c021804110d0b010b0f090d03020f 75
    0x803419250110314035030f540c00c2645400d4502140380d6001d4030b101d00611411400c0d02a160307001a1081500c0b13048103040d840090300480e1248250b0090500c0341081c0c0450501c5144258003600c00c00d500c12003120300e0b140700078000a45001c0804000d05c51100311301c110880c40c9600f8000c440440010005040c4103505040046032951014020800a490800c4038601032510801c040b4100306903500c141c5016042000303400351210403070302030302c00c1c42d0130280b02040c007042051080f40d18842d41c0914881d08541014100003a8014140010080680901c0315000550302030101a9a8401000c0116552451403062000313aa40c164010103e11611a40c5101180d2103030200f03076803259042c40d000540d108200e2040e141d581e080c800180d001a04481c5000607512aa0381090055001c0e444607441ca00f05102000720400d00058010080101200100040c1c5141005040024440e200280c10108880080b0b1100c6d4402d230030a40040c0d00083c11901c00c401d0600c40a00c501d8551944001218120a40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 52456883 1250 52455633 52455701
    0x100801020a02031e2203021e060a030c03021c150e06030a140109141e0304180902040f11120a1406010819050709050f0609010c08160c0905010801 64
    0x80d50918004d80b11001c1e445032644201c0301240101107455008803c105855007040c20240802c0740100c035100c90b400105509504008612100142180d03c0e003514080d04401900705076808505058090040668030b02c00c580d44d01c0035010b1340707800000745003022454000035001c41e40d020052081030034007880307403545003c03846180d00e0b50040b117144e440baa000c1d000726005241c84003010b400178400019510030b146011690040360b20a003a1072030700c0c2040c004041d644070b20a074440c191450112642a10f44030140c0e8014044060005000003064804043d5000a907503a04903080f00350f4100181c00300000c406011402d0f001080080200101c0070001e8507090b50ba03401504a034140002c04c400198800e25203c841040181d150b00140f01c5030400000190410307542e80a060f01c1010344001456aa050603000e54405460580d65890030359030039180c0340b04503404103203c1e922a01c107550101012954003224070b0020811802d00044c59850b1140710345c2111080b800c2c14038000242545004040940c0714 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 52458133 1250 52456883 52456897
    0x7260c0d030207030b0c0403020d03050711040e0606240406020a0209010602060114060304060207050a05070510051303030509031e10060e06030c0108060102150414070b03010605160611070506100801020a0203 91
    0x40c203c803413a06e421480e00303803900450340001c0d400880100c241e0b00305070b8408054080035104103883d01c60f03a1912010802911001d00d0702100d50340c00324001070114901911440d002141c42d074030f90b45c4404184401c144443d070181c1c00031405030b0b00400c1014210305116116034010459403000d008954107021003030101090b00201c01e0701c42c220120220381881010b80c1210202e503401400c43d00780d00c2803860010340b282060b100386481003171482041c0840c1c41c000d400f00c4030320281c10821030810a05660b41070f2082c0d00b2144985400d03106d00d01380c02c40003010041d00c4100740221800180100500d8070000c0c82914243e41000100580c000c050141c02d440002d032030000f10100f401d10303114558401004038907152507030940c0c6140700d000c02d0070701041c062304981a0860a85a5041c4e1b4485501e651040740c1c50b00c420302c14140000d030204000681c0c1101d1030b602440c4a4071411020400c40415246510369801c00642030b10107400000900140210442007200146940790080d82804c00c5203001039200d0160310 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 52459383 1250 52458133 52458143
    0x3121110020f040e04030305060406080d1e030b0306040804030506060f0f040506060d02040e01030515090a12020a0803010305010f050610120b060712020618010203100b0c07260c0d03020703 83
    0x85118034500302c040056070050f190031503030030318a46420300f0000c0c0902801d4922a0086140182c081240c1c003020400429600300d913158001500307041d0406043c0f070b5250b0681c6c8802c141c3c1d01c072604606681c06010b02d5024034052a0503075162030441c02d045007031410143c20389104542c20001c01181c2e03143c252303102c806010304440005440d0b556001040c42481954042000c95100050101c2c1c49210540e48030305807030040048401005210b40110100d410a6a4030030305ca07032150741080000381443c016180655000d1066440007012a0b4850b4115002038000b04d81d5651510f10007501455107114980d40803000702c41d80c1020340e0054001030031a4148141c1d0551107a22440520255160001200c0086920861042c13160070301c42002904c451054030314846260709004104481007050096038000c100d5049070080307ca150212007000c40d4805042000640070b100c5000902c0440500d01d62200250704c0c0c01c9100b0324a400001506242c00c02c85280e100399111031080001c254000f4010090b25441 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 52460633 1250 52459383 52459387
    0x7031b120c090503060903070302070e040201090e130b070e0102010b03120a050a02070503030c010b10170a0903030e0d0807090515160c0909050d030605120d05030a150b040312111002 80
    0x101e002100d040d08150003190f003510a01041c00964040003004002c0a4020380c2551003003922403408541e4800160340190000f84252011f01092800f072981c1c5410401c6040d045107400310580d509441303508119002400710b90003030401e1555507020701841c1000e5600301e0262003001c1201036441424054503060702c081080202d084081d02d03008100003405001c0003012a40c94425090405028280d548074881c010707103c1d54060bc691034010130603881c00707a007c401403062540c1d8282c0c04200a084c3c03100c041e810903841e408140342c0101c0502812860b10301e5a03440c21590f10388404050903d0350550310540c06200e00c2d8800c0034080e4580029a6401d02c4c2c0750500c0c41e03031441e2a007400288030845401c580811850300c1c03001410480c1c005403041518140d6141800510354610400140740c00c00d441d4441243c21920a02041521a000039548100d040384005850364184000c8034850b041c6402280401d1000607080c020700c551400c60301d41c0200781c0d140110581c500a50000c1d01d0f1400e01450280701600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 52461883 1250 52460633 52460651
    0x60507020a02030a0f0615140d0f0206030a06050901060e090406050c0c0625030905251502070e1303321c0c030203061008060d0203060f07031b12 64
    0x2003072085055160b0010100c502c046a075003401020050305c4041200c8152419950702009032240504100301d0b84007402e00340f40741511900380090070051040884d061a00707414181c0040c0d45040c0510300501c60b41c0800914907052030b061220080060708550140041d21a803458566500d06029a21070b0b030045010031940c8810a54001c0380c003075004d54000c0340c0111000c20541d0040d03a081c07040440c2c002a80b045440c0e0810351700f60120342c02d2a0780500706412054810541ca0142910720700c074251410b110456099565080e000c0c50095003021800503081030700e080160184820240d030700414000c031200f40d00100d41d035002e04545002d081011000550b9030b01c204072800502481400388410141c1281d40e00803c9030140341a5514050203060207141091143c01e16109109072807040001505240038501c0f801800c0c3c80682004000e0765103d21011a5000140c80c1880250301560200b0220012410328102c06426121000234200c0b816403903500d901d10066110503500c0840407140c10014841035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 52463133 1250 52461883 52461887
    0x4020d0b1002100501061b060b010c080d140c120615070206041409090106061b02040b1008040c0e040b0408030a150b091203040b03041103030408010c090e0601020a0f060507 76
    0x4210040298081c40c0391210a901d1a00807980060503a8030380340c104060f83c1c0342c2c041a58081d500c40580500c20600c01c26941c00a2103a03400306044450506101482103083e964444155001c0c403090102c0c5521000800541d0311100c078041d8005120440c800c0c00d01e20b000c1c076080607960f00101001d218503a001280c04400700c2540480750419005001c183e80c0b15100c201c041d0986c24104a210b010b5000d14000840c045010320504041d6800b65580385080f152030359a070052018040783c1039a219944002e0521260344611040300184a036485669041c6041c0c24504074940e0f172940000180b840241c100b0002582d1203802d0380d071095004c03400e02c0c6c03251a03681c502c600820f811006010784d85c030100380200c0d460030380101906031004101ca040326103d0078444255260b02452207404100c00d010701c08200015400c0b14078010305200941240e052503600d0811b1801d41d03a4040c5407a0118440c0e850510841c003a0380400c0743d00080078001440c190081da525001b6800000784003070150340d0703030700d002c107031814 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 52464383 1250 52463133 52463141
    0x609010503071b0f110f0a050f01111c140f0306090a09050115031101020106050117060102030f0f0d0b120d120204050a0b0c070801060302090a0e100c02030d0b061804020d 75
    0x21104903140c50b155141340000b441c10a620080d6580412020b600d4003a1415412020342e005020345110840c900d40300c00c0c000b4040c0c020311881c6c10312101540c01d0000c803c08000c100700b85901c0c0283c0c80d0000c0328490703002d000d01003906518034965108101c454103c1c052030048a0300600c1c1502d60004c40d40e558403a0300000c0c403455000400c15420001401c160281020021003a203001c1d02c40c0d09040e1100c5001079080382c44a218150100d11403510640401001002c42c2c0c0d4000010f0040d28500320400b007040983e41d000012841021070080756018601e00f4520440320341120555400f00d2881c02899041d5603006510901c0007000160300703406441d00c1c0d194069400800d00079028403c4a03413640c00c12526900140342c0801d042c41010400140404140500c02c21a500a0700403c46d603203500503010041c0c500407030100b5440c4240d505555110410340303c1c0f4081038243d58042c54640400171100b009861214400b588180d2052200c4001c444807800000d4105000701c8005030740d100c1e40c440c40e102034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 52465633 1250 52464383 52464407
    0x3050d0612050c01182105030d0c0206070e031b040209280e060301090f03110a05060f1602010501180c090816030203100507080606070f0b010b0c1506060901050307 72
    0x6503100744851040080006500c107060b0000d88810011482580071216107981c14400c054000d51500d04c82401080c078405400f11180c028015645001c0f0645c1a0505481500300244016072000c001c00001c15405401811080e1007203024014000285011240084800c0105446940e00040030f000380d58520f84d40841a83d10070903550005980c41801d4100e07084203105100c0e0200350440003c60619040c03080c11041c503403000714841401140d840440380c50035407140e24155845080301c0c1002098040103a548202c50b49030b9195801d1a01206140041621201042c21f580c1000014400080032400c01584240d010038001402d40328004125940800d5070311065241c056103252145503c03810621500303407802034085903070017040c45109400b100e07401c55910000901c020041450b514111005154442c0a020301c14403048a945803211200d5003030384403103c292800038041200342000d200c4154420076019884034286802404100c0900c2062000c90410000200050a02e4062800780e042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 52466883 1250 52465633 52465649
    0x90c0c0b18010e03040f090902010c060203010807231008090102040f0801050a0b190b0306060906030f040507090e0304050d0501060b030709140607020d0212030906070b01030606140a0303050d06 85
    0x10038180a000803101006012100304039509103511032000700000011102140c041b5174942d80d40f00c0ca0440303608014080b001c1704034104011540070b41c01140207800590b01909200e40070300f002a14002d800c1008101481c1c40080220701d042030003040d555010102a241402d44c20700c50050390b42c0c400348600920440e0042d5403007110b1100c1c0800e502e02c0540c0041c3c840c01c00c0d83c40810041e03164508101c04c1020034408203001458541d420f20503134001d00080c5070050700140a2604100f041c10014509800403528000351982503400c2100f80482040342c10010310105a04101e09100c4a082584a101d40c0c02242e024400100740c8030104903007503100c82e004283c5044184c0d00c3c3d04000300010040c01c080c2c4180781c40000078a0041c410340ca0140d00310f418a990003441c1072620001da500340070304d009078440c10f101140010301c001d02e815200e0100600c4110b204500c4003505605520305041140e9139030300706090b2a2810f4040c0279140e210010520705583d0582481034075400d5400082020b004243c0200c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 52468133 1250 52466883 52466903
    0x309020f0303072103020c070605070302010f02210c1305061308010c08071706012106030203190b1e1f03020312030103031d01090902180405011203080106050310090c0c 74
    0x10600290411341c9000303002c0350903500c3e042400030204605901800c0500652508120b000b008818050401402803520034000030404031144243c0004a801040303140031030f010380c0810702c004139064070003131544255540d02036400e050054050740e40e00403560107071602071400040c81c41034543c008402c0318024002e2000a000f01001c40d600140072007800e8800d01c000c103040ca858241c40b003001d103000394032580069403107a02141143c0c1021194000d0300f64180300076903940c8804409030b10140081c00c8502000d14031541202560b142118119400800251603412421041c3d0b40b4000710301d41c103c0c2c2002d200440151458544408441c2c0411584c0c0f000798107103e26032640808411440166041364025200d0f0a0318041c07815040041d07603910a2000c0c000f403440c81041c0444980c1f030740509031400810605001c07a41005021408481083e00a480da40c101483c802d030806500024240c050034444ca0070030b04604104a02c20141c54490003130300180f5449840e03040086c0d119112040c8219080041d040b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 52469383 1250 52468133 52468147
    0x30b0d0615050306100608040b07120f0c0f030504050705010503091501080c040e0c0d08031b0408070306150308090f060c0d1d010e010503010e09010603051213060314070309020f0303 80
    0x100d01c04858410b1a009010b050001040140c0d120010f408071042a107400c20265601e50301c120b4042002007102080c0702200c003c9002c80d00041c82071800551044a002451220190001e4800380ea41040e410816040c401000700150b80840d01030100c4100b03003091a01ca4581840890828004600594900800d50000201614002160012900d090f14200010100b901900e92149110944240c000390000c04400004102500441d8041c0182c613007120303a032a039080080758a91199004d940301750701049040c010302105124485410f038101c05400d4138a880c59032002041d00450644600c10000a68204d03440d44809046a811005117005d94117610581000503101204038644801d49600c1c20058404d15400762005003000d400503100c850450f8a0321042c02400540104580060b5407039010000c000b640c01c020501040700c00005560310b51040d811060840c40e19a44084205030518444005031280b40e29496003213003983c5004206104240041101030112003c4d11b03400d840005040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 52470633 1250 52469383 52469411
    0x209030609070e16050a0807050405040903020303040b0919030e041107030c120809030d0b1206090d0305091b0f0f0616020f040504051e160f0509090a0c06030b0d06 72
    0x1041598010350000d0f000e6102c0180c4242c8814041e903403100803880410132003030442c3c0580c284036070040b510302d450351a01c2d0311040458280c4205c0c0a0840269102000703000c2048142c1c0d400c1c03a031003c03a00c0c0040c8241e200e102d61003804090015405024000c00b01b10151841d200c0f6000391040e070a000fa100e550704c81c42440c004002984030a000d484141a048030350941c54811007500e8069044003000314105482d0304c4504008081071525550703c40c8041d105044040400d0007202d1140c030b000000b60141c86001c000203819200000c000c03c0c41500102152079100c11901c800304105501a120003440c0015200403602d081e405142c0154803010128107455014028900303c40c14500c00e0729801e0007580c42c8001d11040d20360aa50040954101d04812268440c40300c1c104504081d00c0030443c0c0c00b030105114400c64400320f0341c000c180c10800d822814041c500b00130112680204020005001e00c01c95a100c4072004180c0780500400c050301d0700300c008403640d00c0070311003210340350001c40400c20381110460f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 52471883 1250 52470633 52470643
    0x6020f03090c01080108030d020c2a010906030c020703030c030210050c09030c040209090a0c12020c0105040c0815010603150b040b09040b0616020d0f06020c0a020108010f0b090409060209030609 85
    0x10351a2901c640b018861465100b101c016048820020045003032604200b2890081d400c410f8406205202c1d402c6070301d02c2c410400e909084051014409920504185c60004210300102e40083c0c06040c1443c104450496000820a080700d0700340c903146014519910b0704909001048018030545801e00c01808111920300300200041131084046415031311000090000741d029a0810f203500110f00d1000414684098008100c24401440c00c2485800e505030f010040b40c20400e10800d840e956401000b08104007102442d0280030000010001d80c243c0c0c580d01842e0140c14001c1d0804c2545594034440040500c40920025000c40100c0681362501c0d4681e42c240e541220098600c11414203c000d24541032460407580e440148180c3c0000703040c450380900c1061144440100c903000401781300c110110342c1d1840a400c80c00300c03200180803001c01c0e03800010b00400c0c061f00402c01820082004110407290704084949100c0700f550003280c5900300b4102070009004070000d1f241c0600400040010510012803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 52473133 1250 52471883 52471891
    0x901020c01110706390e041a04060f0f03080a1b060207050106050a03120f0e030304090509011803201504080d0c0e010e040b0a0302150301060f0207060c06051306020a090e1303020703080307090306020f03 89
    0x60102b0080d90303104100b145d181900d1064004440b00a41c0c144007040d038841c000e2400750014104840d501030390003e00c241360300c1ca25030140d0f2000e901040420420400b1b004403c01071000712100c9182c1e504548660000d0010b012070f40c0f05021010a1391041140076828000c03031390b60001d0070750340c542c0c1c1d0707a90b550000391508840c10b088651030200d0400c00b00b10090400c50300340381c041c0c0d100b8596103800100c0003081e400c0c104c2d0440591284d051150060250440b0061080340f1518005845174544000041943c4091500c80f00340603100d800c0036002c0e40e10204c25004c1a10031240462810305000c0403420105040d0400303500300c0a02c5540141140c50b010017103040710036039030381e008000318900c3c070880e1500303107d001e400c000130040c0745d0940100380385800c00f54000300c201c00e88541240040e138400c0e080307a0001e5903c00c04100b081320100325584c03201c03401c02d52100165500020300344040e54001e458201c2800700410500300400440d0b40280b007080d40724007569200108540e030355980c840d20884c5400c100c0d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 52474383 1250 52473133 52473139
    0xa0f060b0703090801060b030408070501060807091407020601211511070c0602030405180a0b030115060f080907060f020a050d02070f0b18090901020c01110706390e041a 74
    0x3c2c0b00080d48501403042c6400c866540b608181141c903169030310281644422016680c03507403952004900540144203d6004002e00c41c8005040c0c00c14503100e05070880010582c03001d40d0840340040003500c510420b59800f15090440900740750410b460100c00a1a046070240740f001e26140d50070003030242e82c10040c045070340110113818001da91000308913079900c81c9000d49600800c650350302e8141126858003880d00705050100c0410b21081400c0840d007160b003103203240b4a00320100306c401c1020542003800105041c2161a00c44600d1500c2d9907071a0360b400b82480365504005060852400b064800c1c0008181194024140c13000c844444030020f42c2d801082c012401c2d42014903500083c021000000c580780b5885461078a0034181c0360200308510390300e004005016954080001826250081c03140020402d8a02202600e403146420410116560709200b1154803a80310080949484c000d056546503840459801c65120019207044954410104c41603412506213002c00001641602107189420025 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 52475633 1250 52474383 52474397
    0x150906140306070e090714030403120501060302040812090604050d050607080f040b04030e0f03010c030f06050102150406020d02070b0f061018061b080c031c02041a030a0f060b0703 79
    0x45401c06486010036a40c1c500440d4942c8000810750410203403030b540c80001d03418051844002c802d040200703540119411000282e0300b40700b4103e203680e24442d80d4090300042ca001c5040c1420510745036034a90005d10510110140415031071000e50710304044801418014003640d00c036081d03c0c0f0b0241e50392a07096a9400100c1e000c07400107628001143e003a50f114036048407403107905458689041e9002c0c4c0744101c60340d41140b901c45c508415038900b4001e81700028559a00001d15044509440b0104d034180d41119046400841d4010b46201c041240960041e070401d00044c0c1d40c00282007440004e1040c00001006d2094400070890082d0040310854404c141c05d849071000c000c02007070110b070607240940024504c210780000a02455105110b080302070b070155110141c3e0703a821034940324003d410280c240000c036480011003000850044d0081d409000031402d0960070541041e0784440d0300b0442d9014980000404000038501e2641500145070b0305454200811a803626002e034500380f5840000150081658 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 52476883 1250 52475633 52475669
    0x110a0507050c0105090604180e1e060f01050d0b130203010603080301031b03080d0c030213121a070203090405040f14070504140f0a0b0619020c0909030903070306020d150906 76
    0x1130360488005581c0248218909410038019000005082c000c168005680b29591800280100b104c403200b55190403200c81707407101c6c040c899490300d2402405145411101070040000d074584001e0040101c2e4000741c181070b90b80d04e0342840d154446142c3c00107036156080007400020304c0b1b585401141680c0c0a80b503000c1c80c1420070000b0000a100600c030007000c0800030003031185110700a5200c0c0d48095103514015140443e001a0b441101a10790001103604007409000340401001550f184000080303a0801c00300c92500d004042c0d02d034000c880150b8065625200090304115903041c1c040c658950050098507140045e071249561003009005941c01a07140c10003940c00b0100000f0000c0c4100c45074600c00602e41d440d0f45060014095440d0701c0340d04020140b242d1502400310a44459024520b42d0042008444407010402c0142d00544400000e42041000e40c0f12601c000c150078050340e8011401607074030503840e2020f1009101510616803a600310820108100d25a50418011152152402440d940b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 52478133 1250 52476883 52476887
    0x120e040203060d020f062205040b01111903050c0102030a05070801122427031d090411210c0a170d0309020a180903020601150c0b0a110a0507050c01 65
    0x100580e100b6500c0240c0d107010030010314241c0c002580d10341c4081c020345e00300441c1202c030300d003040798502d0a140d0340c20f03071218140110304240c03080603141c00342403900360154104d8503050340d150803540948420b0020f41e603015000381401035086403480c4252200031036403441c0c0300300d07110010304040c0c41c41c1c00010313003e0000180c00d032b40c14076608083d00e411003820410254407035000148500180c000c82901502c03440301005503154800004101c1e0303043e1140000d0f9110b075250080c80401d031071507400050103c049d048001a11745241f46603105500c040d8000040303440000055060105100851940300140d8a040302002d010840d80c840c900d054860700e50760b0b40c5652550b100384e8003400c1111500c0c0d0103a001090a41d101790040c41754180064040021151640c100016207126001d4840405448581d10810560304115907030040c03104000841d070760149240e004000c0720820303001821785140c000c0031030744c2040ea907030040316081d00310361a8903130700c4240400140c070755005a001554640660400f03004554 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 52479383 1250 52478133 52478137
    0xe0c010216090e10060303020d02060a050f0703020a02010b04150503100e03090108180114012301050f070201111b030708011a04020f09040903030e070506090906010f1704120e0402 79
    0x1c81016030441414591a04014403148030030844078030414a06021800c81841114041c60003503010f088580e149540c0030340341510280050181c54500002c101504210f0b004a940118607454056a5000c200000f01e000d441d0f40b28045610500d4613903000d042c000c1c8500ca400844109074281d60f141c0c1e50034000141181c52040f8640715540080109050359840380c51200d5100005c44e295540c4003010840d01421511001750401c45100b501c00140410420590039400d80c413000122800141c0d00000024010b010b0032400300c00b2507202050101c116800303426281c0c0e030319000208860540744d10082002d01c0c6200900c50300d000380903d16011685913818050000b80e07c80c0c4500d070380c0390741c87c0403420f07c07000350701100d490402420f0074002c500a5a40b2401400c2042e8003e5030081112450319400c54204490360b401302748904c000300002d19813600e1b6020b449500c40402d0a03e41c0f4022012002900e09849a100940150070104100800c015114884404201c09603039203401c143d81c0c00052104038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 52480633 1250 52479383 52479403
    0x4140a06050f0103090c060e060c0303040b070305010b090a05040f0609110306010e0907020a020d0f140106060207090204030b0c0705010603050f0d1709030306042408071502011404060213180e0c0102 87
    0x8000328006c01d0000314040d00c4400030200f4090000384c03070030f40e4003404e090954000351022102c040c5100705000d0321030b40c140181800340513a041e655240c800b010000440d141414403c0b00d0280b41c850840e005841c0c41540540300410750f03a1818014900680d54140c415481220594085241198078230340604042c102c0c035100c1c51780ea400401040f121070302040070340b107045401211101d00c880a940c000440356403103280d0b25131040303001049540c1403510103070500d98a40c000001c241d10601c020000309800c601900e40000150603261794605803404d0880c05001036400240c402d02c20340c8101100e040c400140a401010316566040001c010f070244100380d064152610720180c0e0052000c10641e02e407950280d40c184041c80c19452016070003140000100c16542d01004843c0c2000f40100b1074001076242404515003948000c0140d070684240c101c500c9100600054041540400d903000514043d1140070050f000d40d0201403200380c41c1b250000c0c080e200500828209000d080440007940d400051290b00c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 52481883 1250 52480633 52480643
    0x50411070b0118110c060601140a020c0904080705060f0703110304020a05040e0a0203071d010f151103091509040f050108061306090b09030c060907050109031104140a06050f010309 79
    0x240d01e0001c003010283c0c0c007a01da41e02140da032451640000300e200c500810806840d41c0180440740380500000d41b10006048454005a004011201e05980d01140001804070112489003258440703040c0080c050103104002051841380700d0611503100c1e0a800b280348640010f2790140002480c00b0018090b90006860094214040b400b042c0803500d043c3d009030720490402001c43d052422541c000915020183d4404d0003400031a080089100442582c0e45016059036074060416600d002001c8161034500d1095104014039100400c816090a008031415204000c120040d05520420f0301d050b01c2d803210706018070072440c0c580070446541d1039004080c103d8090300c2c064107080c2c0e580f00341018101c00240088940e41d03598040d21000400c00e02d2414000d200e48401552100b085000310391502c08090a054000c0e0710002c01040540e80c0107180d0420b6940c0f00500f0341080d00303510003180103408960014011031400b0400c000d12000c039980b0000441e107045480003007d0f2030003801901100d01d04440500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 52483133 1250 52481883 52481903
    0x804030609080d050c0301090f1416090306020309010209100c0c0b09041e0203160c12050a03020c0a11090a0b0a03020f030a02030f010c08181b0a0b0c010605041107 72
    0x20800940c80745403403a00403426075190003208040303030080750303012545d99520a00c04001400141d17014850001884034407c010131500d41070080b01c41080c8801000840e15240381c5010903030301c9100700801001954800300540d00c9040c1802d5141c080c2d0406200c0e40c5c0211003030040c66000341c1c464202810901d8024104a060030705240b800300d0307180c1c40001c885400c90346070500f48507020b1100c034019144510710b02d00180c903030a01454001043e25032819140c1000711560f102e0010560302c0c085400c800d0b0003403d00d19517541f5110000d5001c0d009241c6c2c07850301da02408404209110011900c2e4000440844106a030b07642c03008640c408030307888601029081413404c4810f0005040921480c40000c03001030441e91340d5209940000e1518801e00820b04080c0d4480b25a41c01c9142c11450050300301d811082418000026054156500d803e00c90410400720a02490400d40e0b4851740c0405000d44a908001c60f80d5985c84119240a801c25100d2a1701961605d000482c000101c5400e030344210742e029078894 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 52484383 1250 52483133 52483139
    0xd020f0313051203073608100f112205040c0503040303060e010b040501120204080304120506010605031306020711130c1101020a09051002010b060409050f06010807080a1112041109130804 82
    0x4040450b88085003003803600030246c02c4922611581401d0041c83e814004090701d554400ca040300360b4904541e0b500c855420003404c0c0140d0307440501942d01c0f00059000160350400c0c10600e400c000041c131b510913500700c2c0c54101c41034000c0d80e020000f14400e0b4005d031018008035503141c081103608402403140c221901c6041c017052085611928404040e810050b0340075060588402c0031606582c03203544401192810401a4820040300340102401088a0704240e42145003003241b1441030b01501000070801075000800c0d00c100300c0c8a6250100c0c820004d00002e04c032198884402c8014005224408041a01200c90942944050088a24500265540c2582d86280c013092203151004100c0768010355481d80782c20206034a0301c1c00904010302c9515404607950910b07506101c2120405002c2904201c40003007000003880e080780308240c2001450300000784000031030f80f5110103400f03110903092584a400041c003081c0148080c00404e0a181158001d80e60349034141c50700d0401d0848400104550400d00c020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 52485633 1250 52484383 52484417
    0x7030e040c08010e1f030c060f0906030501031a091501081e0613033006050909060f04080a0903060e010504110306013002030f010e0d1d060d020f031305120307 70
    0x30301e008201c56045d1010507489a0310b00181440641103000051682d490404000d5401307600d00d00107100c0360604000c9541942c032403c198000d42e07007024010704820804580891001c00c003480d1030700100b00080c079255842d10850303526040c0d120140440f164030801c00c40118800070842c07d0051444080f42181181c1550b0107a03107002095070560602c420040f024400700030800401080c46440a03c0001d0650500d010048818000b8054003280d612000400101c4080348440c0b5801c2508140c0c010f4482c451a40e04a61000392904000d00300c40c201000d025840b8415003046003c0c2c2d100c2d01503140b48071481814560740e50030034440c15032651052816600f03260401100b8a01080404000750300341415900481e24014922900448580d91075440c5041c0b01c01c01d01400c40c121800d0700c2e00056030920401e2040d86042c8140e102c0d88a80c04c002001e8201d40001c1e0b048030701480c0da01b02d03880e8903441c2c2050400381e8100e01110036100c40c00303503c10218a90940d4422684a404103071181300c901652031043c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 52486883 1250 52485633 52485661
    0x3030c0e06310f03080406021209100c020a0f030f1e0305120702070e0f04050601060305070f0e0a05040e0f06010b0703050412050a020307090617030708030f0411040207030e040c08010e 81
    0xd0010784070a4800b040060406a250300903600507912561b0b035510300b6030028a00f0788151102500000103000c408029130303401000e1a0041c101d445c00b4205142c0750300004030f00c07440d00d0740548d0074400e1801c800001c000c00341c10180740081c05800070401e10150703483c6c400d91060712200010b00088041040418081c6000b41c019003040e6248119403c0646581c01c41c0401181511a130b11100310400411082000800040f40501180e10301400241030110004c0e2628102000c0c3c00b0078401443c10a40041c2c841f04d004c00000c00c1d000348140f00d102d0581590329110b010481da0240e160148a001095260404048405080c5d140d51500c2c0b52620f06000a43c0103951190201c0c0e450258801d000c015035800c100e090094600e10900203281490600e0b848203071841c154910009400034024400400d9800064030f41c02601d00c10880d030f8aa6651500e07020003290801ca50750b01c107202298030070a066000b8084c40c00c04409031410004500c0096003587c000741c0900c00d280301851140c00003241003500d215 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 52488133 1250 52486883 52486957
    0x2090306070809010e10020c060a0b060d020d020c070f03050d0302030f010b03070509031506010906081605090a1d01060305070e10051803010504050105040b1312050f09040903030c0e06 81
    0x1000040544170015041e051409040c0401e0a00e6008600c800712160140701381c640040d440002048010700d00c0002c5012409a0403400901d294041980170040c040ca804640c41c40003079200341c444281d11086514035030b40881c003003503aa51198100461170203000b4421240104e0628045000c646e02c2c00c40481001d80c0000c02000c2003110600074146940c03000c0007540780c01c5e4441c1040220a00d0403d0005021a41d2a0702ca41d042014076800c2c84286031401d81c082a040e01586402076881180d0307004110f80c201d4513480840c10000010550520161480c8018103031080ca07a81408180c90b0700004450001013180600e0b4030440d4078445400050098004000d004250000000f02c4151000002d0031520100d8040d07907240d4580c4200810403868419284c0c4c051519034951100c4130554581a00c010040700317030a4280070002809201ca219800207a1701d00000040041c0706a00da145802400382c01c5411440001c90400112442645001c0301034034140c080c0401050440010042c60342c1c014801d90b4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 52489383 1250 52488133 52488151
    0x80a0f0c080d030905010b0d0206070f06110307020109060605010504060e091f03050c0907030c051206060f0304051b03010c0c0807020a170607080702030403020109060c0c0b0c01090201020f01020903060708 90
    0x40002800c4505222601950b05981c0b000115800141003181c259410003801070301c00c11a010111005a0f120001d403040f6a4020301900024a61ba1420760018a4400805150b45502008002c01c056054020410316403050009010980e641c00064809010394001c03200881d02c003200d01c41c141d0404090040e444004040444a41d01e6003485840c14480107402c00d86545e044a68110102c0c1031813440180c011180e890308005a407014580242203008115074070120690601c040f805aa40ea01c040d681015007511480da03031b2b41450702d800355455540c01001240385a4004402ca41450306110b00c4044080340d4581480d03c2d825543c9006499202e110100e030f00114010000ca17070030206c000081c02401d00c400c0141042c0c2017038000a420a80000c198808642c4104010300041c0d90080c2c408048800900340250071031000e18205480d00150b401c21110000080340303602c404030b015048405180e0003070b000d81c1d0300e91111042e0a801e034420300c110b854041d4482000704103554865420194000c8140c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 52490633 1250 52489383 52489403
    0x609050d0507170c01090b0a09050907050702040f0f0e2d010204030c0602010618110d47030703081207050c0f010209040b040b010f18030212070e070207080a0f 70
    0x14011000d068200c0e10702000640e032002e0ba034884d00b543c01160310006420300701010b5040c400030747d2000784101010701841340a81c41d01400725010714014010385201c980d0042080c010f158003900404020884603014500286c00d2183c07003140504040388030100101100b03500c05c042e029141094082001500c455002036600304070000110780c050340014050080707a0b00204241c0c0c81c14901d4010400e81c80c952000c0d59181c0110300c0640c100c0c0c04129103200c004144041103000e40742c0072428084600d140744070102010f85003100302d4801c094041d90b002d205408c698a6008034800241aa51056404001e120143c100250340c158800c0744074030355108806146c25894800031041d840d0401d444002e04072020303900407403a83d1441c5054000d07030361091026a810800303e44003c4c0001c10305002e50000a0030b000046000f10411014544218044e54018007600216018102050303a25940762180002140e42c002c0402d085503c0481c880307045410110040151a1080c1c43e41d04030011849c80c11100e42150b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 52491883 1250 52490633 52490639
    0x30708030f041401090f0311060702040219020105090c090f040f0c03060c0207090209030a1b12030c02041104030507031205120703020903010b030606030a230a1b0905010609050d0507 80
    0x4000900351260071500340303600c80f4504800907082580c03600480d81071100001046c01006481c041807012a0b400100d51820044950041a29480b07044806508140002106440400f109580340d42450f12540204201c2d0f4482128a4403540708500d803a41c0440300b54085062001c0c0580c080d034109001c0e6000e1030802105654844a0101355403044503410303112240d1662098040c000d140090840314401e41c5050392910005c0d031900741c03007007005003d81d080302c04180c440e44010160802402c0c0343d00907001c1a20341e07403d002d068401910310403481181000415184040500c003a1170459030312000500920f0b0665441081c0e100050700c074882002010700c05104181c010007a1035010320456200161b40c0c40d00101410709446192005034026448901030000e251400141c6022154000c545d040c20680c500008500004220110007240e110b040d81600520a514816120b083c82c2300d8889803496541d040c088003514824800d4801080403070700e04010500300100c0150a051003030080d1181a51 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 52493133 1250 52491883 52491899
    0xa0e27010209190602010e0d0519021006080a0c0906140603130219061107030305040902070501020d0603030206010608010e070f0804080903010908090111010b0a09090201170a051005010c051b0307 86
    0xd80480a502101c3c60110104400c40d020300c1800c0322980e400c80545200c0754103030000b41003440380c461044101b50300c8400c028181340c800e10019140007600c0100344045561101e0042e503aa454503015116074407071134400100180c29100740000c40b01d4207500d00c0c940116032020031205800017440d05000f10f80c400c01504c016030b41d01c00f094010f10300c024280602c0c0d90030141c005246202a61703410501c0c3c8e01402d81400800d4000041e43c0803240411409a80c5a1040c501280640180d590300542103003840c801108254021031950706807402a49c1d100240d03a600d038900005a4401d03100c0c0c00100701e03504074001881c2d1240580642c0315015884a038a81012940400e08441d51010140d030f480b04c01280d20324003507070300c0300c1d00c04a81e510343c9000b446120a0080069582c0c1e055109400c096036440d41c2c204e04590084411048110f5a21040001823504920200181c10104c40d40c11031912106000320b819802070745002c180540000c0144040510315503007401c810a2a1040c5606101c0d17402d0006040c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 52494383 1250 52493133 52493149
    0x10302160c0b03040606050d03120b0307030503040905090c01021c0c02120d030902090c07020901050f0315010b030403030609022a070f06050c0f06010302030a0b0a02040b0d02090a0e27010209 84
    0x201c1d140c00140c3c2d82c6050708080003240c0322600401e200e9100141503401003a805139606034103101902c0300003509010b0000203490032205600040c418000410002000c03803442c0e000e90f2107500e00c417064540c0c0c4002c0c0801241c85034058101000c40c2c14005c0791103a2414413440c0c1c902c2c2002c5c800b82014490403da400c0341c40c903200c45ca001180009844115010860404400160300318141144207070030720b880350f400100000e205001e450302401c41400040102d55003040003d40107941d03042d41c0055961100c0304001b86500c1101e0a41c007190400a0010301c4002e03910845062404010100440119024280341d0a070f154004560142c0306080c4003041c3c1d1f1501d0001c4400a000070b4590741e540d090201002800e041017200c181c045600050010401340e1408100c60110542c0000403822568031014042c00900640d04100741c40c12020600d11000405075004040349482101c1020b0180d95907481c0601084007112010105140d1608403158030309442070501c2c0320050000090305054500001c60f00c41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 52495633 1250 52494383 52494389
    0x10f020d020d1d0c041e02070b01060f0203030c0f070201170108031305060a020303011511060106090503060906060105041202061603030b1002010c0e0904050c0d0501200c0c010302160c 81
    0x140d000600680702d603800e1040c1c5110360b030700006070070900507440103542c0c50301030800c94103008949400704103801c034070403d000e000c40b0140800210340701d182c40d080c135a150b00d009006c2d5401040c4501c100c00c030407034000403c1d203110751100c08085252030160300c64111140c221820882c1484000d10303508000d18041c0102b980a4492840295140c118900780e80030740d001e550344910f009036402c0040c01c8040307070301104417030656052a032002c00301100d41c1000c4070300114025445400340107a80021130300c0c80e44030301240c0840c0c8007201129683d03180d0300811a11520160f0b500c40c042071040004128842100a000038154001031581342001044440d901014072030309070840c0080c3e83d42115040b070303103080c1d90840c2a454051008003d6007070088005425131488202d21481a5818000103003045000c10111010003030242c8000d8541c1110301d0050301034070f0300300000f02d501a20f848412003060729203000d07901502c20000081c060b2260310001980254426480416290040020302c0040341c0000c52038001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 52496883 1250 52495633 52495657
    0x12051333020c0c01030207050d0513080f011e0c08040209090703050f06040c080303071b1e03020c0a080114060405040309150c0204050c0307050318010e0109051501050a0302060f0903010f02 83
    0x30307440c60140d502e41010030554400b0706052052140360f01141c8001a199007004841c1440ca654407040b46400d070314018660320140c468801c42e4511000040b044d04035400d640d42036074805900c803503420303004000e5549203811200000c00700400940545070448882d80c2121950307058031601d0f62aa103d4500b03010f80c00c40c02111a42c0100140010401c82c604610001c106080103581035007403856000703100f10701150641144d0a0489404424400005240ca207010300441c41e0324506030841c94040d40b101c886000baa803203003290003030000e20380c00c040c0a4086440d6404c9003c1c460341d6144130030400200005170007601000208003022030900e01c08032100e6468406a2980c2d42c81640900c108004c1c0c5600600c143e450040034004d0080e400e4105090344d4001c1d041d07003a03080c1d202035070446860040c20381d83d00048080d0300f00541d14041c002d0106400d481d1402c2c07169004440ea0320b42043c00951103241c07000a422940401590005040b90341c0585183c5070024004101c0440000c42035040e60007050345d00d56 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 52498133 1250 52496883 52496887
    0x40b07061d0313050901290d0b0405010603090b060a0b0a11210304060507051204120e09070905040506060711010c05070e0a05070f020706051e0d0204151205133302 72
    0x8546003c0700f1760b80c0146100000082c4100c10145400141000c42c450000450800300d641116009a50450040c0c6803026008004a41e5103010090162551000070b444125116005c5082428001954000c1c0d611803001c05150010550040f9906201d00000e40243e0041d0380d0000d5140f0030b01902c0301c0c2c02c0042c404820b40c480c20035051074001c0312009003281013841410020520394400c0b00020980c000d400a2910b48125800c10b0290348248002c01f2103540b0024210801580c0c03500704c00c0714410340c1c01c00c2c0c408114550f41c0d1818803080c0d100780c9130040d0000380c4a001c21301e0035620816945c1c4d8104c0c864000d6907861584c032030946044440941c0d203100d296489004000c01d00750300070f15010110080b8801080014039141014011f44201341500f041c07215580e06000301e0310702c201c04071015045442011555160307900209411521503462400014580386414000790700c45005040c09000e00c003120160008a9607122070b284001004c6981c4500403c1d403110103200030100f441d00200700c00c98005a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 52499383 1250 52498133 52498139
    0xb040218120102190e01110607121103061c020a0b1204020f04150b0f0c03070602070308100e1609050d0b01030201091d0c03060607050d0509010f05040b07061d0313 72
    0x201020403041d103180c803160710521009210050415039000d01c04c0003400c1007164209000300403210244030103821400341c0f0405040c0498254001684028401c00b944104401c034401c4510015038401a02d0203540721030b113402e03048400c02d14500c034000c1c410310080100ca1000e6442c41c0d03240036074220000200250403c04100803c0d81419035800e90382c520101c400b00410405008804110151401010a200004a500164003d5000c01c40340c1e61016902201c0e101c640c2c078905400030b035002c40001c80c0000e8422001c00d0702450300300b0034202a10700006e0702000da50798411024803461a03904102007049400d440000d001e0320717902d40c19200240104030900f1a0740c1940000b4001c405960321000b00c04c1c0321011403034124100440f10b01c3c3c0002121364000e0f0390380c40700c60006409000e60138000d4000d0280400c900c00d070316004070040c424690281c81d0340c4a20301e540300007a90340d0b00035440303205000f13401042658001141a80101e07456415940400c542d59184000c0d1461900145404141040121014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 52500633 1250 52499383 52499389
    0x150e010f06120603050d0e03031303140111040b0a03021608030a0b12031e07020d02100c05120310030f17040b0403020109050906010e19080111040e06040b010e0f040b040218 76
    0xd028a014502c01885030900d5652000d9494032041881001c2110000a09259a90034821990441d200c115101001034a81c10809011907690702d00b680d0740d61030004000d46841c2004140c504030b4240b030b00014100402c1010a13030103584110300341c15000012a0880340001c0c8803002542c0a2a9440c4000480e1044203050200381e4590780d1500c92180e1051014444030710401512040da103220030b9099840e01c5051021580710194040025070215200c15400c4000d64400c100310f0205000c3c1c2d00310346144440d58112282440241c42d058569a4a00d1040c80441c03802c00300034284030710400354201c2109107000800d6581e00560011401e00c40c001904005540c0c0c002230b03034070103440102d40509081c1041d80000c0c08048842c540d55005921005107000e0309050494540c0080800034001c1c080c0401e0700140b042da6600c43e004414051074a8030100700c4d40d003050321462030b0b000e00c1a10340750204038000040100c2690100c88485e406074031001e41411907103075800906a1a00c0c0309041f00348101c460030070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 52501883 1250 52500633 52500647
    0x9090203160503031606150b2a0601090507110715030f11030a0e0703050d08010314150a1a0d0b0106020607050f040308030408070b0f04020307120c09150e010f06 71
    0x60700d152500c0581d00388029034010003100c1200d07080c01260001214940f420384080e0003048000510705000318070020f41c2c2c010f48030051070f140350300303030040c03c03007500c4c40c10503001e24080b4441030000d160700070310043c450404036034011500540b90703051151110002c4e003000745c503040311030304486554120703800500c0b01641c26008042160100d000c05110071145100000346500004240440c5a503c1d91a1445202e80c144205d1001d190050181c40741c2c0d0b1811400540b0702c0c0030a10085038100340d140039030b8400781d10208040c6040c403465400c4012079140d000558016140341c03c590f0060805d10b64406003e030741e8209030480050320404401c81380c2d40c03416001030b0814000425003802d2003400c105079650340d01c0000c00c44007501d90000d9030039201e40703460501e01503501544000030101e000c0003081c800e80c0b0000c85c01e040d100714400c608440400c3e4589074505048205604010076200301082d050000c08007903040100c4001a0f051001c800302d07074991000c8104135007a440031810305403055042c40326581c0110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 52503133 1250 52501883 52501903
    0x10905070303091403060c0901090b040b090f0d0807020f0406170109170703050a03050a0b061803061b04060e030a0f080a09091b08070314150102060603010e0601170304080709090203 80
    0xb140c281e21504140109448946c010a950160040041c1c0004560300411011015200d44004162039a0321035982140561000880ca4441d01e0054501c3c45640350409012615036030040086040145903402c4c003e801590754086039006440700302c0424010583c1d82004105c0c00707400008100c02c01d190504442604d00b4850b6505a01d10802601012030b4100088400c0540035180000e0142d8030510070400900c114000b0300d501840018500b80344032541c0401c814850400c9040e162944c40d26003080c80c10341c03c941c651450521043c0001c015950151101040c8008060156183c087c03556441c1078000b080404112070b81c0d480841c0400c040755010a41700098955008100041ea120b050340c208545a28051101046050ba0025100d54440d40020745100b105040c03138800b83c140240d400c04120200103100e40144108000038540d49014000c541254490b4005001c1990034006012080304040d001e40341584020000013036030341000c100c06c030020201e0103000030f542c000e144105810060301d10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 52504383 1250 52503133 52503149
    0xd060b0424050a030302030901050a02100203150f0102070609051e09040501090b0705120a020901031506020706020120070206071e050d0f0809120a030605030601030602090f100203040e0403090801090507030309 92
    0x3800f413000903000400ca504046003401c2190300c170132854600324500f807600c0103d0a8001d00100611010540c081d1600710011411540421100300d1500120381d0360301c5902c00c404c0000e40090f030401c031605000c050041d080d00032030001d100001802c0042840140c0640303049134a695503210100c1840208115160042c03a20310341903141000c5d4208030741d04020302a0020003680d900160411550303000c6d900061a00c2c48907040740412550300d140c040e489000d544211005542400122650b440d014a60204000c4000c9112801c000580d000c1c0038140c0c005000848202c4d41007000c3d203a40c0311941c0921246180304000070701210a43c01c4005007000744001415041c049100144030034070202080d07841c0b0400070310510f151220244401200644015480f9582501405001209214a03a0000d007410b001c10780750310003000d0b180d83c2440f050078400016400140c20a11003404550154917125070054024640b0018441d00d44406500b107505c0f14108485075805000e0400030940c002100c040103020103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 52505633 1250 52504383 52504399
    0x303070f082503030501090b0a0b070b04080906031801061401020c040b0303090a0305030429180d1a04061401060212030c0c070e041401060b090d060b042405 69
    0x103569103100480c041400400312240400c0d4558001000040800070900710020680035841ca824041c0080c0720a001c0c1110712070414120050300e003015003000b4200d48500081519001031511070840c400f4000c0d10841b00c00e07000304440c0c40b180c2c1d601400340d4021160f0504120035141c1c0444698211641c2e0745c4464000480b485000e07540781c1c4c01040316696aa41a81e010031405c40c0d8000180c254418240440d9000030454404020f006001001d80252098191146d14142b10582d00f15400441151000e041040801c40410050303502086100c13296000f916418051006070350b5862441008003004040383c2c20401040188121800f96180401040205d00b02d10350400c40000e4480207801e4220100100000c042030441210404450000c4106820340740f1840d1925075020340d4240907a0203445992032411040781415043c4100c100b183d03090081d0701d00d48001c8030244904400034040a4949030b80d0350380748a1032034440b4041c103000c00341e001c02003054880700381100b800387c04500d400190180342c2e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 52506883 1250 52505633 52505647
    0x110d032a0308010b030a0603050d0207030204050903070210110703050114040b180d03020a0c0b070314070807050d09110409030302041d0108060406090807170a0915020a060b0303070506190b0303 85
    0xc0d50b400c0c10340f00d0442c0080d590380d03a80250311000c1c043c00c2c0e000600c070b88580f0041c0a020741c0c0c0132881c1002c0e64802c403020310480d01c52992090f40c0e03024050700607500c8042c82d040d15001d2400740b82c12030040401305041e2442c41d0ba49031201404c550712807004600d04d0030b202041008011481061550104070316826808440c1241a11507540444104031000d0550000c1c01c042040d00800385948080d030301060014880c03400c40c2006014243d03441c01d47d094106000007050400d03004000140c414111659207904100404550401400f09100c0035102c2a02c50b070020201502c65000719038019000703440150381d42c0e140c07402c2c44004444481c01c4203003610101c0c0040c032030407501040507a0032540007c0b010500d454a8140000f15105500c0c0081407128801c440240110f20321300039054201080d12a120641d54072074820300158161202c074401a04010002d600182031544048240c01002e4200e900708452903407014580281034502030030780904a10941078140e458010907400c1e900c1170f8017445c14292 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 52508133 1250 52506883 52506887
    0x60a0c0206151219260a0f0e01050d140702060603010c020303130206160308090c010801060c0224040915080102090306040f050a0209040809040506120a0f110d032a03 73
    0x825441064460700c051816403078070103030400c61015024200141c1300940541440c10180080300444002190503900c0c22400d0714000000640e03598072196254a42c06004695089030032000110000d81400010b1000b100c1403142c034404c076403011402c84d80e03044450802c01c0010b40340c43c04c0103040030300c07d80c144800003070416800300030b0300c0d042800051030303440b0050144001500b034001c0003591a0922520f621207001d041d4000920350140c14480c081d00e01810304003004690942003406058049800d00c44e00200508003168101c0c200c1c4841a4022040450119032000c1a032050b032100da051038440100600584c4040920001400c4c41002185407003940310100e80c8a09000b0b00182c030000600742c1100031300506121807101c03198010260743c050b203004d140050054001e0341d00980140d03c1e280015200342015a800103200e2007020041c210307009217655000180328078079411a4050030501c040c00d00d40e1504810300728038520985410410211401000800e40d5481c51500c4080320040003400c0402d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 52509383 1250 52508133 52508161
    0x60907030615031b0306051b031303030b0a1401020c0922030207050303030c210403090510110609070501020f010b060414010e0d08300a0507020717060a0c0206 70
    0x80c0e4080004a44048400301e14200e448266101414009051890900c030440800080c030640b88290420020380d00c4002014685501071303000f4808c814810808100c01d1980b0344041002c141c071a14000c208030705074502040000f0702c2e42e0b0100c4072020501d41030507913568040c843c88502c440159885c01841c41c003070000e0151800c019030071100000b04041003206051003400320b0f502038003020741201d40d6414443c84110071a071241034085c000c2413a2141620a150f2840c41c2c080c0a1070301a43d800014034202003c00aa00c3d01c0c0c2c4c2c0004090100c021050300c80303c1003c0c44031511070340c8480042c05060f4588800a41001c1c00c0301c5020b80c4592401101072110b03a01c0106640075240d041d2000b40c0503485540c01620402001801c550b8825890000c910401c05040010110220081c180d0100000011340352035005000e02da401f058021850009188034500e80d008a038400074500c1180c032130319a142c648113642d80c902c060590864001030204600405103001e007013007800003480188071901e40300320500192 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 52510633 1250 52509383 52509389
    0x7020d02041107050a0507050a06030209010806010807030b040513120801060c081e1611060a090308090f10020a0308060901240e060a18050609090c0705150c070501060503060907 78
    0x1d40e5644075580d40d10302114180d5982c1d60307003c003c07240e401406085c03035641d42d2010300c5428482c643d1340710041091407090003a50310f01401a1900c1045480c1d40e801504c000354010010020161307030b20501c003066950b90003013500550349510ba504550005080420030804141d0340d40092000e0300f40100b100c16400032209040640007107030340b030f2100180140d00c00021481c8189028848002c101900c80000340d03654402c00c940f040600580d6006240188581c0b80200342c2c0c1000401c401a0381080800c100030020a00140c2c01400b041e003109514000414210450705c1c40d80c010703800032100c041010f070010091030b04800c04544007851585070140a00c1480c4806002e4904500500e4011407a240103000036480200004c01c0c4075220210540024491a0004500d030900d040210000846040c00412101c00c8200907205414665658a5800c1307103500a40086641e84584207600410b1f0920b0421203000f805188003080c2c3d14006030a185080d2041174100300d1003030300031405004c070841c0002078010403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 52511883 1250 52510633 52510639
    0xb0114070c0509070c1e03200d021015090b03011b080703150509060112140c0705060a05070207030f05030c030d05010503060a06140d0501060e040c150c020f01050304060b0d050f0f0307020d02 84
    0x2000040e4a01121a048223107030902001c02c02201c0e0b0b541c04480400d01c1d52403030441e0342c2198080140d5080d0002503a20f0b4415800c804c01030b416040c000f61080d45c0241c800408082d0003c9102c00d0700c22100c84641815948050004040300188072191f0342c136004020743c171091007101d007400e0750a240000d50609005040c0318180041c80d810869031031503d4010990b281040600d2240514100c07040300c1107035014460440f8180991400140c44a20910409010b90510b0703000700200c50540d91407803a01030408800b6199440148104184103604000600c0880d000050208241d490107003403525004000c0e03c400c40407410400103000b060300e0703106c1c40d5070b00a1044825013800703216030901a006050740d40004607000400e504000a1201e007080140881e5401ea14404072030139289801c583c0310181c3c00d402984002d0781064442d040d03200d28065030700203014400000f040700810f8005503026100081c01c6415400280c2c55407081c40c010f010f4004400812405140b0300b201c5a40020f258000401c00244 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 52513133 1250 52511883 52511933
    0x15020f100902040b090108030406020d020105010e0f070207080601060c0c060503090a0b1302030703060b01020d1806120b0619030506010c0c3305130f15030b0114070c0509070c 77
    0x819550360fa005040c84e900302505004007541c403004402e840394440d004100140c4100d01c111015a4814440da41c100d40c0c6417a0094090348580c1000980c80d0400b41c003500461040b40c10100b048102170003658002c001302c0d02c0c1d1116800140c40c20040e2201141d00a60922030f00f4404c00ad03e0740c1010800d5107078244c0c403541880c107560702e106401c2841c80d1031074000fa4061290100c04810000540e0000301f20032003d8088640660540108540c40c0c24500892052545003050400005000e030941440003107040d0400704040312035074041051030304811040007240a103503540f00340302034142c4500b980081007840e140e807003592191520794880403d03108414036001d407101d5104502c2c0c8040e849000c18031100c24269034665600a0081c03c640114000c0340a50b05c04150000ba950707142540002116400c2c17140c2d02e00c1410710340d000c0c0c0003001281003ea0501a141c20183c9400760034800600d60948074800c58032130300f4181418450b590030003c00450500c0621304041001c81c0c0a01c000c041a404405c50b1b1072 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 52514383 1250 52513133 52513151
    0x71a0306120f150406050606040f0b030606190e0a080c031905010e0a08040f0803090f0906220c0e0303090a12050102040b031303020105090c060301060309030c0206030903030115020f10 81
    0x3031500b41c1415289010307000744402520f940000140144c01a4040c0302d0601c030640303950b410881a440355200d0303000c0310035011904105441020025550100004244600300300071954a002c24146500100000480c100c082c03c5562a100240c0c2024060820007040c0d404040c0c00800d683d2181c0700d14051013003020180342d50400409401103075103900401d0a07500001c050b85000c8220b40c00500984c12000085480801c000c0300020580346250b8004043c040c001c80b00c0c0c0c05101c4800c0c0090481c1e81c002035010032410002800041d00d801550714454009010070030008014074612035000c0d8140300350000c100c12516640d802990300e040e140e0a40d8680f07080807940c80d0140c0240304a9010802070100802089800d4a090000007a0700340243c00038001d0307640703034801140c0f01d2203009410760b8000000d000501c603252080e07001c040310500c21300f01000740402c15000100a50011031345030b01c1aa000000601144070005500b25407403282c1d000901d166204800da0b21b032169404000840480c5d0f5071406a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 52515633 1250 52514383 52514419
    0x118110609120f07080f15010311180c09030c030a050307171b0c13151404020c06040803101203051210090c0305040605070512150105121008071a0306 66
    0x1001541c859203003168142184070460f40d84504162045e0000c0e40240b040580c1c0803d030218960704205240c1032401c2d51a03080d42e84083c60100d0b15820590441d500e02c1c0f030700785020f40c407203601c500a04a144c00d840d1943c02c0501018640f08036a066a4041d0b04904c202000085002060b1408140e2000540172003100c0304440102601411031884541a5010320140c00e141000c68003521189003512660600c0e0301d01100c0d00e0a03550442c684002c000d40e0040c1c01c0184004818408201c501c00800141ca88204448290700e000c5050743e003514400d8001083c04610f03a5980031041c0141811486108540d15540b4050124001d446007040034480b90f00014282d008544000301c0034081c0c560b0204031925074100005c0003040c00300c1c0c04a404500c2c100120706140d000700c0a0350042c902d080d110740e03525502c03030b8000d603441314561200f141440700074080b0401c02440c00307102e54403807900007a900d08601e2a0189080c80d041540d40714041008420701408911070418003141c2c4c2c810010f50b11607009099101300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 52516883 1250 52515633 52515649
    0x207170d15150503040215120c04031a01080309210106031a10120b07020703080703030903110f030f0d02040f17070501050f0405010807091703090316050109030b0a0905030a0507050118110609 84
    0x1342200c050007400308410030030b1880c064000c3e607000352200d1a0cc61000c030a020b400020a000c2d0400c0c0b070340180501d038818507111108412558180c3c1082c4507202444800900750380c01078004443e822000011410a600e07192095940601e000415004161070040e0311000c101d20b00c0409000803444c2d000050040c4d0081044000865015005036510540740c1001001000402d00403400101000d04c400d00c481d800060610520b6150b80185261030b0141c4644003040d4840e5002801080d02484001002d46801d00700c04010460784503207004c4844203a4201c2d0030040d2640145040c06824005010000c4288043e9401d80b0300a003401d4006843c0e24100303442040507680706442100020002480c25517001c4054810000150304a4141d01e034002d0503490300e42d0030b40c0652130000d0f040c1c0c07800b0400304d10164001a00007600905c0024a502d054658500b943d200b100b6900101b140090b514040000900c0f0765a048251250054840d03085642c0b0510b88904580752640720f040081401c00465031075060b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 52517989 1106 52516883 52516897
    0x110112060302030d0528050703090801050106051905090405091b031f11040308040602060709090b0d030807020f030c0703020108011d0a0207170d15150503040215 71
    0x3001c40d1581c0186542e0900b80c2d6031b4007000c420620f00d00d0341135224000d0380d0b5910b907901e5072503007009002c060090744000719aa241200420070940d1100954102c00b0341c1c9110140840142c00041740c1c039024040c000780d805850f120038010a09400104510110118403041c09540c2007007040640b1150f12042205c0e8400199a09078843d00182e441040fa1800d00310060b802c0903202d4440490b035422940041015078800010700c403900303810008901c0108034030101072004ad0401d00c045460a0340003c2d000301844516000304415a00910074000d0780c50490301144c0e200c0d4101c0340066650a1644006d0b07002c01c60b4040042100c1051280200c45685c01c0d0342200040c1e03c03007502d000002c2d44030101c261021803504010f91440911000203000c0360604100c0840c042207800c0b10384a00700c4059025003440000417a403900c0c1c55030402e056a40c00394040743d42d07600c0c184844010030110701c1005 = true := by decide +kernel

theorem cover : BRFrame.Cov 52338133 52517989 := by
  have h0 := BRFrame.cov_init 52338133
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52338133 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 52338133 ≤ n) (h2 : n < 52517989) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
