-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1674
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:10:23.80098+00:00
-- url     : https://prove2.me/submissions/bceaabd9-f798-4f9a-9d10-2a08d26b0e9c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 300899280 ≤ n < 301079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 300900530 1250 300899280 300899297
    0x5030f03031b070809101101060605090102011a09340c0b0108060f0a050a0b0604080601140d210c02040509060f0610050403111503070306051302160f06020c010603061406040c 77
    0x407460580302086d000151403801c6480400c680d094903084885030350043c4003013003000840383c0403541c0a028140c40403c08202c0d10303050642d1000402d001e41c400902070001964400003102264600c80594140102a04100d00080360078002c007402c105801c3d4800e0700c0001083c00001054040000c04521800540301055482d03180c09032840c3c00b074070001c3c103145006a202c2c00391840795202c0201030b100501d1610000d10700340d4507161740c0007101245403070014043e0b81c0c81c0c102c82020030030340103844c545103020018059119a9000080700d1460390180002e500904010600200300d0b00000d04c03134000c540c4c01024103882e480e440104100b40040c03001c017001017031042c4002c03c042400303c0c02c80856107002900d11909034041c130100c0c4050f0b9000725202004a41d4564050040b8144400000940741c00c2503401c40c034103100e030f0100b21944c005041009100c5c0b01078030707980b000b04a443d03010395196119071002440000d440380340503c00303000a41d040c0c1c640080841c00040c41d5180601880320229096200c4908 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 300901780 1250 300900530 300900547
    0xa1b030c060b030705181501090501020304060c1e0f1502160209060d080a080403020c010e0d06051510020705130510060c05030702131b14041e05030f03031b0708 71
    0x81e0400740e02c10b6a05004400002a040d01c40c14600000078025140760182403900031900d0003600078403043c4070f0401070026402e02c20761b40c001046400703441d128144515900080e02c1c0c45800d5208025001c00c64034440c80c51a0108150009641d6070355204950308a0b000b56005401d0080380641041b002641460b2407036000541420b6401d2900f08001411412205440c1d03107030603880d588100c00c200d000804004c104820b05905005ca01c0c242d1000340385c035040d10030101e400100c01a01300317000075151503034800114414409803411814441d0000d415400c1e858481d10300652103400910410303000ea9175100030100c005a840c800ca078800c090b012104000301f410b00100303e500c4074580704121a03501c4100304003000359940c00390700c03000c08000850200701214044403840c200703400c01000e842408440d81550f04814095800d80e02038546850500d0088000880c0702010f00c0304591256405018074000080300d090302200552248559031044911501c034900c00d180141b00b0a840507100b072105015504 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 300903030 1250 300901780 300901793
    0x15021506010f020f071409010b0f03040b25020d0e0d02030d050708070b01030f0221070611160305030d05070504150509010e060a020607081e010e091c050a1b030c 71
    0x280c8035202c0e1044440070880340120500c1e00806420110a4032110007901e55186003114119002d00342c032007091400d243c03030301803403203001c0c080944000d040c5800f410000344140c031209080c5a0310608034a04040850b04000b010752120159280f69000840450300e0441e182041c01c00403a40c03070350150040070781d06c0180d107044a25400c0480b0460710908200201c0000c11510302d003040c061030290101c0c04e0407401070300c100701800c02e400c00f81c800203a1010103241e1011030003103401e9040380c0301400d0015510002c6824581042c41d94100081c3c4003a2505004c020300c20004040c01c05120343c1801004103403511182664140614840d040ca05074040d103243c650144250702800c202031060500301d5910b036000e80002c0564004400080050340a5000c00442e40c1d0320101081d04610b900c1c0c4a4104144021032070000c1000500941d41d203843d0306008513a201c00c040001e5880c43c0001601140d44440303400e030040455006840440000390084011500f9421348402c0c0c1c003005625440f0380e0400c001654411 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 300904280 1250 300903030 300903047
    0x8281d010c02010911061b0d020d020114010b07020f0406180b03070b040f0b0a020102090411030a0f1b08090c03010203250201020a120e0f030a2309180a0b0312041502150601 76
    0x47c01d10044d4110101d80b51307400308a440c00b8000a44c0146c6000e0301c586d80001d003114002404584010030860040120038080d8040340d4207250190b5416036005c9101001c0740142800364401180e00c0d41014a0038a43c030b90075404902001e10490030313036500742c2c4d450030660061700550042d01c080100030b6804000c1484020014204515240005803c01c1c0245000408890b041d450390740201200100b04600c4c01d9842c4036601070314142c8042000540e044821202c4403162501494050018440118480710820015044810801002559245000c40c18092140e03403002c4407210311440c0c4003982c04000c0c018001d68082e104203603580342c00c1c241002401d0002c1c02224a41441e20b001c0c07a810b003055404144000c1c414000e894075440158980707070400c504509c090031440c0308811428012458a666a12030b80c109090204030035008580b2100044001400d080c1d0545505101c0c1602009a116440000d48100c0d10088441100f15500700c0d001e03a100e040390b000d040303941501c2c840020b010390700841c070300c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 300905530 1250 300904280 300904297
    0x2090f0603090f0d03020403030810081b06041a0702010f0f05030406180c0609080d05091e0a080105100e180a0b0705040b0c070f1508281d010c0201091106 68
    0x441d0080821a0f40795410a00c100d151840000d4001030103005240c2c00110441c0c010008d03d61100103d880d04072640d07248c0e0080709840c038019013840d0a02c902c50345d074901500d01a11042c0030341e500940202d602c1c20035036808821308a0100d00c100d1550241e050154020b160510056140d091a564455440b0f000030110940603803c00360003d003511001c518200c04c2074014044a44410841d1418414102d01d0121480324240800c0f00400043c1030b6901ca81c10104031810b02260410b40445604e80016032413076480e00541c40307562a00d420000c8a2040480c03240858900d00c12240442e122034a02c14036030b54000850b100c00d540214000000078040b09000d95101117240b030054141500c1c0d235420b0f82e90754042c410048441c0c2c000801809445500340400d03008044141c80814071ba40e406038060a0f03004020081c2911914001009800700b1880c0340040d941c41603a4010000360342c1c00f141e140c00c00100000c610345207602c2c04082c40c0b0f09a0051094403440c0360842c807502c1e42c2c80810030030840c00ea8000c004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 300906780 1250 300905530 300905533
    0xc21060c14120105030609070b18010c150218090c070b04020102120403030801030c0801020c0d030c031e0f05061002070e09070807030309090c090608010311220f0b0402090f060309 79
    0x10a034164480340e014260b03040c0c50201010785545007004051400c80003600441094014010400900b80e5070b40845298144118021200303030212001a585655210406070105484041c80072001780d09500038490b041700d00d51304007418600b007001d0000044003222171a600500411000c1d022400b40c03007606600501c144100e900980c4020403983d240e4205900c00c40105c2c4540d001441086084440b0300e0140c11b0342c200850030310450014056840c035207070b050700051554800352561818404c0c0c01000340b07031075100411000100c1c500490700041049611035403101c0e00d000081802c604d040e070801e4440344a181e000b4136040382000f502d400c41020140c10f554440c40342c1c40000860302c105001d1000214003d44418035101d10304501801a24070b03000c0d000e0100301d0031410034006240c000c68900d0540307401801c203804039045034010404030081d1866400740c00304020812100852650403c8440109226042c44038007111005d00040e0300501d1141940100d50460408503400c0070750166510118000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 300908030 1250 300906780 300906797
    0x3040807060f110c0c1e0307050d0c0321020120030c090402090a14010f03060f0e0903070c080304090612023105090604030e01020d020a0311011104080a0c21060c 71
    0xb08540e07a88070542c00c0d01c00c0e0b044000112076030700e018180306c03190700c0225442d2800c00052100094682401d4081c8a106501c190f000d44240302d01ca03035480c0042c0d40e0006045072080c40055914028200c4100d21800640c200450041043c02c03c141c030300b000e01410244182940c4650301104801d800a1502c160801c3e400d00c800000355852507002002049562001c54440410000061909980440d28018136041900812841c0302481d038030002c5403881e102d801c3e11504d03a600c4050841c8032b0f000000d8000c402250021032405804401003040711016241003041c580c2d03520100c030115065101c06035018140000082c4401d11101341013034610010540d0019801c04400c5480c21544151781e5804160b01810401040580010300340305070f4031003400100404450304100940c0c8081b00c56000701008074101285415200075013101d9403035100741118540b40ca403588119a074900c41c0923805d03501d200742400d00041c1e40b00c034915040000300200c0220114036040362140805800390600c50420401c3c0c81 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 300909280 1250 300908030 300908051
    0x306040e15010816030b15060c0a03020c1f02060112030903150606030f0209030613020303090a03050a230a060b031507030213080c061c090c0303020a1703040807060f 73
    0x38003081d6181e00100522040d5541001d021500e0462104101a001d00441e001400403801c00c408455000240e1782c9a0101c1c0c52045000c1200d6010b682681c07441449241d03022420181c0100340704118038410394106601d0040181142c0b040d0941c2130301213026030008401400b10322804d1204a041a000741800c0c5005940c85d601e1112030f00413128842103013580d0303007018070000d42c0c540070398143c0f0309103000d00b5410040320100103511450003901041c2d031007420540c07201c21510140242e60300308000509221480ba520704255880d4003410300c00300c0b0181842c400b9040d112840c40c8010100c03014100c01080b082c00165956001001d1107400340c0c0d890311a841c00701c5000c1001e00700043c403401c4960b9000d0380b200c000a034086408040c40e00461115004028109987e44420096510201c28181c02424615040342034200034412658050231402c0441004014150006150710f2124401c4008a14081c07042c0040e00c3d1500040e1001020103c0c100215400b0458036001380050b10101c03800010020140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 300910530 1250 300909280 300909283
    0xf060915120c090c0d360201030605040e010f0f050103123c0e030601051c0f080c011b020a050c04020a030b1e031204140907090915150e01080403050306040e 69
    0x1128402a044e1002448481026050045850300c450f00064a02541500140071510007110b0341c90904080c007046804095a2003900560000c19000c0c1017000040d0310798020502801e4940c0000d4125810306002d07881041052184604880d0010b8414416500c1c1900403603e0003c41e42c40c1600e12002004400001c041c84010826007100700c2030384074450401071001418090740288164425000040100565160700c0e075515140d0701007801c861110211403a00d82d842d40c41c995000350085801103100d41100300154402c1c00380c0c035516a00300b459207103070344000c82e91151142c034020001e0300210401d6405050680140a0482c410306011400e10f041c400862040f114018110841d40c21010741c2c0443c6003800d108801601243c01a02c42c0f8050030b12840789159096885880e008007060300000b40300611588801010344025042480040e44035106045440c40b18040c2241250325000c2c0c4495190044c214003108001c180c64062050382c942d14151031b81d400c014812034203d0345908410a0f8240b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 300911780 1250 300910530 300910549
    0x12082a0d0201090209010b070b0c09060c01060305060708100303020705011206150c0c061d0d03050c06070c061b0806010f110307030207081603051902150d050f060915120c 75
    0x2410703800040c0c2c600180c010800d010700c06a12401e00003100300003010102d2100800b003a80485221000c80c1c3d45c0001038045181d074807418140c00d42d90351070140f000c0100100170031154081c103030503a40c00566403100315544026004030300c07004004d41c2c071000d0300b085254040c02d14010b007032401100020711160341c0c511561703100e080c01c81c1e0840080d49400f5031208019698a600c1c0c050855407801c0c00c800c04c501e2415561031075000c10000e10490074100f443d0f04051282c81201c000c402d040044c0c81150820f4800903019244071042218090700707002c043c600320099501c42d07039040001c5507141d200340e07101c0000640e070081242ca800d0301001241c943d68410040d0801c01429103078071030341c018500c081c07801c550141442e00450b5400f0138411a0081000400e00008040d210012000c00580588100707100049004501c10041007058101058102c2c0007600c0f640001d20138449100c1c0c2e400c007a42c42070108036585104a82d196a0408440e40081880c1480c116000304e5401010841e104680d034440024107420 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 300913030 1250 300911780 300911803
    0x1e082113080c010809030a0c020d02030a2a0503120703032a0e01120501030809060a0215010902040e06040c050301090f0212040c05030d090312080c0d1401050a12082a 73
    0x10b000740401007855a2141490b070748010440007941c100403d6010003400c1c6005183c1c0a4810400001400150765041c0024920ba9620040c014040640062026404104803940c44032a103c0c0400001c0e05060109030012510300c0750480518000702030307405600502c20303207240c00c1802071110110201c8815043c40a007500001e81c8030449814800c030001421003c8901103aa160350a005c01003000807031180580703000f848200c40d020307220304460800301e24044030012958500d1100600000e18a0b200780d000b0015a01e084220b511590f40345000d100c03d40d080c10360021700080c0100010000003600c0d9002601020b8500f0340540743c080410f02c00c030002d0070140d409a07207031404907030300300101c0c07070200a03100115481c0e0a0810b022413540e2200c2650140001a92052150a40000702203662100890300500001601084403446450840031604024051603000d000364203130104020207003440d6a944107601000c02442c2c08051405c513a910700a40694024401045004c03004040c0309010b01f40281 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 300914280 1250 300913030 300913033
    0x306010f0504111c0c020f0718050a0c0807180504021209010b03070e0402040b0406180e0708030f07260c010f140609040204090326011e08211308 64
    0x89003400c0070401114502c288050740f481c42044588414100b0000384109a45502d4000460b98a0000b040c0d0900001c404019640d0040107808900745015003c01c00080940c14401c1240703a0701c8505103022a00180301070380200340c0540004003414440c8003007200c030031200410444040d940354045000c0c1d070060107207040c0c14050702007009000702c801d219100400504800400744d042c64090500304d6480c000d0406802643c40b00842c980303549581e00850020403a0181107415696401c4500300200f000030f0510003035000e10b460020300310b9000000e5031100510356041d14a007455070380e2120b200b915a90662980c051002c08080e01c0c10003150702070445540d90400200b4003111940c00081110000c140d00d004005082007480495201c40000561040e419940040c136220340f0704041d10480c0320920000302d003070b014002c191143c80030790a100b4100d46c000c0406200c1d4054060441b0800c00d15130080300d209500841010141c5489500030300c0800c02448822442c0c0400e00c80481000e0a4130b41019805 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 300915530 1250 300914280 300914309
    0x102090f04090236040f06051f0608090c120715080c09060c011418060c03060d12030905010f0204031101030506090711011d0d0909020705031207050702030601 70
    0x2a0420540d00d01102504840422000c8900e074001003800d07075000c1c00645141d8940300c41d0780070485501041440f420000c0840c468610380762405074416204500e089485d1410030011882d0f05140d286403481c20a080d8a20702e209074104041100d4030a401049004188115261007125480d9004a07014400d0351201501100341442443d100d041500a0103001b04500c00080001c43c104c214255055150200c0f885550750b001582c074580034150856011066140150900c80303040088400034410950715005e48440e40d4401070f6012040c00115411600031580081250010311105a042860b003481e060001c1c401e2074075205e15084420410b031030400c00768001010700074030116020f0f03480a9142441d0a008510700b601c089250207d0140660080c00442004010b2010083d005081c0c00140b6251281c1c1d00c404841046641d065914400c1010032824080440c070109035008070b400c2c17150071800951806900b0f58186d800203500420200800805210701801650103225490003400d5405d1004031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 300916780 1250 300915530 300915547
    0x70308010605030601020a060c0e0a0e090705031c032a02010f0b0906010c1104020d11040e1b190c0f12030c0f090e060604050d1505070306140f0a080106080102 70
    0x18a1506030000d9051001c02d1040095030382c4c0c0068541c01d49030748500c012603502c5100609403405280780e401a6070010200c0030104000101c0d61982c2d00c9403040108a4200c0c0360f641003030584800c1c2c042c0c80c0c02e08000f0f05045a5031b02e5402034010505400c10310740d00d1b007030b120101c0b400403815681804c01080142d443d010100700441e058003841030007030400c82c0c0a8209007031800010303240c3c051000300285024031081a424065442d9030554444110401d41406508040c0d40100c080303500c18060080c0300d07096400441c02080c0311018801980642ca2700c014034014020042c2c884522042213080c0812009001c0f110015100300404c409007132260035850303000c240303050024090f54803040c9088100216820114a0305030700c00000421a100c07051502c0c1c4a0722242d02140c0700740300d543c10542d0810342c04030b9004104491031141400a0032006800c01c000d4645d610304505560b45031041180080c102102c141c440d00c4d00190911140750004d00c40d2004665500d80f143c20758441e40d001d2301290754041103408 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 300918030 1250 300916780 300916787
    0xe1213090222030b2a071b0f0b0403060c050406052704020c031305010206070917011b0804030e0d0f080c16080a0b1006022a060415030f05100b070804090c050703 71
    0x7040d5a92020702d11184a21203203400b00c0320701031b00d00702800855103241d01210710000c030301c45c003c00b0306903a00141c0d8202d500c0301e100c1c0c1060781c81031100720f810f00c0c5800307a5851070500c54400d55042d00c00c50707079459142800100f02214219280140380e2039564001d030001d42c40b0754451009181c801c4409015684072481c4603400c0c404040950302041c15500700d04108480c044c0d114620001343c41c04400f00303000c1407051450442c01412483c821a44010b10726080c41c0015401400300c600c01c6210740d5030b0180c03044c0140c09010f020b40a08034024900c402d01301c00070000948610140c60713a000010226005070ba600021400786101d680d1001402d90000c9204009120521041c80e5010585000c0c514644d49007450003135403441400d00e81e494910340700030107100000c05010300c0c80303100c3d00050000340ca81d074540a144c2980c402d00145c0002203032030002c00f10b07002c0165000d0327544a00c0749103590080042c03800600e851140d0000c07504440d0920200404203001c0101d21914541d0040b5a5a06031034071050302e8041c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 300919280 1250 300918030 300918061
    0xe0105060a030809013005040c080118080703021914010c080405060106031e020a2a03020a110a030c0305060f061206040206070c15030e1213090222030b 67
    0x1d020300e108660610128040d001110f041110a02e00091400c25108038800d081c000c5c4403400781c0162903401c1c404541d0340d01da001503000e01e0084403003d10703460307440d034a007801c90b01c1801da070748142aa0500d0401c0400c1c4558090200b03117005c2e0064940c070342c002041180480401031b10441d018144100c903079030b04e03607424450000040c10605056500303040580b6596511041413061804140c0c071108440190b610308112078110401c01681503444070b000d8000504804080405000e45100c0c00325807980124458100c14040d50b09074028041207245502d980d9032038004c3c15030785500104078560020006806180542c0194001c0c006481d20341800d203201e10100c14042c0c02d06201d000c03070f1036032105d01440120f040d50b0003d504a03466691103115181c0520700341d5099002e5608540118541c00d61a078250304040c0e220301001044c0c0f00c00c0d0f011b00929480c14001d0320324008400c08000700c10310a1343d409500420042d2000310000c00a4a658204241c1c03003c46608200c820500600503c0000b0400d42c030702 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 300920530 1250 300919280 300919291
    0xa0f06180b04060b01091a1206093d0603060801141603020901031805010c020705040c050d0504050c030d1d030307080f0702180903070201231b010b10030e0105 70
    0x900e40c00c80d1a05010828094009402c15a8502c07000c0c5141c3c5c00303009210300030070544000c1941c141a040c0c1c6040103030000501c211203200b02c2c0002400c2c80c944040668070030784104801e41c02c446e00c1841501903900e0800c6141d8a0382090300b00c680c82d0808818a10801000c0710350f000b0a5042c20f00c1891400e41e000b81c2d420524544020f4103008014421b4070701180341e24031910380140c880403140012000f900c108100e42201d2001e1501400500106410100004a20b9000c540601e070791642880100c800801038040065801e1050750340000d1140c110581040c0507408840c00b00001c080000d0801d4070800001c00440d144200c2500045120010100c8241084029600305030058540041a1081c01b401002a11000440340704640c0c03108400d0504500b600300103030032031801e03107495aa00c0e4010325050303000c1040c140004071400c401a080c0403207400d4170b65196003060703014491482c0345049100408401d5496248402c0d06481e031040d004083c94060740c001c6100050b134903200d402c4943c007405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 300921780 1250 300920530 300920561
    0x1603031103010303090e04060b0616031d030c0f030a0501020d05010509070f120b011106091b03030301031a10090e01051006020c15160b1501020606190303050f09030a0f06 75
    0x4001181e00b180d0041c045070f006c80d016028076078683c5001d5004090394040031798456800b14000156502416003031141c01c2c825161320800b20345200300c82402c103500d00b00f1182c0c1a0f000c04158141800c00c10052809004050111038090170141d07109426030b003040c0031000400e540c8100400191901100c22504064039041450070102104801440104a070420100107a1a0654001300382d12420401c94021038000990311542041b460041c0c907200b1002031500007100d1013450385100c0c075011044034100d81d8000d540d52042c4510101210780c40f44001d06006000c0c01d221400a42000e803800b54812045450b0b000040900d0100c400c004c410f94560820000c41d8014000000345890703525100454818020815840f650b101d0742002101000d4400104120340c544180b0209043c0c0d1141089034001c241c00fa521207655200501c004903280d10700361195890210003c20109005100612003180352000701d80c507083d03107040841d181000b56942100c29422200e484400e001161241e542100d51111 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 300923030 1250 300921780 300921787
    0x1050f0a0b0a030b0f0c0f070c06030b010518120f0706090503060a05090c0904060209060c070504050c0a050a121404050c0a0b090a0311030109021c1b03030c0605071416030311 77
    0xc5070010301d080001d005c482c11402d00c40100e2483c1200710140c0d8100c00b01c044411341d98804070300d08904402c0484c42100003007810288c85c40c0c41503001d0800d803103d59601908107010360b00104100800b84004011205c654003552260000c000e80c14800c203809042981c940b555010f00d03100c107061900d1b200402203603a442c03030070080c8414042d011a04510003c2d0407583c2441a0300e503414501300910808518603030000002414900028000c1800d80c105e4404850030040d65a801e2000b9110b0b103d60b425000000c0e2007003055003202d42c091951030f0300403d40c040700003802c000d0b1021803c480da2410ba0b41998280c4c8514844150703803030300c004810040c00300e41010b80d04103210a0701054050500d03000043c4141c40256288195071000d40c405a20180c005050050a0700c00c0100b02c903d19203541400e50350200c40d4604a1510540519498200c03031745a903400703c044106440701030091001514841c1080f40146140f2801038840c0040c0600c80d2981e95010b005076100c0c0740c041d0071903a4100703110a0403442413 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 300924280 1250 300923030 300923033
    0xf080c030d120903180f0e01080a030509010c03090b0304060b040c092303160e07110604111507020d05030912010b0604050d05070801090503070c0602010504112101050f0a0b0a03 78
    0x120b15003000400701040440c03022101d18064070918807040d070200b000040d1000005101e00ca0108102c1290444080c0b9480c5989131000241c860201143c058003050040240321002e520a6003004400c9001c0d02d03010700c140d81c848541e8030007544280c0b01a54025222410540f091030300348296804031a4504003450740507d00f0181c0b401d9101c00b548510300d01a65400c4050b003d0b24140300d0b0a07103030300841e40c5074500f0030b45409448000f20810303617102c0005005030064002410001411502664001660800041c07403c002c0007040000505900040c801c03d11401c4011703252050900f04262183c0040d54640c0401c200340482d06003018010002a07040602d0100e15480d8042110261041564440c1c02d10840d400c2940c030f00701031540003600310741c40c25180400b400b4000c8058002c40c0c0c42032420002da50b0741c8100490076a1401e1f02d000d000d4011081c2c6200d40791404100c20080003511310014140c0240f00c14100782118021100c10031031410713010811246000c60b1040d4012031800f1101c46009500350b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 300925530 1250 300924280 300924287
    0x6090e070521010912020715090b030c04030b1e0a02070308060906040216050c01030f0c020d0f0e0301020a030204180207050a1101090b0c03070312020c1209040609060f080c030d 78
    0x86200d030074040d01000c40b401241501501c0414007240d0900000d009901d410314044600b070408800c090018015890085511444c0240c031982c0120700d80c3d50000f003541800c5152501c2d60014000e600030031400c1200000040a1100b1103208010b45000c2c5c1c00e0140300d4500243d0712500c01070020340b05510401810f0002a00010600d41042e41642c1202181e0340d1040442c000740300344109040d428080c1c40c141d0702044070008000c04511002c0e070342484902c44286502041e92401190223003da002084401e00ca00d00ca541c422207110f015162680c50040008003103403c903030010104000090300050184003100080e1580700444680710030845c600b03001520344036207808030f8440040c040c0c520000c1c0342941d40e1003060140301901864101c15614030342030744603076545d80c45104101c010641c4500c03030319020311140c0309840c1190100c0020b401035500d0390f204801a035010b40a034550250380c520300800c0741d001a10034a005407a860409802c00b5042c205520720307040901004601c42d61000c1142040c0395072 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 300926780 1250 300925530 300925543
    0xf18030b060a05030708030403050c09070e0609040f020c03040626180106030515090f010501080d030f060902030403020f120405010504050f0d0b0a0f140105030616120e0a0606090e 79
    0x308402100c0e06600d80c030001030048000740d4030866042c41014004034504001100070412603104070115801d0404480900804013000c41e02c50001c110305544e0710115042550050400381d10092000840c44500c580720012070b0800324071000c080c0c2c03000c03505212141d081070040703420b005540c0c014a001d0f881d1021820b0b052000528407140c1156001e2000c540b102c0c2508000c0140d42d010043c0c0c0c42406803244a1a03160904031240c943c0c500c9041c00c414000701b030604c101c605035268940034001001c0900800c0d005854030348030601d0346a0742d92000140328003052000e5802241b281c0e000d05600e41071200302500d017020340406098a181d0400041280baa040700c00c40c0c0440d01d0955000100e09001c03000211810181e55014040c00005c20030401078011aa003c030f4086a15000b0804c100c82004007004400700c000d0040981560080740451018034010f0110b030401c441a10f4190428400e0030b480c003003550907207040c00007a540840000310030404107004d180c0103405003540400c89100c04500305642c480 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 300928030 1250 300926780 300926783
    0x5030903040909021311070308010b120c03130f05060403140a0504060309020a030f1b0f030305090603101a04090b0933041e05010510090303030e0a0c0305010c0f1803 73
    0x240e07a101420119213640403244c046001d1750a00700120b4917580348000d826841004c0840014044a0000c00d0411080e416540d803c2d80d003e501c80701981d0344901420560b8005090141d2480c110840040000e452200300d524403441080584074908161074083e0440081c10100b440ca22014464161f200c0c1d4030102b81c5085800d00d00d40410a4051400400c0c45642250800707040040140c0401040c082d500e104450300014600245000300c0d580e090142c20880c003404018000740d400c0110035a6860311001440c0c0140f40c2c40b0100047c9550b4041110710708094200c10400001e000c5000c0085032494400c640c03141009583e8a0310501c0d00240d860311003100b58038101c50040c0c11000100d06038903440a01054030b0350107071041042c418201c419039603c4c5600010f02060600b004004038280c1480c84c0e684800b00e5a90310703074480f52800c565054014100c0e1112072501e0303200f00c03910540480d001350070420081d40190000101e2122846004003003c200c0c1d4400c10a2101400c0c14041ca00e20445070501242d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 300929280 1250 300928030 300928049
    0x210405010c0b060d1218060e03070902130f03050d03060501030605010806130b0316090510060818030c0316021c030503011e180501210218130b180d0503090304 70
    0x10350b100000540729441e0081c0180017007051044100c0040d400882050351140c00c61107500005954400403641084854622905508100c4080000408a070086d000702a41190003040150b2120030510804006605c01e5415034403180080e01c6c6140c00d4411030300508001c0c6070900c03a04d42844000b0300042c1000d8400d5000e108180421358a20301c10342d0203110200002800d50758000800801500c1124603405a05030492030040410300420035a00840c04442d165203540d14695a0714030b2040081c8c2c0d0861003c2d800d0301040200056204003840107000503002851455602c0080e801401004070100c05620f8102c03010a8418010a1f0800103407411900b00398940d1030400d03000601100041c00b1a4000520041100c01e6406061050340000b03058401b088490b140401c0022081e030440c03103c1242c0a03401c580303024000e0640a440040c46940a0503404401607a588a6034906180f00011900051802e08014607030405410a06c2030046039422880d2043c11800c2c816000c07a104d02c100d10444000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 300930530 1250 300929280 300929303
    0x19180e04140c04090809040f051003080a0c0c0f140409032a02060c0a0b0c04030c03060b041e050114030c0315091207051b060c0307030309060e0d02210405010c 70
    0xc1c0c01040500c01075a4050300c02d00c40b00c240d61511511503007100202ca8031039401d0004034404100940b0a0f60301c0384070600c1c0c0c0120054903644400c507481d8030612201d0104a40d0480707007000325001c2c01c00d0800070b01e00c03004104a05407038101e8100c3c40b08149015140f1886c00c007640d00700481e80c00f100b0324030707035403014840d00b60b04a5800e0000340c64414001c0000350031030350201d00c100740608003040c060040e5000d082134000c15911029040d07a103120700d02000340407041c803c106101080195003c8070b5456405440000c440d91000c01c1c0784038030072503503504011482e210300c01841a01048400d540a18a0903170081200311040c20000e03403154502e4030004100c681807000610039080030001800f2240d628241f050b078404035414071680b190244c0004040c9400c00d060660b0a40c146501200c1c9401c518401940c105809681e04a000c0c05140030182c6038107450f00b03940e0000001c2800071445a500c81e0b0001e00752120b244102010a0703452074814070740170346c00384400c02203641c0080e8158075655200c0c400230030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 300931780 1250 300930530 300930563
    0x50a0311010e040f0e0a15110a0807020c060409090c060e1e030a0f030c0c1a07060506030a02030706050a08100503031e0c030d0603050f0a0c0902160819180e04 70
    0x510744051002c1944d03003400403007184c3d20004500320743d020707014001641440e000b00260310f040e00c413020000740c9800030030840b00801c1071082c809141c100d070040c8156007180103803a0009215400540048900959562402040242201c0310740000c0c41310742443c50420003440d0010311288a5040c01d21803101850541264559040c0b000241039075100e04d036070768015001c1c10004c0141445e18400c485500001c10003084030b003450310101d2809808410a18904819551040080c0002404654051060200d0b600c0103a81c144415800790200f6a20644c580386001030080800a01801d500240c011140080c00b031514044101c86959010034140d0000e542080e420f5030452142e8402840140000b05888140000b40d4000e6412a4000c2c01183c0e041103c42c090203880b1102010000c0c022108204108000300c0340c0d03009400590140410007620340215100c1c0701c41035002a840e401c0c0304d46404504490720781c014641c0560f403813203400032044450411914640000b0040c2014005e040c12a05001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 300933030 1250 300931780 300931789
    0xe0405250503010f11250203010c090f0603020408060705090d0c030303201c0203042405040212010c0818100603080a03110c0a020103090809060d050117032704020c070e040507050a0311010e 83
    0x1407040d5015008201171820034174010166801cbc0d0041d07200100c0d2828000500d98400c1c02038800b03072030740300c009414941c54030740e0b06035015032020b880f1036000000303506083c002c64916810b150056010392000306041c19140d280c144003200344810444030103c18850b58600880071400f10b10403485040700140d490b1600d0070202c0306021400d44000c1142d0180c0c1014902c40c0b10742c2c2001c0d001c0d074400c2d108840259900c4410500b40d90405008500040210000803070480186501d20043d50144055a81d00104809103000b81c030280d4005840001e0001810908554144105214405d0055030f01e41020840001d043c0ca6440412001c0d04142d25841c11009002e015000c0f02c00409004003080c0e0786003042c40040015010074401c05038900c02c090341c030340c4072100003000301c8103a05007103640d212459030b0056911700c05201e2080b8440c0c115901384400d950a543c20000d05014010504043e082031070940340c410314101180d003142d40205c0039a481040000d041c0440b202c0e06003000d082c058482c420610114 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 300934280 1250 300933030 300933097
    0x1d13031701080106081005070c060507090513050f06120303010911041d09010506120d12180506010807081606030c020a0b1018090c0e0405250503010f11 67
    0xa40a03050031400041c0c1c42205500001c215410a4140d910301044001d0503001c0360001c640244c0803ca400081d200091000d500203580560a82049207506403110046560340b0a428111041c0507559400e00c0011582150301759407041c0200c0360318800c03900b2941201d440780410700ca0140a503889469010030034490740309a4015020b41c940000509030b00052034200d150003030312140c0a40d482d090100f112818145048085d00000d01c00a00507101c0c00076048840301151090182503c3e80c454100d042000010030100c41180284011300321941030042e854145502c43c1d00c00d120962081c401a985000da0f5071540046030041e08001401483d01c500681c04c09032031103401003824501a0402004210180c20901aa511076141d0700f190811030380700c0313000c40b2000c120180c42848007003c2002040214100300758018421803c0d2000101451202c1c90b03255400d0020148880c0e00c0704003031016080074850342c003881c99100c2c403c4c40b11094122002c0568865000e41c00e50801d411052141c1058981180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 300935530 1250 300934280 300934307
    0xf02060a090506031e0a0e0712020604030b040804050a06030203040b040b070e0904150b27101203090612140606090d15060f050306190b0a0e07181d1303 67
    0x1001c1d5070745092081a00c03084160003490f252180e084002c0303001c040035032180c002600140401009100d0910070303527070034401143d48120b078844410032011000a0b10410600c3c012485010415121801c0c030b4100440e102c0036400c900d0402d4410310400000c44c241c0304a554000d908012034920903141c100c1e0440e8580c4004c99495040003000c001d0004204a40c900c0c0c500ea603445503410030000209070201b280303615201c100100d0700c01c0983c00400410482c0c144482c0c00114440740e1200c016540c10400c507804da101d040a601140c000a401c01c005a08107103524403c2050b640f08200102860050f04150b580c0541356900900010070f00044607251880e6502c1c00f5a001990841c90f1101d501080c405840c05019442071040c0c0310100050500340064141d0150f00f4a6104483d8407511815010007402d00b802201d600411051300068804007094915000d03980544c0d030700c2c860f110074110f031143c54540359100400444000c116003881c5030005044d943c001d0251102c189598685040c2152590740f050b5a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 300936780 1250 300935530 300935539
    0x30e061003020f10020a1407120605010e0f013204020d0516081018140403031d1b0103090c080f030c01050a11092101051e01120f02060a0905 62
    0x18401014103100e00030040342d1084544810824001061140440382d0303603802009a44510515800174191034a6030b9801e140500464480d01d0b500c40000d0509841d500e0180c907003a60b9000103103e182180c010041d40204130440d200d0240d454001001c4145201c000c1450001d26884085400c10040403076018030039a000308150740b104030000009004086c107a90041300482401440d020660040d00d03018800c01e400c40030108080e18101101c1f603408011210584510765a00c40d00500d100c041c181d65024500964002450381c1c085070180341707500b40c80c41704031010303031302548034403010b89046c82140c40111000e1802280081051401502c00c1046410134003d60182203541e40707060030008090842e0103955802440701e51580017461088070418640a0270110040010346081d040040d4103403400310503031118074080c160003c451402c40d8010703540c08000305054040c051103a10b01c001d1860141035120700c500040245543d92604103c400380e4020302800005ca07000c148180940000f0005103400307031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 300938030 1250 300936780 300936793
    0x60f0c0c09090c0f030a05060420060703030e19020901090f0b03030409050613020a08040809030a061e0f020c07210804060e0109080a030801090e030f040311030706020d090302090601030e 82
    0x1542281c99500c0d0483c29401100085000741c928500010429415600100503007020f40b1180c90380c58001c10302070071160403031075a00107141c1e02d0b4803600024401f19002c2e0ba000100080742511a07030a00010b8482c0c007030201c1d840c1d800c40340541c1e550204141181d000d1603000580502800801000d401854400d81e4140004680010903181e01c0d0400ca124860403038481c444104000c850500700c0c0200010400040c40b0480020005414007004100100c401000c880301500140d89400c16246d1142c04103000600c00d20b04c6a6404415020354481c1d52010841075050050022901c1e42d28149071140d02803034249a8140c9881242c611080c011031038000403401d03030700c07900c80c0009012000b080000600141446100183c0a1800700d400240b0302d07403603134031402103900c8c003521040901485401c4c00428001080541000c0c280743d4000c2c4011885010842002c060702d208060410605034008401c0d5000744101d1802c66034811242c0007520b90449820f2a65102d903001240244540c0912003a03a01c1642d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 300939280 1250 300938030 300938041
    0x1707110f010f0b01140f03011503090b0a090c0b0f0d0903030603290604090206090f040219020a02030f010c02030313052a0411161e020d0b010f060905060f0c0c09 71
    0xe400001070300f4801e0b26910800102c89040a4440c852050f1510a25005000600c40028002d03085089040346180100f681080354490822880303043d1600c0c481d0a503182c4101041003200169907000f08944100e507400c040603052050b440f84502e500b552a056070f101c9684003010f003e81d0101001d9604010304050004403040d04141d405425265801a15405000540c051516000301c3c1e80304ca40c09080c3c0ca04100046041c405806078401000d907120b6000c5c00407540b0134507280182504c031503296008003d04a004e005050501c0d40f601c0304c040031a4101000822815000000c503900071520410080500c200d9091850501d500b200e4002c6001d850040f1082926041a81240b0301c4442200e04001c000400a001861403064180124a03241400c090f080032442002494402d40c13800f00888c0907642d00d540c00541d00c3c021004c011070341240d03034a0040c000c900a0001420180c485070418030221400c0c02d00040340c0340030701203c8074101480002d001e010720909102e9502c10800c090410000c41c05c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 300940530 1250 300939280 300939311
    0x5060a0b03160e0a060905010c0201030e010e01090b15030718060806010e0105010f020703020108060f030c130c1101061a030403170108031b070e130507120b040b06011707110f01 78
    0x10b1107510400141c10b903490481515269080e6001c0721140e855822000d0302e000010f48a440740400c0a9040c940d8904da10f1100440a0207840d045495080c0001941d5030140b42c000345060025182c04003011101101369403a8174001100e03400c0d40c062120188420003a00c01c0c040c050074098104d6885401004c000107082042c181c440d80c140c0314240c0b01c81c0300b280320160007241c0d05c80080c40081d001400c000c3c0410846d0410140c04c000010024090b2100e62440d0408210318920400410300029507079500308525940c442003109920081c1002800218901010704a10225510505400380c82c0007012604040c040d026215040c800c18249640541c0d441c181680c6940106116010143c510015440600d00115519046d20144903450100e6100c0710b000c40d0300c0c1e8821641c00c0380c42d40b03d002e0020840100c4042c0440c005d5200b000c825409107010b00e04143e03c80400703880c1c80d043c041c01c456421115201001c01c50b0b40318001c3d10b00305064204a81026141c024019a4451554079000c001081e0341c25 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 300941780 1250 300940530 300940561
    0x6150f13030309060216150e060f0904110a091401030e0a0b07080a0b091902160b01080c011b410606010c050a060906020403170702010207080102190305060a0b03 71
    0x948454036880d43da090140c0c1c0700c3c078802c8000c014508032600240f05c15459480003106201f1546070003026410003402040b800c0c0d00c043d81c0000d0034400806e002e002450240100354809003071010440c207105003968080c00100d194040c03401c040080d074504c0d94059100781e000d0a00c407a400030459844002600705418140790035241c4030300080b001c20000d83d220015008858000c00042d004146540da0030306542d0b103180c01495408800380c0c013040810504015581c0000d100c0b4000d41004150394945600d01d07203400e043c5007249050100005200a044440f14400300d00340d6045010850400015445600c82d03488803905c21351070141000a81c451412404040040100c05104a40458031800b0040d0398003540c80d14010003e1f405843d0560000d0842e0304079000d8544142c0001d0b090a4803680e03030620851104c4060030160354007050b410309660707041200c01d008180300c0e0000c6140c0203204c44070030200f440c07444d64107081c1600c403004907810340c50340060b100052900503040c3e500c1e41020060401d8402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 300943030 1250 300941780 300941783
    0x503040212030414090c0f031006090f2105010609020c01091e021c11040c21090c050607030c02030d0512010b130303110f0a0507210b06150f1303 64
    0x10880e10314056207500010488003503545400ca444410380c1d51030100144500000c002600045086c0042461000100040d5015a0071480441350403405e20000410180440c0c1c03044888408500003000007014000018600c0c2e41c0800c00005501079070f041c4240504400d51081301007510005104000c03c2c4192301002103548030b91041501c0000c402c00c02412000303070310406944a152580d024100400030b6003020a1644903c00101d41050340000040454046410101c0822981c24000c401400714903802c100c0070080c0c0e4805c1240140c41d85803610081c6990284600a4a0000c0c1400505000f401500180c1c0d41c01803c032544d20380c0c502401000d940052030741c104900e10900c00404c5c2c21211100b59900c010241c01d805a920340ba40d103041340d81e21000c4a012065000310b500402d070a08091200d040041d003d00020081240342c2500d12011402c03801c001c0d507192040e6102d8070002444a000d240e0080011208080d003202c44050318112807054680c0c180d04010000703000c0f410038000c0854001280d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 300944280 1250 300943030 300943039
    0x812090d03060506090a051017090705090f0907030809030709110702030705010c120503040c030b1e13020a030210090e1303120e151f090605030c042a0c02090705030402 74
    0x541c0e80c3c1e0611215000761003074654400320070300d4180000d041c10185920700c410246040e06007440c5100408900600a850b15015500080d5080c0f0142c240104000e800180bc01012110307841d000c41210b40b288800d0000401c6028002100744460764100305200181c650800e080040d036440d10202611580b00407400ca020303000e50070740099298004c0441e02d02503900290340c0c050001c0380d2102103a20f944000d1007140d15501e444000320100f0b4921440c00c2c441c0d2404c0c10281e404000304200800c0e0580c0060440b07100125180c1b55600580b03c200c8568103c0b541915588cc0080c560034003601c00e904a6000700b201041c505040159650b048001e44060602a4a81071103041d0290400c0d03090300d48404541e00d040d400300f00117142654404000d554024841c0c03410000030046000c00e40c0c0d6410b40d0360321001e80c4a45510040c0301c1c514080c000f40c4081002145e04000420001d960581c00800500e1a080340c001020520000076008080301d060040d401440d0903014900b0002c003802a420039601070380034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 300945530 1250 300944280 300944291
    0x3041716051012051b4302010507080d0c0207140d0b040803060f04110a110313030803222405220213091101080f01030c09090812090d03 60
    0x85041032000c003000c4980e00c0d41e50b4400c1c04522002e03c03014080251052080c0c404200a01041c02141806406d24003400040c07200100c071101c2146144d891240e014103034000038918000d501005c11074601c0820b5a080c00c2268486c4141d080c07650a50040703281a00c041420304500d40403d82d804107060701500c19541144d48640006d106005011000c144014803040e04036003c1408140400c001e10340c000c04c010821661040450041070a48040484010b0300071404210310040940098031550907005039001142040741c44030160003c48000d101c0580102ca0001c00715410700b080d803000384000f001c3e5262070011000c45103000f140c0030906500c04006e21200354100e0268201900500d801401000d003201e285d9032140182031010006041d080340d004a80c44a40e0011469501444d0501e60103522940c0c1e2008039040098401c00f8014400d2119524140040c0f002410b950351580640b40400c0b00020721025918021426110b12450000c144c0005e01c100b09000000051080c1e007058180d506020703 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 300946780 1250 300945530 300945539
    0x90601030318080d032f0301080c010201090b0f071716030e010903021b13140114030613030305131a010503100e0a080d110304030201020403031427010203041716 71
    0xa528880c01058419004814074000142c401d4100c41e0041d400250041c0d4400c692644028002c02ca46c15584449500480100005107080c4919841c4c0b0030b082c0000c0c40300e007106559056100030010102c04403104c101000c1140c3e140306812100b43e4060268001c61039051010070030390b490341500000c0001038246030502103070704018042c1045069058000b031142c0c0c6440303d0045410400c0e0214140c2001240f40340300d203c83d032240550420312440d01c03900545541044c0d01540102002d801d800d0081d8001c40c2031203104101c900c01015450f42515000542c0c0d264455815108030320085c002d008628003e681232162454000501c1c103e820480803079200d0746d000e00c407040a80307501c1c280b5911a50022aa45004030300044000c1034a2010380c840081c8419416004804a41081e1001d60040c1c0d40850140105a00015105907241170796040c117080043c00d0b0f44c3e031142034541e07015603010024040034102e0b0381c1e402001a940545940d005044a44200000d181d658038040c0c4049456032001800005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 300948030 1250 300946780 300946817
    0x1315022b08190209060706020c060601050a09170a0b0f090708242208030412050720040f05072f060f07020c03010c0507060b180a091a0906010303 64
    0x2000c291512030050598525802c01c105078451031440c80c60b66000c0000c001d036590fa03d00100202c500c2090016100e014101e2420700e000c600600c0e660501108200d07000449800a504400703e900c00c100079007020090300340203424a094044002c00003041c0c04107100028104000461007400a03004844c0a59942c8403101d0f580d440200035680b8840d003c0c07000c02c1580740d460400c10790100c4050b030b894803800e504e0055802486c020319402e541088010091208220b1110003d1620140301e01e02282885199218018016462800c0c2070090044200140709621550052400000079890420403071a040c1405083c1600b44036003030101c032403800759500186440484c0760995220310070080c00c1d540d41d8014500c19200c00504084154440c04110100d2680c00f40283c2e0504100382d91515288c1c4003074a001c0303003035444042d0704038464002039100748021428121020361140300c10602144c1c64510b4102207042c8455001d00d103c2c26203c0004102210f00700003621412680304c0e030b1310384080d40c0c00401401c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 300949280 1250 300948030 300948103
    0x2040e0a1b03090203070803040e070f0807050d0504060906141608090a06051b0a030c08070e03121b030313020117070f0c0c1509060e0d1106131502 65
    0x1100c1e0400354034029074207288650300090300d45201504031001c281d00ca507034107451034205502042450016070104051107500500f14088140c00d03050003403242c200041c0c0035209000380d521074a2001d5a40300010309006d21030300111030711a040441041806141c600c0c446001c041125041c04002100d030710003035494450700c5403600c691003107006012100c542e9542c0d4000380c0009046400741c4102c0403842e00f17051101800403c1c00c00850307180015850141c1d00041c5c10160018038580501c001c4400e40081c81e00c000c10704140b0b0240c21020150754038940a01100c82c4100f01099070801d110120070003844551032103404604034001d80364140502400881145c45c410102c5504002400c808a01403a880c000e14060040501c6280d880d41e9558460300810b050009840d050350019940700010024940c00c034040d410110700540780e01041204c103440d00c0303c9a090006015029150005940400800303c00c9a14082c2c90b40c03020007854581d0404000b55510980344080064200100100e0f5051580c81c014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 300950530 1250 300949280 300949301
    0x30506010903150c0c15050604060b040324020f070c0806010f03050d1407062f0c0c060c1c050409140103020f0108070e10021e070803070206070606030b0a02040e0a 72
    0x1e0400d62800c07043c0e104060005941392130140700d04440b0f0a0f0004076030418400d10322080d100f0000c0c841c079000c1c003004280c1d007059100c0c158000d0200030a0002c40e0000c103a5032011000402500b00162000c82c3c140020b228480c51940d11070000720b400020000e01c11400c02c00c480c209821200c46980b01d80b003140205a1070b100045c070f280d04c007414403a90140208186031125814030f81d40341c05c2c0314050311100103030b07654009105c10744032001a070780b810101080c8002100c410300d1802d103400c00290084c5030755214021528503200701c001040d5a844140100440800d5a1100448511003200b00001130000d4000d8080e0382500b50802042c1c844040c10850355134102d80c0c008084d0221f411a0700015142c0900113059001040160204022552181170411401840950050100785081411268104240d500300c04c15600b0070311041140030000815651032a070119842aa18081454403e004190381d41c0b000700500703541d030104a501e08042d400b8000b124100003000503d80d90b80d20000c03040300c004410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 300951780 1250 300950530 300950543
    0x60509120405330705010c0305040804050d020f060f0c1207050607030f021b07060f08040209010501201515090402010210050c0403080403050c010215130f0c180b01030506010903 78
    0x80050f850400f0010201e44880010111118040c40c080843c54582100d80083e11600085090800c5001d1040110081403031030200083e05003503444c01035a110300e2041b40d100b1070450141e40103540c2d401c04000030100c00242030954400c41c0c080e03c07188542000700800c0c41805200040602000b040f81260040759022029000c669580e040aa008001c4c81c00900120759007482804038402c101704030341e01d80456010007814004d00c1c000300142551004005042040780c14401e110050f2607440311141510403d00f04001c0014102d1441100b0a11078002440c0c6841a00b0100074129840d240c0d8601502c02855404004d40d840350502408080694000b40143e002c1e075034071030a030107143d8400b80c0c2000040b42c1c030500c0c103a80d83d100d84809070020703003055400c2d07001440003044a40c0c04103e1882c4e0800b000041007510702d00300c0c115801c0074040841c0545004807080b03600c8108110951000054041c010000e4042a41d0500075401004000c4c0c03140e000c44d10786400f00d42150302510400c03084a07031148 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 300953030 1250 300951780 300951787
    0x5090103080f030c0d0e16140d15020f0406030e0d08041e020a091e0501080c061917010e040b0f151c0215030f010e060904030305060a03020a090906050912 68
    0x101d00c1d541d55000621610308590107015802e04507809000d110540100711b40201118580e004484581c3c445a50110200450b40e00c615241d5440d00401503c1043d0031076100d07124424024010b6010703100c1c58480d03656200000030045495501980000c554408050032101804071220080d0361402050b81c014003912010400600c002460510240341e451000e0000c03c29640d0300d6410f881078480905921b9900280100c29106840701d500c07800340100740329030003070040c148040b010070800c4c412507900d40d0303c1c44e2094003007254483c0204050002c04076006482e43c515a074584030701c0c5090101b80c404561a05e540c2000c245220003006d079007401801d4040c50074070880b1000c3d04020308489811481c00818880b440c2003070240e501d130a8920b003940b551114882d9645081c600790356040d54143c01000040300c012051040341d03200c01d04010b40c0300d030741820006401d40328000026070054080d8002940b00d4101c0d1004601e0003025008008090700c200002d00268481c500041d03225892101441d60104003403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 300954280 1250 300953030 300953047
    0x80604110f0f092701021305061b0303010f03020f090f010b07030c0614040c0803030103150203060f0d05100b010305131209091815051017070918020405010509010308 73
    0x141c040d00a0204459500480201e000301d0021100411000051102e8411104407401004042401c40d4000c5241c9811450b006201c0901801424042d00003c9001000108031100354020200d02c2011240c90b503030744100b00c031441e40301400224090410003281c0340150802c0c010450044030305100c1b4203e140e0a001e003c035495040043c09804101626040101160013481020006003810040e41910301c0c260030304d9214143d450b40f04401c1c0d03030300c100010404590340e20118040d03100f0141c80076a582d1a580c0010b0448003048800aa000040c502003404010002415042060700300909000091840c070040d021298115075024801e001d11070100d0000345050400ea15000103820001030360340c2ca070f000c0b40b412907401109051240a0740703054035050003034110300c2c2030030041081410310281c9414581141d20f61400d101d2080c1d1450f2591035840540024012000580f405000402070081000b14100000007281002d9028924007000456141442d400c540e050342d820801040c6402d840 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 300955530 1250 300954280 300954289
    0x3110d1e0b0f09040816020a0e18030301080709020304020a150906080604020909010909081201030b010603051501020307020118120309140103051b13180f0516020a02040203060a050d1b08060411 85
    0xe5028944800d0880d46c101c801a6a00e00440e4050010178035040b900f85406c900c0d00352056940742000e070030760f84144010001c0490009981c0f00b903804012004d600c944561001c100207202c1c541000b40845045190303003000760351103800344040300c81940d5823080c542c807008140000c901c40e12070810340203a01040180040c04a6820000009200c0c0360031600d01b101108400d280344d28280c1080f00c604010b000104000c0398140501500f010f100740040c2c4a8041c4500083e41d00c0c8984040281030101140f5200700300c1a800d020b01000703001c600782c1700011002c10303e030045c0ba0980381c1c05049150401149028040c0d4860720915104049416443c1c007200700c100900100c81e0408034024110241d445070104100d1044c011401028151417070204900342d400c4002802e444005000c0641092501005001c050340001e00e40c0700b280e01074800595940b00c400114100b8425500450f40000b0180b6000c001c101b1320081c208006061021043d10040d2190310f0702c1c1c0c40b88810380e0080d00100000381303210050b261 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 300956780 1250 300955530 300955537
    0xf0c09030f0807050a0b150105280903050d020102090102150c16050309061204110103090503040b0a0306050a03110909010207020d06020d0209131a030312010603110d1e0b0f090408 79
    0x591000f0304210300c035510340c0d18281c696902100c440c1d031610140622595001c2181c0e800703e00909065040051260103002c0401150320840d0f001e9250910426405005600101c069034000307003514901e80c285000a8040d600c8501518014491081c0104c00103e03042e0089000c4c828807028213284c448021421340c0c096803068010346080c0000c1111400a555000c0280070407480b1541110b002d00d81400d0034072591101e02075040c181410180c0ca03000103200407003140c00b542c1c1c0b02c244d219200c80d94010228000c28580d0016508451000400320600000788040d8002220884940701c440c0c1c1c40c0140b1500b40c0c018400c00a411000c0c41c00e00100042058001d801c2d005054000141040c00010025144500c1351840c00ca11955503c48190b9200029100c0401c0320000c2d8003d501d884841e20031600e05030030501c100c4040540d03c40e510200e00e001442241d038103c6112500788011513184201d6041c01c070030401c00f00c081518120080307920382000d480620001d0b10050419030310359116100e4529035070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 300958030 1250 300956780 300956783
    0xc030717030a20060f0a0e030c1e0f0f0a051c09050609060f03180f030a0e1309170c0106150e090702011d03040e0a050c03130201300f0c09030f 63
    0x710103074200c2100a6013009030b58450090088180c0fa142880300540044400550451449400410072180d80b404001124051030081d000c003d5105400c02c070400b4180f44045080018600500400d4040020005a0a40014003c40c16100180c00310203240c0d6100515003942000715910000402c003d01c1c0180140c081401e018200703516000d10600b11481c55442220200c5100040d80410001414200407003000030705101c0045180c0209d14001a00d404a40c02800740308603a54080313514a10001d40044000030382c03041d0b0242415400402e40b0040760440b480d02d503490740c60024005500b80c0d40c12070744500407480d9168842010f0038103042c418030860040010042d50f482d0551409446441c0c0040000081c1050286032101e00301809000c21240180c850401c0d5401c00041c0440c200c210002c0b240c0142959011400d805410300c0103a4036440088203140b0351240c01d50100042095400c1700895080300d1103010040980c0700b00b100401c0300d07000005000007910780c2005000180100c0110000b20b03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 300959280 1250 300958030 300958067
    0x30e1503010e0f09070b0c12030901020a030e1915090606030f1203060b22080706050a021501050a18060506030a0204031e0b0c090411070302030c07060c0803040f0f140c030717030a 79
    0x201c082c4032026541c9e80c41641d505807180e43c00104860030503071500c40c0700b10004600001e4189002c0c511484101051000d4020781813510a204408401540b0382c826030a079607000304140500c03650fa040429104404c950300782d82c031315041031070150028443d1045c80c040d5104580801d0030844c2140b02460100310800725070803020203840780030451381d00c1000188002c24065550603592414484000c1c1440d894580101c8409141c200510055079500e54131010b881c00c90341c02c4111520309560311406403803e075100e250040c800106200f0000060b800410684e80184035100002616950002c4081034040c03010f07240c1a400710120b2081d0850000900710248004c1c008110728046c1443c03800594040c0c0d0040700035904c0018001038a19092220400a140c0307800c00a080400944416281e4840240b0003003d916070b4800950401c6400444a40c000303401001c41407810000c85a49070b80c030000118103510a2148203000503903241d091181500760070440c005503040596010381922000d41015440410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 300960530 1250 300959280 300959293
    0x101e05031903110729030f06040b03070e04060204140d02030c0103020307140309010e010c02031603030b010c15050403080c0705072303061e070e0f0d030e1503010e0f09070b0c 77
    0xc603c1007140c18043c205004a0f12030741c040c114031030740c040c84c0ca1001c50305401c242402005148150040510750007001918003292a8480000107400c0c240c07190803075000a1480c800744024003003140d000e03000b510b040144401d00c8140c058200320003424482d10080d89a40090700d02c458a51280d0081c540290850904070424a6030910b0454540c10803500642c43c0ea5403800b111030041004d0140440303022460018601e0403d40d61003403e00907c19203800350500d9240ca9002095074400c08080ca0510340180040b103122502c14640800b5150680341030b40000c1620001c1805464900c0c1100c2c40c440d0b0200003401c40c585040702c0c2e924103004000703c0c20011f40d04608880c1c0c9035201800158410748452490201c10710038213002c110f201b54050b06401c100422042041c41135150707690a0080400115200c2841d10a40c0c5402c4416000c0008a00d800c030890740004101c1440c0304000d9416295800a03a02c2c941e0744401800204410031150542180e0117010100700042000d0002d19080d40300c00c054610 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 300961780 1250 300960530 300960557
    0x2100c05031803031c050a051b1b2a03010c020316140c030d0804050d05040513050a06080d050a090b090901050d050c04151e2304090b101e05031903 65
    0x1172503510f801081c2c4196140c50030018005a2881803640c8040401d01c5101c841c456001c0a000d40e008400c03403800e0507003010340318410b03090f810094400c0119480100c038441256500c200595400400700c09406582040f603001c003e02d0010054400c0c85801c507614482c0156141c440700881402c2c0c501d041918001d508040d459518144008a1710981644504c881400d05142c802d2038000310114100c00c01100f48802c0c88241d81d07030032008501d02444580407905483d0021804c0060034580d0041103036214210514204d02d400034064510701e08a0703250059015982e1110000511840000c10350110914005010310b01e0600400c94540d400380f4105c80c0080c418002203004c0f107090440c001c80d8564840c0c3c0402070030200c4d01da044c000c014040610f00c00c0c00d2524800c840d0040e0100c07401c000280a9134600c0001e43c555900440c07280e5000200c0c18a0760500c0002e99514001d0340c0150010103400041120b0f00d4a40070318400d08817200580100084102c04900ea4801c0c1820b035400c078104441c0911048 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 300963030 1250 300961780 300961807
    0xf0c0d111306030b090f04031403090c0a0305010606090909080910090b280c03021c12090b06010f02070605030c03041e050c0405060d020a030b07030e070602070302100c0503180303 79
    0x1014000a850015113240c50404101c01c00170300500c03801d0314541d034600f04030010f80e204a09428481e200000191203446a681003406d14004052440d00049064400400d10005411100890300b00f9100e030f04007203071207441040981d0b0308144007901129040000e030215081c0000b0086104180e8a00011140d484050041990380041aa0780b000720720034410890400400c52052603000203400e01103114072030755802940324200703d0321403055100d542103412030780b078000c051202002040403810041541c4500d41403d420307800742c1d082400104040446000f050002400c50150340040d1201815940c40500d00c0c40c095000070f00844208805140c176064580b0084c9407a28920700c22805015043d441c0d00600c402c41d040248458440c0e51214124409a1145c00800003074907080b44003d113065070b42c1c0c00190054205200400c5451141040004040c0d40c003058810940344200c0e110b4040d0f041000c0c0845040401c00e00140a41e0020000a0300441504504d00c0301404007405503810f00c0c10812440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 300964280 1250 300963030 300963067
    0x14010b06130918200a0503160e011a030f0a0204090e0a021003150603050603030903071203020c0303030f070c02041d0109140f061306021201060906080f0c0d11 70
    0x2824007181103400d012441c2d450041c07098244840d00941c0150380c49407121220100c10600a00080320b00d079080000503120412240c0c0584000b5044481c86401000d00d00f8011200f8811043c2c43c0b000400041800e054094804c030803040701084c520b00395196942d01c2c422010000e070410081c0b6034200b0000030034290138060f0340070118100307015055602c1c10303006002004e000b0307000d424105480c101480745c082114258843c1079901c3d51800040c5a620500481c0c51841800c0171158944103401000421255400e258241c40d403180e800d0700d41048004050545e40e00041d039008821212000c00108024410000406854002400407030101243d06401c003481038004021215a5140c80c00c1109212540c950703204280d54180081401c030a002124513103891010f0b001219490048460b4414003034030f501920700709140b00b0341110840d65104009001480f10b03100f110045012000060b00b0184130349200f6200c1c8200d1901c1601d4080302c0d105440042c04d0113110404d81c0041446a201104440300d1238 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 300965530 1250 300964280 300964297
    0x7020111071a0414010f2007050402030a0e100209060a0e0102150702030a090803040509011203090824060d0201140a0504090212010305210f070c08010911041b0c14010b06 75
    0x4660b9070750b0130203d02c02c074104000380c0403038113114240000039441035202c1b507107101d8080e064109040e40059001c03082d042030300b66401140e020b800402130000e0490740354414280140351504840d42d51400e60b07810402d0380a00103015070322250603c00e6502140c0a9484a502c0c1e040500c140c6600601060550014080545e42d40c0010303803010070690b807040d81085000c009014680300450410f0329000000c3c080710014000d02402252207a041d03002c150141e808003011b40591800d650300c44002c4604000380c07104640203651b0720201400400d4503810880589040550180e4581d111481c1c40e1b503070820140e004450410803c401004001202003091024000150001156050651660400600c2c0c181c0140c202d0f42541c030716070f000c1041c6844040c210b8444001030748480303440d00a181000c82c0c4046107980003911650078114402d0030850b98905540800b02c0880f410890700001c3c07a4a015682c40c585101000716542030b069501085094808601028100c4004600c41aa0030f001c070b06030780c002d400c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 300966780 1250 300965530 300965579
    0xb09220813032a0f0308040b0901020102041809020108011d0708060f04021303020a080102040608010e0907030602070602031029090d06140708150f040e0c041107060617030702011107 80
    0xa580c122030000203c0d480081a844a1a094580c10750f2a540d0140c031842c800d2a0140100180c50422039000b901601c000b0500076250703c1d08811684101c0c0f028005100089001408080001c58542c003540b0511003804034210300e1890560b03c1f03100550703a01101410f0a0b52242e55160300301840e039194001080011a610a03400c103051861050010b80714060b00000426401400144903882d400001e00d4110b802d94415620075071656a4581d040c00c22540014040500014003502031000e250011800f07003000d060b40008180d558001d548039140c0070205100040c0300c480c0300da21205c20050203081c04000c024081c01c40e03040c0550f50355003141d058000181d0ba41c5070140410071043e03000308032140d00080c0c1e803528200e0b4842110000d1300e00700c40050034074803d03984c0c0e14007444450702c01c2107407816841d0040c008000c03028030100e04000d1900301c01c100b2076402d810f00c000418015100002090703c09204001141444081d600544806030013070041110b500c03030341100240c0802d10401070041c0858442 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 300968030 1250 300966780 300966833
    0x1e081314030715020c06070f050c070306240302090114010908010f0c020f01060e010501080403020a051605191802160611070b06090f16050903030d0b0922081303 71
    0x94641003801c3d41d581011074052041c032480c030030914040f0340c03254030208a2408903c4482c52800903580c034024510303008110300c12031401000b040306a40c02840b00ba10b146204000412903403454640c0032000d408000d4000d41540010003400385180c081c3e1a0040050401039101511482d4403403c42c0c10440510180540314900010703542e40501181c91304c0c8101000a001242c00c00b0149401e091040c071800f0304005807000010705140c402c5c400d074844030b81c0c0242542c3d281941918420107448490140c0e1707101d041030300001441012880b980e9400c0f0f0b81908441505068402101d40c000e41016202c800d9402c6500103040c00180a0302c510885500442015900c03089a420b00c01106c207802004070703020f42000d1003408102201d0740480799011008441900034503d003810300f101c480c02444599905403001142545000032180c200a03c2c000b0705031200c100307070f56401c10310707040001d401490245d141f02c084483c0301c0450000001842882c02210820045030b0b540d594654800c8135411228141300b1010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 300969280 1250 300968030 300968033
    0x190b0601080105011404060f0c0602070308061201060602060c0904091403040f050409030e040c05192105061c02300c10021902150a05030702010c1e0813140307 70
    0x721850141c002881d1000303091040909041c1e5a00c540d000701c0040c0115080c0c0800c41511a942d81c404003640510300355102c5601e4500903210318800c4e2000f0340b02d50217008008000710014814041203940ca940204000d4035903a14114984e80103180c8180c00545a00c5c510001c1962001c0051206009000440d0382d58a0008880c004019641040d4400c80c2000f0020700860b500000c500c4000c5811100040d100004010580b03a0744240401034600c0091600c0f08036603e038205010300301e0a490742e6070242c00300c0e281d1080c1108460303044403a0f690251501c21410038400c0f024151512142c8054001801e000032541030a03002e003c40f00c12604400301ca402d980d031456100340001d0f20340182c00e8840b03000200c240e601c041e443e0039401d5101444007241603035075410b55640002000305070000623902c44d0b488205060041142e8022510034016608162200300000c3c401c203880541d20360381c00d061808030a00c5410407504c0c4840542072200c4000f0b0791410300c002c55540500d5098164080c1c00071561a142c0703 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 300970530 1250 300969280 300969287
    0x60a0b040f0608060f1810030213020a020c0303070c0b1c060e010305011514061e0a0323191a03010e100c171b16030201020403020f0306060a03060b03190b0601 70
    0x3041c1e00c3c003030b0b41d03210800850380d00c032401b00e0b2072240c020403044c420642d141030701052012459032001c0d41c840c001c040011401645075005201c0b15503181c0c20741d07105c0801c8005143e82c0c0d01c0f03030840080048607004420000000742a000d0480d810948816610380d10314600500c083d21401d410440500306031030010020800244100d208004a24501084ca28070300500c1e00c1d2a2500b8000c0b40380111400a5607041090703e0400d03040c1c000320360504032900e80e6000940100200115a050700300150008a010080054901d8180c441d54580e12040c0221410241400141c405d840d910312a12803403041e854850794081c0540745690035081c00906902d001105100c040c0c65035480e01c00144110364403a102050701450038103610840c0f480400303c00c60200c40032000d961013420340c0498404000110541015419002030044a008031020400c1030160001c058941030150780c007551040e9854010000a09035404c816030841d0001c09035904220740f8507045001e0003801e40b080722002d40c0401002030b41c0d0380 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 300971780 1250 300970530 300970547
    0x1101050c06340806091e01230901030b0a0b01110a0f0b0c0c06060402070503040b1b010b040501060f0804030e0612010f0b190315050d0f1a100608060a0b040f06 70
    0x314480300404002c1c4401c0c001c0d046002c0500f800d409030000c00700045c90048442d03941d89151211100f40056580d59814503080b05600c1d148640c20700403440341480d03492500040c410306072504400c9001c40e640f111f07041d0f6001010508034143c140001c00701008101007080c41400d81c16800b4841f03801d1520740da4505001480c000804210a4110074801004001c07000600c0540c8001c3c00d031030050b919205810214a540280e034441741420000003024030070400d43c007072000441c03030381c0c01c000b0f2200080034403c00c0300340c0e1401d01400d000580060403001410344108500c503000b074002d05106030220f0b84031010600c10340c0b0450301c5000000c0f0640c0100940b2030008101c600409155502c5d50610044040403000108072060320303010507842d241c1e428030180802c2c1d0000001e0500800340c08245070b0324a440950380d412807a0039244162402070b140c0058203041503140c401c41100000000385410000262901840a450a504540d40c2ca40c0881d50a10101c0180054a070050500055910300750300201403c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 300973030 1250 300971780 300971851
    0x606100503010f1a040f06021c030b10030506042a1806080403050f0c2406182a0c010b100f2f01060e060102160509041101050c06 57
    0x341000100101514200680107490701d44014854500c2a100f840c902c0b401541c1024130008048400080d40540000700001b4070040301e8031410401030003a82c01e40860304800c0010f07070084808071030050901d109a12055001400800008140b45c8140703400f040040005c44140544134408a40488039410903104144016032094a48409081400052030340001800c010148040440c0d8200821604410b49a064030248201c80d8205509034174101540e001d2a400110a08000042034080c00d1100c03a16141c0d5646642401407a1110180c46c04004030b503541540000341c00740c40aa42007903502000f015103c280300000309040c0803000400140c030003c48104400d202c4000d42c44044550003024080700c030013100b20444410a203101869808c080075840ca40d100d075103801c0e00072460306450102d6a01552082c1c0c22074100381107284e044110f4040f140039407581309171103e000900144890b806504034180602d070281c00c14252030300451a0000030f0b030306454040e8040620040c000501080ca50009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 300974280 1250 300973030 300973037
    0x4021201180b04151a2b05070201020a0e010e0406030209010e09012d020a1403091b01020c150708160807030e09070804020405060a17011506051216170405060610 71
    0x1d814403000303000b03201c0c204c5c071915124240070090840c002040005031040903504000c1d041c02c41241c144040303445001c11841864007441c0c0004100a07a01c14401d50307002c00c6981d150121401c05950056400034044104294443d40341c0b0b402200513104e810100d030003400c45905225007414040c070000e0958035422981c4100389444190290184400b0303844000c440202240143d480c3c07550342003124250740043c0c5c0201303180c0d400018003565040000e44c03860b1040b1011844d00101000400490700e0700040010640d00c45404480c011075500d20300000e20080d403103541c505150100e0008000290f12041b00141c5269102203000018142c21141c01c00e542001102d000c4070070300e01018040d00c009406031020303000c1c0341d5400015116444400300800030f89411001d011220100403810f6001c1e041c407140088040811a0000541e640664155142030740c00d0031500d645666a050020710040e40a40b2110030428803c0c03031505407010381200c503030143d4040e00141010b07180c41003d00651401184011041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 300975530 1250 300974280 300974291
    0xc0302070213050f01090513020d030509010e04050907051504050a030c0e0603070506030f07020a080f09011b020a06051612050c010b0f06040611030702040f14090601081b04021201180b04 82
    0x84c3d40c0e12a690341500d17074581c030000701529049211080f9180e0040c0083d003110a0003d544103154000004e420000703800d980d68640312503203130140002d842c02940c1c0c24805500c541c4060069141c0214000102500c0c800d19604196031000050b2040d04554015100040142c0040c801c181a1201540d4401420340c010001203180030003040b035501c00101000080c130800c0c00402c0da16442400070919642e003085109840c0d0340100781c0c000d826403041012901140f010204444406e0f20030381080c002c82e800401410006107441015a81a44414200c400c1e40041004400020301c05540c80c00c0c00700d0032a5660313500d40000204880c04c41d9200384905100300c001c03049165250380c034401121b083d00c001e40b5020040c101950102c51940c02000c2d8000c1d80181000c0c040c01420801d5400868600b006400c3d5104a840b00d100c02919102c0a000d0701c4441e03000b642c0e04166407150a0011120007601810040c5821081003e02a06403000c2e0451b080044d010008135034021094000e0220019044031304101c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 300976780 1250 300975530 300975541
    0x8010608071202070305120c190c080d180c0603020301030606050f13020913020705030702010801210f0f0812091c02071202280515120612010f0c030207021305 70
    0xaa0416500d40201183d00018240e0405101d81e0a881032402d0400704507400d400d04500e88204d581050300400c0d4440007007100008501c0c441c10240d40c14580211505181180032392000024208000054442034410f80c281070000300d540746c0c03000082855580050322541180781c1001503851a41c0018850030444240030102e0340d4422002c0c96096074400010703900d407400004100680b401720041c00682c0d101040413003d00101100a00c40c0314400d0366040526038882a4030100c00b0146011485220010001c8200003820032109504103800307090681d4403400c05a98038899a8012107a00e10b040d003003007091100f1650708000800d4880120303040c040c2c0f1491000d000070b5417592144501e00303c00c0000c0003200d095440e00070f00c0c01109003409000300300060403909083d0841c1000d115183c000e01e5030480000d113006116080c0c40ca1f05010a0080f800c82e1103000400510384455822092195641c000d200039111231032154881100540e00c003d40c80d40340900400ca01010100d40c0d01d030029050408002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 300978030 1250 300976780 300976787
    0x2031501090518070e03031b1002031003140102070f050a110102060702031c02040515040812031302010509030c28051906080406020f0301062a02010912020d050106150801060807 78
    0xc6081da10001c045143d640c8061080341c4d4085001015034050100040291503c04001c2000c440c44d4074190480d241e69440c6108c100c100e22044902152014030143e0500000d650074200f803800c0201c0c01d00141c10600c0644034000d80042e503180031074280e48002600030030400031044c1580328075424000383c15281fa0030031003c1d40328030a4140071080c102e0394140b100380c0e18885a0545010b803401a02901d80001441d400d2141c1d80c0c828001c02e0087c0c0f10f00c1001749441180303542140d2280310a0045200260620743c015900b5400000b00140c1c14040c2d807040400645941c2e90310300f01010b02d0805e10146000403c0c010007a980560042c600980c0e4071268618112101c03403034202202c00614050f001c6a03910b05010000b40a1108222150b4a00200006020364041d01c41080c404806030301c0b1001e01c8480101880410081ca002804280d91400070442140401e005466281c0050710740082c032461030391920300315580d03908491000e1000c664a458465400034100d405022a07081103416414902c01c040c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 300979280 1250 300978030 300978049
    0x60906160507050a0c080a0312050106051e090d21030908030f090a140601050a1d0a020f0c120703080907290712030603150216140109080706020315010905 68
    0x100305004000034201c0400c5010440c010034030350050019002a80c60390800303500c0d01d500350402d03000290911184e803c0c540c014800c41c0c1c100d4545407161482c04072105841d03c441c1031400e10400004005021080c0c950319003425015110b4810f0600e0695001d0000441981406002d001801c0500d0300303030302c0c20014003100101ca4100c116114100300b00e90b200440146409c4402400515190040002058207000015a241a100c0c119240d049050302c0e0443c0a5150306c00404c84004582000041062194954010b103105480031070290301e4004e00c0c0c00f000345800011340b410a140e55000511400307044c2e010782810780200008014000c014545880251851114600707440206403480075202861048411038140c203034022032943c001c42403238401900500191005a400c41c40120700c0300c500041c0c0b8822a6000903c43c101d6482c288290349501d401101400c0c07040c25a90360b81c00150300491f80d003d02070161203108510241c0d60340b030004518804802c4010200e410700084030000e00c01c50b92005080e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 300980530 1250 300979280 300979321
    0x132919050108041b1703070203070b0f22120f050606040e060712021903050603120a2703050a05031803010c140a0903170c070b030c1606090804060908060906 69
    0x41c4001c8004c070712400d5586803a0391281d07840180341c100015040001001410101e8001c4007a95851542d407040c0e070000e4820610405408403040250040d9880307014508582880049040316485440c0c03c3d4500d003000c0d0340c0c0c3d419a401d210a081580c100300007048030b16030000c0141d0b0140917074403030104456074441c0c0181503d414400d00040f0407002d0b418581c1074400132107c41c42801050a41660003034024001620b00e03d009000320b1000c03125071913440701241d015580b15035516980b00a620900400e0081c8502c0c410411004514004046981000400c25081c000e1300035651b00c810a10003403264281e10124079001e641850b02c0c921400350000d100d006c81941020301c641e552404148100e59000140c0c000034441c40c01c042c0e0707551503103564401034446442800110384050761580344a081d103000c1100c0c5006200e80c100161464074020000d6201118441c10011491f00040c0c1d4420b41190801e41061000501e95a020011604c2c2007045130341154000300501924107110108400e098141040f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 300981780 1250 300980530 300980543
    0xb070b0406110310060806150405040b0f040e0c030d0306060c112701090f05090d0c0510141012020a0b03091911030706080108060613291905010804 65
    0x350070702405810001d003001955200c255640ba040e8400b8107a03152500030000082d000d030000030304500b0081882c0e001c25550442d0a070030f0034a0213042001803c0c241e4121a000b101c040c106032000c0c2c40380e00450690190392005440d14a0403c02850b1820300760100b80ea00701400c01c1d904202490f003181c0d40104d036a42129180d80c401c5841000b00d060300f02e0307008a05401615580c1c1c005410395104100c5816105a41c07414851833a0285040d07090750010b0f6a9070304039811111080382d495029071a4828054403e40c1030310f00c407181004402c400c441071000f41802959008040100c420a401c502c0300142807841d00c0c0c002280f001b034000c00d0082109010b40c40f82004000085204100c042001d07841d44089404425240a182d1402100d00a2101c0c1818000d204031640860460b02484049040e02c1000004040c0303581c802080043c0c0c0c00d540804400c41d19500c602e403e1030340100555201c09411035081417003000390740005202c125a14400f030011900113040c01400305a91060784c0a810941205 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 300983030 1250 300981780 300981803
    0x3050601050c0f250302060301122904020f01050f0d1508030f0702121f0903123b1f11030415060b0301031104020c011e06030b100b07 59
    0x20050340d00d4030940c1e80c08441845142909900300000248840020601100c68141d0b52400795045805802c0c900000754031400a02c014040440080294602b09006003003441c941403404402d100140000e40e0240014101c0d8800c00081d8104150344008504003032a0440c17030801c1654202d4501d000d002c924200068541140d46c00c0d21500c0c1d203030312000c1d110780740c1507940c2c51110300d1071980c0305d903c0580124002c2611007030501f40140040303560b151180004d000659500e01000c02c0e8001017504080460910000a03c000141200d0748034204540c0c810140a041d4035680700b060f54010050130103071507021b00385220320b003c00220206024101d20006149c0c002d0314502690f0700310141603035030a2200102408002c11050000e41c20040c10241c02c141410005252590089a2144024080940380080e5030740c005050341410350007409030b46014000020008001c1801c401480340509064074a5a20385005000f80700090009680200c14480148113052510340b0a84d06030194040181003007213901c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 300984280 1250 300983030 300983041
    0x1a0f012102030a0b0108010801090c0b030a0e0d0801181514120f0322080c0105091f020102030907050109030f0204230406020406080f040c090b0a0e0a02220b04060305 73
    0x440441020318103100199242c3c580280e00100134081c06102c3e500050300b510001a501c001803040c0301d046900241014502170400d02442400d80c0060104000a5a207017041d2030882c0c01841401d018198699030450b11b54988800c000c0c07004500c400065905190500c03080e840c0c20a414060304684841032078610100418001030804a00080d0740074041c0290b003101c11490704080000c1800411f003803010500b191440c0c01865148580e0302801101d17510014001d400707980118060507110b00000d01c02d00c455000701c07042071103080c025840b05002d81c0d004401e0000c80c1c0300074040000540760a2901401c2d56240d40c65000140d079040750f002e401103584014058405c280c4890340805001400050b410504007480c044000b9802886540c0008003440d000c1084a110b03001e1603030246030080c8807142424248007002c2d00a0480c04ca00551000e00e1a0000542003c0e1241c0703d071040301302110060320b460b8204a45a0850300303032107100301e40400d104002d02c08400d016003981d090700c10501d00083c0d50f80d640c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 300985530 1250 300984280 300984317
    0x10302040c17180d0f09091802031009150b0609100c12020a05150105060304150e0a1115031303050702040605061207020d030209010f0809100612061a0f01 68
    0x400d0350120000442c1000040390003402c24104548240c02211526144441d0032189004424103c10014544050410195603d03820102040804112400171130400307900183c9004814400840c81a444091a00c1440300009820340408103101c0e00344180f6104e0380004407035104054141d4460620115030350300440c805c60003000c8460340400c0c006140d910381f078170203983c0b411450000c0301c980c454404400010b240030035030b45040700c00140415081d0744556450074000560b00c1141c00d071096441d00b401445100030080344146601842e40b420b02c0c002d012040c020300210311100103104100c20003e201d07a02c110955106201500f45c580161107141c0d40c40000c024100b10381c0310a61103030007c0340140021040140701400364000d60201c4a07521181c0340160141d0003181d003918041042000e00403006401400341c554010f00c01c8044d50700d00007000750740804488040d0000a80f1900100100082082c0c80c0b00d43c004050250044503050001100000c28003a41110294100302c214401c111843c0035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 300986780 1250 300985530 300985547
    0xa0f0504090807050f0703060b04060e041113050115030e07081504060b0409030e010206060306090601230913020a0603060513021b010c020f011a1806061e130e0f010302040c 76
    0x14484e095558440d200071186682d0003441c00181c8a00d0b00d8404840244e24141c031410040314401001c081c074542d143d0700c0d210703001c017000740075a5004807982c103c2e5054031000d03104450180006246144514814810013021200180e1445e075040c1e01c006d1080c0928040002c4000a80c4c100721280251780e40e45d4070342200581b001c50006c03a00726042003003440800d500000c0c480c1c007814003a4210f40099844108155640e48280e92100e207507000b44005005c3c030040c40040d04134601d14075034010000881380b0045412680c0455000155402e41415070b4110728100d5072200c004c2010f480c00340031a0341081d0001d0140300b0341174000ba1009500207a816814010403044050040c0a00001c00c1101018080079480e14880b04041c10694600360091280342d4030310440c9444400043c000282c1c41d88007901d0305900c1c247c0601340561103075091020480c0303485014070705202144178001c03840d141d5000714503001c4900e22507040994504080c13820003010400070307055941141c0d01128086108008100c0030b544121 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 300988030 1250 300986780 300986783
    0x10315270f05011d1303030c110a0812011a03070c0c090f0b0a08011e0b18070f080a0902010c150b060403081c0905150c1b0d0e0a0f0504090807 63
    0x81c141002040301c0015a030140c0d04a61050032076801d079a01070b002a000c241c00448210140424000403400030a220f9802540d240b030603805e11810314054200c00354a0052140030444007c0d40c0040e000515031a082031090040880340741d03404d9651180280d0b0352041c00b00408001c00c02c000c141e00c25050041e0110b540008050480081041d81c90700703400c080140c044142c07080d0040426440003e01c0400510442e1004881c4028108031510450004000380c9400d013915607001820808a03203100c1e514907540f501a0351561035142450381100f00181048078000c1450142d14a0040750700f0150b604150b202034459404201c0c02c0c4120b505221600043c00c50b024600d811800100d40030040000520007050b101c0b0341d40c50304010600b42030400c50159001900020000e80040004801c1c00c2c40c01a4242d0b0403030040c8080e9410004a03004203484010f012010002c01e07032000800b01844e6400c0181102680019507401e001d0724141076010000f200b1501c58107014a90307c103000014444400305031002c8a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 300989280 1250 300988030 300988109
    0x103060b0c03070201090506270604080f060717010b12180f0304140301150b0c0f10060e07020c0102120a0c020613030c120c060509062115010315 64
    0x415460708100c1d5680c0020000f203011400245000c1400d280070310130741d81401040c2c81d0307201a156081c145001034820010305d1680042d020b00010038554000d00064402e502c085000700820314202000404184181c043c0b07103503907074a032801030200004640490b5502c0b400f11440341c0450300d0390010a04800158910001c1d140256110b00d6104203000c0010000c849022000c500180388210425088505105030440c1085100c00c0401071a008075001c0d000f035031001015540903420303081401d8104044111030805407035513550f00f40005aa02408642c10420368802000e4003010b040000c2c2d500c05401014003405240407503010004d40c410350711031100580c06810075840798010000106040d00c10b0004803030103040e030340c40454481505001242c2d51074003c00ca00e84c20780c0c40d11074181c0300c1e90b00010105800082c2008000705002040500d0079180820131201c200c03d14050a203500407d0b01980110304060921180d0034284030900f20300d200762442c44030300040021651091050401c50707042e03440c010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 300990530 1250 300989280 300989287
    0x50606120718060206160c020607060c09052b081b0a08031608070c03080a1404050d0e10080f070504050904030305090c06091c060f0608030403020f010e18060103060b 73
    0xc00d40d100e0401c00c0c480d1048109902c8807a1550fa09980b035000032114400c10359210030b94080b055200310390305130441c0c2c009030550749010100c0c0c4442d030a440c0c41c82441d6021070a40e8804000c82c0c1005200c00040034144080321906070940201030f43d66181403407003e00407d4000c42c49000c0078401744110b452111440084401508080ca40003a1940040b07603a0342c0180301d00d074901c80b82c02d0300402240d845510141d0f101d0705000c0e907945d0203907064a4054100e6413041d41d19902480034003042c10758107010710301550003011030001c0810000c0003100d000000c05d01900710101c04642454000fa805500102d030300f00f0000702d40e6505181194503014903800154020680303c2804107154069001500800715202514411f482410500c42c940c8550420f03581c00c454002e500070b03204494800e211000b584a810702181540c1500c0066060340c0994014142541002a0400441c600429640e2501e003080c00c2c5540940c0c02c441c0000d1440045034012079607000500b000608581c030035440b920191050101d82c030348 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 300991780 1250 300990530 300990541
    0xa050d1103070512030d0c030f0507030b0405060a060e060d0e0d0923060d02090a0306020a11060a060e060913050a0b0115180512030909040303050f011409010905060612 74
    0x1404461140d14000c1c000c21501040d5410704070070ba40c41048483d002546407070f401c045c000000f0008883d081e010540e4440c54007240d030015000d2640204c04a55010a03007031052000c00c030071900013410305c0e0710030b0034140c2c41000400c1e0840300803049104112041070300c0d00c00f8081800081c140c0c21180c0e2400b4010101107103c007640203c04102a14038040e540c00c0c03151940655005590810340035168807c030709000380d46803041c0c550000c002c00c040c090b18408485640303681d51016a006a01c0003004120021400d0044010801130030368008504c0c01c00340403d525140d042044800041d200034060951480001d049101e541900102d099014044912440315403d0a000c404020f0188115a10134018040a031034810b0152080b0125118490034015180104004c1c140b848504940000d00050000307805035036810711070b244914040d80f004107041c948030103018120b24058020300b080c180d4080c40015103488540c03116042d01c24154001545803130b8880042e01c54001c84410005c0754500004110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 300993030 1250 300991780 300991793
    0x1050403080414120306060921010518010603420f06060810151103030a060f0b0415050901050408030c010e0c0f09040b040309030803070201060302010f030e0303060f0a050d 76
    0xd11541c05005540082d00f1203990071038894000b209444200348090000c64402e252000c000c0440020041c440c4261004c4c107151000e100c1c1022145400d243d5442081141c01001801c0e01c11980807400e008114690a5135900381c203106030407032030301000f42200d0040008100d141140c61403c1e803d500e03200110500001c00d0304041c1031040d00500c1d5842c240b150020320076016442240c020204c00304480001741c1401c2d24010b02c01002c0c07075041d0800c824904003401c04502400218054511520082062820a41038041c001515401500196000c210402200c81d2545a00755804280d107006603481001500489160085400c055814080000d441c1c050b441c0551242070f000c10b0000583d26098880810010540b820b81c2040741c02501e014000f60000d004500607683c003600c00c1c20b004402c1030722900e403400760390000c50718800540e554074024020741d81c1103100f90300e400a4030300d01032101350726200d02103840303000161006004403040400041160707190b401407009403101400c01d0030744032102d0808c0d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 300994280 1250 300993030 300993047
    0x6040906140105210903040b0d050f10030f031b0804090b0f091902071506060807020708070b25060513200105160f020409030f02010c03050f0106030c050c01050403 72
    0x10145401c103111100c01c5500a40580c0c1c4039441050100403507200400160110050050801c0b0032030104000210b059103140e80038100503486414005101d00c0c0c000d00c86003031810094402124030030101010800100c0105000000a82c5071a00040c118410385600c6000b0014020092500c9004500421104440d601520345440220f0325500400c80460078040c1100381914411540c1c103403180301540e650241c0d0001c0034110300ca5900518404250102c4404079040ba80003500001d41c0d0030280501258100303c1c001c003401655014104191502e00070380710b14820b03c19450f2065220f41c45c5603901c80e0040b503070065010f401680034001d5181c40c00e0074411140100d00100d07071001c80c41c4460304a12080c4085004180410b8503000e16100102c104134136403010500d4121403440b140710040c030058845028140e14203229484211002626600203400d441030801344804040c0307007504001c074090700d0642e10350440c0d03034600b00044c04404a50046450b4403403411055010b41c242010721040540c0701010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 300995530 1250 300994280 300994289
    0x1413140616030c08060a0501110a06060f05011202160201081e04050c15040f141504121109040209011a0f1308010b030303090a020118090c02011b0e03060c0705070506040906 76
    0x400903e4001c58054401120944a0603040b0b1200c4c0d0081c0001d500898803011300b005080122180004503954800550b0000c0d0040c0c2850f00424030704201558010390000100a02480294140152004101481d44c02c2e0807002e0b0401c010100800c01400419064011700d40428030b034000240b9040c1025541c03000294080c40c011001c41e12485402c49001007038074292400100d211012603c1d14100022004e2051846503002156031505503240d801075005000410310340030642c110755a02e041104a02036241c000b5409000d000d000c02c40181d8801c80c8440c15030759080046082d44004141c540c02c24000d182d4401200304001500451700c000d03080346241220256002880385101c08010301d500c0c0c1c001501d1800d90307940040d003c1001507004036041c810410000c0e042001a035699000a429690402d40d160003603591071030840600c807410040441602d860b400c08814400210700420354079040208100c105200204000c0308000b02445120000d110080c6840d8803203842c1c011580050540b4401d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 300996780 1250 300995530 300995537
    0xf0705010b1504061e050903030a09060912050604061d030412020a09090321110f030709051017180f10060602120901031a03030310090f1413140616 65
    0x2d500c082c2c03403903160407075080c0c404565540340807240f003682e146420031282001c030042c4101844001825103040001d030000b54180c0e500d016542e031405a0181107100f0940141188107564900311001c200e0004429030015400b03d80014100d00c0c44104819089044030014090f00000400152000301055840d880307034002c503100407885954140f28000c0f9500054014040303500f0510141220071144560026070940042c08101081c10000305c91080c0d01c4002c0780f0381c50403000b1041c008516801104c1001824050301c43c2009403040303820180c142c0a030f4003400441030362400009036000282400103180d011407001200c40041c1204007150b161085110a541c22501d85600024100d20019090710f00040306074010b440c2804460044002e0000302d08240180e042c115403062035914200000c40c451012100c00b44039050070508060140e80050b0b00c02c5c12424140f800c2030b62083c541e0100710350403001c0101501e40c074000c1ca01e4a488604000d41f00305d22140559800c0003003c1c14400d0201000d01e10994 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 300998030 1250 300996780 300996799
    0x3040317090a061d280b040605010603050a060506031b040e07110f15011401021e0705030d03020405151308120d050a050403020606060a090e011509050d0b040f06020f0705010b 77
    0xe130798500141140d5646a039800041001e40350400c0e24400c4d04055021052126060050f403500c4001d0300c0d040d1000c07606aa511001005050f9241c03080719003004a0500504c134103840c100003d612400041d0070141035a8106101c07040805c0082c1c2201e0080502c0f4140e0541440d140d000a07007030401960051040e40240d11a0300e40ad14404200208080f04201041030580d0800c4281c500844d001c449040c15440741c0b00008002d001300900c90341c640514180100400c60400c070a150034400700715250805d050051100380407555a84c1c80503001c642001820301c0e00e686252a5001c2d441049910002060145030008424400070b80000e0601c110701890070300480e16900290012502c0407500a4016008140464441d2502000600400d00c0b28580851559180c9490002c034003030a9004404400d16400c42801052700070440c580180070440d218072440c0801c1d1a03020307000030300610081c205001d251880c030070400c1e1036051f034a0000c1c003181c04944400c5c03140760440c024407045050900c00d14001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 300999280 1250 300998030 300998051
    0xa0b0a0504080106090e070b0f0a120b1e030d021b0d06021213021801081c03060f0e06031213090903020a0602040b0c070806010b0715090807260a050a0503040317090a06 74
    0x102e0841d045811127901d01071030031944210441c2d100c0940c0710b070545034a8550b92202c1855079a600c141131407030312803482d40340200d2012040603d000c03015078507541550411642c504213001408058002a401500d00440e02a4144cc00c14028401c0302003280e036150000040c003c0b0941c107035080d401868801e03105210030201ea0850785524000900c100d00c2c1d1f0350710071004024245210341d602c014024080c18081817803529069040c80342401742c1c0088000b900340d0000c01034a0b2904101801c109000f60030744910304000d81c1c42c4003420b0304441c010306113955110900142014800c014161503070780c01c07020454540e6210103041000f540440d03030055940c030030b06d0804102c000300801c8080c120380c00c6014051504000c0e5455004401d014440d40441070340e40c0c036010b0045910140144006c0788034070500c401e9651230151051f04911210000395048070107000c2100401c1d0402c0840350b0b00225420074035140d643e58981120415405c4400310b40543c3c800060001c00a00001c0300174000b446030720284841a0f15 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 301000530 1250 300999280 300999299
    0xb030f1e010909020f030d0e13020304030e150d1a012d0e0d020909030909070e030d1d040e010f0609090213151208090405060904020a0b0a0504080106090e07 69
    0xe8640e400095445100400140001d58040b061852004c2e2422282d00e01c03041c0002e003411f950b1003c1a000c5030150351801030525026502c202200d000910840c01e604180e20003c0650510342c1c2c130203028004c5a00c10b400000b00800a48840d03550700c017010f01882540e4500541101008450913012840112401007030052140f04680c0030942a48645041641927808940303c4003140c00c01e54009183c8400b500c056140e884205101e04c900400035031382c0f02c1219041c044030001c010301c00800c000d02581d9942496a0205071418032a100b40740101c0340701880c1d080b11070a590078001c03591303002d49000480d0381d100006401200c1e13080c8000d50100000ca0303071281401d09840714880025441200721a400c2d0b9040420f500000141c040c0e032480e4010f40b52250281141c8403001e15041e501a100840d03004800d01e800d0003907983c0400e0030354102c200e5007001da011815030641801400b000e03007000b041c0455910320405c1900c0080c803041c2e0080c04020b070b4400800000309017440e4030340c800b4001c5e1000414603421 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 301001780 1250 301000530 301000561
    0x80c03040b0705090111060103060507300506040209090906040c060306050112021b061810060302010f0309020102010e2a12120c070b04150f02010b030d0c17040b030f 73
    0x20091072540e00c1d40e5820400300c03030300d41c000e07100d407418469142c90452200c082046001d003c1c521401e800141400c1c09140644031081050301200103504810001001459200800c074640e0540400400c0d103032600c900040180c0241050241c11119040030401107031700000d81c2501450061000701620390301d84504405807580d900423940403809082190005600340c0c2e0090400d07101c141c40b817401d070507104d85c0034a05044042c0c03002580581040040800d804051100075041c1d40c2024007088001e20315800a001d00007041e40341000d26a03145100d10942e4006e400441e041a5080192203201111640c0140400c059200e01c50301c690180a060a40e4100241e100251503042c0c07000f04602c40300f05071054096808101089000e000340c900000761907121300003500161007100700b00c0e10f041410740401440aa088035107081160304092965500b03890114106030750000742d181c005400605824401c1c40c1410100000ca00100005070028034941850302940c020317582100c052180e80c9414400100d00d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 301003030 1250 301001780 301001783
    0x101505190503100e090f01060602030703090603050f13050a020619171b0c031306030b040f060317070303020f0f030402031626010e01140108150c0703080916080a03080c0304 76
    0x114180b82400132442820442c1c4d40030071114126083c240c8280c000d01c0c291781c034543c40203003d031344080361100c01c0503003002d6490060940d074a0108000d1510750100100300c40050280004200c01d5070143c0d080c0001405040c066a8015095176542d11034031042c02008000300c545107000500e02802c44484001c4c111145000c1d2400b031940400b0102030010b515065403080298884511040080c2c40051180150300d0000304526140000e040e80a007061009452652009591403403034802c4c20f0000800086941d40d410581d095202c3d210f0440e446c1c103500078820b42c400c030403e0020218000b040150f070440110310861003a815100d444001c20340c0013409040a016203042014203d2034541070070001c00790b4070b03403034810707640080303085a040e8442c07500311100706450520340a2040c0c0180900305080090f40c446100c1d0104103802e5281c00d00c0944140e000d41c40d0018104071035480844d10350340d030403c0314100340600d004104900382e036507000280d964020b5a10271000729414500003045160f207070003035920a9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 301004280 1250 301003030 301003051
    0x80a0506010314070905040515010b030709030809120303270303010303020309040c09030803090706030506060405130e0c130903030506010302031306110c0d05030f01050a080d08101505190503 84
    0xd03421a40c4030f8945941c50261044188550b800000e8003640d43d0044a002d14094809814508441c150604241c94144c00c806441c1e80c08006001c4c10591160050044036046111303107841300010400146c040200800c030100da0700c130220034084580761100701e52411404000031035203442d442444040d2640824400500540c00c03c0c0a141c80a013055045030b54502602e2070705a51954076a5140d14480d0030981d0324403040c0c2e02000b070600c00150140300b01078000008660043c109032404000901d11140751405907030350380e01e4104440c41a08c2c01c05c82d00c149590002c103100194036803a030a590080c200b80303c040c1c001a09000201e59254028400c507401a0880700d10907040074a00d484200240a082c504112a18801c014201401006200060021000b0780d60256039041018212460001c107070001441a08034040420a2440000c0d11070041d4a543c10041c809940318010449001607070b1348012140852895840811948800148680310203540003241c80081281c040b10030780811a21501603 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 301005530 1250 301004280 301004293
    0x50a0e010308030405030f0d0506030106080105010b040915091e0f050403050306191e050405010f0e1602160608160e130e0102071b03021305090622050703030e0109080a05 75
    0x102d902e980c01140c2c03141c011000c89141c4208040d00c0da142e5807001100b0407031a50f0741c0060000a203400e000b20740040440b80001e1120f075041050303180c500e21072446149001c030382d615850804800b0b8038a1500040581e52010402d2030407445100c2c0100721512500c1101c146040007592003244240714080c042c2d0303096a80c40d425961003c050001840314901c84480141d51544000340c40e160340c0c44400603c0a1140f000008907183c201480305995041c0c101c03144500c0e5203042800955480000b0b2648034018403142c800341d5020030030990a0030742440f0b40d4029902c41762008a9100c0d041214280600703841010b080b8181c14118040320061517030384003503a120100d40204035440309207030401d030742104500313000501c0c01601da5a9260088c0b860012241201560081003065117801203c82c0040d100d800c00030702851814280594584000801d0413070801c200b80382200d00c404075080d45621041c0d0050448080940f40d040c09854540b040117071a0004201000c003250091001c81c00103401070340080107124 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 301006780 1250 301005530 301005533
    0x62116030c0f150c1a0705180604050d030c0c0e010f24170604060e0a0903080702060405030304031b05010f06051e031005060111060709030605060a050f01140c031210050a0e0103 78
    0x5666500400c05d540d01d50021124042c1c104082081502405840d04d4a03651580103440b00a000081000b0041c0f1500701800200100e4030380032402a034455043ca0100404c25039498032424240d004c3d00404080e0030f00030008100000c003170308402d00342c070303005260140c818400070160851942501c907034000081c440340343c03c0e40a1156040c01e036004030005101017206900d6404041075020100d4000f80245d0f2581c9084060640112240d6044800d074805450340b480c054940a13070341d10024200070104251114190f0000e400d5078010a0060303407290003402a075046c1c040e80005000f02d406203034840c220b102d01d10a8042c000c3d0340b1a00d00700c0c00140250030030900c07101ca40343c02402e00900403810300000d0005180c80020070b2100c90710032040c81d00d84050860860804504481000b01000c1c00349000107024010340d9945580000c0682d0240b034071001d107421805200301c07940640309402460303200101d04154000541c071109445111104d240235051640c0d201000390308000340c402e440c2c0b07081e6500d00510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 301008030 1250 301006780 301006787
    0xa0b04061d0a171b0309100201110f0d0f050406050603010c0e0109091a03010606080712020304020901180b0604080f120a050a050d060b030a0212100509062116030c0f15 74
    0x404110112810b5030402c044043c0040000320944d0701030100d50030002da900c18a00c0c0203000c8411041e003e2008104d03803000c01d01c1e200082c2c412a114682d440780c1c0441e44107000340340f81d00009910801c03803806004908051819101501065440501c203508198405803740d1084c1c2101d66a400140e4801410b41e250200b40300040c04035440101c00e8205c0141d800d08541c4090048030300800340342d0b0350f560951400f42c0000305417800c0e46021101c6180108140005680e8440500d810b5945030440140d04201030a1078400030006400700702c1d00800c01040c0040c0c070140101e581945052a40f094030a440f20502d01c050b11441407503d4500495810f003c3c080300c1d00d1160000e00f00720111079000044a03903c5041d40d1100b0b410450b0300744c1c4503a400107244541d41c924601101d420158072180050901c1c1000000389010f140245014000d403031448004003244140951100b5412000c019a071185005001c0c07419240183d0200341c034002c5903803d0001d01c0e00401c1d0750480444500d0b040c0040191520034048 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 301009280 1250 301008030 301008053
    0x601030e0a05030304030206071704030e0f190b0d0e010e0312040f21030e010c020c1311030c09030c01050c1507051207020c0a121104021b0a0b04061d0a 67
    0x4409074400c040c41c10000903810002980264060380050200c3e1030101c100403c00c2c0682d1896098880c0f000c0f0034000041d13044204940c250b8002c0300d502e1a1017480502045075a624210118a10b5416003400501d480013400100f0003174950020910000c100740458074280e44d4003002400081e03108002c03802920003181d071004d400034480c2d0100010992640c6950394034a5480f480034056140c41d40290409540501c542c00d01b00040c1c00081c0511005044065207484008410b5802409403510008035950300c2e51090f00c1e1741550170f40c3e1980724100a00304682c65084082c216001c1e12842109206a60003007058819108000d8010606d00309101ca1501c511140030303050600380242840341c0c00040c0d280c40c4849203e511030b540100001d0790050200300d04520a82d00400b001071640e0410008586880018818030f1400d50307015036102c900c06130b03818080550040c000b001d0700440058030100448c00414074003460040f001071100f03d26038641c4401c0d2051440307092655134400e0111400260803580c40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 301010530 1250 301009280 301009301
    0xe06060f090d0303140a022802030d0b030c12030715020403080a0e01050d021605060105040608120f040803030103120e060a1b0606030c15021203070c0314040f0303030911090f060103 80
    0x103c5c9000e41d082000421480640700007a0641d00402d91846d04249408102c0e11014261a4402a502d4802c0003944034443c000d0340b00525070320340503400c01d55181000b1603542c000010b4001000c10280111a548941080700c04a4094211888160442000d402510142d980103000c0b00d29143c030780754040d5035150108004c50705005041c01120000e6000c1e2000d0070102d401c01c1d441c0410062035103801810310030141c000c02c1c45613250910610406c000042c60420300003071070160580d6010320f0314400c8803034012070340001d4992100200120401c43c040781d14a84419480c0c951120100003441001250b005441d003100c0054403002c6200c540c80c0020100510880c000e0b80000340c0107860303888541e0300c6400c98000c0d00324483c081d00c000510130f0341045140c101806584850b425810304840c000c1500741c07418005000c0245881d8905a4044401d003240c00411641d41c046200a80c0c1e4a00a0042c00c0391000a44100b0010f1250410fa4100443c07014400c01c0491403440c09583c4880c0103500400900c5039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 301011780 1250 301010530 301010537
    0x61b0a0c03180b12161b030e03060406240320010e0301090b060f0108060f0607080c0619140603062a030c0310120b060607030e190e06060f090d03 64
    0x2402e00080c4072122210042d00302031400c1941c40c0f5424462000c2508090322098078042c18903c1120b0050b44802000801c07400c4002819401565041c00c9403a4010700c42e4440d41800ba0400740420080c95912610001602c1501c140181090150401100600e0320000c0c1020349600c031802d1300f0803004200d50440420505200d207100e030b20480442e0841f001400111348680c60f03907003070180504e0b000c0322802d6011024030384041c2c240b901201140029012490880c002c00c40400c20808120040c000d07520b580300c200085400b10300d88000c89501c0c03411019840d000d42c618003400350320039007400b44446204410150041005480342c515120060b84807401020700a001e1214200c540283ca02c015805074008088151302ca0500144000302c010b86984000300b41032a54000310001402103e5480d4040d4003107801d50b445048030f060079030301c0610303000c5455801011950200c881100c2441c9a4045e9082741d51f05415a43c1c46000f4070200d4810386403458050071092102c40c0c158a40703040d2800d8250701c2443c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 301013030 1250 301011780 301011797
    0x925030b010b0f18012c01020115050f091302030a034a01020c0409030302070204150f060c020d0606080604030809010203090304030206070501020904020307050d110a12230703060602061b0a0c03 85
    0x2001549001c0928860016150ba5601b041c51366680c24003078402d4140d0002100300040d49481c0000350b2071a541c10045000b00b0030107000522280b01030b55002e84141c0c0240c140c40d40e0000c5d5140081c803150003032800310414001c00da200801c015100b4200151040f40040002d10042120ba020343c0e0070010705c4140c1d04501c41d00f403032200151101d000d8411054400e88001d80c45a60358410401640c02d88400b0489100b828201006141d10941c281021540e8500f0b081322821954004581c20100c00b4401501240c00c0c032030005030000e40080c50900c150302990300d00d00300c2e44844414500341e11041d102082c0d5940305000500c05450680e0041c20700510840c00189808807481c042020790301704460300408202c001c5a055160015401a2482d240d651040107262000d8041c026000052180840c0c4440780d60301c900d242529480708281c0d17052600c0e0b0000503c2d43c0f50410b4000c01070306007070207280700600070240811905000081100f2825645000341c07030410349144021a031260349086d0560030000f110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 301014280 1250 301013030 301013057
    0x314130f0516181803020606061305190806090706020d120207062a03051e0a0e12270a090507021603050d11031201030204050925030b010b0f1801 64
    0x10521100038088003a08440b40d1080802590031100c00c01d01104c20000c11040990020381c1c045846984031a089540c986c80b002003660380d0341c410741c0940020f40c000314250b5840032600e0791682c0d12000c40b20304008981c0590703110000d40e9103c0b1243c0c8952409680a5a203800003180a11100700c0d04040c211001401c0000a4890300c0c00d44214007007060303600c2100d40d942c0440101060b0100c0d500002c1341000d0005081402c8070b4003a858650001c030000d440c0440124172030810380d4000f1807600d2110b000b105c403d0241c1119081c5160300640407401c1d00e91206a1031340b644400500760f40109140184800b003901e1a0190000c05007000404500460184000d04040c0011078402c0901650054008000c2500c10300303005000d4006030000c0300c181d94030038015000850742c080750890542e541918045055190105447e01d00381000040200c400c1d05207000715140203184200070300b107a004203158003072a41c0c0c0701c11450040c41003c40d902998070f81040105d60042582d41d003100c102c41d0600d001c20300c40404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 301015530 1250 301014280 301014313
    0xd210309150e0706021f09080906031e0a06030807060b0f0312120109110901120f06090209040605090603060c16021201021309050105180c0f030108030a0314130f05 72
    0x81d5030308409550356400b84079140308030400400019210b10300080404243c81c030696082514440c010a00302601c17415214104402d8901f03a030303c008809464542c9034100f0120ba10240c01c45200c1c1c4000103400d60300020711107c118010785c8100c079080100b080ca403a1458403881d0182504032516904040c00820401064908104540c1c0c40008811060b40300c1d080400900c04041061f442074071606d040680c2c00342000c206408541c00008242400e520100750303c4880750161880415414160b0300d0b15070005005141a00103041401085508026040d29842000725039041500c03419011752201d00001c0e81089003800415000c21304036070b0b01c61444415800070f81200e08420600015035004201d05820302000b102280140401403400d200c15810140403911000703035a0701903280344260303101043c03060241e41c086520f80c42d84440c82c0383c3e5960b115501c071656540242d07100d0000918000c0c00c001d42480c0041980e00030440b000c0d40002d80800c60300d56610110924800744c51a010344407141031007886 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 301016780 1250 301015530 301015553
    0x6060515040602120301030309120611270d2d0b0a02070203010b040b010806010513050303040603060806070203030c031b12180d02120409021303080705011a0d210309 73
    0x2040315280d560740e05100c802418003081800000b148641440144000383c0c110075444151198210120007000250400c8400341c2009402251200c0740000c0e0848201e80884d02810141c807400c210711056449003080c01204100040058280c0e21110300117a00101240a0440100660414061580241d860ba8840d508060313031480d20441d800503400b401c50400303028840d0498011903041000340c0b80400007030007413640280403504000c000516031180c8401d911031100500b501604984d22a51251006030052030a4000c081042c451f120001c0c0f442407000040301d20030240388600170305540326100151002c00324074030314540150062100f201380081100c03100c1d02c1903a51920701c0d000d00e503901c000c00d410003501e50f0080c011500603940c0c4400298a940c203c030308542070450010390710407841040810740b08039030700001c0500d2000159941030002c1500500e404030042a5011141d10340b10081140c02d8582180048c400946203004008203441d80c045c6007108811800d02140e010040c1d6152840c010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 301018030 1250 301016780 301016809
    0x41721030f0603010902030a060506130513230a0f0609080d05010f080304050105070f051c0305040302151302090702281110020604140715020c040b0301180807060605 73
    0x4000c820000321a6001c04400c1c1c0200094008200f00c8500ea000f0070b8803000b5185010340015220b201181203507d45090946006003002d00401190030240c800d00a4855414800d072603441d6001c802441c0e40c3d003010704018211300c4407802030020740c66a50314010050405803054905540d20303120b090100d56500300400b4640300c05280080c480d810302c0301c210100354564101544030f40c002d205c2400741e660014102d4150a41100852070595200d1811038500980960401d64600c545c110ba081840e8154008601981c465029034680720b80030941c030843d081b021205000d6051410b030800c005800c0c0740045580060880c8180d44458044507160013090002c0b03044018149001c500840c00d000701031070161078004045882103071032a03103010002e5440c4400ba01c05880a585202c52100c503d03c2000084002e011050404c00f150240100182d254510068407501950804260710300030719040c416103500142c07031440794100860f5522640c069400143d01128050340c1d925010a255440400340c1c00c004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 301019280 1250 301018030 301018093
    0x30f0307032c0703170403050106120506010e1006030e151e0c040617070e0310021207020a080a050a0e060c06091006050607060b010c0c0303020106170a080417 70
    0x70720341e820380200e0b44440c1e988200c2030312400d8041007030040c00100d41d000c101c0b6045200b11205404000040391944550380c802016586401030014014540c280c2d0104c55074041e000356401c0e603903a50342c0444071035401c980d098440c843c0c0c2d080601c0054040d50081d5118040401110603002d0601c02c2c0f491082400c1d0741c00d480c0d00c40f903070710416892442d20341076551024403014814200391905001900303410340200142c05407501070380010b41c0075120746000d038203c40e0020129800c10f52174805500095220308203080510310a500090b50507030001403202c010940c849192850100a01d40c00c440c03581014010404200600508e10f40c1551251f018280758001100a8a010b003003d00c2094604202900914501ca003007042c200101d07170345c01054a0a0301d03008000859824640c0004031094140d190006002c403200c41004024981d0551041064030640c00f441e114030315a066020b592001c00450007801044108003d1005149507400c00003103100b00c00450f505508108206100700e4007095049810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 301020530 1250 301019280 301019291
    0x1804060b0a031103010f0b0907050c16180e03071211070e01091b0f020a030c030c1a04030206090c090a0b06090a030818060f0306010c0c080703080c0607030203060901060e03030f030703 81
    0x1614080c400c03070201d80c03d280700070407a0400070300c0480e0f45800024109d40034020041032007960300d0400e001030300410403078441c203159441c1c441d52140d02101d8465150700d01a480e00c0d0058034004400030858000c40d070400c080300d02c0424039034800c450071883d40402400034011940009800c002c44282d890103401c101d0004a0307001158030010210b07400c0c004d4160108001802c000c50025000300c0c144200c103806292400100c1080c3c00c0544603aa03038984028043c45208c0d0004694002c0e02c4907a90140b0700c2075095030b1854940c0340c2140e0b6a08403000005900c00c08078004524509081da000c01303003225000e080c50b0305101d4481c00184034485541d0058800d5800001c480c910701c0c680c5054003080603000c407559410944100c0c5405014080200304505001c09180c102e41888020841d603401000b452044078906500c03441c0c2494550003040c24424544680000700d11200c1c068001e0300e05c154030140481036540c1c40c04e9005c4800c0c9010f40242074041c0410030a01d41d40600d0100218440c641c11340300840c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 301021780 1250 301020530 301020563
    0xb0a02090a1719020112050702030405100c03081b090d050109021203040f1a07150914071d0c091c05061005090703110306040c0e040c0f09090204051804060b0a03 71
    0xe00d031042003c0342203d2001610300380142e0300030191001003c04014002a17607076500c642039141d84184d030049a44014010000c202c400d60000f07801c24110304ca0f1391415015120b11200300c4403804600c04c12050003038240b14500c0541011110b6507085c41c092000807070010480d07004246141c41c00c0d00c050126070800202070003a000c0c030030401c400403c0320707841c2e040460404d5042c410b038900504100400024456400c01300702d44a6400200c5607a80202c02d003115a40e000204960b140f280e40710311400001580c444109a0401c0205180b00b038142144003850145058200809100c0e441000098680044a218041340c1b003040002d10a806110460390710070f041004000300c44500a11200c01c040c02d05050300c07102600c503810f6039041a800d49012a640306504011349224004000e0396801901d80000001c5259025801d1510413140d0f46503d620300d904da1412000360710680c0070306600b2010364102c2881c420b4090344d10980c018050a800560280d00d01c00203a0b400c0700907482030750503541c112094031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 301023030 1250 301021780 301021783
    0x1b0f0302181306090f1209060906050708091c0b041a0a0b130e030702060c1606110c0f0d060c0806010807030c200106030c1e050405130b0a02090a17 65
    0x2a160000d06200c11482c2c9003007814200700008121004050f180c540442d001084031900341d101e49580c0c0031081134040520720f00003c051200601c144000605059000614113014804a40c141c40e040010355140011007003c4c803448206402038484403c411400040209100c8d800c0300b401240704520041d00c09408100f4030500d1100039283c20070319468094001c94983d6000380c41e031300405c0043d4003c6803401c00c0700780039410b601034040301a400410010325140d50a5011078030181280364a1503403406507446001c1121300da00030703000301e41382e990140208042c585410380c0c0107a0142001020300c00721074040d541750802d03210503500c1c0002044a84052120540c1c1100000303a001c0d00b0380c6020403a4298600c2c00800c10540d154141c11444450076844001410070740200006d541c104004040305982d6206140c1110b03900040d16801810307205010800e445c0600402d401400340340414084120291030384040d0210190540c06140c1c0d0030400c00500c1c1d02c0701e108030402442e11808a8a41044854415 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 301024280 1250 301023030 301023049
    0x3080d06050f0112151226090907080c090a03080d060b0f0a030203061504030506070905061801030c030e06070201090201030b03070b1c020c0a0c080f1c0c1b0f0302 72
    0x294801c20419940b42007599208a010710703c020042c9010400c80790b0792005164458054003e030403c1c3d1011b404000c00d028032038000003140480003841105081001004010300d0280e0568168001c41140c04225114440d0080b144c004549002107840c2021102c00148046819802214000804682c090150f125485848002c114903100c0a283c115010803121051080300101401c0c0341c1d001c00405d1803616400e041d028081e154051840d5182e40300c3c01c005030740f4482155400002000f0301d4000c04c040c10903409550034002103610310181084000c006601400c04544440101603495819070b916100820040e401101c607500001031040f101d0000400760b40200c100e480c002e5022000400c0301150701000c42e40f103072801c0790250340700c0f00d101442130005e4815551021400d00c10b181242d0148076001003c0c1c000c44407240121684040c01d100f2190b110036841304000c030301a25003e10040c419025110184200303200740701d80c981c03001c4c2e544902c0400769015040181080d900210900850420203884d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 301025530 1250 301024280 301024289
    0x91f0b0706270519060f060e1b0906030106110f011a03010606090b030a09020a030c08071508061e010c15050108070503191b0801021909090b03070e070e030703080d06 73
    0x2100440d10098a8083d13440c0359a00c550305003244a0f055102c103104159101802e01d00031050140406551f50746207840d40d68041d10070302c02c280800100c02c60788400d6170f0111034000300b02034051030031a80f03090010f440c3d49045100f003a440d4011141c204003511800c1c8200192041e2120351100c11588003014035007118030540108003800440c0d070003800000400c0081c1e0386e004401c05408070b8010403a20114041c1001c83d440103041c40c000d188086000c1078045680030550700d00c0029218400c01c2e460b4201c50740c280580d03070b5542102d07240c1081040030741801c0c0b98480d900018145501882034a0b5543c2050400c4200c4041c003065440300140039206040c03000a002f800c040300208183d4042d08540d90105510071002007007511050401800c041158104000502c0a007001315203440c07540d07410789081e805000c01d0400190065001050356182d9120324051180050000c000103400c2c00004840214042c049a091015a401c40310407541c00704010070145200d291899201da50456400d010713200c05800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 301026780 1250 301025530 301025591
    0x1020c070614070c09020a18030c030501180f032f06100801140a020a020a0c0b0901082505030c130b04030b07140a030b040b061b061302091f0b0706 65
    0x10000204400204c4401511088900140d43e4030200d41d0603160020a80d40194580c888503000100b4492640c4d00d030811280240000d0150342d4070f182c89100c044000c1d5100900b20540381c1c00304c40c0428480e000300c15920149030240350b030b807a1505039000100140c1001104180c2d020318100030300144003c0000004140043c0240030b074500300850b000c9080381c000c1107403c5050707022803124a100d00c00c0021102c1d07990002d0314003c404d52581c882c00450b0344252505404102d01e50045a0300103403224050b03403069581a035045019071030f0038048481d1347c00540f07014518942403100b1075090110007815030003003040c500042d0f40e5506d141b9211240d018000c22032000c0c0a50301182c820120350b0a01110140441e91800040c0c03043d2680000b00104230218809810510205a85001c1c51001d4a4800c500540108856072641c6001c0c020408001c1c0c00c0000703401c000c2d48008180014a22a404948514241c03140300c1c0c01074907440071589681101c542542c0c40303500d0300030b001f100d00d4210002c4040d1507801c1d00d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 301028030 1250 301026780 301026787
    0x1410020c101134080301090b01020f0f0d05090a05030f070303110114060d0302031c1a03010207080d0510080a031707020d02210f0c07080609030307090909021201020c070614 76
    0xc82405016050901072a0707808460200310345a0b0f5103400700324885651128006440b96162151907009101690203e030140c801c48442d5030001000107500016480340e0b034010074400007211012250764010003e91500100100d401280e079a070140140d125201c0000c000f0f00c00a4910b040080030140700701d0640d00303503900d400403255a10002a003400d5108006039030b00c00346408240342c00c83c42c6110729684032550350703d0480369240d503814a41000800707007410b032109500f81e04000c0402d401c03845190002410a0001c202e2000d401c0800d170031103076002c0c03804109080d550703698040e081d003424662941200083c0e034603022444800d8465180035000441031001784425080444042c1d55a03420f8002e14807030b001d4058120046030f03220002c5451000140103808c0d103580622481035990011400307a01030342d0081d00009001402c3c0003040e244584040d580c2c2040c0c051514500f04010942030800303070381007691211051410b240900052409a4510b03006061107440d19070020050010306011000807401007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 301029280 1250 301028030 301028047
    0x120a060b12060d02010c140109110105040f090c1719060909080d0509010b03070305030306100509030607030902010306030b190501050a30020306010f03030210060f031410020c1011 79
    0x400e050b03500c140240c9111054400030300059903192022907008200072203034013803070010580640100081078070600c010101d1081e400c005454500441c050b003500341501e103108000a10940c0c000e142446105c1c02c0c51040191175800400700040211100d0113032940840c42c1424442062092000401040700100800035055a640d507444c443d400020700d0568681c0c021a14a1400398000c5d1002e42c002022220100d031360f484d10b65102d800c2195075902c22082c90300d071648443d000e80e00711106064028007815a60752074080550081c95a44c0b03041c0d0402d170380c50307102000007020810f075903000341c0600700c0350342043d10808031030426540140c011034010f40381803204000b203040701600b03000030140000d012516041c203042c0c00c0c006001c0c2e055010b5414420440001001d40c60142c81105407800b9038244c5a01440402441c0c05580c1988192100c20050090030004241d0301d003034039454104040c00744e510800c00c800900c410390b000f110808045800c0b4100017a00317080d0074403824003480c0e8011403550a00c8220f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 301030530 1250 301029280 301029307
    0x103112109061005100806120304060c050f01050f040b071e091503060305070605090d0b0708060307140a032d0c1403011107020f03030c010c02011a0108240f06120a060b 74
    0x1204a0102071180341b401180c240d5035840524200750845d541126111666000024500d640c080401d0b140d42c015554000301d0b800042c09035501c1051300c00588490b0351a15902c0001ca06c900804031020411380c0e80c003103200c1d10040024850101c0896071042001824060394040c00003098001c8018146458000c00c00104042450300890b0302c1824242e03196110f0340c0201d0403030700181a00901e074520b07210801079043d4200c02d0a50140e0b01c190304490107292134a8042910014503108184e004014401c2080004c1110350301442c002010398504664490800d030610403520300d07100c12551a03840345002d01ca03980c0d8030912050700013012002030114a200e851103010343d12921202901680001031640c4941d10b08000300c500707030501c1400811580c0140017000f802041051f04404c20840300030712181c290740c4504181d038004c104040300724103841c4c3c68840034007070203400541e219004440c9440126199030344801030404540115002a00b40c600503d000e02183c0c200e0704442e03100c0c081800200241d508 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 301031780 1250 301030530 301030549
    0x1609020310140d0209090102032a1602011101230a060609030615120b01030b010e04030f031d07031a010e090a110427111e0103112109061005 62
    0x12900041c801c400b0702207010030380c0d541140d0381c043e4002c500c01051280541c0f05500039441540c0f50740f17140f5100e0050f030840300c03d900e1011240030380099050100946070f07409111900c4045105040510160414040c1a820b646911000d8401400514400e03802c0088400d45140c2c801100c240400207541815009003d4014500002d4482c235680c1001080e500b5041070500007078420003007400510700f80d91500300e0025400f4001240c48001c85000080c070340b04540c0c43c80c0d000d942d1503110020352204a80085008082c581c2c0c06111400d007680402081400511554004e540110f202c14040007082c01d10955090040c0d002e0040c0100c482c0c1081500701c80070850040c0203a018003291500c209070000540680040804039000c1c3e4401c282840341c110301c00d06080d001612a0a002c403040001d041040300e0101304043c01e00c20390a11050010b081e61190748006c220007108007110f8180f0240005d07004041c0f94452441c440682d1050a1081080c03040140550001c200c0c50300c3c244c46070510340031540003074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 301033030 1250 301031780 301031789
    0x11a0a0614040e010e070f02070609030f0f020604060203090f0f01021515060f0a020c041e15030501050408031b16080c10140105210c150705010e1609020310 69
    0x10145085001d9000020704075001491a0f41c1c100b50a0f5858403450040001e06460f0440803548442c607030300c0303214004980740c0102c0b4415100c40c4c11a0740f440d02d5605130800300540848442c090440c80c04c0c016a41e4070007600140c078080c4c0c021900c42c000403042c8100054003400d054400c411000d0007501582e4001100d001c025692900710310307aa1991050030302e03901491498203030b20060116600b641680c1d698081d04801043d5070888040c0703d404420300c001ca621100701842035844001c0101d84507810764000e01c4001c2074601c0c850060660300e403030f154215401542c0886105a001040c131281040b46080c003039850701c0c144100c92401c00c00c501070501c155419400100a0700022607135140d01001070145161460052a00344295180700082c4131900a0034080d007071154a604006039017180400c1030124a008400303000b0503100303040c00208400e01c040d034251034103895010000007000a40a0044604201c0350380000d06440c80c82540c006140040d030381000725014818003c00c001800f20001220454 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 301034280 1250 301033030 301033037
    0x90415062604062c03032d0c0906090604090203181227090406060608070207030c0308030903042720070b090304090204030c050f03120a050a090513050603011a0a06 72
    0x712600b5401c0c1c1303001d505802c00211024040c5026068044080000c6110343c604004a11048800500540103510807500d24411280c1d620005000040040b004141c03800f002040c003410181c4010005000c0c2d480340d00900724140d004410700c621807084440e0100c8210a0b80050104150a101005480d02602e508803460038000a400f0441078030510700b2107400701001e4940c41a91a2506011020305240e1040c0350000e040c00b03001910441c8013240034015264098a1103408515544800000703800282c40b031221400700300000078854504100c40c9003020001d400710b58002c40035090490443d40307441290001c00403083c50320040256801d0403141a29405901e0745c41a0701d440d4203070b502c0c5010756084500311504c0081c01000f80005600020b0846100b1030302d00b1241c081e0703001490349403a1001449540340c03201f4001c120074140251b01030551301d556440c04149090351800068405900d480485c0020b59486041c408181804c0c000c25003c411b40314075019007540e011010684c0c0307aa0360310480041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 301035530 1250 301034280 301034291
    0x512031c0207060b1002011d06070903030809010b04050403020d08010506070c0e1b13090605030d17070e03030a08040b061e010309140a0b1603090c05010302030c09041506260406 78
    0x7040308581c0207021802d0045e2284d400c0010140029000b410f480003511002c104504d140f4009010000d0f9452154880f0742c0e0303c0004624559082ea00c11102a09121880d520350201c54505c0d210b51090314401d074060b03401440495074000005d000c0840603000140070301c00410078000842c0c407001c0074004541c007417201d201c13035507031400307129a0007485100a191000a000801729441445415110b041e944845020018582d45908059540289030140008540300c1c00950610042d6616030f41d80c480060f040550400b14000700181c00c3d5444900a800071403c0c04082c08240000d002403150300c00801d42d038087c040d0092403500005040d8629800d070400d5100d505010420031511200c1015981102c12508500400d1408000d0100c088403230601200580d201001d180744a0300540c600b0b180c114120715503042c00c1400440196100034802600c0090801410303030310780c940d481400340c0c5944140514010b0b9007410b500800300c400b20440840c41c030007205120b103e4030240c0111550010b0340f14100140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 301036780 1250 301035530 301035533
    0x18050c16020310290a21050a050706030c1103090a14011704050c030f12041a0912070501090b0a0909020d1113051314060f060d150512031c0207 63
    0x70f880036070107102d62140d00340003644201e510704580140450340c0c0f803907500b500b8000d80f41c14048030f50000d1113a09441a402d4000004070b030311a070754400046014000740c48540b20191262454000300c0e0744581c00280e41c5011000c1c070a9400b00909103846100809180f402c0c0b1a14001891001180100c15900708040b042410b01d0380140740752503050281c8080e4130010f18041c01c042d919231110358040c0f8000e004074145600090404514580041250360ba110f003028142255441101c41010f241052460304000040030b03903440c000c290548800709001020618108000101200c20341c2d403040c605a482881815859034100346c2c0e52003540d0010000507280c0d02841d841c0b001805018043c50000e800000e0010b4090200e0100b42c4141c4400b03882d049071403500084841c0403a081918000c3c80500301102141c0391703182c001d00c5103058840c01804507080400080c0a102200c080d1907500300c408405c04800c200c507092299804440483c40c101031403e0907164103507a440c840c401035070015090341c001040300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 301038030 1250 301036780 301036783
    0x120b0f2a040503010e0109020a060c0201120209030a150509011b090e1f060c0b1b030a09030c05011802030c12060c070f0b070509041a0f01050903032218050c160203 72
    0x1c1c02000028024042e482400141038000d04445000b41d000da80da800005c1050b50040d20310b40c44469040c0c0d14800700d550204030510003504900107056060152041d03110100706078059129440902d00750000e54ad040c103030b10290855032502c41c0401e14a40a01c3e264801681284900b0201c40084900403243e80d40c1e51000200540060218a1110440003000c03482c580d00482e0904102d1086a0488540e203918102904035100101e89500c468410000070780c1254858201d05c8503a0701c070381042c0703d42807200d82d10182502c21074100846140212042d140c258901040a50440c5005440110003039410300e0026403110001444502041c000143c114100041d01000c5c282c0507400004101c441d06010b000100f40b0307400504528415400d0048115000e6104184007041301c80052034042409554001528985c109490700c41d45800144240c2820900700700891510301d048a0320303a01c41909244902c00002601103c0c240882d20b420201b000306041344046400c1e003845500d0310400c040301d920029 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 301039280 1250 301038030 301038037
    0x10e0102010914030301030b0c0f04050607050c09090d020d03020c101805030c0303070906032d0603020604152a11280603180f020d1b120b0f2a 63
    0x3e12108650210345040e14010020f54185c0c0c1c0704890f50800c546410042040900502c07280194a5004010400443c9481e50040082c5132291081e9980059840005041e041080b1254540b40d041100078102d01c590610074501080080d00701107007001c1c6840c502c2a5141042d03032660f07026562307070300e400b121000340244002642035000b0222940c1d89404d40285c8c0d203c3d04255014004680e400b94049110740c000c4c00341c00704d980003001c1c03944221894016920700740744c0c0c105808207006581307580c04005600c45d640180040c2980030a81d41d80034002210007081c4614045007a03442110781400c1c2e034400400c1e103100c20b440603000050783c11400c0c01000001c80d40d12030b200041a2907038020340c08510f40f00b5906003031000c940854604001800031403410503100c1d99901c0004040807440b00c00800140f801c00301004250707009446004401c03810181100780182143c001c920f524031340810340000c024868040303951001c0c10480c00c051a081207011414081d5030086250321001c181d4042ea5070340401c12054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 301040530 1250 301039280 301039283
    0xa08060f03030705060403170f07050d0c05040b04080a02181012020301020d0e0c100503070207051309050a03051210050a23030714010306090c0203030720070b090906030106050906010e01020109 85
    0x83da481c07170405141c094041040446040707423810401c800183c0c508402c012003441751501380c4529260071f42d0b5072140401003600800c4001802410701c404180880c0c1d000c05000a03084400042031590740600420407285048104109140c00110412141020880318201201c1c0010607000b070101880c400280640608404400a10710b0b081c14800d0f007060000c0c40d030181d0802942c405072a0b0302071000c111070320700c411640310000d81c1c4800801c1001e81050030300190800f04d581c00c00500001182c0da0036040070303801c0c50150000384010503402003919004520903002480c8400d9072110b00d20f4a030114440710b5442c4100003640d0311003582d0304054410350294142028008041e1200d003510313848414100941c1c40d008a001034501400450061603030310600c1203072035150300114210f1307a4141080f11550002500315074403800702c00c1408a011010010b441c09410400b809a864105260611405150061156210740e04083c000c01c8251500f001440c1c0205080ca440000c1c0d1807004010303405400c103d1b00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 301041780 1250 301040530 301040533
    0x6090504060b010e0301091e0804120606210c03080a0c06090b0702100b1c050703120801090b010503240d05070e150102121210090903031409030a08060f03030705 71
    0x802041045070742c881d03426900243c0700d1400744041c140a00d403c80b030040c08003d203540080d250300c40d6010040e280c80307602203128910680c0b81544524051018041c048811030352140c032480144021440384074000d403140529186040d5078503480c1c03a142c1d0855210703c0050b14041d40081c10303a820610030a21001c0c92600b003007041c80800031518080648010840c0c4200050289480c102440009400b4800140100404001640c007903984c6089101c0c00d003e0f000c42c1e00b4480da400c0080010030340070041e0507505094494070020740c9800d40381402e4484001c00941001000c1041010310000c043d0755061600c40c1d5820400303403000d01030103e09203048203c000361061060b90000200c000c000311100b8468901c2110f06400c680803d401680e607600c070902c105014200920520340021034403807490b903210040310071440c105aa5254482d040b14441c61054000980318000e081c0490b8249400035040f024030700040d841c000c0d1280c0c00624403032001d40041e01c10100c05c2202d00e415030342041522202e540000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 301043030 1250 301041780 301041791
    0x1b0d0b060c0c0f01140d0e0307050610030b060916030c210f06080f0604030c0c0317090a060e2202130605070b010812032d091005060603060f01080a0609 67
    0x6aa40c0744000d6040340d1148108030140c3e880c030b5116681e201d101c0c0c181c2e004000d00b0840c1104401c80a05001d600d9440c4901c03007071000c0c9000c0340e010001c03540640c041c4800c00034a281103050414650100070301041c040c011403400d1000d032208866041003004c11514002490024a40d4200e1b40d040301c0c0d6007d030f1000b498003d105515a85290b1020f20700300d00031141000010303910848680c071601e400150f101d030794104200042c040307030141c041c00140c107114980d845e00e072603200c1e520110300300b0100c9940b1000d02c1001c00c540304a814403d10003c0501424103224000310704840001e400041c40d507071403121a19200f4424000b80c0741e1901903480b0340804100c403440e49529080000c1c51500134490036100e6220540000482c1100864410301c010441d1284500d540d44418400105481c858006840002e0b02540c80e810003c0781c07a00180602d5909002d40240c00b1070544410a5075800b0302901c1c0700304800c000b480305964841c080606101002e003410100c80d92000c45060041c5805e9200c041c0c0d09007400c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 301044280 1250 301043030 301043047
    0x90203010b0406030f1b14041208120f040c0b0f0d05010806040c06030e030703031e0608011e060506162103020a0822020616020d0804050a0503061b0d0b06 68
    0xc1c805001a2062030381d040221011420360781040e14000b4040b03c91020b0380201e9000e086110f12108042d00e007260098600d0103945113920007001104801c01d845800d00410642d01d203102520301a40c0000708030842c4600e03810146c0b50300300640340d2407103889803212000402c9140e8082c114142d813100031103c001002a5a51382c0303045030b152070088808075105061441c0c0810254040d00c10800941c0c520001103040c1000b40d82c040d4010a941e4805060300d50403c0c441d5002d4851a00400025021078000840c0c2105444011031a151f40d4118503a141d5042030350a20445d00c0340c00c190f941c25421421045d000c0c00003070801003047d819200c004140c60920070b070001401c54040e0000c140880da5580c8040a69071001901108041c2c104200c0c0950180d6040341c1e005858000c000d000c07040203440c10030405a14542c000f404030030304903604075010350740403804100c07030301d001d001660080400350044c040500e403240c61b18001c5540d000e2210481d01c2c0c08184420382d080c640c1d00020200802610706651462032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 301045530 1250 301044280 301044299
    0x3090a05060a0e06060907080601030c11010903030609112b0621031701060f0c0501020d0911150703170703060f03060213061e0e0d02042a020a080d0e0709020301 71
    0xd03d43e0b014140c840c4601007070003410b011a040344130b00b01d00c2d42d49060303548490b0011009414001107000c02c1002d0041070119413002880380300b070300920a48000600b140b90003911030a075408504400040345040c440304100d00724106c6180345401c0c054604038800d155010380b9030000d00b0035402c003032226041403103809200c800201091001a020792560300c07483c402c1d002c03802c1c01d11809001e400c0011f8802c22600b02d07600c0c010404414441d204400150400c4082030580007155002181520001c0c2c513074002501504040c00e03a1648001c2c2a100c2c6883c10b070254801070000c0050307010141c0249000000900018440c0d4450f03000351840134032503444c0380d41e40d00b0b03d034000c0c0d0010306070b040324040c40350b00004005000300d080421400010940302012000110141c3d510f03289481c2254002048080b182c0c01a40c0310f20034640d09143d80c007008031908491498007445c82c40c0e00030001c025981b100c44100f012901e820b05442032081490001301e5001c00714070304181070a80c160b010080003400800041890f846 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 301046780 1250 301045530 301045541
    0x3040e040822330c030c050d0f0e09040209060d060204090f05061e010e06070c0f0f03030f02010203010b090d031b0501331401301d06070503090a05060a 67
    0x45481c88862100b1810307042080c40841c0480f0285511440c00040307807140a00d0018136464000d0501010311507042c0c0342c141c00e10380d0f02c1da100c5000905521200d5109904203140b401004810b4a075008a85003960120714100b5001e0640c501c07036a0940b4281040003800c1c0c04450140160311000d00402c5104042a80588001d90b8200c0c0f00d80c042c01d13682001410108402c030384101d0140d5800da00e0068420a1010951080380140d034040d18400010031541032a8841c00300030842003032407403a00c034510309000703100c0f00752292000c045900400040098180700030a4400c40c2800f03c0390044944050b28040c0e03800d1450000d85400300d90702070784400500006500915600300c801c210600280d00b003c201c5a00c9917100803035014020064003091202400c8055481c200d01e4041c1090040c00c440c8440384104042c0480c255618810101450a24002d860040e01c26410201c020301c0c1c400680964003035252400204200c0401c003000c000644a8007003008640e01d62908001a10b01c82d052150806001e4134 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 301048030 1250 301046780 301046789
    0x914070e1f0815090402090a02090d1703040303060f08030d0b040e01050a05010302030c0102012d18061b090b0a0315050402070605160503040803010e04050a06050a020d0c02030a0203040e040822 85
    0x2c0c40340700c00f4541022240d143c856580205506020f07a9178405000003900504080c5800c4103806100c0d50024050300500c01d007505404200075240e20381450300500360384071030b000501c050410500c10815071000005890702080c0031400403d90302c2031100440c0044c1701c244905001da42c00c01081c000c20b001c050b4000382c141c0703000f0340a480300450205c00582c2a5a01440340c42c4450510041c603d100014903a900f02c50700442c10310120302c28050000f41402d43700d01d51000d03200f41c4e907684030007041c6800d41c14807400080c0e82803c1c0303001028a421107506550148001040500d41c403000c440d0511016502000c000c2d040080007107448a0321800e000b001000122a2a400d030000d20500300d00150090303044c0d80c8159840070b8441e1540c2e00b409018078010b540680200c03400e201d40b074a840c0004059004062080070f19420050722000c05c2c0000f981560426281002507410800c80400500e5000c030803a4103484200312102815115441c001281c0d202c0e9044040e100c030350884050800714098014842200c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 301049280 1250 301048030 301048051
    0x15040f15181a06031203061c15051608011205012d0b09010b04050d0302030c0307111f0906030e100908040e0a051603050627100914070e1f08 62
    0x1030100510782c0240714070a0b0342459160340101d80d141c2d000071a4070b00459005070007504000d0440251559116040d903642c00844455031402c204200a88441c40382d981c0c466618810b6100101100e4400340440c0010300403072480100a0388010f040c04001d40100c003c070311b510b5076000d400020f00c00c010040c01a00200411b003043c2445000d1480d407600a80080c10307907050383e9115143c245800c0400c407501c280301c1d90460a50009000504075408148040c014081c0240101c0d03074080411820002c0300e01003030400c0c0103080c0c40900d0303e481c482e41c0600c206041c2c4e0b0050070000350000104101c640742c80f1400c1444c40c807450074224064200082000a030045034002c5c1c0803014a5110000a5810f41d0350440c2c50401c5207403459062000740c1d02c6030f0170054002c04050400d01141381c2076804070701082e804094489040b40d0311028040f00e4000100300c030008040c40c1c1010000c0740d11100101c1218500030781800200501958940d900d9941c81c3c04e0024482c240354400c1c40180c0030a403020789100c00480c3c2c0200e16 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 301050530 1250 301049280 301049303
    0x21010606020615061b100f0b030a03021f060b0f0c0c0102031617040504090b0126030d150f1502120403030203030402010c030e060a050c0c010215040f1518 68
    0x14a40001000390140355550315403140400c0c3c3d20309008003500a41014076050001c29092119148288010001c20034816004500340d0800305c01c94040e9042d40f800e141c06035201e401d0f07540110b980418800890400480c040c0145442c6101d00704c003420003500248141071001a0060000d041400200541001882540d200303440003c0166241e0140a800340d914511003007260002451007681180131a103900c1e0030700c0c2050b40b41c4001c60125100c000c01103c00c0c1418100502920b4450b40c686084504044803144510a00800d040c0d16070007089034121245449000760300401d07100142c200003628420440604007030780c526241a07070f2070341c0d007000c1805405040b001000c540c070104121001c0d250550011840c589442d07004503058a4407040035400c0084040d40407155503100340007011200055070f149911080c440c12a1804c054820200a0641d80030b810801650081c0c004a00c0d0b100350011400105d1050504000c0810484401c4401c8990b2034403800c03c0965090100754420740d8000d0010303010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 301051780 1250 301050530 301050539
    0xb0609042103270f0311070e01230604060504210209040b0a1a01080118091502070308060901080727060609030b070309030815060f07050607140403020a03081602210106 74
    0x80b80c03070603c50050400b448010b040c20100380a2140c040601c0c000308200d40c400b954403188801084000e070007a60700d0180707060310807121403001b90002c0080e0700300b01e03041441e0903d081e502802c40e115520034480b00206e103281d0031021038198411f4000b480d402134881c080c680b030300d803901d010038205c03c60340074a44c1441c0a00c036a0540c001400289a02001030b180c0325066402c1c52410045000c404900541c92503c2e551500d002600c03504000f4840907041c000903807918094503001e1711241d00140054003c50f45440100100c0701c0006408040718402c106c0b001080441c80c0b00500311401c0562004222414650001116540a07001c101109d001e42100901c54851a108800782c0704850360240c0092010004103280b524a010180700144004012a02c1c0c9404002d903400d00d41c000c4241602c107500304000b0400d000da0418030b09030800700b00582c0a8905401d550000700b81d160203000250103040b02140c1c041342c00e952021407444254005052400b10070002868881c0b1030125030b9104455400d00380c0009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 301053030 1250 301051780 301051841
    0x3140703110904021b0d02030a11031c020703260a110c0601051203070b040606060e06040821040e04060c110307110d0204140f040614040b0609042103 66
    0xa08000d60070348841ca030281d0801044060741006440c514014505224201c441c001048280c0a04030650051501d80d0420f01c00948810ac1c0d1800c02d820a8004000ca840c640303024010307141c4190050040140ca5200c1405c046440c01d04115a41c2a030403a03155080b900b416107100e0080c411020703401c007480643c90041c0c00201c1c03406036089070303a082d0303010800600c41032800284075010220701304100d9083c440c3d291941c965582058806032500c2d59101014840e4540c840064031a0361010385400d80340900d4030007600d6844800c0181c029210035600320402640c0b10aa08440041050030514013090800d424440014000c3c0071010001c586064010304441c0800702c242e4080c15045101740a95402c0541446408000c0a204907805560f80c0b06a8041c040c1048155004100c004000d49182c40d03d4540300b01151415004500010140020400080d00707004490341c0c01032007521400020345030b91502140c615188200c4180300503c0c80584c03400c0c1c50b416444075100c0304c05a481d21107418031121001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 301054280 1250 301053030 301053041
    0x9030607111603020d11010201110a17010b0c0a1203290307050901080c0103020f09101e02012703090902030108030d180b040305220e2409061309050a0303140703 71
    0xf5004000c01044401080c08007006d604229010300001c04c00401801100503140d00080e40000444d002c220b10341442c3e01c03070510460140c441a0305103890202400e101341e9592080384001085450318005010344140b0a07000b46814983d159400d00c00611814101001c1418840c5058040d00c81c0701c00015070b900e04070784241d040311342040c0075059a8050100441c00307544482d5640c007280f4003c01c107886003a1510f0018a903029000d550f2140499a0503400c2050540b4400300c4501b1681440c001d02004a510000c0081c41160034440000c0142540340690300c0a41c1988522005407021000180e2040040014070b0000c22826041051080c041c544c084030a00d0201c0140c401a4000300080003c0d00400081c044958441c0e201909491045903402050030140c1041041c500e0050a0200a80100b89010300a43d0100034100841480d0008a000840003c0185114603d05c1580c4800e89699602203c80e45402c5001c3c0c86c064105820702901411500880c1211001b03000001001c440c07080c41031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 301055530 1250 301054280 301054283
    0xf080f120405040906091406060a0626090f0601090614040e03040506070206070c0f060f020307030c031b06020309070312080c0f0d0204080d02100b04060509041709030607111603 78
    0x420704182c2400140002852450b100302d400c4ca64454964001c20110341102031894039035402800c291a116060001100c159884030052221140c0b8004028248042e50301140070b404905020a568a0200c80c0c600030251400c1155402040b001140b04c00f032541118054030000d180490085029000b400204c485480002c800c0740c20901060185103000402072007c02c0c001001c0e58181f001a403039110300405a9403101d03a2641040f00200035031030b084a404207410345103001543c1402095240030f4003240038000003e0400c0b200465624540045100101700c040d000981103481c0d01d09482c01564a400c940402d907441c0030301c1c40ba0740c1c0f5464450482d040c0b090740c18042c11410b09510700c411082c5078010001c081c801ca40c0a00011550080410150b01540c00c0c6074020300a008100440c9021a4020440e8bd0301842c10424284419190b02d0000da402580c4114401c2101310001810b04581c01008141d0342c2c9402010140701c1041e900941c000f80d005410015225901584d00d044c1c03a0050040c0720 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 301056780 1250 301055530 301055563
    0x90306040b100302060a030b040f140601031d011d1510211a06010815100c0c050306160909020a120c030e011d0f030a21150f080f 57
    0x2600244450708441d40202110400104080d1203500254aa81103402c2500000740c1d100c0d2040160b2070140243c02c401400c800701005044600076580e80c2400d0010810781c103050300e90340b0401652030404000e840850f07140c0001c000380c000300f284882c0003101c0510800c40030310440101184102c0560240c0b406420b008003a01c441528111b101c106010509100f120701c540e082460301e0105183c030402101030892003114003000d2500d1000901601005044501042000c11249159465484c1c00c0541400d90741006000c41d50103103041c650407019904003070341502036003050040420404164628080840c0c890021540d100c040b00d000700d01074120401d0026515484000404580e54800b02c45454245004103803130251042c03181c00d44801070000428a14900b9802009202c24400202c802c86820050340c0f0346211000010054403020004030040180003041c14940b0040e548006c00580c40b020080ca000c0343c3e1202105944c40036031244044034014a00131140c1e43c00007045560f104c10354504c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 301058030 1250 301056780 301056793
    0x90d17040f170c0d05030909010f05120a030e1c140f060711070b030406091a0907060e060307140705060c0306010e1c030807091a181909181202060109060b0903 70
    0x1001c04c40b031415601c0c019a9a4003003088807a110b44c0710450128040c28001e084030a04a01d40414051155411444200c158001c0d088034400a42d208040410804084586030300e91041c0c2410280743c0001d0a00c000c1c60380c0e10124003038010900101e40500484000703816031b1400c0c0c0e20048140d50016282e10202015040400240149021000a180c10502034080001da85000b59100d907040079403404022840d83c00c2008100d00c040040040b1005050300d4502282007900350b101281c0540005491345041c810201c54401841020760299500180c00070b080315514148a2500f101c81d601c10368040380000d1034040900c01904002c800b49940f866150001c9805a070a43c07011103640b2400342460042002e030480002c0c00c03040702d040300003000c0d00060b46955500c110000c080f004407201c41c6162b0103240340b0000240418402c0091a0859242c1c200c0424011010380d0f0751840001b0b1201d00820140401d07100b0581d0a82c00150075061f81c01e2a00c08211240e00c9035116034640c0126010300e03500d5070203031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 301059280 1250 301058030 301058053
    0x1005070b04120e030a05060402030c040903051204050c0a06090518091903050d090804090e0106050307030f06110304060b0f030f0d030b040e030c0609060a060b090402090d17040f17 79
    0x260380b44442420640b82886809442d400020f04103d495801581c032039005200b03000c15868280a891160711045400300b2204606980c0a00305002d03d200e428403095030000040c05200083c054a45102d0004105080c0f180d1a40005410a039140c05202d0180c00d0b20b0300100d00c021102940c03980904000001040102d01c0c20740302070f540e52598101101081000c5c80050f1080c80706000300c03020144502c4245480d0b50400d052802194801420440a030b070510300100442c3c0c03804504202641d4001c1d445d00301d030244608084025001c111012480740ca800000c2205014255018030300c00070045540044004142c0201680e0301440d404c140c88981158040707802c2c2c180290b0002c01c005030040c01c0810455100c0d046d150443d0010b1000000980248040040100c418855141e20a00000c810049542040011012401054203d40c0a5940012405103943d600c4103001c010340d0f030040e01146050144149002e164100380304005403086c1c00100820410344120400e202c0c4103284c1c0040c00c03041c585 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 301060530 1250 301059280 301059293
    0x60d06150e070e010c20030d091802030402011e0c08030703021b010902030619060504090303022809030305030403031515030e1b310917091809071205010b1005070b04 73
    0x1208104001d0164041d000380c087e450900c041890b00c107091700c4040c40f00d407404020014500103e1001e1302c44510400030080181c0c0c0214000294201c44001d40324034510f040b506640c01c0b010600c01400e03c5001100b04484190315030010701c0c0103107940d882c1c1070380d41d60350b200041d0981d948118000d605d17070021800a5049410b180982c40404075500e0041080da84d580d000c0f40071158410030650010b070f000240c0184043c29040050106400b204041c450402c0d2144000c2024146001c01404c101001010900b03241c801d1f00607210090440340418410390b680c040e400e9240d0452008000402d04040105042c55400b2802e07807aa040b8140352070382d800180e08200b0015911450726598000d298140801f02d401423802d072104030500240c0e00059012032404c0c08111652260300d502c00b92241084851429120f00303c102030000d207072703910aa03160b454641d02c0e5810008290802e0b03e16081c07501141d014004150000001c14401781c4031082d050314610003c0f00d00d0700c0f420201a0880c04500b0100300010312 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 301061780 1250 301060530 301060553
    0x110111010b0402072a030804030602030703060302042408030906092103120603010f0203090a0f02041122050a05060a08130f0503070203010c0e18060d06150e070e010c 73
    0x29000001000349120001a040740c04c005015928040d9502ca03880004130000c217018040403c5200141c60f4500e19900e00300c03644110301000f099141c010001c03e40050003904060040c641c0203000340440011881d0110341e0311008441003807980e400e5100051801030110490350340307d01c090302c02840c0c24004024000144101c0d1150407403409008e0103c51595424005400030029080b854101400d11504142c29249403800d00700c803091040042c030201140005080701700c10b0f0710600480b003032006400090010070400002500001c00082c0700740711040220448480540740000d401042c0e5110024072044900c1c82c0500c3c1d40001c41081070700107890082641540c81811004288562403d80d510300381c04150a540032a0b43c0c1d8804034003c400c5143c02c1c0101c18001205203048285c25081000141d589141080310002c0e202251000c11569120307400c50084003500400103102c1c09003035000c5200c0d01040c40c8544c404c00001c200116500c140700d00111a00d030780059582c0614400c5c1601d07003405d03500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 301063030 1250 301061780 301061807
    0x170f071403061203030106020d02011b090302042406020c090a0b06030403050c01180f02040b0d0c090b0d0b0c0702190b0a11101a011b0c0620030c010b1c1101 69
    0x3e44121600410700401c100441c041c0c10b203940a88241d142c0d02d14040c0c2521485030095842c030350704840a00300158803c49030700c2100d07011580424203001c6030901100c1030046c043d002d20b4164114501191181c0c00083c000d02e01c0e50203494400c00760b51903240b403004955a03c200c20703610020810100d00840c0c490000307000ca1090000c0006100000402c02503c003d4001c1030440c0c00c0451001c90600f549081d2081088181c0152450b4103010510b5940c001042d516000304180c59a40d2107210401d40c80300e01c01c0c03c1c82a94840851030150400343c05201fa180c0214000721320800c0707c80761158049020403081c008540010300d00a04004115505507010305a102c0942c1d00c600c610040141c88809a0280e090050400b500124180f4041000142150080c800303a48403000c00c280c60f000001c001868a9085461501c1c159826110301d0402d207480b100e80d507984244610020a002140c4201944100d188010880300881601c01202c071800411340803810190100f00c60100304201075000710f0007050400d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 301064280 1250 301063030 301063039
    0x40207080f030403020f0106081f05060d02010f0203090303040b1801050c0a03030917131e03110f01020c0a0311030d2f1603031e0e101803060606170f07140306 70
    0x201c6d09042c205084448076401161580d1083e05c0340ca0214409404060660581078010b000615190300868281c100800703009041109811000c20218428000c0d1241070038020203481d600c40e41c030050741840341c2000d450201d802d6980c064502c1c02d036000b83c00300d503141000341002e854400070b5514140c00410300c00c0c5d425200680260b0f00418800c80c094010059450f0b038600805443d402d155201c4206d86803109500070203203c0640a0021640409901d130f82080110b80c1c140b08a034864004030b081403d40741d50184c004029243c04810007419502d2914911003d0f0f00b210501000403008880b5080303540a480151080410307802202c01c0500f501e06a0008440c08503003100e503602010440d1024240d0095000440040303500e8a2070306040c181004203410744c602401c0340740c0b102c0001405144000b4802c5d041c0103d280e64400460340141f0030703000940d000340c1c003042043ea8852001d40500460745151200000c1c0d90005280105488240d6004069650719180801c1c1048080c20700c680c00548802e920 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 301065530 1250 301064280 301064293
    0x309280b030a020a0f020d09170111040314010b060406210912030c02070b03010302061b070306090b1f0308040902090d080d060f0b0301350d0f0e040207080f03040302 73
    0x55080303400a60242c044401d005948505101000784103000032000c00f41150000000c1901d10382e40010150140c0d482c409141c840078181a2100d4010a03135482a240d00d040d0109000060003000201143c0e10713400d10b4000d100b0703800d000c010000144214081c050108a04400c140b84202c4902074a800c2c1c40040c19000481c000c0d181c494151400400c100480000d4a4243c3d22801a50502440c3d004000c281207007802d650650303000030326034055440c4405004d0191101304501c00380821141d4025034014104210340483c03810001400300d4100c0d029400045003880304204260403d0952040729045240e02c1c1c11315080c0840c8038040e40c042c2c44210740c0009a0072000001c5a00c5c000184030740303410103400190044c03030f0803000201c00c0034941c0126900003040c001004440704040f1088514202d4056142540c0b400800c100000e0701a94000c20f102e1260780c002c00d0b6001c0d08105c0440345444d542e06d88105107036101e0100010f9100d0310744c0040032904140015050b0002c0040a103400500c680107076210f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 301066780 1250 301065530 301065539
    0xd031109090103060b10050c03070b040c0e01060210050606030402030a0602030a020d0e100608060403050304060c3f090c150e0910050f0a06360f080f030928 69
    0x41c1002030f0410f4900d50b40e160214940791900100c104003440143c1041c0b404c2010320010a500d0340203420b030141420842c3c1000030704120500c0303110005040349400140c415619400c009561342c2d80040307811b01d1a0302c0c11700441c100c0e20303101c0e054a200342c1d4024000c12503d00a540c2e0a4040e42001e02240085602403003441c070101482d0181c0300c42128040c00030060f07541d00f091000c0c141d0300d490740256400d800070014007021030ba102003180e0740550401c0000c2440c98940ca03045039407500346000d1145e8107440f102c4503c402c0c108407104124050640c024988444820456030b0b0484503007800017003003109100400c00402100c400150120031203401d0904140d204040892581c0c0c10844040d045042c60203003c1c800c5103480c100456a2510a45010209905003813000e010310300040d0011001d800c2103540041c21074040c0c01e0364039010350741c22809202507030ba400458200104501601d94140152500040c07800400400d03500881300080813a000d20022000340b03550803481c101c03028043c0c208100c3c0401c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 301068030 1250 301066780 301066789
    0x31506020309040b04140a0207020d06020d050a0c02120d0f0e1204090c05040f090504020409051b0324010e0405010f02370f120b10020703030207060f020d031109 71
    0x8090540265039903180301401c01c8215100221001e02c100d1030010300000781d0f49915426544502e034104016035440035400043d4048220240c01000c0b036000007a80c0d04845c0c1940c0129020f0314104c2414000d00040b00e83c02d90f2100c4120b0000d02d10000c0034440c072450959650041210501402000240d561100c8242800c22440200e82010280001000c00c080000b46c2305000c03480d8a1454014201801e009241405000e0f520807103c009403500d0104095503207030b50201c8041d03a8010200c82c0403c07458480c0511a00300c0d90000c600c04e014440c424025880303017072101d02c00d008001c0314000345c0d0b80c02e20280405269020303100344e42c2c1d0f40d40c507030040002503c144010303c045090b84181d02181e03004002d0b020a01c014060114024520820410300e80c2500f0000c410788600b03031410806910914002000b0081c041035810a902c1119007401c1c200e01030700481d030300701520300035404d8130740e02038840c002030303401e414140c6072480140d00404104c0101d034031a6000315a602d41c1c070900c5902d00301e201e10008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 301069280 1250 301068030 301068071
    0x80c1311030f04051204050f0f011704140d0c02030c041e02130e1e042d06050105120d021f060b0a0315060c030503240a030f0510050f06010f03 63
    0x880ba600c26050601c41400000c11014450462400b91a0300c0d060504d0b011a081c11468641c0c41c0c05512204a5204c042e030240310004c804078a0035030032003021326060909400700e150b071b5600e0192a0044140707010f0100d01c00e01c0600030f00e41d0081d001303102c02e04144003030000034018a400c082162600d0820b80c0c00520b5540020319651030b4040f0101113950400d411121041806480310218114115050b040066504031069005400c903215491361000040300c003000c2002a150301ca54618880009010030071142d20940c165170301521940c1441c01c0b0341054660b140c7e242241c0c0400750f4020400314000038040c0c102d600200b202d420000c12419560135800308960041c4502c180866140c40c4c41003a4034045584510050009161200d80c0030869100039000384006445003001d01030034841c0700101e216061113104000405440c1c1c01200d5920706081800c4040030804495a004028440d86d4601c0b40e8010b140c0100b43d20440c2ca01107448070700042d90348681a000c0f010905884400041c04500c080025 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 301070530 1250 301069280 301069291
    0xb1b0a03050708060603040f06050604020c0114100501030908121509070206060f0108100e0c0903070305030d0f0605060a110c100c02130e0604140304030605070c11030601080c131103 80
    0x11801c0e0500c810054440b60004200a005100074810040403645500780407210580140001400e600c650300031402034400d080044800c1d40c201010002001d0002644034400e0900c0002c07071902075192401113055400c420b4011305150014402c100d4040700580c2101e41140e214030b0780e015854500c40100c3c6810804642c20f0016802600800800c1e080c10030701041d00d03050900c5c04458034540401035030b404085601134131a0303440040c00000c0610f6503500484040500050445807000d03030360302d01f1035038940c004102e003400d840c1040c046204c50070a90080e81e099403401071642c0c0c2810480903044817855120217044030325100b4601003d9058540c1400c0b44101183e80e9648091404a4011710402040603841908050310b008801200540c011800c1604150300444940c800c408034203003207245004c0d40d000a4a03051030802030101d0950006000d40c4094815200007158005c00404c050b11640c1c244170700c0d90180c000c001c000a0310b280503202c0c0030b4803080d00c21001403914202d0f4003404981e0000c80e507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 301071780 1250 301070530 301070537
    0x170405040f1e0b060313030207030f050d14070215031e0f070e0a140d05100c0f110312010e09031e070303051f05130f0c12060902040b04030b1b0a 64
    0x6500500c00c600c4040c02c440380140700001c0c0070312460607000c5000f07448002c0030728959041da100b03910100340c42030216800458010010110692581c03d101c0c5d2120002503004002c201e50030003407401c881010054a4031150002c01ea80384040c01004960030641c0000d05071907082c075003145580b00d43d02242c0e0001d406a000d04c2040350440c41d003900040c0c030600e035010351584240841501048400208803102520400549101030440342e00e00e00a8580769a030380c1d018900a0400080c80350f020340c45014040c1040320341d40c5004481c5000382040c0d88901ca54110200f030b003401c081c0184040f18007a0f46242d00a00c3c0300e0112481c051955041d60119080001214000080064248181039042c0141034100703280341d800402e040c85402d0780140351106071203924010b006c81d1101c48410b403803c0e407004070078469080040c8000c9a41d103e000b0a8003c1c90f03458504d4052038001c0104410020f4070980e802e840c50400010b16103421a1280c9009a83c01847da03055280c2103105210b800c5002405490680d26548 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 301073030 1250 301071780 301071791
    0x3060d02030f1b0604030f080c0312070c0308070306060e0907050409020d140a05010e070305100f0b120109050c1b03040803070803090f0604030522150c03030b03010c020703170405040f 81
    0x841101009503005026105404c180000d1010a40807031404001075845081c040da600b60b40d0f007143c0e0039400b03a0b000c4101d000700b120301004a0700e5040900f04034414400e54038400c00f540c58541c140c003100c105000d00000105011040902c1e820f0a5259075003103402e908040d414255540e00f000141c0c1e004414070008552110109242507480d160710799007003035128005021b503605260506140d0380f0b0003480c04007090b07155004101d00c8128180110060f100d0408000c00e510b455071100d10f516800b540610090344028000081e91485c58410903000751800c8611624210140036030716203001c400104901c45000402c40041c04150030002006441d01c500304140d1207281c1301880320705102a21124084a030041c0c3c0030000080c4d0710104841000c100100240e03500c519503116a04454295000741c4800b5007003501f00d910894110301c40350300581c407035a028400320030240141070a8444544818015a000840c148009400000c6400040310040c1e041800c040d0364200003401d5400340c00340a6400350340d0710b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 301074280 1250 301073030 301073053
    0x10608090f070f0504050a061505070303020f03073b010f0915180602163308090c030c030c01320414030d080402040e012003010f080d021203060d02030f 67
    0x140100d03540411141c40130001c48c0d00c0c1c078401c07a01c2c91107011118420020300066440805000e1b034191382c4242404604151240b50000c00901402425401003039000c000702d000c10640d0000300d00341e901d00c0100341508a10860000c0042d80e05164881c1000c0503c00001d402182a03690a100301d10300301070f681e90b1380c21186990040d20324142c8860700200115085994034201e80c0d00c80700380b04001c42e00c0755181240800381010f400c02c7e14403503400030460b20303030141c0d12102d179400d1b80100500c1c06540b82400f41c8050700340f09020541e40340001c01d070007030305500420f214080642c042e40e0b0800b244c00c4103c07190b5180c0078806111541146940003000499040890140000016000305845001d41030300204140007140e800a0941305008100900c03c035110a00300c41885000c3d0003a45000d006120403802840104400121030f030824051620100b11720302001407030840000e1a2075030360049401510750303408003040c07041e1140d00040c07010303411003110404180183c404101d41240313a0400300103031510500c038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 301075530 1250 301074280 301074289
    0xf0402101b06180b091b1504080f0a0309150e0607050f07120b0106090608041104060506070804140402042117040b030a0b04060503100e0a0f050f0601050402070803010608090f070f05 80
    0x1d401c00c2171550010b503d2130706040c15401008243d0310121f0300000385061a04400c030246c0700d1900b000801d0302035040b0b0390100d4800003c1c1800460f10a84401c3c109640302d540741ca046401130b41150000844800680d1281e0800c0c900038254940650181c903002c0b01035280e224070b020f0300c540c0f002d003031111401110b00901280d103901c41c1c050001403502c1c0700a145014001807142d9009400501885050480e0144507521031b0301c440d000344005010f080d2209000c0c02c0910360f40c2c10900c6031091011000c4440e032680d11301442110195040607030401540d8001c400d03030b0725064054540454000c80700c0200161101602c0000d0001044031204540e92450090382c000d0988036030b460010302031804d00000b03100c03a540102e0b10048100359418000ba100981e62159031404141c2e107800f4004244140304c040034040d01081c0c410440f071102007202c81d0350366a041800202c0c0306510300501864018401844507900c2108056000080482103510043c042202d85040c09d5165004030141c0300940c0081009040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 301076780 1250 301075530 301075553
    0x503040305010c031833020406021005130308040602040f0e07031b050d2007030e1206010e010504020714011e060b09060307050307050d0c0e090f0402101b0618 70
    0x1c940c0f07002e002c120014170442d0410341000400034035a828650082c41c0c00009104110031403500c8400001081084001c02030007503009015400c018050100106100100c07401840d0080c40eaa03160858400c1e10382d00c049544c5180500101c030180e80030131000a420400d03c0e800c8000e0520b4216100340360801c00700103001c49001060380140004805400c0c121590008161061295001b101040c1c207070750400d20001d6031741160740d00b515640d0701282a405240c2d00540001d401c1d031080d11080341e58414507885039030f104824440c07213641c1304000d401413019040580292801c0c9201d41d001c443c09070304043e030391429114036810610948049003001000c00702c85006a400500074030106914200c0f01d040480c0c02d80c4401030001090000000105d8400e6105608403074407840d030480c0410140b440700c040144040741c0c031022180b091102c440881d440390001140d5602869006040d0760344405000020360704046544188410910b01c1c0340e140c000714426010b035003810b183d18554054800d40c2c92134240840003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 301078030 1250 301076780 301076801
    0x7030207050a050d200303070209180105090601080a17070203061801110703081f05030d030e16081009020114180a081612020d02130b0103051501051210080a050304030501 75
    0x41c503000705000031174150030303102c440e1082c01d030151114a12203402182c598464603030025080800c050400820700c54a6860611511100000303008540760480f150395902c1c003e00884040f0b401c01285c513800105641c0c83c25850020340c1040d1814502c660300083d0074003900f03c131440c022a202c9090300c90003000c02e10400780c804440c2c214007401c2083c16140142046801401c20380300f000b80618244142c0021a03420740103240c003e08a0300d203400502001800707440110003400d0140315403a400098442800458401d45e00950010081e03e90b01b010004054141c03608141d047c40102424100d50b0b1003440d0080c2040c40109032640317001c00310718051101034003081d44540441d401580000c140c8811180180044551002034100744040700d000051441c0210075000f9440f02d20b0598215148945402c003009401098030100895550400040800c0000d4800a4001101002a520180e01080e40d840e00700382d1002c80407017240c1d211401c180ca801c005e0307901501d099102150030800c0010034003c1201e0034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 301079136 1106 301078030 301078039
    0xc110f0409080a0e0d0803060915040509030a1b1a04110402130603201e090307030602030f0a0e07030204021602040c0810060c0b0a05070c0807030207050a05 69
    0xc0d0f01c000300c0d420104001000241480c504074090010f4150001c515a1030369481034100100c0102c02001d4810203030204002c80c4080c0c0300e5200d9148107200000040d41e481120120240081030042214404007004516080c0040c640354000c400745540c2a404e002d46440c0e034030340409a61440702c11190464804607a062800444440000848841c4c1c0c40400282e0b03503039002210800c1880b181c00c1d200c1e0b841003007040c4626459001710310040d8150301c045030070480c00c2000a42444116841540c5094000c000d0200b1b00701c600f810b00c2d0308650389030381c204010b91300c200c14192500010b100c007070310a9a0102d4020040048110b2400990394014030800502a0b03880c00940200c40030b5403040d0440410f46000304009015404681441c2d40068540c812035540c0b040f0000944070040c650070812180c500004000b03111007002e8940540710b5005480d040d41070030f0500255461980c0402d104 = true := by decide +kernel

theorem cover : BRFrame.Cov 300899280 301079136 := by
  have h0 := BRFrame.cov_init 300899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 300899280 ≤ n) (h2 : n < 301079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
