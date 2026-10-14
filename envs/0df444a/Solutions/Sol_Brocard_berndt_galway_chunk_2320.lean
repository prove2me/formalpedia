-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2320
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:21:05.709245+00:00
-- url     : https://prove2.me/submissions/4969b98b-d04b-4af1-95b1-e0eac8bf9bae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 417086330 ≤ n < 417266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 417087580 1250 417086330 417086353
    0x1050c030f043008010503010c14090303090411040914010b03041509060e01060503061f0303050a021501151106040503030a090201030e0a2901050d020603070521060102010f110a05070203 82
    0x190100320480a90f0180c50400c69040300c1d400403903140944012030003000550041c12000d4000c0322202e2000002c1c030740c04682c617405580c0a005540490130090014000540c2100d20280344d68414006c8840031480c140340b4458800390706900d24180c500310010b251441d00d40d038880c4400484c114001075001501c030740083d80081c5050103403620204800002241d070f9410a402c160600c8401040031285a04d0311081c013144c00c00194805003142e42508005945e06044c0a04a09291101c1c1c000d032182c036000000015000074550345003205c12a950b403814958003028030281c1d12154240e40c0a00749a00500125410340402d9100d028060320505001402c0c143d00480f460401c0d58030402500d40d1050240213025220542c184027200c58081206003425604220001e0404038120030040c0c001c0d040800090520740c0140100c3d4031100c0006524070041c00d18040c668841c0d501114254019420082c102e410942103028414001490301000c0d0b0074000101d00446090704802020390b0f042c450780710000e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 417088830 1250 417087580 417087623
    0x207030e0d140a0516060c02150a0513080a0b070314150a08071409060607030c08180303180312161712010803041a030f040f08090604090b1201050c030f04 68
    0x642c000e2184000c5d04c0c607600600050000300845a100e8000d010b0903042e40c1d0f00594520260f041050b0550000549a8005000440c1e203800340c07a01e503403441107111601143d03099001540404e0709109481003115596482000c034203a4070b40001003111450751002142d99401d85008003410694080d03d1000d0040d40d61402925202c01580315100f201c8045101103200d040c99841e09510a000b076456528007061a0b4005054048074803010b410404086001c03441c40482504a400151004084a845544001e607190103480c940219610038420b109416940b0009101500c0b100c5114046644070081c05441c0c0c0200760b0101c65100e02804402c10021000c3e042d043e50080c040d010741401551280e04003110380712107030041c130204200c0c8201442007040c00a00d41c00742541c80355100d02880c400f000d1925200c045401380035076440e8400800304000c5010580303944041d00034482292010801c0c80400400b41c00c8a006481d40044400c04200240103000940c61442e0014894103400213005e07580c40002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 417090080 1250 417088830 417088843
    0xd0b04140a0f0f020a180807050a1502013c0e0703020418080304031121040b160210020a06060504050403020c0d1a0415140f0112030309060203280207030e0d14 70
    0x21404151b070102c822850400052884024200343c00040040a007004002900302c2000d202c4c0544403d119000c0c204658400c0d00041d4903d00c1910050204126903203a0015a124150801d03030300d41c544280e42016515140547c2c40d51184140c00742181d84d04580a100141003083e608500d01c59080c40b50100248180f8000c600c80e038001c2e80c5004001c441d9224460401d0b4820000e00c052405290070200702d8040b6004a908a41e42c080300240d458542c03002c040c0f81088003803c080d5000d140d03180d082610940104400344910300c18081007059544907002c00080321030590b0003500591190300701c21402e081c000b0000c0740840c060300110003c03e0f0103c001244120302110102c85580040100415114080c003032024036220ba01100c064600d404280202d003042d05100d16499a03007804020400d150203540440e011941001c0c05554a281040120848071907010510000c100c0ca14841201c4205601c2502c030f03016416561040010240010030400c0f8240c01d5003550303070888200c0144040441005070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 417091330 1250 417090080 417090097
    0xf0d0f17090a0824060f1503011e03080f13091a0906040e0c061608040f0f05150405010e04021b0a020307080724170702030d0b04140a0f0f02 62
    0x91681d1841c0120510800100a43c807002e480c0c3d01c02401550f01c0100e41504090031040320140110365a42c040028420354000c1c08550b402400005440c141c10301c280009606032641010102e10101c42902d551518a803c2d201c041d245140901c0050502e00000f801000f42590040e540301e14540c540c142102221442c51441c0828489440ca40956007840503a4651040c4211410040d40c42070a280a8556400449a0388510740002c1d5590543d4000440c5107012504004599202d0791259221701900c00980540301c0c0d84035001c90005214680b1043c503c044aa07480b2403542841d181400540d0600c150b061400c1e8400e40900801e04036058102855055a10700d200825020002c2e0040c50300b4240c0c2a0009040c0707801c10903080c00217040000d040041150081510030185156a80c1282c2e4940c0344d41446803618081814400705541c00400b609050244020801c114001c000402c412145082c20b6140c1c18240703200000c4070305845078402c4480205900d00841c0da840e00103140c800b02d83c0001c0300d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 417092580 1250 417091330 417091373
    0x9040e07060201140f0105060702010809240114060310090908120a0209040605040c051b0c0306070f0809010c200a05100911030106030822150305040605150f0d0f 71
    0x100c2101e6520300a20035001294405c00b1240c81d418003011414138481d01c1000b81c180110340000c502a894108100c1c0b540d110304a01c246c5164900761984028540300380f0950582c0d1110386004000e0740741030307021640113403d00101c22080a04c0c0543d400d01504101d04283d0303203908140880f1542c0880c035110203100c2c11201c1001a41c0302608000c11007103640940000d0701403072401d41c0d42e0715402d1700303c42100c9024a8200f1510f00304900289880c0c602540c181c5c0d455094001c2c0e03c103215806400280c10084400c140c3c803a28910b640e9503808500300c0e0001440c0c2d0000620035002d416440c1070149215240000010681c0c0303483c13640743c0f680c601c0c100360a820300c800507680e90b5004003449000c04000418030b004800034403d2030714603140c1840078081d18641e48a0803a0007200c0c2c0d100e403402030002400400400d00c45d51080110102c0c068001d01c8121000e444050a040001c0c042002c0b000514030a00001070070f41501e0340d0443c0512030b10080104045902c11500407140020844070715640d0702c11038080f403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 417093830 1250 417092580 417092591
    0x90d0312020f0c2b051605030a0e030607111c2f0c0604030c14061303080a1e1413050a080705040c02030406230412050601030201090803040501080c09040e07060201 72
    0x20095444c140703c2c1e10400341802080220303410074000345003c4410102c0c1926001d80c81e0f115041d051403c00d2881c0030001c00320f11000401060b401d03080110302024803001c405075201541d4040060340d07084400b264102d0b0383d0304018100035a00340b040008140051143c039040c3c0b01d6a01400105144001d186180f00d010041c101c24071060300c908114034220910142c3d4504c2c181807441c0d8400044410500844802101110b80c44019440321019500304201141142107240d9403818031916640c4240038180004911131411380320300c000781c200303611406480d0303840001010048040d0360860304941e0080d001c44101010024060b501c1c05a407101402100015103501d61500007080b0861b143c900c00d543c255001070108004603a0040c40d0204d00034820039122741e2402c00101005a50300c52a0054003030007840d90582002d2190004905060701c0c400c0c1c0f61039001da92103c0c14190307640101d109890004203d5070000310400714100c0a000070010181020596103080d2401c80d003030035050b40025005039940c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 417095080 1250 417093830 417093847
    0x1300314180306071d09180715030f060302010c03030c020c04060602030c01060e0c0d0c09090c0507022d04180f080304060b0d0c0501030203060102160f080708060c090d0312020f 78
    0xb80005900004c0303d0804201a60301c10380390000d150580c00c51940301d8900000021210030910320b5801440e071502d000e03607195640350040e0072010b00c1d801041d1400030780f0380641c64400765031078840c2d8420303250143c41d0154030030f5040d51704030060701202c100c0d0070450061076034402458507540a4500985400e8002d551651a40e01c180790858040c0d5210b168104c82c0070040c080300903140b100702c841ea152010008241040703a15000c2d0340d20052a407040710740724a0071401c0130903540d0020107000700c68400c07a1044c075032032140d0b1440d4012070f01d521448003251700541c400325042c0c03a00c0d60019074116100c4041002c0b0304020340b02d03210005440c030001e951040c0c0c00800c0000f004450f01c1007802103a0b00f00c601e404081c105464910504200d170182c0d0b4181079002011036010380c020054115440800302c11810004c0d10b441c0000c02c000054401c015a0f40b1800801060740040802e01c240305203242e031101401c14882ca0100103546222040c15400d1041d98852a00601d4180c001809001441c900541d6141c094 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 417096330 1250 417095080 417095083
    0xe0913020f19210c0308070c0e160e010f0f120b061216030501030b0a021b07031202010e1504080310031208010609050906010c0b0601021018050105013003141803 71
    0x1c06841e061104070080c11400a4101c1308800c090300d41008400d51101c0b541d140c18a080e06040d009400900c11040805c1010904032815480488040c0d0320051000d2141c001500c01c8890300302c148012038902503c01500ca4400c1911a4909249040c0803171480c50074404190150b0241080105242c1a80100680540702c4061505001e5551a04105a61450b110b01c0b03d0550b02500301c40c010754001a0003286034116200781a01c100381401640c64453f0341e0701c2c1c4409490002000800075500b010102d4004020105069020031000c4090704aa652181e40d0f80300d441d0700040144002c01503a40000c0041080d08003205146400f58031181b001d0350406074017620781d200f02d9001901c07680c200001c121a03a6800580320100d0396001404441a41303a886c010b0341001003c030140b80d03100e0320b41003589800c803085072001040f24bc0200020022a62601550b6024010442182c200203541c0c0c80504100e154029004000318003e14003402c06403242c980080031540904c101d0213030301c0c91921004049240 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 417097580 1250 417096330 417096359
    0x303090e0903030f0601120c0207090f021c020c0708030d0f050a0c0e0d0c0b0d092001050f070c0e09030316020c030d110c030d0f030c0e0913020f19 65
    0xc1405042080d85080600300d5aa0310000f400074180407407a03c00700f0642d074082c0b0f1070084090996401400038a01464000750b65848034030032803c0c40c0c0d050201c00090103806200b20748040c203501240b0030794002000780e088065800403480f0b100b148030300c03000001d600b04140702a10070300b2018500450089103c088a10a0b56409801c80381e519180c0400401c18680205e801c0021100a4804c041c030319045041129000c1c8030b50388000c2d08160001805d240b4084164005814180b00d0704c09107520103090242e0302046007135030000602150b01000582040c01662001c0c4c0002481180d202040c141c460720741e4a8011070595951042ea4800b00c140305020400c0740701506284034a10060000000f00400280e9500c80f03500064207110380441440c00c280824060702140c0c5034040c04680040d150170900524600303c49520100003031604610881161003503401d00344d000b20040c1400701c0c4d511100140811015038500032640003001c80f442109176190880311141d040003072030403032840700c1c030b080c0310f564040b43c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 417098830 1250 417097580 417097589
    0xe0708011a0a050702090a1b180e0601090330030e15060a15030905010e0a0215040303020604030305180d08070201181e050a060f06050f030a0b06091b040e01030309 72
    0x8140040b0348000e9011096400c0141c04981e502c0c401d854190355440103004114007401c00400d10307000030f5001500680b4205002490395808000541e0751404e0f1001840d054826500051030000100045802c8a041341e502e07541c0036200c51304c0441407071490015410007220701408607484130490102c0800522488880b40c07100103c0c881107107170160028210303080c18000c40e0101c0c0c803121909840c0c2d40c0310b03601014443d64420001c1140244507003c4564920400c1005c900c140c400098220100404409940c201c941c0740d0000c02144e100c030750701a0040d00c801030143c055159425a00c5940c05403c0013004040c0300c098803080f0701c50922403002030940703000c4000203c080070302528030800208034644903a03020510303040c05000a00b080c50094208403400307030003030455820300d21403c00d0100d4581c89001203850440395012440a21418035840f519441e01c00350140c24200001042030814050a40d400031031a8104801640c0d00c40441d07581d0b4029800051080301c40e64014004c01d0303006250340c000381 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 417100080 1250 417098830 417098879
    0xd140d0c120501090c0f0f0509090112060b011d100c05160602100614100507141b0f1305041112100f0212130309181a010302030603150603070e070801 66
    0x910654000e00120b1b2088020010800119114880984148240d5488443c0103041001c3d65075160514050203031901d805031491841e0040c40945507015845030310001a03184c51a120f41a02c02042004560b14107040c0001c0c070454988880001d0702c240718001d040d0034405208980f55082c244020b01d440501040018074070714051086c4100344641000c58003248003100e412500b000c0c0900c0489150103001801403181100307009914a0900c04607000d4444441154680106a2490104101c10400507000c40e04559400d207400c0350300700b19400c203540c4903002d4001e14551800103004914568460140d010050f007020140d00c104903582d024000032940c004500303604000500d051028440e4018105000f170080300c1c40341904050090101e0345c0240f0302c40060440d00c3d034181100601420091020303440c8580c00ca10b81c2c240b01d43c068404d8074040e02014008003410071600406c810729030409014254103110740c000010340919140302e228030500c00da98845101754503002c1003400040b0105240c0810 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 417101330 1250 417100080 417100091
    0xe0c0409141605010c14030c01020301080d020f011104050f010306030503030a0b090c030c0f0a030b0a0902091009141002010e010f1509050c030a09150c0305070e030a02030d140d0c12050109 83
    0x3541e0b4400703024174420740c1000070300e0340044140b0601d42c0355106465901c2500e50001c00000380e0b0090101c0d4226480f1196003c1c2c1d442116824111401c0303400e81d802c0509034803400d000a108a0a100c0d5190039061018100003410b9916501d8003440c68004603802d00c0c469031503407031410450514881c038a401c41084070041d800c504001c1604562405501e010007101180454070440c490b06c00e4001c1940b83c600a880c0303944c4141c0340d800c80000f039800150250b0180d80c2280000c0901441241020215403a0800000403601c2d41000c001900100b041350b4030440d07484502d00c0b08114820301c00c08150502a00380040c0d2840214141038116205500c00b031031251400701000040d103a55400c495000860041c0021104034524040b8441440c0c864012176507841c5c8581300801a400d507010030f01825035a00c0c0e41411801540425545000382003009416402400c5500666030040f100c030380580c044a15441d0801040203100012504140c034240f00007680100404405411407140601620455809104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 417102580 1250 417101330 417101339
    0x501022a19050d051615020d0605010509010c060e0c060309010204030201020c090f0a0504021f08011e030804030b04210921030c030f1e050319020406120e0c04091416 73
    0x1c548180009580500c000040e1340d05c5000c3d0009222072201d9400a249181c1c0000d601114000350010700f4a504464501000410950701880a52300381c0c180503524031140c031040d0395602c809801ca0000c5000346101d10121810565a0319010b14410044500010307140d61850000a1900048200f154081c00300d03841402842d044880c56507500080c100700106c0e154540e4170105001c54509100d2508004191080c00e0229503c2585241241c405e00c0740000d411035410a000950203e41c03200401c042001c00c4104001052003003126405802500e4030080490850030b10240001d90711910000180261810700c240041c03101484002e120511590741d40300b40c80d5030007a0003001c00c031402070203111904462088551040e0b0582c03107074018810102d03d046c0350445014140d030300151aa005030200d46071045105131024800e4804981c416610310603048410031885000f0600c8040003c094011406022850b031200c1c000c4584462050040c010255104268241010352844179000960010101040b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 417103830 1250 417102580 417102583
    0x301060504120804120f06050903040810111e030115031a1c080a1d0301052502010e0102070b0105130614131d150c160f0501022a1905 59
    0x1c064a01015984501020b141004040c1c1d00441d4001440c10092119000421a20041d01c82243d84144400e10158070303601d981585030700841c0694102a8403e11504448c0ca2154001c81416000c0e880d40c0303458580507070240145464040c1d11031080410001c010070094078584505010300c0303090300e410808500c1c50080e10a409611600b120322821101c101046140e80c0030320300c051080da000240719654881b0020151aa041b500003031101900c240d5900b040904040c0109071041d80500f0071000021020ba25a00601c0c16440180045650ba00c28114240350244010140103010b40c140c00e8056161204101d6081c182c05043c0a03440d080c04020000114000e02e29100c20303c04446554109402c40491b10007030100704030403415003003030700e440044e44007020a00c0000c905074101480c100d81e5808182c00780c81d200d10b298180c0d03035065040c6800046a150189145210b2181001615000c544034605a9080c0d51b9048165000b54404010340b44101c02c001008030f5400300207600303054003842d8131650b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 417105080 1250 417103830 417103837
    0xc060a05030a0b0d05010509101107021210050a0b090612060106120f090b060411072120010507120c02150a0e06010602010b0f0f03030d1119030218040203010605 71
    0x28014400d011000c12072000440d0020201d081010b040300d0040d41c50340c02c0190180209680c0c80c0c00c3c50040408080c4030599500401210038100790f0b078180b90000943c2442007819000c0700c1c0c441d01703000d000a4025082c5a90180e0341c005c112484000c2104654102004068140a45002d02c00c04d00c01c0498420070002140352411030303645040c100f07111088a00d442d4081d09000025114240c505902c0c507040140d0034099074010182074900b08509501003808900d188100f00000d402c0d4504164241c1c0c580180c1c044003800941985013840320311045a8180034143d0003002004d4890351900c04025603075038082c01101d01590446418083c0382c0304030801070b4545440080e081240d403817081c0084d0390409290468680c0c6100c00044480560b502d460082c000d04c072100c502d621a084402c0a01e0f0280740c282000640807000501552911645074400e100070b00000703180540011003803203d107a43e44200b02042e10003445546000d0703a2180c0003083c2c80a04410714590612840c0b0500060040c69444000d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 417106330 1250 417105080 417105097
    0x6050406021b012708240412020a21140a05041208130803040e0903040303171305160806011a0403030c030903020409030c060b090f0705180a0b12090c06 67
    0x500207122840125138404e45990404c0d0b0383c200c4907072000d02c410146040320045031107040544064080e072100f4078000085004030008018501c80c040360124414000340c4000e81d03c80d00483d01000500d54a07041010a9101e69500d241980310740740094507000203048031030b4008a00741d1b520b4442d02d804060000e01440c000c080c0103602d03041070401002246c5086446118516504601c560340d5012030039600e40c000c0c00b480c081080b10700702050746402c00000380c030b00362a850b4a81c40a0460013280840e10480c00410300c50000d8040c01042e00072074018002e00014110701c0c680c9035231050038207124078500081a48003100603102c0b0300d00d100602c11500180c805899041c6071100c288000c90070103d4041d6025000070358030919160512081541000c0c4800c8440d210b00c00038006100c0e80b00403c0b1040d08203c0340b0303038109040100014600e901c03d00040803040441c4070403d03101650b08001c221a429a030304104040040001c185480c0711509801550020103040103044070b0f000300c070200321075000c1c140300c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 417107580 1250 417106330 417106363
    0x50c1906020c100519110904020c010510080a02060909040602092e020712030c050708010e0c040f0504030e040b060408150a180309050108041e1b060c08030f0a0e12070201090605040602 81
    0x10802202181681214147c001c020070030341d21941040055402014295142c8084101004001440e014045203d5503003980003006e403400c02c255001403009507000100100e603013a50030424012956210f004141c03100501d41038001e5451244030050820020b103a90010965000300010031480c2c0e40312080780b089079414507040c2d107041c846242c010315203c03045d0440c040d15400c01c1c54099508100150701060010122818003c03640e14404500840310103450107030019600040f070044500305600b0038120800003510540c5080d5a810480341000c6130704041817001d48021041c4007201c0300c0ba003e100c12024004040503199043c03564040d0009240b403145a06100c1c012002074140088444610070341c081076001802c228100e8640500c0d80c424600c000810a07a50a001080319481070892580b041d500041c5140345407550240014401030082c5174986094a82c441c0603130160b005e00c0b014165000003000240ca9002e5840098070b8188950051820001c0520041050603800a604200c2180005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 417108830 1250 417107580 417107591
    0x10b040e061c0c03050a12110606120c1309020a05031504060c020109063213080d0b030109030c0501050112110f01020109080c0304090f0507020c01050c1906020c100519 74
    0xc850038500d40c40d120150003c850490004180070001c40c114095602c11501001403490301d2006917240c0d00e0008034100213600000020300142080d540c5200c2032640401250307801c02c00400014200200303200c8400c030301500e9010300d504504043c184040640004c40140400d500c80c1d902501080b54000c00203454603841c0c0c48886005130003980060340c0180c00090038040e1003014008000300c02c0c0e19070300c141c1e51110011851010051513600443c0a5101e4030601c900000c41d507110f0b03115607002030280081081e5100d00002966509115030b03103035a0302c25103842c0d0300b240690500c60708498050340100e030340c9240710084000180c585d6a02462100c41241c44419512010004034014201c3c942c0090810f00c0008110100d1f0a0000150040360203030038051000090490080042c2c541c11307034189001da44400001c04056004801a01c0e08030954000c45d40c00c09048222201840c0c2e240c0d03425903a1a42c00900c1100d40c003828016040d070b8031040403047c0214140415400c2d22000e800c20200700703465440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 417110080 1250 417108830 417108859
    0x20709020f071b0b0f0a0e03010b0a0b280816080402030703060906021908180c0a06031d010f0c03050c0703090b09210114060907050f0a140a0314010b040e06 69
    0x441c81c0001070010b07400e0440c0c80f210101185d10869221441800100701c034910f65065a140500980481c004060030801d40103290000780d02440c0c01c903410814188001c40200c0e24411170741c41c0c6880711003005590707400090810310002060541c40302d41c41c80030400100b041002589001030b10500f1280e212800003000310060400030004d0080c03520307202820003001c01d810181588042d16030300584039020366006000403a4090f6580b54003007004190040300c0201c0402445010382d110091312802c500036680328403c40000c8a0845120b410f40d100900e0307a41520381103840d0700d8030480b5400041040081d02d00300f102c0e103015000c1c03100c80c030400d1483c040010794808181c507400001803810040c500000c003d4503c00c00f0881c084c2c9201d10502c840304a80b00001040c40c60160b4540340620100e441d500d00d40899070380e820a06501040540b018081c068a1000e401c000b50801016100115900040c0c0c1108210026440d0740c01a80074040b131035000d01047c8411a8901c04503500081c00300c848a02c82d0100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 417111330 1250 417110080 417110123
    0x305150709050907120609020703021207020a050907051c0506010e040e12120402030609070501080c0915070501020310060e03030a030207060b06030c0406020d050a050414010903050607030c020709020f07 89
    0x29003103290010498014001c0445d002900901c0b048040941448010f40740d081620407806010300145c01070b4410303102280c0348007201d0010714101e400a804c00060588800118824280c03c0c1d4115002420000d040040c1241c0803480d943c030b0011100c030500c01c500304100003c080301804441c0c02d118640d9061003581c100300802000380c0c00d2400b001403c0d00d44a20014211400c1c404440582c000d014000001e40032a602241800c03d9480584503507549031519100c180c51900b1401d00d8903000450101d2007002c1c1200c4a000e044014420000580d80b85000581c003400d4540d5948400140034600340751550342d9802005941d4032407a14500103071910440e06190f00504041e880080e0000c070004244500c000e1210000c10541d1201e400b258101e002d5031504690030722030310309503c000038420b1005011b40040d0110744901c0d00700500d018444c91380c69403681400c010080c0d4850340070a641e0b0001c920196010f010a000804801008504103c1500d9004d000c921070b100c0028600301d0325040800c130b150308 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 417112580 1250 417111330 417111347
    0x20117061908010903110d0503010e040c030b01030605041203060e06012105011514090a03232512080304031b050f06040605010902130320040e0c1903051507 69
    0x3580c4004225241d5441c102c80c020044a60154005640038050005000700051401c0c601592a998940f541c0e107072040301290303200050021290489810b20020210700507664ac680070394085c101c005a40d09082c40c040071080b43c1082030341d043c10b00b4010b0030015000450601d692061080c20048800c100e0b107140c00910f840b03503000504490349441d00106050403420004002e000041c1c031040000101e0907040019030081c15030041c1d000f4010712091000850041c0410501000d03004030410209454000318188a800e1141c00c03010b65480100c8482501c45400040003001808841d0380055900d845107035070752000420241c04d000c02100c00c1c4495030303000c54031a41d900c0d8000c0b05803142c6040356107105171555070540f000e9030b490782032030008a04a80244212450000b800000700e00d554695078a444100806543c4815610b40c82c241500d40c685841c0a00c3d038603c0302c6ca4000c1c0a80f810480b04202062031000c007506050111801c051000034000920580f0380d25010b0f074242e0b1265510101126800b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 417113830 1250 417112580 417112609
    0x1302130e030d110a030e0312040201030f06050409031206090c120b01110a03030c0e0603060f13060b1305040e010207030207060c080405040603060b120f0a02040207020f0a03051b0402040302011706 86
    0xa14100310b03e20306008550190141c2026603038284413143e117055000d580d0380030f008c09184101e010040410010741c040d603c42c2c07146100014000c107805540310001002ca401c18001900490794100b040221030119100d0030f4042c000c00da400300a00c0c5842e038802410001000d2186140070751b140714590882e0f000e80c0d500100c0203109422180782c81068500200031f80458007481d008501ca80c0b1b034001c030a141c079105491040002030904141241390100b0420005d00151201c0700003903032554003050074603843d402480c00030890b44140181d6071070b01050000b141d810700000c0c0b03007c1c3d1050250f80e0003e98003140390012101649401489c042c494148441c0c00e00c901d6000660092804800104005042d080103640501c00c41e1031020020764400080c0d12410b808043c0500c50300150800c1c001854564054542d090001d4928030b007814011010658406040d08141d8296011500c50001e850b000440d05208260a03030b0250304091644e80080c1080d003102c80f021688540d0000020071a0300d51419013035950 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 417115080 1250 417113830 417113857
    0xd060308041d01080a03050a18080d20060121170310140f0901090e0c0a060c0c06031b030c032306100311030711030d050c030f1302130e03 61
    0x65554070b415451241852402e003402242c1140001946500414a4905d01d40c158035003d00c1e000061500301e0b02d14182a000310200d081c3c00f00e0100d240102006604000b0300340d40c0f01c94810b45654890001c2c0044003042600465001e2070040c04030b0240c2034109014500c050519114082840c07030720141c059281c60038103144070400f0003003004900303002d0020821103020506130700329500b14000b80321409109806003500400f5000040103200c045920070458000e07094256201d107814940017420180f050340c8840c0c002034000344100c082c000c401c00b0b031034000e02183c142000f288150600c668000104a46134109059031500402842400b80c0c000540e802d1894020a18418089111100c8514196107117802219144203258605000c2d10801000d0340c046103925045540d004030840e4500c8815200201c00c1c042030200c03211110042c014640241140c006e507a840b0316119601c40b848242c0100101c2c04030112480a40141e02c80b40c2d1001546440c0d000c011940d6203200e0044c51441c4501c00b40d99140d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 417116330 1250 417115080 417115087
    0x114041a160807030804021203070b04140109020607060204031406190506011b120f0c08040e1b070303020a030c0306290f0c01050108061003120f1202031302031e120d060308 76
    0x41617880b42d8594480d030310846070307a4a1340d005000400c0d500d000b2030740f00420034115040030130081400c22071041c4825600000124030110580c3c04170740e80d0f4102030070469001d42c021405000f00b0000c414584803501140c0018062450140c000e441f960040703120f41100240e483c4080b640d01d91003160b501c2c1c4035005030a91b48940c044140f510405541c1e90350041000100f03040788240c10340e4820514070000740c0c7c02c03410083c1402e0901c40c0031018010090401c03c402c003603450051000850300005005594000c2e200161a01d16601029082d00c9080301128101440c02c4014400000080d00301c8800c81d10400c0390070000030590540d6001c030f00c551141101c0003075020540360b400d00815044941a510840280d80f0a9214030500071403c0515000c003c080500d00d6126403081403060710100a43d940500d03000121500f616003c82c1264020b83d0420500302c07c4800f00070030343c1005c010b0042d1010311020182013480200b001251108085221050a010001080d45003082550007201c00345412036600c079038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 417117580 1250 417116330 417116333
    0x3022a060301120510020a39120e09040b01090b04060503011a041d060708040f02100c0311060702031801030204030804151803020f06030916030803060114041a160807 73
    0x3c0520822008503201d00c140490074540e8880e0b4000e881c1e10b80b00036125030954006000140c0d08510f01c0041901d4540c2c0d1852040b00e004008444607020342d40100460462801c171032800070085007544a481c0d001d00100f405100019468140c0c9604442110600042c080030b80b100060240c541c640c1328562640c200402d940164803010844d220100c0111000c00c08001c15a0100303a0a990700400100190080c070001540d450080c103000fa2b0152080030701e040003030b81e0fa030300203010101415482e10000d1808900a8101a04010a25035210000000300703494640420001c1da641b00d414044803038407001c7e415440b03080e400381e01520040c0d0707171080140792206c0d212501600d000072810f00c10f200290505c03608200b448000c0301c41c041960b4000c1e10302407803542030005200791584042d04c1c100c85440384420188803034801000784800b9602c2100500e031359060a40c001007500c2e0703883d0220041507400b00700802a190540172000095101c601a95481d00654208500c00105240b4003400c40c50b0000b88450 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 417118830 1250 417117580 417117599
    0x10b0310061d040203030909190e010c09080a0f030e0d0204050103080904200702091510030903200613051c210905030913020c1b0a1203022a060301 65
    0x1070380d10340e80c1c40014400d55022402d2400000790f034040c1d0141c000300310402e0700341400808168083c20083c40210b250741444040003c0702c611000301c4a403655206540b41c1402e80c80390002000f0500307800100120845500ca0303440c1200107400060a00034081015a05600c501440c5854203400410420141d03075642030040195010076070803886546820014140e94504910500c02141d41d404003600341346640c0d0900c84152805003c20000100384820030304c003941d03074440010b4001425a004100d12500345409400618010b80b00001c0c800f500d441c9440c81d0ba00090019440511200e40900c00c07005400c006040c00d107101000c0c01c10181c000c00d031440c20340e00840f86584114501040400c100301c8072070b40310211004008000c2003a0402c000040d0603103030281800303901c4000d852006242c00701400700f0a25040c0d6042a1101c0140d0f5207003000190310704864580020080d491b0880b0b00c0004564000791100700d45c45031440508081400d80c88220130307858140880b03c41c0904100e50300d5131907210a5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 417120080 1250 417118830 417118841
    0x3010b040c02150906040c031e021f0e0a0b0a0815030d02061009090c05010305040c0503070801060302092d100f0e041b0e0711100c030603050601081b040e010b0310 72
    0x100620034800f000700d01040d00004049100340d40004180e210780d402c603521145032484801181003180051240c08c6c0c0980d4401c90040311480070300d07070b454003510801d0001400908213504041e106517090309c402c120502d82d00086030010405807810300310917a05da00110060780804440709416104904801850540001e9000c1c06103021040185c44a41d03680704c0c4030151940d20b00010082899940c0810a0754001c1c0c2255800c1446015030b8060581ca55002c2894000594000c041c2c40e91103842c10030a41c10300120498000d1103d114420907643d04032919421040740c030248400041c0004001118210010b00c503402520540a0200034243d5071880111300200c140c4050f9010b80a03052049849006404d01e0f60407030740c104038042060b644050098070300c900f045a100c0f40380d004078a010101030005101c0c451400300c6540300024074a043d070610629101050304401e005600860a40815102c13000c0d40800280c1c0490300030840e00c03819150b50b800b40854916032509441400b08000b0300c1520390304036 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 417121330 1250 417120080 417120103
    0x7060507091a131814011a04060c02010e10020d0306060c050a1106071208070809030304020f010e0607150903030c02031c0b040603020d2301090c0e1506070305070201080604050705120603010b040c02 87
    0x145071701039894600b100c00c032080404040c03220b0711040000f081140d010b0f085640c0c0a50050524221480c1480d0100d070526010580d2440103030802c807180074400da010700c54407000d0031151815040141c02135031001e695840c5042c01400071100c0c1410b043c1a44c0d1a44216041ea50b840002543c005e180800c01806142040d503564010401a100144c42c40c034000040d03e00c180d4009000d8402d5804803401076911070980d010280c4c10590400100020030054403840703244920302c0310000351580450500400f102d114448003800c6400800c0929442c0c14101480008a03480c910005603201c4070b10000b60007440c060740003e4000c6c400300801070600800c00350314458000502807070094588803504542c03c990b91080c0081203810541c40500c0321030b0041d4403a82d0300240c1c2c1903010b00740c62459400189a0381040308124005200080d0050440d6800b10740c40d500700d00306a82c00d004600f4580c42c00f400034090754851070000351140780065003d98094000442030707400540100700384211060001c0d02d07107038489007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 417122580 1250 417121330 417121361
    0xc0801050f0306040b2d090c040c0906050306180708060103050f010f030b1e01030b10080c0a09020a120c050c120a0e01050a091a07060507091a1318 65
    0x940d800c10000d100203484008010306566610780d82c50403260100a8050349141d10071342d100c03000200a000f60204d0100082c5ca40709020310b00240c01c1883c1160707140340725005034102343c05004415008648542550318905145840c3c5d580d0b14041007540800301114680851400203000360507030010001030090034280d13414407242e42d4003002810700110a21415201140000303040000c9410352070400c1d04607031900c01103025084140042c050301c0600f82c10559803141c80806006112181d00e5216004103d6007001e064198280000250340c0d40c820303c14004d41d5600062261411440349846035141d20400104000a00d41b8580003040c60f08003211403080d5104640d0000940c00b144000d484500751150790701846500b2072801141c40f40c10440f100800d101c2290004241805142c82408040c140326003000e44449003810400b082da00701900316028440100b030180104940380c920b1140020a4052980d519885c84170201c0c2d00c460242d00c806400030780b11a00580001c12030300400c404050450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 417123830 1250 417122580 417122597
    0x20901030c0c030e01050a0908060c0301170f1c050705010614040f1b05092101020901090504180201050a12060f030506090304060507110f060a0e100507020a0b0f0c030c010c 76
    0x40c00e40703200301440d5000d000700301300301c8815090f0b40c420001446409883e00d44070f0600d40e41c550030140f620382c0580340c65159030b1020006100100241c1d00c2030524131254001880c89a510f1420103885240c076402c060004400703000c0c005002030061084951385036110008200d15070f82c03600c070f00307610410b03001446d8412400c1c4100f01480175100d00955816002c00d1289285448841906480c1680090600358202003100b65900b03400291242d40303078540042070001359444200c00001000c0602030341150b8804c2c2c0c5080d040540103030740c110a00002c9a42820465a03600481d90301360b81400d44210640f80316818000003054845000d640c9d201220300c50f0007210800e8850400050710f90055004540c0001c0702072240c079020540c020441c41103440c0280c2200c80080d0404003244c2941e01031015900424100c9020b030304a42041d141800314207505150041c20451158005030341600e41e44501140d2070000302e144c0804101c404120b81d4041c845400b102d0341c0e5101c03100c03407e028001e401d0104020501c80e8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 417125080 1250 417123830 417123851
    0x3081c020c03190909091e030c080f07020103060e040b040f021912060606050a4103152215051002160504061809240618020f19020f06010902090103 65
    0x1800781c0b42500f5808034140404080d207155120000c40708003c00c8d03041084980b11200803842e001c000700646120400b070306607942840c1c0005070036914190321440221a420b0308020201e140440559005a03024842801c258a00e00004090500c4048080e104086250300012181c02050350744168038441d5105102044d90703070b241907515015020034400400e611070101455110910714426000c0c8d900c10442901c501909880300c1910f0b41b140503034405150020600440c1c01c5180007404480b10100d44900421039000c1114a0b6047c0200d100e0a003980c60b00d0034100f000c200c242152020b010f02400140d4044101701c2c000b9552400c241b13150400c0c1c966100042454200b038010007080c5c600d408066000c003004010000010481544156031000b000ca10790304450220000b00d191020110001007241d0782040316603c1c140314990002c45401d48104610458000f00c003054600c04418601d0a60014000600503800c0030390714000007402c1e004900010402a11503400352042000c01c1e601004802c050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 417126330 1250 417125080 417125099
    0xc010f0605030715020a150c230d020c010e0109080306190e190e070303020f0d030218210102071a01060e090a02130302060708030901110403081c020c031909 69
    0x32401201e4240e0016070781440811581c100200350307850307140b04854841596881300b404400228028242941e100c0074001c2d146980215408110302007196440700700510360b002040c02c0e2188030300380c401c0130381c001c81d084088600c02c0d8444541010240002d100c0c0300d5040ca00100d596100301d420904c5899020503c5220342c00c080780b04429514460b85001d065104c0856074407000d006080030450441e01d80b00b420803150000d0000c2401540310760010130b2820b40304680715080c017402100507010144140f1640000c042c111410a200c03c100b9280ea484004900240c0b5010140c10205082c0d55030002030000304201030f9040021004c054481d0740f07030890762903c81c12107180b5480002250b100c07a81c003002c14035540f410f500500c12108030004003200d603079683d4045036003900640000d64000401104204485800b0b004841c1c3d502c0560700301c2850603045568215880c01800e440c8190729441c15286140754503158102d07004c0480183c1240d0311103410011250801510080da0400651311480c0002d81003075 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 417127580 1250 417126330 417126341
    0x40201140310030b040606032916020c0d08090901120c12030e121603140f1f0b03010213080a021201020a051b0712050f0c0a0e060d0f0204020a050c010f 67
    0x90300c2c21400c2d6007520316110b60000200180040e80c1544e56090b0000c001000100a12511450340c50307030b50302c0c04800c4420f03100480c00c010100c0305c0f4641e21440141030301d5408900c596654004481c8080900624101100d55004001107180c0021902c000030641020307044c0902051032048a0b203c0c60140c40d410141015460544001d01080c0e0b07150a40f005c528000c015250703003c0308517084a031403011088800b03c00031120342c400c0c0d8501000400c07100b41410705000c0003650000101c01055181e0310f8000108001900e40f0034240351503602e091250455800b0340403140340c1a900ea9030042d6054442e075040c1d840c2c103e030410072885600c201c030300e00415203410b0081d510980d2054489600b07280594002a90380403200c4c04100315402218004507410f1203c0c1001322140340a00000e0080324941201b144c500400d9018492042030080ba0170800303040340207595540f1020541710327002d0722040d40c906045504c507000300081d4000d002156012184e580100a4100800c240d402070207100c503c4403070700707040742c1c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 417128830 1250 417127580 417127591
    0xd02090406110310031403131701090b15030c040e0d110102040906180b01030605090a0207020a170106030c080a08030121171305010804020f150c03070318172d03070b0402011403 78
    0x90100e10030040400124120302c143e40e009c40c0089164129595601340307003c0f080b100825030300920b440a035924181000301c1124000142c50070803a003802c04003100d43d90400940c3c001d003004036071200f01c6607552007034040d6002058030203c1401103030b442e40e079214149851030794910f8806151205401c01913109000b44c8048420240c20031310705440b101c2c80c4501a504c04d55003640c105a841d00002030004d9410000d00c20703211102700004213282903242c1914001c07107503800741003150300c0a821000800d1380f0100316411500401542c44405030480d04d4021240d0700610007614080c00c01300f44e01c480800c0300b0000c0540080070400d4408030750302c401c0156a90241664040d4015800951490180c1000313607a00340150368844519040901c04120a40f840e841241d0071000200780440a280418510840c07201401c2c0c16580e007681c1c0d40c1c180181b2940c3c2d814044107010007540000c4816001d00c0a034034070715486100c900a4036519207160604000400c0103890403070000300c000030200b481110100c16a405076 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 417130080 1250 417128830 417128857
    0x1a1302041a010f030f092306010503031c020a09150f022e0f06050603100f0e09030a0c1e1103100605031f1404030c020102010b010203090d02090406110310031403 71
    0xd0296070f1045000384030300c0c0502c6070103598451018000c20b00310b1882c002d500e030011071820340704a030000c50641006e00c183d0115000b54001c3c040410440444140c0040403030f010700c001070700c80c900034604888800c0e0b5076118482c5281c2d4109505046540174011600c003c0c916022920301c50501e00448001043e0f40700381060701e100340801c820a2002c55000010f50088000d4041210380d01c480c0007d005900035151084002c1000d002085008a0354900200030903007412544074900c0c00c071010540340d05c01c40d01440704000c0029201c41c100000c00030142552440c0c00c0304031a618a442c82c20b1a1003c81001480780b0074400c504001a4000f000d00807501a500701502603c0c840400301c2305910b00c441a0b14003040c80c0c0362100441c140103007400e0b00c07040c032a0b8001d6584203048002c0f4000a42124064210b0ba411034004111024054540d030100c040d859a0545900105036928103041c8010f094800a042d48141c0c004184812108515895000e4901409820204140c1482d19903036030b00c21a910070b260b4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 417131330 1250 417130080 417130097
    0x16020907230f0912100b18160207091a1503070c03083112181401020319033e09030f010f021b070b0301030f1a1302041a01 54
    0x1070880064091041100c26842c14040c0810000d51a10508060804503a002070b030030701d0030400180244052140180c410011018a100e42c1003941c800040122151440748001e1402e00361007000f54800520030f56108005140c0c01aa055007004515050b5520564115104a017800354440890b80200f520391106a8030f400559015a01246e005001302c0c0452020b00c40c4003c0290205041b022642503150400082841403928412420a81c00e00c0e01c01c0080364102d81c20703d80784100d072050613910010041c100b5200c1c2240100d00d14400c0300301001e00d85c0c0c0c4504007001c1700358154029034400e24803070304507200070300341e088500c0148000c04199001c0328a040b03480d0422243c0f500002e0885c403001405580c0e811240322101421b44444409103c1c51581c0000c000042c8007a0340d00072180c2007000300140070034514041080c2001d00042c00044c00c00307041489440108032104181400c80450507a518906140041030b220141101c43e005038050303801c103800c4146080c3c3c0d0100c0c024074517405844a124 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 417132580 1250 417131330 417131387
    0x50f040507090305071814161103040b040e0405070605071101031505031b0405090307020105030402040c050c10020307030f020306090f0c0c100204081212070302071716020907 77
    0x1400c4068580d00a1028514000c0003240d0103001c2c0401814440c2480c0450340c01c00700c070503070889012035507140d026111801072260f800d0008010340d0004c006860300d82045081295800d0441c850f46c0d000341da846000080008281d8080c1d107055100b9070040f82660351181d0345041c01d07130381ea00c95030030014440c8400078092a41980694009580d64100c6160881416103580119180030914600c00440e1030254107403194515242c090b032a400309044001e541808015400604503001c042c000078420b584400d4414940780c85a030a803104441800111101e0b80e4018201c1c4000398020703100e01000a040c04081d07400c80b0854000c43e405580040c007a80a02e0742c030700104401c42100945056500701d4100114070004008000d0b07050307403000150005a40701d280c40c8065107004103031000d00702000001d010703014041d944410141d5203d11641030143c1d44542a15104000c0420301e1111b100005010800b40c0c920080c61130741003a003d209039698a03107a00e6419058420070f01c04208090642615510940c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 417133830 1250 417132580 417132589
    0x501060f0f1a0d0c03050a05060109083004030305040e01321f0e090609090c150f130311090402030303010603151203022127030f060408090406050406050f 68
    0x20b58003070011641001609503801083c0c55001074410002074840c0140491041c107841003e0304803909090104485150031206a15624828072108814205100003180d0100c01c9043c0715007400384010b140e0381c45e6200e1601a0481c0c2042c0500b240749000c010001c951403100d1068261070014a000015038000054a1034080c9a415050319811400c0140c40180300040d5840040c0c0000170f03178861602d0b084805050004600b13005010720711813010102481a02c0d000803541681180058a0308000e01d0740040c0e8500352841500c00800d080301c80029107114040c101d001100c280c3c0c1c0b0030729408400440000410044000c00c1d10301a5044d0010401041074a000e80e200c080c4210a0041c007011141c0e5135289182c2d40480d11400358051380042d00b0300d514181500103644960155030f00d81c2810481114001e0300f2600d03031101d41c2d0605810001c0304148655080080060300c01030030080340c0c11480c01d8900420b850701b2540d0940d00441c00c042c2c000c50249024000c200a580e00a000e040c00e5410303840400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 417135080 1250 417133830 417133859
    0xf090a140c0f090607050a02040614150310030b1e1608090c18100e0f0a18050d0c1703090109060e0706020604020d020d02030a031106060409020105072415030501060f0f 74
    0x106c400f40301c0c500c2c025005031a20702801c1c00502e4030480060398540c0f4001440b80c200794421002881c0c110400421509070700700c40d03040341980d0f005240048240d40e062403000180c3c084140310044004800100f1800001c5c403000100d2000555544145644902211030f944d0794001c610207a22400c1c1ca1617410b104500c2e4864194002c0b284140d0348062075540030024074014007520303c00c000f00482402c01c00d4144580c0a0b400003890042e1000081d03c52541701c0c203460350b40c0100d440040041c000c074a0350a20940103503500701e80250001480e038070306060301034a0007441e021204548840c200300324441c2400c004074444003118500d03005418959119400c0103d03005480340101d901082c03419125000d030310200102001c85101c3d0301c1d03101405061003261032a1150003010944201d003030481c0e150050741d0040699510a07480b03081111000711095a190540502030a821041e038904161258100120350302c0e03400700c03030041c0000c1041d9512041c100740303440e4a038021050011590f0f0f02c04c0020640200c0d44 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 417136330 1250 417135080 417135083
    0x31a06181f020a050606090c39010e0706020d02030d05040f0b09101515030c02070509090d030e030c07052101050f0a0b040516030b0f090a140c0f090607 67
    0x14099103481c1511400381c00106040000140d00004160b01040342c20421a0340200c4210340b41c00491402c0846070541d48215400740c1000091010a0a5248034500481c400250f0b00c07801084488c940e0300056000f0f16207040f121516100f45000010b00c9800032602e0200d2440c1a0301840c40d1120701c100c90000345c0300191048170140d07105003505000c80c4d4051a00c0c2c0c000c030ba0f44000342c1441503400103900160b51440e016540242d5100780100403245074035646420004860402144111280d00140d0400070240d0009810105120801040309000b0070002c0c804802500c0820841165009180c5e580c06911030302e8405a10945060007035240c400346d12640500b140740704000741c22414000c242511805d4503018503140c0d4440500041d072104d03024100c0c1441c01920100036500c1e010100c8400c2010031030403901419035982480d1841d85402c51800e01c2a40054560f000600301410b10400a00800403000400071584001c28100d070304207011140758910b50303580c0d03609002c0d1410130003000740d100301c50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 417137580 1250 417136330 417136339
    0x30f0c02010c080d020309060106140304030f0e04050c030105032401030f0c0b0a0203031006030b010c06020313061b08071403010b0315090a0e0c0d0b0a020307030618020901031a0618 80
    0x1040c40014610000401031044c0900015032242460140e1503d0510180c024000740002044066080c60201d020f4990107909894803882012200605482c41a2a00d0790250000d0920007041440000000214100c1d03000b40c0c12124035107a50a919103d022504d8101e07005641c0c840010404120703c4104203983e24001c02c4011030080e03440321403102036031208000002607003002c0100100191081444401040c1c60f040c14000d1034803050000740b6403a44510003c0c16603502002003201038040c2c6049500b6039610103410020888011480380c1101c060080c0c480000d40074000090000e84201c03c01c032410100e1401d11404c59080000000a03604020611500e428160031940c0c81641c495003e40e02840780b45c0300015082c51103020b1182445210140ca03400744071114200300000f007280340b8a83c3d0110700e102005032280c55040d01100644200d030300154680780c0041c10184102c0c015030007800503400c242c034201708642441c6001130114a103104070981c040000e011030076008400b042980d40e9500c0040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 417138830 1250 417137580 417137597
    0x4170a2a0312050c0f060610030203012105030c0102070f0b010b0a05040303050313021f02010c050a14090d050a0c1509121202070e0711010e030405030a120c06290904030f0c0201 78
    0x4c043c504d05544402d102d09903900c4007007405464100070034040300c10302c6280390552840d81003604844040307401c10701c0005c107004201c1c4000b0038087c1c01e205480c440000000250740c0c54140c1d0900d1007104c0c0f0400c00c243c41c014211800051050f510030101c0e0b640c40c600780c4030a8109880d5480c20340b00b030f4000410391003503412022103e00069483c40e52860a088030020b8500074110340c08402421140c25005040502004103da91305050f002441608101b4030809501d0f0368102e03000105546020356000100301e881604031440401140121b207000b500d007404426140160480e208944811891044c2c01d0f001c1d08031810ba00204640c810321051a0800d401180c41c40b80c2c0e104c568281000c821514440082d00c0c084110070b15210030b018043c5035550143c0110308103410709001035140c20700c5503001030061100c0002101a680941507644203940c2003801080f41c1030030008512035140340700c084490b80a429805c01d0450340b400c0c4941034060380d0156a441072a031014141030310105607502040e0706010405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 417140080 1250 417138830 417138847
    0x40e040b0a02041e0e070e0901050d02120706050306100914060708090907020c0a050405010b03130507241b0308040b1e16030e06040308160504170a2a031205 69
    0x1c0d004c00402d034850400e0454a001100650310b540a80300310100540c0e480a4201c0da520082031606484084450002c4200360f8070010307d08550007079040c8054040d4841c0003541c07640003000341d4481c0c002500c141c40c5444107108200d4401d51680030b1042c001c100c260708c8451900303110001d01a218419402a03203409084c00010754101e004a41400c0140d000d046025801d0400000e658010081510b0500080d4148001d41c2840d0000801c441d00c10001c592200040c44801c00084008000003640050000d50310994581d01c1c2319440161800300c1d0034012201229440001d4401280c3d426035104829034030f42d6900c0517040f200152503002011410000e4903104491210218021072030034085d440351030501e00c40a000d03a14903a500a0b400d4006104100c04260020001c551069031005511030100140700c0c165024012600001a0038440c074580c490702000c002a03e85409026840d82003101d81c3c0d81c0c40304135001c0d00c00c000300c03411512001d40420011340220260260341d08203041160030603580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 417141330 1250 417140080 417140099
    0xf0501020c1e030a090b070204061a040303230d092f03100203060306150a030819111b090604140915010e060d0b061207170c06040e040b0a0204 63
    0x41c0020391541d0300125020b550005500c410888020a07420146040c407648910241c0804400d204680d51003030001000c4046594030350240014003d002d0b141c120b0215096001400781d001800103c0119000b440c41c8000400c3c030080c00e16000c1040c0c0111407030900440c03003a401038590103404440d04405901900803004801d4614116048018941035001c101c0800b0145008420328119810520401c20b00c00030b52004140e0700d40c4000401c011040d130300400004074410003c0741d80081d110344000704c0d010703529801d54150180e02090035507520304051403c1b0030f0306840f941d6030039400540c9060317900d01482d2428540d603d5036200000600c009420500803a0b1202038a81c00c4450300500d0300071a000c05c480103c01414079000d001c2d148841100c034030b000004200070ba00244000340c04504220b000800a503511091540f2200c1c6880c1941c2c0955900c5640f0031448450003081ca2550081201c200114101070040e10120f82c0741a0f9a01d250b40c8031600c440b00c0441010300f00c12400c070b03020080030582d00071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 417142580 1250 417141330 417141337
    0x70302010f021603181520060a1a03150118180302071d010e042d12030b090f041e051b010906030510050108071116080d0f17040f050102 60
    0x2034420304409041114a0028614000c00380004003180d4800e200384407841401651b0540c040c000d041802c20f6444200352800744290004800c2e48a1080f4410410000c60704d4003c00e02c071410400c501c02c4045d00e103004041c0c0328a261030700ca043d1900302000401030175806a950003020051410001500c140301040c1c010048150001913002d68003140382049900000240c1890540c05d841d400481d03941440d41000701c001006d08050909041d000003600e0600c200042c404800e440041c5034842d104e014a49140745400c51280d2a0200f440c068152005007811411588120b210b0042c803a4156200da580300030b0480d155004102c880840122103001400805c2404521078058904070044c0c2c040b10001840a456500054201401c15003884000d016025006040c0c0e182400d20b851995500481214082c00588103038043e88121380c4059101c0700d10002d42c1083d11088400c0d5500920000400e945540b49480030500160320b03229116440c074248000e154115108041840f05c144440e11240e00360b82 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 417143830 1250 417142580 417142597
    0x6030a06050a09050f0a0b100b0426030714010501060215060d1110080a0507030b0303071502090d06020702030111070506130510020301060203270f06030a060e0103050604060b0307031205070302010f02 88
    0x748112452414020490307c0260b00c004040c090030f6110b806c2509985950140d485a040024084c40e920201c0500d840300140d08002c40c80e0843e0b880301d00d5420724184a005103603c4140e40d500e0000041649031010404d140304100f45000301c40f0b41d40b2001c080c4920a2142d110507203e070001180032079090713584e490340b01c000450300344c1e210441c1d400d0803640c0c0801c962014090405152500650a030315440220541c1d07192904912000400e0614200c400042c1c4507030006194021040e403038100030881e055020705003050095000f0007101685403e103e90901c60444042e015500c094001104900300d502d200701100d1048041c0c80e56804009191426a0400e030030034000f507040400c5070310403400c1c02c0711400c0780d0150604540002c01404804105090801030f0341074007582c800030001d440030200f5005040104190320155010b980d6900341309440713800c04d80b0112051820090031400724980002d0650540fa0480e00c1440c107031039031110954107a4040c1000320b00f99500c95043c03d80c040d503241b002e0a01007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 417145080 1250 417143830 417143833
    0x61804021606051e0c1b030c03070314090f3a03030507142a0d08070f0801050609040b0d0f060605010f02030c0d0305090304170c1806030a06050a09050f 67
    0x800c0700e8600300c41038990081448203008a0503200000142e090360041c0d030011030010089903952014010f903400c802c10b03260b400b0780500c000a40c01030705402c000700404485000740d40e84141c2c003201c0c0350b00c00540e00c90f84440c41c0d030002c520000602180b50400c04d912208500c015011328444485007000e090080018015503141700300500c07002407541600400c0e074024803502d400301c031061a840040301c49018203240031110f410209041c0c54492802201080c4500319107080307940c12802c440c0d00070f10781c12080710501c00090b000038142070020b0180c040c0c0d5059660040c14141002106000c0c0300060014a0300b030780d4051400d074003070000b00b00d40ca40400807050080c580801c441d41844000341501d6001d9100c003007154010050070070080c00200342e080c5481d03803a10b070124003a01c0d45d18025241d40615000510040c0080300c9050701d201300090082a920401d03142d403510a01070040c80340c80c007230341190b155416802c48c408500001d560340d0304c4558011112100040c4106045d252030389803181c0401503241e070303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 417146330 1250 417145080 417145117
    0x50c0a0c03060b31091e030314190507120e06010501030b060c03070b0702070f080d0305070f0c06110408160911031b07020a0e0705030a0b0301020405010e06180402 72
    0x24414540a00d658002c401c0d40e100d131810301e540a41103902c020000c00052040e000001c0f140c003103081500080b48660700941c44481c0154040c0c0700f00143d4442640c11804640307801c420001002c00f00609600c0741212042c0c142c08815030050080c007a0100800c0d00d410410240d0f0002c110301468410001d0040400c0010846036050200240413105800205841140c0910410311031807030000c105c80b001503010602d0320403511401d40503071401e180c42e0010345000000384004151444006002440c04420b55403c5c001070300c17201d6040c0d80c599000d0722010002911104440c0c0810700b0303038000400c0c6c0e407003414200e80391580c0c07084c1140c01d01c10a00b107550a128210242040540401d0103506201010b88408614504107043c00c8501c41c2020400d0440d0844013103040010b660340d10f03c41600508040c0c550311050b242031354004020342e0084901019107458451040f040d03040504c03d42c0d00303485060311080540307002c1c80b041021a804c0b0b10614244a030304a145045142c440c0d0000d4484010300348010000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 417147580 1250 417146330 417146333
    0x33051b011e0912020c060919031a090d390611040608100807031511070605091504030e06090d02030f0c12030a170c09040507020616081504020a050c0a0c03 68
    0x100c00c41601040f904550100300d65190b1903803008225503e503042120000005000134a83d00b1040da40303584094100d0342101016440300e0200d0034100c6c8140b14034425a040c8a0038035000f40c0d004803840850b58110091030140c96540f00305169801080e0b8960b08050024640d2079075008140c0781c4a0002c141e90343c10112702003080c0747e00501d48a070407000b407030200185241401c1071a84d03107224510014003520404607900c0c03004052a8081047c50344129012a6182c1032402d1400260100752441007161213110355034500ca190381c1c0b603030900a650550355074011011707540400c4440d400c03815030590300581410708a030045c0c1d020400c80b03a80c98003d001074034081d1881c1040040d2030405031011040c0c3d40041040083c05540410302c05540c4072424103c400a40f140800c1c41540d000d00300e0314941051501e0b080c44180da4000590f9031040306a032059400403946451304440c100000e860403a030a40012030030707050901d800c2d005440c0b1000a480c00da030810840503086031900715501800d0b01c810001203010700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 417148830 1250 417147580 417147593
    0x1030203040f052b020f0a030302091513051e01120c0210061d100b03070302030a0b030f01241d04081201120215030c07060906110433051b011e09 64
    0x501031030550018206c94510395801c6034407002c4d140f40c02410154001902e0080d955242c198100481141100a4448854448586501ca03982c01103c0c465a01e01101030b042000007010100c0c01441a99070f806582c030460286006042065400d0341540154441e03d400c1000d5446030600402401c01c0202648810f189003010030f42c0c000e80710180ca411000014080d184402d000c40384c1100f45440d0040e52950b801050100800c2a031800603858081e01400c03c119144c150464007266601c211320b0850306050503600709200e002c5101d107292038295100da412601062644481d40b00c1d000c0c00c4164a401001d00561180303500907002720f1303100d080c41c0030120f00394103100c0c10441c4c011903100e0742c42d89141003c810718280d1307028a450041000f42c40380c205900f00101d5412401c1c1c0780014041c0c040e2142d40300c0d1518400d41c261700102ca103a1a002141024450003c019065140100c50b1610b520b03054100c218845100242a154a00d42d0b403607180781d0551500d80000107030909500e03000001c81d21150315049 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 417150080 1250 417148830 417148903
    0x40b220509071715130807030e010516080306191a0c011d07150f081801060801180308090c100804030c2001120b033003070e030d1d01030203040f05 65
    0x14110b0b134048101701c1000076038000407251600d40505015607100c0b031a10049440d480741602c2d003c2c0381240300d2062410880b071500079600500045032548940d464025008018284602c290160455490a52801c58983c0c00080841950000000c105003451147e840440c00c151044e2050940c0400000c000e0024200800913800c0d51790310703101c8003041080100400c03515000d0011046c10320046420a860a401d5014200411190b0024011040c11500007008010400700580c0890801c5000404100b000b0803070582c001402429031284082240c003ca81d0600014022800d12216070200d41c08640d210206a15400002801c0364200e140d00d400144648040040b59200320f0078000c0100c1c240d90042140c030405c0d106d80927000054207020508035441140d010034480341d0b1000200b40708403990301203100400c06000703504903801c40701780c00e00071a40170003100300d4070303c0244805074070704290740c4250001c680042c050448140c3e4101151620390803d0340746911321b040c1d950500a2800c02c0084034206 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 417151330 1250 417150080 417150091
    0x2041404150c02030d0b011704050d12090b0411010c0507030c091b020c0f04021216020d0c0506040f021f0305040b160207030b1023040b220509071715 66
    0x74000ba0b660107402035030b00d019075100703030740708030740724200e00d1a43d0748a10300e1542000000440c500d01703810f00d400c0c1140c40c0c1400500c4a40040c00040040040441c1c0e800b440300d8040d840104164940d48075140c07041119540c8490904200c984841600810410489600914081c0b114141c02c075251000000c21903401d44040220208a0305a40c2c501a801140342200d001054409404406c2c4c1040018000d1050358040c0040f46a13410901c0301041ca640b0032519106055001c544000d0311900c03058951590454008185503c00d1002a000600c0c80740c004c40c803684060584c10b0103811050116860026100c80400000c2c0e4810800040c443c24044464000c000310404a001c020844802515001d45010241880705500c1c082040310b00700e207900030010b003000081c0000054600011903801c0c81023480c110720403402e00313410302201c0ca4841040003c426030f0740254516120303208101000f070038001b088001207006001000070400d619134003070b1076061031b05030141c031010080714601c0180768006400e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 417152580 1250 417151330 417151373
    0x3060b040204030c0e010824070f2a02031009170903011b0e0a052205130209010f08010e0c1c03111221090a03081f090207060b240d0902041404 63
    0x100c40c2d9403d08d00e403c485820a03d0313807428a403446281c0300c1c03d0360000300c141401c0ba40c490005d051804103405401c00b010304030b4803c41c01c0d2426980c407941c004080c0c80726260090001e03405c001c80c200858403a0001040ba01e0000707000072400d12500340301a446040b0310745096011842c8400511070078a0100c1d07218004d040129204241a104909040d180c81890422001119561004240015400e01300203c540d0390081844402d51703190a60302c0c50400c010700c5000f802c3e60914164055482d00414100d00230507010702080d00480301c40b23904180c940c0e01d23030700c064047c040d100044100b8007809000c0303e80004007a40c0700580d160300c10b036a41d1800405044c0c0c6071441041d40d02c1408000c45c0042151000c1c1030305482c0001d0b064692032100b110581d403c4281d1202514a9600001c4003140343d0050880a4003034002007140d0100501800040f01c82082c1510703000e184007900c610004c000708054000c09140c1000050420110f5010034103c502c2803d440040b40d1203a0f0400040065068090a4030b820460 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 417153830 1250 417152580 417152623
    0x40e04030c12050d0c0903170d110f1b030a170c1c1e05010803070323040e07030e0109020f0112021b010209030706020313050f06120403200c030703060b040204030c0e0108 75
    0x4a07608c220050b4020b0349030345403c000030807068240140c1c210510035505050107a0783c41081c4100351903160321000204401c2043c22078002d00c00034010090310803903011174035460042a804030883d89c00100082c04841c0c6001c2c1404989400c83c201c1c0c0481a02c001c04150014100358800f4480050603c006070046030603007004010711284402000392a0100c3c2e05040200a521006035008010000401200e86420f4082400504420045043d60007041c164408011404e61031100034280c2e00303000e030081d4102010000c0784084e0751003900c6518600d0005000142407a03001d00c2c0b02c0c40d54001a030b0448005a4012406504918062102c1c0b80107011500003135203010112a54140d2054451140350700c80d00b03d0714010f03083d9440d0401161000000c1c00c0401150385440d14014114145070010750f85a80500102c0d000c2d8580e001401c43c60b00b0324018001e10075207155a4803c40030700b020440701c0c2c4e0465024800000024200444e000103450380103125540747d0704140ba00c91404c040207080143e0402c520 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 417155080 1250 417153830 417153833
    0xf06060e060f091201020412050a0c0f1409091c020a05061f03031b0b01180b1012090c0f0f090c18060e0d0b0a020703080105060f040e04030c12050d0c0903 68
    0x74003c484071050142d0b0090b28129a0804003130090250ba80200c0c801d10110151004011020407442001c9110300c244851031904c2d03480c0080700880f2030060010b265401d0101d44004d20b01022201c0c0d0003003100c41204c3e4640500e15040c1252941d088901c40903034003051143d020000700f440000e52041184c0d8100d0854065070450002c0c1001a22018062201e4400002c050b21080038100100c1c80d08554091a00e583d5038440402480132221742c2c2181510704501d1071501d250030f04c003e659044280e0781b40b50500c03022a0302c00004101e29001110301001607140040c1800d10600d800c0300408440303140001052811b42c400c03003594001182001000031503250034410050160030741003034071668a0b000304140910740c00b162101c050020050034803100716007000390300404c94005000e65403081c4c0d21241c2c141d9968082c08803500651306e4020b41d0034810320083c482c1403e6010301c00e5009020b0700d0240340391102c0384c41c2c3c68003100001148500041e800180d081c502d40e12800340c2d2021001e6486d125110a145 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 417156330 1250 417155080 417155107
    0x905011b0f05030a020c1507021b0303030601030b0a05030604141506010504061d120d2601030b04080f0310050f0306060901060f031e02090f0a030b280f06060e06 71
    0x1c0148405121011000c00d0300e507030281c0e043e03030401c03e01c0804440303030f40d00708032844042120111000c1c001841203070303108103010144001c66244d80380003400440c156120b0000550291892210040c0c10080d80c10300028a0380c1c007001028002c03401010301c401340d004e40c0c0000b282060403051000a045e075080b01441150390b48407084504541c545d00d006240d076600c03050007140d158100f40d1740d564801400f4200b2280488085285503030104280c032502e450403c044000d24644030b042d106503000c0e855060041000c11301621080c1c0d8001c1c40390348541d2404240303801e24003250304141e07900551200910011b1296082c1031805a0312010110010403140c50020300041900c14140901801c01031a1080320203194001d8018007150034041795503070b44e058a2040755000039007000ca00340784100d0300d403d0314000303c0c20800d00c0303001680e801200188036661100d203132030500341000c04c42409400e0000d54441d1030621512841040c00a00c0c0c1c0003141042c94039200800320303128203040c0d40c4145020020030030701c10003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 417157580 1250 417156330 417156347
    0x306050d0521040915060201060f0b03010b0a1b0809130207020603070f030e0a050a0c0506031003082a030a08010b09030a0b04050a0204020f040e1b0a0302090d020a090905011b 77
    0x10000380002e84200c6010110344030b0040e60310680d401401c0070300c444440b120300c8002c02c00703a913401e074020000c8035968840500040700503ca40f0f501e0142c01c10041c00b1110300ca80007012904180d081105d140c450b01c01d102502c00c940749006a0325a80007040d449032500c1c00380001c1d010310301509030030342c10000c541c0c000850510010b010340c0103002d24110b003406141d000e600110349801c01c0700c1c00e40e00205100c7c2800307510741c80c00ca00f003280d13030a21151001c545480c140d020b030380c058040320120307404081c259a20007041e035103e20403509000c441608100004010103003d00007000c105000b0f10348035410000c015081d41d0701a0003580c65400c0038407000c681070301c0000b5104105900042d1403400ca4aa81c02c2075402c1c480342c020003941043c00003c41c1102041e4150007042100c3d00c0c0e41002c40035680355005542d4254030900301540c0c2c0303207080040344040c0d4070079005400c406100901283d4007540e52b03800605880a19440f0b108c4913034440302040107000013882942a0889003e800090208001c4001040c111 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 417158830 1250 417157580 417157603
    0x50d020a11060c1006180b040504030504030212070513020a020c0a1404230408040815090604030305190903031a01030b0d47070c0506010b03071103040306020a0306050d05 75
    0x443d607982501d000b0450030b00c20002561040120715240d10000034983c904030084094541070101d0602c250400e80b10301840b89070142c1d14581094156802c111180081d903442032040d128144010a40f51f50303447c02c001500030341400060b610840002c029003403c043e84009803140c900c0d4281005505490b101c006170180c1c003140c0008a11181c0e2581d4000c1500d40d0003c68400103006041004114181d8001d1095907c01411140014180001203000180c1202c0400d0160000c0001c02e0003c0e00075000250482481c44a410042040350502c4046070409803080d4000703a00c90140d10005610311501c0c016203e020328003400106098030120300010300c80103008111554100d200d130160180030030f00d01911103803906040038400c0c04034030490f05042c084003000c0d014541c0c40c0208260314003881c4880302d802e80c0040a000d03640e207800005085500028485000d0281080c200c04803500c046c0000c2c40038605c0341200584640040303a0080c22940c00703400c031500410324590f9002c04030740005a80803652 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 417160080 1250 417158830 417158839
    0x320310170d030b15030a0e280609020103140703050a06050d0203072102090115020d3209040221070905130f0b0a090b120105161404150804050d020a11 66
    0x10450300403900704061507601504515011051000d20300c1d8076086081f807014034000710f07070180d02146c564240c0c100c00e42a014500200c0c0344480000508581c002c40c0006005050003c0c0c0c40d0b4101d8150601c1e05c10444014000030f54420400c04001e0b81c510554001d03010648400a0040c1d16034003090303940c0603a002d5040320050312503404040c0041c0240400310168040c0c4101c00659403a60000002081c0d45d40000141c0640b94110348410b10501607120300e20b5440a030b540a0344140d00030fa1030400e4101d032080031035010400810416071542d0004142c0244030024000d03403180f00004840c640f107805800c0400304070322020204030541d516011110503001ea107070300055100e1034401a400500185081c1ca802444280d40011506026400031f03540c0341081c5c800070060038410b441c103400ca0300d04440890b00c2e1a0081190003016210f200d01a442004000409140c00e88650004500d04007002030b0b140003030008010032080120510160459200074001007005511690351000305012800915004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 417161330 1250 417160080 417160091
    0x90105100b1219060602030c070b0a080619150e0319030206160509030715030c0816050703050903030c0726030412050109060608010203100b040e040201320310170d03 73
    0xd504945443d1010341c200c400100000d581d9040040e4980d004402c1c00ca0380c5005171800004c44000d081d040301c8584c8000e42e1544843e03a1840e0411198203809030994104050400020441404407503a400c45101c0649854050340000c1e41007500d01110340210f00c4d05030400e80010740c0000d800150713454004600448403885800108030480e164061071819940c0b503c280b03440042c5518800440c1784184c400340e40d0502c1440c03c0b4002c1502c0c1c5d482c040c1c070001a2420a40d820042440c403440141101c64403901e0310510b030081c0c541c00a0f03c0c6130000f000104e6182c0201e842084000a95041d82003002054111030b071a1074009400c060300c0e80140d101e0840c401c5210000402002029409141915801501040140d48a0305080c1c004c1d0400c4400c2c01d0364840c1d80d0408140409044281d030105d81e0400072403101070350380da4011290318411440120400300c185001c45e10242c40050701d149034061058005e91a880c0180ea00c106201e072644c0880134214845000d044225808071ba61135450083d414041070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 417162580 1250 417161330 417161341
    0x703020a0c2108071d010e0607020406031104230601081005040f050f0a060506030c1e07050a0b070306030519150c050c2b030f0f060e090105100b12 65
    0x41c1d11001440c010a18141004840d800040c152042501000e0b180d03140e20b40c03582c4104095514440042c44071410b464030240d560703100d6124a007a80325092010f40740c1c03400d080385540030409441098108407096950341228810300c0c00d0034821001059030b030804034203085800000007400c050001e40000d04002010000880400444901074000e08010304100081952805450002c20741a182d1100c01d000c820b0200c3d001c6012401803800380ca100510306840e6489500c07903102a6401b64002c0d035a00e00c01040c1d845600c1400c1808ac01500d40a20043c0603094043c1c41d100d51460b03001002d810230f152510000303101203000083c201941e00c05201c1c910808400500380b4291803143c540042180030f0510000318a081d50060141c4907905c4000200c401620b90281d960a1604200ea00203490604801c0c607064003d00c40d4100c42603000d0111000901000c50440034010754401e0341140025074103070824000507074003d11600b58001131035000d801c00315007403554460a40c4144000002d034941203002040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 417163830 1250 417162580 417162587
    0x10201090b0702060609010e1006050310260606190b0d090804080d020705030f060c1303081201030b09011a27090604052a060a020a0c0e2a030703020a 66
    0x4040c0c0341c00003078150551038007010007556103100700d5800b80181d803090000074060021800740c078010700304454141055418000300b00e50070340009015564001ca6441c0001d00c1052440120903051004108001c032804820049442c001000e02582e0107000c034581e80d201d1603044040100d00b074420010300070303580d015500d0f40200034090915018141110004000031928000145806904001d8080e20603090703a8400701030302e030302010310400c0050b0021000900040601002000015004000c90b101c2d0782d101d07102c2101907000124640040e4400e00010700a00042c405090790001c401d0000b40104c40b0f0001c2d68030102c0240ea8511030182080380500161148685a01c400d400510704041495107010140d540c1d50351420f50f015034140c05400ca070200b403542c610349241e4042d6018400d013000e44509100303020143c3c0c0181a10300c11400742000c0a40015a4078503418010881c003140c4403400c1c20102d031488080101410500c1c3c007441d51114000310459003070240c0e6841600c50500585410f8024000d5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 417165080 1250 417163830 417163841
    0xf04090809041a04110708220f060f1b050c19050910090b010215190e151005040b0112050408070f050105041101030504020f040906020c0304060c0614010b07060506010201 75
    0x155005051400111043d9801c040c0d15004520445042c45901402a0f0401480c85940030107800010104600c1900002c000c407807698506031500c002d00b041d0394403812320100442c16000f09001455a0890040c6194404031811001d520103051194100503951600d03a0382008000031401100c014080300080140c20059200502d0050032120311850700010b00200c2041c00c1c0070f020b0324180381a00070358983d480011a500a490f0000c0099199192490101c440c00820341c0450820382d180c840e1903206c40c0c0d080c409501d01218204504d8610300b0101420100e100c100d8001c036019901d03000c185c220f103a03804003c0d1400320080000008264580341001103091007285030140c907a2402075007050401005602c902c0c411401480764580c0004c4220044040c0c9009480280d84506400140310881c982540b160440ba40f02c0d22006280089408240d405c5400980c8410301143c50b05141005200003801041c00a90f010310341c680383c80d8103012100e0a203002e4100054a0b2139a0b07000041e40a9000b54000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 417166330 1250 417165080 417165097
    0x1a0603100c140a0203070203120f0d1806020c060601200705120f01050403080a111c0209040b0a06020705010207080d08070f03060f030f0510060515070c0b0c0105010e0c03060f040908 80
    0xb582da00c2d00460040c2d0340340d128060482c042c3c841d20b0080c08900c142c0f0703c242c50900360310303c0da440d250185000ea200060300d51611410b5055080c0d100c0800003400c03a00c0201854120103003d40014907000c0009001c8001c8800d8201122250000101040382d000c141c841c01d581d070856140042a500c20652032424510480744603c1c0c1d07103040280001d00d500240094814005035805000c8040340483e03000f510b0203102342c00c1c07030081c81500b4160345038070080d009804a02e2002c2c2002421000a1000560b102c2840c1d1020000d81c0140d002407100e0b503818491003016220a000800e154900501c0007054620010206000c02c070b400a200c4003800c0c80790b08a24010401d0000d20ba103130b03507200d00742010b815198440441b82c901c16104654180340490141d0000c81d0001404c5201900b0000040022980715200445805a4000d00822001042d10103006009802c00000880b90b04100c003040c0c01800162008108400620800c010f5503920310440b40070240940b4003141c098443c5ca419211402503a80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 417167580 1250 417166330 417166367
    0x920041205030f0a050310060c050703020f010e210c1c032f03040f15140f040305030d050a1d070b0a050d02190f090b12060102030c0d03091a0603100c 66
    0xd408121550203001b0b18018101d086428081d01c1d61558141c4d100c0804000080650f0014a0300700094640a031038803121040c1814000010294400014160100744249000188402031050011a000c0040618101e42651141111800724036100c20701602044014100080154440c541c8a004078a04000f644904c402500074980030411076100d8006000d4220078801018001810030b0b155280e81641c03107001e0b10741000314880d885008145910118441844040420001002580400081824020341c200000d0b45041c1070400e4810343d00400c0000484002050344c80d0914280442c11404440302c041c00c081c2c0e18610100282c0c1c4a014003160b40380e85520105071250071040601c01d2080d80c0301640d4600316100c1040704d007500c1c0b0b00980c0c005ca0743c1070f00f404e005031448000850300751600484140100d03414068580c40722807604070780001407000291164000010402c00d25405050300b00900302c140d20919054000c40d03911030b08000e0800e03655031140f5103500f50500501e1016001110740f81d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 417168830 1250 417167580 417167587
    0x7080a020a150614040c051c050f0c09091302010306090e0a0506011e090f0e032d0304021503100f0f03030801091a0d1118010920041205030f 62
    0x4081d4440e81245020344414000403540b24600c82076109840c00d44211081c030005400d09401808014880e00448000b44081008000180a00b4500240800310135000102e11441c01a520051540000d040c6001d42002403065140701c0c0d941c200d10301e83c01034507411982c0d44c441c142e00040700a01039a0740892030140c6000c0710f24100120100d007800c2c642c0c0c02071003101c2850b40d8807109222100000c015000c01d0040380141400591456080141030700d1010710b01040d00881059040e0851f4040d4965201304100840300480c1c6180c01044081134003d034290460952506402040b14292440345480090100100180722890400085005400029044400282c8445014944030300c01d00058010400a0000103115000f901810222081020451500c40300c4d00d014020b0103010345100320713040c02c1c05114140b107503200e00a908072220622115141070707503d0600c1326400c0311045210b007500080314542c00b4800c40e405d5801c50b411502c900c000c040002d48517061081c21401401c441c040104c4001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 417170080 1250 417168830 417168847
    0x5090703020703020c0108010323030c070602061807060503010306050405011e020309103b0a030504090c0201090b0c09031f020403060b060408100c120c0c0b0a110304020d02060708 79
    0x1507002d010401d109400300c4402248407401520149801d03c801400c0c2c001022000c1ca46940390300d040f46010f030f259802c990500c00c0100940d1f0a054440d0042d0005a0182042022410140030348003103148900c0b000d00f03600740c14410006c041d03100501004d411680ca42000c036080103400d500c04041c035004d120008200c02a0320b65440041d60080d5981406031040103c034030040411485900c500b02c07001d1f88a1001511002070f29001e102d841e01d503c0441e891000700b202601c06041c813884001c10321917500c190b41c46080c04089407c5814214401c0c0840e031401490100041c44500b1041d0000c6202d402581c07140000b00c0020f14191940c840040c450368000004c21754a144c070340160042e28861402405405070900c180103c42c082c078031420240350f0104a525100e000c0940c401854480140751000000060b0801c00d0251080080e0140014403c01c0c281030a00074403c50722a041b149215041c4216100600c600d00e031400060006880781c00a494007908566641c0100e5041651002c001e03078503030548 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 417171330 1250 417170080 417170087
    0x60309030a1d0310050103061a1e030c090f09060c0c0c011d04090308100501030e030a0e0f0d0f050d08060310271a010602190303050702071e05030f1204030b0709050907 74
    0x17803104030b0740300d810404074500f480c20703010b40038415180141c0001e48542c01e074500e100070014ac024071f0135014000e00e560342542d511680d020318880c00c400c00c030401187c1006c5202034940741005114071003c602c02d0041303410f084404200c0c06189402440c0030340c0d2840c204000644c400c412245415445803500c000c03401010340180f00e40c0d2061071360404003400c007941d174401581580d40c03a6801c00c3c6190020007108007494001d003104500004040e0030900c216410354081080e080060505694041c910b04ca0302003000002c00c40b030b080481c0c480c03604044506029000c2681c80c810f8800c0003030741e07540f165213500303002160404a2010603031080f203020604005080504240030303445d1284003181c0c02000040703a06400010101e00d060419100750741c0314030722034404038001c0030040c21a03000c40c041e401e00040c41000d009040000880c1c460056142145007004040c0742010340d003501075081c2c000c402c0740c1d240340c98094260b90499811000b580c00e165034039002100d184859030491940050000f00344610280d2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 417172580 1250 417171330 417171341
    0x7030608010e0c010216140603100510120f09020120010e0106060e030d02120306060304021c05010f0b01020708210c01020c071a0c06010510052a0c060309030a1d0310 73
    0xb07809407a02e41902c0761001b21021958001e40c51100c003d40b01c400203a0528900840d8803c00000c180c80714207481d41c0000e41c125030b07807001d4a000569060303c00e1008400038480d0110344c407641c03801004a10510307070000c2c1a25403042105814003502030840e2505200a40101c502d8100010003040a50348503100500001c144005c0e59009205004d100b50505000050880104003620840c909590383e10003045480e5000034000c83e0481008400300c008260040408101e03684501e0001c034044041d01c1c1080115100c99100c141154442402080b1043c000320381044c1d2031100390b4951103c0800042c90001c02e1040044040d815840042e80c8100b40c000403541c0e0701030707031040682b2003030b402c504507105010381c080c1c038411042e26080000104140c0c5090780b4004000c0c0002d04200b81811140303110620258510b00420f404a91021080c0c503440e5014001058041011030310242142407440303007a03a990151210480c1805403a4440d43d0040752420340802070ba01c2c004045409012032040400c01510 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 417173830 1250 417172580 417172603
    0xc0118081306021207020d03030204052e022b140a08100b03010b0d150b0705060405010b150a030c09051e01080c0c030d09020607020901030503120a020a0804030807030608010e 77
    0x80d01c0d24404106a0701c04100281034070080001542031a596800300644000b20040440c28503500700301c0092141c88240a4121000d5030921009238064603040e0104500b20b00d00d070810071504410220b05804480303082c1c0c1d480341c0820a15204101c000007105550040610103046c2c848800403031002074955110680c20700c60310481040c001d0407940c64109822502080c041c2604a060504c0008588a06903204480198400c7e82d5040b441e030303580490510561001905685c40d0b0410010441071041c24051640b2403102030b15019640900034407540014080c0944803010951503010201c8280d10a02144014100082802200303000f64402e00f00c5800650b0015400310b107050000a03d00a5803000f81c4a00c2614403008d940b500304650b8104006000c900c404a038040d030180050740145e125200c0650103503100f00700661b40d9900b09540b08000b6000104200341050040082941a950000c06641c0080d410305003100d685c2c9503a5015005000260090820340d80382103e00200c0b01c0e0000340c1d034000d02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 417175080 1250 417173830 417173857
    0x918050c09010b0304020111010f050123090601090312030f0f060603050601110d030b01030e0a1415040f02010c0f0b07030605180c1617030a090308010b09150c011808 73
    0x100c2540a00c0701d80c4000340310700903c80e04240002000355004c2c1c4c449083c41c100740000007860b060300c80c1102d81201e40a8001c03649558041c002246814980020448807a00480305015140792a4000a10030300e124040106446410321420811074042e8010451795034018006200c20512007030b4807001482503210340710000e07090002040555001d04910700c0d4844811028103034040c4050026030282120303030141030415948841003039102c5428014020410b02c82c0d1100300700040d81502c8685000102c000503d0301c054004184000103903520f41e10f03005150b080c00c2c00b0400944909191038405e80b043c1002c2d05100306031003084415541640300c2416904210b9004114545100700c07042c0c06042103030244102001040f000d070041c60b07140c8200010a22400d08000007520104050820780c02c280c0f5401d14258a0711041000c0682262070365006d49160401c02c0e0400c1000b40000780d20a911000321182c8000c0003440e400905d8003034011078540205401c280341014881d107082c2210307600c01c0c601d00410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 417176330 1250 417175080 417175093
    0x1203140c09010f081305120c060105010912111c05100513030e0f030f0709020301050103060b071109040c271d070b09010302120c07020406091e0510091805 68
    0x501880c064828500e01a034848039a01c14104090703688240141c03d44902c0740749024160700280c400c20208121801c140652900d400540030130500e4940180c00060520088440c01e100b00e90120221503034140d00f040d600382d1448514400319424200d000c0c0c00c040000483c0c1080d00078440c1c00151064a0b9411032401c005643ea8481e0703403001451550001000291185001707501031424400301a080e07980101603801c01183c50015a1030105242d115031a2950048010000380d80c0510942000780103580610f49012010355410b46507801042c00113119689542c007240c280882d0741344400c00f0705070b075401741c4401c140b02c40c0e60110100d0b80f01102e8451036090020040c52070004c14403d20100c440940100360807800c04007142800d80241c0c00312810180d09100c00c2080c4601d6076a0580a500d1058101e9900c000c540148425103060b5000320b0700403410029030b4071b01d1501c81c1c001400d4480070804009a0b54031030380b401041540841c0e0001301c0c020304040064090848000d00001454450002c5980 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 417177580 1250 417176330 417176341
    0x100b0703020c0109061b060e0f030a2313060810090608100605060408070b0a050f031005030f0616030903090f0b09010813030206060d020d140d180807050d020a03120314 74
    0xc100c1046c41c4c18007420345007042c02030001803540c0c21088141000009441d000c3c2441462107103550426083d1000241481c5500071044102c0f6102c0c114060f2680c0d0784a00d0b040d201c4086420f0010030307111304810800c4000008200c9070b000b00c1c2403000f4100c200c50500c28903030364185450703035120004c042c841c03024a4241d0004140c42c2c0081102e00304c91001e005021039a140800c001100c3d08001c030404184002045003520922040e001113100388650308900c02903c0c20541414640307640000c406400358017490600400103200700180d60a054a850003040059461604035072140e060340c45000130440f031240201d1010a18030107801452804c1c1d032815440c0d070300d02050a422000030380e0301078003681080c400f15580d41440b040400c03d441c00a85104c801c070005075200607018001c4030368a82e40c2d03046180407c80e000c0d401061040f246858403c002007203030030244100d490b03002900c10310348590450301ca03550464488234202c0005607080f0b42481108000c181d00503001c1c110040c00300704802000c100082 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 417178830 1250 417177580 417177587
    0x170402041e1e1a010f091e090506030105091b010c05100c140a050708090402070b09010e1c17090f060c0414010318020118170a060609060e0f100b0703020c010906 71
    0x510603800301260f9507000d00450010340f60540c90325550020011404008074198003985591148404658104c0690fa8130f000c034807404940000e032070648a64100300510500640c001100042c156541070729119107100203005a40460303070320744000c0c10ba00900381440381104442d4040d2031002da054482ea01001404034070400c0070b100d082d150101095003070110402291180700138020151001c0c0c4014a402007a8640d11800c0b001203c60510aa445141840c00300c2b406210100700b042842850083c1495110409460b80701e00990401c648403019000801c5503908120305c1c0c5e51103c0d2501551020b0520700790101c0c440e400741c003664020b05060120031400354813911a9210f1010440d1010a501845130700450348243e5002d90100494490400841c62010190698074410b00010040652446900c1c1441c20340d2004e07031000401c2458800100f01030824113207465800300051400302c607150394002608001800030b4000c3c1c4000d030808995807003010b4001582002c807035402d88030f0541c1e169564070210b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 417180080 1250 417178830 417178841
    0x2c03040302030d030506060d1d07060e0303072406030308040b060102070b030a09110303180a0b031302010507060e1203010e090105070e010e010c1a0610050a170402041e1e 75
    0xa4041d402261414078240c0b00303600403a000b07000100707050308c0e000509098a060b40d075101c1003220512810600c0040076442040071000808241c2000c00c01c2c0305079a00001d499000d150305c06030280d5100c000144800001d8400d40d1007094107080100303c3d10b610f9040040103640c003102d040742c6a000c0c040c00f280350f5600000d0417000f100c0c80f41020526580c0c40361840340140c04d040c202216054041c400c0c0801d1581c041c409070204a10085070701e000e890781d290400c00705c03e446c3e0b849440c0c507080800512156820411f81407001c2c54080c02c085544601078a40800180070410b0590500d0040092684c140303480d55004504803403101501c1d107800c0d00e60b070341d1003400c80d03800707a036480e001c01c500800c1403450f9401079015004088050503c0c400401007500d91855035072045010039000c28085040244a10b02042c01d2507074401d092508909020304003c020707003081c0c01881002102028003000400715540d54100c800c0008c1e400050381030783c00c0c0070802c02c0c025010034090303122642102c509441d003800c0701d481103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 417181330 1250 417180080 417180083
    0x260a08070806030601120201050903060906091002090d0602090a08062703030907271805010c050703020c060706020705010e010e0613150e011b0f0210021c0c02102c030403 75
    0x50132007079103040e00701e0122900c8020b0403070600c44140b0840c080c6075002c3c07103158410384c0c000b00075048a2900d03c00050800c43c90000c505100f0b0f2040c4010340f0a903c80305043d10010380e01800050f60380c4200d100245902c0c445500803801c42c805c040401069440b03010502c1c400880400e030640745280155610b94490000300c0d003c0810746e010240401408001d00282541081540c2c003e03c900c2120b05a61000d0b034403000d660718040d10020040c001085024421508004120f141007420f0000f83d0740d0081d1902c01c500c0050307200d0700c0c010503090244246a4100c9803001e41c001d000b00601d4983e524020301134007030301802c80750500805d800114a0320f10340d00c8614075140c0c4501c840c00b60031010001d8034011b02180e08540019940c2d0400b0858103a030120258011007400e8031000451040050002e2500030701c060500e0b0703094010f0100c1c280d0410b1100b9200c204803141c02c1c006c11000e4039520200e250800000b0260052406c040c0e0b0314a548095110817030000d0807040000801d110300c100103079a00d102d035200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 417182580 1250 417181330 417181333
    0x601050301180903050912010e0f0a080a0305090102040902070f1103010c140705070519180b060a12200d05010504060302010503190605101706030f0712260a0807080603 74
    0x1900780c0342d2049a070124414500c40d0a080d4101000c00c001728248a0a00b02d8540c00d6a40d240344150802c901042929110400e2900078511282c00799106c452501a040c0001700740358458000c0b608c882029010380c3c01400d000c8c038086495490600b0040c0a10148240680d00411030610603400340c141130040303a85602c0d158545101c1c000391316030908040da00100090f0341e20b0059400c003040360f41c4c40340103001c1d0b0032254142c00c50000d81401c17000310030840340b001c1c0c0e014464030f055840b0340d003502c454068032800140c50811101ca000c58010040150218025968190040c1c2c40d840514500030780c090400c2100300541006980e0f04c480c01e10045941030300010740031903410f00026002c4100c44001030284c20342500b0110b07078680d591002c513516030345444405010991070041c0c0704a22440440b00c40d4019021401003d1920340e031100d1540700c0d0749901601d030082d0150b243c01014098206011501c009064820314688541405c02d14410b80002c180000082d16450114142034032030010b0340c0c0110350040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 417183830 1250 417182580 417182609
    0x60d050601060c08121003030f08040c171c09080106051e090603030417010504030f0e1005030a2903070605030f160903060c03140c040f17070b0c0f060601050301 71
    0x8140c8024040f054101d880308010000700d44030088072105240070701400000384880b2802c5103009004a1030418951007002072003002c10001c03401c2c1c01101003c64202d10610f040e0141d20b8040a0700380b265a04451f214444010300c054401030f8003822040c2181c3c8407070006c1040b29150303c2003010300c0004203900c1da80c0e00070700b80c80107445140c20705402e60400d9008048910301907075802a22074a11050b8819070b10b07655108100024150886858441d8904078941010a004054005080102440b020004110010000915424140e0b01158a00400c0036404800c1085868008030880300c10240d035000703003e0602c0c00141140102c0a403400343d480f1507440714940d940e10b40c0f070803100c490140442081221004001012403458852010307c0f0900380c1d00400e04071401c1c20800144031010f406003160b80741c00c11040204e107210320419000d50340104e546205034039002c503d0343e141c46410380144498041c0003d0403203c20400140243ea40c1c0404016900543c1da4100103485502091060139505000c80d0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 417185080 1250 417183830 417183839
    0xc0f070812040b0a110a080d1b02060f150d0b18010b0619090306061d0c1c1a0a06080703050c030103020a05010c0609082d07030f08090a0821060d050601 67
    0x3c01c0a401d00c82c46510b002d0101c070245024540c81c0c0f141c1c805043e00c91150010701c00600000e0b40c082c0036001c4c03100c0fa03801d02001c03e20310702c001c2d6900710040140c16600c1d41c040118980c40c0b12056101e03c0040e0040071400001c0882c2070841c201141034900b040a1103420803d505d0000040c0036010701c01c0401007030141402881040e40d1240030019600c4400c10001040120001715148241800f810030801c1080c100740005a4008001001074840e0080c00001c1c0101c3c0803074001e0322001c02c0d0748580644086040794140501201d020f520703004141c1e03c5072088401003101e50348646450b2248030503540510442d02d440310301c403615220a0002a4101d14090300c00c0c031155004e110803000c10b40c0f040c840012010303810384a413540f580150240030801c40040280f0f07010075001d0482c0b104001c02d00c10805203805819076000c1c0c2402c0f06149120280404000002da16071814041e0f8960300b41c000c4038082d50b41401003400459207006680310003502084602040e40743c184120003107101a44400104540d9090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 417186330 1250 417185080 417185099
    0x1d01060c020607030903081b010f0501080303190b060f030405101b03020304080c0106080304080d0e0906040b030f03120105010f05030405120f0418020d0c082a07020301020c0f07081204 81
    0x21341c20310800c00b00000014424030300a0100744020300c49100c50005001e040c50035148442040c180c11030510700140402d070004401c5a400520020440002590001541c00a0301c43e401c1281d078400700214140100409003801541b01d41e00c5071040e14030350080030f500c010489241500381403400e8020000b80704114003d81c011038009004001c2c030f500380200049080c4c25501c4d00c2d0010900d5810201d401c1000034010810201011100e01f490301700484981d0106e00444002041c0e14459a141c0c03035002c005480a00081d20300000544c252a50781e590b030018104122401e106035030004114003400840c01f40300f07030281c0f03005503404009096000803c1c4e02510780c9030400031205100541c00c000014402c1043e41205a02c044050070142c0c03602d4a910000003104c039010255000e101d8411b080011043d00203149441d6940000c01610a0740d0144420034800d003d0404029015032002500840941c4001041c98a041e450000c80f005285c99580e103c1c0c48200d4040c0c1c18800c40000c0c001802400c02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 417187580 1250 417186330 417186337
    0x12150103030c080424020607030612020d1b0b0711040504020904030e150418050a020a23040909140d030b060d11070602071a100b03011224061d01060c0206 68
    0x3c1c0700360b5070529844900c1907213a4401a142960040096480381310100c3d018800700d42d1061050504000301031421802c03080d50301714050000d11421900d85540708000301400080d081400c0505581d28541e140c00f1224042e42c0000c0d0305464115180382c8001030391505002d407030b101d542e001c0c103200300b541c4950350f00740c1d411550303500c01690141152001020010280010300010001020f0200d48260a02c0100e02290307409003180480314010060100d00a0b0005c85480c90010000810301c21100c11200c058401d02481d045210082d0408044c00c0038404422448020540c000701600c1e000043c180050f0101d0700d00c881d0340c0750858010f0200b29882c442907480031480d4004071007480c1c0740480680d140412640700c1c0904496038a42c0f9004034014102001c610b50f885010140119106401d1010b90402070005102e101035800c00741303a091040201c51741c1d19418a242901165940042c240c0d130b404094026800b8282010030164410980c3c01d204000c0ca6041b03802a8440c0910080c80b40c0070b11140d5030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 417188830 1250 417187580 417187583
    0xf08010c1b0c08060c070606230d06061e031101230d0902090f07020f0a08040b0d020910050a0f0806060403141204140a0b1206010f0e090a020912150103030c 69
    0x102d0201d000110075005000c0c0c248030392841990580e690035280307000803c85038140c000900012108810b48003007114070fa001c1001c41e1084901820b1030b1400c1c507140c4007070300141d08030084060055510801c1801c2c0d00d0369a00949208040c2e40d00121414401107480e520141c2045000741107030300e44805d0710803c0000401d1030a42107400441c10f045142c01060b41c0e58003c2d2406101985036808000e9502da0601807200818050b401504000c140754451002c18050340c050b0300270348400060309040e041482e80c110340340c801010300181c0c104044101e001c1d24903000303401c2403008214804502065070b4440e200300752180000521803070500f411500c99901c000f080202c1c072900c0d4840d0300d4070032640607003c00c054401030000c1c910700300440040c0070600c050103840303600c0829a840d0501600390525407584440e64400f6080c03030081c0c0120310030281103400401001820350003c0704141407004803072458005142d100000d64004500b2000b0790b901c1e40d0b40350f80040c240c00508000c00c00510010b48070b40b8245e4004ca = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 417190080 1250 417188830 417188843
    0xe0a170c12090406120b0f01150503070e0d0b0f040605010f03020607062409020307020129120c210d0c0314030402010e04051e0901020301050d030e0a0902030705040f08010c1b 77
    0xb6891760381c0711800501a40060729180b41030701c00c01500d4400019524094101e84a01d4860000c0c59240503140317000140c15542031203004203a03098140c03210b061241005400600208003801c0034240c1001c03080e4250340c1914018101000440e41010b00c000c8074080b80d9001c0d090b1442c000e0662100d100070110886500c51307c8134001900c211240c20360400c040507210030200165642000070001e07084a149500c2001940c91100c19105001038564511880d80c00907a00c50681c0c224103000390303041c4581a00c5042c0e200c440c00c0c0c0c0800d138841001e8a00c840641010045918410703c000b0f0594285002e2140200013079281c0005041c43d503081c1c00610b420901c107043c546441c4030400c000500360340e01281c000c22030708124202514a000b400c00255000f003202002140b0395414100451258500c5540107400c1c002041201c9116803070780040d4070f0040c0308201d0210346030b0600c0e8400800a03401031240d1280200c05600116030988184910740c2194910b4032440300307034144241c00101c2185200742c20f4407074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 417191330 1250 417190080 417190091
    0xe0405010f15060e10050d18080d0f0b12030403080a020a0210080a0b09060a0501030218040905010c110f06151306090c090e040b0703020304150e0a170c120904 70
    0x10007106004000031840d4010601d09000e0601d4002811441807844562040e010719480850b01c40d00901101c1c0c0d464503c10020404400480250f8050b0380b001c0070040c90640001003c86007050702ea44500911110500c040c003110260004001c90100100002d11342500200420000500300e074004042504083c0141d41507140389070000707a2105105402d130400b250f404000c0001d890500d104030151030708121512851410044042074440e1405d010302030605900040c005c4d00f01d500f000c00c070001410020002c0c00562824074005002e0880c50750307000041804820005250940450810001e00389038009181c40d54811140740c19810b01c03068500e800060408070031900080740c0c003410014005000b008205a103241000510180c5c41e0f921000d00c0d41c400340c05110018003440b00300368100406280141c0c40e5103450921035011480b9040c1007606910b0441512162500810221000c900500414001406901d000c0c05507215100d00944c80703400c5031040d44d5001c030701e00001e0075007010040c000148 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 417192580 1250 417191330 417191351
    0x70c030c0503041e12120e030307150209040c020312040303050601120507210204060206042a06020d1d0d03080403030e010204060923060a0302030901021c0209030d090f0e040501 78
    0x71a8440d403c040d11500b4000c0090881c8640b0784528070017442c1003d01740710192003c4c1c03a540b07420450003806404026801000207015074042082e80c61080e00090f8015641c03d000c80300740020b500141100d400b0343d0a106108400e24000b00603034100d581d404401c1041c99945540031001040010a040d061101000c40010784003000d2281703e105801c02d88501029502109441c92152808000c1c80d80c114010801841020f50106446411552212070480a50b406404280c09800f0354145c055481942c401c0c0000c0f100e500080410f2403c1c0a912114848104e2580758282d852800b40e069421203031a00d400c4002038483d8140540c400d0080c940040c440380101e00030b82c26684503501000002d01913550500107891040d03200c00083c0350b0010142d07400c40c556404a40b05000d03040507141803690100c0000c1189100b901210541c50142401d240c0039003104802e03900070740089082e80d0191044240300101d2078043e092500544101c51500c1c00301e18178001c0002404100204201c0d1a9500d4184060 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 417193830 1250 417192580 417192583
    0x5010305040c140411030705030a1103061e03070302281d010303050c010e0334051903140307050301090b030d0e04020f0c06010f1701050c0702040c05091504051201090506070c030c05 80
    0x43c099640c7e9582c4641d01c0c2809803012054034038184012500402c10402d0003441d5a4403c2c3c2c4a1030000000c5841c82c0d100d12080c0003a081c446103910280d00201108503003102c1842e4440d030503005110421030751008a44800100304800402011802140814030040c80401d0264001d8054080400c0c004981d44000307920a03402d581008a038a0204c0e19060344c46807074a43e003c09081c2103240262400700c5100d65031381780c1903559442c62141500130300802d840c21003450701c01c1942022082c1c0384100d00740e49080800000380103500921a02d2451031038119100014138010400580d1400e0780eaa078005010035a0080100039880341004030012403080200e1603c0380c40c2803000c1c82c02006000320445e8228586904100202031034800e08043c1d92400040002d548240c000380c42c025a01079800241d04600700000b078545106500c01c10f58410403101e8400040342243d0001c5c0283c1d0825901c0481245101e40524240c50360110001c01a07000017000417001840b6900c4180da40340680760070024040540c941701d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 417195080 1250 417193830 417193837
    0xf0115020d0215062205102c060d170d0f0b0a031502090406030f02100906090b2a0d02010b010c020105030402120102090d08180f09040201080a06150c020a05010305040c140411 77
    0x801646c4940c10001700c00540c504c01001803a582c20207224032114007400e00509400803051101ea00035001c00b14009444409000200e950702c401540800d40f604400b620007070300408000350100c1c0c1492040d614100c40da01820b50b42c0381c00500030781d4915045070340700b1580b01658a09c140d1004e07420b002445540ea1140180c0d401140100c0074442d90146034010301c004c5512820314503081c4100d04104000722640004011304848031000f0181d160100b12441c0c140304c1a20617404413100d011a4405040040081004402000690020040d14400e41c006545104408038081d012500900018000d07041c041003111140d44520300051520600b280001e0b40142404010781d102a00800e0107028002080c9c0519210740044804d0b01d4881020b00020300308101c000d10007030400c041c0300c01113051480c8903040800504101119207c2100c8020b100500e00b03071807280c3c10381c4102c402100004140d4003c0c42032900031074101400b00080c80c20142002d600d00d4a5003441070300a907442e1852102e803000d00014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 417196330 1250 417195080 417195139
    0x11205220f021801030c0306090203120c1e010501060e0111010615050409050603060103080a0309140f031314010507081305030d08040203061e130c030b0f0115020d021506 75
    0x41d28000791840c01030000c0c1c0c0f4030315640c007820070307860340014004218441c0c01c070403c9990112010502840d103102007410710140e404890040d45020808c880744100c042a00d0030030105c0407051100c2c980c02005143c1c2a981c081c8a608040ba00512280110394070035441410410041030001c02d00035551503002d102e0076a120050f400054000c10184136040c0350780105500060203c0c002d11440d411a1100700b0144658100c0c1c905059070f6003649410802c4100188503024041d400355040281c220320031503200c0d0f010300c81d110380d4411201c60200d1441c8607c000c10701d400304103940b254101a000c4d070b074000007070f0300c02c6612803c0d880c0c4c0c0b104001103a81c0c0c10030401948810694890342542440d1050510b07141d0007400461501d9281044440c650061614440c1d1002d8110580c1d00441405d0501852000040d00043c0040c019081000718000140400c241210103002a00710382c0c10300507000726103840d0840714090058200041d0b5025079054229001d40090004001c0c003d1000440404900740e842d0141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 417197580 1250 417196330 417196343
    0x3021516300f05041a210f01270504020d0c09020c0c0105070506010303050c030c12092b03120b0301050a0c09050d030e04050a0209030a05100e01021c020d020708130e010b04030201120522 82
    0x801a40051042e021f0780103294013512840c5480c0c410081001c44840304603241c090300e9568002605640d1080349035005c10340c115132410740e03894849800c0400781d403000f80c002c0c20f58840c2030f04405055201d0001c03142d07000d4020b4040e0103581d0855504441070b520440c0b01030b48511050105140040342400012141c4824400881e6a03e40840038000c0518103601c0134000840c06142c0d040b551850071407050751041c2d26207050711012000e030f1180001806080c080c91740541c0303042d0070401061090f9201c114900620f0b115081605da032082007100046130f40100600040003040a000203040981145400201060016041c61040c0003ca071401446510648169111442005a40c51681300d80100592168001c1d0320308a0b28408215545038034039040c90b0b84960010700042559035950564015075446041a0b036a03592005103075185241501032103410450140001490307805403000ca40c2120b6040c6c440078920070342602d42d4402010b00800d40f4201c000304601a4000c2030b1340180301440d0501c200b1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 417198830 1250 417197580 417197647
    0x24071e0803150306070903030f030b060c030a030b09090c011202030403050912160f050f120f0106060804060c050313080a0e031c030b04020403021516300f05041a 71
    0x4140c40c204014240720288041b0b00c90620100340e204000c032400e061141400314980300110040f50325803140118800729400081030303000516505400240d03000d80111b0b0b121445846d0300e0145511200c00701c2500f80800e400f001143d030000781640103968840d000c1d04001e800e00000e00003040c1041910b9240d000b2507009408841d2040e0b803100035403005040110454400c00d420b290100d001c0341d14813402d072441104418408039284004004c07030201e0046644c0203110269840c5005800044141c804a81c0c05092025400b00e461086003035038030403420882c484400200c9905c49440c02d501004114003002000241482e2680302049208069481c2d150200e090714032010f8001c04032803d011030a48200d00422041016a542c80703d0a142c882c542007850750396070000501040850642c980040c1090120703100c6480f00103407041d071002d81d400d0031004c5000010980400b21840c090002c2180c000c01d00600041c840703900c6100080910124030030806241c2315048008040382c04200700508011020380 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 417200080 1250 417198830 417198871
    0x170a0609060b0c0610051c0807050102040b0703090602030a051e1306080709062d0504080a0f0606060309170d0f0203130302010606140a0e041805070524071e0803 71
    0x130400b60303078000343c1c48074030034000e0303017000700142041308090055403c0c1c0403c04980c800b0312403020300b1501e115500100031541d8030f42d00d4612841c5038000304c0b02500450840c1d94009a014000303c11294454a1640e03001c2c608002030859005d0411188044010070506000b040241c0c0c414400e1031010b03000a031100552441d082c0802044c04443c0c3d04040200720406000b2810341c19080e195003c0d0310f0700440081c600100040c002c8a0600860b4407902e682d1003600c6001091181c0c00c19250342841c00307054180400e030381703072041501551045c80c0700500e0402001c410030a07400c65100509440e03881030902054404410b040c1c10705030b070415103002241c0c1d1101d0300001c0c00c040c1c09105c0c0c24000c00050800d003440c400030400c2401da134082c22a20409000d2921501621660b443d40b000c0b038419403802010b203024020303040695688005004d601c1c0280001c030000f800b81d08030300482c0035603011b5a080041c5022a59560f11400101d10f80d000548081060f000c64001850000038511813040450071043c145443d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 417201330 1250 417200080 417200083
    0x12070804020a0f0302010c0602090d1a0708011403030306210a030503160806010c0f032003030a051b0405010c1502040b070c052d0a0315020d0609020901170a0609060b0c 74
    0x1e503404094064508407013000140d800406242009400c10b41c0162030312080700104607400c207450002801e520442d05541c4a240a1208050142d074541d914142c07240c1e21912a08003c1c050f02005035815401030001034000d00c0e1004028040c44040c0f003598000a09400c081803514101e184101c02080300401040011300808044900141d000d280111031410f1060020701034000703030f8001134120940c1110100034540620100442416044008140c0304401c0360202d860390402e130340958140c2e0400012501d00a241d103a6492452902e04c007980c078181c5032400645400803428070031226203800500b4030a0049039840644018140340c00d00c590b5400d050701c0e01c214102101d820840c0700325601c0059107024261403c00b044400301c409019844c10580c8000200d003400a40c0c0001d008008803c10701807404581c1d00500f0780c1100c05c40050001c00e0b21103d000c07003a401462009400079020046400103007518404154006040300c40014026403516094003d1350b039035801c0144002d07400101d40c2a031010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 417202580 1250 417201330 417201349
    0x120414041a010807050c0c1309060b090106051903110307020a140316080a0c061e0605091608100b0c03040f06052107110a050f0618070b0706021207080402 68
    0x1242580c40c441c99a9440082c2c81107402401c10800c0143c046484c010000c0704111a1a0000d0001e10801c090b8074003901401c058a0501011943c15003000c03090b80e03d60400307030103241c141c46050700d60b5401e020b5000981841c2c1c4080314075140c10141c8600700b070245640c01d4401940110710640c05805921581c5c00d0042d5503000c20b90700303034005920030402410801910304040503500d0f03108404599804040340200e840310481e03075028100c60705c1c15440307250388903482c008004031540315441402410340c0c5400701300f80c030701003115403100500c0440d06c031101441c0304190380c3e58845100c0ca465040f580d125142c011040d084075880b030150340c0c00010b0510060102018081c01480289060751400c6888940094441c1c0384001017005605800701280e05c00b8021081e040490245004a4207044081e040650752000340b2030f0155041e010708d20105131529490070b03090000304160401010810b2034403221055070782c8000345c16200c0542c00e0040f12444010b030801d4500504071035841010a08050040024008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 417203830 1250 417202580 417202601
    0x302120a03090e150d0f02042406031406040203091608010f11040302130c120f1a03010e0d08040807061103070e06041202210d0207031a060a0b03060312041404 70
    0x50312034100020f1000e48040c4c0901400c013a10500c99080a81c6400318001e58107036002035009040007203000f0b11031000d240005c011188141583d4105a0b11001a01121070a0b544546000a000009005801c1c41e400942d0003110070340858410821080c4a24005034543e040318103aa51105040342e41c085141c050b0350904000b038000b40345807a245a0000b0303802007140c150000100c1c0c13182491040180111621155000c90100502c180f106448803035004101e0400002c21260b40201c4103881c9050500c21f01c01c90b0568030b40204511001a0300955080b24001e100312001c507001c21031500040ca60b400350300310003e820180d0a0301c03428820780c0545141d43c07002c13199009030800d10003040359000e80c86e0b50815032034060b940200003d00c04004481c45540e581c0c400c811500c50000d5100d2042d9001660804a0780248510300d2001200002d41e55106070580380c441d84106402c5013401300ca030341c941c02150404c030001d08035600d4041c1d0b401c404801d500558040041c50b43d8540e070b211810b040c2401400d9401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 417205080 1250 417203830 417203849
    0x321080907050f042315090912091c120c0311150a0b0a17070305060703090206090103050a0b030601080f10051006050a1b110109050609031f060302120a0309 69
    0x500b028042480e900c201e000c010310440c1c8809000d03503248602d100c0c1e025840c0e54084501c26a24000130003030848030200f014180500c0f8410000f903000d50011801990003c10001c8841c40d060084080000c20f440c1d540e4031911041003070082c03500140b11040e02003004541912030b1a00b41015050147c01c4d264004820045900041c00701d41d501c00c01d1082c60303a401950000c0005104411501140e000509600a049000b40400e80745543c600c000403548112032042d022640300da61082011420b540c0e00c450002c0d00000144401c421135030182d0062030b4071051403100041c4030030307c0c500001d15000e800e030300200d065008456034042c0d0301801d0003414030001c03607071400707000a0a0401441c001100c05114100800c1000706a0382410b52184014100041031101e512400605a00300601c0d205005070003180400c814071400030300c90030050b00342c1e4500e2000034050400940641440d1140505401d0540a025654000030bc01680c0ba5081022003015940c020400f80d40340b440e01a000d41e1150700301d079640 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 417206330 1250 417205080 417205093
    0x111009060b1f180302030a050f010c0212040b03040f0f0c0e0c0f041401090b03150901052b0201030b030d081e101202130c030e1c02030406080603030403210809 70
    0x110010002d81002280d00740f6011841c040a074284400400c11900b00035414022034425a040c07001c0000d092401500e260300170800c542c400340c41644c2d1461005000386642038144030030484c00000d140990b600c070307015210001c01d000c0d07141e8502808186101049440400d0f0038030502c420340d1041250342c2c0c459650700e80740f442c105601007441c0c4203019134401c01c003840440348158002e07a441403034201c00402200d804145c69040400300e10004000b410503244c0200824400080da6103454101daa03403030550556600c402050740d10034008000c00c06501641416251400902c140d1420040000149460344d1201081e060100c122046c1a26080090035182980340c00e01840c1c2e5401191201161800010800c16a50501c0850254848001c20300c0c003031440d02d03020303040b03464040d08400100c1da500c6043e680c231206098804001074000421010060f4001d22051003024060400e41e500150001d0459041554a40c1c0e80c080547c0d00107014844800d0300640007400315009000c0c01c0d003108428014005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 417207580 1250 417206330 417206359
    0x1704031218030f1d06031302030f0604031803080d0e07080d0c1a01032112020d05040210030c050a050c0c19240f0e01110f1e070503070b0703111009060b 67
    0x20200282d6104e90311a45000020640c090440c001da5541194080e00b03545500507076a2209031103000496094012690921004818502c00407460302500d902c080100d0a26401c0307880140140350025a2a0440c800c02c4804500c0391f0041008500010596840c0e958842441c40c000000120514403d4403105240300184009618000003141140000384151140d05804038104d0b424441c22004c80119440001c0441050100c2d8008038820782c025580c024121042801c200c00b02c0303d4510381c04002840c144446a0041d1080c0001c10b600c0c85110105c60501c02241e0029417086d8088007001c41d0541415420807410030384000c42000090400102c4801900b00a0043d102c504503409031002c020707605800400d680e00400408a000c040d5608446140c0c41420b403207903440d419035508114588600d0000c507418800019020280c441c094050903030b4514004090601d6048458201c040c0080d18500100c2400e0801c403160303034030002d01e1000c030380c0224900b4041d040354200d012a90140f86100390024 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 417208830 1250 417207580 417207617
    0x9121f0609201606090b0f0c0703120515060c0106060306080d020304141c03020c010e04091703070203070b10051008090604030c0c080714040e06071704031218030f 72
    0x382e4102d040740341d40d40d4402c503100d00480041407203d4000c10304c620300304020302480b8428866920035020300460180036101d0421288a60054040040000701440c40c215121000780c1c0000b038108003440080907039400c002c40000c0783d0f81c201c0400900340c3c0e03555a600700030903030b818041e100090500c14043c048200700d4101c000c1d1603100341d02174181488600041c3c1016a11480c5078003504060018a901e0070110030300d8029100d034203041d00307140025154a28146030b842e051081d0109140d00581080380f19003007203207100250700010034071000d50100b032201c40086140d80d1f009905c10408040381e04141d074200002c0004c00141d0403d400d040003c203400f081070f090742c001841c1d50042c3d00750038005a00e60042c90150800202d54224465502030301c8800203001c0d6801e5104010f1250840f4103000708107401d4004e07551144200d03034000010302c142091007c0b60354904d400c2074200e0f010b440c040e21a0fa0f411114201590100e8420445003080d00d1a034505242d408989120414000e142c01c1006686410108 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 417210080 1250 417208830 417208871
    0x216020301061a03070f0212180a0e0127090503030403020a0c0e0c030a0f150f0611030a0e0d03180308070302010c0906140a020309030709021c09021509121f0609 71
    0x17074003401007141030915118001c1000300703d003c984101d2640e42c0c4a42c094840365000d148600d060140303201c803a02140c0b0064a00d02c65041c0d400b03250703035141039031205690840c04c00c0007540703841c0c4019601c11a2a0116409000440c0316902070b070010112041285414211201d595002094001c502c2092103031502105044070341080007070070007013219501c1c10401c0c03008220f04030410f2188207070900d0005001a180c44014116034681e1540003a6200c9200d0480d103034801c43d0350f088000740410407885418a0070a1405041c607001e842c2001c000e00c5015403d21422045400036220498045169420194240900150306106240800e070444c9041e101800c01a128110301743c42c2c080210703c25005600c02c0054500401e002030880d101d0541e140d407020008d5000030442888404000014075180b242e600803183c0082c2e014105842d0780d80d0384a83c402d078541004102a41c400c06010404040130300412004021034102007610f820340c03090b600b001d011100c3d036a006440701c5061860140e031623042e54504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 417211330 1250 417210080 417210091
    0x301060807020f011a01020c010c1703131a061003021206010f02120f091002030304080a08222f0102190503040b03010b120105092e090216020301061a03 67
    0x10300901c0c1c4803100c007641032196165078000290301e801a840c41d40c04034042c0400c0148002c0e02514264015180115420780110b43c01400d482c03500d034038120101080b00025070b400303250418410a0302c041950340f1000003101c8010185030800407001c2c40780c0c5242105c0b6540003800c40f41401c41c0b80c01d031080307074261034410000d111905010202c802c0501c543e00a20490032070030388001c40d1555644426060b04255080380360170034041c03001c480c0b40c606d10382c2c00001101c0c0150b030442c1c802c1d4117214040c203040300c40040c01040e040c0b01c01e6506405114014030b0a2448070014030070100c114480c03500c1d07030060366145400d241c410b042c02c1541c5407000582c0d0300030840d00c1c4072074141c400f03110f00350000d03043c958034501c0740f0b038420714088000000000d021455000a095120b503019560701c801d99842080013000d0206450600781185103c5462503c4410200755411000c0c441080c42d0704603550300800c004a0700420b49800703407080c50420840c11850284107080c003038466080681400a2810803d1000e400014127 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 417212580 1250 417211330 417211337
    0x608010f0e01030f170c07032a2904050409030206150406060e0103050a060f030302061006031104050418150b090105040501261204181a010230040306150b070503030106 74
    0x103c1107003250343c02c006c68081050784802c4541c2e299481c600110241c0c10155007221086604110100301c00c03020580200f204d9a0201840805040c8c000392110403202c500c00b890324000400c00000e07035880f24041c51401500a802810252401000d5000040c0310f0082840c4038502e4081c0500c41241c2003410045205001c1c40d00240b80d58402840c400282296003100a03c121860f000004044d80001c1c028400c0301c900c00307072482040e960038040c0c0c19030780e0174080151100d1061105011608050b4005903241c3c0219a100420460a80f9090110513614aa00d418107407202c0d095401c03410a070042500400042e201003109600d031607050150a154070302c510a401e4503504040e003120310100841c810610387c05043c40c0d903481d650f90380c020484d1f0000204072220381c1000180e07801100980c0d1011000c0d50306802900d28840050725004010700c040406c0c488041030000003c0c400f0803c0001b42c0081c51141c2400501e8150282c2460b81205481e803050900362400c0001c100003440100175281101c80508 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 417213830 1250 417212580 417212603
    0x120703240c03140a090804080f0f1e060f0603010213080705040e1501090b0607050d0305160305060904080a050408070f030302060c16020d030e0616030807050c12030a090503040608010f0e01030f 85
    0xc0c04048510560340848e4281c410050182800c04010512820103c0070108580c0071845843c00c04001002d10354583c80c044d0440d0002034150107100c242a0352100c4010001480e0403c0a81e0080d00325403250000162544052001e0080b41070910a100e42038140100501c2e5000e580041c011012005000307121000c6d0300c41c001c6030342940b01d00041e5103c499008050300d410000c4030744e00400820b0100c1d00c07149130980c0aa103001c840e078000d00c01c5a0203650040c0683c200c03655103445141c165070001030000e0810074200400a50001d0a0080002911000c6d0f1060386451450a00130301d45440a49a2405d4140801c8010111f8039050900c90b1000d0703042d80c04940c06410307070038117595103036544010a0300b2810000304484248801405440c1e2540f00c1c0d151110380703072130711074007180c95010382220121981d116040329690b10321020b001c0c5600c509003800214075202965103003070441e0001e62025000c24615001800703d241e00c60300c0c410281c40c1c3e0a104401940c91525452404031041c4009484082c030798 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 417215080 1250 417213830 417213833
    0x1d060a0509090c0306040612411c0206070507060b06040302041406031b01020c04050a060b070b010608010506030411060306030c0405132003030306120703240c03140a09 74
    0x28019662240c400070600c0d4940c2c03900c1a0b0843c2550700803100548107a181c641c0100f0035030b02807131010b201190010700301c0c2080081c14412000042c2203528004424401c401a800d1743e04030144c00d0a6000b900ea8007900c445074258481000341c403900c005440075508020100090681c0c010242c90f80150400c20200300c2c0440c11001c200d00d80b19540001c0d41050800d05c40941034259464940d004100690444504c80c40140385889a2180c0c028098010703040720920310143d18254104581107550660002100c40e6165070000c0990300c6140104c1c0c0084c4c215004000040e00202034a004260940740c00e40746107401d0351540181500c0700d9195205450210100750152002c10406903400405071040203103040400c10050400f0000404482d504000040704003420164072117024035150281c01942561220410001b03107410703407100c02c2c5462060142c008007180c1d000010302c4030ba2040700601c0002c0040c1080e02c00585014200071414181000e0f0400c046a28095044d6840511381c0bc0024542429 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 417216330 1250 417215080 417215087
    0x18090714060a080f07030905070b0714010504171308071409100305031e130b09040e070e010905040213050c0d0c110a0605070309051209090105090f0a1805010e0a02030d1d060a 77
    0x3080405441427064210106111100384001c3c04104e0081d00503000142c100c1100e00d0036940202c030000c2020701c01841980c0c0802500300582064141d950030225005e46440380c2e14603000c2580c3c416448071031030043d8050541408802140c12404058071503850500b907440c0ca03584d034842c0702c01d070040c80001408c0f08544201018203941c4c403040d01d071030300060b140c0d034850711000f8907001849400d101c0e82c0342407404480140c00050010803250030b07c40103142a860000050010040100140e800803910440c3d1072664030f00d88901d5100300d0450442c0c9031140900c03000d08088601a0b51049d090090110141901c14030000702c01c181c0320390000c40881c00382e5034904120003134100c8660041c050300c1030548181c0e01100c1070b030241410700070039541510039a90390001c115001d4010740b1003414880044000c1421a41c55410900c205490794050406040d999940c1c1401c55007400c0d40e003800c42e000b4542e0502149803c0c4514a00015107141c030003e4801072668080e804021181c03245c0c400c81d4001800c0403402d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 417217580 1250 417216330 417216341
    0x180303090b0a0509030d080117010605010806040b0103020c060c041a0c100c1b0c1806050604092004090b01020705040b0f011d030307140f071a0918090714060a080f0703 74
    0x4c050152000b200c5550b0003d41894030a00458410304401e07000190005014400c00b002c07100140d484101d540ca40341d00f4080180f46a00c070f6141015001c02070115602002c000c0103003d0700035080002d69881c5130116001c0c05400c43c1e0b4404c0e244050420000c8401c00000403001d44200164000103020049007009a501c15400122241849501c864000030311040d20b2141045804400202807081e1440940b1000c0b150b0358000c4d035501c4002440180000c00d25980200421444029211000f0400f03202c003035982c1d00142c0c845841d0b80d40700c64042c46203590601c07040380200701c03e617000d100f460440c20006140c103503d624000c0c10400c084402000401410074407140181014040c1d07651200740e0f0078881c047c1c24190880030403500c58600000c03044000001d1030422251004442c410182d2907281d10051540100308140d80310002c0307081e5181e11585c20802600030182c010081500c0741c5028000501103102c080e05502c035200920600c03a815402c4081268080b4003040782941c00e07a58880207500038007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 417218830 1250 417217580 417217597
    0x1e080a1407020a05060a11041502070e04060b120105010b160f0f060c02070b0703080f151509010f0315090216060e06150909120a030207050f060106180303090b0a05 72
    0x5400d03400e10101980100714000c07094064415540e499656900706029220035040c003401c450303010403003040b0a400440d011124881c0c00e05c107440c2060ba85803003100c00d020098405464640c0c1d116030b1a406458040c8c8100d002d403501c00028005585014051100d80c044d8003c06140882007a614030100199252800e211030790059000441c02c0300c500f0944020001c142440000d8440c0400201c3e2400d8608261281907178540d43e14426540c801c04580301185002d0095550407850500d0609030355074148245a40c810645c00c3e4503100d144007000113003a14018032809060510344506215212080380b51002a101d0032140543d441545148a40104042000c0138140074030b4000464459440030070801d005888803501c5203002c19030801005480340c001d4030148c21541c01381400e00c03486070707121010b0802c40c8240d041c01070070201c40d51030706414002c5500c22003820390000b0b0f00601000703400c04040c0c0c0c8070045003603c6400342411998060000d0303400b400f8a4a00200208034960428030502c11511102c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 417220080 1250 417218830 417218861
    0xa0504090212090c03030c0a1511070609150603021806030a1a040c150203030420031204150302090d0b04081b1b01030e0c060c0a0611191e080a 63
    0x14506a8400b940c0d001054440c050140154800c4044518001080d070740c0d5412218040c10b500c0c5200da95403058200401140d44520b5200e0405070550411080940000340c003a50002c50078214070f01e81070341442c040f00c081040d641d152080500c056102d028810401d001c1090000c040e0751503003000a440d0141440c8028039020040001a8154940780c5070180201e100789240c845581d2542c3c0001200c25800400c04c0060b8010300c009004110703c8520020500c0a200c88844024510340200303007130404401c520507014000040400040d02080307a80c044001951408504042c41207001508294615002030306000f40e0001040501000008035280f69415003e11098440c81c142001d0303d82c000c7d803505502e10003084c0c3d1314101c1d07540603006121170080c0034406031040f00b0b041400c0241d03d8001e9503035080d030b622070569002c1c0000e40c24030403000d030849500310b4642c445641c4504480347d116140e021908101e02010b03e10041034045141d0b11440003942040c2c02c290b5520014100200030300110200f11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 417221330 1250 417220080 417220087
    0x111c020a061e09080a0f02030702011b14030c010c021c0527040f1a150f18190f090606020d0809190b0a0b061215010504030605041217100b0a05040902 66
    0x40007920300c01400178032850b0300c4103010103100c20b80580e01e901543c10043e001c0303106410000c1110050344415240e651054841c070300c0d0300c410581200e1858205002e6450b042e95507174102600d8580400c001c0d65007621300e4a800310f2120340382c4001010b900a0018150f8043c01881103002d40d420410307003030f84e40d041c07024204100c040c0440320740401a0003801c3c42890307041441d80c441d0b141400d045200160f03440f4041d051926001c51642402c0c0d003070344440942052001c1100204207182c0d9216500300f0004151865481071500300140e47e01440e000341d2104c2d900624100007001000e030046030381d0301c3c21b11090900c8880c96442c50062303400c009030700d0340c0d21407013618000501081000b06a1100c2c080e865214042140090150500c0114420300340c0740840003107e80005012405d00301003024010030185003903800c181e5240d540e481502e20641c0e08a8000c9250741c0000c01041d80a00d4070366221004604d02c400d00d0030000c18052a07041903001701c0100a200048044a4502840880d401400c04001c01c554 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 417222580 1250 417221330 417221333
    0x312060a0b0d09140a1703060307090e0f1c02070603050403090e0403080702010c0e060403020d02010915050309060a180b1f06110c0609090a09170406111c020a061e09 73
    0xc25510381c3c100c826540c070541140b001000041c0c03800350194452148180b2048583d000c0e01e064000070035850303052241d030001140c004100d016203115050103000400c03210b00080d100b11b04054040d824039011815030342c9882d49040c2e001820b0000c84003607050014581e201d605003225000400d801000e4105042010b0000300765100103041e00c180c06544c0204440c0484041c01c4a02940e641000c075030000061006001503c0c0c000000803945205040080c0c1050342c0d00e210030104120700050f500820008800c011401d01c050040b02da20403101e40e000c209450000c80041c0b0504c03443c800180400004400103803c40404c0308070340c00700074400c15100084550f0381e24000c0c182c4c0c08101d5040c00601680512102a0400600782c5c2d11468004001c61102c0d85d81418000c01081188010354030062442c42c4451908000c2005001411265031410304402201c0c134403503d40b146442d003558001c0c500c0740050200f0f80e408128851510351003140400c20030100980c18102030742400c0b503115000d14110741e8a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 417223830 1250 417222580 417222607
    0x11826070305180f01021e03090301060e0a060e060d03081e0907140303071a100902041815080d030902060d060b03071205160c1a01090e1e0312060a0b 66
    0x80c440e0440c5a550055081d030783d00388180c1d50b00f540d001c42d02580c0703c0c0c1516003a4050300c100010340002180300312402e00350084d0001c0e080d00d003a0350015411581038420302c03e41c55983c1c0030f50320143c030001d5640d6907070f401d146012940010345c04102030100111900490400ca1540040038607403040c090041d5120b0411652890702c480c01489042100c1c03007100140c0b5000e04012044da2040345d00b2580d540c40032000308188801100340181341201000e41c0791004107e07400c5900c00f074400b42103400500725206d00040d4442048840c0c0151520148001c06401c1145040001348a0080134082c0f40204006000d0710115007035014100b41940030300e0800b100070817070380452400355200d41c0d11959040c1800d5500140d010131603006644580c141d0306c0c4902c09044440c001c8200165081c0300c3e0702c2914001792034030080c1100c00d06c00c2e00145041900d549019030051070030409080c80506c0800403000441c0440c1200356a8851b14020701d8a001c60240003a5082d03503800900d400038206546041c0d525000b211068 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 417225080 1250 417223830 417223837
    0xa110c0405040c08010e0c06090f031504122709020a030207050f01020322200d061802040608030c032208060712060e0606073c0b09011826070305 64
    0x44d642c80c0444001183c40000345210b00d120014000c0c61408201d4020311000154010b4003075094441c420855074401c25031280d0600c0b5034012010807120551804001301094260225045401c0c80c158084007007440080240302102c80100006a031108a034005030064010841c024105004181c42c00843d441c064000318480c01c2a00d1600f07000e144a0403079019401c440344000f4102c24400c49401079030300a900660b8811480c020030f44a40100d0650314201541c0000b8825840d00d801c0b65444404c50906000e01c001806040018500b4419007250071503903030040741024004c40b64850703881e94504d83c0700c0d000e0401500c081d6003a0341c0c0514110070050659110109108800c0717207042c80c000740150501d21454046c1c1002041e01e8600070803170f201c4045403c02010301c882400901000120f8070152551803071100040080500000109800d02000c4000700a04440f1142d040107402218242138400e2215100e0380904940030055030281d2800c01c0c1041c040d15030841e43c0001565000345030700301c0044c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 417226330 1250 417225080 417225089
    0x605060a050d0c110607081306060306090c0f060512060f060c0a0c1d0402010f0306092c0304050303031f0b0a1e031e0b041b1e0203030105060a110c0405040c 69
    0x3405800180f8030125210b000c116503d850981100c070100c1c8015110b070440310b07007106a8800f440d4413003085071034030710854000f9481207424554401d124801c010318801220010214a020300c0d0703600340340c0040a401e601c9680011a04658400c3c0010f0090f5070b007003150070f211207015107196103649006003c90f654030a5448117a07818000c9060020b9032483e080c030b2004000160780d04ea043c0f66102c44d8019200220007051160905480c0e03031010590101d5841513400c1301d116114440c4034152015040c090620790320349a210560010041030010392800400c40340c12213152649040010004600089883c0d4660040001e0007800201400503e0340455408400501c3c2807409021001d541025021600114900319800050350107128503810070754405100300f50043c002158200018082d10118054034803000040f40070b810340300041800003000310b08000c110b40011403a42d410100000d450740144401d0204100081886604180d002d11548a0807140230700203014905081c43e00d0418041d02d40034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 417227580 1250 417226330 417226357
    0x100e0a0b0a0b120c010c0f11030604030302180f0d030e150f030105011e0c03030e01090f06050703290d0309080a0606151404050907051b0f060f0108030a0e040605060a05 74
    0x10b410b02c000030218001c04e54030f02c142c40f03a460726503159481d24403c4412104c00e5a00c1c800030b2019400d55141030000c280f15922a40d0300503910105141d411515644111003940a070032000e583c200d05464464a07030400a8050801107100905100001c0320f82c600b00c14207d10040002c501902c01c840b1120203141a0340f0243c0f2100c1200703800b40404a20305c5103d800b010700040e07942e2504004240030f50b20001022a50b0f0001140e44070417925000d030380d079511074011074015958100300080381d5414400c544010a415003604c99008058003510004420b14100c24400c4045075803410070103004040010003062500d061b07454a469a00782140140394522420180300c11512081008511501680001041168030300341840e01300300500450074070003040705092203c02c120100071070200340002c140b03000030714005080d2402450240f0b810024081e102030541c18251006100f80e40011041c0c6200c2c90f041d203000405099084002805003400f0fa108a41000000959807240c543c03040007000c5000302c0c0b55 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 417228830 1250 417227580 417227599
    0x3020a3f020a090905060610050f04031104060b0c030d020c0102040317030601091406160c030b1306151d090a080a0512130c030807060212190b03010e100e0a0b0a0b 72
    0x81d5601035400e0804d000340b0580280780011428030745480e6006200c074441c0b8100e418030000210415041c2e029400940706c03291304c41401c00e554602070084c3e9024000e21211142019440508641d49000c2c040903844115008aa00400000300358140c070300458001900340c4240c010b03100800c90642c000d0703070307640e00081d01d940000c5404070840349900d00c002d102404080c941a006400521811200e44c000c84030f56084440c000b000c58451144a8001c000600400380384030024580301080300c441d80101444d810404000304400d000c480300c040c2041480910151044c1c0d20a1446400d00d601c0043c000c02020020602c0c0c05c506511a0161100800701005e4404503142d035645141c2940003000010501031b00700320140006850000030b009114460701025080c01d10708180c41903038803001c8680c00603a020241800748444807134051040a43c5042d4001c200305120703041042d444009086000ea4150303250754503003440580402258011940200c181062410180c074220080e104a0880c07621480101c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 417230080 1250 417228830 417228839
    0xf051c0f111b030a12080720120903010e01050f070906030b0d021011030c1501090b091f03050114010e01061707211b081003020a3f020a 60
    0x1040140c014241140007000003261100300e0340c04142190b1070458144c000c0415100000b5007006943c0002016070701c8080403442c0000e40249444160780c0e40303108014100560400758103001c1125145490b513610700030350b6030394400040380c090a20340c00801101c0d0301e003030104810b08100d0035030320340103540d5562603240e441d9843c01d0031015501e0071044d00c0d900c0059040050014030304600748154059450070220403a0b450f224503241190800c40904031203421500391650611032101d006805804419410002c403c0402c006c681481401010b07000c40e241c401041c00c41e40c0c1e5090010a0040d5800002417200244590781c1c450320344d10038450044c0c00a407620000c00e00c1e41c043c0d1030485c03808024020920f030079519907004480350645442219800603201c600914030507030a006003801104150440e9a2601c6d60100c0101020380080480403000406c1d04244010780e60307507040f40c04441400392002d9a10b02d040302606240203411a042103440701c2d00030344400d03001c3c0ca9590314400a000705c1d818000c460b6603 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 417231330 1250 417230080 417230087
    0x903060b06090306240307060e090703110706090206040b0f090427110f10080f0f01080703061a0616060b0303030606031807030501020c0709050606070507120f051c0f 73
    0x211407407140c0c10b80214001903d4035003102e8588400105c0c2401400b03082a0860100c0e0414200381c005500281a00d0100704050410000044c2c024056190030000b0400405205c5614081d00b9001890305841c1c040e110b040d91340e132005031030190412034001907807a03840c100815804d03030009841501480c03c2c960b007911150039103180b9401301c00c01c840140024030740c0c41d610842184180d4002c0e542c801e014154110181c1c40b403140141500d10b41d505d070030f00d05003090764952803100c034010000508402148014000c00300045940000c513540000d0124401d98030060100705c403644503400940000b8041410b00800089843d0140400c2c003c0da41000507250801c149616031004848030703070b00408100041074500e21440e0007600410900c0082d00e610540f20340d50b09081e80e100800241055001542c02c1c00b62101074403405402040c111540c03840d000c419600d040c1ca608070303031042c440c4404003584c0318014854400c6c0c40c0c07100e5590110031346080701c5410b004124074501e500b0350003000403840b9070548001c0d0300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 417232580 1250 417231330 417231337
    0xb0111030c0705060f070c0b0901030b0d080405330a0807090b070f030203070501090813050a0e0106141909030308010603050421020c1c0314031b0313120903060b06 72
    0x740032024242e018200828403000d50f00155000e40420000c010b13580c0440c03002c055042c0517000f4110296600c000c1c1d40c0c00101511174a80d48140705030b41024078000060079860840b0210390094a1400da994100e8101010305450b1100030000f406941c0070344803045041000601450340c003a102c10507140c60b100e004032111300060203800400e4001308050400305640030365000300701b4030a20440c1d2420045035907031800d680d10380b00c0403210060041421f0141c514269094006084c0030343d80c0300c0c4120302e08443c003403103482d0600c9403c00307000000882040e14098403044910704110040c800f40070000403840184200c0c81c0388000e40000301c100001141e054424051540278580144040084001d85271068100c1000d5100c03010540c0300c0c500e0007500d5620ba0040c5441d8140b0381252050300104681405011f081c15034030f81102c007440030001c112249800f10207050703503101c1c1485619126601e240c0d124240100d964805000030100803064480300780c2c80401c107010345c1d20554061090342d031b10f181405010301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 417233830 1250 417232580 417232597
    0x602030405041e181401180b151207060806040e0c010e01051606020c0601080606030a0b040206130306050615041a0f0904020c0607031a010c02060a03090c0602010b011103 75
    0x200100020819440c10342c00842600c040c01c18841c00c00e84030440040c0484081c0664a1842c001d45860381e424011045521083e1700d40400082c08105c11030440c80090303410301c81d0028101504000030501041e04a800381030302c210045e107111443c106e50191a6900d400724800c94000031032040015801d800e180c051028840c1c610310040c900314250354019101c40c0340f00700e2060b0411105000c410f008900480c06510180d00610f070041e520400104061f0170480140c00150345030344000280301c02c5d070710006122401c194018045444644442c400544584944100001100104c00011041c4000355220501900b01191803a25816154084c04400d0250f80b180380d821600c14035840c1c0c0c145507640000e0201007030000c015454010307800e000400f260403007140d0314000d03804001003281c515010b1080e10f03401780309203005000d01755400380020004044210004d014500101d0342c00003040c0690040648940c2c0426201c1d81c05407a039000030300030070194002070700180d0808034480c0d4601c4088115a400e8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 417235080 1250 417233830 417233833
    0x30310051519030f051302030f0102040b070b04030203120709051002061009150503030d0b09130819030b09041b06170a0203090307060c02070315021305091503190303150602 76
    0xd0b20400000765070aa96480b10050644a80d060880460f0622845100780d420f4915024222a1401414036012000c11240e181d030307104003c1400503500c540142c3e44215402a1400050741d00e81c6030803815401001c0390058813903c5c1405002c40300360000d0451007528416a180da10040324103004903030340d1205030340318402d4440c0594140400c1d106904200907901150094108450355040428556800018100301a1b50f444c411810305140824555801140981c01083d0001d10742d2180301c011310aa00c1042401c505040c43c04555a01039000a0403040b0000c005040d42d0bd01410403c080302850018250030000518001c110640503044646c5800c03c83c5a01c402c007562240c0246000b0751020700b400d180f9200a00240000a155019800322600c00d640034000042c61454184840c00180c810309140500502001c0745030504a05078030201c1d68200d0703e403421a00c0305001d803d0420204104039405001e02100354080003925080c07001c40b40c3c442e0b82c007005440c14011510f440110140103c5005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 417236330 1250 417235080 417235087
    0x82b090201140a020a05060414070b1806030a110313030905060f030f13020d050f010c0e031c180909170405150a051903090302010605190303120b030607020303100515 73
    0xa5035030076000d00f40c1c90324203004079503d01851743c8460386000400ca408544840040301c0c00b50001d58180100001410300801623410a0518203180301d50110341b0540501a03c1d010001a503461059004410418803884140e40d0720700700344c6128040d40002180a070085200c9440c0015141000002c4600c642499030f9101d0650301c8014002c0f0744010043c0103401114030b50040c1202683e41c4002d5800400c5c41440104010482c5600395800e5a1070940c0d06020b1007000c480b4444507031404240e0402c103284807400a01401e0113900c01340d0341d82c00381e8402c444900b48068070219081c8415445898190300940b0107090900c140156001e071449140603840e00701504a07508510724504802400709100107041c800e0400f00c050450020003071a001c0d411000a0315503190b4014150288213080c003800003551003038051900100301c49072880741e51000504000c02818446003100866201201d880801800e03102c0600301400000c3d40c035001030b980e07524189040b00d80081c075442d203943c001e05580c88a0141908 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 417237580 1250 417236330 417236357
    0xc0a0903020d050a170307030c1b080c071509060e0a0f03031b0f0c0608090a03021b01030204080f0c010801090b01020706050d0b0d081905030903030c0a0c082b090201 73
    0x5104000c040300f00c6503803041c248030b0b03c0051417503818441d442e45035100d010703224940040000c003580d94880710b100078480340c41c500e48149900c2c4440070407159007203d082c41d501c82046420307502d007204580c404540014a41716411000c0c2d1310140002c111010399550b403c5a900c10401c20a2507c80b504c1218862800101c0030800280031b5080b403401d004240d4600341c00818142c650180c2e80c045403004944102000c0000d01000e6000500623401c00f0b002401401070054595000e55240b0814951611100300030220040c0c9070b1003501100c010703084e41c10682c0c14682c03841080c1950b500c00100303072601042081d0004120f100b024461004406016401050064589441520554803407958060159103504000380c01d9240c20368400c06240c440c410030756440007004144000c40180c0c140f51010030030104244a8070712800815a900301c4001c40344107941d481050710645144025002c0207165440110b00b401032004d04e444106a0900b01540355266800e200a50344200e030b901c1070009022848900f88a031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 417238830 1250 417237580 417237589
    0x9070f030c03020310050904020d060905340302091306020423120619180b0a0507020c010234060305090106050109210203010e0f0a051507080c1e0403030e0301050c0a090302 76
    0x90f0409d0000d041c150540b103058445500f41c8a0280050361954000300400c080744030070b1301c0201c003087c80102000e840c0d03240c80054580001c40510000c0d10a45240307012415003480000c41420507030344107100310341e200d80d149900703120341001036000820003444004241c01400c14103c0180640a00005080e803540c0388528409246003081c01100b07001c0d5502c452140d03c50300031503e10482400380140607250b240c0b40f44020156a4000c01d160b085400443e1030381890307600024502144100303c10072200a601c05801d007a00c4200000311300c1d0200301b02e03241c0003407000c1d0950300183c00b5180b020000d0000c1500c030401503a00c030f1602d11844030518030000030341c094065035009400007a440200045104003a1000f0145080c6540304103d045400484464040190130807808903019035128070f000061130920006000ea070401040304080d0100000c0c20115070080b0813510b01c00c0d20448074455100d0382c803402d00820640c8940313800343c0290f190a0200380c445045a041c1c80c0d1032000e6035a0f01d00f0b014116800c0c030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 417240080 1250 417238830 417238849
    0xd08030a020d06170102130902090a050f12031b12040609050f040e07080d202112010b0306011d061905070c0b09090109050103020f1e09070f030c0302031005 69
    0xc010710350b61880400c410591040c88000322413100000341c0c40742d00340f45258050041503400047d4951041003462402d450f00700040044aa007210340e100d0342110b007808145c2000303003074a030560117020000301c4424513501d070140e0038201d1611b00201d8461040c03040d5070072810b124502800001c00c00e80341d42046945000c590900700404080c1001c590302d03024070700c072518002c001e4011450540052520003041980000f4895040402401c10110791000744d01c0a9103581c10710f2001192400c012211a1060783e540007254507881c0d681556540c0b543c0d4440012060344c109903900c42c00140784154a61913a40000c022860036200201a00c3c50205008803070880c80f2410341c15002884004c0c401030700820020135a11009000d0400e904c0e541300209000c100c1d01c10300503000980890328150040c400358440d841b445c00d005000f49c1e0010380d90300040400300a00010714040b15440ba140344200303c0c2c0d0300d0b8801c00e0703491015007903102446400750080d0305500b03030f000844800c0d02c1c039078503814100994030b03294140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 417241330 1250 417240080 417240097
    0xb09030a1113050a1d1504060209061303060b040f0e0d0e0a0e01080109170f0a030b0406051c0c0f1d0a0e0304150219021c050c1c020f0d08030a02 64
    0x20004145030b00d02d102003d48808403503502180d680d5256051072041030f40742d0a109140418040c00010703940d258510380c01d0202038409001958082142003203902c40c00111012001c3c014149148107603603180c02400340841c00b0016010324100680c850401c00d203401081c0020666001402c404040c040d01207503007a00c0d6000c21230b03000015600c001a0800f52201d001e02801300400041100b1500d400c12010b01c0b045030b500c0e040d00502c1041103071990700308002900c808a000e1f140104d8040b026400040c0130b0203554103c154841812000049103819140c0c80e074000c240326404c08000305a803580440480e80e907078462003000d040c0402c602d0184041c104040d55114200c44e80000d14624011412481c58001d40c1100840400c81c20b15450f280e034041005c552000240201e0f6000a04280e01040e040008030100c09689101d0103c0391080040501240c250400003402c400980000070b201c402c90348040c050180c0c000d8298081135040f44c180103c00221854016100c0c610395260040d0410080d801080c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 417242580 1250 417241330 417241339
    0x3040213021801140f040603140f0c03070c0201021e01020a030b030705030705010503041509080705160b0703050705070e0a090b0c0702011e02011512110405010819020406051203130b09030a11 84
    0xb5000300d60b0b941c40a41702600148d500000c2180e80d24040d039200500c0a040c2c0080c0017162010403041051000480e90b0043c59454449010160f502c0141e18103950300811000c200501c6001e0fa54186055001d85407084044e80c0600408003030100b03240c1c07140041c0c007425402d500604010300055001d0070086401a200d0000303115100906d05030201100c450240c00c813021300300010260b0610800f04000e40100030740c2c1c900451420320b00142c3c14081d10410034020240f20703011892405010040c001ea00080451030484035107460408030380d5004024008080319820300d0840414401c000078005d568a8690603140c02d000d01440880d00c40911703905898a00071503407929881c5079450f201401709030042c40f03103022201c070303400207840d05190848943da0310900032131624004000f40703500003031b09115520000340f13003000800882c000705001c3c102070340006420000884c03256920040c004003c02006030ba00d003900c601070781c80d40006c3e030480c4903144019605610080382140400c44500c00c110100c03c0050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 417243830 1250 417242580 417242587
    0x905010e130207060e060a0216020909030712020705040c03020c0d0c05190503190305090c060f0c0304080307031806050d020d090b10090b03150408160f080304021302180114 76
    0x103003031000343d0f80020401c480b00c2d5100d1824034000c0800f0011141c00c00c80b01e440030b5041c90000744681540040e130070380181c802c80c000400701c0d8441d43d00b0300480301c400350804100010380c88603440c00381d5202e040d0f10807940660729110162600a00c6072090f158851224405440400100b0030100da01403946582514140140c0c00407410710130005c011604107510900c0a03507114020141c0c119001a00e402580050609040410803210004104504107080841d0001d8840e69024044d040034040c002c100d0714648400100401c000c0c1d000800743c18094880d90342c000614180c209000107403600383c420b540200303400303104444240b0411b03000780024802ca0440010158070648a03100c1c4502c0a80703000c010000703900000d0081015501440c218101d0075002020340e42c484081851110030001e001903c1c402000c10007410311201c5000d0f258809130009001841e9005909207200707180c1c01914200d1040013182035007101d500050080c1c403c1c1c540d0841008a00100700c4005440d450729250005640342003c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 417245080 1250 417243830 417243859
    0x1a040902031b0c1006050904020f0d031e09082104271d0618032517030106020606040603080a11100f0b01080c07260f0301090203060f01030b010905010e 67
    0x10240480d002c600d8004c0001c80c40c0011100111021a0440c5015030440000c100c05038803104418040100b0991b40c00e01501c440d4102110090b00c2103038030000d9041c400400342607141d8003005100a036041d51065804401382004400e080c1e15855024640d90305c814001004455010054885c0c1d0400e0008211105020b51840604aa041e00d070700380c0c42039506002030010b000e400c000340d0341d0140803891350030088120544102d940b8014800810820541c4420040d100c0e0207010ba00c1c10f0b070540c4a0310150015050340060465038100b406031200601c210000254546014001e80e400c0740e42051103246005000b403000c855507200c800002007648101c00ca11a4405d40070310a81d10781002a03c80080c1c4040c00300001490514043c207549200d05041c00324001186080860032183e80308020180041d540307030040d440e01c600810707900c4021700c200440005200d20302e0ba00198416001121207181a00940b0b0055046601000d01c0500242c0486818000d0754001c3e2042918840010100580400803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 417246330 1250 417245080 417245131
    0x8061012050a091202070e0a1a040c110d081005120f061815010b04051009030b090706032711060405030f070603050c070b0c070204020d0c0e0a1a04090203 68
    0x1a200701042d01d60342d1800005110000e60b80c4078000310140701178503c1a142500d800305a0202a188074003940c5e90700c003030910650017003c08050410340070704184003640b036624000d010360811a41e035030110b000d06070700f59180e203210b075943e40d218480341c4081d14640ea00786002d000c1c07140c1c4910801c079280d01c00c4100da10000d8104001051090302c801d202c00b0301d58a1500065802c04400750100804513a040e40140319450b9010240c81c140c5005403246400211508811900034625070300190103c5002e0b02030044154001c152a0282e030400c0d00c05010b00c0c0c000c0d4008850100340595617060781c45482d07000c40c000501c0d0110819000d84014901814240c4403c0020b00b006100c1429a02d0303644190380030000c46030503004071640607a06c200d0240c01d04402e51640b84a514008041d9000036000180500c11903450303034161001062000010019801e41c0e0344050882600e10010310300c1103c1c40b4400244800da4250041180801010003605103450124140065000900300300080d00320000582c900383d08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 417247580 1250 417246330 417246341
    0x605071101090b07120614120102070206070305041a0427060b0f0409150506070f060f0501170606030f07140d021914040c27050301020408100b090708061012 69
    0x15405401d10f5040450019100c0140c402044072640c0c2442d0f0f0401903070103190030f040c0b000c1c0f00554940201c503440d210b02e01d00a11070144000d600180110703030103041c103500c5400b80c0156440c0301c1020340680c0360200750150310b0080d481040c40d00d480549e0302a45041c2c070101810321034918440081529515040e80500316048428151000400464204103420440c0120303910441c010091080032414403000c20400e00c0b400308040e040104501c5188100705003a406600542c80c03c24040046507181c8441d50205064040f540441d4420640850030f90f1401046601c1c0c042e209900900000d0314100c804e50440000350b085a074401c11180c1000056101c1e01d0b109084140d82000541c101c03410400e1401e0380c0f40c92400494061450190039580c81c5c4d400c1020b480c2d032020b0800c07800660004104c00e100c054010b42d04003c5d015400490f000404010005140d0081d800005c1c040c00101e239031a0074082d5004040301e22000186410003c180d1318140601c0002e0341849521b4030392824015032101400f41c89 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 417248830 1250 417247580 417247583
    0x6080303070c1109060a120311060411040c08220f050109060209120a0b01090e010e07060509150f0405010311071407030b07020a0302150603010b1306091503080304060507110109 78
    0x5945181c0d41c4204850300d100b16030300034004c848034900c2d4100b05011400241d080d003d007114141c8401e440805150189030010b6641c04c00201300e6400f443c180c0741c1507a03220510300c2d980d8019030030400100c0c00c050007246820300ca5001c0103c1c0c0c0340a060002100c0c0d0000034010010350385008400c00e82408038100b8092012400d002d8280941d03502030b00410300208120400c1c070804c85420450814002540309038032a03044801a01d8089070b1800015005030050a008800080620034000d000801075009030240a25403c11103403003420502d0071007216182c1c81140f040002c803000400003480190300940c0140700c121490542c1e1170600304660764001c010f902c04201c2c0442580502c1e410001c000c40301400e560b01509a20281105a403690307800395840101d4154030103086994400201162025480400380900c014010410044029044002442180034800940341004c01445200c0650740030407048992044c4c01928594640e143d42c4010f18004d0044020042c1240356003d000f00240980007885 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 417250080 1250 417248830 417248837
    0xa0c0503070803150306090d05030411030a0b010608070e2101020403080418050c0a081b09060d0209040518070303030513020a0320120703030c14030310090b060306150702040608030307 81
    0x3424540e120307413060080008914803e50007202004640a004030b95a41503080c1401c1c183d0712a251072400d8006150001d4050307070144070341c1c201c9030140315464804904032011358899948075290224100c844d602d10559445c2c2000c08101a45020742c10820840039a5a05000050503d6182c0d5920042a03002d680040e80c81d0781c2e4040b1454060300782e17100d850380114035100c1040ca0000305c20405403021100415601071542958009443c041c550001c4030240d050042c100341d650b144403401c141c005c1d001001454001c51824002401c08034513056140c1300b41582000800029103075640c01c80280000500c1041090442c00e0500d005849420180c0c01030b41c1b007041d086c15059149940c038855a5039105803184a90020141e07090018808500502903039050700d40015100054180001031508000300c41d2010321000040107010120701d80c2038429203954000500c1103003107440802001c1e001c1503a15640c0958651202d0705070252140040c09114406040820348950340c060490460704211509000b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 417251330 1250 417250080 417250087
    0x70c050a08030409050603071202090a060e10060e1005190219061e06030b010b0a020109020607050708060a020c030415030b0a03050d11060103080409111303030c12020d0806060a0c05030708 83
    0x4c1c440c0034003840398050004d030004c0c01983d1802c05c0b034140d0441a054060701a02681c00031607034080c001e402100c09464071059069060a2200005242402601c00d9800150300d0b4002e0300ca13035280c41c1c2c8050340421507640e81c65040c8544520902620881c0d446010150f12480c3c6142290405c0a8040603100b405100d00150079180a004400f45080c0d41110f40c003031a140032000d00004040c5c5049505542a540c400341d156442600140d004060b010760117540310340d010441d001004400034241d01a20790703403410f0300c0017a12141101c005078001c2c01c608540e1504203100900c40200e0302d1001400c030300c07014680401c0d000d034207402042c040400360300213507080e4012016038090304e5002441007c49a261b0340080880d58995140c0903040d004d103005000030140c131042101c0d94400c2d9181510b03210021040c000c002150f60340b9000c4d1080b84a41c0c001c555104040e040800924008075501c0c483c0c590030b84a8816960381c0d8010000075500c01900b000c18840800160000315000b00060142d03548100d003030a55 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 417252580 1250 417251330 417251339
    0xf110d021b07120b0903070302071406070b01030c081c17070504090507030e0607090f0302060304081e09090a020a1b020402040f0909020f1005070b0c074112070c050a080304 76
    0x3c504c2c400814112080d881007002d04c000170742c0001c80c48100c584205410100350002030002e99148a6410040c2c01a50548004011300c807443d0b064000721103500b4219003440c2808008180c03103900380c50040703001c00c0440464900d03003650b8042d4a541301c90700e03213083d503e40f1340c888081c0c0040302d07425582000069501c4030400540d80c410001e058003c120f500307252003213501d400e1448980c0409030000a00554011001c50100040c07001554028104200d02001c005004a400b82603a082084010701c104400804158070095900c00c99040c1015982c030710304002d551803000c101d84a4004800c0703030015400c100000d2140703034016115000d0815203001040700180c030700400803604d00d40e8520f0303485600407580d44c0045681000440e003880d1307480841303821b003940c400e801040741e030141c1d030340c0a0082c21070070a132480e010071040e1300a0003440c00c0280c03000300c4044d5103c903d1103000d503160540c078180d440f00c1200040c4e01b403208054503580d845101005000e0b500c5101290452070f40d81e00205856001260502 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 417253830 1250 417252580 417252593
    0x405070203090f060408031e0c01090f0302150c030a0b0f120c01110115120302010b1c1a060108011e120b09070b030c07060207080d15090f110d021b0712 67
    0x3443d141084030000c1c01c00382007072800c40d1a44503c82d2160000c00c0e500c01c442d5200452101600d00300c10806008004030040c905080d1009000c540e8101c0050190405070000d4a1102a01602925002c1c0d212411680d07007000c00700051221126603644a40ca2030404c00403581c0300002074180b156400040d12001c420b080002d081c16600e400d030344c030072a41040110011481101184801c440c24207051000c503a20350f081c01e030700406d42506600c0e0001028070f065143d08101825180f0f0603071060403d00343d40c841085558001c903c0956807030340050980f200402441d0742081007900c180c03258420081600303a651111070317180d8081a000300d03085201101003082010f02801050001c0009100c1e007851843d094800103540c0c402c00038010300059002c180f4000380301c084810b481004802004c00c202580c00011548008070051045150700382c2092081c61410700709000340f511a94200700b050b4107000c14502a017020790400651007009000c44c1d40c00c0480a9803c01c0f00d040185070141e03149100b61598103018 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 417255080 1250 417253830 417253849
    0x807060c170a27080901180e0901050601090501050a0f08060a090f0b10020a050a0210140c06150105070b0406021803030f0309010501140d022107090e07080606061215040507020309 79
    0x511240c0780882c030034040744c1454112100780c2802d190030201d519132100e080c0c1038490190040203d080c803000c204020340790158043e83c0104400d0f2551a001590741e80110b81f5446108a0000001e454980c02900c2c507020301e9405401001c024105034156443c0d000f1706003101d0441e000300594584400c491043e071305204900d07440c0051244090030b0f042c2d500303442e00b80d070f10000d0b8400207004d4209141d82c00c00c42807040890011035901c4942a658940c04207030074550710f00c0150390040070488000400501903000300210b45d1801c0d0301c50511040d80c0d40d50785850000350040c11880e6469501c2464107442e5035024401040c0e1400121a8183c4a0424556040c00c590050700080d030181d1104550121541d12840161049a0304846d5503828a803000903441251101154030038203032199417004501183c1907044914005c11740400c840c1d00944c0c0780440760ba0b90300305464030707070300074600704080c41101111182c10b44d8402d846502d0101401d085801140480e442200d002e001a003021030320707103032519240022 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 417256330 1250 417255080 417255131
    0x31b0f0a080d23070c06272a0504051e040f0b0a02030709030212010f0606050405191421060c03041a010b2203081605060f040807060c170a 61
    0x550054043d41145880c502101070f00c0340c01480030454500f02080300c0e60b0000050410304907846017038849045855043c500180c042150207080842c0200134200040241c01d80812070101d60484c42803501c0c0500000300000390001c02020070f40000005e03c18200701e138490159220320b41c1c2809010b01410a0151203c004d0702c807101c1c0900410a00100f80da000003104140c7e90101c948101d1004040e11050040c4003049002184600301070740014201d4001000c1e000302c5405a50201501c070190050304c90712051400307007003c0038089110f06002800c103142c08164481c10001002180307000d0143c00c928003c000c544203501c5140000c104010001d5802c00340359850720140848245504000d000b50b4503016040d080302610f076491260a05031410f02c46c50800847d040102d640d42c58200c1302e42034281100c1d5407002c0e900d9100705004240b4603441c403a0301c58859604090324508010990b51150082d206807810b88040054241c0f04440b40300b0240700c0c40d4040c01c5030b60070006000c50040c0000319450502c2c0710 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 417257580 1250 417256330 417256361
    0xc1208180106030c090f0b040606120b010c0c060503070210020f07030909090314090303091e0103050f0906011a0d0c02070305010b0411041a1902030403021e03031b0f0a080d 76
    0x3003000040c90760314075541039580341903010a81c4001b2100f01d90040051805131b907409801d001000809907080244543c3c0409030082c07d1200484000055030740e03801d6000700901000d007250341041341c1072050f8060340c0c1020541c410b41c0c017102001305021041e60032080075811810b1002a101040540141d074001c001c00805a0074004c000325500d01a1928401042010b091900001e040400d65000d000b220900400145600020948140301d20030070440c40e4a41030106e8a444003060039a115050010300c140f05000007000c03180e09041700c554280c141e061a4650405050011441950340ca025895000e07140c1c0d070050004a145081490a4414182015000328901105058920081d44c1101c081c0c07a00f110040348102d041007060704580c07292001e040c1c480c0e030402d0445c1e040641c0c00f10003401200c0c02210f10501542039118230004548094000c079916600800c60450117911f0448001d20340e603016410760300c101241d40c01160030902901001c4a010340006030500341072032944503c214444002d078 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 417258830 1250 417257580 417257591
    0xb28050106090603110313020109080708060a0e03040b0703050f0403201f02030714122701020712031b05061305010f0c0906050304060906110918040b0112030c12081801 74
    0x717246100900c40604030201c5418142290401d59001c0d1040b040104240c1c001c4550300c2d40d40d401825100c0c04107450200c80c86092081d04064880000280c0b01070303500140e24185800d10b00d640a48041d400144d0203d100d4005104c004045078180b81800000010202c064074105010b400b0481541161401c26a00d140400c0d210704020380e000040d60202030740880c0310340c81c888031840700b1854456901c4848064072030004000c202c01c5d00c1b020480c0320042d420054018604105001a40c070341c00e150040c0340014002040c0940480d1040c01c1c004401840c4200c80c010650554441c0c03401c2010880d005031100c103440081302e04002003485004401d02404004100720302c03075242d0081494010b48100010414080041804d00c030715584440314040d4403040c02c1107146413207410b6540035004209502d1103440c1030070200c80c84c2c1d10460419413003142d0200000c41142e0070500090000395008030254200011902c0d10b10003e0b401e0403107000800d02d0b680352103506181000c04440e02205040600e4080c0c1d0400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 417260080 1250 417258830 417258851
    0x30109080304050c01030614100215070903050f06010602060705090d020a080c010905010c020303030f04031202070606032a0315140901060e090f0a1101031b03050709210b28050106090603 82
    0x14004002003404542d500201615290f0484c94032800b0040301c078049102f41c05100500c0d030400d20041c2264410015100388000320091252102d2013441845c001d40c100d20006a201e5218030300600d03002a0041101c00143c40d00c0d000301d800302509400500d0598081c025501e89980c2258406c0c004240034030b0181500400395021030349902024140a0810030903102040405000e0880001013840c1000215254a06405c041024001ca44000e41d04c503440f0110310003000620710300404199004080d00145603203107075151201d0104808000744060369600d85000c0e00d1500f410f5840c000c80c01c44001185280c2441200485100b0240100c00c01d0381c05842c0004d80ea110110300c5030a1903402c010b00e042440403040040c4c000d422040c0700a041c040c00d075079090801c0340d0103502c80c500611a55840404545d10340800400149070400c5d52030409541c541503c0000740204030096020740030400e6542404101e1101c0464003450984036100c103070b02c5074014000541c0c080020030040a2500d000d03c24040784 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 417261330 1250 417260080 417260099
    0xa0504080f0d1803020d1202070317071506232d0a0b0403030807050d0605090c1209010c050f0f090a1d07020c090402100c0203070b0c0c120309010815030109080304050c010306 77
    0x8031170041107c80c0c0b0511140302d650003480715800464010500111140011549620a40c4009821500c03801e42d1a10303105000800d100d6101520034503001411f602110a0b64114030803600c40340550300401500240d58256946542c02c1840350054400c8106014240208400c59100e6003107a42c0d2500180810004660310164017030b0421840d0400641d10b0061202041c0500001d8004c0c0742c1003101c807028407004c00c0025008000d8486c01010090b001c0e11441922030036101101ea0050000d00d041c400c40444001160042600d5a015a40701d0702d0b100e20382d000b080b103404159019041c507400040002c43caa4a40c1070b021503010301c8601c05480f01241c81000a200b00c2006403000e401881140c1000c2240d6000344415100c0c0c54004049400180e45c48001740c015a20402080390540a9034174000c0c6641030600040c11885d508101031410010314200441d8000c0c0c004103241d0308500e462000c4070440e18284100052075000d07651081d642e248c2410074914140010b59110b0401d480d01c1070030001e8211 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 417262580 1250 417261330 417261349
    0x60506131a07020a1409100303020d0315090c0302040e15011d030a06140603160503030f0319020d2c0a06051e0112170315060a0504080f0d180302 64
    0x20085408007410194001240740c0d40182440250000312280340030a585400c551803481d4528100c07801c065650702d000c5148603101040c40000e02603808004074106203400394103d1584001c2c40341c44e01000c107540300c1040041d2001c1c0c00c0d1480100e98002000d00400c031484503120341c4036919100b0700c00b1034031188000829022401840000145e8080d44500066409010720044941c0148050103070090800540580080c140e90b034038428862420b071000303500140b04031403007103130401400303141010100b040e280c1d0968030081c001414012840c800b00154030302840601020345440c0c84c0040c860f994454048a504a0050314684204090100100b011400150808565800580816142c5480e030500c0c4c0c1000405a007030380042c1e03181d0004143c811090700c1004440b40925040030006d11001c0e803000d920722040ea5064225140201c002155003403403001003d0f030303146502c0e00c54a03003540d4009c028100400c0d0820703182c443c2c111a103048482540042c80c17604c1008580d00008001e8650340c0090188203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 417263830 1250 417262580 417262589
    0x5010f031b12110406030b070e13060e0f0a0b0a09020a090609050d060c020102040b0c06090106060507050a06090503040f090e06060301270213050106080106080c07120503040609080f0d06050613 85
    0x1075018841c400c0380c0b101d810540046da444000910b0a090442019106640304040d003030003410301d41c402c08402c060900038802210321041104865440310120340c10480f0b0014409a8903a854012035401900d82080c81402011082c20043c0c0f02e40b0215402040b070070859000008002c20301c6014040e03076540701c508061300350303100c28001044440081c090740a400780c2c1d030000b05d09440200d40722242103808100c1c3d610900f910802003000c07d80700c40b0160350038050120040c06950001c140b03500002c2032503000f050018011400c8a060603610745c403001018803e908500842c0361a01d101c402c0e961400c20805401482c110024012907000018808681c20344040703252002038640e6401007991501100d0801d0038200300c00038825580c642c100949009028440c1a002407804000940480411810381d1030090344084440c0100d05c0d246000c60b0990030207001134594541d01ca00d90400925814000e06265092091550701d805000300500300b1290940e0010f801074904201750300c1c180310b00700142c40a46 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 417265080 1250 417263830 417263843
    0xc05030a020c0f030c0106050a0b1204080a0e2101050609040b2a0a0309021908060f07112a0d110409050f070305150105040216030516050105010f031b12 67
    0x402c010080a4900507258056055900001031041c00c020b00641080c3c0c04c0d82c906035203115101e942c13554924028072605184140c404440c4004c9400200c16600a040e08500e070320b0025044c105480004810180075000000344a03001c400e01c9003100400c2c02a954405012162000b052a0070b48400801c0500140154a481e61740ca4000e440445140700c25468641b076800c2d487d882e0f00d0440b0000e00281040c20341688664010668078100940d0141000203a4880c074020749150303166170f0240d204900000d4036107002e0200c2008003440940042003080040d00c504081c2002d118038611a2156443c0317542c011032b0055205920850101d0030074040100040030903200040d80100310f00f46641480380b95000c2d46040c0c0201a000418098009000c0d141030708100300c0000140d90b2030003000b00300e103d82054101c007403041303914120100f40200c01030250b1141100d030841074100d09503121400c40e4001d8008444040020500f403090040d4901061548081140411401d40c1400c0340f05580714940400102038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 417266187 1107 417265080 417265087
    0x1050906090d0f0e0109120501050a0605120303061912030306090b0a0806060d06110a051b01020a08010e06060417030c1612030c0c12031e030c05030a02 67
    0x3044242c0d803150994600180300940d500035642e000c85043c400210f8002401e103180460340e41d40b1900c100e000103180c3c6001c81d003c004131256504841c2c050910a4011044400300104494200790100c1d8030242c904044c41c641402403a0a8010791030b114505180e0408240d055003103441540e800745802e03c10a14054184a40420f4511515920381e1200b00407844504040c000000c1c1e80380140c5010072a0a8411415640d0f61b21101700e200002d17000255a006c0c070b2446100b01c051600b04180294074081c0d18040040065070180691a41000c2c4203003c181039270f07500800c85006103030021a954044120020150300c3e44c20403c103809560043c04000c00c0c0200c0350510311815200344451081000106803411541c0d5029900102e500200444001c140500b00100c0d07400381c00d02c02c3c0ea9003d00101a0f1007121444003510304184141414060044c074001d0b0008150fa42c06002c01d08016103 = true := by decide +kernel

theorem cover : BRFrame.Cov 417086330 417266187 := by
  have h0 := BRFrame.cov_init 417086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 417086330 ≤ n) (h2 : n < 417266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
