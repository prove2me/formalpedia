-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2454
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:46:06.247688+00:00
-- url     : https://prove2.me/submissions/15f4b402-0de1-46e9-bde7-f7bb52c9cfe1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 441187050 ≤ n < 441366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 441188300 1250 441187050 441187057
    0x50406240b09030c10050304020405070c11040e070f08030909072a050106090504030c06060609120b0c09120616142a0d020f161409070c021e12010c05 66
    0x2000d090b00c1d50001000319140110400c1c3d269484844104441a12507000f8000c40c400e81c03003910305210a4031031007400c1d44c01a80251004003000d0070f0b50650302d040d0400c0d901c814598400c0030201d808070b584d5683e12129520704c60300154516040041e4110843c1401f41c50250445103501d0b00c105418403400002e00a482a161080f07408041c0421031424800250005406003014140401041c00e09140c0030344450103c103001c660f01810410005121402203041c2c401715500c040d545404e1910325664264074207001440c2d01c050710414056911140c84d036248100030810484003d0401d03082890009c3c00038014170550808000c0b2090070760f85c40510f410180c0c0e1100509818045080c81c03030000c100c0e10346030040c0e00d501071845a801040407880d800286030f118106100180c40c50030301e4021502c04030a049015900c48820040c1083c0ca050400c00407080c0d01070001c1ca000319801c6001d83c00100381728040784c1c1038402010194140043da181603418103d2900c0e80305c008026000307510402504a00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 441189550 1250 441188300 441188309
    0x3080c0c190c0b0a1715090601030207020102070b04170f120a0c03020312090c0414040c14150409050612150403030203100902070804060201051608150109090f05040624 74
    0x104052801c404000c10076100c40302510541040c0ea8a9100c00070000b026480d0200075007000c0500400132410b084400012058079580c041d0810401d03a8900005502079480710404034110310030007400241d040241000380c8003921403071100e1044204940400c0d0301d012220000c145494000c02138030803901e808101281c3c2140c0160506441244180c00d003a4158000c4401c509014000001000801140071070284002002140c007084061016048105543d8080303030000c0014020f00d009021fa680b1594030181c128100409210303400c10700b00c21400c900c0e00184c0c019245c09441e08203000e000d1505a081d40e41c0c801d00d010090806000e01900000b1240001d400075091581c0080402c811200e2500d00e0400780c145030380107550307034021841c022926a016100390f00c011b500c1c00001c25843e082c5100754001031040755682c0c00c4581c44416246078143c1c1002201414800f1401c000629010384e0300949100c1c1685d0030b000103030b178034050814400f81c0d4085d1002140708180028100203244d008282e80082d075 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 441190800 1250 441189550 441189583
    0x14070503190f0e0a0507150e060d1b09060e06070b0412030608120301030605100302060304060b01020309040e16061806120605060f04060e0a1202010503040515011203080c0c 76
    0x10310741c507450764004140c218122140c460070440380c041040300024001d5942c41c40380c1e08442500e0ba44620101102502d40348281c0001d80c0308488840754909413001d0304144001250020302c46442c00c001038000d001e5020841c01081c0700300401c101c007a4101034024859401600c0c4945404110703600e28013400c0000300000d000c00c902c0385e46042c14034400d0344160f014120000c01c640c10184100560043d9402c01d01c0119801c0341010001804104900750032400c5940c0a003805045884564482d0040d1071501c4046045100034484d001c0d080d07941c1c0c01f0305848086c1c800041c1400f250700001200030109542c21001c03c4c840c140107400c0300380d064400d40c041101c0151a10ba80786414400e0424042c0c200c48d0b200350381c01000444d0006010083d10001d00c01c4031704c0740d105d0108042140040c0184000d19203c0d9081c0104003000c81c4000d540150001d40d401803140d42500d006940406503021405400c0c3c00c41d4203000300554140d420140c009a0303158100701c42e130404a0030300900901c5a44c0e00c440341010031220f07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 441192050 1250 441190800 441190831
    0x1805060c030c09060a0c050601080f16030507030215070204020d020c06060f0102030409110d060e160309020d0b130210020f1e0601060507080705060a0f0606030b0d02120a0803041514070503 83
    0x1c45c0d04c20b104d00c41d10b00da44601540c880756507603007500c0c0c0c0e18200624010030b9400f51a0701d241d100c2c00002c0003201166480070180c141c05103940c003005800c4444e0070201818000c00c018080040c0d881d07100801102440c1d41c40180c4410510380101d03d4880300404c01801580e08401c001c685a030000160f07001c84503601d0300030400280c3d1100200140c05186200e4031080d00300305001c50022048a009403041440102561148840354011016200d1b2960040d40202000b444071000c100e080003180c2d44809600d0300642140c1242d070104400c40c00c1210400d005810009851410700700038491220104071100344074502490440813280c64032018810344040c4500062038100300140502941c443c03a0f0401c050b40d1040c40c040883d0405811002c04200c00189000800310b03ca5000c0d2043d60207038107010380380c810030f0b21982e801c2c841d16490700c0089408a100340200440000c0c424001103114921404981c0902c04405500718152155a40340044207840d550400000c02e512005032070f4000403880043c40c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 441193300 1250 441192050 441192067
    0xa080703180212070816081203100918140105071407080405040e011523010c05030a030b0a0909062c0a030804030e090103120915050d0209060405041805060c030c0906 73
    0x2d042001d40c0401c4c00e5026011206000c030121201b0310088514190984000c0303898062100c0c580e1008481c0d01c3c5180002c4202407164007403590250801400c050035504403109680c8070700c101d6640300700c0c42c210300f60b460f1010400c595a100402d81000345040c800641032141c0d035641d41e41140642e0140e02c1c003441d40e61720006030907070f025005110514800c00031481032a8495900320f000d50000c154040300703d444600340c4445c2e940b091004040725900500a1401d040b140e403011805170500300045580030140040102c1c6101040c488c18500c144a400006000100329015420000841e0800c4401d0a00c1c0100f44d00e07400d41c081110300d01c85505161103461650b5624050b600b030340d02c1d844410307000240403002100f080b05034501c1d9013021100761070f0048001da4038458030000e80c08690324940000d07001d000003904100c1c0764010708104800103001d00e0070b058035500483d04070341108213480c81c2c0c42c003d058000d050240074001250002e41c2c050345d45145180c0042440114401d00d5112401008000380100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 441194550 1250 441193300 441193303
    0x40501081b03010824071b02010909060801020a270b0d020c010c0e04380102010e12071208060f120a0c060f020c0102010603260c010207080a080703180212 68
    0x181c1088030040140e20703035841d0354101d640c8041102803040e0800c100340c01d0114041c0e204480074807a01242d56001d064606518072041080220700d07040781807003804440801c10103424003a490290502d100010f803102d60070540180040c5030a6000601c518601072490300c0003e032034515005407201100b4095075441d01c00b80510007032158200080807540390030a42040140e20141008412008803070038800900300e140040480b14040200c0500c1039145240700003500c400c4003105a1071501400002008130000b0411070410740c1051258807d0280000c0740c008010352a54403038101040c030703c1c4c125a10720b81032022032025031784402528810f07100f100308004501000c1040248940d40420007000665440d80040c0c84d81c10905c003c04098050020120925441403041da011039400c1502060361121521034080d440114402070100319000304644403a1500034001000d07002c0c0305940340d40d902c2d070514400820600e03010301082d0406041c002c5020780c10344207041c060512a012905c4a040ea2081480503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 441195800 1250 441194550 441194581
    0x60e120703030603020a050105161101020307140705180c040e0a021605060a27020411070b0f01030c090501081011130b041401050c15091603050f010c0201020f04050108 74
    0x61500540025208101a07254210340200d81c805d4580220907501c4500540301c83c09040d0217905104030044401022039102e20144404002c10f005072860185152a403000c03504148044460035841102c081100f400d00145e0f6415000f0f130098441c006042400c10003c0358421440707580d00700403000012444540180d41180e40c007206030846000d58440d1881c0860725440110345031030700300c0e11300300588401a0550702c1100340342e80400b403040c0e054451982000002c01c41c0c4565080e82480501c841000104021545d42c000c502c5034203c40203d40c5185442e80314204c0d2034000b65021401d060040100c203200041c2d0300ca507801644004191240c0c00c4030841418002e1541d03800390f01c109454001140e2035200000d105840d011102103035064602c40c01900d09200d940c040c454954850100400404110b03030803942c004444405449440c80483e200445040c0300342c0007078a09800c502800c40000e80d00348111418800039000035404c200b041d034035409450289100e014103002c00b840018010844d0044503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 441197050 1250 441195800 441195823
    0x20a02031803100903030c020c040b060a032a170603151321030b01020106120807020d080c060a020c01050a090c090f020c0a0303090b0c04050d020d061e0b011416060e 73
    0x800100040d428028090300d0781e8000c2d01f0250048262051403400c150148422a0b64094440d5180600d4400120014000e40c1800396104111400300800c0503140d408070668803100ea990440c0c0d440c0c0003141500302c3e22010f46914804d07804884407240000ca015806580406ca14480c4010707c0702500708020001c2103195048142d06500d51404a0b81d41c02d68440318100d1002c0e8002c0012a8a0344074100c28a00041c0b80a48020010700200c8014a02585071642151046070114142281a410a4540340c402e8401640103074022500a2903003800b4412642d1000c000002400340301e803251a20203e0640382e014400d6042e894061280945006404461080440c0b0046640901d0241070050040c003403490200d801c05008804103c058030401c0a071400c0d03441c010580740854aa075800c00c007480c4450718044a01503101c0e21186c00018a10070185082c14400c0c501054601c520000106048088003140a02003024058400724660301c2001200680c0d00080c00107405034030400307a52501c00004071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 441198300 1250 441197050 441197083
    0x3060402210607030518070e0c030405070e07050702120d0801030b1321021c05090409140a0b0103020307090608060f10120602040603140106020a0609020a1e0e060301020a02031803 79
    0x41c0700c4021341c150b2082d0f120711029096054014000c1c07007020784a649030f20a030740302da0811030b0200304200d1400c130003540c00034419000c03105110b541c0c10540f0f4840c1001c0362482c0c08600d01040c680c0550904880b107209001042d0080c20f210a0040e00280c2030071030601001c2e000407150f0001540d411543c3c01000e02050300320895205162266030500b0707607025409003440050003090410f44400303a03c0c01d0240345428042d03e5840c1130002803800e00000b044260000e880d000d0340700c0d003000840c0409000d1814042d005012854442d81580149481d003003140d48071105292510504205405d00030440503008541005002c060b5142c004190622046540040b21480601000282049603540c020401c0b15080d4030280100c0c0b80340841000d00c0c0c0c009100b1800541c0100c1844400921164440140c951000f0b02c14104a42c0310010000700090f500e4110b043c284241c8018018110200c0c088e0703501c070703400310300139884c20302c503014025141d001c0c0c180e4060701041c803000b08034003c3d1b80900c181041c0346031108 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 441199550 1250 441198300 441198313
    0x290a0f03110d021c1a1c0609080409021902030301290d0509030a02060703090807062003010909030e0d320d0801030b09070b041e0b040801200403020306040221 70
    0x2151444d810041080e906062850419030481c2c120070a42000d00000c402000c180d006100541c44607522810b07402c003128219910041c082c002030380302d405403016100310240140c807a120710110802120080800c042954418801005003224031000b03160604400d20241e8002d4445102a00203806003010303409a603828102003100d40c1400001400c0d5901c5c0380da08850490b2076221050b4100d41074108041c1031001c2c00c000fa000030070602e4003d51035424140d005190303000f01c030740e0001e02076400a81140542e03644034007465041c16030149030044140c00860b003040e201c3d84550340e503c480c03c0c1004044205ca00c00040c2ea10308a050b8010840c003809032180c10360703a02901600005107000024001191400c848902041e162580080c07981c09440010301d0140c0351509106580481c00c80110000741d480f1000318020458494807405030005203030303040003c100800791984101c52180460b10b4010305400500003080135070b50010306150015015140c90103a111401c010307802074629440d0440d010300c10507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 441200800 1250 441199550 441199567
    0x80c12070e0a090c090b0a090b010c0b0907080d030e0304090c12060b09490507150806010c0809060d0b19060207060302090a031416290a0f03110d02 65
    0x342c100c81003261041e8056091300fa1100c000d103040751800250542c0000490320b0a000400700390b0702400350300205060050746904d0590394100b44800c1103810713000c035811008003000710034410000401c4c034515504003030041080620340f0315900d024a200b503480494490620b6200036005011601c0c551b00794500501001d0b464015210065114580e40740c001c20780699908001d0103548070f40300e01440540510108280b40e071042c0f0700030240041c00b16841400008005000407400c0040345d0081021450606d00d115140d9800750024000515542c140600d0802c14400644018211420010304540894403003040c001210020074407017005907000150340741000c4420480c03074a1041201c41c65821902ca1781d8031603100700c09a00501d15650b820141800042c400900c0c54240b00e40b150700e4007011201040d00081c0c20b10f80c40c14443c3d200502d5800c400403540050052180450b082c039508e03075015440c1004851005041280321070856041665440d190041a8008000c0394901c20a102c001d540300d5120 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 441202050 1250 441200800 441200821
    0x20f0406020c1305070f0e150a03051e04020307030f1505010b090406230904080c01140702010c09060f0305191b081005060307110309030316020910080c12070e 70
    0x41031511031080c1c4501c041c1d503041034100c0c001c0c41d201700201e0317503008000c3c000035000780c03078081098441680c414115811403003c501040041d00d035500c01e80da8041014145501d0520001e1f841503130302d885401140041002685000615408032a801103400200c69458100f10900000b4a868054054100000080e103c8907140291040c010200c07000c001c0c40c1da4800034034008107043c03141d000b942180c0181024151500d01c0445a010f07000710070003483c00c050100d1041c00c48110030030400c00748210390248007459030b09100701036881c1d0040c01c0c20600c3c40c1c01d01102130544c6c000000c48404141e00c40d0001130001031800c0211101c14a184018003207007095042c60381c01d19820800d910005203c03500000c82001007140d9403021148081c1400303103141c5449038115003900b425001e07800e00c1d100802c00d09205450400c001c20b03402500024000c0c2c1ea080d50710402c850124040e0002210111204003800300c40c0001c960b100d0410401c40340c955551801d81c04030740c1402c00f140d21018001ea681c0c020007550414 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 441203300 1250 441202050 441202063
    0x101101151502011d060c18030102030f091506010e0603070e100207080c01031a270411090604020723120304050106090c140706050703180f03110a051906020f040602 72
    0x405800900c104c80740d5a880203040d224011842280758071200c0460345007170414000f041443c07400c548500d444110341d00801c0c2685d100741d60805400502408011a5410601009043c0754907407500000c6410300d400028040c05ca1900c0c054450000000440ea81074050790076644080c00140107401c84051414001c0c1d100c1c10203100354007150040d040714a24a601c64401d100e03850000e00e9800c41c1c848960701c2480302d21132011000801743c074581c0c540100d4407060f02c61001d100d54483c2d4000c0c0444c07401e05090000c2c1d800081d100a000b030b0300600c15100000c0d600780d9000c070b440c43c440e5100e6020b135407210030f21840d1602d1050329a83c5851300006120a0200641219080d19419241404510500341d13045982c00388100a000c52407800b445035400158542d041181c000700640340214071501150b4140c41e030010309100c129a4003050303440d003408040d04544000552981070000e80044910342e02e546842c0c41d41d04a120100312801c0c200c840800210703905075400c2c0c00d464214180c4960301d4040296880302d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 441204550 1250 441203300 441203339
    0x5060a05090a0201140708130b04080115061706061902060a0b03070321050f1602010207090203010803040303030b060c07150206010509040c120f02040f0603030801080c10110115 78
    0x40c14900055202a400107951990680c10381d502040811241031031251a00705590480b001081001321160100300501800060300e2400d0010f0355a41c038082d029400c4030158001d113000312203000310400000b40c10001c85180152504100c1c0141c0e42c0d800009151413042c00035041c580845550103801c0143c0c0029424410800c1130420005444213004040d070720111440010304003801180000e818035a480c1d04441040d4a0b410094102002c03c41d41d181c6a0700080c0085144102200200081d903038100035100042a11500851865043c045226140c1c851030002809240c1c44e441c034640b1540751001101c107024403040c241c520080c2c541c1042103a4001013030800d401882040004581490309008085c0525481a070f100c0c000c520b01980030b846c05001c100300342c91003080031040302c002d61030303600944a1685803400001249421440d014001d010107811135038413070303005840e010903d40b15070401490f07169842c00c0c0703a22484150300d01c1d180503118502080a20600303c0c14000b42c114600c090025512 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 441205800 1250 441204550 441204571
    0x201030e070e1008063402070b0703050304050d03060803041a09060d0605010207060813140f1e1e10021c1e230610050c1c0e01020d020a0618020d0506 66
    0x2e844038166002008051b0549000034010484100d50304900c441082e00c442c0300314010364000c166140c4848095400c81c4200ba40414030010820080140c05d1018001c118440e003410401c66081c50b01642d0b5a0140e40513580e509580000c80043d150403030b40551382d2060b0001c0c04241d960340b180411402500c140c1c4511400340c4119500454483e024040c0d461054549289c0446240d001d62200c00c03a1169914504203a0b0054002042c01084144908200b60b00b48030b49a210514650784542e19007030800c500500051040030740400710000126120181a8aa030000342e2030f0076503000484511600704e4640c8548500d058a00e009a140d81f911089141001c1d01042100898885890058003400d070380b285a81049007002440510b8440d4440c080010310340b03020f908261b1000c440300d103003c1c03020640c0b40310000008150103006078015581d1000880138405804846240d907006541c0b0f41000c0c800130403440e00c0d1384580f0780d8200700c02114080780381c00914002404900781091500c8100c15a40280701 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 441207050 1250 441205800 441205813
    0x50c0106180c110a080f030a0204090e0109120f1403220312050105041109150d060906050f0102010603030207150c1707110f01090e090c0d0b0106090801060b070201030e070e1008 78
    0x1421002c1031300e180868010288a01e483c40345144000780354801454840007030703824480400c480744035110301a4490400b0000084001240c2000c0540e040c2040c0381504110943e1046201c003036100c82c1000b0f85442804c00c2d46d8580c0c80c5c10304501044002d114000c5106c8800542010506078084405040101550341c10005640c0741d105001c240d8416055910103100100806045400d0404180f58010882c0e50002c3c1003c84020b9044260340d10342d8440b0740c0080d220030302400285818410104a200240000c115451950350302940f150941d10901080390f54208802d880203000e02900c07030310103502c03410040340c104082c5010503464000321000da803070b0b4010050404450030511903105005a058485400c4c8903d0014001191a03000303044900c5030040885040c03203601d40d030402071082c0d8030400c9070288940c105000140384250a5002d00301d1a81821410000007800300200d034200c0d60207183c041031000c0c9444043c2c2c98a086075100b1a5100c0350740e42008401600020705c03009540c2c8400c1500c40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 441208300 1250 441207050 441207077
    0x40f0f0807061104230d020a0803130e040201090510020703080a0f0e030c01020c13020d090c030308090102030f011401030e100c110c3007030f0618050607050c0106180c 74
    0x516008034021600c100010156901410364071030210ba41d0a1001072101b102a00b1607804a0f810440c01d600c02c6141da800411038002070000040d00001070040340c2c6142d43d0500d0150002015182d15104803402801ca504011110f14403c0c031600c006141c10a4510f90b031040b00c000c00410480c0c01c01044000170b0f94800001300d80c0c1c503002c83d4200301080140e006044009120b000c014236060f103100720724a255800c124103002110207000348400707103020b141092443c52075401e0290040d08002c1134607485034130420070404036504142016040d10012442d0502c45d100070360050340200703005c90a90b0780d2886411b1081c616044c440d04251849030182d0342d0340c400050f40002140ea1114800606940130512205400d011580d08070040c1c10300060003d9034840b00744100840e030500550747c2041e60703a080341c1c5031754a09216240c050003003079040740040f803c4a62000d0701d8080e1982c501910540400200142003810b80009400c100b01900c1c0d1407213003141580345200c41000801601c089800442c0c4c01511030702 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 441209550 1250 441208300 441208331
    0x20d110d1b03140a030801093b15040b0f0402042c0c010f0206010e1b0a0e0103060b03010b031501030f1d0105010e131712071112041a03040f0f080706 66
    0x40190700d86c68121059090115250113010321401041c3c0203091581800800384410402d81445100c04100d111110341e6407114030308020444145080b0848003000380700000302504800381c5e1000c048680407103a51210701c00103014000e19603c008a02400c00d52180c80c001074040c00d031100501e00c008a0320001c1d054801507a0944802542a016030048801000306c104c1c08841580d00a24500b11050010060b00e450348a9401c6282020005014032005240c04c1d60144038800103494180c1d80941158034250303140605110040002405d840000180b0940e85d01941244482c10300074142844070f0189180700314207804111966100710340c240000003500c000d1400015000304000380406440d10340c2c9440304c254490780703a84c107618941c0c820032103020584642401c50b8040c82d0103a030f4441c500d0344a6159140360058041c0030002840080008011440c103140310112101c4008080c00c0d03c0b030380c1c0d504005080c0b600d440c1e8050100b01c00d03000c80310704111001000f400010b110701c80c2000150811b800700c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 441210800 1250 441209550 441209563
    0x71b080607050406110a020405180c1e3109170310030308040515070306140a0b0d111b0d1e0203040902030414011125020d110d1b0314 59
    0x16804250b082105000702440b50700742c01c91505480080304d203074009035800b150440f03401301c2d007d00042042031401140c4035801d010746002202d0440b030750101002200b401c0c44140c80400c0286101c1d072808282403010b4090022507104400640144401800728503030305030060040d1100403209000015072820b1416441d2003030701c1c081d00241c180d203021581156010b0342c9101c400382003501c940c070840405100708480d05c02d06521030911940d01180140c074004000c030034004007070101441000c00e008107104151040e03081c1c44440e82005004500c0b43e04011f8044040c0c811802807100c0c8032050883e50703811000018074003003003c0195841b503680c60490070748410556082c41c030480050304108810040100960013854115000d0020b07801e6070000d001c0c00c9401c460040c20354183c0a10042a8084100039844526013411030340c021024a0848035800a079030241d0009009003c0038004401030f00e130b0b46440d0240b081c5244d00a00c10b005003c20781284050a258a00c0100c80b443c8000c008441442c4020400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 441212050 1250 441210800 441210811
    0x3070e1009060308032206020a0f0809033402030708010b09061203030a090204020c0d0c0c080114190608060c0403150209060a0f021f0603110307060c0b0408040308071b0806 76
    0x81400e40e1921070800c00c1b00b0f0700c0403028100040e1303400408400f04400340b000b80007115107520380d80b1030b80c00300c40c0c0c004c3e10181c80281424000e0f0414020304403c101c034070140420341894040300d007117142104460f03032901c400c5c1c00e803010703402d841142e2000c40c0d5082e0540c0015102d4034112030203c990354556041190703903400c442d513401990300309002107002c100c100c0c0c001600c054401040903091078903910714146003420003d03c800000d040145150148504030070310901401543c0000e009010541814000c0b10030042d11041e054142411128041c480717070381c055400f030004202600c0a83c141075000002d01e41050000391084540c0310441e00460425108440f00610f0107020b45060240410707090307520700940b214400a6004d520810300e29040008515407604814640000f082804c5090000c03840ba0089039042c080d510410f424030059800c1100302240a50011440f0f0250b0361380d03d490907250040d54402851075101040d034104108901a040740d011584081c044e8090b59240d0f0389580e110742c240c41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 441213300 1250 441212050 441212063
    0xf07080a0602070f210f0908070317040902030f2401091202180a1a090601140a12050106050c0d021515041404080a080c0c15060f03070e10090603 64
    0xe40c030300003070150307009071030b85901640002c46000481d440b090b0603000000201c0040221468075a240b0640140d0403208040c4c07189000b0001c2424614410355074801ca010240034045900404100e003030409003220060300da601020340d201d04108868043c01d5905442000841290140030320005908482e84001c07180160764900041c0e24040b032840c81612003100c26a0040790f0a0301044c0d4250f040c42c01c06000d008021400281d01c0c01510342121441100024540700702180c4080c055540c0c0e000d0182d400440c0d14a4100c0d5540c0840d240665000501e403004010690600000241450b0071401400c80307030130313600b00340d4100425511080762910802c00c04090510414400301340404034881d030791070b520f0001400028449200e030b211202c9030041140e007214011000100d0010140c1d00004442c0c00000c10081c81c1e042401d0203c2c500d4035048040001c02d80443d01c4000517410741e0380d040b50410f0312403001e0b003540c070410340b1040c1031a0244000c0b64031035000050108001410031051061004498002c02d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 441214550 1250 441213300 441213313
    0x3060c03091507020a0f1104240b031317070627060c050d06030803060a0b040e0c0702150c010f0510050609040504030903081201030209070f051209030c011406030f0708 74
    0x402c0040380c0c20041c04410452049040c1c00d80041c1107200d5140d041d42c00344480d500e81405000802040d01c40c001c201c0c080620012000400c55019014140207452030707840100d49a07524401041c03140260150044d203207052884108011030380b440001d027800e40c0509001c1c042a07007001041c2528900d04000f985d00c444400111a000c82d105512808407400d1600d0704501e001a0011111706480e0b26401c107903940c1c1400000c0c0301d0980791010b80e0000400e0100005400d16184c200c0ca00d48541d0010000000c02d080011448119514181124050024214202e454100c040d1040d802003400207219040d03180307050f011400281d1000214400c9440080000e132902c1c06000c00c3c40702a040140089082c0720503000040001b0b80c0ca40060600460180c450200d20f41c55030040003401c25000c1c1c604400e01c104602581d91085c0d002040700c0b0022002140b941c51070303c0794032029207180724084a51156510b40390101030881400c400140c052403080341110107980b800030300385484180b9031045d02803d50205 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 441215800 1250 441214550 441214573
    0xc03040b041104110a050d0f0c090621020315040b030106081908040b0324040b09180c03011b1d010f0809031c02040305011401080c060d0209030a03090503060c0309 72
    0x110501e6800e480b0103440400c10f0b018903083d40344180c00403d100da02007180801c9000c104100351003001b626100711101841108145031016100710220301a0f001084603031040014141e60b5070302400100d90b10307400210358900c0d000030b480035a0103028101c1445241401101c238018501400b6401c10358180700040d209031612058136442a4901c4402140c49160a020005841600e1805107200340004500003600d0580703403d4000016400000b0203111f60b181030500902c903251071010036030140088440b90741c00007007508003d1070b050504e0343c6030398190708040b0182506040d280003c40040540e0710380494041d41c1000c0100f14921786100d050018081c1290071880d04d11907082c09401c45110015240307402d0b00c2490b00004420b0300321070301c00a43d40000c1e04204214013445215904501303005501c0e00c03035041c01d000549544280c80110301c0307041d011400800755910b5604403031559500a0848140c1c00507807401503c150b00c42c2c03003414400e004030000100311484120481c3d00c01d500b45000b520090404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 441217050 1250 441215800 441215813
    0x40c0503070906090b10120e0c040903020d12060614180a090f0b060c0a030f14030901021306020105100621020d090b060d030503061005070b04031106100e24030604030e0102060c03040b04 82
    0x24040d00f0043c0741f00781a4075a01074ac403035100b414190390003680640417074000b807140a000760390101c0d503501c00c16150410401051341d000c45502481c45900b080540d0311640b00200b0f50400c001201240e510000e480c9001600940c0ea500498500006103000d000340e210300020003000d03002d401c00181c00c40c0c0101106c840040c0c0714102a0b252040641070038880185094a9040d16800444605140ba0f60018880047c150014101002481e0910080c4031078504205184920841842000d00b88418221082c0309205c1da02c1480b042c40c41000021500c40500e41c2900014040f40d50050b41c2011080c00800da1a00f0320b442006800358068581a10711b40340d050030b1003000749849080708100302017400014005040e200981340203030300070341d501d0600941d1070091b0350030300901904502540c080c401e0304122114944501a50080c4e0380a0202d11020b492842c25030340235004108250b25010b0807080004040e00030381c000b0081c14081e4221009565a00e001210381e11058402403c2c907140c050000b03000440703 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 441218300 1250 441217050 441217061
    0x18060402090406031202010e06010f08030a03110c030a02330c18060f0309010b0f0a030b0910021b060606031b03130203030c010b030f061e040c0503070906090b1012 72
    0x24000158443c0d417034580000c1580070590000060b51035041c0360b1840ea00400440b4090704124a190701664508040c01e9a00e108481d1f01105141d12200358507d402c1c0d1280c282d80301c1000c4c03242901d648450500d0000d4a86580b000c00c0c419040c52846524441d8a0b004542c040d400708464100000c1d81b2901d5003600990031401c4079951130301c111030814656403240d0b000390107000007242d13459403a0304042c0c180341c0c25a01c5a20889002d8a04180c0e160480d6482d0741c50b94007225001070f990081a15074009003410301000f1002e003004a4000590781020310607148010200000c0d18052342d1950311502c0c204403c920090f21401640903d040da00550b200503c0001c2d900280700729075040e115006940480c9c01c42e0080350b2441d9440c1d560380c44001e40760406109001001d03000401070a071a1828606004403a045038210402d000f03c020b0014017000000c41c0c030f907070144c9002804c60f600c40d0b943d80c000c0e20107040c00d40501c2d42540e050540440340c0341030050400d4031150054407903400e202d00360070b8002c00601 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 441219550 1250 441218300 441218317
    0x503030a0c050a0c0e272a03070e01030c0b07022b14030406030c0c021008060a0f0902030a0c17150a05060c0304150c0c0303081b1603020c18060402 65
    0x40c800e00c6000050180c40341400a0840e20400d030117900e0304202d100c0315011401003620392001d000100720720302100860121345254014025040382c0c0c440c811080d8654040c03441080d090300c43c001d0049250b44201a00c0c1e41207034810f15204842945951a5090501035100025000341179540703060824920111509040104c0c0440341000304110789a41ca403503400c4506585054100203001d21440303506002c0c1d440b4200745414061000001a40851801130f410304101c0c0400007280080344044c1d0314401e2500040c40d20b006e2410001c2d40b0b03811a200250300c182c81c1401d220349040030815005000340c42c00c004800c03001c4803240d055510000d8039410ba51205c0e0015500c0300201d0303400304003691f40c000074088803000e050003181c94a05002154000d80c2a042e500e5043c0650b000d10130001803010b00c00c543c25a036041ca000e50060702d0b01c030700340d861a036444010182d4032a00861154003541c580701500b14220f0013682110105c0700c01200b44200e00300c20440c00d07452146804e00044007410f0a800800e00039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 441220800 1250 441219550 441219553
    0xf05090a080d021b030d0606020706030c050403080a09030b0403080a1d0a15020d09061505060f0d020a0c06090b15150d1538030606090108090f0111091203040503030a0c05 75
    0x509100f2038685c1994041001203900c50740e640d030140081c0303504000a10140645060030461240c02340400340c07150055102c000e12505002451000e1240700351a0800115442503520b040e0b420186001f400c021011a000100d00303140c0034214480302202014151960b6141340078000d074403aa40c45252405040084141801e9020094064458003c1c03286408550254800164034000711029a01800300b5520480c0300301018001015140b454500321001002032030401070390b802c0307240e2080d100d0061800010f80b02c0c0b403403d10080280440c0f500b46610071614200450341c481c551004210089a10004042d2031010a01006440c28801e0b131008848200420000c401c065480410030000070941d0440c20000004002e180c0701100b80f48410b00c025100b109005080d89000030100701140280c0503c103041003580c00100385540c0b0b0500901054410f0354000340045115046102c10980c030509106004142106140d1064100807080d6010340300010059072500c42d1403501100d85120084060303655 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 441222050 1250 441220800 441220837
    0xd0308150a031407080c1512130f06020703030f1401120201140a091502030a0507060f0e0a06230103020d0b061f09091113171905010f05090a080d02 65
    0x4500d10503015014183e41c10010003529061584807401d0140b481d0a443c0500040940310b10001d6050041d00c103030502049800b10641d86400209400c2c0c0144403010b06103c0f210044241805016002025294040c0c0c50502c00d41030158280400c88203500054031131034030074400504c1110b1f0202d004102c00d900501d080407802c00d00e0029400c8982c414030400005c5403089104010f080a03040028611014500107175040010064010f4400d1080c414001c0c00c4a6842c480840d0001855128040c00381a40d01100c0c410b615074a4030200070b00d28103206880440b070010003144190200300c00c1c681660790152102c003c3d5a41a80c510780182d02c058000c66010341148044001a0a200b4a180c01e040442c1c0e170742c4919030302e00000c0c2411a0150241d888100c1820024102031010724140f100485d29101e1480410280315030b6090304216208504280062004082c1420710005410000300b0654082082244c4c4e1a03005401c2c1da10800c20300014001030050045020702e00a5901800000800780b00c50502c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 441223300 1250 441222050 441222053
    0x30210140d06080f0708030f0342120309092203091a0f1b010216080702180103051f060905010e0712020408120f131706060d0308150a03 60
    0x4a400c482074800d0150b5441c03608003e031040800094607400300443c042e201650605042580300d128000969001c1c080000c045803c2030f403d401105142e02512000c41c07240c488400a070780d9081002c0c8200110f0326900706146a107494603021950070307a07264400330361910400009010366010000c11200c10b82c600300014000d07070030015460401152207130740d650701e0090415001d0f040c0080c0701c412084440c10240a186032031110b0f03404407844468440400c81d40303402c9038844240a4480c00020104412000301c000302080380a1001c1c0004038800c0702e420402e4280540901460402441701802c290b01500510480100d1058460013b07030501d2001b043c1d484c0c80e13031a0201910000e074007456030002030604101f002a840f01100075103c050759802d5140c180780079140d596503c01c18030540b41d00300001034800c0140b00300b842115031450000003054010743c1e6072004646e980d010007000c0d0300b1034000d02000401a141060b544050a0b88c15260300909441c0c0c25080d0005800c180c000035045078441c0c40210 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 441224550 1250 441223300 441223337
    0xc05011b061e0203090d0912020105180f0a080106142e05070501050c03040b06030c0127090c03020c0f120301030326010803130f0b0d0c140d020909011e030210 70
    0x10b05c290044401002022841140142880d010354040b040704da02c0880800c0050383d00c8002c8812940c40448008230000c0280e0005583c4010062203d500640402d000240c00c04c040d0400c10484213100c061007500030121007804658003030240b54084070701d0300c1061501842010a0000781e4003003640303081401c00c030803665520b003160001d461819030110040100030410680010055000d601500a480345003c0c800003e0400c034190700740280e01d408012100300c980180d220340c103802841001c2c014040c214013004064001d6001c407090f494035014403011342c1160b48000950034880382829181d649107078a0f42c0c4085034007404550300006001c80740354180303440d04260301800d8060301240f8040c0d0382d11500c1d22840d6040b0362032a408045420b101120420881034148141e4105822042c00031940c602e02c65001c84500300d8030f08010301c00d600003181c4d40c1400030356940608114102130701c1e40089a601c43d401d16403924012481c01000c1040300c4400e00040c1810b401d0408214601c3c00e00105400b411031000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 441225800 1250 441224550 441224557
    0x703063c03150501090b0d11010e130219092702090a0312022b020613020f0901030b07030f0209030d030b0310020a08040519120c1b030803040c05011b061e02 69
    0x3940101c1c0c940006205500191041b608002412202070398808903540c2c416030a1a04c0f51100c50601c42641e2981d0442c0e2a100a88005840c0c8070704119a83d12030103480c084c140d00c400209800080c05144040b032001d0103000000007030a40030b180980d41f55113032030b10000a903100e011a250400f085000c0080061440b0403810b82c1e00d0450b030041d01c0146483c1c24130031841c052001e0514040070005070f10315280d0b074011038265080030620605900100380c6001041015541c160716680061541000105103d46090264002d040a64051281d00c0c001c01241e001d80c001c40141702c0d0315400c42c1040ca101030340664852855108060f095401500000b0100c004a030051600c55000c00c0229082108001c41448110180303601180d6448409295032180c56000c0d418200c0c0b5010712918000e001e040c000829110881d020705000003503502034891520600e160001c1d00d00303c40c601c0c03040c9804240c943c014048003100b8040ac080748490552180c8420b0003400b00d01001480300300c0c0e003000c030b100c8002250005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 441227050 1250 441225800 441225833
    0x18031507020c0405071d040f060b03090d0305070201091703041401050702012a0c0b0c0c0109031119050d0c0c0e070504060f0e0919020c010e01050703063c03 69
    0x74000300d040602c280825944002d01c0f480420404d9010920600c9402c40d40070018202034800140e41d405025420004118580000a05001c003208100405200290450040c0b42c1586c003840682c45004041e8207a070803160000b090481e500e0350410a000420024562003400b84a4000c0d05e000024210b900312001038807680b005035102c0c102c10811800388220070a03440030002c8415100c980e40c60000304a03010030786008203150b4855020444802c122025628003c440c24002c200f42c0e09a4a4054512104800c40c09024050b08811035550445220401025500304004e07013500100903c6c1183e1090342c202084600206a000c0824000354990100c1c0c810038894840301d90300d60924038050f01c2c550f040c092075400c21480c1c1c800d5003001c2d111072402c5500104111060304000c01c002400714080d0084142c0d0718102e602e01516034840d220150481802120b090714100616074444016021ba410f203000d141150f8076071107541d62100c40311070701c440300c03041c484518680003161030750780d03000078110511035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 441228300 1250 441227050 441227053
    0x90a05091f0312020d020f06010509130b09030a2a020402090a1208040e0c0a0f030207080403051f05130209040209060d0215040312030911040c051c05100503060c1803150702 76
    0x3c40b99010008540c4c421400e000400d030032a40d0b4020155140c0e4140100c901405000e80170030345130303c500305121034450780c008040201442c10103a510390f2500f00b08550400070b01c0107081401030494070703910781603486985454130341651116002d1001940c000320705180c2241c440c9000103112104101905481c52045500a41d102e242258a0403075407070160900c0d6180c0001c106401d2069041805480a907065060140c6c4810301c0b400c000b03505015a82c80905117001c0c50188040038251280d41c460500241d07a420845a210307440705a504e040422002034201480101280152922000165014100038101541c2c0c801a5000c40c0194a9035030581451110115044c0101700009501000b00c2e003540c9001c01c1680340c1074550504400010407000c1c0a10740c3c070f001042d8001d114604460a05c20311110800b2000c2c8440e00003c001c140445481c42d86240c0a9004140f030700c0c012030303198005d000c0d581016040402824800081d0307042c0d449801d40c1482681d001207900026001d2282c4105103d40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 441229550 1250 441228300 441228323
    0x408030910020105010620011d031e16030c050a0819030501051906050a110303160905060a081f050d11030c0907081f050a15090b090a05091f03 63
    0x1410701c001e00d080100e426003503904000c01800100d9014655490740003809548400300c1c1214080103004000566031010304a11214003403040036000030040518a07690404045201d01c0c40155108500403441c400880490460b640c03400711780720307141c03d418941c000c0099808009060741d84111540c04803240003003400c103100c040c404460b050300c5554010328080d07480c61072961003400302c841c20320428000c43d0700384031010079081c1081c0e210314110b042d04200384040301e130b4074100410040c00c074151042011000441c10340e80410035040140584080c02c40a40341c0840320740707034403072061008422110360035409c05007040300048030f43e55280d030301e10468003804040030403584030020306081162850032140241480c4003846281a8000c40c41039010300080042c9001d2103004104080b02e01e40c0390710140c3d020200d0000858000c100b15901a400c40e180d440799410030b41d480c090200c0c50b000d0300c2c413004e500006c0241c0401c814202030280903844020138070000c0b9620b50320510b11101c10b45a80041e40e40c1800350 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 441230800 1250 441229550 441229567
    0x150a0206040c170d0804030e0301090507050415050609101701090f180308070e0a05090a020309160303050708030a06030204020c070603060503030c2505030f030a1e0509150f040803 79
    0x12541001070080d4402444040e002d04507041d039101482a8044d0800038040b00040505100b802c2e41d03210710303c1c010001e20036401d007810440e075a0304903805120321403450304884500e82c07001160540201c40010b4801410a600303d0300300065040364041d64010300000c1094404100140301c0a18041c1c0114030000556034072100300c1d0411200c03468a526440c0c0302c2c0161100101e0b80000040d45c1c031201d145402c800c564417040100303462144907445140c100e003001c4180101000740d5006184500401400c0705c02d0b00b2803030700b4001341c001410300c00038000c00c80401594003c5076140c401942e01043c05400803580c07503500c0e400b10341241d00c14100303001309070481d0405100709640340c082c420080c0700807001141001c0c01000003035280c48101d40c99980341c400a610310001a00d4405040c4000c00c00201a00c5502c0541404681c50398030a040c0c500014601402c20140d100c40d9011918583e0302c01c0e510581022204414003c070844901c03803070040c600060003403410040030b0380300030401b90030805c02031a00d41991 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 441232050 1250 441230800 441230813
    0x13031203021e04140904021504060302070b0f0601171e01091d010506130f0e030a0507060b1005040e090c031b13110324090717130b06040209150a020604 67
    0x1000100950402d0400040100644051340300226441c101c480325181e031101e10004d00001c1c40c2c100c2900820f40d010130001904d5426a01500481b80640c084019079030f103800820148000440d0070700d001c184210000f00d0024000310801da800325894010340e038030848042c81220b10070001d030b00c0300d80c0c225112030489150114849100031440407110090005003000d90000c0c51040035802c0080d1816621480103c030f12409070820783c0c4510884007681d9503056120340003441684040030a440301c03401c2c440901e00909003024902e2000700c107035407450700b403e040a11501c0b100002412024030340c4a10003020344150707001d00507240c20000185090f00b080d0241000d0107001188404008102c600d80b0382050254a00c2e40c003200d03480124680607268160110441c80c121a40028005030003041c45030811500ca030308a1100708852440702000c0a0568900340308503940b9181a00081034400c2e0440855000c0c18150080c00c11098020160b0300ca045282850505035084109041c006901c58414072062100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 441233300 1250 441232050 441232087
    0x501140718050f100207030602040905010509010602030903030f0a020a02031204080115030f02010309020102121207031a0307030201031d061504051807032915010210020a020c061303120302 83
    0x7a041c1181101d03034580000030340443c4210b00a1402118401410450548240407801c05542d00480441d11547c41e1807140000700400d0061070b000751000c0700045420790001040e030f031025500400840c40c1c4600580d1000b5950030103071524003544100080c407001603405000c2c1546002048880d6521a4581b0312a0350030f5941d00503001d82c01d964000710030300c046444141008030075602070901040050a500c0101d14101400714100d9140c48089003140400c89841101400b8520a60f0140032154840d400c4406c0c1b5001003840c1e6030325603c040390400055000303400414207041c0741004000300703c0044124070b0070040c4c21210352000c2e00074125403801c05d18041c89903d802c0aa901d01c841108140b04208030760b40d1083e40400f6042418042001c1e04a0f0700000f10008180ba0781114000c80f41003c0701c58540009040c00391078058050002e04510411301407083d05d100384901c1d4001d0802848030000c2c891140d03c010b9441030b00800e84640440441c1090012401c0d660312941c006a550b0025000072441c1c41 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 441234550 1250 441233300 441233327
    0x40501090605130c110304030501060305330606040515070c120c03031b06020705010f0f20091c050610050d0b0109050613051303090902030601050318010905011407 72
    0x1e00d820424481ca489a00004000810000000441c06062042521415107a004410700b500c03001801104011064001d034048a03c41d82c1101c00131480203501310130303603244503000000800ca01000702d00300da40d209582c0c98200030090640c0f8a4261614003052010244048000b04031000040b00401c1110050410008103c6600d84100c0002941e403080ca003906248030240c20403101445456010800245620080340d2250085558407120310340540600005400703c0030b4149810580002d050060042c080402c5c01d0400501c20040d0b03540902c041504181525034124002d120034115000389000c40c052068003500040420380b40603010140e88048641005004990b1f1b881c903c400550503002090550b4103007074002c80c0643e00c1c0000b00d0a0000840584c201d03071810103003400007504d00050582c0038075002c1c0ea41e6100f801c0d10784604105a1005441150004070100001403005141c4188441203074094000810300c0c800c0c64650b6070a480a000030300b0141005201800791083d04000c615034990b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 441235800 1250 441234550 441234569
    0x52821051b10180b070c03050d0201051005040903031107080909130b011208070c03140c04022809080102040f090506031c080c0d0e030c0c060c0303010605090a0905070806040501 78
    0x944030021038000c4102000090921102180a04034584403070340c030f0070140482e984407940740e2016041000c2c0c42c103410f21058909004070915141000e106010740e610444a0704ac03280d241500d03040511004001d6a1010f80816545594800e0058401030040c04c40c21300903456281c13250321030010081140d0014008200305040442214009118560030394110380541c510007050f07c0741410031034007602c200700004120144508010040040604100000b05840d104885207520100b041c0422446131441d10410071004825046404102c02d440c400740444a103802003006982c0d070440e0307080e41c109810100c0c6c22100748030288840381c450301c2050303407060080340106800d0a151042c80510558918aa4200502c00300002d071001c3d490000c40c2d240c0071700341100f081000362601d9a50740301d070820564402d4500511805860b14074022060740d404082c0c0300e01544c40e5034648141903072190703c50220a6040341d01070340b0005030b0703011030310419200310281c0d01c4240e43c2e49081300400c811204140c02c10100c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 441237050 1250 441235800 441235843
    0x102010b0303130b0f190f1b05120a020f0a0803190513110f360f1602011d0606010e12030a0e031608240105282105 51
    0x14940c41250300400c584c070698a241d82c8100e90028410144102d0f002003541c5800107025841c0075510119a04200e086540d4000400c800038100303004000e80307003c0c050a0b9601c0307000c03103031503000c0d03000014605d101c51801150701d40710350684403a0900440390810f07504503001000308610380e51402e25920710380304103a204000d40e240c8448080e640c294010f10241000070b207454514829129140848141031000703018850140a00004486501e451030340121800c1c21586100c1034995001c0e2514080c81c104662008165a048c0c0e8010b031741400846900115900d5000b00c080324030085c1480caa180c3d04000103009030345800c4001400c45607818048502401440612204080005c800e44020703900d0303413400030054140540000d18115810183d0184041c4110340060100c0c000a0214024244070040701d907240e031034010034582034a0134410b464125007a00c1d5202a1608186ca0032141f008a20780c40701c00c02a207070030244024005821628a04440740361012007030050810500d2091441c01d541d2403030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 441238300 1250 441237050 441237067
    0x20f03030712090204090606080109060b06090604030210050f0f0301080c01110d0e0a030213020715180201080606190e010315080a0b06120f030a03050711150a020d060909020102010b0303 82
    0x220421098000c2c40b090303035414810119611a00400c10664014506208140c0c45110311802410b009a084607020310b051125100c80c10709400b51038030005c00601d00c6092518680a0004400c61106590104901000343c01020300d16080075007003031518864000c7e10307507042c004118036200b0100403190520102c3c2031400c0d07070580000750641001d1103914004001602c0380000c10ba811030b0b16003000354000d83c030b0407a040340c845107a03015005050081803800f81488103070700440119103501d11109000da60072510800554095440190000d1000d0409480c2c117a40c034040400075141d4644460002d446d035062911b8035a403601031807c40341c400006041d20b01d031810301ea1680c3c4c1d144002d801024100703048000384242d91804c6004086d8405402078524110b400d0481548985c03001ca4040042842c06001c905644d01c604949140c2541e00f400901d100c002c0c0426800c5c0248006065030011a000c02c181c14000c0c40c0350150200810080340080313441e1103d40300180c20b4847d03010700c89001e0342c0144100e44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 441239550 1250 441238300 441238307
    0x9020111030c0714030c030712020f180708130b2401111c170c030618090a021e0a08030c0f031306050904020f070f050105101202091005091006020f030307 68
    0x822213101c03a5860542000f010007080c2004a6031030165454041c506001415441e90305040b011680300300c3c1d021081101980c01c002251514045240007031101c040020315884c054a4159004802002c0c2000030700120b17650864110400c840d0740c640300c14218081100f0051004481c00948000d09101300800e16a210f031680d1841190051162082145a00c080e1140240c1f1200c80c00c0c111030420880b0b030319098015000170b17481030380c11500800c407848540a01400c0360700c0d640c0c012600000500003180881c1c0803c900c2d10007140100d40c0c1031b104203001c555550340340440e1f94010100300c4003a40d01c540640016034101804203144120350b0300200075030a125082c10803c401524900e0810a854101401c00310b0b000340140c0d85850481c41000800c4003e1041c0c40329200c01c1a0f11550091006030755076803a02c905a07200f0300c64070345895885042074005181c10280c07141d200182080c1d0807a0942d072900020413510060315050303004144602c0c18029151705000741301ca80003045000b1481c0d400c1c40c48004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 441240800 1250 441239550 441239563
    0x7080d020a061109040c0f090503031c05041b150201110a1b03030207050613020f01020d050315040b1507031b0f0b0702030d0e01020417060c090603040804081009020111030c 76
    0x10030300c503659800030141002a070700341d404c0d07a03d02a1042041c0407901c58060706d0119000c01d2080800d600150000d040e00e40001102c5007100940c003114000003111035a20041c08010340304451402001e40c0340480c01c0052414040100003e200c1008860075202c00642140c0f150450294210030400680c803503607401801c000b81d4060002410031806401d414203e0080c000e854004295001d8a018002c045a486040c83c9486000b100c0c0c0900f8507034008016659000c0d400010004544144000741e00008100c1503404900400f0300046540c6040300002070345c0c0002031031001c10074040401c9480516034007840d20b00c07210362351841000c0d444a10f51550790305012000710007403509200000003403a031803090090383c14849a10205108010459800d1030207504207004e8907442442019201c0c420f0000042e1a901035401d42d0200d1380340c034a010003480314650004105540b20f100c10480058680d07020403145040189503040065451042c0c80010701251039000401c2441c6e0052210b00242480842d50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 441242050 1250 441240800 441240803
    0x30714040e060f030f100c121b030213030b0405010c23040312200a200f0f0d0f0303140601050a080a05041103150a05070804050a1209090905010b0307080d020a 70
    0x180030f660240350000901d0301d0720010fa40f0003a80261503030000781c201d46030440c1d61215000e45500c1c501d4006000400c1c00c031045c086003198845040006224507a010b81c0c02400c20580801031151255180c1c2c842c0076180300c0c1942c00f00d400c1c1c1e555041c941c14480d4010f038201b6250b09841032810020802c01810000c1e130107075000c007800b5401100c45109a1600840c90150424091030b00804444030101545454580b074400c2600c1c5526144001d800e000d02507415012021b80080094088041d000c0c2030200380c0b02015070254106000c2c070000c50100304050141c45146101c3e030340209903400c01101c0c0007821704e00602483d05001041c02026800c5401c1048983c5c400f625120019959540d4106912007003010a0465014010701e0914500d1200520304248034442079401031105407074440c402c890807141110054000d030003c0e0580d100040d50406081111810745c82c1014019849a20140803244a00b100f00c9090b03654100708240d5040a0080700f00801c0880050319990041c0171380651110b410140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 441243300 1250 441242050 441242059
    0x120e0f060703020309130e10051003020d05030a110c030a1b0308041205010b030c09070810030b07110c0907090b03040503120106091409010f140117070c031404030f030e012003030714040e06 83
    0x1031400e03015041074000443ccc0082034400702c4107007414119260382c0103a03544800240c031442d000301c1000f4001460242c10308090001e00f900300031a01c0304155400c90312210f00515840700400000700740448090405000510b1191200301c00c036260060844d100071504a01a800041600d0b80994030080f407140e000f401820860500c0c0d0303030607681d8400100b0071340005061040450a00501c0b952044000000e28100002c86070a0030070070341001040f11046860760002800740f9014801d0341610400782d50024800c4c01148d052258201c10320114000980140c000111030300001c03c000788010002c402440301c02e031800c0e042541011040c2405401c0c0d8003860702c002d00319035121000f50348a8101c05106003030380000b002030350030702140041001030207403001d80000700c1c4501d000c500708a26034100d4040343da100000c03203c18130070b83e54103481008900c11400c0c140081210941590215441401200404440516924641007101800c0001c80b00341055512a00344030500410300b19608040d08200d040f038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 441244550 1250 441243300 441243311
    0x405030301120f0f0b1b04030209040816062a03021306050c150c0c010e03040b190e030303160801080a0f080f0913020a0e010309120e0f060703020309130e10 69
    0x4151442c009882d500406003109600b4210038082030501c0b40d8001c0190058024198072a51034146e1a4025404040d600c076110402050010395560024012a101d000c401d12459509480f040110f0304400700c0354801c0d82c0c1c020b5680d003650140b5501e0303458007101c81c1411401d05102c441d07011700031709007401000180b100008071454038400400c110130441c010040c14100a141c98500f036032950304010b0741e0300340660a054441502410100c00d403010341d070001c40841e04205010190055580c8800d90700070910800c00368148081c2c030b00303100031403007403103039900b08101000e40100042071004168049040ca420031056800003071464484d8000c15500f0004031519003080c684296080d20419801e5a407280d03288250101d18441034016000c6002c0688030740001030748500c0150140c9441c10002803001d608040d052400a00444940440210103086005070890070b402059255202c1c0b181135016038004038400c600c514041c2c944100b40c402c4a801400b490b1107178a0015034800c1c1c44045000c035542c950 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 441245800 1250 441244550 441244553
    0x9040b2707030e01020c030d0c0c0f0b22050c030d020c06041703090a06090801150f0b1c020d0b190f0303111002040e0a0f0b060a0e0f030a05070f0e040503030112 71
    0xe400000002d07504000071503960661b42500e6075207601c20250f4505580c01c1841411031039000d034000340d098a4002c00c00c0b600064840d038402c00c0d40c1070000d25041c6040d070011a2064082c0e9004942c0c41507510850043c0151040041054a8038521081c1141154006e010f07011003a00d400041d49c0442d00704a2440404542c0c0100e89410b6002d03a904280e0030801d4041c00040c4164800e60b0304d800c59071010002c0004819107140c107000e484207402003030458080040e041000408120042c01c3e61030002082c0c6040980d14420f21090342e20480720340c41c0d025142d81d01081c980c5440300305c2c0c00c60b2100190001c0145450980305809400c0703940f10260a1010b1407031280d1300340b101445014213a4102103021959161940c200e90311100094415030349441c0b07020356103220f8400a01c610600440000d00050501c078068508464543c0c400c024550000d0000ca08034a2589081005400d43c602c9940906010ba05102c5019120324155000901d002005800d01004c15000300032281910200a050000c00310503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 441247050 1250 441245800 441245807
    0x5250e0103020919170613080f12151003020c0a0b07020a0f0f0c060e1e01170a090308070f090909020105161214041a030402010c02030d02010209040b2707 68
    0x21440b4254012800e150003000300c411441109064544100e8020030103403103240c040d943c0350421110070031440507d002e1000490702102c054074540303245814803071805c000012001e40307040c8140e4a41c041c004a91403a1201071602d15200d440400341c1c3d2400b1400c000301c0748682c5684080815001c0d020152803000320b8075080c828009103200c1a0444035462090209240c0f03a0115240e0344016901c2c421a00707008a10b1a00c51603041c44181c0c0300521107810a400745112424080214850505020608540310a0000000490f07842024544000039004000c3d08000c4c0c0b1308000240303894200030f60101c03c40101070300041890141d8404440000c2c05450f9840107039103a2140b800351100320f0b0000700380c220070003903502c1e000c28801d4829230b2004410380b54002d150595005038050700002448201e18401d100e9280005584c0c024014234141400b0354007500031900f0040407000100040c0d400058101d0135003030600940070704d4441941c10b110030011034800b0b000880b09c21220a10081c62030310124003076521 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 441248300 1250 441247050 441247057
    0xf0606030203030c0f060a0b100f020f0a0807110312030a0513020402030a090302070602060610030f0204090e0f0c0a05060304060f0f02040f1701150626011805250e010302 75
    0x340034003220760b13441260001666440002d490801c0c5841160300240c0001c5e0503000d00991544082c01e09049150074400641e40071808142c00c80440c4a491516009032201f00441da05d624000e845003540c43c1081d080600010801d501400c5c00b81d441820b20140f91140e542c1103035032101c18004002041d4840c0c0306105c6511255120103503005c0c0c004400d105d54030300c0c9540860348151003a000c07100002e075140000c0c0c2e210301d41155103540c070001c02d512061030140281c006961b80465400d0041c54991034000700000c488581524030b00239400503580d0400780f003080040a068440480351401ea1602d008000b4655200040004110701c2d02c501c0f4440c44800e16800034449403424580c10b548580e1201c20640303406c04244103061802c407032800700c000030040610540760b0096025159450650600f02e0503203000041102c9807196402c80d480400d40303d0070108545010309041d24100403880050725a810540307001519149a00c6660382c2e002007000b45842d03800c0d00052050412810003000500182d00901 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 441249550 1250 441248300 441248303
    0x160503030f0108060a0b06090f030a0c03080a11010218011b0204110306010210050f15031608030a03050c281403040f050d02060702210c0f210a0503040f060603 70
    0x84044140a403107062044440d0607255034100f00c81c200d0351075812a100783c5030628032403034020408100146050902003801210002c0140440e40b0102c00e40d41c603685070007625401a60044000304004138032a90007550035109411440c000d508000580700e0f1444020400f010311350603c03d00b43c0313a807070f00c845840031181d40194000f001040103a4114117a10078a40c821991136006000f090710010f040d015510495005145480c070400c00359442d9421b1903510b0f0800e10745698584103100090b02080ea42d03610800c09000700601031a15000d9461002c0c0c15110040c0031342004030000e000f80c0841030580c182952a0000300c0946150140d12040c0599105100605607081101c00004100030722080030200c00120b80314200701d42c03021303c001404a86071003058400c580160081701c55240700c0711101441e031200100740c103505c625140643c28007900c6e00b40e0304030030230056820886000c0c5c2c8210740c0c40c1004440c4003003403a8003403412041d5900180703d0300c00148020100030b0501480381c1840402c0d80042c3c00b81d0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 441250800 1250 441249550 441249553
    0x140118083c010c0801120c03141203040303090219080a0b0c130906081204050604060c030e06030a0c110607050901030509070302030a030801032d0f060b03120706151202061605 77
    0x2190900158041d091503c41d0343d000c10300d180700002e0314241c882d1216088036042107405c2541d50443c0c0d2080d29002d2440203002c001e2090b00902401850f6400056028a1103034400240540003441840803130030481c0c1e85203107541d0030300c8010400d00f030000c070b00c410119500c0f101a031510703034980180020500461004065072180c10001103036904880c3c0c03021055820314000c64411103080320400d2043d1166000d125040703034003480100a06409040c0030034401c1d00c43e05140c0d04101303049010170342c5900222003500c00c03161600da801421a4200f04000b120008540103080d562030325820203401c0c1c3c49202400b90401d5038540000318002c000f44540e0f40078690060a0b1a601116400c009109441c01e0109448280f083d41340e801c80c1030314200d0745201480c840e03801010f540c0c001c5d4840c00c080d40041c110641d60651100600c80c016502880140000c0e10710340d1005403204443d0034940106e0b600b4a88148031070944e001c1c00c0c0030714403407a040451580c0e8101d84140d03a5a4140081c00044540e015008009 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 441252050 1250 441250800 441250903
    0x160c18020c0601090501061704060618021b06040b180a050604060e10090201021c0e041b0f0207030209010e2a1c0203061302030c07080414011808 64
    0x20155400501da00c190000071034206988446030001243c40c20b01c202c10220382d2580c0b000001d1071008885035403050003014000f840e1035503204400600c120f612503400c040b590000b01111a01d8501218610245820f0010003a41c40c013981c4540f5840409481018908040c0700001c443c035800b04814035072181c0c04000d481e01410b092901030060641d601d60601070340510011a0740d160b680344211018690142d00030042400700a05803a84c1c00d1404c40a1020071403042101c05d880e845038084c005013041c0e40e10720211680000a030080070720080c402283c003150041d05040016a650503000b50660728201006907203070300c50a0014170304c103011690f200315000d020a400c01f114640784015000c03240a40b000c0602200455007284101e1004440f09540038040104003807400d007c50703010310b6000c81c032049420b281c100b0780d0303c51404641040c0c0c0181c548250000c0c0f1100d065034000c401304900c224070358642007124146000c4548481003403c014084c03100c0b00500c801e800c82c0c03d2126080c92104507154200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 441253300 1250 441252050 441252089
    0xe180a060b0108010b0a170c210603060a02070c1403030910030603110904120c141b040f0e06071407020d120f0e13110d2d0908160c 58
    0x1500d80d0401c9075011074601400012851012400c80300f0500d01ca80d03400e100c1c20213030120340e00500c001914000d40700d0414015510041c10005c0150014004260400a11301d13082040520b08200140a581300c54018010800003440e03100801042e100c8811041030220b80781c00c0824658001c0036074040e842076850201c841e07250740680c080760a42e03002d1b40030481030001c0340c1c0c2071290454040c1c40c010102c404201e800c207440c3d032144d8a804003081c0b0503c10a9502c0014064080c80c0482021100e1502d031200d0441d02030a01d40351083c0b039045003034810148618801c01e103180d500e40c50001d00540a02030f82d00000986403000004481d1000d5008040074880c0490b81003a83e0704400b4131002d00c0c0071030306000d90100a1801868060320080005110800c403012600700103014140d0b8100c0f11103404000d00400341445454080d007545407514031045001044001403070042c0b00011a40554503501e00f07100c1801040b5102c007150155804d50100c8030301e4000d00e01d005010b01c8015480b401c20301d1041c4103801e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 441254550 1250 441253300 441253313
    0x1c0207061e0b0402191d040e0706110a0b070c0f080d05070807080105091501020f0f0f101e0221070e0f0415050108071206120c090203060a0e180a 64
    0x441e560344552081000341c4504060208922031010b20078100d1107003074210b0140ea03106440340d5840119000c991108001d01601040550300792044908154110110500170507a00c01c0051070000601d500508020761315449180c504e000143c240420494181c2c0f0580610071010705007542e0552010b882c0381e4440240f00000000c00c41500d49900082110001c559418841d405407410390708024001c00c0580c44a000c2c0d4002034681680007030560007a1420000c91210601103042c0721242100a800c40c0103103500e61905000b000862501950700d8004138450b2449082c0d01c096200c0000c0704010703607401084010a490144500e2071918540c401020895a254040303050040b0b4031050750307202c12034460740303003000b0607110481d141c50b02d084180403003002039620680310160091304604181881000d0002d2903c203440d110740240300107038280743d600c1d0200400001d08500920b54602c00b10304604000e0000303440c06099108a107400303442c81f40400d840e42550751403a445d413129501280c0c140c022a05e00345 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 441255800 1250 441254550 441254591
    0xa150c020108010e09121c0609090c05060304050601050f040b0303030406061701020909400c060504181a18060a0603050405030a0302160804080615060f1c020706 71
    0xc900007608100005501180e48000078000c0c803840340504894030038a251000b1680041080702c940d070015002450a40308030340b0a000190200030700c0880e000c091810100000701c5117600c80c40c0140b42c20420400402c00104805064403c00c4030aa4200303240310000030007520329202101e81c0341c0000000d00040000f2580180100d55411840b6202003031201c052908038011102415044800f2a0000303103106050002d0b01c883e410711040e00c003c50003c040e20000c52922088000c502090090b281c001072001342c030810401800355190040c60a81881c01c0404c200c2d002a500c3c0760f11540704d06090030000264195441141009001c0c03032244209500424580541036079000d0155642550109403a8424000c40e44a030303400c6030045241c1035100b0801c500035400008211040801014110000b6803944c0c000c10017411a80d00070f020341c0c28040d03101c42c00044d11480081c03040d9410410540901c20b8001078038004000200242e81c900c00c00b900e81c901038400d00d88028040b40c0f030124500140015140030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 441257050 1250 441255800 441255803
    0x10210050c09030d020c010c23030309031803070302010c030c02031f0207020a0b0313020607140307060c02010c0809070915080115080d050a21020d052502070b04090b0a150c 76
    0x21543c1401c0205011703a251031080b442d940c001900d6962000100e125006102e00310a10804150b0f04404079038111811a0000c2d00c1e0342c501c6820000c1c0a2140300080c0c2c01040201c08110050160141303164000f038180c904031100201131000760f030509010f540d01400341490b0b00747c4402c240000d0000d08425040290b0115404901c100890070307002c10590000c170b044da886000d840c2c2182c442d001c00340c1c00300112900b02c03030b5044801101d0070910202092050021340a0184a441d0110702602c051078043c2c00d403548400d40e1010400c404040045400300042e59204031140700800041408804c00f050410f800280c00403a1150300b801e02d812440c04002c122801142c1d80301060317030b45039000600c04695910503d00c0c2d00c8002120103280450441800514003007144a41000519040080c400700065500880d14645c48039078400c1d6542c0b03400e0400c2e0606050004c03d06c00740404500744278201070580194013803018580e6480e4080301c03032134031030011707150240a00d441008608611120000c1020103080d10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 441258300 1250 441257050 441257053
    0xd0206010602430803040b030a0e0a1205090a170a061103010b340303091101030e0303041115190311090d0f0606330206060a14010210050c0903 63
    0x92902e0308141c503203c5240c00400d95907020502e40b165081c1c00c0d030311600404220341e841c143c1c0240054106020402440200100e0003940d49915040000d603080300d031651040c201c2c2e5009500020f0020f0070181004003106850301340b03540c43e515004007181c0d80940715000001b00500a04595900010010b452a90144900802d0046819030810440319000a1048818800050103250300912074081030085c1a60410355088400240d0100010884000d04007500070955460342d601c14000c0360100700a51030420708040c40b00303042000381d25607207100c000c001078034221002d030b0760402603500d0703209040740f0145c0b071250340342c64140355900d1700c603500240d02c02500803034030700311013134840404036025201e001e10001c001c4100c0d00c92684a401c0700c41c00d00c8104a0301d60740e4a0784080342000c4040d2082e2418100e210a110400f89009800048140e9004840b011740d4807800c10440c241da01c00d81207030250fa8461869541e044150030042c3d02c0e1a03404480b00d540c440c00c0c03008000901c210600a8900c03514100c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 441259550 1250 441258300 441258313
    0x501050a020a0819090803010e10050907270509011707050a030b040f031809020a020f01090b04080a0c0f111c0305040b1614160f0b0a030f0902030d0206010602 70
    0x24096080b8415110941d021800d06000a000d5600d00484000070101800c00441d600529170341d070300c416500903042070170640750750000d2007500c1c584e00b20142d002d00000e80b6256184c0c100100c015010030f0743c91022a0103500c0c14602108080403011541d801040042d00546407541c55085500044071001598105441880030006403844c052000104a070b0708000d16140d15215600c80208900303245009405214289248500f0070106410000c010302150354010307141d2418400007400d104914081c6501c90381018032400120b59820501078020b03034000034141da00e102030030050f036081819000103001c1110480c405030500c0f10003050080000c07801c81c1c40c603819001300000d1300c200303220803240500000c2c0140070078003141d00d40300d00070207200d82d040e100c4929804403544c4155812508e004c030000b07a60821851b103d0310344402c030241c0015110041013206c0c200e0804102010f41d00411114174100b5445030a40329600a242e0300c0074440d99005425070b51116500c200195403200c082c4542c400520441 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 441260800 1250 441259550 441259561
    0x70512042606070e0f0f190807240e0a0b03070806090702030c0a0b1305030316142706072306010b072111150f0606040503030304020910090204030f050105 68
    0x8514140f10b1900e03034403600781603103c2c1001d0003c0c43c20001c50703c0d50881c0a259002000303668a10141e0801c08036140c031580c4540c1094003050908080780c1c0300031101d00c090140340042507600f080c021251a41c5207840803582c9560000120036440035805806840703000000c1c002d40e5a40301120340c1c41078500750707003042c5d03141c69044040fa601e200d06c10b40c00049420140380440010310801d8810703000300c0c443c0d06125210400391030302c0d0300710f038002d8501c03540307841c80841481030301033304502d0410303400116010050a1130203c3c40c04015800343d40c207041e060307074543c013000d043d450b501d00b0140e076155604a081c1c1d91100c9800159030b080d045d140402941c89114080000541403000c1c403c132800141e00c4400440080c08001c10104042c9021000d03d062146014400a504104201240d000c012003203140c0708d41c1c1040751882c4c0952030301810080c001e0303400304411710640e200001204e0300664140c4442ca034641e10100300d221440c089404c8100c07c00e0000500105000d1362404155559004030000c00080e03c3d403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 441262050 1250 441260800 441260803
    0x5040602150411011107150203070c06090806070c2d03080f010b0405040e012004090c170415060315060617090606090a020f0301031406060103060b0f0705120426 71
    0x49070002c045400c101a4043c05511820100b003e1a220720201c4202e640c032504410b08a104e00c1000c11b00503480441d510302486164000000140581e00b03102100390b081000072901ca040c010441001d200301e001d446420490001030402501c030b102d8600f5510100502040145880d01c0030098000400d0040850001c4610300e80d150304851404d044076141c5484c04d42440081e18410195012a5503540100a50f0101d168001c000340545000c0c055a20780c01d0041e040d04881c0d102862030104000351090403050300001c0410354200da00f0000c41900440d0300a1108080c0c06641c00c01001e00d250032900c0409035003e504110305031002503e44068644052600e98403641c8100c0b40500280e00020100c1c032581446485550030889103075000d8503046d85400c805d0b0440d402a4401c46054502d038981044020042c020340b134100713000346010300c0200e10b0220510000d01684800d285400e00000d0140100034040101c10041c011445155469555881412082500b41c40111015180d04510310098010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 441263300 1250 441262050 441262093
    0x1050105010f1d0901060302070b010602070311011b150e0c04050402030c090603030706050408090a0603090b0f1906030b0115021207030e0103060509130302010f0b0f1005040b040605040602 83
    0x1041e03682d9004802041411038181072841d1101d00d980344501c900c3e000c903458801c640d0740645001d0f240540d440d6028130f001c1690800c140c1c0000219000340509000103000e9990001c0501000d00c0e08112070f94009071060040407001034024840c5c08240c0c3c000c400310a0710b8004c070b01c0d454400400d0380c04140c09070301400107507541282c0082d450f40050b4409101d610785020400c1d0412006000c490400842380e032808122182920140d91007000490341c1c144031b107403061100c0042d05281c40c05009959450b9141036120f80c01400726840c017001c0400281c60b004482c1e4042d052340241407018001d09a4038204240884001c0c050714018413424402a05010300004440450740d0319050800e04d818072031b0f00d003106c2c400042901d2504164443c0000505540c4d400700840c0107495107003040d07500151038580a42114042d65510161909204104c0240c1e40c80c4000e01440c140c0c00d80300d050804a444100302c03460f10498016010051022401140e1182d220001e4000ea608075003c445401c0e8162100c010341c2c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 441264550 1250 441263300 441263309
    0x20d030b010f0504090c1803050a060f020a21020d0914010b030309030d080606160b0601030b09060f01080c07020301051317030c04170a02040c022d031615140414010501 74
    0xd00070131080040700c80316480f180c040e84880c80d080c8542c184114541c5c10600065109907416030002c20350209016a92040e140040600130086117800100340024249022620718440202d40356500f00b81280c0940d01194040b89400104020301c1d0403c0ca03104541020b1112280150f610b40840a803081c28000103c03440340e03000038028400c042000100f00ca030100002c041c640c01100c18001013001524010080411511030610340c3c00c076207401c50006086401c00403060b0300c9540000d003030140355100ca40300190501c49c28039049015507200c3c0c0f880140341c442c2c80d00c001d42540c031b80420000e00307520b00d40348420540d2292340000350404000c0f40c0580d140c0402d1f20080c02401041004001c802d09041808c0d036451040020346000d50500e400041c00c0340c2c2652825009a000be803507c0e504c3d510007860308a1410110b88008a850220110a0b540d901035092060200c0011004010030b000210ba03082e60700002d661020b0000c0c0e1410f001e4030b00c4000060b50101e0b0490240c41d5070554031601801101c2c1070700c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 441265800 1250 441264550 441264557
    0x2101060c0c09020c0a1e0f21031a04090303090c081c020d05030a051302130506130212010603020f22031a070f0f11030c0102070201020c031908070c050d03020d030b010f 74
    0x500658176558100c0c006e0351000f400240c20f031195440026800f0328918182d034000c2c61011000c0740c0e0010340314110003001001900705480c01c299644c0800c2c0d40d42084020ba0300a4034009098489031034180e000300340c0301c04040d0500d62880f000058061001034520340100c1a4504d2440580c00584240e90350b554032a111000302d81c003400005d00c0070400f9842103504c48481310142401007459000700349000002c80c415280c05407940108942d03802c044043c004030720000f102c1140f41007030440b081016080180a4038042580000b00221140962426100c0180c0d65045a020955141e02d5011142d40c280c801107550340b250300ba500c9501c0d4100345005104007025256400d0103040481c041b10038036005d20f8084248038540305070240d90310081010b40701c0f5130408000180d80c0c3d0700500000e890000c24480e928440da000e55851560300244118a0a642e948481e0480d2101d44a1038803068101098200c143c20102c071030b4481083c503a00051100503440151030401541c82c0301401101c2409100101c030010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 441267050 1250 441265800 441265813
    0x103060e1509060117090a0b1605070809150a0e03061003051b031c080402130c02030d0b0607020d0f0b06040606050702090604060306090b01090606020303070804082101060c0c09020c 80
    0x107410803502d1103a01c203c0514000307120300301c140e0381c17001e0204c1d0a9400c05147c0c0d028038080800c0140d040d00150300201c55881c040c00c07405074004000c0c010300c21110001d1190402084e0201c40d51282a85001a00849000107440380a5058001c103040290401301b44a0312541b004607a800099025810640b5001005020401d00360001d0381c4541c0c41100800d0740600c0b13011007420721604010552001540a90350300001801c0c5401085003e6003500c01c00580c1074940324452440940020466419824100c030104035a141000020f2040c0140000607400600c11100b0608100c50440811902c40c450400360465403540d80038401110224000e88012401c100401d101600d400c44415a03ca03000410220704e00741c80c0c2c4e480c1d03010348141400407034003920004018085400c25000309000782816100560540c907096800400d5020007510151180b40001786d0a08003c21280b120380b50216103017003d6016503074410004181c0c4800c0001a604510210008600e00c0c402e40225824000098001d141c5c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 441268300 1250 441267050 441267091
    0x10e0406030209040b16030504350f09041b08011203020309130b040c18121e06020301061409031b040e1c090506030f01170a06050103080d06050913030f02160803090103060e 76
    0x100c45201c0581040c51550005007060ac00e080c0008000710702e00413829076194a10b420520080d901c19281c150741504c018615101d003113900069847c1118450450510b0208081c10264298411114001c9d082003007010302c504101055000400d020340299070801010514074012612029040e07c200c001d4a0503000801007000c50011041165008164011280d0208a82549002c8030781c10100c4517242c01000400c00d036a0401040c0a0858a110440d0301e00020180002d450303002c05811504480d1001c0101607150310380c0c0d80400c138140e428800702e90000b41141d040b0625583c0c0e0000140009210342d03030104040c20210140d90107410f02c5680c4410f941d080007200c816003000040d07030658038810b034482c2e03001059075401602d0003107001d4010ba0b651a0b828186200c156009500564010404103045c4443ea080780040000440e40500d00402c05101d0588104c1c10144140100c8036607055070503011410400210041200400c242c8040124642e03540c11f10303030b4905046804c3e2040c010005010321 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 441269550 1250 441268300 441268343
    0x801060e09011e0b1801020c0a0810050403050903031b0d230703030207020613090b09011d040203100614090a11030c0f25052802010e0406030209040b16030504 70
    0x8499503807041801950380d07201c4110304942c1e0845206151790310801c8610080301e50701070100303003d9032505603900d515460804007843d554085000d11000d0107075a4070001000d05101d4000e8615442004040c2e80d0b44e5200c503a0707041c030310a6090036a18000c0c00340d803626560740b900407203a1004a40703800b0124141480f0074071080c1d1aa0f040000240c05140d001c100400040e51444020070038032892011040600d070400c200c540071034411010b018021072650005101c001c88089040782a40161546070307205907030302c0c030102e0b0414219010b03510640307040060119041d4103640d4403041101040e1b809010300d035509584201580c8010070282202c8070104041840e00640764014901c0e540d0440c615854010144004100c90020b00c00e9594060005601102001002d0021504112501411010f00156080d0340c902e01040424000e05001c1e0040b5a9039190300c1d560800d400441d00107245021515043c18a000305240880c0c090324005054080040254024410f1030701640d00652441041c00c0203ca645 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 441270800 1250 441269550 441269579
    0x70c0803070b010e19111603050a02060903160f030908010617010509031e160c0e1f030201080711010608030d02030403020f060c0304080d0e0f0705030709050618130609120801060e0901 81
    0x12031440300402607a40300e54247c40710300191900c80c1da11213541e4a01004000d0808501400d920707107a4008025038040d80768042e503a9410180c1100301c01012030075600d4295011034455218002c00d5080c4540024120126980a880b43d0110b00c024010381e5a00c884075510381c4150316644a0645040e92240098407006000c1d00b0a000c800c2482c7c031400b0700030303114040311990550000801e4840700c402c200f8800d003801c2030071f0030343da4a2203c18a40303242150b0010380841e10081440b810040303070b690b821607928001d4115100070910807040d256202c3d41d4482031006503008032415800351081c031320503049500700010b01078031566181d0400c5065441d16921103006a12090300400e003e0340760310740003044190600c202c2c030b0215103460080600034a060b080c0750510f080360340208140c91804081140070346035101703032280c8007403004503824042e6611070780070a500c03402c0343c40540601c1c030341340d10102040409c0c03005002d0180240c503040320580c0d0758841260210010b37425281c01034000b00040140d1400c91114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 441272050 1250 441270800 441270821
    0x11506050c070608191802100507170d090f050102090f0a06080a050a0b09090f0d1704020d030201020f030403080402040f09030f0c0309083004030f030503090102070c0803070b010e19 80
    0x1800c04d0a0170240c00340203a40d110000394910500c280c40c200214600754032801c10565490500c0342c104103568950304214a0725030381c0000c940d0720004101c008010301c2d6001021241d031200403058149030030704141e4000c1d00321006283c003500401d00032628034030380903050000b181e0b501d035100c0d4034603502c0e13180200240002030010700c0c03041c0d1110003100f456070f190a40284a8440c04000b0510301540c041e41e20b2a0440c04400101800342c0c0562a507001101129240c0e8019010354141c1d020560a00c2e04900a02c580900301e8000030021007400101603202d840d45000328002c640c1400244804001c1d0710881d5414400200800c1c03c1d0321400044d07901500a06509078080c0c184800c3d00c2d0fa481c0b03400350074005030b1601126850840d428503083e5038100ca05402408094900c01c2e4109419607a40300115560030202805002d0003000040308040700750100c40b072080c3e004104024072940e80a002d5620b800c5040215420003030800049065566158400d201d40b118241c00c00040c5000c408403001407450860 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 441273300 1250 441272050 441272071
    0xb0c0a0e040204060e150a0c020909070e0106080703060608071d0f03010e0d090801050106081906050a030c08150601050904090f02030102032a04060f0f110708011506050c070608 78
    0x40100e030340d036500c0640020019074440301a086190006c1114008501910703403580c85e01800b00f01c48107039100c030345002c0e1694103a96130382458441e1241c0c00e141c81105e07485411000c5404d00089000c42c0d000120724003a45250300c003030090a803038120541307151204071404d600150441040c481d440e8041148105207031005040800d20b10b001d1404a0b0a442c014180502140c0c01522061070a5a00600e10402402240002c000d19414698020040d4101610000c038a00b00c24136000004c50700c0e540068001d1200404a940e1aaa01c2c94036101c4c804452256012600518400140c003800306810f00e48150b41c140c0d9a2840c0800c10001c000044c035403800c0135030f010442d204218005840920007140207031200010b00c0070b402488010400e11202610b043c00035100207000400c15603030403030b0b0340c00d4560040d420503980c01a1204001c951914849600da0344620035940000b42608040d81320140b8481c1c03115100122f9522440700717680c181301e0761031064040c0c0d0202e0800c120b0b5500c0384100a8100400d0007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 441274550 1250 441273300 441273317
    0x4060f0908040518040c03061e0e070501121a0105130509251704060f1b030e01060503010c1403060406030b091c0c02030303061203042d050105070b0c0a 67
    0x2445201140c000c58422a00c0840000d001c3c00b080c9000340b400000341010f05020b10f89407800d5a00c0c109810404c0c0700c001c12594441c000d01d1540c41040fa0310122a07203043e20104050307000d06075129071301e007007520829010480c5032541c19a1640d041c042c0500504041811105842c1200300459455001d400004000cac0b4022802064035901c1c1c64000d03004214995410340412040c078080512004518201c1c420700040e8400306001d0300c01c1906540d44544c00c44400541c2d5400144c0382c40203803010509015464510f40500784000760181d111403c0441160001c00402d900c502c10325081301c041041110204040c0152140d5520080c4015680072034043d0000c5143c40d900e68071075030000d8096907804101d410410080c55101c218190f800266102480c092400b095a500842d80328440074040344c2c003964400f6172800b02201c08000311001084100e01008a510360b034a81180042080c0506c0c0341c0d60f0903c400002420b610660039580d400350400e2208850b51100c04000c1e00d503a001b03420010502485070b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 441275800 1250 441274550 441274571
    0x50a05070813021906090315020405030a03030515040c0201020d050106030b031906151503150506040306200c07030302120909070f18150e040501080c040209010203220614041d0406 79
    0x2021300f000345130b103031107581c4000e00718a04059030059040d10300399054414481001150742c0000c00c0350075a90141000215500c50000462540c1410030f880d07a049400c140d01c20001d258158005d00ca0b1840c80702041100f82d0722001c0c01c13030a0f9818040c0e100d0f4181c2c050100344401c00604880200081c0c4104000030f40350440943c1101d50034103903030210151030300c40c59005520350327094001c1030303c1c0749039481141460a06060005105003c3d80c00043c11b2640e030303a048034501002443c410707002d8901c00300c0c2090721051100d41a6542d83d04e1380c00110300600400401c00d445c0c0c44000240c9600c00d0000b80300b00c0319661344400450310b608840c0d1b400e50400c440701d910841e1103141d092003d4054070000b039014800c1d1060040c0600541981c07001d2a025620309001000b0015006c110b0b10780b2480c04981c00b581e07840c0002c00407455401010310350700c2c59003201503591040140d12860031040300c1c201d480d0301c41540c4821810318801d004a1281c030386803c1144920008182143e90403552007842010000f0302c08104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 441277050 1250 441275800 441275839
    0x11060f0705070f080607080601020a080c160e100b160f02180c07110303070312020d0212091e030f03012702070b060a05030703110f061b0105040204050a0507081302 72
    0x25035011400303c030340c002418000c0c920309118180d8800528208529a4203081d00000d65401d482e000c0036100310004950b0000300e040c14003100c102e8111490b8000c040545554594440d10025100003450748460040041e008000d5415110701d0340f020102040c45080f191286444014000da080382d2180340d5401145207000c04010450080e50905002c6403169030381e03e82000f08007401c0d07004074801d41c8244000d80019500c50b078080d0200301403580c090307121006804458040e004542c8041641c00140007001180b64000681107420b5800c1ca01d900e003052902c5601d20707128460691148601d000400040c41720210300e94a144c1441e40c0f80b802a0488100c60240344103c1e0440e40e403c840d01c0404505001262404080c0180500001c41c0505100740c59503851002038621501c885001d0385034500303105440c7c0d440b541035560181012000468000c8240071f16402008200c03000ca200e613180002045008001d881042d11a5005032241c034a142c1b41d440b81070b07084800201c1d0403030b8003200c1103203031003421400c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 441278300 1250 441277050 441277063
    0x90103050c01020115031101030911030111070b0c04050603162c10021c030e0a0203010c050a02060c130b03132a0503010e1e03040801060605121311060f0705 69
    0x1400181c10024807000009003500c2c180f01544980013558001403011595400c1e050607501c1c0b007403c000400c5403c03890a007110080c00e0418035403551030461007150342640a8010590540300e1099002c0654400d8505403180c050780c018a038000005000080200c0340500c2500d06c4d41426082000d040640d052801c004419842600841005800d51801c01742c1498091106d04401343c0c0050006d1817001040c2d02051494003440c001010f480d4085200c00c050305021481c2810f0f000b90082c4102a140390700684180e02031001c1100501ca403000040c074605091081d075a070b150804403501000391070300654131b01503000070b40759000e01c0c00c070b602c00a0001065164010304c1c03c820000e003a044c0a9159000b224008119444640203174101941c0c00a88030000c10142c5a030781039849203034004103a10b800036203980695000801550319103c8049100747d0000c001d0401500916130091203503a51001c0c20300001402030000780044005a6540607515104000d04903011100d9440760801c84903803075040c641103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 441279550 1250 441278300 441278303
    0x50301090c090506030106080d1209080301060503071409131a090f0108010e010902030606151b031c180b0615030f010e070507050604030c080c1506030f1614030705090103 75
    0x40706490400c001c45030b50180b2540400104c2c000c1009520b400703c00c54640001c000c04c04200808044003240e5a01180e0144034002c2c4c1115900c0c1e02c0b9a19480d020b0840d60081e521103010039203954850380d0f507494075400c440c080f08000e40741040d80501242000050110500390011541644141511640f11b0f125040d104000302a852419540b4040c0140d003100e0941d0b4052185905051822016841c00036030190802426241c01c0140c80e0140c9240da41da0242c07010507038134181828880410b0b4580000600341d8008581c031135207011948004c10000301ea1800c48108194018184680e010035000060103600a001600f000c0039030703001c00341e0007020380d100702c41880c2b002c0c0190006104001281860961100c002c0c2403540c5007010949a8681d101c000400003010002808122401c0181100030b8925a1028400f00c0300d00d40141d0702c0d410b00e5440300f200c589001c0d1240b00f600141c2c8510008034001500e00040c0010807035410480c0e8078244c41d0304512855014814440c0010f031584648106034001c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 441280800 1250 441279550 441279563
    0x221090703020a290d02121021030f08070e04060303020f0105130503040b091c050a020906150421050f100f0501060f08180d0e030601210f05010605030109 68
    0x481c10751040041002154002e034201c0d030503001c0d407050100104400d40a03000c2000003103a85448804081d07901030b1140d200c1243e414415035003404078030041419401d040d070f09130482c0c02030044039041100e08111400c01010b030015905140c0000c415010300081508a0725071b1400441094201c4085019a4017640c82280142d101003400c0c02101028401c003234100c42d155181c0c081c5031b10140c5401d0b50302d0055000b403603011440007910840b190344101100034080e91104000700d40881a007440790300c45541087c01c0c0e01070090034001403203d29014013566400381d6161304050809080010211000381d078190f40a42141b100e415040101744e0810410a801072502c4c0241828900c09540f1015a0000311450041c18145001800120741001c0450444241407400380c0041d554100c1031100080790795a15003060045c0140d070802c46600901017110580d069044400c00d999070064628400c8154450030305498140c2c41c0701c0700141c907490030440980e00440000ca1401c2d2541c0c006030840d1400641202d88 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 441282050 1250 441280800 441280813
    0x203070e0616050c10050901110102040e01030b010528150e06030f010503250605070615030b16020f061501022505040c031e151a030702161206022109 66
    0x40210410130300c034020b0420340f00070183c0310190f0b401800e540504d9400c503041c0120107901c00106c9a00754180c070010100040d032100296902d003072145402d41d0a0042c4c0307000360b40c8480c200780c82c0350548105491142180c003403e0f20103032500038606211410000c40508004500e441c4a14940c0d0340303c09540225030b0500369004951400d82090316003841c152844025402c0100415091449043c4640c102e074542d007002c80e551642850070b1001008099400e1140705006800801030021205505206009840c418110341c01c4414003660b41d900c103048130751070551103000003403024068070200d5281c02006004642c10f9004104004c403001ca04a010080e032070b541d81c5020007161409000781180e00103903050800010201086803070b00c0038100703840c8a2801da100c820810503551200e42c3d40b07000b00980c42c1409882050301d07070680443d52081d5500300c014449c0108440ca140140c03030340c0300110b60030003151080b1040c4a64402c0080e410407040c0036081b1010b00c1020a0f00702181c12064402c4210700042c124 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 441283300 1250 441282050 441282053
    0x90a2a0e03060c0708161e020411070f0204020a0e10020a0b01090504150b1f1d0a150f050904060b0c0607030507050d110f16060c021f0203070e0616 65
    0x140d424511103041c400ea000324140400d00350301c2d204541c2c0f00b07a0005039443c0d0700c646d1207510038502124008010205120000100030240c41030b0354010308144212014408194a80206070007405601c0c000b410503d5403050000c018a0300750b0050000c03000700e0518800807100240040c010b0140e202100c0c01682041c11000304110340025800e0152003000020013141c1429152009060f1a03031114a6116640c0d0019003141e80d1180300c0c180b1031015101c018500c1c200e100760020302d03003144030307511802968000c0400b40300b601d00010441c0940f101c1e154100c0500c503030b1000c12030311402d58004503c03d1003010040c28225072202d0252401038050b00017803e546000e01c070b44d114070302a4020200b10070180f0342024050800e034040c04481c0c580040200109040e09140f2195150388100c01c0340344004000011807445e041c0da04ac00078403100c4e0040c18200580c1c18050340590f2180c803920314182c86040c0080d106921541c441d4003940d04050b031480d200c01c0340407403013000c2100d9a120aa4244042d8000d568060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 441284550 1250 441283300 441283307
    0xa110c0a0b070314070b0601030506180a020405090a0c020d0518031902030606100807050a02011e0c0207060201061a0706140a02032a072a030606050f01020318090a2a 73
    0x240c1c03000c2c600414641200c03034441e01c0300d102c6e015100c00c1c10162180d01007500782d5240c52900c2003003010703440808101e04000c41010020741c414415280070300662000138003210250b00c00c54009018507000380000c1584103408075040c1c1e1200300d26001d0800c403403100194580f030401883d401980031800350301c901d4203d80100b62500c0030051280c0d204407440c01c00c007503140d54083c40040d00612607050054a902400005030701401d0006e0002d0307800400355101103d03481098120a0307040341c01c0c1e0240c2d2a02920b81c44100d00ba20b8a0303001d82c5030b580066024611100500400a00e50300c0c0c0200000151080d01042c0c01c1c030100c5090300c0c40c1c1d006a40120911180055191131003041281040e200c01c4400c0c071000c1580b686000b4481d000e002980226100740c0781060b140c03c0509032941ca0b4018110076a22031a10f00010f000314041d150049541c890440078550000040720100c400700c510700e19140707141204020302b01e80010408050580c645c16804d00a804101e0202c0c3e43c0c0740e20403000f542010100800a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 441285800 1250 441284550 441284567
    0xa080a1103060a0302061b0115210c2705041505061912060207050f2401060806101e0905030c010903080d0c020705090405011a03120a110c0a0b0703 65
    0x800d0121000c10038480c99030b844000c41c2d0700300ca60644041d07445e07031381c0321000308071082451310a5849542000340d10f00f00900041c1c001010b0f035001c0801c0e1000c030305003102d103800d800340704070b000900c0144c000d00e05001a054000a0301519156400c1050721241014110340c02c0d05d10603681194200b11803002c07120030041034010194410b02c284c5090317215441000d004591140a4482ca1213414006000081408040d404407454950800e048515580000303043e10350340c0080400400f004040b0303c0100040c0421241d80740d040720a1551a002e8907107641c000c00072114100860350381880340700344600c0094038030030606042112181d1a03c14146103094240750070881c40f81035031410000615800e10000300f841d020380b04200c0001c0380004c2d280fa0f0190007649095401d1308529030100500c0101300400005410003841c840c80c000804d1210100042130507507801c0f29510082850405005c9070404510034002450010f1480080301c40c01c1c440030000c01c9180c0102d0300040552200000e222082c1034002040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 441287050 1250 441285800 441285821
    0x30907090e0309060d060801051008100c0c020105090a090e01020714010c02190516092c0c041112070207050111070e01030b04050a14010204060905010806060a0503070507080a080a 79
    0x74441d00308000081c0d81ca030320810801a10484022403403c41d00c503215801440900000c3c4000c0065081201458803003117881e1080d0f00c841d100d0030002684a0800340141003e8400580300c22480c084c0d260300540b000e82062104135040802d041300000d100c90035004490702c2c5140040016a1f0b00d0341428104c08c0004d40840c21062a81070404e1908025400120000340500d1400c01401f45e40b09803030300321300f0302c0449000703040c1c04621460081610745030340c1d00402d564502c1d480388003202211760400045956003550401d005401c0884904c1e06800c2941107589589000021740d89010002903e20002c4401130707501c2c0d00140e110920501003560040382e200040424800180740302d0f4034000d1140d4083e841400003c1840034a10089010131004100101190741c0c084901c030034040055009034000d400038440c0000051069500060302c0d4000d1603801c0c080c05c2c01421152802005034000c0c0da5a0380050011030400c41c5c100182008100343d00e01a002e290815516000f69090103e425415a80b40042 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 441288300 1250 441287050 441287069
    0x190e2704022e0f1803050c0103051306090b1512120306180f1006021204120f0f0b0619031a060a080d02011e18260c0a0614040503040335030907 63
    0x42440030a90004054000340c00274170307000c60240c0d2804401006213100c603c0083c09140ac0c07840c80b508110414402503c07032a041600c1001000020b020001c203038881418906140d040103401c1203004006c071009640c0882c01803c4c4601d11264250101350500341115420a049101800d01c0039082e40e0911507130041040e840240156614a20a100603104500c00c0206181c04240f08004001041101141a50700511900080b031380320f08028a17503d804941c1c0600c12004450044000b006c19030058050b03940002c41403501000d50403180f084460081c1820354002004180010481010005420620039950020540e48084003403c02110000d010212071103044c0f088421070704840e0500c40071542d81044406451100130714480408506001452002c500005030274021140005100e031929072107404104081c00e10003903030905c21441980d0041c1590810002000828003a04580d51020114030300740700d0783d0700901801d40d90031540501c610000711010040103400c88043c0040b00040c5082134 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 441289550 1250 441288300 441288347
    0x10030e0a05011a09071b02040603081c240e0c0c070b2101150503040c050306011e050306013602030406060501030b3102190e2704022e0f 60
    0x440074000084024000c6c803099106030200055669540203107006640104001c3d503039002d08802072055180704080c1007009800c0c0000341004100c2c83c0060b011289801c0d400c10341a5007414202d06580c40081d00d50380000100b8010a07250035001c2c40303980018458140f0042e039640343c22051012030201c1079403000c40085448010040b8110300c500460f0610b82c0c8d481c4c0142d803a51285011b0060707927000e4200315003602c900f00c004600401c9031501298004881a08075000c43c0d0781e14101580c40d034090241070b0006411032404107041c400404540c8916440854100803c85000703e4082240c204941c180c850a03100e210400507540c1500c50740441d000181c802220840102d89403c1c460100044449020f0b440c42031100031290a0b541030344c2030710100c181c0e40480c1088090000744806841d440b072900c903107201075203d126842b070b51031100f03000685e14209117a01c0d9a15004c1181ca80003101c1c0d50699503200c406c041d43d40300001044411a860245ca0f50808258000c800811050000d20010840c8413001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 441290800 1250 441289550 441289561
    0x6131802220302010e04180b0103032016120c1d0f07020303160f03060f03121119030e13020d090302010b01020d0903141f0f1a0f10030e0a05011a09 65
    0x103000003c405075004640c00e10703400d47d024a403026003e030240500c241000003004240e800101c600c030070b804001c0ca40ca062254220039680f618803100c0c03010706141658a0030040d075020450681c04140c0110414500f0565400c101380d6081001c1107004203281000c0f0400000c000d44510403900051b00348000c0d410342c03402c42c8500d0210450f88051a090104001210b0200c40c481e8001c1809488241c460010b0190f40b843c0101d404200b20007282d000c19400d4940380c0c00d40c040021000110b030703200b0315038000825158034103a40d54005100c6d43c0380c000c2e071031101d900301c500c02c4d43c0010161030100c500002034896550900a0845512400c41e44c119001a5000180d050f8841c01c14000c1c0d82e0400c5190f441490101e28907031a003182d81807100003154400041b1000002c00d0b80c01040380720020102402090500d604035030000d888400c8840e40502c0c079181091040c20030500c1c00300d514489090004441c0d00e4120000e24008241c001107a05a46449110f601030681d4131400c2ca2003141911003003e2030910303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 441292050 1250 441290800 441290807
    0xe010305121c0506060c0d0c0b0601031104091a040615080601051e0904020c0a031706010e01050a0806030f030c0102040f120b0103150b06071109090703110613180222030201 76
    0x1c681c8400821511100800c4582d60b170b4200303c0c1d00c2c010302c900031501c4105180d50068104c1c00545802e9444808040019402e54085d0041c017015580f098207035031801e0b003450354a0f0000c08880111206062484100d071111f600c2d60301c12140506a002401008c1c0d040380d083c000c0140200511440c10441d0500c41282071400050022407c150a00f0942d80c540c00c5190100f0001e00801c402292240b0030b804d074410605822600c4403034240c84480340329245544105c01900e1300f41e9000980384c0041d1003080b001600612074405907400602c010140c43c4205002e40300603143d5001a9410b140d41d9500207020000741c840d9414010082950060503140e0000545440e500448140300241424070641200e185503201917003c8a07250f900146066203d00305c074100022500340b502d503400c2c004e4500b5004200209030000742e01007140e50000c050240e804036102400f100360045000c04c40d6000c201d181c081000c13090104c104003610316014006071959954005a402054560344042117a6215013040c40541da1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 441293300 1250 441292050 441292087
    0x2a0702040c17010b0a020f030d060512010b0310020702010c0c030b010f050906133201050405090c0a06140d06090507022b080c070209130215090d0b1f0e01030512 71
    0x402407134603480c0c000c414000d07810918014041d00480c00006600c071402c00c80d603841002960401c0c0d07002c151204542010900300d46003400a030394564042807540131309a68580050100c035206140640f1000749035031714903006c19101e130070440360351100c0c40043c4078105940c3c140c04001c00049407450410b041c00ea020516694045d402c841c0c103640c4580780f003680008202d03400c0a420010500e903400d1521404810f00c1e00010a0254038850703401c110101da860840095100c1d0102d000414100701c2300e1602900791940300071321031403002425083c81001d0414001c3d1003040000e00c0180340100c3c4030302d010200242400015225181100560300c02c000070500c032440401d0601034541041c4400c0d4485688481c014000c0440081d402401c4008102c207806106005510b1980b0959142c04140d04241c0e10180d03600600611a4000007482000004641c04e00b03007007038101c00003c400403c80c41400ca02c40e00034118179045a060446588010003c11500f0860b9600c5400381e0381798107041924074210042d2008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 441294550 1250 441293300 441293309
    0x7031e0c170304170d0f0f050c090f150703020c030c0109080312070318030203070309050603011203050304080d1b0e06040b03010b0d110c010903030b0a050603010303082a0702040c1701 81
    0x740080000340400808144101c010b58114944a8448240f0007201000d07007180181601003a090200d6914004001e010369070040f4041c460070b0381802d11000600044841c4100040d50140401c103a8088445510008108040c00303a8068424090b001c030515191038a441c040078104280000c080051389000b10554201030201c0c0f07201c4481d0b480d01c41c000c8010305000740340c030711964500803024010190000020700050b486034071140b00442c0d50b03400708803d9010034450301020f0400e109502001a00c107400030341d8400d00c1464850305000d400310085c000c444e070140303890424000d1102c49011207604440314401650013101c03290324160611204440c0390106215069190101048601003006107400c07243c0c03541444035034180c07203295011500d8080c1c4809441640172a24160300c040c0305003069203a60003601c0e4090304543c55a4030790765044840c244000d24002e2404a445000c6080c00d119041f03c0f0354210404c1140c0d51907020314010401100c1c228004c1d0002c1c45030010000c05d40c40c20f50b40110781184e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 441295800 1250 441294550 441294593
    0x132c060130030c051203090d0315171e01020a020f010b01050d0908090909010f0b0a03020d1b0f0909030e092a1309050a060509010b030c030c0f07031e0c 67
    0x75007031480c0546903500c4003040145680116540c1001510400c0d001e18403650300a0202c800307010b903a9a06508030740801c1100309084181600c10311030042400083c056404076141241c0600054000d54401441c649010200c80c1c0d4000592044a583c10402c1040081d008402000000c2d20305001138900d00c030785606a1215925142c40c3d2b0103100c80e40003583e2203520050140c0150380f9199040c4c80c000c02c0700d1012040c02501e400a000303582d04140c0c00c8070701503a9000d4024507440010392190400c2142451074054805900c850204681009182030801003001100220b03800707580c0c3c0740150040465030304490140030688100011132115402c100c18911222103c0300c5260a0a1003042251040e54083d40701e00344601d500060f107121917880540315407003015081001d00d80f900100600c820007031181141c007034018000314103003982c0c0c1002503400200103e0000d01d028200f4021a81035040318806401041181e14042e043c2d031001d0042c09602041403078002c01c0d006541e92501141a4105a0071508 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 441297050 1250 441295800 441295889
    0x10b1602041109060304030f020d1103120603030408030406050414040506100c032601050307080d12020d0b0a140103150501021504080412120923132c0601 68
    0xb00003000031201c2d00780b070140c101652868542070240881703a24404910042c03040c0c1003001d0700c040c810382500ca170352000c070344c0614038280f0510706007024403034043c103081e515000030040050607110400041000340400e4407000d4030341d0f02d00301c480034400030010b2580d40100c0c00d100800a030f03a40d5407401c1c1c100203206800e00b0340031403009080898003650320740301611001c1c07401e03400c01000c8541c1c002800d0407120201c0c101c03030400741c44007800c54681c115011f1180100d9803000f0f4a8110390503540180062509907580061405034450006120a50a40c090311f51b001c03114440f0069568103014144c2c003421101c040d1741e41d4a10f4600000d66032a030100c00c105190900c4000b01e0b0030441310f14101c800a10841601c40a905440d082c04030f4005040c00540c8042002d000c4005940c0002d1a025031903040c00c2c8402c0c0301d800d9165424861044a18401410842d071b44c1c02200f408901207141c3c4400c041562172800c3e10b142c10300440d0614041040e00164000000c1001004034000031840a1514100780881000f8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 441298300 1250 441297050 441297071
    0x3e011404060318022709030c1c020c040207030503070f111b0402090a030303020405011d030c01050a03231b0405060d0b18130308150102060105040c02030d060815010b160204 76
    0x1d5a0301c1000003940a0a0a4a0317013202e86201008032500c1050f4801d900e00da901c1d520110390352445109903000140d0800745c0c0015000c0d69104210b0400c03045801501e140700b160400280803644603c00442c0070030008800c3c081515440040803001040e6801d150851035182150706540d5000c140c4404a00d039040035a402080c0c03901e8060f948440b9014104001c51a00c0e80b5002d00a5001402060700162049032a126844000503c40b442c2d810094080c1c038466400000465040d4000c900c04070034103864019165409690001c9014034001c0a002c1840c1030901b100380407071500e80d0440d004c104580c188400d00141c4d8940d001c44002000d030400c000745003441792012900340d0801c1903c120207080c1400030010b40402c0d002c49207401ca8407995681c0703440d5540d181a40c1d2001c3e102c1401d46d0040c4d01c1480144010304050740241c11640b260f004503420505a0400d10341503070807541200c3c00c55081940c8008800b0170b134840b82d074050007507461214200104080000b008003150b0501a110b50303100c0c880241e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 441299550 1250 441298300 441298331
    0x302150a0e0106030606050f0a030f020108041106210109020703020c040e070e04031d0405130303050a0b10020a020301050a0b060706020d022713050717043e0114040603 74
    0x489100c0700710300030301040303a5900300717203005000a00c01d003400f403142c4081041072880d0415608042d00d500250700030b0407410700d40045401600041c070889549455041c46011aa56000034081c00035104100502c3c0c11140340f4540170414042c0d000032903890040c070040700002e402080c0401c04d406e040d43e00117043d101d81c0c14418a041705c45d5006000c0b800400017400181580002110500030300341d441f003e0380d918075a00780411644115601e41324400600028030000f40f00740c224503013001644202166076078807403000547e04034010218030b000d80c0c09116048110f04003070013403940c44165a0010000215241c02041d124854550000d008590016444408004540c15110a02c601501d1505e003410300d040d80203030104c074405009100b0310406c08102c0b1521014041c0510601c0301e5030300e90401c0e401c102402542480090400c07035080b456046280b4419101c20000c0304152000d01000000d0407400d404003010401d8880181e04000007a125244041050003c55080700c9081c6000100e2031341c140302c03c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 441300800 1250 441299550 441299561
    0x18010320030f030a1817030d0b060412020d020a08010e01020d0f050405070513060306050703060302041508030f070501090803130209010909051c02100501170c031b04020318010e0a110d0302150a 85
    0xd406c400c13514846614013010000290842c50308655041007000b540c4410000640134034440c0360690340144140714018100465503504441c80900540c2130f55072951002030a48038880c082405903175010800605800060142c64810101e846080007241003a4440b55220340c214021580540d001c0c84203000110410307481080216040101040282441c0000030040c2840f4442a8892420440043c040010340105101100e113114001d61900e250707a640c5100e2034220f03100c1a10325541e165400300214803004002e5205845020030b00b03403080c8480c8100001e091042c3c0203644190706d0082c88000207080001c40e003188240400c03428443c070708a0310049283c00d031000750300b50045003001c0000620f499485404880c2c282c010081d075441c01500b0b0141a40c0340070130f0004000344100c0d61000368550a1641c000c40d0031a800c1440c07103c02e4005a00c025007581c2c2c41011442069004110070010f00131082c2010b000908104e500e000d0164954030000c0d51040741c1e20913503016900c154041741d00030314142c0c000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 441302050 1250 441300800 441300809
    0x5090f090a05030d1a1f110a0609060f1401140105030604061706040c06030209060304060b1503070905040b09010303201606080108100203060102120918010320030f030a18 75
    0x1c0360394502000400d0700161024601740200e0a440c0641c000452501151800c00c40c1c28500030000b43d014041c80460b100343d04585407103101d0180a5450b8007080e0720340107814001b0f00450380440d0b48050404044119400003201da41c202c4007407401070154450400d0700641d07645003441c019480c1d0b2500000500140f2060344410041d5542000ca6441d40b070001c2041c1b8412030280a07101001c5a8030401034080c1e101d840c8403280d1066003000020700080b083c2d806801c02180180c8049610382081c107410749140e2040e280040401c00080040246241c607000c0c3c50a100410750300c4045551551350b01400d144a180322040840070301d59560f258200e8200b103004d030010348084c3c1c41c10a9070356802d806044c542c028001c5141c6030159036201700d00c0e10200c2c0210307402858180e000340a0303540d06c080551419000a2412a444104100c810401c500004605406107009591580201c07a180c8174515035503416010040c0250005411041c0200003c400d0340e1040c40541041001070044d2040319103420341e0341c0c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 441303300 1250 441302050 441302053
    0xa0c150e011d060910081608150607051c0801080c031203011206090c090c092102010f050904050a020c150f010b0c030904050903040302101107031112100b03100605090f090a05 77
    0x503d400c0350b440003806c0d004540003142c03105108441941222820300843d0150401c2c1c0844502040c00d0915a0040204a00070002d54910000305c0d819200100c0a1042c110300080324880103102c007400078401909641c600310000c281581c0d002c0c0008055010521841c004540c8540990043c400c0e80d8024403201c6a1000346010400d80307515080c1c0092002c440400001981c181c0041441c02142e409081090750114601112521541c011141c00c18a100c58400308a0b050018081c103403214041c540c081c43c0e1303881015807105802d17035541c0e10380803201c44c002503021855010700030280401c02020341135421211145648a08400c07200703181d480345a120540140c0303000100a02c4101c0440540240c3e4170844410a8041d103a5908032580b030380d41003041056401c000070410018401c000a6020405c015040000242c0c004926500b1300d0400c0062404490b01c644000b80240340500c40140c2048900c5020042a410000443c0c88424000c107003c001d451540c002c289107140400c1f030b09508660150 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 441304550 1250 441303300 441303319
    0x30c0e01094b050714030402090a11040e0c0d24170106050303180a060c120f0306080f100e010c0c1415011205070501051801140c0a0c150e011d0609 65
    0x2501d102c02004226125000541001c0303691454031202c070100c03800346400414003401500c1d01d14960009000248528040e00010400040c1340e141d0494a1441048408184c58460040c0240c13071064944000f07600440c1203005001c00700b400011003c2c00e040d6089000540b1440c0000e04c800c500612194005503814072020981c0c00c00011080d692038142502940c00481541e600c45c0300ba6200840c10300010490b01280d82d110b58003e114550b44032101c8503d290204103980d8031103115003400101010384999811000c00184480f580b0b0160108040b608002040000740320310707005207403168541e8000c099034007030081070300b0300b010411190f000744407002e15490762542d58042044080d840b04030115450f0040341030003d5903600a40990301e076103011f45078015400c00140300466000141c01d419150b61032060214a03140341003000381e000000e101302e216520050501a0b00d491842001c1c900004000030117420010990f8404000d03542c5088140804150004800000e90f6502a10717001d40e41100c0e495 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 441305800 1250 441304550 441304691
    0x61002300c06090c010201060b0a030e071d0405214f0b030606041e08030f0a081f03080307090302030d0804021003110a1b0804030c0e0109 61
    0x8034040303000702140f40854505000c008016070a0780c0c0c081c41501d046403000e01800103014040c0e08050300c10601030003a5403142e07481e0700341c02c151000409400b02d02d01000c1c804102c1080003c0200349407611000e07041c40207036030f00d00e05500004d100e561140031400355082454982c00002d0042800700c2065000108003590056040c64280107562100d880c0d0355010305400a08084808222402114040d001d01c0c940383c28541c40c0c010341025504034000320130f00c00c0000500c05500348090100301c505a0420340d520380410900604c0d02e00701411814820300b00c441e034a118200c0a6207003000726540550f08a4681d41c500c2c40c00d81c0c02c0f607082e51002e9003600404000281e8140d0050840b441144219200031403003000c0001101190384a054282d50b901d400c200701c20905015922a00c0c40c51002040c0c018958466036545115801c04d500844001e1b0660030180022180c0da4039079405880403003000c10400450f01600d10620307d020180310307801c001c0c4200140941100603100103110000b00c101e261401c524 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 441307050 1250 441305800 441305803
    0x3060e1302090c0f0406030b180a150608060306070c02010c0f0803071106100302010e040b060d1a06030403020a030836010c09050310230103080d05061002300c 70
    0x8049200d111100c2c001180e02d010740080d40c03101c0d050700c1e4142c1d00b07140c200304003580100303507540c0d41c05e902c14a001d090b2182c10941580041c810605290086001c1412903850b01180b41f45d0b400c0001030085980c20059251000103040d03038444000c1c5410000b10140d0f0005980010581a001c1c0040d0f00c0c4501007014882020015801500c1c1590742d510749410300b0940c69200c1505486482005903641010405503201e007058103450300e00104005810100c400003e82185c5c0546030709055540c0300e256466004186100175084004196141c0e851441c00759802500c504840e4401001d10889501051250301600e2445c0c05001117110001074081e184650500421071120180c01190300741030300c2801c070b0361107154402c0071940098005e1585046003460480078000c0c001e0005a01c240800d4540200c07d1083d040b42c1c02540a18440c643d2141c050348001c0c251070006041c02d00801c01e8000840e48140c0c006161903036410075184484c08030180c02c1440112400c9448042d04100003c202c01544820 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 441308300 1250 441307050 441307081
    0x515060a0206090d080103050d0f02070f090902040b060a09150c060c05070b0c271315030b010609050a0302090a09020a0f060206090114132405040201031d0601051003060e 75
    0x1014100c890303004d4104c004640540b006d00004002d5008034005030145070080c03800540d0000f0500540c0c01c21901c0721048a0103103103c2d480700e260300d030303e03882038105500b0207107c1c0d0b40e010301e4203a880e1840d28600b1480500b0040076440780030400030f100100201e03d00d203e101142d07042030303010809021f14444008000e00c4c1350448002944e01031299400704803a10400b0049603208848551949007540f4101049400045000c03a00780d0407001084402c0300319192840b6900600911281114000e821801d0003040600c0c160850000e101803084140496a1050400b00841e54100c0e00204580c0e10041d0f020050548448006e40103112544040b8410020860321801d803a41079003159052f039140d455142c01d90b5243e031550b08101c0e01e2600407900880c00d00004020303c0d405800c0800d90094800c1c1680d03c0000001c284003129507035201840110340c0e040c0580c25410880c491003407060740951604544518061003451b1007002158207500070240a60481c00003404068900401391403c602d48810050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 441309550 1250 441308300 441308311
    0x1a04050d2402070c081c020607050d06031b0609060f02031c2d27061d030f030f0903070201080c2b0902030f060121031e030617010b060d0515060a0206 66
    0x441b800003086130302d00d540100a190440c1c1c024041038460400603074442d032183e01c1a155107030700d64134044003080044558100313a8285400c807500d06407605800401664541c1c001d42c04000054040640d01d545c00420341d404c0c4071480c0e011540b080c03944556680104030302124030b8854081c800c810110b040c3d4081c0e010940308024a4140240e180d0249030720b0491084a41a01d403a10f00d000d0308001041403580200005240d0800301c2c075010a041c07075150b1540e00b150650300384404000040141000c440344c80702e42c000c00b04500450a02009500103040f820b40108848103410022a050081a048040140d03d4194200180c440640700c3c954440c0a0590366009074000d1082d51340401c0c102d1000500700e412030712880d01d03000e00c02c1da100210710f039103e400020580c10080720500501c0d254110100c600c0c04940325450020b0b0f00f80c540381406000c8204c0c40c000d401607914001c04004a51180e5007111815419503400155699904c1e00078102c4c650403108060300f00c10042007440d142c3e500001c00c40d0044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 441310800 1250 441309550 441309553
    0x20405031f06050114030f040305040e040602090f060a050a180f08070e01060e0a17100203073605040f020d020c34050603150306101a04050d2402070c08 67
    0xa84403401942d034a030907100c038010b110101b000051050400407540c42c0d0010702ca85041803400c0d0b40c8903124403295106680580e1000d5001481c2c100e5850400074030414150140d072801c2c2400b6600710b010b0100e00610044909000544001d412400d8900e480c02d005001c3e04003200c0d11441d1501e0707601380d0b00c0781c09001e0021616840c8001168031800f542c2e0006601c02d000304004495828200c4407000b200146100b0745d6244103070300c0311403001780030390014600c030706421360f140c1d0540d510301101d0b400902c1b10010881c40151080c1608009090340c00f01c3c0c00d060300d6003a200440e00b24510460000280300304205111514408a945072100c180441c0c104100c050408154020a10b003401400d41c0f82c08410300040c052540903401c00c480d0500b000135640c040c4168800d5080d503004080420309140045500304034001c10040b0602410320120401121842c0f401c0e002e82c200781c10100490001030400c000900310052009003031208814030180000715213a041801e640720582441c0c490100005406030b07807601e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 441312050 1250 441310800 441310811
    0x1203091b0f080f03160614011205010f0b010e010e030c030102030108160f0506180f03100f11090306130807080a0f09080102090a061b170c0d022e020405031f 69
    0x1d06000040207904000c03030001030351500c17038401204442c0080c110401c07500213856140b00e03a4081c1800740700c0c50081114101094000e44140351450031180c00038800f00c845850507001ca1120390340b007090b42103101c0c2c0230701704140c008032650006850a1a411441c903851341c00000040b035030b84030204043c1e078114912251040595112140c010b100092070041c160841c0090001c0030300c460300034000c000d00d40e2001e02480100c07030750140802e0828400340804c01101d0380f00e29051000d201c00d4890b9030400b1044510542c1042c6905000076100c0c0c0020308541c883c5010144000240a65102140c10280e030000380c6503604c450001014040c560981c01c40c0020845003400080c8a200600840b100d81a00038054035144c0e090110907a001251141d523090804112030203000000c56501d5201c02c0041190900d540341d0900c48c40b0b451400400b400800e0464206403503407024000405042904981050003000117100d070540719074024062170f07008680c103104140c000040499288509000583c655805204 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 441313300 1250 441312050 441312059
    0xe0105030103030c0b06060409020a0e0f12060f0a0e0a060b180408120c0d0c18050a0501080c0a1b26090f130b0409081b010501121203091b0f 62
    0x29940024800500840e032656151400204841022607000c40001c09075418182c540c2104000c0b600000e00f100b01141c0045692021072070105408035117510b04607418408920f20501031500d032840039100030003079440000890081189a0071074600c0300000303411151500700e18105000074240991041d80503030002100c1d07800c02c0c0002e8610510a6410002d114601200750003298a008402490507810207018400100100c0c4d15010301c070303d22280c542e50500c5041c6035511220020705154440c85c0f00d00d402003401c005690300024016840700840340d4054a80d5100c0506956001c1004140740e2941c50032031a400412040090101c2040e41154407c4195103021046280c14401d212819a0083e0017140001c00c6140160040c0038040044002245200d1420003040c1503c03104017045541240100b0300089500250004150300600f00000f80420b504d04008100d4102003248050022083c0301e0940750060f0098124418580d44040505819104c0310140b9a40001c54000c0034240c142001d4000b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 441314550 1250 441313300 441313307
    0x110a05060f071203151202030a02060a0908060c091f17040c080f06010305190507090c1e08040b0106030f090515090f011506030903110d0f09050108100509130f0c060e01 74
    0x103035405c4500c60b8004c2410305208005c16400c020840032a49481000314140c0161284005400100c8051300c907120920b0412402d50b0400d607004101240d00c2d41c00b48490a1266201103c0300088141d400c80f01420480c1c00904840c11814028040300d03403001e5006002c2040321440d84441160400800d0b076052480c3c4c5000e050f21524288005000c5501542d90078181401c10414164014840c50844140c11359031140744064a0700d80c400e900103c7d000c0c10f0040420a4800540c4241e2851487d058085140507642d100c0800010b0103110304040d0382d90700c405164402a400740023496002000c803100c150700c2c03501501c822501291150118000c03079044101d40041405204080d2400034070240b100d40c1003040440040981e148140c0400285080700400c0c203c00303100304058068280c0c0c80d403400d030020782409000721080b03511143c100040070042004034005902d5400940390115840d5005803a0035110740c840507840040500210a503415802c00c00960003620000ca0b001511583d0f900c05d902c00055 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 441315800 1250 441314550 441314561
    0x90f060c0c0c270501080d020c01091a131e06110309010203030406110714030a080f0112030f0e03160e0601090312180e0c0703110613110a05060f071203 67
    0xe0003100c1104040c0125441c001c0380035014495480c56805100f001c0010409442e4203174000242c0d500303d01941301c0703071607418411002c4044082c00e10305078a03481c0c0422005c4207a524942d2058011020460066501a4044c010300600b98100e4080d100c1100c0a00b40044590601c00ca80204220343d0000b5046100401030350300c8450140c001d1800c580c0d960702c64401510186410428044040020784001980780c44034250320104e030001145c40300e000c10005401c6042c05801c1051010042004005054202c2e02e40c01002c2c3e41842c1c4000d00c001180c106172800f5007040303101507140c01501b0113042000c920140c05401c4038401507280310181c40301401503400c00414040980500000500d03195842d0003450306040e6500e0a985080741280e46038440c0085002c10303100d1469911000034443c040c16400201ca4803244100c101401260400d12501e41141e070170f0800090101c2410840da0650755151000d04e030013400c019040554440380103007808490303030001c04210f840d0950303650741400c400d02c00e224a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 441317050 1250 441315800 441315803
    0x1020706020a080708160b01080606010912030e0d08030a090611070503030117030c0307080a0e03010506030d03200c15070804080f092205010918170c0f01090f060c0c 73
    0x1400342d400294440c1d000070351142e482558458001c0202c08028076038248090041c030b00500f00306003c1d50500c418582413100c080c2a2a04120741e200d010300800c6801580140303d140d00d41407402000003030034041a0042c901c0207025246040100030800d155200750441850a4802c0004008050240c002d0140a0059840180c040e40c02800148a15580308511003018a1517104407400c101030007480301c1c91944441d208550201d40440d141b01d000350401504d844541d42107000340401c0c5082d402281c1d484082c2e14440040588a01e1101081d14010311a40703214050004250354680c80056404c2c6e0300c0050412a4907850f0881c03000840d65071240b40d182d406241c1c051401e0349084451510100d0ba50001c41c2c800d80e02c440c601c880000910040d4213040c00e01c4030b60301c002069941c5000c03040e008a9401000041c500803011031104006415650406105040c41030f6003621025040500c078640f81c1d41aa00c1c610f2507282520740424411411154546284110740500464030140d00860b9801d00100b030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 441318300 1250 441317050 441317053
    0xe1b0d05070e070c0803011401032d02090118030b161409040903090e190c020d121a030d080f10060c060c050d02040e06030f190b0702070504290102070602 68
    0x20500620446101c2c032500700c00c1600d03280c10040b5842d154583e4640c0281d11036025003600c0f40803140d065815006905881d10041d60980c0c0c1401c02480542826050325003486c8080e0b40045e038200e40c0da00030880340c4080d000c4600703040d01540d22490400c03d120310655121100282c140c4178000001d00c02c50540075688080440c031350a0400503000c0c803000d0001d04104a0a200c031000d40030806076035031806940300300d4031140200706040c040c903407840c121a9a58609411034009103400d00045803c11075482d140c00f500f02000400d594410306540f01034104070342842e0b0502070395841207040d0768400030042c020700301090103e03c0350b1645030526000504900c20903000c2044c0341280804030300359a1100c8003008050410a03e404010010001280e0094010014810307440042c8452418100710107200c0e00d80100082651501c401841a4107580a5000403c20f203c02e200144850784240b000364010200500117004100d130641003044445000711008500ca100407001d00100e610004100c005c88501d46c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 441319550 1250 441318300 441318313
    0x170f0d050c01140a0c0306090506060915070203030c06040c080606090c0a1e1106011a0702211504211e032406020d030501030c060c0f060e1b0d05 64
    0xc0e1801c1e04841c01c1060039558074100c1ca4070441807645643d1040b03007200700010f820720b0801c00141c21107010390004004146071104003c6103444e0f51007150034880c002c881c4000c111600850303003003941c40f54020080d050700006c54065080303140029250701a911030311040760403130b8640803240e40e980401c407a51580140c500d00803c15440c001f00003081030203218982841c1032403085940752100604c0e078981d100001c40c40d40508248480c14004540948006501e010002c003840403421014000d001c0b010340b18644022141e008150710030398040030111548241c4810343c0c3d022508801228088605403004803a6072542d00100e4084200204e00c00c8040d20b421802842020061406d84c149920940c117041e56119041007102020014840c500b50b0007248040035424101c0007402d00410810701c4d0185410b0500500001ea401d101d035030241ca40ca4586084040c07440d0414485440c000320000d05100c1ca40710005481c000d021440c40000f10102418401d120f080e8170900841940701000035000781c0262 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 441320800 1250 441319550 441319573
    0x60c0406030207032c011814041d0a0606051002150408090a05060304060207050d0207081f180605040b011208030f040c08060c0c01060b091c06020d0e010204170f 71
    0x1e038041c002d0240689001080e0121600c0c021788035440c180700d80f041c0000c090103844030560303000c104503151000c09111003119601e00500b001c40505034451141c0314603104c0000140c03458000c1580f0320450390704030449280d40c08a0511500401182c010b8502034052510b001c2c00302400050a8844200080ca1070542c81e41c0f10f8441c100d0319001403030000e0344070741d0910700011281d03144009180650302030500160b9400b03840c41c3c818900680f2011b10300564100b4074042260980100d03480500051a0795034003014108142c4e000c00500a02d80d0b40c415000c2c0080c000e80a0120700d5000d13a2003244903a20700003569813a07001c184c00403911404010207880040000421078920044842d4001d40300701e0000c2119510b60840904002e8201c407541014000440c180d50340381400d001e0703030b00100f43d07450705039142480140203c0c90016803c1020794050302c05d0b96a800c00c100550f070460300d07031407803c1d00c0402084c0e02c1003000e50302035400b0740710b100620f07901244030852088012070849640c6031158010030a84458 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 441322050 1250 441320800 441320807
    0x50103030f030e10240608040512030c0409020409090317011220030d020f06070e1305060a0801020f040f050a2103180f080f160612110d0207020909060c0406 69
    0x5180f400c0d12140500d65a4003076401d140c0c0600342c04101d00e0206503150005e403180794041241203920807020408990184004180e020803402c144160300c16149660b07503980300301c0c0c038510f20542e40480c41c00ca1000800040d600d4980c3d02c2525054802e548240b44025141070b40c00f074a44080c003030030740051504600c000024003c0712100c40c2c40324900e402102140d20038000681001c6000c2c0410000d80c011002d540c490042c00d200b0f6070350088850070510101d0681801061410b455242d0f144d05481e95200130071041d81c0c81c240848000d202620080d5690b1124220340b2045811a200e00c540b14400c02c0000300d00c41c6002d6540e0400d9502000344c0303d080d074044200b400101c144c00003043c0e090018560b480c0f410090284814405041d00030284140e042c43e0400e07013440c201114584c2c48854000c2018001003e6642c2d60300c1040701c525203807030a60340d9004080d9200402940002008130400064400416680c41d0050440640203c400010075912000e80540b1210100d03001040050208410311401e800b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 441323300 1250 441322050 441322061
    0x70305060306062205040614070c11060705010b0907021e010915090218010f151d041a0a0e010608010f080d080a0e0f011e09020a0302060a020109050d0819050103030f03 74
    0x54130584002925500700400088070000d403029038a1644900740b0720300300a00c52149541003802413074165030103040d03a03ca003850180104200e40c818000015440f040c01001d403c05600004010160020ba003032141c0c01a5581c4280080300c410942c3e42000500b840e42c040c40346420040e04170204440401d0100f0098008050240049038407810b50155035103084a060455406000902c084500450624405500710100816090104130240ca1203600568400b10107112040c42610081554002c20b810030074400710750030820b501f003200300c2030024008240c06180c44c120b500b2a1142c46482c3d880c1c450b40800c900c0785001300314180d8480c510604c41c4500c00d42200c3e510117280d0fa000990b400002c41018104440280780c0c16030391b03448840342c1200b407024818207102c01028110410001c071072540400c00e802c4031840041e120368008103a42e18110b00030340004280680c080305403402c883d0003c070090080300050340d4003c40c003101c0c0581c001060100f807103400e05894254a0340402244c180c00c04034041d00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 441324550 1250 441323300 441323329
    0xe0f070f121b03110f0d080702130605130902040509030c060c0306030304030c08061f05030d050c0a02040c0216050102070b0427050a24050105030402090903040e01030f0b07030506030606 82
    0x42000c04140c1014990402c010245200303000444010001108100950345403868132449104200380c414001103800c0c08440d4a42d0381030388d44070780d403049664404004280760303030007960020800d40748500300d0522a4449480e2078400c42d420012a201d1580e5030342d41c3d020340c50702c403a0240c1c090004600d009a0321009998800b01c0201240e06e45038890f039612000401e00da1010813240c0c007000a010380d1181c50340600c250810006186040c46182000281d074890520940d102032010016041c1d6807084140805580c294002d0401e00504498500007544e662411100e00503501081801040b990310100f17800c41141c0e050711100781081c0c00c096484074040902c01c440f26001d1007031848540585010300802d81315124a000008010b80341c01c0189030320102034082003c1c40e00030101d09102c0c581c1c209040d60341203034058030300744000c0ea14120f0403072452060f0340200c001860010000000c1101a0a80d005490b128903a000c0d02e43d25117030003d5043c0c40c0c2c1a107400d58075400400003c0c01a0070017078001034040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 441325800 1250 441324550 441324563
    0x402092205030a0c060b12030405010c0201031404050303040507090911090619060908070b040b1e0c030c01050105040b03190206030c0d140901060b0403032715030e0f070f12 76
    0x98641e640d06403842d84007403408804145a144000300307202003441581220310060352607901a081070700815441e84200d014060601000e20384000540e44039a00c81004010b0481c1c03001d4045c109806e02a0ba250000c407400c503558800c00344080740321405800b0f40018141e000d609420004007003420000100002403081d500444c41c88817015050244a117040002c2c0917988414080c0350814a00505009540e0041180b85500708820000b00f030030702045446a1801003401621903000322040d00c120321440c400039019102c0400c411202c1031043d4403007030407100304580400201c15001d09060300c40c0b02c610752640c042507603140c1c00000340c2400303001158024100d1803000d03e0b00040e03084413400c4030341408003500e00d0080d8200f0001c04400c01d01c1444041d1524007241350500e803841c1e40c01091410181c1c500299850803032501c2c039000c44021503400160031120712040d900b04d01800c1c01802004180400c101c103114201d05902101004280b60043d24220050101d0b0fa6040172000403024840c0b2000b00d480 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 441327050 1250 441325800 441325861
    0x6030a0e060f0609010b07080415110f01050a0510240e2106060a0b1615020715150f0b0c03040503062502031824040906031a040209 58
    0x20062126034801d01c6801403120903803c280050101566050304810418801041401d000c5000241601c04840844142424804102c034044880685810900f440c030721034180318490095041d006248140b030041000c002c20b40e141c14810121144074412a084180d4601100d6006145113613400084281414010036040b043c00100781a240107006a42091034100c0307141a43c5907040c46003a400210449181100c036003060f90302c40c968402d20742d02d8903e40100d605003000300720710491081600c0d00078900440d105d16481c01d02000e24120160052081c516041c0305281c8203a8a0305200140d40141c20f120321610308004050385281e110f010200500d11061100203400c4e50200445031107100c10322403d001414260310702030800c10300c0003050000d40d003081c403900e80b45d07031441c00368000680070403a8040070008001c6182c0d0a411081640030070069000640807400551a070400f004413440b488205060001c400c86d8004c4800041e2402540078524402060500381148401c002501a03441e11404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 441328300 1250 441327050 441327071
    0x2010e120a020306150108220b0c030603060a09080313030504350613020f011e050a0e03011406150f0304030f03050901090308010302040c021e01140108070b040506030a 74
    0x39036040c012090a041d0701107100c090460406000c0305030052420000b44804294400c0040c001c1000145200207a080220381400c0d0345000000740914142c00c05482c0525042000c0d8441e117680c02260300a0091040501040044040e485646c000c035800c06102820758607078006032650003400c50015010844e0038080800d850030b50106010548000e03200b40030384426081c01d00b0369500b44540c82c10002d0780182c0104442c0213081c0c80010080342e03044512500241004005866100d9116802e12414010001c5244070540060007823180080381d48901d00c4081c0241c04060a81d546001103a02400e0900042802410f00d81640782a1254109507281020f85090310a4070f41c0d002240c0a600160705604400c4071203415210309604001c050380241b0080e07446803000f81400006102c020302881e92905501e1603a4030a22840c460900c108401c03440200302050304034060113540001d82021070301e09000140b17105000038403004031602041a542428900301c1005a207030001011503007004d40360b071141c03003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 441329550 1250 441328300 441328309
    0x9010c1b03060f02040e010e01210312020309150606040308041e05100801050a210b06030304150504090f050702060705070816031d060306010e060702151204050d020102031b0702010e 80
    0x2410f544078003001a00d851500c07603c0d000242e4186e0000c00954148001444400c45080111002003039210071050783c07041302d2800311042150a55108001480441408140700380803075580165507404121150380c0d00c1e0201000742910a41c4401000c00c4002c000c01c01184204c810400c03203070501c2551814800e81d42354081030300b06d00166200c00000e014100140044d26103017039944040c0620600b4180081485181111801e0200c6006486000c1c0c0c0000900c540d50b0400403a030180402481c142d003400b00c440d0010740190000d00841e00d40a0070180d49040c28096807044a10401e0307154010b0201e901e5043c0c0070340c0c0d10b034072550003521050410003100e4602c91408030a5903649119585001d655a17120b600100d14007800c43d0354a1260f04104180030740340e030340441011015031701101c21541e104181c0c400194008821450080c0f04000445c4010b40703404040a542e100d070b4001c005865130101c060108034201d02c001c036000f0751901c9a0900c11b41400107900080c161061043c10b2000c4c504c001e013030004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 441330800 1250 441329550 441329561
    0xb190f0b0a05041508010516080a0c1d0d0804090902031e060415110f0306040c0801141c0c0806071209030203070f03211a030601030c050402070302070e040f020f0609010c1b0306 78
    0x3004d6402d101c4c4101005036a00031450f1b5800232b20294100004490300758000c043d20000e21031107803a480d0314020904665a1401c616005541c404000307a130b40c0d0394909150001c0c2c46109400d81c401e00511049920280c40c1c80c6042100201c20700c0074184541d0b41e43d4541c000001080401410684d54160071200900c402008100401040c0b040d203880b840d01c00108425584081c958104000c030403401040219011382c0400301802d0102c031600f00b0b40d030b1800910004892071120180072840e441c2400281600c3c0443c10f40c1c0151815070f11a0a080345061031181a00e030f02c544c00400603481000ba0501140540350241e400c2c1d8868608001d100790040c2c0d1004001e42c4444000d0962561031110b0766007026496141084c4013001d901900303040d807454075005500c228501c181805603400180601c1050710a01c4a04050030700d10b060ba014500b094105031007101e05621040f80a054408c007200c0301032400304207540007203805a44d0800c18080d1591402e0ba40d801c01c4401e450007082c0007001000084450052 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 441332050 1250 441330800 441330811
    0x60a050c0c1603021011100c050c01110a1701120b06041407020d090801060b0d021b0d0e0301050a050108030307110c0a08150f04020105041208070b190f0b0a050415080105 75
    0x10702c600c10f00354010800090401079203801801400040c4101c003500100d03900501903070440000990480e0818203944078801d0340c40351380095182081c82c1e003001c0310a501401d03a003401991800e4540690213515281c101b000e014047c7c4801203180400d0005007424030083d4400405403020961a10454029081c12001c0d21208096080700204241c0a50701c0b03001d0fa401030443d00b0007406490701e0050f401d051485240000c40e03495400045101e98001128107040103000e07000111108a01080401020305080600c0310f403180d401e04020807414560b500549045e90045006949507445501c0107031800c8100e4440c007000c6001e417442194807683c4050f461001483c04030041d06407000c0c400d210119040000304150f01d500c10302000c0c000540d900806443c20ba4600000181202403c1d007042440c1e030240180040070003d0310000c008540343c070414421040590804184000340f2100d170103000340e880030441c00b600529440c10401c07192a043c1c008445200c0540c4007012041e840d4100607003500c408460 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 441333300 1250 441332050 441332083
    0x7081e0418230711121608031b0c031c0917070c0b04090207050705100503070c141b090906010308160204060503011506260a020f090d030305090d11060a050c0c 70
    0x3202402130303c0034840c0b04010324541440528103034501c88401d016402c200005000204c0100010300b00e14260904049100c942078012511800c1c03210210707030340c2d600191100e49500c040c4800c40d44910414007038200c51a40c0030030034400416080c01054003581110034280d586084603180011500c04c168001c001a202040e00560307183c00342d0504914221031a0310040c0200b0400042104a95214040d250041c050740760152034180c160900d503000c070008a03500341c0c2d64001d503044e952541810030084907501d08143d0f20680c495503402982600c40500b407102030801e607c108034850012201e0f014480d24148001c200280094440e40482d003110f090178559246204858030522240340c02c1102c0c03c1002d0041d40d50500c510040d22226101c1d03020182444001540100d00b208801e001d020a540003030001901410b5040707000d00700203000d0079059801840720700030107990550443c0308050140000321850000c1c14070742c4500311984010440280301c810340b070b00180300010005100340036454030391710000c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 441334550 1250 441333300 441333317
    0x303090406091d0a08030103020f120f07032d03050a02070b1b061018020702010905060304030824060417010603020a0e1902090112091707081e04182307 67
    0x4407114001d582a50400f9015070051501c5000144248112415282e068642d0204200c90f000850f41e00722001e001c0c24410302907080740d01c1d8124400150102101e0040f0f01021440026403040c45640001c040030400403070a40364601c0200740130340300604900c4820310480d921310365916025000d03030b000101050f031015110201d01d0910441000840d810500303181d0740c240355a18200300980c84844246500c88001d0b0089940c2082d603000303a038948010403010740540ea5a250a00d0002c0c075114040701e404110744400c3c2e00164440b08400d61f00c02c00048060800d42ca01170401b4a800d802c1c2d1640600003215648032800400103071900c07508271000f407290824205080c01c000d201019504003500c610300b0b2191050148116681e07211080310380190800100291402d0141030211601c22015280714240d0800500030040003032002c0140058400f035080c9400a0001c103000142c03e10551140c0c1010302e100e0302120500e1501544100c8890503500c44881d060300800d088050b60940480c0d80b40042003110307 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 441335800 1250 441334550 441334571
    0x605160813050f1f2004030b040204110307030b0109061e03020309070f03030c200a050f03120c030909090d170c13060801030201200304060e1924080c0315030309040609 74
    0x3801006500340c8212140d460700311990001d422180904d110148c100c41140e40405c0030b40d282d503130140e10b00d0b40c1042e000700e0f620f03c1e020394050007800400a00320f0005001130400100203200300c0030500580c64800d8031004586c07145400710065080036103074000724000c00c500000c5010b646c040040045100e501d80d22008903480c1440700341202010003c0700b0400e03000c060f0040039903950a0103016510120356404d42000f025000c2898802105452070501030001529464590004041c2c01c0c840c0c8121030100c05a40c44041960701d94030360550f4980440d03035100c5450030502d2031001d00ca41c05540c8024150030300c44001d84a00348154150300c03d1002c0341d00c1c4001031056581c0500755000211000820356001c00702c001c059030703a030311442c81803008001031a203902d4600d6854052040100041503c0ca1200d9602e4501c0b160b0316544201013a040651510000d030b01041c0100c002074800d44208607000d0031035460525120b1200c100c050407550500040003166595690340c400c01015029001000410038880d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 441337050 1250 441335800 441335863
    0x4020f0d062307120525030213030308060f15191719050603061504020c0106051513230108130203030a02061009060812130302030a06090605160813050f 67
    0x284e038001c40b01c650410041111064048014104041204240c10440c080d8444224000e003e000030110224086810000c00e141d40111640e016410803180021001803c03001c12200c54601420342c0041403040c0803100352584e900c41083c158542c5401d201c00e400700e401e40301d5503400c00304440c45941118500d09185002da49489100e51042042c1c0080c441390600d250120b05c84440c0d841224440c0d9000980c41689107000c1d0003c000a14001d03003100c1e25404002c5d0441e440d40c011511b120f400c00d04800000928007404869580c8050841d840d040a4241c10070045510401c010301e403a4100c1c4040210034016103003040101210100d6030302405041c10429042d64510200d54440300780709081c064103102c10680855a00c0354024500e5070701d5038548070300907a04500354490b80060f516000e40301c6540b060003e1a00300c055800d02c910400c0000da42e03015642450008100600c1c4001000140090010b0245002c00550076024008481c00710142030840e52900c1d01c0c40380381d940f0400220404100422b40b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 441338300 1250 441337050 441337067
    0xc09030625032c16081507050f070809030102070b070309030216080709050613110c21071211060901060e0c03071719090b150904020f0d062307 63
    0x14a460180800001100d01003074200100441c401004200740700ca000c001e80030401c0d441401c0700d59007010701903035035841c1042e11303441c1c6c0e0008001099022000607106510030021200040382615145050107141c3e11050140c5c0c11a810702501507600700084c101140c0c840c40610703c02c10305580d012442d0740c440c0c503000b400c0c42540070b50700d10103042e40d160078014008082450000e48400c45000243c03aa252000030b400019191100b502e0f00703180001c3c01c2100d0000b08006c118040380e0204941c1000c00010302044081c0c0c0880c0203204000c0300380038a000207080110040140301c3d65107071800c0c0c0d1100442041d4180f40d1f0540710302e0302c50b170f56038241000601c1d5200c0130a03a119004940f843c0c00d614060001921140d074003024030107114809400102c0080c440c6180c21140c0800c15800c002d0891700e850034000f059019a0f554040d1a031100f062401850052102881183c0c081c0c04514944a00400c0c48000c0c4425807040b6029174651407e9100703004000311110103030340501d0f4041c0076420301d080007800402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 441339550 1250 441338300 441338371
    0x40819020d0f0309050106050d0c03032715022104050a0b030405210c060a0b2803030503060d02060d060306180308040201180b0d051b04120b0c090306 66
    0x10844440c1d8220160000ba081d40d10194905020440652910f4003500608a54002c2940801080144024084d0a0402c1c00c1903038880e84414550b80c003402031a00344460641c21403d02d24180241c107002031070300d20780481c0c2d05000c0ca0046071a103002d90102ca40141014506011a40320046020402441d01c2d064410003803c480c3c039070a1075400c0c81d881c1d031038030303a9140700050100d441c0060250030f0f200340ca0011259a003490f01f003a0307200742c10a6000500545001694684104002c140c01100440e0401c1845504807044100f48503281c0303581d9050743c1c00d800040c05130740d110303006d4207030740000d078641c00300810550100f0040060340a082d0f1401d8030441e18107c070b45043c00c3c10402a010002500403141c2c64005409091048010303100c80b20000402d0400e8001c02c00403240404c4541e11004582c2000d0f01071000984410910680c100401249000e14410900304000e4420898081a140000303c3d80180354070701e215103400d030b1303c002091400c0e200b0b80d07428841c4c0b10005c04944482909048004218 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 441340800 1250 441339550 441339553
    0x303070303091209061407021807050901021c0f120b030703151d0607080406150312080f090309060706200a080108010c120b0a0323100216030c05010e030304081902 72
    0x4c80c10a640100010b13042030240640c2100003c81c0e000b555510300c020f809200c100b507007402c3c1c1484d007808020400d400480c0d021f40507100d840e42d41c0c0c440003104204030310806130701c0d5904d50030882000300890f00c491040e581c40580e155100c0c42d00a00d910280203540140d8041c41c0000c000404102c0142c0c01c4800e007010a041c46040601114100c4c0c0c404215a1b030410524508060380e51114145800289446000364015580c24900002000f0380318264034410b02450300c5019190f607907402c03500d100030021074081c48240c008001f12190740c544000036060362401041d0015000602e4000710b4183c00080c190048a15408102c00390f5440d0f001d0f07844e80c0500b5961009000403022030102500c100b14007a0800109601c42c0042a295241c0e0b105170001960050007010361a0851a01c0d4200740080e100707420072038040c0710880803040c500744c001c9940070300480200004204480d00c084030b148001e6a007c0b62955207800081030715403402c201450045010b0b15203d40d0394030852000201c3e1007103626098066 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 441342050 1250 441340800 441340817
    0xd060819050d14040f0306050103110f21030d0606030e1006050618010c05060f090c0906030d080402031501060e0a06030b1e0f0a08030306010f0804170d0b03030703030912 75
    0x19001003000080c051860608410161078498143c00314000c0f6001490301500b00d0200009010050300070714100d90182c20407202200724070301842043c40b07a111000e60080d05107100e0410341c1c0c1e00101894140c1c0b0040080e2030030680324030464001d9400507403100300000d80f1030f41e6000441c1418419400800604042080001d00d00800b1483c2d0340111070081518039564410541c050740a24041480d8a074050190b440310300c1d04800001c5541c106035690021407250454001807800d0400800e4042c00004000740010301c94403404072200c0c0c42c014400c0360180030b0700b60014600940706050a004c0e00c2a5111850ba212100f0284540c0726120782c005010181898002c074516151000e051804e005840780c0e40441c075403100041001030132000406a00980e000b64000380200002c4041c46c01000300f607071050030081c02c007081210074040580740038000d4a00440d1a146000080c0000c2103a0b000955010996070146000642035802082c0103501090302c072102d03041005103030f001e03080841c505400c10581 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 441343300 1250 441342050 441342053
    0x8030406021206033c0f0703030306170a080703050f0d0501031514060f0a0f0608010f0807030210050c150f04020102070b03150d0503070204090f052107080307140d060819 75
    0x10454000d414a06160320314032459042c00c0d03070a500c01030014505d40885010030600d00310b45540329003d210542c001f91030210085015200300c425001c21504e40c100800b03851103541c5a2072540d5001d40000c4061040c10043c44008080000161000c816040380002c1c02d0361445c240000305118000406d034855181c894560307181d41c040012243c20002c25903904004a1500020a80300f45854004034001401d441c80001c00707079842041e130350688043c4000912450382d510340480d80c85030207000003035108420042c1800780da4890005005840d040e0301c201c03014507910b005114080c3e0010340c1e4492030340c84004108030641d41c04214500080c0007000450b499894034012860005400110003032007041e1550719001070260070003e440c60f00390014010000503110b0b281085010b04411001c45881c024030400021130f0083c01010303124500c0b02034505207030000703550303d11a20340d00040c0240b041c8000c0e06600c0ea00001d101d8050f2041c1da5000500040751030801c0d003000d150440810000e43d612102c03888110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 441344550 1250 441343300 441343333
    0x3030709060f0e060f0c010e010c0503010b03190f02042111060a0309060203010b070201120c080c071a091e06060609060f0c030c1b0306040c210803040602120603 71
    0x864840d442c10100b403080c02075007181d50a0124440380d500c0b810200e2540480c56400d0000c2c8024407042000300300d02c0548891203404c3c0c51040d400c1402043c0300780700401c0f68002000003103074001030321054072101e8006500b404085902c1542840851030b404a0107108403980c00c3e49081c550100503914036069003507590780039607a0601c854424060200800d02c40761144c0a83c10038104540c2c40241551a9070b160411550300d5007044600b80d000540401640404c4000c9216030070f414800f41c0d03110742050380e49129500d0b0a9124040c120b80170180003820104031501040e00c64014040c42001e4101e50882d4609200c1d5217410500400f044c0c0c020106001540d5503d00440f0103034042500c495807295400c41c2101418064001c00780c3c0340b808000713a02e01c601900030500d26107031100c2540c0c110610504c04145070f9144400c07140180700c4140c69105001140581300700c444814041c042003014400c45a8410440d5002500c048071540d80110345c40103521007a00b083e41e400001074005088580308241e468 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 441345800 1250 441344550 441344567
    0x6050603102906030f04110402090307030506090c120c0409020a0302130603030e0f0105311707140d0204110c150f010e06031506010c122d0512090c0901081608030307 73
    0x1002080d4034110843c10307481d1278043c0c44d121031000b02514003069030f0b414601d4032003004a81c2c0c40d186000b800060b00f001c0c50b040100d240c8000c0c1d100e0081030800d1024050000501000c00c0c1a40d0107080fa41000005903501c10030121035140d01c4001042071440cbd40b078054070103542c40c81c900d44034030340020510346166404029290990203010408020b01081c4400c280c44461800d8403003040d07a1040070105030403141c602c0780004c003402c00e800c4070745040d41c60700032140d0128a100c019902c580c6095082e130243c501703034105c4c4c140a04000708013031414001500540c900301450180200c01a506410010b00520030031310303a4010f0110402e5030b8024640180069200d500101b0400d82c400f00c14004508140d1096044400303055010010b1213414501010260201c00b1320301c040d2144c1107031500d9100d0703160b0042c802e03410b9140007074481d1420000c42d40204511070074010500201c07803040240d642115668044a5402403265101030308032050020312044880607107030800040c41c4d004205010f0480e0f842101d5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 441347050 1250 441345800 441345803
    0x62101091b0804110603040b07020f012c1606410d18060504020301050619180e0607050c0d08010f0e2508160c0f06050603102906030f04 60
    0xc602c66489103482d68459070041c940c00d4110802008000410441c0e001e220300502061b000c86c1c4840c5060804c143c20717203122028298410b00c1144440e22002441903825000c03860402c1524980d188000c060f000c103454503801440010024810407403140100c030070305000f00022056400080e030100d079a09035561405030b602d01d0000d2001441220060306980411a0040805c601440c19400c1d414110050101600d05078829464040400c05600e03200b0880c6461204000c3c0e5540194908021411034210400c0c2c4c04040b613840350700d0902000800c4c007440348600281e89030700d510b500b8a1590301c1e1070000c2480c1da80042c0042040103000341c8450801d0b0004035401e6140c543c031907a680c0810801603000f1a2007110600c3e0306950360700400c130b401c200c2d0607100d4006220002042003119100710f0344c0c07117400d20780548018060740860340450040d03040b003035021030301800b00d6480a400b80c001000710b8440080314648851400749820404100d000010f0380400101c03403060031428000d4010400201c003600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 441348300 1250 441347050 441347057
    0x101a04060c020a0f03030f030501080c150c070801060b0d060803040e01090f0e01140a0c05180d0507030503030903220513090611220927030e062101091b 67
    0x18802c568541280002074882c0501c14882544d8174900902040070072103070100424100800443c0304000003d0710600d41c1e4006004004180707008030111000e40c0011504c0209008421002c82c0f10403090184000506110340700e59a600c09903050501200d80d03e810500003a00200010030254100405c1103054170100d2800051001c85024194011700441c03a00200707550900e400c4403146036402d0341062281d0f088980a02100c00046400c5800c0c2c81024410100c011000304040c050381414001c0d206001e04c51001c4403007498894a5032481c6800031a199801e40d4070004d400580140903100e00220340a502204e0281c050910b4009900184c052203022a030742d69810041d402d00c5205e4015402d032321294100ba55548260460f1241c074004007400c0311034440c042e5240050011004d104c0c41200307444204500703400c010001c2c6d55500e40c5116003416000c2200102c404d241c01c0d510307640240094829045004034180c04001101c5c01000142c0c00300b8801803400c02c0300b0040c03000c0d4001c10b8074074283c1e518 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 441349550 1250 441348300 441348317
    0x20031501240f1b1a100f0501120504020628020d031a041a19140a0303143018070305030a1b060207080405031e07060c050f01050f101a0406 61
    0x400c3d10340d2001603140301900310541c030380ca51114408502c5400c2e008050792643d0004041d207926034101040018401c490024900c4041088281d082da0702c680c2d001840140114901050141040340403141428000c0380014004035810b20241c040010080f42441c42c02d0a202c10400300300c00c603e03144800110f10f03000e1034480120642c4882902800c0080510007007081d0405040000c582c0d038000c4042c01000d9098980c14a21a06858181e8141b002c50303515584120b00720040340d4005002d900f0030003800380303410100c45440a40f00382140108000328003140041000e85004404c44e05012070070000e011981e082800d0501c01f2607804000c45940300b6060030070210200c80b110460410f05c0384000302820861011030341804108101c0014001c40b0b004800f1292811103080a81c0f0700e080c580c0c89030b2890340c1d1212808000780c602848494803981e0050003580c0001003404002420b503501111780300841e440384001c000180a046d110f9601901214090914420512985088900c220f0142505200402 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 441350800 1250 441349550 441349577
    0x20327120a1707020304080d2f030706090308040209010501080f040201050903070b041e05030f0d031107080c010606020607031e05060d1b0e010501110a20031501240f 73
    0x1902c00c01002048100368086901d4442c0000b9201d0300240030343d400314014034902c0d030f503158402d4104102440c00e011b05226450a40d88250210107410640e0399400e020600000001c21030502c64141c00360301940f144011494903204020590034140c2045060003920780500010f01040c981c540d900c1942801d10f00c0d0b640d408000041c3c601141c651001021420008020500d85002c0c07480078000903e44220f51040345c0c65900b0551200120f480100c0300b41c3c801c01c0f200c18424443e4001040d601038182455141480b03544070603119910910701d0700b410740c0d183d5000300080f650410040307502500600d002c011000881d0002024600c0514110148035141d001041b41640d9440140aa07591300905c1881e1266150454001d444c8803445140d43c07082003800005000e501a50b4030804204076080644000700c0030b80c1d592020840200d18035000c98920541864030307610200840e18201ca143c0c50a800d8540c58901134924040204e140e00c0503005201c2d0500600c0c07a0048010b48051045060040318110030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 441352050 1250 441350800 441350807
    0x601030e0c1302070c15080a0f1404050d02060705031017010f14040c1413020d060b040b0c1905030a080406020d02040303081e09120a05090a09020327120a 68
    0x2006000c1d41e01004590602500c28115801802d8440c4181c41810300e0a686072800c00a0304250701030340000c5245000003482030f84107a804542c0503412100005079502d0722019000103420203e4080b51143c0c0721880034541550108032580d40002985003da19610340248400d844445a110340d074065015045901154442904110030005020008000c102074013a4010300740700c030503a026100d003002c0c1000844c1320803115481156105001e42034600d1100030b00480c0c0029441a9038003202296640400300d00d660b54000100001c081c14038901d41c0326030819115504281065482c01c103002c8075010301c00002003012052300c0300b00401e4107090059a645040090203881000c254210380e40c4006400720401d600011800d0003840d147d49540b641c0303259110340c40c01c140001da4900d20a0341c000001604588403290060414042c40d150860400488101140c1c0c8802190070070800782d500401088000c8144480d10020400b2106450b0101d00b0100500f0381c50f00500c818100d40d0341d00015001001c1c601 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 441353300 1250 441352050 441352063
    0x60f111203070804140303040201021207020f0d0b090730030c1a010f0509040309032a030506061c030801090b060f070b071202070b0f06041e05040312140601030e 71
    0x20540c0300c5039034034074101d02c000380b2801c002c0340d0071a4080b0500c0d80c54141030780c000041c2c91040c0c0c0c0c1a002080d8580b481c1c01d40c0d50303554015900032030f8003600798001d00f041600c50600c43d0800501c1041d000459080c00690541800456002110007043c07074225425108a48502c0c10513580c04080f03060480105401c044600e11448400900804002d0040030034482e11040098100c500045044402984450070810b0481094601400259005506201151301d03d1104203881901e100910312900c180e400108400169070f0040c3d885400c000c040060a040c01910048040112031500c59105066500540700b4101030041881d4a69160022211602e0f0101141d91071001030fa40b158540c50705e80780004421504403120b0002a202480c0718050b5452402510400e55104110a0140e40d0700c80404183c580000c0c0140c2c0c1c01074849014100b200d6110000c044021f241d1500443d4619160802400051074010350341c0d101840c00c802d03041d211036004a03054003e0024600402d456004e032540303519140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 441354550 1250 441353300 441353323
    0x503091512130b0606040303081504020d110309010c020d0c03030e07051806040b0a0803040306180c030f1712070509030115090b0f03030a020d0503100305060c0306030610060f11 78
    0x106075000c2c000c0c00d072140e1450000651080303c4208203a600c1c00140300150140b8403004002c035030f210000c54514055000d000c2100032024000501340401c030030002040d1482e007600900a01000010722544880a005004035100140014402c003106104014048450024041e04055540748201c0b030f00d8000f405000000c22005008040340e10464110040007201507039600d1045250041100301c9081044682c0c0c1110404406141040e01d141c0340c02029018000f030b40d56140d4192000240043c1d08480e485000e18000c0c1050b01c0140303c6403401c810018420194264850130500804160240e07641055512102071302e4101d890340c0b840400700740540b2078012201d0360101085000b1075501c0160317014410712102203402c0810441520240f5440e40300710034074100140c11038945100c1c410301444c0250340100443c8002e03a00e181d030740c1c2c84d107508141d02900c1d5030049540002c1400043c5c50f0400c0125046190390300080002458508058100c0c00903c0c294818001410260400d8100500c6042403c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 441355800 1250 441354550 441354577
    0x1f0806012703063e0d020f0f04050310020702060301170c09090d090605040807060806010c06020d0c0f020313031b0e090105061809070e0c04030614040c090905030915 73
    0x110388034076015015010384e02011200760900e0842d0308070640341816859034038039a20b901c84203000211812119543c454400400c81c1c5808010b1b0164606440000300711800c2c054051a8585061108041c20900c1042080c2000ca00500001000d0f0340c503a4201c90441e25100c4008580c1d00116150030f09010340700b800c85501508010400c0020703000401c500c00741580b10794990b0f48030350b114081520035010394081c2c0341ea141e1111030300303100302030003002c6007500035805040038140a03190799600404d0341d02610210100e1521000130040107a0040072818150700580080d6081044406440d10004440e01c0054500780c00b00e00081a0342c2c0358910084050312040c00210b03000c1c680a000f06010301410760f6980e00441d2501c80d101c04034101c092140740610700c00005089103604c1d240344048103000240100e02d14034410880000066800e100c0c0700c0c058417001560b216070346480d0a080782c07038a0041d8020300711a0b04210442000480c0402103038070b4a4000c0310201414000442145020b025900402544 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 441357050 1250 441355800 441355877
    0x3070504051905060a091e18050a1104120308130b150f040c170f190903020705041e0f02030c04210605040503041502070513020903160b07021f080601 66
    0x40f0340d001c81c07407030300f44d0707d00700802c2c4001200201150200e50b03042c8a00b600070f035107040269401d6040c60f088a504010000b00c04078002c000b4440d104170075801540b0124510a40300803c1c0c1c105138001c213920344e100c610b000e166036112001c0e45810304a5000245002414a2840c8070100d059507414241004400d000c2c0041102d0814080003525240602410140040041c3d002626040d1440c2c4402d00c02c0d40591540d80d4410000240300300038281c2c600049065006030f000218450702c41d40b00e811070998500e2845100703102d1400c040710403103140f210b10100d2540100700304843c10805808440844405082c030620351400c200e400900c1075443c1030f00a00c41c40c00d00050209102c03001000c1e106036417400d520201414040c5005076230707889aa10855030081c00c0c4a509032030b40e00041d405000142405410b444110305a90142c0c10086d103071b43c114565240000c20f518040d0b04000e16001c1c403070b807440034104140201004001e444000001c0149042003140e00c0c4a0080c540e160044a042d00f9141d101c151f0b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 441358300 1250 441357050 441357067
    0x16030309140703060b100f0f09122001020a02030c0d0201181d090615010e01030e060c180603010f0905180a11100806010917070e01030f0302120307050405190506 71
    0x8031000c180c8001c1d1441801c111100380a440c00c01b0341c0082d4a03d807515050201c01c82c0c0d0b90143d0310724000a2480d0140031403924001044400072401c03005d40c61140c011503044a4032031002d0f00c001503946844a0465100009400c0103071400254660600800c480103058030700d061004841302101c0010414003041c2c8010300099103401c84c040340c003200121403500c4c01503549003055542e64100442d100090461816125581d6502507000e21405807410300d40814590312041600d0f28200d401e498481911a001440c3c1d040d03a00001104e050081c001c0340d80e14034551410350328107002c00160040021490703462020a14500340f5855000c0640d0501042e01d104440d9420161803004e0803c0300c0ca4015500100e00c4584288202500d601c07540050715a01e005d14203011151142c054013a422100b117110300a00400c0e46560078490078021407040c1341e178600785981c034500203040030255511040412024020301080d80e4120f803d6034281e8500391011302d0038012803c00f100c0300e5503540e40700355000b410008100a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 441359550 1250 441358300 441358303
    0x4030c06080711030d020d090803071d01021b0906040b130b090a06150c050309191d0f0c070318120606060e0112090614070f231603030914 61
    0x412160261228035003030b035521006440c44520814603c1e10ba40007000b00c1c1c03c02001c680d0140c20710031840700c800074031540b044e0342d03492040d4402c0e62240c2c00304060002c00903511511500c1124079400c21b201500f5216485920203a0005030280e500703100300007580004206849680c4103a003880030080042c0c48546c02684000000c11080d69458011910040040d0b1909d01c9402120201c1d000600400c8003804494401c89200c060b80394100c0301c86c0010824070b200c0e80d03540d480e0780c024455052200c1031402d00e00402c4128060000601e100c0c03201d8200c1c00c01551418054902d41e00060b103655441da2251035103011600c0244081880311803444070f88011500120aa4985082a10039a0308004103038803134000380d40c005111454580043d03c582801c0b942c1611b50741241d40c88500ca400085040c2d40300154004c42081c0480e0041c000442003e8074494640d8000f040311005007030400180e15600c40d0400861051141c485070f800c94258042c840d8042511a0784502d0816801079903400d2007461781001c05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 441360800 1250 441359550 441359573
    0x1b061d1518010207020d081602040c030b040e070f0605071502030109060602010b0906091b07080409020306030709200c1e07080f03120109050622050601081501140c070b0403 76
    0x460244034400c0c00c0c0104000c14404c0f01e00d1941c0007000110744044650303c000403580018069111040c1c1c1c0c44200c00103848901507240104195100880c0b80c600c1181400100d404071801d040307070b941c89164200a640703442c1011200380c40c118588250382e00c00d03504003a14501d81225800c1c1c0a940300100004004c0415409034054903140c0d4000e0042c03495480401c00403003015244a41e004030090081000741080610200c01091410082c6080140c3c82e250303031345103812036400050050303000010088149401d008820142c4004001004403003542008503c0006803d40c00c905041d00008000d60362060401c44183c0c5407141e03c1d103011074203c245000d00d489000d43c0c4100d06e12440b0301c52f581d60620101005541841480c0c540c3d8801c03581c0303400480300260030060807281d041540340300320240d15000e1684415082c0404200401c0d10300b00350f000100310030b00c000e04540c255600002c03c90582e81c3d015040c0c283d40990b5a80841d2134081014032141420f0041c1c0c4030f002e40c000002000800c10420f020315 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 441362050 1250 441360800 441360811
    0x101b0501050411010c03080a05100503070308040f0803040e0703020904060e1005010f170a0902040e10060f0f06020309011101060b0a0206040b0105031207080a031d011401061b061d15 80
    0x3e1044007220240151000171074208000c0200b10311200250001c03282d50f100e903501643c2d40595403502961000400d080006581060b20850710001e41403089280c0b49801320300030f2030080025482d2614150780080c0c40300010304941c0c10150000341000c203942e11500114060100d200c0d409400741003181c2c45040c0ea10142c4246070120303801c40011340401d070180041c1c07060341c5101503042c041c995481a05c03c009000c20740080f6071091f541d1001c4420b40000304414498074008000020341c1c1c6042514100351600d232a030100341008030ba250306200996001c001e0b1450100c00b82080c929000f56004101d000d0880ea41282c903d032a4040390388100700d5030002e41140528022800f0071016601d45080c55116442d001a001851070f04100483c0001c0740718000300003040491074001040b8081c005400b04801b07540a21001c240c0d1100340041480c816881e40d03034010407650074000c0e00d4161241940c400403000d0311010f083d1507074602100303400e2417400d411140700c0740c1c02c3c20649844c1c0c105807480100d0060103444 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 441363300 1250 441362050 441362063
    0x3030510150f03050f07090e04061d0703030e0406050d0206030915090312060a030210080a1103010f030b31020a1d100b03040c030b0601020a0221190206040302101b05010504 76
    0x21034118000351101a015081c1e076034403808848d08012181048000103002140d81654951102540002c01040c00140c013002c100a070100c0740c5075007401402d001c285032059110300d00c3e003c0d00308004d0340d4002214030400d034191040758603a07481c10003241c1002034021124403685880002c00417001808002040328610180c8407031019212807040c4190b00c00240002900660701601900074a07011707032030843c0d102d0b0142402164040e151307030610b40d143e00203178054030401184840c01d20420840341e6046600c862407071080c510401c0100070851040d24420052284007480800903825915400038060241400e204049049404d20010200d5224202c443d80d0203040c2c480404500c4400400440e40103507044010b100305903041d900c0b09d54007804081d21590641c45003540803401621891100039900701084400c403e00ea00c000001b50030728181d082603003e500b4005101d00c0050b0303542070503101503a07010b890500f01ea1420740d4082d10400d800040e90115582a04800020000150481807081c0d01c181d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 441364550 1250 441363300 441363311
    0x150c1b08031e03010b0d0209060c0a030f030e010c0e01030b0103020705120d05091b010e041805070305010b01260a2705120304080d05072006060a15090303030510150f03 74
    0x2d00400c91404280514200c1070401c100d072a0825419030068502d20400502d11450503407808200707454012140c0e4100d001ca00110440c20543d60544283e01d64154044028460200c02e0392005096040c3c80700003a0505a980403e090564425819a80d4031503111b02200c904500e00580641141c00c0500115105410071000607140b00000c285c1c1084e14a1034146206207502850064584038411180b00c1c0d00540d80e050703060005a0031214000146024901900000d030542c00c3c2682503622040585043c014010b5910100440040703903e850413100b190100d20700d844644100c0c2c0500701d0342881c0c0e86188681c0c801c0484030116040091311b00c0f0b01c07800895410440752081e0000500045a01130719501e410b10080521110f00c0e0040b590101192070564003650307150504040030001d43e0071741d11007980100f040264a04084034010098004101d11120107040344030010104145070000501705501c80b008122102000d1039260050310340100c140b03c907502e101c1c400403c002c000694840010b801c12 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 441365800 1250 441364550 441364597
    0x2120f1e0c01050a0909020f0904020706050402010e010320032a12060f0105071b0306050907030b09060402091b070203031b0618071202180a0905070b04150c1b0803 72
    0x7001204c0040e01161240a609864450140c0c0290003a100d0084984401c202c0c02c40c030380d03881e44000d117035092103041c0000ba64106400010444948481014141454950f200320040d207403d000842d0001403141c82c40c0c0e6995000b40c4010008480460081000c03d191544000d100192000d491a20903040001180c0d903516030810081556038045e540c0032540800c03221000c5078242d90203140d5026005151702d05942e580e52104e040740c07c1100c40d0700c07998111400c1441001012b01e80560031140020080c0250706040d00011000300005d4480844185404801001031240905591481e90014103498450420502294400100546c4041117004050001e0840e0300d00750100d401c0718000d280201603490411510300b5800e2098003007640e210f0541c2c0100a02000503007403241c420f0f061a000840c0036225031601c0c07440d107011030f04600083d0000340f0090050750682d2100c061005442d16101d817400c90b4030f08089198038040c2c40481e034981c1d00c1101c00300e09003000000501c2900d0343c00700c2c130640d020030340e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 441366906 1106 441365800 441365807
    0x30702031005010810020306030c0d17040b0d0507020d0c060b012703110d0f1b0b03070306050a0b0403050a02091b07060e15060d02120f1e0c01 63
    0xb54001401036400900c810804181068010f604609003440001e45500004591a0059103d00003074002d118284020b1010b07401005a160b5a464603004100815407003013210040da00d007800003050720300d440003d400000d42519038801d1002000d5940d540c000d070000010312410001e01540d050024100010040d1170a5500d115009405c1d146103454040080003c0c500c80c8a00d2040014401055529009c0e14915501c10500f1404010001d0700b0b12203400e544d08501d140c92408410800c07002d03016407114060b50021200802c0d40d6070786401e0314049100c1d80c0070080c529003004451000600300b07494107030b401c805a011640324400c204600307080e45820241c3c0603600e1684a00b200c0340515000d01003485100703205061a0007514010010070420032170410000d02682c0c5060f072003482c42c1c00602c014500c0d000761506540b5a5045030b00c8007c15800302602c8420240038008203000c01e50300 = true := by decide +kernel

theorem cover : BRFrame.Cov 441187050 441366906 := by
  have h0 := BRFrame.cov_init 441187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 441187050 ≤ n) (h2 : n < 441366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
