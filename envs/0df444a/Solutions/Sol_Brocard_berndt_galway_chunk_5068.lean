-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5068
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:38:14.8332+00:00
-- url     : https://prove2.me/submissions/182e43a4-a9be-45b9-a2ae-a96f1ac2c8a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 911330935 ≤ n < 911510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 911332185 1250 911330935 911330947
    0xd14063d090905150a0b0c0703050d03020705070807060503010905071101090311100203090703081608071b0e0f1f0306050108030307030b090910050709120b090f0f0709020c0106030b010b 82
    0x8604079440506111144884d010650000f66a074a1449081d00c000d402d4168403084038080c80c4d86003001580008046009030351b84190390640c540d021b05001401031003100c00442da81c100541c1c9400c954092500098070401c018020031550382c11441e0004150f00d8180b4401c40c111032410300319401c154040f000102010006084107008028401c0c040e1000c060461850402404d01d40e80c0345200e00c80201600800b28803005d400c10411828940150880400c42c0c2d100c00511308030401004d48123600341e98038281000860151603580b4840d102e056082c072080070944981302c40210050340600040390854010f034000c4001a8140a034600807c40b0b24000c50304d9040490002c1c00790707000d0080312402900d4180030001c40700d00c0028401011500f4250000709030702c55980031142c181840d08104004441d02032854100002810543c1c85a80550166050703003c840c1d411648035104004c0a0155a20002040c40b0002070740e4002e00701085000c00000b1540e80e69500c81c05910000d80c0800c10882c004501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 911333435 1250 911332185 911332199
    0x60f040f051606140f09090a090c0f051c0f030309050f0f0f0607020c130c030207120e0102010f0501060c02061c2a0305040b010b03090a0c08030d14063d09 68
    0x400035008404d21245080084405c0c007004d240c00b85180d4244141c00320b4012640351042e42d0700145041c1d070860140400241c0310000d5109a40083c03261030300031480100c00010038541355046108595010110707e61a00791703520200c01402d0281c1c01070302d00e4016055030321040c00081003410b00d1b031040d400140c44030800010707040d810028024200007e6400c0003800c00f01c03030750700d100740f9070300700c0042c007100160780841144110000c0c0100701c401004480c0c0012412400743c0c0046807038418041c00d80c0280440403138000c0043c1580c030300f0302c1076102081059038824018a01300028054140c41650b003125204e00c034040300350984140c0c1048516044080c4610b6100341400840501009414242031095003482daa4450070500305101d51820340c2d02c084040380208400344031947d8210b800802c80300d4449c1d10380d074565032130354880c0308820483c1b440c01c40c0c2031321500fa141c1441c6120392002040c84060380c100c04c540e02c841d0005502c0b044500c907803041003228240c844a146244208490303548141003810104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 911334685 1250 911333435 911333447
    0x12050a0c020f0606090c13090c110618030a05090d052401080601140409020d0b0c0310080a0c05040c050d050f070f030203130809030c060706020705060117060f040f051606 75
    0x4120202c1e0380008081024944588040716003061742820b180341e4901c1d81b0000c9560304603182c0c120405180c1000560140c0c10f034002000e28249013181c043c1c903040e454144092071032803160000c0c01042d030414441807039610b00440c064031510b48090200b000a103016520721b03041c900e8914a001680c0464500b0441491203c0901c501600820004101035414817440c2480c3c2c1038046c128902c1651101d8800b011034071044d00c50540c0540c000f0709030765141400007210400786c100b1a64450541c5010700001040f110002d02e1185d0380f43c001206d150014100b4013808041c0918000e18814460204a40f015900003403103114407030851620048034506100000074034031007003415100e04060060003808001082c2c010141e0b82c00e68084402c03565001100c01088c2051000c03e011507000c00c000ca406024400180c0090040900c9841510792a030303210301c500110b000c0552541c06440d07012500140410305031041e03143d005805410100884640d56481c10310300401c0d0b503400440409000c804021158000f4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 911335935 1250 911334685 911334703
    0x1403040f02010f0c1410050c0313110a05060c1b0a051807030e030c0109020f181f0f0b0715020f0301140303072909010513032001020301260a1509020112050a0c02 71
    0x180123078a1410000a10f288803080c001015141e05521025400c1982e6140e180c10b0090101408494441d0811088541c440004030210950f810280c0000f03603083c030b0501c010303509035031004016044c0c1604200c07440300c4a900c002e0041082c150b5441c00002c12890410240c14402d100c5400030440081030300c1404203044849405501840d0100c100305001400b643d55142e1000c40124080000021302d90204514000f03503005420500241c80081102411000106400c501807548203a5016a4010ba0000c900c24030101940c000400e10042c40300c0c180000c00c0e583c4d00358000301240d0803c0c0142d150700c980000c00d204100c148441c144010103503920707895100780d0300908001c001c0000d0700e0940480404403d20800040070400001031904680e0308400544090740440e44c0219240d684410512000549100e00641c07008441840c00c14036250010b200804164032a0002d8455000740161002070141100102d0602105820880a0003828071603540710b89410480801d0554525101a0805480f8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 911337185 1250 911335935 911335951
    0x50a15030b040f110415140a030903020c0a090603110d080f0a1107090b210d0509130608061803040f05060d0b030d0329060a05091f0c031403040f02010f0c141005 71
    0xc0d4107034400940c00340c242c23070300030b40700d8200802c83c3c102c0c5150481c01c0c92802001550700c10014140400c1d244101d41c4400300b901e210340e0078000d4030042e490402c19040b419200042c000f072800c004a0340d1211045001d045404240c0c1051140e40900c5186581403140d2504140080d6070358603260703001031800320b04060014088007000702d140c0b540c001c56161900300041d006810b005000070081040e071240300d680c1c134000111510803c601c036141d8148030344510703084c0d900fa13040d8160450081c072001800310455046454448210380d41d1882d0405000403a040320b41035000d507070381c1d8460f5800706440c24441c000515031385543c0080e5400c69554858203542d031130310994941900184c90360440340c0341c120441f407840f40300703051092702e906601001841c03107c144c03128001e81d42142c503d451b040700e41003101c0c850058400d859812228042100c1c0c15030300e00003100c0280c0860304500800000d94002d48200a00400914190721580b14645420120600e10030040c4265400341c48141c80b040078130712030070343c1005003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 911338435 1250 911337185 911337197
    0xb09041101141909060c171c02070b1b0414010c0c0305011a010212041a030606040f1508070305040b0a0e070b040b07050c010504050109140619110601050a15030b040f110415 76
    0x840e00c4609080b030121146038164000007400b01100d111b403d141303c523071813401441596540c0940c13401b203d10220a444800c01c2010f6401500c13600e10400341a40d0903900107480302072102e94070100445860f41c07521800d6480303405c40c000c0440401c4081c0542c100070300c540350040e0074142015000918081d61400101c0302d580c0c3c00d00003404042c140008205a16080d03405031a1aa155040065918071565020007450031140d440010b00910f00c2c15100d503803034041e44914246607202d0600385e040c1e642c1250003c0c411215140061403041d030076406400040241070803100b545880b8603000505a00c1904822001c00001c110135080003c00c00512142e51003c3c80c00ba4103141c40d040c000390000303402e80039603007404400e01840c84454032540f0550b007050341000720b0b0640c08040a080981628003006c1c00c1511405284004281c90808041080444402c0d8100e2120345c2c43c6c1200807002056030440702070b1f21039241c002e40318034007003a40103042500402d0f02055983c0c5240c2a078040c04411080310040500c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 911339685 1250 911338435 911338457
    0x1415130e0603072106050609060109031e061d122a01110f040806060a0303020d11010902211e12071a04050705040608010b0904110114190906 62
    0x2404540a2003110040c20240d038035601c4000c0002d091101c59002400500b0310301c0390407040d107600b900c21140e52a000789410015501c51000740400d0341d404407401c9001c01d00078141000010050075481d45001c20481409001150654508041c0c0311607009010928803922111003e0701010b008401501035401480380c0340030400e02000a1003c2600c9a01300030410010158080d04000c0d005030481c0350070460481d59968080d0490b130610340040c012040d01d03101d5100007a599052000102c0d007980d40540082c10000d08240c401c03903402c1d5281c4030300f003002d540720b01503040140c3312654440507041c0040040604032420904651910341c0306003040b001c1e03000703c00c1340b41a00702c400b040c200000141001010b50b0b4007141d0400c00020019415413628070540507042005008010908400ba900c1c2102d00b40b04066454248d54281c8900540d113031f41c403180750000704000030101150805007810604100d200740400c42030700e802641101074460000d20f980d0101004566001407514003520060500300704903e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 911340935 1250 911339685 911339707
    0x13051f1107050a030f090b0307050406031a181003020d050d0219080f1b06150a05030309060d0c14030703051b040621020c0d05041e030b13020103151415 67
    0x80c2e043c0142c01c0c8008140600c40c65881482070002420070921082da80f814444401403056206204c0c01002034a080280240138a0b000111100410300a06460101e680b07080700c0d00c0c42d207002900009a5414205000005880e60400d10100501500245c1782c1000c0100d0045d080c143e00c2e418501218942078000c10009515400751821070000710030342916126500c1001d22111200401100b82d0300c01c0604105400086004010900900342d6012245e80d5540040c1a07981c00342c0800c0543c410010b1214216108040d03003c0c3c812a05603141401104c80700d8400c0041c181d02c10344400b00000d8849081001c018404a480c41d64a690349002a26103841e1540003054004c54450460b00420f403070904078070f015059010b41c0c10804808054903610700410802402d00c0e031203846400000b16080e4007003404250b030140c1400840381c0150746480c513641d44240700c00d200ba10030301c4124141a170b6441103900714041d4a00d040090040c40580300507d010241c20890340090b00700c500b80f007800c003c0000503c14 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 911342185 1250 911340935 911340943
    0xe031203012612092709070603020408340608100605030f0c220b0a1202030105030c01080408070b100303120b01120b060903030f030118090803070813051f110705 71
    0x501661400303884d45101000541103080b0542c01a14a51801884200030701e811031100e4010300f4a0011250345580d2240d050b8183c1c0654481d03101c150b0850650002100201514810288a1041c18155084161461003c074840c1c6410407400103e100c01040341120444240c03401811240c00c0c0b2a003180b43c0500400303052203008240705868100801c41c596032020100c041085d040d00c1406c017400003a150312202c0c02030b0300210080000a06a20105001240144216410780d40c0240140c805000c502c4015214400047c1048440e043c00b00300c0b000110300030480950096000050565503189142001004460030100f21464036107083c000c2222680c02016640c10171125800c042824400040081c2140c0124102260140000140c102801030a417000b94143c80d00c21040c41d51200e640f0400c032044644200d4002d200b0700d410004078007100d0042c1c000590041103040061100314107641c80702c0c20101440201044465103c1c0c0d800e03940c175000c1c040c08000015200c4810b0503d15540c42d00f6540b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 911343435 1250 911342185 911342203
    0x50102070e011811070507060e040f0515040c02190302070603050f07080a1107021306170307120e0d2003100911040c021c0804150203091b010e0312030126 68
    0x40c031a503130303544101043d0158090701c0c07000e134124099841c0c01c3e0383c0311806400d0100c1c1c0202d140c4a40c2c83c01c0852200342c0c219204060141c402007902c683c01c15502c00c18000104036002c6aa420351003422285070569250140c0405103038440d902421819143c010050300356403014209d81400004030080009180e0701c544c2c103039804000b061002c0740081107001340c40c81d90710450001a4110714004099040c090450300480e0458141d04580b50707051701c00000054490142c003100600c40200c0002240305c1c18855149904180001480c0420a6000340d840c801840c0d042100c120322006940105a401c0c0740510103192500300030342c802d120940080e0380d0715021000c10b2007520b11851340c840c60142e00d248200104041502d00c4a1148031101c0205005000c1e1030040340d0440f13803041f030201c0d084140403140c02a20f01441407072008180d4000025100030700b003685051010304214000701d000d00142d904020343c0c1d15131909000c0c019902e50400501200502500c82c440441d61090394111200240005825113 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 911344685 1250 911343435 911343479
    0xf08070e01090513170904020703031b170c0304030912050f0106050303040602030d0e07170f0c0319140a020a0b0a020c0d02010c030503070509060a030509011a1e1f0504050102070e01 80
    0x2541d05c420784d18200c0303a03001740c80d040303604584003045003003c05030164000c0c10352611107400300c41d0350220400b0403a00c8a8414134001621310440010030208201c0e4405140c1151084c202801900e40703c81d0030140070151010103850650001d08607820002c0c1c20b1007640090034050f80594580b90400102035034a20844201c000804d46c1c1e200c4072014000c1c00d001007030151122418082c8100743c0c0511555440054500303c036441d00403084007200a10340000c00700040c00380307120307c3c592401c016150268a403011300074000e10b41c02080b4040f0016591042500050800c13904040d480f04461300000380382000f1400070b640200508000540583e0300260a200c0c060740c5403a04a650381d88606003210075000c1c495000341c0102010820103200da030550001071240000b6002041804a840170741100d48400318983c54200d82ea1081d020302ca0003810340810007413403000d029900951080748880002c01c0184080030000342c00414288a10340c1e06000b044000e082c480022441075041c231625204503116060b11203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 911345935 1250 911344685 911344703
    0x121510051b010b0d031106092803020c041409190c030b1f0311041416110a050303040b060108060307030312150b0309060106031d07140105040f08070e01090513 70
    0x2001e4070000d40080300d400e078001e0008040140249801381034012150303c0d01c01c032801140300103405a1400605c1001d061102886506040e450082c90445802c000d0030990031070107890300f10601e98446004581c0f031540f5003550050707075180040d280360511412998041c5000021070001c8c000c6012001e001007503035000071441b07400b5120721082d0392490100d03446a2490859241d400800d2024503d050004914141c4043c0b2184e510200c5060f00036000b12045410b54444030040e40083e03124036880d0035022903981c11a10340548030f0b00d4851560708203d4040303418401d80401c2103602d5a100891a401903025030003080a107065070390181440801514040c1e003d44e135000304031003004658418030005c2421a033855540e00700144400e441c1d000034010200403e00b40808001030050340382d526a080403020000c3c00c3d20904026400c64003029400440d4100321040c0701c0441d80c4003014035a08002c05d4180010611036142c11a286004076050340110b40440c500020410a01c41000003d030460b94000c03280b03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 911347185 1250 911345935 911345977
    0x150507020c0d05010606090e01271e06080d050a090312052107030e0d1b0215121501050703090509060a030501061403070e0c0702011b02030312151005 66
    0x403490680071024080d80814507125600c24001c0c19840401a2a01c60b521528401e4039001500d03d080d03000e21540360509502c0076008021904842c3d050070f03000c2c2c0000c0104200d413035021010403410385440c4034034090340d03141c204105250301080340d039460710010f00701305040c12002031000c1e2000549200c094407568144540d0b284c0395109000b01c481180b410440e002d0842c3c501d5020003510b40c4125075080100c1c0c580401e004410000280101c02c00b200e41d503400e039100c10030102080980b0040b10040343c10501307881d081403103c1c2ea06400b62012204200c12241d241c83d00c1c00003020303101d540c0a03075207040c40700c100a00360100ba4000c1000e0b003a20b40583d601e054a480d61004145101d5496101626952818101280b2840b090002a13480b800880072948035944448900d40d41400c151a80c041810b0204103100055000c1c000c4840400700a01082c180e110582c0c01080c1103522019004121452001c100802070300303040842c89280c1c2054419074510301840501030000d1084011202c0706901c10415 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 911348435 1250 911347185 911347187
    0x103051303051c1b030504110906031b03010e0d11060a02030907060525050f0c120318190e010504060b03160509030708120d1b0c02241303020906010c150507 69
    0x2524003c480704c09414140c01072a004000f46403e50b0115420080c160070100d051421110725805824000c0161900051481d403800c00d00c548a50603a8055495201050b43e5200a1000000da0703034031511001d0000e482c804119040a0b401030417100103910600900001b1280080c0c1c403015104182441e84c2e07540001a81e0440e01e00d0054004c0e002c11502000003020040089040c01170244240704450300001c2d000b00308400d1500f00001014a540180000860000a00c16209a801c40540b1200080c50360034104a00b141654002c41002c001804c0100010709091141100419031030f51f2031800c5041913aa41c0b132001890710344203810482e02186010032a1360038480d00b00100401403c582c40c1948403141c10f401ca42015508010381032030011100e0802010100e5004100d87d6a620244c004209900300700440c7c0301601489050658041c000c28046009001401c1c4080c003150900340e580c0c03951040201900004018904000c14002c1d00e0000500300c1d004003503c06002d10f03000c103903035582042c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 911349685 1250 911348435 911348441
    0x1021207121b0f05060a0c05090420040b0c061006051801141612020114010b21010905040c090b0a1a07021c03020105010501020111030a020304030e0a140103051303051c 74
    0x116900c4a020b10700c42c08002c01c642e501481e034060348503000340c03405503488070a4442200c06064500300420010080311106181542c422801160440030034001542c1e8100c001c0c0326500950800c1100100015004044a00821449078003081e074103007800483d0300303000009003240102003042c03001c03495540345010641c1c054880800100038499429482d00d082c00550250305200050550f00100406848a0840d01c18050000c01c071b201c139690001075174a49071200c48070b54040b1440c00d00082e40090000906020400b803140204507000c80450035003081d08091502c001ca9521038000c013850400e0085841c1c4541140c070048030041f007594050100105010445440b070328400a60048454208190300c1c10440171074115940030303074020005a80c0701c40059003202c1541c0c00d25102a80c081c40015a0442c1d85d8000b9988a03200b46054801813440d500490040340380354000f000b44800c2941c006020b543d140c07203032603840380310162041200713525610098254803030182800d003840e0050b14844a03d16146d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 911350935 1250 911349685 911349707
    0x807151d0a051c03080606070210110a080a0305040312050115032a020a03170f1b0706052a09100c0c030c03061409010c08060402090a080a0807030e0102120712 70
    0x80c002c003041c55040551040e424041140032000715100038041240c1f820716005440250780d02504030822030748018400d075503e0407100d8409006c1d12451072110009000c1030050107421701e0030348000c20903040c20b01d4050b003140b0220080c1c0285524160040004085007100b10420711083d040c002044003e06607a059125500d2500b0034100c0085200300c1c204950000d00703030700c03014025039a4205d403000220224114076425601003080d4108000881c1501d59140d060307404040544140c145021800e655030800d4800445060f45220000840403180c0000c04844c6840241c0c804e09540c40d01000e1000518500e18006000e41000661400340c0700b0008142c400d44042c64020414400c0c00b6520318000300580071a031880f041d04403486005c11108141400ba41d0003088150301e07001c03c00c0c0e0b01d00080c00020b4001e4412954000712070304002480354130038003015100c64003035117080341e50b9034a5082c003409200031011094110340c010450051807000d8041500c481c66400025082e84084070b04d4211030315400b80c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 911352185 1250 911350935 911350939
    0x405070903020a26030705060406020d0902130c18060815031f02040503010c050c060f060a170a061406030312091c11060a02031e130f0c0807151d0a05 66
    0x5110085104001c5800a00c61a14000040103e4004e16903005849018200c0c0c0205030358041008034000495580103000c82e1040034000040b448604d40000301d0451680d001541410790b0b80b00316480d00c5600c5a04c80b43c60301d83c1c0d11644104d05240450090002100030722040381009103608010581c2d40a2044500701d000700c0d0001540c248e240001c960082d40540303d501c1c4298a012001d8400e24021401e507698079019901500140e80e40604140544800901041c1c0c060441000482c17844104100080b0300d100400041054400b2440c2c2107040710704444103060a401303140d0401000d5500041210010181c24a455801d40c4400d120a480d00303043d050b84000b001c8840d20412409540000d10181300517881007191107a4550354401002c0748002da4002c24561850031061654041d03003403040340c2054011418000f40c0100d40c4800c00400014003003103586580c8454100462041000448007825910a200c02c1601c0e00f180b0240415080c80130150f81c22101004142c5255240c0113054000c00c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 911353435 1250 911352185 911352199
    0x1b0e06120403091410080f07030f0f0b270103080a021603030e01030f052401110114040b07090503060a09113006040c0605031306140a0b01050304030c02040507090302 73
    0x49071030b0203080007100380520540d0019209002d0388078030784208400c030948220f40b0b61045507100c3e9541c03503841100081c030071000d25403940c007143c0c0303002d0b035a12520011090490700044c40c980c4403401c000441168108070f5191810050341c002040079240b10841c1126404203000790356255011013a03040150b060040344050410031000414035030406190603030074009a0b420010100d1900c201c200b10f801c00d903002d1544c80204695565042114010302ca41042c0504007610b40d4000c85503020b00307669040b02ca420415201c0c0302444204000d5030b840355007003100d5003058150f1a0030200800d51321403008200e0518103444103d032000b8041d41100d181d01c1c1c26000360507100488003010001d41044594014907415011441400c131181ca804070726240a1f980c80002d6500062420500b01d4044e040544210a121080841200010014494200b501c01e03880200d04462a09058280c119251010300c00c1c1482420010000060b5108842001c0f1950480d00010f441e11140c404843c02015500b0013074108103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 911354685 1250 911353435 911353441
    0x11030a051206030307051b04020f0301090207020102120a080a020702060706020307020609060a06060806100203130305010608071505190e030a0807050607020a08030a0f0b15030610031b0e0612 84
    0x9481401030001d040440070414a81d1140d000303041c1c2e00e00c00d01002410517045600c46047c0091041480041071600520150500ca110800c20b48540d00070b80c010b00040d60f0019400c021135070144812400d8403a01000d0a04000c400c1c10090701803a001801803100c10f0b400038260f03045661300d0055451064020404646030310b814600650b4814080c0c440b13022074400c0b140003034a0f4000900406042d00c2c100d07038440e4220f440d101300f400310160641c90b0590541c0414842c6410364900c91168100441c001c400106841d4640001a0300b8040385800280302c50f10320000b0740c40d03001e80010456480170840142c0300300c142e0080320112900c0241d400180d625004000359130052008000c0600b91660207803055800c00d07140c000c0182d03541c1d50704040052901c41d003800081c1108406900c01501984000008521006100d00003504402801c4000c2c11001d8003000344001404c201c061a204885103040402c0704003012145500190034101d6064200502002440c40f117480396000e4458007020003401400b181 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 911355935 1250 911354685 911354687
    0x30513030b0406050c09221416092306070c0509240f011b0f0f03080f090f12090103020f0d230f0114061207030b1e090f0711030a 57
    0x810642d82035030310a0805010801444061049900c0081b0081030010046004120342e228001003132410b081881e510080d0008102c8003034400e5108100d8596103802030100c0540180031036885820200c1c0c0226031542164151401c81d0000c1082e250484450380c4810640c642103040d510b040d04019040b048080c180181214040601220790020442c60ba01e2480315009021020b407003100e50794001202c80b100c00c00628000e03541e40041d54011410040e0704400350703d480008100d1a0710840020303210000b080001c01c842c044050300038015101810020300080c00741030b9525400c01402d2094180014880b030107a01a034100d0390310300c05038070005456002c1301e44250010f04040820200442042d003181980c400343c1120b01d8070400070b03d52400070a908110f0410355084180d0141c541143e42000070341c1c3c440c50986000c9108910a5030040754500100051207040c800c884030441c4003842000380c0040d5980c0d1500fa50780c0c0501007009c101e50760354410000700c810b10765154a884040c00000381c1510b05c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 911357185 1250 911355935 911355953
    0xd0e010203070f0c11010813050d020d1119140c041107050105060a0e1303050405060c0c0111151501180b0903010c14090f010315170c04060803040e0403051303 70
    0x201c0040e191010002d0341d500040c0c419404040009001c802801801c0b4451b40c001d24810341c020104001c8405401e501d6500e461400355884529070140c1d210200c2c00001c03640c400c140313030004001f0001521840c048610752220700030404000400b07602c1c004068400d4140d003001407044c1040010424800310044001240c41a44511003c3c0c40075400d1200160090806410500450f40030717814110b180c1c2c0d40da840b1622150b410400403801c214007040001001e59400001d0405040c1381000351404841c170310005812064040d1203821240c2000000c440c000b00c421940ba41d0004c06851311500c42264000101e03001c101002400a034078010107408543d1400d480050190310006400030080d03044011416941c036030f04803109081b10102007065960030f0401c08500c0741080018140807a0012117104452100e941039000042001c01e030740d186a21101d420010003021807000c1d0f804014803414032484603240d20642c0074801c4e075510141c01090800d4031610440f120383c101006c0c01019261285400d00c11 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 911358435 1250 911357185 911357191
    0x20604032a0c090e0102031b09040209060a031b090b070b15060f0406091410030b0102011d0d0306050414011e05030717061006020304140604030b0a021b0601060f080a020d0e010203 79
    0x103254070b85885004d00b03070f20510840340120305051314034040f0039100300c00c101598010140c49402ca9000d210501450315003801a000306803d0b80c8001c11542003025100005505040d041410442a01d00800803031a101d0200da2407540c00550b14040c95850340e8200f48241c04028502d03800c030360001454202e0446000141007943c1166541c2859250b031001d4520440c0b2880c52981d900075180880c83d00028001da114403016a818000030941d0450704912080f40086c4c0d105200c5030382c0000c4080480b582d814401d1402030b020480d0104605080030035a03803400c00d014096141904400400d06040036001d4102c50024503006049441193708d039502c48400384c094054810107446204003040c0c0c00701d000d40204094420303613401182402d180408160058420031842504041d007080048003062603128040d00c50440808003507642c80c520180340b00b44c0001501c801905800c01001480b00030350021030890609424a05511aa06c540000070003e03c100b14001c280b00b07280c1031190240781030640103584 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 911359685 1250 911358435 911358449
    0x1308070608100f080c130b04110a12020f03060405060109120515162f100203070f09030519021c030305010510021204120c03020d06060f0b0a020604032a0c 68
    0xea02ea648860800001d161800b414509030810b0700c02103114107102045075031000e000d40000c1070340c6102a02080886813801d124460020000694002c00c0b40c03c07011021941c0c3c80150114501111901d42041a020103403147d8415038482020543c580e10602042001d002c5414001350021414074000d5030ba40101c078120020503900100084459030549003c5a8150480c1c9441c02c070001850942420048004a02d034140407080d0340d040b1410100f04080e24810900000040e900c9c207282c2c2c1d01030078203107988026504010304036909100161010801e0403c0071006202ca081c4007040c1d10014401101030400707143d0030034a00020205141d41900274034100c69090380c4c10320340e00200c648201c0e01c036803030140c2c2c400e070400b010030082281124079003d01c40103d0084071424040707511381d800074202d1800c0c000240c41300350b01e03440702740f2203a207484041d4002403001001039842c240e000e0202a40300c00c40100046c09110400c0200280b105070b003c0c0031040c07a4039181500e170451446241c030b4030f50b4200c0c90260030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 911360935 1250 911359685 911359711
    0x601090e210d050a11180a0b0d0504061805031c091401150e0709140a08060117101802100309021f03110c1c1403071e09030b0a021308070608 62
    0x143e0340c54028415010341003a07480074549080c220743c06c0c0c01e4485501d4004503401841d00c9100185004554001c1c042038003c10384080380904083c1400b10a54610b8444841940c01d518407080c0041c400008079041c0b0f00003c00e22a07818400026050b00500b0001c5001e815243c1c00011780c1c0c2200c0701948840b000300034a4941f61071a0341c88100c16150403c0468131344022400c61070090040d0310300300c03800200c1030000900031983d03940c45078060b50070b0660030f91108100d40040e03046035904400a10240004c01c840310020815039110881685280c0c0000c900640684815651000e00c07610a404c03141c2480d402a044809a242c603083c2088602034450700c44000a00d003c1180816900e0a011034040c041c0a900500c0314001d14031880000003180c0f4076803400e02024086188018900c14081c600c40d1000f500e030100c0c4000c22003040b444100c212210941044403481042c00012035145910703030000c100c1800161108902c0000d10001c08068100e208984210070b400580b0651066945124206041c008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 911362185 1250 911360935 911360941
    0x1b0509010809010b0105041205070506070f020a15050301150516030e100302040f030206091318210210020d0b09040804030624061d1002060105120706020601090e210d05 74
    0x610f080711103021100740040e108120030081000320652081c4081d01410655150b00d9441300042d44650014104a81522603c5554010b40c035003031880d40014641800030400500400f1002056840b05000381c8003034038480700507020785030700c40c0c400d840e45082c164403e0030f00080c2c0c5080103072013851500344240c0715a8050000e094650b100c0c0c000e503022036001a555441c2130f4250b50801895402000000d40c00c0803c800f41c11003400142d000304d071006881180700006407040e80c10000d41160203d0404045041c00062141d4420750001d02400807815460006032640b2440c4d403000050407034044100d41c03081800c01400300703100d402d100420480f031040e80100186000041c000055800c204010540300181680401965000d43c8240d080c4402c0e0089002c149401900019000780d13084a00c0001a40000018401400c00340c203007011005401004010103881c0000c003c4d5610414083c0c04071035901d0304802480a8401c008105c08c00200101c114007010251341c06512903045480c1d200d03c204d00381004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 911363435 1250 911362185 911362201
    0x1b151d04060b041503090b0c030402030c090403230f070308010503010e0703020328020406091a0103020c25030b071809060b0301271b08090f031603031b05090108 71
    0x561000c0b41c0620544a04080c688908881d00096250810040c0b507114200e0800184210501314410320546135160b0303c905050046c14945080c0400e1b06000b0740c5180c0c280000301b50040b811203800206030040305030340c042200c1100c1050260b2103498080c8000412180109a0442049030580b00300340c0082042080041d07006a41d80002e120182d0540c010007144c1e03240086030859106d602c4105a032007000b404d40c940c08581144c500307601c1000b400d559200c03026a06c0200e08504980200e091906500b086115040d490700c40c10f401c0d80ca800c4046500c40c00030590084001d8240046821140790040762a04850182407100804c4942403030354028100400c5503c0c96124620660740a0446141960b08142c0304001c0450484060b2200c500a41d10741e040240301d500402003162414119040740700468034000d4960440070b0018807041e0401604020781c078200105032000304600c000c1c001c07501c40303640c20280c00804410111141043c201c80c0e031140340640020050081c081d0a907a141e055941d00f40c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 911364685 1250 911363435 911363441
    0x7020418030c0314070c0603020304150e19060b10030e060901110405010f120623090c0a03090206070506070503240f060a0e040f0b0a0806090a1b151d04 67
    0x940240030030402c2e000500400d105070700385581406110351051805046449081542a0a5201d240081e0b0004208410045004840200c031002c844003442407811034662192255240b03810510729a80001030f0205000041c4c0102e40240f02c040c03d403000350300060400034042c011070340500d9581c0c4110304c0811000c210501c40c840541081d00c04407424181014011a01b01605040f40410083d107000301003c40060340c0301d070f44001c1c0542c000d41125000c20220000380c2e5810f0016041c424500c40d01000002c0c03400340100c0b010801240340000d50031460b440020f069001b0b00401504604c5134104010341550004011409260880c0e189590745400d202d5640000e4060705040e0b070003880c885c04181d42400d00300c3c0170307204a442070b0828108202003080440c081303441c50000501c2007500c440380d0400504207a4040d00c081c6c00380d01c1c090203003450b12901045d03030780500180040c448901014061002c40001103e40c028140c0b0321031001b00d24410b05401800b42ea220030000603115000d045600035807034284 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 911365935 1250 911364685 911364731
    0x30c03051e2e091118040c0e10030e01050703110403110a0f0e04030206060409030e011206091104210201020d110c12060a0b01022806020f0f04060201060e04020a030b0603070306020c03070204 84
    0x1c422280d40c15002010700000c0c20002d560072081c03225440020350f0340d9850360810b0b89c402019680025420a000002c1801c0d1140640450181450414041c10b94568002140c0540e50014213480c051010400401c050390040c1d0312800c1288500d590106980510040c0b040c05a4082d5080b5640340e111802000704503001100000c0c042001e4110f20020740d401040d00404c440440c800004500c0c1e41d500da81c00c25600107480d054117260700002c082c818030300c0400100b80c910724000014030702d801d440e0340007070760303402414044c00306010620311840d048840030000341c3c0350b2000c05050b6903408260154902c0c0d031a20144d400e20009801c0120b002e2240d40700041c00d4090b60380c11031031502000d0511036501620500e80c202074a6480e000c00a611100800c0f20052417041805051140d41e24508803009007100c6a582007491154116402c1c0400740e84c03960208001d3b650031140b941c1240e21004c000134600f04141d44000c00460011400b80e244007404809403100600a6500344511580000d8041c0f8030044c070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 911367185 1250 911365935 911365957
    0x2b0c03050c031302150a0e0a0e071b0807050304030b01031a0907151205011d01080607020d0e13061e06050304020603150109080f0d030c03051e2e0911 66
    0x38800900481c0400e0b60b143c2d0300e940058061a251000e00200e1741d002d510621086002c00d003403400341d44990a2901560b0000c0510381d07108001424031107030042000c00407107130003e00d9601c0071071044103004104080319402c0da40300e01100d40d20740d81c91070500c1400400f44015242d203190080b8011000440c1d1000780c2c4242c200101818019051000b90078040300b040e84c0721002c1211400381104d03030300c1c164810b482c0600403c41c2000084003040c05910205c9105030000c5c0d031160099014403074010380002c0d8241000109080400c4080c0c0142e0102c0c0c5d582c4444c010490203107050400006410f8450703102c43c3d080351140040101d500380c03502d500380c601c6d10040d20000e401c620104000f558a002c98916418420014500910890341d81d030740c002d00d080c00700c2540035035503044100307000c0d0720b01c2d050b114006d12400c850600380f00d00d16203c503043e210100501c8400340150210000204c00c004582802c03001040b41c00701d00001c07001d02c145d050129000902402e025213262407000420b60349808107507222801c070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 911368435 1250 911367185 911367187
    0xe09010b1e0f0405060c07140a060c03051b1614060a0c0209041e08121005010e1014131701060506040b16080a0e090105010e1011032b0c03050c 63
    0x107040010440d6010390200b10301a50b060001041c80d41c0c50900904190b64850014644942000303d160100c2c0c41c020350b06841148510010440f40390099600066150141052a118a9190900d50940c0409850b0080d2030044450090100142400319015991411300007403440515105118140c411041c0450124284884800c0103103000f9441d50350051140a12010292440111440c8c0e0320078800110741d150780100380d1901c480703115014264004418410344021038505400a4100313070841030000e001c0c10001c003041c0c90003400f440300044008203042d91143c1d104407002c42680443c10034014030540c1c03403420340360014500c01402220290744000b441185018900300c1204d0b1590301001034411950010350502020070071060192030381ca02d0580741e01c3d0070381403800c0800c410305005821072030520002950211031a25100f00850340110030341880442103000120301899030081d03141c00c0709004495010300f024180045008510ba180d003480c14800e205a03841d003901039850466002d411200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 911369685 1250 911368435 911368477
    0x21140a031403310807030206070e0409080702040203040f050d0f030e030f16050a0b0109140601021b19050604120c0b04081011120109410403021603030e09010b 70
    0xd00840c3c0c25041c11290b6000c090b44480503a14013544da00080c0003503001d41c1141c820806117075000b541e40010601d00312002c01000b0b001d0380d43c02d1841c0c0903002010740115400b1000908202c44810b0301b05110780c00204480c2d00b07416421004284c0100c009501c2d0010782052008111100700000f034404e000081c5003868203008081a4402628000314130594241c81030700c4075203000c03030b0040d1b81c030b00e02074080c840e008201c08441382048001518003806680c110362220110741c501021140700000205022140301c50302c05401200360410102507000b040c1d01140c0003d000038440e104600c0110194070490f122800c0646c1d07914403d41c80e00540c030410031160461107450180c500558490011071480c00c2d9100e0406105010706091001c2c26006043c11542d07408441941e4450509940c10302c4030b80802c50564900942c103400c5400c940102041c0b2007080c07100104007014001e00850035201c50104d402c401940d41e07030800400d80710888942d24065040440042682080700044503401303000c40c10b2500d0518 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 911370935 1250 911369685 911369731
    0xc1204080c19030b010e072a0b09121225020304030204090c0e0a0e0c19180212041214070308190e0714090106090f21140a031403 57
    0x30703100040301c40b55015400803002030f101116540c00303052100440051490f01e108050035828135000070708d004828078040d21601512510783c822400342d012035140a2074460780d0460346448801000000900c0000c50036503600021490481d1080d500c1c91207a00b1700000c8046090b41d109031b8154000c0c0103030030401060000d030419030400310b42c0b64030030748404503240d65404440c2c01440c8140d81081e401d544506150f800420200305808070394404840d1a001481d01d002ca81507064594031030307e615001440c240460307540b4035a043d209098042142e40c00e0f10710f0a403600c0741880d84040d18a00106070482100e0340d9003400402075500d12941a1154102602c8151803420f14400101449078600d840307a0403080a060706100c0c2c6030040281c406800da0702c007040c03820001c80e0681608a00e0410543c140104140300300d02e003040c401c50b40311815801c0103c1584074021603c940403100500428409108545200000134a5010060095907416040c040b000d60055603031109072020514000c0c4d4034819044d103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 911372185 1250 911370935 911370949
    0x20a030b071206170f0c01120f06080706050d1401030803130f140f0f0c010e01050705070b0f030f07030b01120b01021c05040e07021f0506040f060305030c1204080c 72
    0x8585241880c0d00c1e54120700001c4010f50300560805a919020b108000c10035110030021001001c2e0b180e009000d40490b800e0000700030b40e005a0080c00301d1515120340c0f01c0392910381d600079005001604290b8050039107902d0040d040342d01c92142101010b251601d4260900170084100741130325401421180780d40c03207040c0d0ba8440e11917000000d40c0c80880c00d000302e00c0040d0150b420901400080d07000381615614014426081242c21001c44020b508800e03081c141682c2c1c4084019505082420300a4a6500340d00701545444c50507081114040000950034000341610800b03184180f1440c103440e1101d94451038101c00340c540d0401c2e00c80c00320345034017a5501c1d00c19194100c615584010310444004120942e91880c0040c60801d080c3e0201e000010240000702807441241d6000c5004e000503c080340d855030710740c0022800161546911990b5201040c2e5035071b915081454000120f43d0b09000c800d84074103107a5201d9000e40d15184c0148520b14001001c0e168180a89007240c07000030140280c0e2041e04240024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 911373435 1250 911372185 911372191
    0x2010501030c12063c06030f0201081b0703030f050c090f090c0c0307080408010b090f01140609060a030b03010c03091509210e0f090c0a1103090a030b040618020a030b 73
    0x2030b43d495032180c15910498407044410740368000100300d00c80017149a00380c0440217480344c005015041207400c1c008100c1010358140c0e896820b2a00902543d00c008000c48858800c0c0c1c448000e041000403030030b0915030b00d604101009040b1002c10021500c860041600e680308000c500340e0007441c1095143c6140c0f80441003507511100200f03146142c41c45031007140d411548240000c8600c00305c04a000d02010100b442185500a0241c9800205050001d0320743c0c50700c1d005104400306000389a00300c80190f143d00b019a0540f010180540747c03030780700d1964040e010b030023141366242c040d6180052028850344a40204486033f508051038045603810000c1d801c0182c60194029030b5000d064800c184400d411540794490f01d000d240d55103008032104181041100011460068812503140d8103100b6424810701c11100c0d484000d0801440145450030b090f070560007641074041d0b21601070030000041c0500401414440d502c01c1100b0424180e4000c1c1c0103550b4a940e00c00030b5080b200a400c00d000040c004043c0c10b030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 911374685 1250 911373435 911373443
    0x90f090d030b03100906020d1b05072607030210050f06010c020d0c24110c13051e0a06050a0b0a050a1b170d0c300603050f0102071202010501030c12 65
    0xb042456000e440549410100841d05e441c6d00084ca9030323001b021481407044d001311101340100e00d5481d21200130080e015004020b40300982038000c00b003902c940010b03440139106100001d0341c0c1752042070078040c1d1100c034165115a412410400012800c18500e49510300c05c810584030345400300382079004d2146001000c40100c3d00c501c0201004501c8803100140c0001a20594070b100f02d42c00c0410000030184020ba2140301c000d540f042d07130344031b4040d0b43d820707400c280c2d4607207034500042c42e82e4641d4103c0c1c0600c0c10313903041d9200c6600c040050004070081504075a040d0b4005403505101595a20b4500580340304401200b40003c006011030b01c40c075841582c0301869940502503424114609444007401000704644000084000081c0c580c0c0401d81030048250704011030900102603c910341b1017011905860040003841d58840710410301d4080e080e8044c502864224048a1010508141c07041c000e503c8a001590004819040074400f0751050060300d0592785c0c42040900d13603925100c40781542c0101444104c0b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 911375935 1250 911374685 911374693
    0x3030f230403050d3005090c040c0216050603010f0303030513060c05030714120601080618040c170610050904060f021809130203071503090f0f02090f090d030b03 71
    0x40c0300460140d018001071400341018100e103110ba044054052032600010030b0581a4000070700e1250080300308000c24060780303010701250315550310300c81c0380c00d0060305442c46a101d1310307200d60210140e41c00110320102ca461842089a02510b5804201da070380000d20540700520300c191024030009110340c10442d001001070301c482c08031007607039501c2000755001c00b03003600c0000c0c50100c204203101c0e501c09200c69000c008200242e1520054107100003101c13000070103c82c10b200c441c8001c56000e40301c95580f4514a08440c0072042a4249071074281040300e128801da0000d0102141e40801d40940420003500814440840d882914688024040039003002003050311401e07541e1405000b03144480c0010121080b1740c4d42c407542c94010090420100150140851101b10380b03040c2c0b0326005850010303180c0d042e42c00d40c8040446000ac04c81d4120090900c103c0d000f07004241501020080080c038240e400140c902c01c40b0128103035521414242c00044003290118200d0380f154a15081d0345010b0f901070007a150020f804c0c0c07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 911377185 1250 911375935 911375987
    0x20d05011512030e100c0204151805011d101401090b030c0306101e03020319020f0403120215130f05030a0e1e06071b0801090f0201080601020703030f 66
    0x119000c0d03550355200c40e020102d011400010550310181101945108803042107003003035250743c02401800840710003400b4039500e1400a40000c940e40b6801c009100e0b0000300f81d4124400500100505407c0c07040c1d618440024403900c54441405030b24a10504116540030203851800c1d202400700382e070307010400f0b06100c42c3e810041440140800190300c11240d094520743d49040c00401c2c03142c0500e0300d4007004104543c201010052080c1004064001d05846c81d0158030b94580c02c0c80042d03d1100d4011040302603100081d0600d422220202600c1181d001c2c200c0c42d072910200d90800da80b54098444210400810000041c0f400303900c040f40501d8007400350301d1101c0c0c2c807156695084e146601403411070000c0340318000d02405528200345400750401034060140c2c207119905000c19110f00801d84010140590003d202c0140c0f07850310707440002001500300030700140d06141084200781d0340501007a8002584000000d665500010303a0070220382d0305588192030b85440d080300712941904003803210b201788400190 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 911378435 1250 911377185 911377211
    0x110a06270b030a0608190506071413080106030209010b0705150a1d061609080c09061c0807030e030a2004020408010501033f05180402070f170412020d0501 68
    0x7840c81840b014000207441c0d4217014401d40362000c124000c94440009a0141c40040d6000c5140e0b90001d01d541040003a030010340e1035001150185d040641f1203007042081c00140c1e5201500110200d90081e220b05425036200c1c00301e401c2a201d2008081d1035079101907014504044444000b590001c00094009280018201e040e0b84d00b044010b024649603011400780800b45001844481d0130043c02d08008080c9481c1a50030364454004a164038450120007001070540e4584078006503401107840101e290300010740c540b415a54104905c15800034141480f81d080500340001e1a68400340c00c108100e4800f525a0080294450307800c040a80007034003484002408030003401490b002e1031050400d0034080e501d034540c1c440041d2a642c2030710340b030f00401c0c0314806011003546004200030310103207000ca83d2543d00c22092120b4068411032181c00920000d41c2c1d80c24060640030000c040e81c42905a99911501100150281d0103940078441d01d101f004040000145002c00c40c0b88012807199001203445452651 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 911379685 1250 911378435 911378437
    0xf010302040b160212190f1a040501021306110a0605061908031e09331903060b03150d02030c040c201507082e03110a06270b 55
    0x41010003c0b644409070011450600b240e54800140b100c020040c0d07010b0790344525101031582d100500149144c4151070103004a2508145a80c50102c4060b02c1e542018a0b1140c001e600031101c40720800c41184001c40d0f40ca2003941010035007181c49005101d11035040c1c45940003028041c01140c1d01a140e110100d03c0c0043d201710200007003441e01c1c09162500803080344201c1024080100b01c0c41441d04011401465691103050724412035019001c2c0c0f80c1d0302042e4004040c018103e006102e2003007010441c4d1800c0203002d02c1d1500030125658003403080d2a0f6446180c0b80c540000d0720b00542c00c1c80110000e546905186548001c00f90006044480c50690b032004101112110403007070b00000c0062130040d00c0c99582e8400b00c1d0122119500800708034070020501980b100c2c025007030a04125446001ca6501d600074030900301600e03000800da42c828074546c030214011210301e11080f40c3d00b0706032465500702450100003c00840712030f903c815424038180c0040060030041c98040301245115080301040c8282203074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 911380935 1250 911379685 911379697
    0x3240905100f15080a0b0306070807050708030a090312140604180204020307090e090d0504170a061d120f0d020a050c010216110609010c3801140303030907050f010302040b 75
    0x41c2c58019548403c070001070107200d005005c5030701c0c0303400d151300021640c03000211558031802d20f02c0c00602a890350001125a13100700000a420b811011003800742c01d804d00c3c1d2003c0d21702d070321039120140010260040281500d0202028045010244c80010102d042640101c03400c2100003021442a40c201d500040480e0002c3c0c90b11000500d0411040c0300341402442596008080b40004002e001c840b690700034894817076070259948518800303208684003582000809a030580c82082030021060103080329881030041c0c403010007141710300c0d440708090580c0a0704440120750802d606900d8003031a500c07428060740c482824113040043c100862000b8583c2807000e0290103610340c01000102e83e850515081c034640204000f4491030040180e4802682c00000502c0f41580c84203c6e1240c040c02085190301d0025100061798162641d80307a2b1010701551441468180d4450002c00d0704c00403056001d0665134081124201641d900040301440240340060322800740c010145405440c040e200c3d1500c00f8503403c55 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 911382185 1250 911380935 911380949
    0xf0405100e041202070b0c0d0e1206040f0b161403061f08100902250c12050313151b050717010c1106070516230d03240905100f 56
    0x83e05110354080d0305100d80802040c5503800a401d20507060380e000e885a4250002c1c07424020004080a1603807141844900c1148030320f000d5592a02d854107000980290301c000484040c00c4940c00a0085070504c00d242c0d500782c9065941c445820221801c0c0d01c6203034000351680360b001c00c002e0785c80000b5050b031346c41c030607000c480d03c0c0e5802040382010883c0d030803240500d4020361003590041c8500070319201c42885040c0724040c3d4204081481c02c10f0304000c82166190f421004200c1c040c00229018001c0000041c410291418015007135a13694090702d03404002e1154105002800b4078003050000d070b845005420082e40503206494902e40c0d200b18204410842481d1144c02c0d94491000c04040da80000d00d04e103078603008401070101450120401046c611844240000184031540c0f80418086d42d056268124101608040c0081d403550010070380d10a24454960300003400d10340c00001e80b555192144584032500e04440c5040c17800c140401e0007030b00c001020005008503d010014022910160540042585c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 911383435 1250 911382185 911382203
    0x71a04050d0f0305150409151b08090105010807030f0303061e0608150307151701030305030619061b290108010b0d050a03051c1a040c020a020f0405100e04 68
    0x122001402c1a0100c480d5141410724280c20041c281d1742c080710400140d00c04075400110480107162042e071100345c0c2c600a000715480c0124004c948025800106140c48081d1034100b85a5100d00c0d850f4240e0341c00b40520142500070032400c000240451000101c0c0601ca41408150140c888901c074440040042101a440006141c10007516820042561b0802d0002d2001480b070010000800e9035184184200d200ca05040900011a28421002956900d807192260402540d403820000c04641081d21074030311580c104d04068007443c50b544c2d0072400f00c60294070f920313608001403683c1400b01070754828203031805440400d03540060a0441c80300312274a204403502499550410700054211030f81080a680101c29003a07007100818000a0380c0c1801c0c0381d01d80b0345035940320344e480305c1030b44405011030700042d4041c1000d680d041807101e210042e100c0490140d03010095038080c144101e981e4070f9409806500440404209401410190040390703000d010301801c5442c2c41d6071090400c0103c0310844080c5c4403008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 911384685 1250 911383435 911383453
    0xc0307030609420c170a02070c08070303090602061519090905061008011a040c050408060106030606080c0a12050405011e020c0c011418010212070f02181902071a0405 73
    0x85200300f000514803500408101c02201d004c406001c03203060f410b60702d1003115224001490001036404071950240d010710b01c008119503404190b1703510f0740240011000b00340030b21008100c15100240d918404d840400c0800e402040a10600c5516244049550b000000c2c1d0711021601c00003500400e10501d104d04010001450301c511149003500194208401e036074188050520750b0300c10031001c09483e44040b1000100320101c000c6c04e4960f8419544000032034061000000b4950350141d0010003154050f4503900d0056444051344411403080544803c041a200d05150062001c80d03480b040d8814419400000c05040c541e0600360f000d42340400d1100410740000350304180d803030103100500607910300707007485811610945c90702180c23400f0b40041c035400030a0200b4802440e81c030812407403004404020449903100301a080040181d0a400c00076401a0081042000400060040d040c41014888420300d601d00d04400d01001942c0b005506441e0014810303e95104260030a8509001c0c80c45103005004140d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 911385935 1250 911384685 911384783
    0x3070f0c0f0222050603010b06040506090a0e0405031902011107110103111305120f03091c02210d08040302030a0c02030a0c080304050117060a12051e010506120c0307030609 76
    0x110005c041c90702990500610941c01c1c2c503054242d03425a0400c5a80300d849070480d40208a004010b030788440350000c0c03680107200c18400c0100091001c0c8061500234112182c4514084e8241c80105c00554001e6100300402c0002c00c0183c0c0d800480c52034140b40100701200c010100c0754040d00400440030700407001c46810031061030652014002c0c079041c040509100386041c0100d544901401308228000e100d400c0c0840d0500018110704c60240e907008001d000d08110848030004400c0c1e010142d5030340c52080303445824519001d000c00c18840d55050f0f00039898140c0c592400c42d88c00800c45000c03a09403003a1001c0c0c030001107814510b403020340003210065841c2c600d48400141202d01c0e94004c0201c884c0040b0520840c1e88ac3e03001c0d400700365070448105000c40202440c005240102d207000710040c008804c10028038100301908541d00600044a2916030043d5000d042511140200e500c25403544c040034007003001880980044100602403e10040c1d0507414840c5031134901840d030038440704559a420060248 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 911387185 1250 911385935 911385941
    0x12041a160c180e06090703060908040b0c150112020901180e190506010614070f02010504080f0a050721060c180e0403092111040e0706111203070f0c0f0222 68
    0x85040d100040413641001e500c02078441d181c0d8000900035a445074289400e0000c10300c2124010805c10300720940d6059032210007621001e41c4084915544100f40000075440700c00d20703811515035001001850a40d20f07205001074589001904582105c0c0ca070400c48201d00414484a90042e1111903107040e02d203820703d402420880141c002d90305000c5012030501e46007035a07034280d41e0110350103080007500311007074001a5031074022580310b01d5140c41101c0401c0182440400c140307002030b01c144121414107458844c1d0300401020702d42c03d1016000701304c580c0380100d50944c22045442100b42005001c45d082c021600d51021038940006400a1208040c4020507138045a071100900d003203000458545d002c0e814a03100c859010170040d01e040c60b032000b0400746680d543d11401c14551440c08482d503aa0340d41078050f00d0010000c2c00b07207410f07004003d1010400030200701201e100301c01c20380c1c5005410000303400681e4046107080e401d44025a07405800b0340181c8503104079170302642410080203d6550804050415 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 911388435 1250 911387185 911387201
    0xc05060a0204060c0816120507020a060504080d18030507030506090c0904020616020406180c0801080f030301051002030903010c030f0b2b150c0c0512041a160c18 71
    0x2940d40704010400c52190b01002e0703071604030391140490381da0b040741c411800071851480300c024100411380320090154a03008001484914070079600c60365269a40d510958550045204640007034204038112a200c510800b0715400d03960031240d003d1002512507c03058075150041e041100c895002d0007c2c00718042c0104036086c0341d60b0084a1303c9200c0e10b080e60100c1d800e4060300f20718000c41a41c0d01c440d1801c55403903411100281001d08c034803800246d01c1da1400806007000c2ca06071070118001b58004105000081111142540700318000d5207180d00e4103040c80808045c08130003100314042030120300c0c1666000c2c000c0003d4107941b50f42c0070074034a14042201003115248483c091040180c80c00402da02d451889010340120381c0742e0107082d458044c0b030512044c403100305c07031019030790034a07140c0344501441d0002010311199018008941e062400c0e40d013103c005200d00d014801d41412803404000d22002d44c000244400c0344a8441280001c0ca180d560381405070079034200301384e50081081d103080e00842910803004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 911389685 1250 911388435 911388451
    0xa08010501030c090507021f1d0a081210031e0c05010e0117060112090602031617010e0c09091315060e0a020901030603050304090b0103050109060e0f0601021006060c0506 75
    0x41d5145a45045040f02e41e40300d0107158945420020318094001d03c10038810744100707844d0300c14000134210780307400505900d5203101d80581d20f03c107207906030040040c4070307040380e0340c44a0b00f603241502d504039582032440010700201c9081908030020000030110000300420120200d0760302d80d9495145052031b03280f0100d070000e0f0304120810f0241d290980c0d001c24080c18160310b1104400303403501c52400407a010042d600000d0303003150510300000d041008a5004502c10000510044a4aa001003040b10704841c42495800d42c411642c0050162021510f80c6a41010052078400c0c45c007000c40f404500854401c5074008107041d540607941040c011200c49201d900c02101c1400c124050400c00c00d065480c4000e030014048a502003811141a4040d0707010a02954000c01101e403030f02d94910508000e0000a502a80040d051900010340c85055018000648003401e020080c03903510340301040c00080004122604600c82c1071403000402100b1300c10031000e48001d9031901490389031800c00d24a80b01024000c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 911390935 1250 911389685 911389691
    0x160801091a030312090118050c0904020f061b120406050a08100f0905240102030a140f12070905030a020d0201030203040c05040c09030302060f010e060d062a0e030c0f0d0804080703050a020a0801 85
    0x4000361020a548189c1d40b4200c0b02d191190b1118004526000380c8102801e8002c0703000243c410210000d80c0020701c1902080040365080284044900703101c0c090b5100700c6000c03d0042c042100072500030080c1c2680007034003480181d411582e0304044407504107654000038203640c1e0342080c0300e12902001c15800007501d00b040c4034a800205000000d64034880c011102c420000621046983c0c00356400458041c00c404c41c5201d911000701c9800c1000052058860f403011441d04000003540b424041080381c88550001c1060514200d05d40040d000382d44014000c07100b540342e20070f003c5a655528450030754265000c0c0d80e0500030a040d840c0c0646000d4001e0000401e04507440e004200d20007407640040c1c0c2c404010748140c440001c4034034040c0094040c1c40902d5110402ca00c042e00c00a039070b0b10b00d94900700d00465940442a0540700141511010a20740c12034020002030500541070505040e00d01d903580c407540810746460f548103842400c0c00d1040d0411100303500402110b4081d4513004800c3d4000e000c600d0020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 911392185 1250 911390935 911390981
    0x30f1b060f060f12070510270602030f030627010609060e0a05010f110f060411041b1b0503030f0f061002071214010e0d0206160801091a0303120901 65
    0x7841d002141c1d0043ca124800c91144481441000c0c08401c0045ca0007500b24074080841c1c44e4080d10007901015208005c4c2c3c42900246d107020042204101103030341c5034014502c2c05402841e80e900c03e03480201030700e4010b0181710340c0101e2581e0340300300d501c940010311444c0e020a5050110041580f03600e80d00c180100618100140791035941d900d510000c2b00c009080a42c19110030400554404030409008052409941e541c0007040d003001ca81188901d10485490b149a100c5004001c2112001001e403504150351208514049000300c51a0441100300218002c400300180d403001e19613441181d032907440c9280c1400307000d0084c0b5105803040d0001030848030132100709450000255a109288544694414044c403014140250505030900a060102c000d0001a025030511959488a141c00c00010310a0b40d00055500b040f10a90100c03003222a607600c01c0c00d0b4a80707001a80079040b1074201c00044501000303286082d070b504000800c811100d54520b00e000f0701d0035426080c01c540101d42d43c120101c08030048 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 911393435 1250 911392185 911392189
    0x15060602060c07031d03010b06042304090809090702030c0703060209040c03020405030303041b120317070e180a0f05160e0301060605070b04050a020402030a0e01051602061602030f1b060f06 83
    0x46009a40c540849940034117074000001d014001807560650230540014010031810303140000e8034180c11400c1c002c10084e041d1482403008860b64000043c100c4a0309200071046450004092500000184100c034100400350b844c0a08002441e8021a01c0030750001d407841c400e0404e40907032040c80340c480c10300314141480c0c107000c280c403440000e00c0140000d28241c1c02808450084d01700ca005021601e242480d2940345150181030805000c450380504980c1c14001854070b03205a03c94207148102811943c48103201108030080d07250f000d4141e02005841c0c2e2044031904205200b4144990700017450b00244c0c460038503002c1d11601c100d03100280070380d04000c01440896002800c840502b0f51000300900545e5032402d04a05010007810000d5109000009100c810203081c0c0004986000002c000c000c180c440850745141c840028144801680002d4002a020100154088160342e001d0058900d800c0e0441440c05c4a03a00241e090b030045011780d840101c441030100405c50340440c810030303105550f040c0000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 911394685 1250 911393435 911393447
    0xd021201082413050109030909140606090103020903030d150314010c020607050325020c1203070f03030b0d060615080a450f02040e071401030c0c15060602060c0703 72
    0x1614101d20880c500400c2c94002c3c0c0c03168901d8000c1e040300c0200030769481c52800924850523407050284440c1014202c000b103502003030b4001d000319001403c8901d0140703c1e40064010f508090400d40d418003003440b05900c1541140101c002c2214070440c010001d50840c980060343c0050500000c4140e89000b004020403600007404c070303800c101c040c10066101d1351112204150b0f0f1000720444008100d0b04080703036003020380000d04900d070180c0842c0c21181d0840c8401946641c1d00a0741c0000d400054000990004a406a4091618828064601d4601b020749440b80c5003a580140c0c401000b12200e441000704080c1e21102181d00440c1c0035505101b0031616120324010000758440c1060200c1e5035140040144c2004007800b403400c0076029038030300810220b09040c6002000d4410581c000c07410880704220308580400c110302641c48c080f0703c024a500780b0000450080c034205603524144810490003102242000c83c610050282d142c1c0049846030074810024200031001e8040c11010209014420001e90058 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 911395935 1250 911394685 911394733
    0x212090705180c180a080a05071502030a08010308250302030738060111010e0705041407080a02160803010b07110f03030904050426210403080a0b0103110d02120108 72
    0x10a0380500c00041300000d941d05203503501c0303064244a030300c14041c1000004100e2000312107000110030240c4070040020380e120b10a4007a808000f82e0310360b00500024540d4009011103529051042152508102e4003145003070700058180e0140e8000705208040002850342007601c030003c40f5124418104c02600916030800c1c00b840d0095840d0782400154259101d00c80c920a1003c070310f0000d01c450704810002940381c25040c0203046c061401c140b207031a103441c0c0e18541c9600804d00b56035031000d2940c40c1c10b07050000f07400800d01d0300c040703510700c1c101000402c603044040d5001c0c00e454494669101850310700344243d40401c07107500340501d406100044050750044146c174a200c5041e9404601a0307542d10f0001d0307542400c17511000d0019500010012055241405490180541070080e0f24452200c5003403c0000400c5800400041e0811b0006d2502140c0b50440490320f20103060204611200380b01c7d41805800c484000c102c0c5560120300542c41c0001c0346402401400c10030b0150040746000410490090041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 911397185 1250 911395935 911395957
    0x30a021b0f0d0f1106030a0b0f0402070b0c130803040308040914013002040c1e11060a020f07060603030e04063212060708191505040f0212090705180c 66
    0x75005400340f00c810384c2491942000204141d940b1315024522a0050020045642c01400400307000d2a05081c00d10807104100d8004821040c1f03079480449080c1c031a40003026020152602100004801e04108080d00240d403143c1c181648890500340d950f001c5407185550011400d5928004121002058160910304691403410845447e10011022150512180020f4120780740c0690206030540c81001204010521000240d043c501c82c001102d0ba0000c0700345d8145680c2041012512913102a4000d0505080c040c2481c1d003440e840b6190501285c060754000d40110f600500119154902441540003409070102c0e00d800a9041071441050a45001c00c4031030411789070031148145645402c40070410b8a0079008807801480c0070130700105000010303031f410701c03040c400d030340412002d010741d8028204485985506041340510b464104805000407000101e1345903820010990040d00c50700c4118460010140100700d81464803080c4075001d1000d504070706030070f01082e05100d0448110307800c48507486e0803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 911398435 1250 911397185 911397203
    0x1302130306230117120a0e0108060a17010606030f02040b040506031008070b19031b080a0608071d1e150f0d03080405071707060503090708030a021b0f0d 67
    0x300400300c403504007601c004286201c0b061000085220040c05603945080004082d60580f100700d022004c03440c00b55200c60404100e0071000c03900c1c1d40d4800c0c11251790141c402080c4441456481a581d8207021000d604001079944800007401141d40602480c043c025214008520f028a00081043c0c0b0780194087d140c49400004041107445440c02c0901c40681604419900040c2e0384211510701780e0300284070150800756480b00d54030518004e20689506400c621440300021081c1201160641402400340e8007495403114003160122003002044060007507081c034003410a0961726221503004008117101d00040c45d0071138200da080c41c06940039801c85c1000c81c42c485408c0310032001440c15184c440b06181c200000307151140505034844039540c051405501600d50941e2580040c585981e0240c4041c4d8181c2d101c0382080020328400c1c4000c44d40880c40d54181c42056071241c0c809801c691001a154005038001d4100e400d200d2498041c0340c800b89400c45120900b543c014001c00c150350714042c800b0b0203110b5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 911399685 1250 911398435 911398451
    0xf120902031507080a0b04050105150904090b070e010210181509170d0b040908091e030a03030516020705010f051c15060207080c060d0504081e03061302130306 70
    0x400b00030707110071800107440241262900900080c0384840c00c0311110152030414100346800d080a1041d00e0681d00007070f154110160200880022039405580c140703800035500e1280e10040380b010308006004841a9441d402c0818100c40020316024120030412100362a0420002c001250340050324030741903001b480d031a010280031840394014114004081c00403800c8900c001040c80c0200d00030200c2880020003040b9900203c014130081b10203010008081034000c001c5c6103402d21b88042e41d46108a0754120402c141000302020034141107002804030080303611541807003044621000c1645081c08a0310051003c545814002440003000c0001c09091220004110800a011024020b000a40a0001d000110302403500150b0841c1d14440d03032006004101010480b9900441c41a071145030080c103417030518841030340f070030014440904111081da1003004080700060b1408816030202805c0080f9a880349080702c188a00144400b0901980364410405143d0021280a20000b03682d0040720008a000e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 911400935 1250 911399685 911399689
    0xd0305031e15010f170907051206040c0b0d15120201080f04151a0d1a100308032205060a022a100e010204050604090b0f0609030703110102011407020a120f120902 71
    0x145001c01450180317107942c02040f84c0018005040421603800340c8452001280c0104400e49a9100b40c500405001f4641420421010a54041e0140b12409403001540c1c5041c040055061410340d40500d002d0010401400b06541e00700841c00da00c040400c002c0596840e15680724101c540c010072051003802e0352003001042d0038a1344004180a480041c151140d4003541d42825050304030503450540b051040c82000a46a4141c0a07415080f203500013042070540d1101001c449103500b000d0341160901c913a056003680403503402c021860051006001c01a911030700707200791540c4004500c0030100d83e01500c80d2201102040020140c0d10010b6011000420340c42440100d0b01a2185910455102c1d0000c0750200c1c1e031051a0f8040c1d504000c0484544290601490074400c460080c0b0113030550607000660204042028118020408003052000240c00b0070f100c00003151100e4161510781c01a40f04640d21030410001c1000010715611034245a1032040a5543c010081008041d00c0724400340c075801148115 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 911402185 1250 911400935 911400947
    0x90703090309091404021e0105090111030706050f1803090105030601080a0b031c110c06090111070b04231503070c0f0804062c030a0609030c020d0305031e15010f 71
    0x9080000b4040c88400341120100303130030307000940e02a40325500d001d800030b00121459008072039404041c0c650034100100500151000b04040d1038005250104004080016850f445414816441d00d4042c55450038885003c089551807644c41000d1a0f00c1003000d01256a040010369901c04400d1825a42d03030b41d0f803108080064000c00f00401e03050300c5810b0443c0811110300b81d450b030010302e10b550764082c07505815900c40c1c0c1c0c075842401c01c84e4100c00100300c803c0c680e5115608010000c5481f10484001ea6601c2c2c40b03405043d405a032040c044540c0c2c0d0032000c4140003a40c0c900c107401003c1280d0086c5030061114030120035100c0a850f590a01400350418001c03c5500b42c011a08180c0000380c2c9503d030381ea100c030007810703041c8864094050050780d44007085103001021518480d240e0b001e0b000340415001ea903601801001481010b80600c0200b403070420041e0b80c0c41840468440c031075940c140d102d0400b801d40c440310041d18000d21500810180030403040c07140100061503215000d10340410b0200700f10350140c800d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 911403435 1250 911402185 911402189
    0x20408030d0e1e0d020d031103040204090c081212070f080c030924060a0b03012d0909031e0302070f0b0c09030f0a11062503110304060801090501080c090703090309 72
    0x520f54000c07030410752011001c54038950444080d000e442034040c0f001400c400720390540d1401001d1030030500200e00542019402999414030440d09000e8450b1158a0649801842c0d100399510403000545040e4205a4408650f005005400c0070212542c01c060050b00544000b45040c070244004030008100d554100b20304109a0200741341d61450b03100321946500c000e2000c88030a800f81e10f4031800011001c400c2e008582c120751108484203100318a41035020759a101400400500900d00c02c0c0200300000c261260502040c031a0b15200c0f03600e11124595860701c4a090408003d240c414031010b808202e401101080044d80702d40004000d9460802d031845900540708074075007501c240d180f500554080040c8662102e8007a015540700b08175184100225880b800c1d0b0b4180c046030b0301c621841c3c03410b5039611150094501c86e08008500c104018607242c85e40d04594405000174402c000100134440082c403415001d02028406080c1d60341c520408500d000001805400400d0790b0703a8581010700d84203c8080740 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 911404685 1250 911403435 911403463
    0xc0e031917040f0503010c0212071101093201110705060c011104120b0c07030527030d090501030b1903030c03210218010f0e0613030b0a0207120201020408030d0e 71
    0x500c50f80c48078100d28002c0c8242c061640a907207420b50001c3c103103000144c1c1415150f00caa02e1503281c07043c6969440401041c1720611818000d00f034201145241703011510240c00701c032070101700103080c400ca4410544c0100d004c40d650b040c401a004004900c44005c1450400d5072410b5661070340c0ea80700c41440f607005090303090103201c081030045000b080404c40d00200504060040c07903406825252090b9811251013040c0c802404030700e00700240c15500066030b496001d5442204000c0e00043c9003507000c01d0031700d034039605040c002588610040c0240c0d038241c45241600072042e110811a064041a402d00c43c4000d0b0101a060203500e09181c002c02d880380c400c0d022840940703031180714136403041c0709100080e404c54011400049500006c1e101c1035441807107103030104a480d60703c02c42210f04050902c2219400700d0001c1c111307c1c1c921080030011900b449007140c0070b40341030100180e4420351070401006145c085140c140031079004200400603a41d0001c01d88441d41c44025000803103d02c020000c9207840b0380c10340241 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 911405935 1250 911404685 911404687
    0x901030c050f0c07230f040902060705010e0c180c18060d021611010e030601030201030f0e0a050705030f15360a030909020405010203070803040f1e060c0e031917 71
    0x550654404100302d1300b05c41c86a80c0d081d9411104042103a20150301000681c0c00640720441d05070240b8040e000031040310b001a04403032074284aa21603c1c00c0d07521000c1004540d81c0725450120182c100701d54005035400d514a003240c0603050442c0200103900c1000b0102ea1030101c2085141d42965841d411512403020243c0115512110f184000c030540040300c80664040d4001d01108007554000c0140e6011444004c0180500360300b1540190000c140812100c03511560300d01040f800290100041206a4010300c003c03e0040c0c901030416160115401e009020354114859035034035003012035641900481112403009804006407240c5400b01d2020140007812003080c2d12581103e00d010880d01e43c058000c1d41d4000c1035075203800c5040181d10030b603c50940103a03c00c11801d00400cac640005035070420b210301c0030f01d800b40301181c607410403420520484421070440307045482c0401156101d83c3c1100c040c542489000f0340d050308006502c030b5002810b800021129554042c08000c0c030104640b402510383c56500e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 911407185 1250 911405935 911405947
    0x6150703020f0c0a0b0715060906170709090209040f030e0405010b13060f090b031f17240105010c14030a111b06042702040905090d080c0901030c050f 66
    0xe544440449003500b150007401002e101600b0100e440c14103442c2e1090200f8900081550745d40310f61110780c2c1001510555032880403448107800e0207408004c2c640c0440c8d48043c91503103400c00342004c0c610b0b4449801c0c545009034110058a4980c3e00c2e591241d0001c000d01006071150600b5a100041c600c0c03003d074054a040008100c000484010b002e0490400205002c0944c84070410b80d10402d0f0b00c1c1d001d20105020180c00c2043c0101c50000710740c008010103c644803103120344014040b10b641604100000c040d0302c554100007020410421001e001220070140c2032507210b0303c15845064041c000d803810440c44000b220244080d00c43c40d201701803203ca044039561411110010140b65202c001751000380a140c2010385201121081803c0c00c400041c80a8501450100d031840b901c9110352109044040d0728070043e103000202e00c041d00c0107045080020034540750001c60300c1e0030078075040700340070070710800d079082c00301a01d080e50613985083e000382030001d1040c20313200d41651207020f80c0910200c864400191 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 911408435 1250 911407185 911407187
    0x50f0703030603051504081b0106050a0609032a03021201020903060103060b0114040e0c03070210050408042408150112090f031707020a11270402030d11030d020306150703 75
    0x10704a034041c00035101c0c03559103417031406075144056070040c1218505000903011341d40011440d0441c40307002300000401d19541e07000f19218145a43c001008119028800c00038410008034400c00d82010f00211080030560003640c103280c034440e0001070700580c04011500c1c1503803c2541207480c400f0004084450b07542e580e00d813941c00707815010800703800201c0d0015803e01c0c0006440680301503031040351241e01e8943c2c600131800c0c0c0d0364200a15070000c602ca03011100040b03000300c0c80b86034001e90140d00055951070500c00f15510400c8001c00240000100c0b10361041000c1d8403801070790700907000c6a00f4030709924201004a80e02c85482e21b00c1004035250618820411805440003518203100780c40ea9400d1142001040d840f40c00304030b07001805608810346503000241824010181600002c00c2d00d90414250980c000f42c3d130301d68682ca00c1002a8050910003503290800c4800c204032071030f107007442c50041d19110301520b90003180c0080c660079070040003040c500d644218841c481001ca10070055154615824 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 911409685 1250 911408435 911408441
    0x51005131a0a1a010e0d080403022707050711040b0609040e0a1101080f0412140f03070e09010b120408040b070503030f0604231e090109020f0a061b03050f070303 71
    0xe40381c01510300e8a07441c007540080f40307980c80c00c1066051310b484e04282149028842054080701085415400401001c40140d58044400091440c1c1c8880b81c402e2400096002881d00c101030a03110a001d41070114000103808050b1039412294103a4012400301d810002082c1e4a01540a4165009007400000311004400090350070403d40990340c0c40618403102d00c010348501c030041d0b9029001e07c075414001000710350520840342d0f07100014036100c02403500b0350050b907141d90404035000c4100310000060202169105040c42c0c48840d0448141070294541002c3c1210b9104160b24030000086402c005000c2c8502e08060303c0003407900194aa64941c00c40c5441501e940c4212248444011080302140590070144600e03001d403070140c1c1424491101c1000044c8504078000d10600d8401120300030140900680e45105004207204800843c0254480c41007040301d0b855815191b0060a40c50003c10000d41d0000f10045611048004518812240d08085610f0711030810140707400900060103008160780b40d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 911410935 1250 911409685 911409691
    0x3060e01020d0f02130b0309192a3b011202011715211e1e030702010c02060412080409050f0f0708090a02030a0503030f06060403051005131a 62
    0x59020081203c160b00c24004078001c440c2000e05a40e007200e01403003060100340c011600300042d0812034100c01001c00d0142da0300345084008844030300580f45c941c01c0d00800c03083c2210031280900b440d10801c5050a01124140d922400a4548044040c099400800c80010070500300d04482441c3c000c1c0350303151140e0701c502100219080340040d99201c00a00350040705180280501d8000380302d103460300c580d2400c1002140d0b100708502c8030884404600c106d1a03400b080310300c00c2c0c00c170000d40d20a01e844851042e203044c12140d00f25050441400030781c5450b141c40220455032040d90900306540e1040c42d500100c3d00c0d0340155000180c01500c000d0950090100c1d00d0040d00456084100a02c0b481d0344e8501100d0580c902904d5002042c9804000f103601503001341d0340d69600902d0034044620500317064000070301d00400034030141e4898000000b07110700041d00d070741d56641c03081050f44c1981c902481c5544bd26039a19141c151181101d603a40085981c0d010a92032414040742c01c0045410800c29403920310201a00907 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 911412185 1250 911410935 911410957
    0x4050312060109181a030607020109021e09011e080607030509010c050a1b020418030e040b0910030b0403030b04020304051b0f0a091d030a0c0618200a03060e0102 71
    0x3000064507036114a044109031098120708032a14404000d13940701401d80d40007003101c910400b884080310354404100e282d204240c254000710f1101d005005000c1005c25510a12403189001e103840122516002503090446040702200300d6980101c40b040680d031425600b1880480c000d81090003030855140d04003d0165880c0b20003001140d4480406481c2842120f401e0350200d101c03807604100310304003210b0088100b800903101003036505d40c041050500c1c0400d1401140412995000400c0c1400c0900c20b00902004c15100e00e443d03802d0071140340d0000905d40c44020508458070300041d04242c841d0b0042401c001010b04155100e040500c0c01c41d443d00e554244030820b001c098030001d8407902d00324441d038001c21000341800140c5824030000e4400307400c01c40206520145280800b80358290100b0042000051f17039991000082864a0300806a880084168005142500c0c281000c104000c00321134145d4405c2100c0045404420b000c1500222140e00140440d40f40500003203000c403041d00149440002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 911413435 1250 911412185 911412217
    0x1020406020a030f0804030806090411030619060503030f120c0904051302041a0f060d0905070308091503060310020702190603061707080a0b1003170403020a3f0506040503 75
    0x448001100c00170400c03a0098006044000816040d08040b24040e070058040c5004281c031500740800701c1c1c81c00c4d401342c608094640a050100046042c5031007080003402c0220003071460a540340700a40d45078010b1482030b5400311884400320301e0403040d600403520451000390003404585003448190310400c40060302a0301440c2008005035240505a0f40c5460364040140f5001698090000348480c0340c10040c005000c6039640c9184038089401004908020352241c4240e554404d5184184000f43c0169900800121402e0040c404250b0700071601543c0e94131614401619148180000742d03654170a940d4840304070b1442000401c071a40d01d50401e6041d585c0c225440c403004c0c003e50b065a0790f584038902c40c50300b4a401900300c40c1c0005464200e59504520004484c0c41d1b00e6890785c507841030707040c00c58402c3c600e50100040e042003142410340806006003401409003039281c0d00003c15510f41c81d800c80e4030946007030b018000010711141020030949100c1d00320b0304a41c140e10b800d14001d581d83d07026030074440d4a151 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 911414685 1250 911413435 911413457
    0xf020907080720070f080109050f0a05102c0c091e0f100b03090304030c120305070f030302040b0c0a0209130203030f090a050409150f060f030201080402030a0501020406020a03 77
    0x70050040501850166441e20002d805511001c00d0908038001c40802902a4200000780e4100e1015044060f200308000000c1d00042403501c00e10f40360007103500407200c0d00007183c1900440c401145003140404291008200b95400340d0094040034902500f0609800304107032519091100040c80c20030030320066072000c42c075403240403000498064500f418030140301c41c000000c0000c00c040100503002506803d85030091a210610780c00305400403181c0c2186a0b00200c3c1c108144a803240f8010f004054020a807040001651070060203131040c040b0207800c21440100e0501014425412200100b038480038058641540542581d1907083c14801648a801e4031400308890035032401403d0050b6600030010351500f1b20320000e40e900c0c2d07000103c0307269000403c040005910f4807180280ea50044c491660039000003a84400039082358802c110041f4218a44202071005040c4135051000750790302401c102d2859611840080e10b410035050008089500109002550580014051480c0e03880781d164216400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 911415935 1250 911414685 911414687
    0x118060b0405151e21030d05010e070504060f02070b16021201020306010f0f02010b030604060e0607032708040b0f030f07170103060b0d050a120201060807030b040215160f020907 78
    0xd58000c0c450b903808000311a007882840650194a120550f01503d84581d050740300c500304ca80d401c58403410100c25080014012803107d078500c0707082d01400f814240c2d5040c1e42005040240540120301642061100300350725181580c0c0200a5100203005500c031107565046213401c0c1c4400496010000ca00511940d0b69105c00250180262481a00182c0d1140c4c1a0f041c0c000c400c0704c0104c13145445100395540e50021601c0d42c1c5040c04820320441c011480030400c00d0a6841c020300e0040001d103c85c0c01c25107040400032203407103d503000c0c240a000b94159201014502e04014840784159440541400b0300083c000b1340210211002c0c1d4810b02c815200280f265451380c0094504e01070050101c888441d03500014400102c184c0d000752101e12000d40324061001e8180da40302d280c0010721105881400000f01016007081d424060302005e0701c090030240492900e1940d5883d04160003a00080c812a8610316841d4215620010388410300403894440c00100800d040c4400340e035200e07137000c3e030050910a000401003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 911417185 1250 911415935 911415961
    0x106120906110a030f02071124030103050114011409042901180e1516120c0c0507080f060c09040917031b04080a141c030615090f06030b030118060b0405 67
    0x43c0348c112188040241c041400c00c02006225010714550501d56441c01588180c4c4801450107103208600004204071840803800320044143c2c042c0c103080b0000c004c80900340e2202204a9041031744580c0c020400100c1e148800f100d0382c072800406845600c481c000051800b060b0410f0401e450440d030b000c11800f54020749854941d40c03507265483c0c03444640c1000c035030707c44405d40d02691459a50320b007840381d4101030400c00e07040d00d08410300400000c00b2810350f18284441401640020708012000b4607800b490362030110384605004002050030000401d601c229a25603821000125a0019215010b030041211000c0240c02c00d40b035001e5845c0e0540c8441540d114010121026203101d100240030715405540e6080e120500b0b030111242a0103000360081070000804d00c0c041038070740d00342ca02244190804090000c0050000401000c012421504201c1e50701c14100602c26203030240790204a80d00c4c1440428050489100d00c180c47c950099040b0041c418254000040b40c0000c450030711103a05c60b040c183c208 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 911418435 1250 911417185 911417197
    0xa1502030105061e09040603030305060301050a0203130602071a070504031202240916170f160611031608032d060d0c0506040602010e1501030302060106120906110a030f02 75
    0x100810001413490103000180c1c1800c102151980e14042603400451706550060740101c01098445040c030506240a0040c1307136001c12450011810340c5072168175800c41c01b000c040007400b1f080e80091041c1c02d01074410301d00100c88440c0c0807042c0190510b03004c001c01d030394007600c07040d141d40d04611003080c031080c0b01086040c0340b0520900300071850070710101d4140140b0b6002d8a108454031070b000c95030403510040381202d80140010492903a000401c030188909081742151840c840350040341c0040c10004001e03e803c02592a145040900c1c28100c21a0078958441c140d001030702141e0700b59000080100280055120f0b501180822141003a0000040140703494900d00b031800407841c400041582c184000420407a9000300300316004540d03160f0101d13010764095080840142d4558040c03400d02c030002c000408079403089906000f046e6255440c020740302c4006000d600704010b1202c0b409140c2481c9034012840b003940100d02004142840f1800114590149903250302190502202c0c03001101d0303510940d09 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 911419685 1250 911418435 911418439
    0x607050d02070507151b0b01090e1507020c01020c150f0a111609061715060a1706010807060c17030a09080a0e1c05070e0c0415030504020f0a03260c0a03020a1502030105 74
    0x151a420800308801038444c2c07103041e501a101c2c00f4bc0c0480d80019814001c1d0152581c0e4024068084641000a01f00101c0f8025240204803241010091a007050211503070350388050491a200c010440302218024640c0c0c07100c5000d40700b02e80c6070222200043d50210200c1341800c800700b00013560f40c2c04426101211000f42c0789281c00c0b040440803c10044609254044001420104400d454916840c00301d2038800c0b800c05503900010040c4a0010204940c070050916420401e0360000c050b0b880c03a03040f098481c94074144540100126203154a960041241590320424a60b140ca001a10080c112004001c40a110300000c07001b01c0b903900802e5010001035074100d805030a40504049000001d82000b0301070030581d510400c0006004500d002500300b02c580035540202d11820180104010f2072040e881c0c0502c1807003800810800142d464038484100c1c101403104a40c0710b00c20241011803409810740001c410701400011504041d8041600303035034103100300603804c812010980e50104a000c00d000700790f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 911420935 1250 911419685 911419703
    0x406060c0303050709170609060c1603110c1509100f05070215090607051f02041d04110901121b03110118230f090403020607050d02070507151b 63
    0x200442c1c8241c020b50f40c484414244140d0b0a0b541d80c0121004060001d41c2ca422038100b101030040703211003071020f19000a40b000902d400e0013000e0302000f8542c14031881c000c09016045100307401c105410b02c08503d610000805e6006951102d02002e081507204d1000c0d14850180f22002000303407402494140120400daa43d182e0504031720f6400c1c040301c80382000c4589011f28084c40100629a115002402e005204001070100d201c0010b950084030401074a0b1494a540140418011078648498208803121803000004c025113981c2030400801c0640c00d0ba558000c0001c40c00820310116580100703108900c1500101c042e080c1070003001c82098164040240307000b88400b01100c0030343c0729a0a0102d020041e013108803c4039a10042441070000324070703240740c101701842c0740c404861804203040c21442c0b100755200d0030203241c00c2d5402521210300414010a000b000b040083d58010303158107440b94140c0c0310080740c25464072403010f1360425803e200300500280d800701d0030b02c5a203540b4891038035000b58010550 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 911422185 1250 911420935 911420957
    0x403120e18012c150a0e01060c080904150b03061306030b010501080403021911010e220f020d06030602040f1508070e040e1603050601060e060d0b0607020603071706040606 75
    0x1a103680140107042c0c60b04103c610415440d98507100d6098001c0d0340381c007190640c1d101d60100748501190154008800d20f041000100106508200c0c40d9040c40c2e4048410f0b42e9640050300060020010300c1100715010040241c0401c1c1c07204154001d6001e51000c440d2084d000441c0302c0311000b03490701400000c0c115142080104080d50250518a4100d1b1103801a0b440807030402e0405003200480c030000341e441105d01c0c50b41528a580002e030410720000180d444000d4203098101cae884100b240f01942c0d0303030041d0b82e0741d1460301000c1c81e95042d01d2883e045c2d01c00500080e6968240b030720107500140644001080b0010000401c1c50003110248500b0b002c50b1135000b615a01e4000686002032070001c40c40d005904c03150102050301c4103010140d019a0104903a000490440c1026890010141c0020003800003034184030300b183d07a0b05400d03038101c031804075008a41210240c000c2071a600600c8002500f001011051100ca29000000601d00c0d0718070550240d566a42d0380100700513280a446080e010a036080c0d90 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 911423435 1250 911422185 911422199
    0xa0e03040f09020706110c03180d0201021504080d020f04050a050a080712080412060f05060301060503070e060a0803130602010e1c1826010f0605061c0f020403120e1801 74
    0xd000c8443c018440010f5282c800030981b1150360140412071910340001074960342c9120b5010602c16120401c0c0c0e00c8545419a6600203569040c4000601c480c01034a24002410070a0700b504480c051940343d0070947d01c6a000b0158030090b50400e0280c1e520407010040081241e080a10502007200c009600030a1618504007000c00c04040054054400e807004010104840d00300c0c10b02110340e07910682c00050900b020030000340898a0280c0124800e904285c0c3c00c0082c0e5800154001c19994003c281030303016100c2400040041c42903a002000300d000102c0c0222440352805002c100300c0c0d030203030000c0c844035083e00c0300d09860302c2d4441c0105d4a0b441079044031702c041911408002600070303081c254542c0508d4540d003d850010803003942a00c12420782001d002c01c02c200c01e000b862000f40724541c040c4229800c03c4005850b07401807413540c01c2980904c40041d088061950000310b070020f89000c085585075143d080c25040400059064804500c40200c894114100040c2c014100404402c001c07000742d0070000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 911424685 1250 911423435 911423437
    0x801140d08030703020d0c080109141605250501140a15060f020f010e01020d0f0506030a0803062706010f0f1e02160b0d0501050105071104091403120a0e03040f0902 72
    0x49600c08050f800e124541c3e806c903091040c0310f42c100e01601c2c0c003501585404040d2060740c0000034218100041079003480510032005e4101c00c0318580605005407100805100c2030281c12403000018ac3d000d0040b414001800b40643c071070480326107510803074109903588080c1101034640c0001c2e581808110060200000e40c416000d11141c168548141d0b00b90102d9203103401d00351400c1d0340c200d8201740d6001400e45ca0600c0a449132000d100c0c0340c080180326524210002039280c0048482c042e1102038000009903a0340d03039140310842c1101a0381600104045c0d0000c080b281144203c1d01c2c036001c107203140080703000107000b242180540c1400d9038803400940d03d100e2081145100c54881d0034103510440c0c03140034281d0034410301140500114090075898444216440d02500c8060b40410305101c0204003c101240c02d01c04685030a03081500c3c0454022054540800450a10b1000c41071070700001c02c0700700403511030a005e0b6004071501503040c00f02c3c40c145d10f1040d880b4812031090f01c40c0350341c680004110030350744e60b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 911425935 1250 911424685 911424691
    0x7060c080d0902012c090106021605040504030c050d110622030c080d0e0303040213020f030a0b0607121101051005010e270c1e090d0615030519030801140d0803 70
    0x22410070b03507400c0480008a031200c52444c182c2c10f01c00746007604032a94100905a680140301c230344000c0106117165071102960000302e003c0c81e800b40d034413180003405050082c640c030901203910804661550086010080c85000b013642c80c0303003560007494040350f44c024a0102c0303141601010000f520300300c52683d405954210b2155011207102105114225010741184241c1c461170034503c01035540d37444c0070b2040012a802068000030343c1481030042000d03071040c64080d40c0e4040c00c82b03280018891024000076185004c1d0400c02840400044010360030994000303074040c499021080248019101c900c0030684015050191500044240340802c1613880c100210080c200b0b1010020308550f0703144400c580c4c1c040800c076400a485200010704000269413818203118a0707600750042414036400c400000c42000c0d0044000e42115120120001c0702100881481d00455110044030820002031070000001c642c08603003500443d040e00000a0740c00034004080808603030080c008030803a0300c140c1d11100150805 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 911427185 1250 911425935 911425937
    0x50f18040905032703070308190302041a0414100f0c02040609050408030412090b04170309030d09140a2612031e1f05060a0315150207060c080d090201 66
    0x29441c2400802c000307000070841c11403c0303000020f0400c0075507480c02c90362000076009802603001070030400100307a5030b9007912200203140c0e4132240140e90381e02041340079005541100e807400c0d03005013030382460419985c01030003101d0900303031211801a944000c00c140301c0112406040420201c403202d4900e00d110b940030710182c9100030400621980c8034111b890480e10308131812210454004107100a0080d40c4001d814403000a1a00d032070040e0900315081071307134080c904c14070040b8849001c8006401105006481c0071803005030440d0291003894500070007030b0410f441500841411054240c109003051200c000540f45400380500c0051940025014050300001c440c4015015407100c00d0340040310900194066180654112038100c5840c400c941c61840240000c628444806000502400c1040e2030b0750440340103c80540e00c8007405035065000d04078030000c03000e01c202000c00100d0a41072400d400742200341294201c40307110341c03596419200700210150240807800c06003c1502a4150b58001d60501841 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 911428435 1250 911427185 911427191
    0x90f090510020901140414010806090717060d1203090c1401020c060904021309050619050f011d040207031e0807050418110304151515050322050d020d050f1804 70
    0x119640044150050380000c0500030032868401008d682c843c1c222030b0002c10843e01c618450400d010040c1c0036000280040340100360050004403a56030305c808149400360400d048000002096000034014498214220390a80c240d04000c20f8100108428018240040e0010460342420000b009902e41001e9401a03000e41c08000000213036420202c08001454500800301c0c1d582083c03410440da00d40d024802e0300d42e40180c1e001c1001169035141000c500200300b802c0c518001708860b02018800002d41c82d01c982c0040c0000390800800d54044804200d10090250b640700980200e40221600d48060318100006a020b100511018880d07070104010221071400000719000101118080d54000700c80c1607904040703589040400300080d001d03da004503850704c1440501360505043d0f060100e800c0310310808004002c0000781c0600c1c2142590004505e42e207642d49904152450050741c2c901150020340018001c200d2824049030040e400c3d1081c1c5460f4007026402e003405001c3c02c0056581c440d000540c8161 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 911429685 1250 911428435 911428457
    0x20c10021612170c190507060f0606050c0f0304050a21020307060905030c030d08130f0c0e0412030207030903020405040f0b1527070e06040e0907090f090510020901 72
    0x240c8068050450805926220200020710f501c1c4815400d00a280b8408920308001c01044102600250300d1580071a062858981400e402d19030003c00600380c0e0703003283c1450410b01050007500035015007001e66400701125084e10310404800e8403401188209a0032107001d07170043c40707003107800c0064051011910000100321002030b00000c0ca082c800d81c2c42440800d8210009003d203003828009120031044c10b400900c1012160f16001b0103400d0014245480b902c40143c0c0c2000304092031500500842e0400740c100c42c0c0ba61038428001d4100d10682e001c4446074408807000031403c3c080c2c02900e1107140c0644034000c00360700d0740d0248000b41800400840d01c3c030803903500010009450300140da0254462074440054040b80b070b81403000b4400000c1d40c1450341c1e404d201d61141c072084119034281d8030491515041c00d0210603030000c02d005000c1c40c0c201d102e500c031218040143c0c0500004002d42101c3e03407048203010210716002d00d6030889195100c00703000f0350888901004080c2c0707181c00800c2d119006141c4503070110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 911430935 1250 911429685 911429693
    0x510021c080610050a02060c160213051e0106121505030607030f1109211e010c020714101d03100b150306030613060b060318070801020c100216 63
    0x812111001408105110288012428100c00d003040d00f0b01e690400524050100e203010b9504d1a006205100820b00002c10b81c041c14908160030180d50b601070403800141d2a02c0b25440060442140d13006446440a41a1840103800b4400345040321952384130a5804545601020042c105503e070352103032020312000000d001d807410054580305507810b40e40041c0a0280150030740035505107203240540361a080c0a2000c00340e035000d90500b03401800c1c0010075002660076180500340202c68440010800c803080c080c03151164190021b02c081040ca90a550002e510342c1c1d02a100340b15201f85294001d4501c050440c98540240e00407902d50146901002280044400003441c040728054031003c0c2175201c0d41d00e15400e007070542034480800f4160300340301e08604d00040820b6580200030540000c0104120b032410134403600c0c0d0b000710345001d8003030100750352031820b9088481031001014101c502449404400609190103101351034004801c40060540a51301c483d0f0400650442c54801c00d0340102013038404001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 911432185 1250 911430935 911430973
    0x9140402040e1906080111180d050a031707031404031b021c1e03051603030b040f0204151706011d03030c0c01180b0403060c05070609150b0109030c051002 68
    0x258084482c011802c00243c041c2c0002e840c0c4641c00b420b4241c2c102460081405e5811050fa1500314441c902c2001003444030000803011702140101074a603000d0007079000c040c5a031010400c004803200240d0054230388c440d048121704841d486601c030b105001c0c00801040001c0d101c1c10103064142110742c0b1003640c6041c640c0004006440c00b02007050b0203224001400c003081800c0101d0070245000d90b801d8400404943c9016080f846400100c019008038085000c0030140664044807072480050010441c2041c1005000d000b5803103030142060009190888c08465813140c005000400f103d240450f41544441d401520413510704d15828081c1f1240b09100e001c103840c00c00c0505601c1c48080d0042c01c007a0034286c00501f50940030710300c0c03441c411a8150140002200142124100c4c1c3e801503000542d0025080c08880900501c0d0000307209030b080160310420f00100720356005010041e50410816540100015a0101c03085d00c0014200e02c4960420000c81c580b0b0010040700c4002801a0781d10821503620136200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 911433435 1250 911432185 911432191
    0x20309150d141524030703020f1204061409010c120b060d02070803071704030f0f0c120c0209060d02090402150f0a09082e090206130e04140303040309140402040e 71
    0x3003007901d58145131501c22020aa02c50400c041c5860070308012036849218400149501e0904da00003951781288260302c03007210500003102c00f01100c107041c21700d8854040c0c484592007042c09844030f40803451443c4113201d1200b81c02c0a0352103140642d42501a03d034050050f0300d18640d03104400b8088400c070029907000411102e0f2080552b1940c1c0d190a05016080c040e00c0406060b11160030381c108000030b0b81003828500c0d4954542840642074000c1003040710410000c00c801002e80d6039001c90050001d420140c9001103600c00c841c00381290769010300340140d42c02c010780040d52003201807011501500342601070030384020444249504d81503205142440e141c3c0300c4d515800c0001c4801030108030340c4809204451004a80b640d070021072640c40102c1d48000c200f003031000e29540d03544030007400031540d0b41d030116440604c03440e02030a0120340d602c1c0e40a44024045030151614607040c0015054000d01000300d80c8915455141c88002c18203050320100100c0380001c00c540c015a0030000844c0e40200c003840c50784 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 911434685 1250 911433435 911433451
    0xc20130203090d0305070f03090f02220609180f05070e19050106031e1505091806090708210702130515030a0209010b091311070210020309150d14 64
    0x10780c0341482c030211450300400d03442400c01c0500d880e00340a0b503903501c000405040e03100d610740072507001030754140400203112584000f5070040303c0e68140c1c041101910481c003181c0c1045041080120350320b003030007400c0d165000600400300c0195810080043c002101c1e0b02c007000c2c042c41c01c0b115040e895407400c510828050f2000c9000004001104d40a40101d026460240c4001d00d010701401c1c1c114000c2840860001000301c50103515611030716034450200301f4070402040d00074007803052404c01c2014204a10300c042180205400742000040c09010005a0f0800b21000100180204480c00450141508260a000d40605402c20002004d40d507504102144044401000aa5418840c50b1000c6e000c0708200450301980201d0400b0000d666041551411203100010701d80c0d0791030903080090665030315030080c0c0d0303002490b1903a481841c00c40e420260841602c04e030b0b600e02c0305181c40c450036039483c05603c50080e4864290010080003161a60140c1360603619000301042a600584000e0403000c0129081a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 911435935 1250 911434685 911434687
    0xf14040905070c0521070807050c040f06080d023412120f1701030303021c02070614010b0f091504031a060405010b21180706020d02010c0e010c201302 66
    0x3806120302404942c04103071140074106001844001829168019000041d000000205948c002d0090520210010f40c40c000d000b00100c148600ca0100101224048d0b00924454541813903806800003610b2110720307401010586400d20042841303010030440307440c0c00e0031202410000107a00076041c4a900700040c8981020f40c1c0c0d414440c1c40003003c2a40701e800f01020084c0c980c2e0744c410a01c0c1580e0200341942d4040c0f8026035604980321b0700b881c1d18804982da0842d0b59100141403028054141d21000b0340019170003107142c40c0e90340c48035103c010340078000031303403841c400b0400140605140206d6658450380c2c000b017480d4101582c981710714801001c416018000034003080c04018141c0340c40c0c82100d014008100120b070812204a2228030742c00401d5101000e900c0000700402c11604011000c2035031140050700302c2d0b010341d0300c400000f2340f94080039041d080550300b0000f054000702d0103040c5600c90020103079940a071400c07043d103c194156008034090b601c51072042c00e0819854403040d61071160031402c01009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 911437185 1250 911435935 911435957
    0x902120f06100b07060c200105010e010503030c0d08101a03060a08010e100b04020903030c101a100e0409140703020a0909030c0b09070b0a030b09070309030f1404090507 74
    0x41801d091000b003048080b00003019080c084920001c050314180c83d0456030000b201300c2c401c0001c0d42c590710300404d154144030004c500c090300741300150000c42c140d458412038810543da1303170000c0c19520300610700d0541d02d581003010b91314420340c4103500a550004001b0b130b0580c03103156144203580e458901c10701c80b903000100c00800c10101c0d0601040c08402001000002c01c84208400c03261902c580c041c4820100142e181d035041c82c0030359030716011350b0b00028008090300d980341d10008807a0341d80c0c40d40c001224900c5081518540c200c0a01c841350f050f902d10080d00c14090640f0800c0304032012404130121075400ba03995207658010840b0f501748501006001c40040c58032900310700400005ca02c2a03444921010b040c00c4004000960200d001000c55600c04d450078081d8403109000390911460f900421074a01300480d401c40c016605800c0340c2042039064030081c1c00381d2102e00044050340c00300000500031500100003204030314800c516000c03001ca5110140c03407c10f62030350742900a0740e1095800100090002102c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 911438435 1250 911437185 911437213
    0x22080d15060503150103020c0114060a09020702030316031b0b100801020f0901050c151603061202090c160b0f0f0708010f12110301020a08010f080123060301090212 72
    0x14001044200c4060028150700c0c08400821a1100610354960000008620059039009405460400d07810300001d00600a1409540c85c2021003114414441d5049801c0010135000740c1c82211151900a07015618154101c26006540801c041088040000041503141400f4152001d180001e00c2003900c0080b07400c1c040ca00380c0c4401003035040a01aa48100250390000c840081180d05686003801e015440c2c0440d07000c05820410040260703c003c007000380800600000c0c1a180d802003003455102042020340716842003144c0d5440b090001e42050001000c181c2004151004c4c10311070160040e6080f8449a995a101c00214107031001c0311282c03000c0007444180e9240319002940600c030f070b140403400b96243c422024030780310582c8101c021050400c08928148050100038003c0c1c1c0401900a5580303040080f80140b481c503092040c4c400c103425001001c200843d041c0103a11040d0b0208509850020100a41061700307036010303200a51641d41c1c1c0c0d00c1040141c407004d82045914000d20054030900600d180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 911439685 1250 911438435 911438441
    0x60206010501050a0c020d11121c050c030319061502012703091a0409020a020307031e021b0a0503250603060501080103060e070e01140a0e060108010b0322080d 70
    0x2000d81440f81c01c2c40810400355102c00300040c010740442c0c0d00080c2c913140d03080020541c15524003070f40d045920803050800421000030544c5400310035104107030085190080c229142c1c0648031b0740c26000c0d0000c1001c10281c4c14204120000b0006100d400510a5500c14034a40c42d01404d0300d00740701503515400d01415003455031007007410301d02050110290044090750001d01000b40e600035001ca01c840307080705400c06400b0000381c03805080d450318110342d1490140320180d40c2e074020290880010b4100d04030001170039010007000c003007030b4808d40003030034200d4401d600c40104040841c5000e42158400300700041c240d8040190007a1014481421207081500070300803c06c07840150050b40a160a2400410207642d029600a0450b40c00c4000000c90680a000040c01c0075220342c000d204101056001044004150503101e401c0348080b680c0300070032a0740d50407690780348408855881c0458070501c010840f0500d12030046a00c904078401c01d441f400c0c15100c00d946100c000d900180d50100f80807403501100700c0d00748 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 911440935 1250 911439685 911439689
    0x1120b040e0d0c020a0b0c0613030e090a2408030f0703020c030d180e1b090f150910020f0a0206090a0e07030203010e0c0c1b0103090b0406050f0606032e09140106020601 74
    0x10700052908449880e1f81e95100005021000b040000b6000381040c5807040c61100c05035040148200381c0ca090070600c0c01c018010f442811006000c00440441d0004c2105051004880ca1100514101104019409100d810119040d03096005051190f02182d90030700c43d41290000e0341d100c2e0701c10500321001d4010706030002c0e000b040c00407201c0d0092004040704210b402600200c010307100c0c1d5452000f240800c101e0460f482034190040e003024468901e034540341300a01045003064400c0c60369a82001c2c8100e0b0383c1c001d15403410b0903d40000754030700c1c05414004024980c2103805044c1540096a40c0b14030280e907035044071380b940001e9001c0014401c603800d018946801059200070141010380100140f0346480810041190100725461280860b034003e41101200580052401c010746c03409051104c00382c001100c50b094000c001500180ca01d14090301a64000c8040c0c00943d00700e4540000c661082032030884040c90b10190071343c0002840045c5d4041d102d0800403103c82c66459500d4003d010745802d2040e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 911442185 1250 911440935 911440949
    0x306050109051e040b0a091a180c0a050d1403030f07120b03031204110307060206060907140d020d0b0a031b0905070e0d15051015020c01120b040e0d0c020a 68
    0x4a0040e40b0f4400c03d01050340054000f55030341c0b080d45400394494004c101c2c64400074140200e48543e20351000030700520a10800a0321000c00c08001d0103c0482d441e000d048103600c1e84807110780400d014504201000c02c0d10b880c82034001c071050b84030031100c251658100b112021140c3c0300c214200039a1580c040b0905020a9039186d0030702002e90382200090712030003403041800041c001e1000003005d0104080e8150324001d0042c0554481d203482c1d541c001c0d15400c0881c4d619004e507204801203608103215074003040c034001c01100c64500309010801c00d40040e50240031000303401500c2c0c50f004000c0f680c560311100300035485039200740e041010351520110914102d6200e18607080c0b40c1820000303181d07002098040d10324070071642180817900a01e85031224003032558204000a00c1c01e400c001e015500740f4070450a41d40641004440404901c80880c6e80e55184440c45000911140800305100c0290300325603100b4500910124098640755440fa02c0d00078088480400900d00c16030900c19030800c0e00d5408081c28034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 911443435 1250 911442185 911442211
    0x1504150e0f0f1204090c030902191d0106050f0313390f05060f040906090e060a090f03051b0d0519080603120a17090105190203160f090f030605010905 66
    0x1540741c2c0848513008900c929451142c6504058580d50310903071011052940c020102419072060b0002d807059039409025040500707012544042c041c0d414034081c0c904a8500c0c1e0703561803600301c0c8504122178541020300020100390f001e01290001500c82c0c05c000d0301c8254041c407100c030400c5078064038809080002200b8503040320048010f0142041012000d826507501303449060380c42501a9400a091145a10001100740f900c103002c222a8800d8202011650100c001c03626243c580022407412150f140000034011040e4501c11400070b406040a0480c2d213a51000325170780c2c40ea13401203c2e41480710842c90707000003a10024042c03d00d8040000f091a1250051900c038400c4d01c1c04c500404d0b078800520707404400040f03000c9046808a440344d0704500d01011020300c2e2004904290040d035003e172205542041400b0041b980c00454402c1a10a40b03100c2c0d5040603020320001001c00003a203840501c04a00001c00800f14400303e000d0841c041c1c200015481160000f401c0d602d000c8503101103580243c403d40c003140c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 911444685 1250 911443435 911443453
    0x8040b12042f1c0803090307061401120303050a06090216050f01180b0c0f07200105090f100201060803120a050603060c12100906080321091504150e0f0f 67
    0x15950b5101800c841055903880c08403400380203041d2000803802c40c000c181050010030025021030120251144920820341030140d00704100b500d10b000c001c05d00540300004481144000481e109800c03464010720001c00014030192181c4008059030700240c000400790ba14074045204211082102d40800c1855800811200030040c04c0c040c0100c1205001030b11f400c0e81a80418030000840c01205c1a074401c1c4454a40c1c0da20345407170600c800645449404101c500754602c40256540110300700c0d2050040241080c20500021041212a04408080404544d680c503004035000800700300414134540c9152181c101442c1410300d04040d91070003401c0134000c0d0410030600840e4500002568000c242c01011015a59200500080c04540c0d50380700a83c19410039000144800d0003000825014044080521078240c400c401c9007130b41070091b50201400d9100e00642d4403240c03241062150458814110420022503000c41c0b5400da600c820350080480e0401c6001c400030350010030000301c3d00051040030300344100c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 911445935 1250 911444685 911444753
    0x31e09031804060e040b01090e03090901051c020301110705060a181509050d030203090c0f01020c0402160807050f071208090d080d0e030405152508040b1204 69
    0x100a901c1e414104210204065103565a03541011020307000540c0d1140b024a000c0c01c00c45103604080c410000c043d8036060610301540000300884030040b0b000b0703041e9100b992801c1d05104005c0f000280410130001e4400003140166000c0c000c040d5240070308000c3d00e8a80280c1d0070a9800d207203000c2e00c1c00c0c00092402d0035858100c0c00f984051450f854105102070500710006c03c1640107846081c0b00288203000b448000c49001d5050360246006049940450303040c00c2680092180c480014140300b8096407140c00c1d00f6425103032540040002000c68104cd5071909465941c02c40d141c0c1083d08121019004a5003001140741c08218840081540c0d03a1503090b0720103a82ca41000620803000c10078002d007104c1c1d05060900501504442d00c07440b0400d01003128015a12125031260803074040c480c0f044005400e1000c1511860b4162000c0d0020f0070010100c8911100301a018240400400c4803814020f02c000100448003c0152128820100760208180380030301d07250340c015034100d0350350009084250b1508104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 911447185 1250 911445935 911445937
    0x7051c0311015c0d063209040602130513060501080606032203090e0a0606020f0a0308150a150207060801120f02120118050718051603051e0705031e0903 67
    0x1106844000c090b0428503084402510701c030b0f15001c0c00081e42090343c00501b1000a161045001d02e044188203603682c5440050540807464400e500c1c3c2c800c09910115000c61255070041c0f00540000185000f09c6540358082101c0702810f01f100060142d80382d10400c019604a0300c95540120120743c05451841c0047c0c0513080b10098114000660b4011012402018055000703032002e094000d10f2000c0ca0b241036440c0d80003070401400791500500408058035426040090f049403210b40c5620b50107929034403004a000032a1403500401d52200c691800000e054608101c204101c00055002d0004d03070342848005403840c401a401241c502e10303001d40410224510180b0408442e6046500c40420b04020100c0c130301411000300d140500000c542c008008000000a0442c21160400030300403080201845090803124110307600c44c01e042c0101c503160031051180c0d0204d5402412081d4050021548a45000c800f42048680001203000001070002605000018290300c980d11000294a454080310060b1a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 911448435 1250 911447185 911447321
    0xa0512062401080a1505090f04150c170406060308032403060c04030b0a060e0a0e100b0901030f1b150e0d050d031109090c1b07051c031101 61
    0x200c0c0d590352030301c80220240d4000c424020b12004201e07007e681041100300c551424261400c070b0341c2072082c1ca21000c150060340100c200603003903600d4a008042e4461400707039008200500803102c2903602c44002c070000b1003040146000d01e850b0841d50611789081c914814040712b541c0304051203035210500700300700402010200d506981d8004402046501e441d501400030344030580000078165044410800c1078613030343d400080350f035100100326072030f180b200003035036080341d42d45420030741c101d9861401800415010420201d020384a40500a848804085503100100c481d42241d01d808800f000c4207400c0b2a031020100050b107408070b611045181180c0d4a6655403800c1006440a01d9160a1111001c2e1740340c9050b40c420107006400c0340e00c5480e100e000d180680c2e02100540c0304040c0305070495022800b001406400ba00e04c042d0410000410b10038141c9040d044170101101041610f2040241c42c0d10207000d44800424a82c2c0c1e242c0b1919888040f88001da49040403c3c12924104144010b00110292000c10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 911449685 1250 911448435 911448451
    0x111e070b07020f030d090305120c090414060a050409170304120917060708221b06050304082d0a0206010f08031c0c050705071404050f010e040209060a051206240108 72
    0x1c6c02e03102c603290646007400303203411010103001d0400401c000400c811009200301c100480d400c1080c030041c16180c8481f214199489a00880d0807032003400303a8100390780000c024070300030bc40100d01c00e45851541c20712548111411103500850409000c40c683e04000c40801802c0c1c5204040d03510000c0c0800c013580d60100524120800c06280040f590001000070319014090120b4803480c15201c03282464003c566070030240300c000550313804001802c1071140c4103a03409a584400400d140592007290300c501000420362641402440d040d2006103806c18030700921041e003242e009810590700d00440c1108601480d0b00410058200308004400c041400420110b4045a5200001c1c10040b00d902110f4900030f480000f0040e00c0f5000010801c100142001103a45200b12414042c03642c90420b103420f6102c0070310413a5100e48244c4007050041c40c0c000c5807180d002e07402801044155959900007114448440c000c0c09003500100d06000d401031541e084140f5010030904045500d06c01500021300b000c0700100160 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 911450935 1250 911449685 911449691
    0x203070b06040b03070e18061306020c0c0a090915110706271a160504121b14041b0c1b180204170703030e04111e070b07020f030d 57
    0x2031801e0b80c6a83c000c54104102908550034661030388440800310605071002024070b844003800c0034200300d00042040c41440c070001c038040c03480c80e0765580002030740202d11202140d014041904c0c945403600c42c00e05c0002d0101800120b00f0b03072400d0030610403405601000241032030409140b030804000201c11500816401840003031006990394400000d110264190005120b0706002103042c010441c041e4420b03004407082031242c0d500c4102911858207128a00440031030001e100800461480c90460b4008600543d211004510800140118944035802a4110204030210215a824507100d82000503a010418003400300d408003000d0710040c12844000c052440c1c44a210000e06402000c840085ca0554007803200d400e0f41080c54006074010f4050259000e190700d1410007070b0480011008201c2e40c060f204e0f01005014801800090007820280701101503040001120504403c081e007030030420744030301d4540c85811502d069270791404060841021540212210850b040c0044211403040c86170007000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 911452185 1250 911450935 911450941
    0x4060e041a0d0c0302062229090d140106061209021e0102120a170609040b070f031503081b0601060801150903050609070810180809040905120c1504030203070b 70
    0x41d40030000303410003034014a02148481040d2800b01c0116501c002c940d5203480c4803904ca04514040700301c0d81705000601c0402c00300100b030601d44507000b03050303270680601f031920f4504442d19602c6443c0503a4002c9031880c1c0d56540200581390703004100100040000b2400c1c4040e0409400040c002c81e5901c2d400350006044094010242c7c3c020048a00041406d00d41035840d03000b02c40d0050a4080040d0003d41159514000940586415601c003482240c0c402050405e644511100319002c02c2c1d41054403090640e01c005a4081031241003200000b54410101290b0300c40e419011901801c1c0900186141c0768048401440102d40048529054440c0102c401110040c9a030003211070440079030024045002d04014484034150210341082903d0500081302c0102500171800012100c0401002d03c011003e450300000141c1e03c131005001c801c000402c046499480c58440b1403c08a06814040010380d0001d01c03003154134000d1021820038100813022122620380307510003949901c102100140005103800c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 911453435 1250 911452185 911452193
    0xd0c020304120807050709090302100519020d06140f011e03200306090f01080c190b03090604030e0306011d04020a2d090e03120907090c0504060e041a0d 67
    0x58600614281079520111081410310030710941c4101c4054409005102c00854000302c60701400323144590683c000c04610305019401001040b014045010741c14020a0109000003980050040c80d403001000140d003e1418070341c101c107444c08000180c0200c0320310300b05400d940c0c0c00c19104c04280441c1c040801580c076001000301d0081c0b070054060002082043d07540070b01903049801462007124251040049500e070003446141c848070920600d60f00303501141488a0324108410b048643c80b01c0510482e01c200c1d00c507446076100303410483d001c0d01d095022108200905a001c003840000c0f8400350007406903541819000078103140824504010820703403201240854a50b022140014016495003401800c1c0c0000b00c22403122078a60182400340131481d01103401e8000b03211b522014056807000754600313201184014900c0100a0142896015044000600002501403e842d40900b6aa0b00d640c3d14101701d4081d01d5080411140e42c00f4901c0c1c10060a041800b25004050020302140d2107401c820403850 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 911454685 1250 911453435 911453437
    0xa020102070e0c0c0d2a120e060d0516141801270806100503010b0d12110d090315021801031104120b0f070512070e1c0b1008120d0c0203 60
    0x5500c11203171045c90100051180d0050014032825141003444100c02d01040100489001030748018004000784510004054001d03030342c001c0101d00103054207042914502c10101203503011a0342400c120f401c2e002d0b99203800e0740000395855450700400203601300b200c0400900e5003841c80c044058103100d03c40e50100f5410881e165251808200120314000040d241d20f40c1c47d4440c00240c07404a00149405800304591030180504100454042c0403c0d650f00020307145c002d203220030a006101442011440c812400000b88803200740404581c4a050105142d0710b0302c101c000301501060411944103000110350340c0c000000d00f0b59504002d01c4c01281c5241500500c40e03641c0306542c000c2ca12010044451070400103007284003803040d48180d040a030141d4440030709980078482c0d403162111603041c00300001c16081c01100103242c42c10b40600603c44101412455044030001c100d030503502902110104a007400112250704058004000034102180602c40000c0c00e03400381000c03c0c6001030b280c1001c4070700b03284204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 911455935 1250 911454685 911454697
    0x1023903031809070306030f2a0f03031d01020627030a0c060f02040e180a060f0203060415140621040f05070f050109030f0302010605060a120605030a020102070e0c 72
    0x8041c1c035070b119039007141650080841a032582c0900f0040740094404d5001b4480c4408490b003000000107091a0b581d1b072601031007a0500744500b0391070140300f409040000b00313900300c000d0715101d60261491415810090880400e5981010380d82000504104c00399a010816070303042080d9580621a074002c2d0000360f51150078a00e5403951610001ca446000107034003602d800d411501880701005100700000020301030744594010050798801c603001265280f012802640d0700c0580c0c0c0740a40d411001e0541d02c50083e1265401e03078105990f004001e01c1841e01d0540b0552a002c03001c010701100180c948201105610f28072071300700727115100200314407061484a0755034840186640e58115003601e424501040b44004c094015105ca119102d0042403843d40501341070160b45050315209810343c6580e44e40300c501c0c129210100c045540b21400003d4030780320b05000c1c0900c004143c80e00c1e191420880c500c842166281e90246101c2e80c0207200407400760760082002d07070036221484035030502e907034940f5100000c83c8141d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 911457185 1250 911455935 911455939
    0xb0a090204020a02010b150708120912030a1d0604030915051e0c15010506040b0903010b030d1110231b04030b150607051f0b0a09060f05010239 63
    0xd03d03120300c181d06512211088004480803a00401800e10004040c01410001030091000b0492011322800440d2040c0c0d00403d08404c460803004000010380f41078000342c410070035551b1103410180080c003134101903000c8000400002c050030b2401c0c0e01d00801c1c1c0800341c8580c0070030941114040700502d20030811613107540d840001105510000f010035104030ba01c00b4a500b40103018100d0503c3c2d04410b000750046c101e5000801c164100fa0900c49011195803008540030341c550340c0d5504410060300d0500641641049a0b156080100c0a4540e42400c0000072186120300030700d4003100910749100c4524100314604826640c2d211940c440c44100301e42c1c00c00c0e0740c030700343c0c0d05902050000c1007214800580e486468043c0c3c071148030700001c1c0e05000300b6001c0c4c2c0380001c0c10340d000401d403440ca80f0884450a55046101c2201044500c01c00001c541000380d2500500090768840c4802d01580303d424030000000d00c02031004108581d0311054240c1c28140340000f8001a50140481c1c40260380d0b0000409010000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 911458435 1250 911457185 911457187
    0x503061908060103020306060904030806061c0f050402030c150f07020a1d04020102070f0302011b05030904090f0203011b091a07120302030703150614030c0717040819020d0b0a09020402 81
    0x1d5034041da5030380c602484100e00c248501800a030b00741c101042442d00680c4c0c561240f0101e0744500301000700c0d80d0484010602c8200789808111303c665001c4c010001060001c03807000420741018010f1500745074118400030301801e80c140001041c80b505c41c0480d001c1c1c21508100c551a45082c0c40011041c1c00349a05c0720001505803d00a0742c16005040003e01170751003602110f206a0340c2c0c18201d10b5640c51444080c1c00b0941401e110081c0c0c03a203400904410300e200d5070940c1d01d40124100020f088820032070040d101e009400e1078883c00c5041c00d11407200e00102d030750701e4810101c24403100101248803134051490918189102131102c0403203441a111000e0b4060101044207100c2e54000340250821942c40c03001a04003034481c2038100d00810f041043d9501c80c0c0e15070012001c05000003e980e40b001d40b000a4058041156902080103403101d100b9043c000b044043da0b641c1341030001803400ca21103202a01303d815500c07403500142d8682d800c020301e5950010b05051240d076010903000041c01d02c890041d4000d40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 911459685 1250 911458435 911458439
    0xf0f050103030f0e030705010f1b02150409063003110a200405070219021216060210060b071403071401060512010506030c040b120d17011401090605030619 68
    0x18115090083e09001030740c80403800b0041508241d0b88100c984079050102e074202041101080c801d01c0d482c4443d90350050b001c581840300743d0201d00b04000e8001c20440f8007070082010f006108681c080e9000030411085800130184941000940c4200001c00204400d240c5164050405018002503007426001005849001d0380701d05000040396244444510b401c00000c00038a1a45040d2048a0049425600a0413644194600c00003418000c40d400d0340e000042030380b00345a8140c20800d654183d014810b0060546180c002c02030700c1c150301d0504921940b420840c05104640c44d0a00340d03900c1c0e0390480407000300e43c10892012030551181206c05800000000e00b0f00300840e1054010703c046542c01e9803265803201340811410300701c1304d0950302a035051f00102808400b900c4c064000040306100100403122203207039800c1240c035044a400095002c2440702c001c1e00c410f404003482e580d00400c41c0507507010040071440d000a040d0400350081105000c00480400c01507101d40441d603904051020502090176 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 911460935 1250 911459685 911459687
    0x602150907380901030b0306070e011107030822050315040204020a03020f0a030621020108060d03030b0d1a0c1911070f060809071220040b090717060102031c0f0f05010303 75
    0x160120100601081c1030286d440a2400c00240680c4110015901c3c0140d418082c801102c035032100302e01186847c4203d001c0032001c03500010050000c4891460f20440c1c0825991720425504c0300740d801244a44c0100c0030003503904080c800c50650041e4111001aaa085146016802400f17118907914203c0c0001c56078110441c0c00d544000e050b51a800c43c2000e01c00003403c2800c00f00700c403c034030003400031340711001062460a00b07d602d001064842c2c140440d6040c0110040b40110982c45810341d40740001b0340040e00c02000c20750055403c203414401d0140b5000c00407104a50342050716500204000c031240590403072420900c00c14010b0400c4d8103c91000da55510b00040000c00159009800f40c0101e01000a4040d0160403100020380d00c80240c00001e4203c00940141c0c40c2c2c184143c5d50080d0700d44a02c49060342c3d80c0801d0520541c016164005030040500c8050900390000341a103040d50f00070071480c05030301280040b49860003911600402c0380040b04841d40d020b0b140c020030310f02d04603050500102c105 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 911462185 1250 911460935 911460937
    0x605103605010312080f190906060b12010306140f1303020a020303041716030314030408092e2f0f100203060310060b040b0304141204060215090738 65
    0x1a03c0d4030780c1c07054041d490340e01b083e44a4038030688802401c0f0700c00e000320b21801e03400c0350010b400e02c90043c00c0014100e40d0750540b50409a20400c00c0c51072040f0000300600130410580b00f4261205541182420381e40342c58034213022524005421404820b1180c01c01404041c801c20050840c243e01030240e81d201c0c4d03698016400d481d01500d11926450103455404e5070b4910980226408484d016a15051742c03c4008041c140e569101400940b00003404012588042e216602c0903000c103039403030300c50403041c0a07030001c000c080404000c2010100b020b029a030700c102a10808030000d07109072401c0d150046044002081e840d0400c0c030400801e05004141c3e071031003a00142d81c06144201c20550030741e80c1c7c10404502c42c1040390a2801054400f51b402c0c00b0a00680300004040c542c0035208146414050648805542c600200024900541d501c001001e2100719418041c115280b00d080c91070302c1503420140405a00d58410380603480b220300c0503d10714801c3c0340c0a00d081c0400b440d0f02c07886003c045041c003080d519003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 911463435 1250 911462185 911462213
    0x14030a0c0e190e030702060a0908160302010311280c0614060307080613080a090909120324050f18070c050c01050720030304090c02010906051036050103 67
    0x12148180c2c1040100310124011803140d904800c010314a484c4240d07007001181d4101910a41c10048401004500d58104010180003050509903080711a4034501c00142612856000f0620043d41844285400c04000035001000c44601d849000ea00192502c100d4071011080340140c42603003040301e008120703650081c0300d6005034810740c243c0305600e485422580e41c4090545005a10070700740303043c80010079511006480080030901c0d00100f540d503100c80c81d00980e502114140c8400c000540b5840700319815200c2c1000206608020314006040bd0743d00c90282c4841d4444c05000311131001d8501825a600136100714075207460704002c500340c103040400405000550b41c08071014400c04030382c0c2c41c0560044d01a107420942c044041c1500e10500c500008951481d4030704030350035110a11004c5a0080316004e0070303003a65650b40c0001000c81d0a41001c2065400282034042d801000d4141403001e0541c110308854804280041ba80350020700c00c00400070706040400400402e86003500102c1000b0101c20341441c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 911464685 1250 911463435 911463451
    0x111040914090102070b0703051f150206090c011d180103050601060801210230030909010f060c0b0705040e040b010905073608030c01021908010506030114030a0c0e 72
    0x181d03540e039103411401c0b4411907074054110b1000b900011a0207209802090740880700703c6800101c001c3e0310880608000441c1c11000740240b8600b624000664100310032a8440707003e10040c44400201b2001a140c1e40c03502890342890700801000700341540712522881648503140080e207545680d00d00b00207403035136020b0090800041c2d10700000141c00c1c0ca680c2d00c884d060f996103142e603440424a42d003041072486500200420040c0007003401c0300c00340c1400d16882480c1181c18091070307603900000e040110040050b000108203401d210814406540d001a41c80019075100007a40400c0e12100015100d03409203600140c241500700041004011061600304d040703ea100e84248655110900140c83e10300342e01d00c5060741d6034420008100e2125006800014400345c01c2d4189410341d4071580014111340c00f0b020b80300d00030381d00040e12204840003640071100c411700e01d24210b41e03154100400103d407480b0621440a134560311070100d980302e03078050000740e4640784c4c4004a810140d5440e54a032a1268048480310 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 911465935 1250 911464685 911464721
    0x150f0b10021c050708040e09010e011508070605040e010603020f16030c12050306090609070c08120108060601110304060c020a1e24020a1217041b1401080406090501110409 75
    0xc50018081d000340e03031940f17900500c401d06003070401c0280346e0000d0008000703441c550340352904c20201d04000c0c801c050f40c008501c8420b1203a241011003240c9004002d520820030072200300b000f0450526504017841c1504d0003880d000d030b61002c0c40f1070640300e540603400080c1401d0603644c01d4042019040400840d00714850044642401e8128606840e2030100703d0b501da070402c005500040143c54402d40c081c0c0d1021550600e810b841086441d091102d030004c91200c20502100c1005009003d0100805540484240303056404000b2003415640c403030045120344d0060190881e402d00440d990111441c0c007820540c1020700701c24247c0b004032030356a041c2d4440c8802100c0c003224001c003058400c03d00408940b065800800003600300742d40d64080d41900d0510b8408115981040f50318003607140e244103004034042c00074000341c001850340c40c071940446544144288100329019465030790b00901d101d0f80c05038106400052a0480707061260141510040000b20040b000402050514040d40640c0d1240c0340400d0f10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 911467185 1250 911465935 911465983
    0x503131805010b161b031115030c1e070609060f0608010c090515090301050414010b100c0b06030a06052406070f081c050c0c0c0d150f0b1002 62
    0xd030100c0310280a201c980000c100407010200c1c0a83e22101465031140c000401c503100f24221072498204180c208a46400c2844800c41380c40c81d0144404c11211040704d0404e1a5040c9005403015911030130111007183c024010003441480001802e450ba0550044024080c2000f40d1074141e0003481e034402010041c5213810350128020740148284003054500ba05c2d0283c100d41418100a07960202100c41035a0210030070520005444c01e0080c40c0c000da00c5017284030f0071110540c86903803d49013603880709401190359a0702e041c8020307480050861040e80100c0040175603100d4801090419543c1480541400e0505080c0300005024054480e0950320000b5a01095135600e801c0001e188100f001c00740203904a102d81d0004103560400a000c0e00c404d40070a090b510b48011031944c00c0d25401c40301f801000d8030101c1d0740f031356a1400348444203041c5002c0710069149940e946d56001810200742d10740014596402e42900d58040592000c2a400c20082011350800500d0380001c3d5902034201c8580340ea01205013170 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 911468435 1250 911467185 911467229
    0x30206090705131a0a0f1d040807030e0102101a0f062d070b0114130b091501030e011d0d0801081209060d0f2a050d0207020d050313 58
    0x49909852004020010286a000c98000a080551300c4c4000e21069049070315025621450020f005202d01d640c0c80500615000e1544816880d618481c10803400142c1040f0006940300c0803210019070505252955102040c0100d14080b010580940003a240c0b00400300d40200c00307001c0c1c100301d9000301c0d52030004113017410600800d40a207085105425010b2043c103030b600c1c510f06203060340e114004444c03c0d080540641320b842c1c40c0078083e8410320501101d0080500030342410815406078607900304091180c1d40501011490040000380b060f0207910100000581c2d0b684280c00c025101120b28000b44011040510301e281003010502110782540b146a0082d030b961402a50310714122a440c401400c00004154002600b5602c034010555000d1420445808403d02c68421409156104a00014101c41c1605020750406142c228854240380110303854104507400390072995591803240015032926982d10100794000950f141c0100300340008101c40c40e800742d000500f0411100680c40101c030200d003074a1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 911469685 1250 911468435 911468443
    0x903051c1a0607110f0d230c0103020403020603040209100b0d020414030706092108190e040203100302121002070b040b07030b152b02040608060f0a2102150703020609 73
    0x10001d00d10a4a0015078131107181240000d000d500d401350007502091013030740d960001710101003c1d000307220052400c100c400340c02c10408091080b00c02e0074110320707180c00e6400042241c0801400280328454000c006040041e90800707400003403000c07841c81926141d905100c40d010350040c2c019448a1032114150382c40c41c2c40c000501104440c074607101e00090030309110803e00840350301e004080c0c188940704034803c0000c0261000b401161307541c21a000c68110039000c0200601c03000d22026203d80e00520500110810244000040f00c1d41140c205600d40744051900c0e0030f03c14401c03050303011184042106404d02c002c0300c2c09540f00398031400701d415260740e412409404454000d00708903001b50460391030311010042000100b0483c00d00e0380e64400f000b4030920654000070440e86485480c0c82d00030408201258200840c1500204201c0e035681011008001045c980d80082c415140745081d6241024141c48401c901c1a0081ea00078011442030f004140398803009503ca03090440061203040006070614602103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 911470935 1250 911469685 911469697
    0x50609040209180a05070603050601181a07020f1c15020307020303010b03060105070219050307080120070c0f060503150117040201360e070915030903051c1a06 70
    0x805541d100d49031844440380e030180e10660f81c0990320401d114003010840410046c0c0c01400c80d0b96010505103404800102120301e040011016120f04100c10b002039050240c5180780311080010303450701c0324002e000141048000c03803201d680104410701e01c144010481c01d8201c640d14090f8280800c19001a0044412440112a54401030304144010300c00c240812004503000f6070145861400c2c10415000075000100d50024407249181c403c0c0c0412450038240152002031620350001c1002103041920024040031a0311071200e455800108403082245418081010340050701c00d900310143c403110050560b500035604400c841c0124021030016600c074100c4d510b2803903c50521030000d85c039580c0c01910091080074659440c0342c0f40b1410154140004445680700090500054a8407860202015040c00700a400b20741003204141084c0550714103205a04080c4903030b440c002451290a0400311024050209011001600707020b0329156001c1541025120340d56041001d076608000c0310400003148160 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 911472185 1250 911470935 911470939
    0x8091903080a0b09070e040506041517071502060601021515010c02120d120c0e06070b04081c022718060d0b070903110d170d150b07060506090402 64
    0x14002010000348645076060304003080c804081601d5000100003402200212410b070300003511201100d8051034240251900000190740c200107035000342e9a90b41607050b131405000c44100401d00001c042090802840c0f006080f1040d0707030002d041c640c0300300070346a04040d500d0a0042c81030062680740c258240b040140a072028009041d1030300c0780d090065480ae500b00328180d03805859210300004140b0248000e58080260741d4901e003007041200091000c030f500c00c07a01d510400c9804084205c041e29250100c84d045900264842071640d00c0b49400b02d40d0744580c19400c0710f11408940440941001030b0054000a00841d0300c0c000742c5841c0c0b10403890300c00340360850b45510850346440c5041d00c09425400c181c01c070801406003007403080795849007400f08109980410001e00380f02030810a10040c001702a0000c1c10844100c4641001d0f074842a652007140391100716003030701c001115400362410b40e012010b000e10018081490907601c224540c095003101030169022401c0200207001e0707203040902c0034816030740 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 911473435 1250 911472185 911472223
    0x406030f0c0f1809240618050603210426100e030d09030302090904111302030630062406090303070f240605041a100f0215010b09010809 60
    0xb004401c00103000104c4054441d150b90481680115031400e1741000701003451200894043e01d030220206184411000c2440714500c0c15050160503074002c00c024141201041e426050301e00c1c5000000414420350388800c118440000749804410740d0030170f006110940c01e0080e40c6115002c406000191864070018106079082000ba40e010000940e01c03000c6901e00910780107040456150110740d10410685080c0c5202c15030100448480c40c0450034401a8942c1400c01d60460070808046150b02540c1607041c04152a8046101d101c200d5984030805100d41703c008440d41818256035040c80030842e69040c6d4101140e41c0c025020b981041022184103181c041c0085142000399250f401031111400012604904140c0607031504410300015882c84440a020010b1110301c0d1000700011102e26000000503040d185a00304034582e1005820300403038190341000c0d40d608080300000c13810031100741e0004010307469120021901007404800750919a03000e0302d031450300d40c4410400507178039032900000c200607000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 911474685 1250 911473435 911473469
    0x906151d010801031b0f09050103060c090b030f06130207061401151e0917010f06050114071124090a080303010f15200d020c0111030a05030606090406030f0c0f 70
    0x5d0514a6020344808440340d0052031602c036080940d401105030300414425440f2401441440018456851400404d083c104090ba1038903a118500e0700004124140002003100020001d1b12000c074409440c081c0340c0d404654070001890008020424840e0308031160080000104092034112043c1c400e46d02240c9403c1590064172840d585000903c1100d035081142c00720002406030b6443ea124a05134286000100f603200c0351400702c03c01c407035255000504116005943c1c071520b004441c12107140d00d03002050780000c9130910000ca04000e0001c41c0c00004940e058050b0481890044003905001400f12640324186a580220b959240003c0c054900e0b145a1a101000303c8815007072400b02d1a449810b01d0400d003418810607190702e14600700204441c1e0400e40740903618590500074110189401d00300303803520303007041c685030f503520702511040400740300b0004042002981e0b003200360f4248600042090281644900d89590644103180f001c4a21080b110000308407200031100f2042aa202d448004c0000c139 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 911475935 1250 911474685 911474693
    0x8100e1e0f07120e0102040f080f0f07050d02040c020a02031006170a030e060a0311070c062705040903020709090f020102060c030c0a03051f1512020702090a02130906151d01080103 79
    0x104c44110120b00a6508100000c5d107070460400460051241401a0103900010240c0c00e0a00a039100701c500150402c100511082d61458090524250150b1740000d00340e0420400b03a20707220720340c034029505116088140b642200240c2006c0e06680c104c2204000101c00d000c0e05995440072900b004012800c960400c0c052801c200c00980781c40041882d0110300751005102e4400294480308044e5624202c5190611501e600000c071404640006003040c403401242c080211100f408900450b4070440d25441040140341c402c0042e68041c00c000303c000c005803001454881e40c84494054124090b005200c00210180b072038000f624801d490300d40c0441c2c500b4441c80c1007207004000c0180b0f109041c822401820000e6000300c201d00010f8820420080266042e60b10094440c804140540384141e0040041c400103803228407001c0e40002103141c01589603107401c055606a001e0380c0c2c00015916160660004107909003038110903c00250361100030b100c00c510407034100c00e1840b0882450120780d40200400c005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 911477185 1250 911475935 911475941
    0xe010903052e02030c090a05120706030e010b031204030c080706051c020f160b011e17070302031605090f0606073c05060f070f08100e1e0f0712 63
    0x1610400b5012500d5110307203000c501c200e80064031040e0410801082c10609814400100c0300a42001c4541000c1e01600d0701c2c0c02a40c5ea5414000d207420140c0b40c1070440d42d591400d40040c0342070400182a182e070b04420f10320b040000c0d0800e10040d9511076601c440040e9040c00886d86a00769210b554805285c91684041d025030001c00030648034826074200305100300070300d40c1c2e0091300c101e51220b03d42c81800222030800c041d403050103030080c3c10903a0340f0000038a10f40c5105002101161554180701c080d0040080e5102d0902d00a640041d416014419445808801440b407240a5500486e0850010b480300300200304080400c0b00d0340d54114400b0444580460010012400000490500c9005441074415095142104400e949043d4496400711100300a000c0c070041d44c3c0001124030414151500b22001000245252411004c2c05500d0001c5000d81c2800d0034448050000034034038076000d051a003144103003000c9011110300243c071180003044905800010340e502030003075a50786140c0c028001c08140b0003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 911478435 1250 911477185 911477233
    0x40807150507060c030b0306010509131124070506070f0c06020702280e0c032509030501060b030a0b010c0201020705040b120109030804050d09051804030c170a0e01090305 75
    0x5202050044a0000700d240c010301508201d075590200303c80c4420010305182c104c040c2c000c3c62080c20780d03804011180500d401c0e1820b00340e4120410702084070040c800316964490008420f41ca004c814520f07882104c254500510600748501d0472944142d8030f07884c4c1112011449142d060004051645a001059640e0068040c2d280010030b100fa00300400c096100107071640c56454107a047c0c4000c010404a28808012903101411505407495403401034805a26680403260144014003141e400c15081d520070326114000e158804000c100c2d0310344401ca000220f800c1180d48015181c2449021401544610408a441581a002083c403a0300300410800a04400c640a5402070084007a004c08001c0034014885501d0098440d404141064113095040c00001c1a048041c8415034004103d01d840f840801d41094080341410070301c03900c0c0ea2804407881d00e0f020a01800b010b903a0185040cac000d100c040105024030a81e29101680a101c2d40103666555280c0f0019000380c0192000c0601400e4503608904 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 911479685 1250 911478435 911478437
    0x708040809030106090e0c0901030213110d0213260d0302030a090203030f1e040b04050607021c0c08070f0308121f090501061403160e19120b0a0204080715 68
    0x10400c1d08420200b400c4643c154801c00d00d8035216590308028043c144004405608192004141581550085401503000c0884149101d90b64003850500e0740203070f0306555911407440320035980c50552002c2801c491806000b444680035481c4211318284000f10459691847c1c1000071340502c7e8080d400c1900290001414001d045450b0000700700103a030140010000d00f82d40c10f20b07007515036414400880028020000285040d50100010301c4a114a201550100e40044400d16644c60380342c03000c1017180010310070b40600c0d028094103510411444500030000d0f00c07440f00c110740e40c1a40c1c1d030000c0740130318500c1e00c409014070904220806010a05030020307a48440d0140e06503a032411074401039424240b075036000c0b00321159210300600c1400d0f480104c41c200d80407074101c00d5003035080000d000c0d03000311003d1501301c0c00d2080c1c0c54144880c985481102204090001800201c1d50341e40c3c840703504200a28041c01c4442000200000e0351030f1400344252025500c41d940200042802d0039001035144502c525410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 911480935 1250 911479685 911479687
    0x706110607200f1c030504150e010207020a080c01080c190e0f0907110c0a060509010804020a03060203071706041404030c08130603060302131e2a031b0305070807080408 74
    0x4059800c042010b070f00240c88400040071200c80040042c07800031000c102400030507003080705000116280050406450360703030200016102c000280b031a802449041d800940003000620000785d9440d001c110300702951400e898200896075010011145842880006103059041c00749110151340702e4080a850043d000d4034040000301d03568001001c3c0941201c1020002d030441c0c1c5030b51f21241091001030314081d001d0307400484680c200700000d000d0f80203c0302c01c541040b00e00c400003400d44d691201e06c1c41c01141c005504640e07a080030340740144209640a2403001d5680c2c0301003c60701ca07040910030410098802d00c0f401100b40c845540c00c9458001a071406e444480c0c0500425002c036181c80070200007031001c0d4400040e05413861041c084041403c50001114514200380550702d801d580300c0c01540c030818404c000907a2084603d0000d070301c1803003184c0d140c0c1c02403080c1480d0100c00d030117900208414601e901d80040c00081751100310159401140c01c01e00040c600808034913110300591000e13030041d101301d21807 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 911482185 1250 911480935 911480987
    0x60f1401051315050d08190f02120d02130e240310051e0109050f1e0a1e0e0607110a080901200105070806091e0c1b0a0809030706110607 60
    0x14176000000070342650215000202e1803142c40001c0c80084180e031190801100801c0d03035040180d200ca015002e8850014800240001307051940c3d412110f80340d6089a51410103500d404001a1080707040703a920007070200c81c0c022501145c05004002c41d480304010000c103c1451340400000107418040e1401d03030f030261640f80c130a1203501c107000583d0103464501c000290618044c911041056030152250207003651040300603004080c00784200354020720f04900480ca09a8400c82683c0840a081c0070440082c9408402010300e200412424003645041d0342e141211007849a00c691550081c43c0000c00d01002000307110728550281056100038421300c801c18030350081c103004240c2035500c1255003200162000080048529004d09203039044040e09412802d0303000c01c40d43c6084000c10180c03004070203460114000c80100c03240000c007007219142d207050b0303940c500083c41c06c2d1035550452500c05109015900011800c85d1143c0c0d080c0d84415101c80081c6505d03101c104003668174440f050702940440000c8022 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 911483435 1250 911482185 911482189
    0x110f04090b18010e04052112060a081006090b01030e0307060b04020f0304052530050d050414030c1507020a030c061115091c0e040603060f140105131505 67
    0x1424001c00b09030520044500d17207403800500704441c16040a90700fa1051103220b0350042108140c4100d038030700605c01c3d440342d1201000602d07444001d90013518036114108094103004465005001190b040a02c1400120007840041d0260b8804c5405149154414841040890203582003c0f003595000381005141401083c02c164150b4401c403010758469002c080c064005100250701380c445105c01c200032510302c6042004040d1203649003442840c16516026080c5840c854194000e901c5561200846400401c8454054000c1d0054070403681c059200984103801d07070070081918030001078014080403040d61000315580301c503004400e040c2d07005200d03104d01000089050139058050029a11200d0b071282c19401034030710b8000d40a01c801e000301d580d0000c1c013407030341000144c600d10b03010344400c0c0d04280746a60f44116040035070208101c0c1d12a04143d000414004035501c8000040b0b01e11100307000441516000751040b02c020300c100380d004003c3d0742116520b519186d12804081510080384403e5640e1080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 911484685 1250 911483435 911483479
    0xa020a05030c031f092013050402130903120501060c0510050705030f130b0a0506040b03010213140d1205070b0106030b0a21020904140c090114060304031407030f03110f04090b 77
    0xe100500e50b4480c038405032941c1f424400c81c0c40c40c0d9007107060030f210f41d15269001c03d103800701c2e40007194200d03a260002c2504050003200066144510f1400c2003140f90394a9000404117642c01c40300340c1c1c560040903881c445260250107050310840b0340f602c62502c2c58071014140b44014034010444000c00700c80c08068800140241e41d114000c0100c09408189821300400304030172036078610034140c4079031701c104040c005c41001c0401d10300448040d0030050720b01151000200303105080385403004040101c8040700c001ca1a40080c0074048060088104030282c2c1e8030385c94250110b4580104003a0b102082800420170520700d040c601a1201070803080c0c21561080d540464480c00c81903c044508180724911000d5640e0100900c5140a400311022034555142c012600103042402035201d001d45000400034080c18000c10031076814070502d280715643c8605509000313000c5000318140c0d80000b803c1c040c2500c58981741c1004d5801d120b010814203490705140000b040004c041141c41e003030f00a446070310f070035402c040001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 911485935 1250 911484685 911484713
    0xf020616051c0f020703022b150506061813061805090f010507090e06060909090102090a0f0f091508030703050a0f05040f05210f0a020a05030c031f09 66
    0x9401441072510100b0914030340404980810704100c8030000d2407190720750014201c1c00b242d4060b5000070b035520344000c0e200d200d0345c2c40c0450740014036100c40e495010440c6080398540603809203401040240c440c0e4080044074419100c000440c030f5801ca1406171a8a494461500110542800000c241b40d469901c1640000001c03000d480c0c0540d00c0c010030110000a12a04a410078032500030815490401c80190400041d40602c8001d4a0707404001b60003500c0e1181240d0700600d0003000200d035842c101241c81d002c0c1d4412418180110381800d03000405070710410005064440320303107604c280c0c5030a140404001740001056400003111144000400e40c40c10310040501e14080e0392502c1d07032402c007240042c10785002c19500000300b00c001c01003005659003056480d000e5500450f40c8580351352071001a072018000c400b041b01d81501800d0044000128001080c02e4802e06c00c1e20303081c84199880c42056201d584050550344c040d00300207483d041041c61a0075290310944d0070750000514507040d4403003d008003040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 911487185 1250 911485935 911485943
    0x160b04051c1b0e0a15060810231c020f06250305040806070206060d120e0405070305091b0315040201020a0b0c0d06290f0d24120506040f020616 63
    0x4003003d12a2440718040c040e8441c150307103010700c000100c410380c010f20001e4501c500c4007040300d0038010801c00c01c1080d1206c401010009080d42003291200d8100510a11460b8a035120309400c03080d401114003111824040c2c86d40091400d180621b031171050201650012003081c020074507103548100c50501400c5600c030711500070f81d1102d880e2814545e803140b6104002d400407007954440f904000c3ca580c1d80c0d60002c1c004e43c0e800800344060000c680015500c0303145000781194458104010008081c0e130540c0312a2060014508031010941c640ea41c03000300c5108800350b1a0140c0103600d000003080111011260002e1041c8125403002d80c554031458400340342038440b070019240004d1b450880c0441d5006500292002e8600f1000a01402070000400c50f1004014040700f80c0c0480c01104100322001a40c16000500d6014484032000c180f01c9404140701c0c110f201300b02440410f0209001c0b83c95502c4070402c0d98407800030441074480c0d86030408004034004049a108004000c0c1f10444e0301a9a0602c178000c0c0710b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 911488435 1250 911487185 911487233
    0x30703020f0d021e03010b0a03170f0f0a08190e15040c0503030301060503090c0a080c040c18030614070906081f1d04060c02121b03041203050c160b04051c 68
    0x5408250035915600c1070244034604d401e00030710114402b403103c43c2070102810800c030f80d2290080d80b4071032035002c1d999690302d200c0c0010850460700741d04000c02c04d1040c6a10b5000b11001c498241401085a00c0d100302081203512007844a440c5d03040404040c1e0b042401201901440741d130303580000b455075009801c0f440000d2000f00074410060300030094558a00c0c411102c42010034101000541d4030f101526011748903944448003682a14041e0504e40c1d9100f1079840e100080b0742c0c40741020f034050503502580003070014818001414191040024101f55441075840600a40301d2002c0d200740d4030b10743c0c240c8414408000100151b080d4001034440c00c040320305c034140e07100f911305401c1c0b0f182103034002c9000d217055400004000071080f60307a401f00c030740041c0c0a410018165142c1454541780d80104d0b086042c0305060610140240f5400801030031200e400f402c101c0342e05010403181349a0780140c1340b16001c414217042c4010f000e1440c00d0764288110b107601e291150884da102d0740b28441c03c11070b807000c01ca5282c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 911489685 1250 911488435 911488489
    0xd140c100e0d0908011406040209010c0b011401020f0601061b05011b0309260912010e070303051309060305030a1416080324210f060702011b0c02030703020f0d02 71
    0x3401800503c0141010700003081221131402c801d00c0344030307401441144960340c0011000b6090b03010f801d51a182a800012490066031200340b43c507031088507001103d000d84900002c6e40ca41120004000d8141e4800795100c5130141c5d4407000c41010703038003105004c90b040e5480d00c030054000c41007204510000702031543d010442111a00b0111300302074504041c20382c081407801149148240220403543c3c1108142d42d607404485081d45150b0040c000c2c1442000c21780118900001850b03800f00240203212420310b80d614445540d0300369401281d04034840180740c1d4200340311010b01e4a0240480712601610a0365541c50418045110818590b10035000c13560305601000303202c040341c0050010358800c4072a420014940300c55500080e044c1d444074441500420360030302c0e0500c11340c03401e2100005900c2024101e6101c1c0c01c18540280c0a0000060300c01640c5520902d0310203d1480707020b103030104c0d81c3c024014220326821a000e00c040b1109180409800c18002c500b03240060b05c0c0d28007851068650f000240d45151 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 911490935 1250 911489685 911489687
    0xd0b070c0803091c05090d0213021e090a060801080d0507062406120c0503040b10050904110f0d230c0307030809030106060c0b0a0506010e0a1203020f0d140c100e0d 72
    0x400313280703484104003061203282003e8542c61006280c054045400f02d0180321102001d2020b4420304444070005c4049415200c003400711a0098000000304841d020441078444504a40b811402d215403800c43e44800090207605000d0401080314070f025420104107020713007190521151030080445104201d011204000b002d901c1121a2285809003405100e40d080c030311001840360002400150013000d010b00814200c13002c441700c00005200c080c2620300306203030504100170103400703a200090203400c407c000f0003d14900380e0080c8080a41c407030014810703100030940d60051102c00b9422120070788204402c5c42410340d410090308004600c9004d0b1076650344d030428180341c259405548440c0500004103140d03400030ba240009141c0c00031065000040d503580d07410049880205140d44160441e08000b808102100c0840d52002c1d5503000703800301c5450480c4c0c941020b90301c801106600c000034904000301c441f4a515400100300030302014084807001801108130b80226011206e080c041c80d844040c104400c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 911492185 1250 911490935 911490973
    0x41a090703020412021c02041e0510050d08030a0b1309110405010b040501050d02090603040f03200319050403061410081b04020a1709070602010f0203060d0b070c080309 74
    0x41240d07480c0035802e1520344012036040e0140018000e10890740b50a80d290180c05a40035100c655030014000e0000408049021722040b08400140d4415803c10303000030842e140c0c100c0c01d082111805041c1865018240e12601d0f0785800150021030710070b8882e800e2034090383d5411348000000c00c0800c400188280a031500640c9000c51400c00c5004505000042114030440d90554017199003c1c20102d540d1046604070800901c5821429035010344040188014002803407005428070344282c5820411107216071010310794204009107220168810072640c0c07200721440410102e001d20a0030014289074480d55014151082c5002c221000d0390b03481c7c1000403218442c182d40b0010002c500140200034050300c18405461515000c007070145800140c120f200e50322950400303485070129201c11009003441480c0c69100c0e0110b218150043d8240403a142c6514103034400c40780070340710040c60b250091005941e182d9940d04000c0c86042840780722041c80c004218032900441c8110fa0710809081c2c0740d500d020307881940f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 911493435 1250 911492185 911492191
    0xb100206090705031209010302030903040803040f1d10090209180c340308061f02100b01050c070312020a120c0b1b0a0e0301020f180901120b0403081302041a09 70
    0x319174021341c03c540017012940d04031110b2020038a0050f940b50340f8030710710030f140d40706541c00325540340310000300007820031154006882690307180c3ca000782b4409041c442c0314002a00540f894100040f540104108100c0580e000f000d00e500e018020a110002240e8411810700d0220f40c0c1c0020002700050b407041510b10905080c406000c00d0a0084010b151034521840144010b90000e003802203103001f1540307517900c0c07004c401c1d10010801041107160311010300080d02e444e222800d10010505200c0e440ba00d9600810580c1c11240c40c0c10000d0104d01d00d940c41d0700d40042c04c20b44c09030382076020380c20307203000032078044003100380e0b00e070280d440c1c5c004020020314000a8130000184400c01d8851030396850051001c2c900300315440058186812041320041200190091080d171444121001c00001c5006290300d158207280c2801200301d851907102d81c0e03110402016001d5030314000742410080d10006001074080d01103503400c41c0412101200e0240c903603000c036044480010b2000309030401c00d1404443e41c41c3c005003e42d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 911494685 1250 911493435 911493439
    0xc03240106080f180111030a1a0108060d0303090206222c070c0c0e0a06060206060409051c090509070302030405060a0c021f0e150412050901021b03010b100206090705 73
    0x445480d160b080904000e6000d13182d031000c1010604112106072094214225007581d40848903500e04141ca4803200402041c9208c4504181c0507810340070542c020350507207205a01c09422045c1380c6d4103d41c0d0031002010a4401280e000d101880780203078040c49442003243d04003548030001d00f1030342400902461101044a0001d110301d4403140841085907032422107401074124140a001160310b460065102d90040d007008514803220020441c81c0c0b151078100c881102c03100c1d0244d81480d19010203000c140c4a1003803001e026a8400c1d062001007412011a40c01058542c0c44d001890306e8032000002c0240106440c100c00094022041c013080c840d060000540003484d00f0810041c81d094200065200c01d42d01040003030150300b4031032600380c181032a000359000d01c01d10b2054442c030425410b10400d210105460907150618483d50f04c0302c1d254041c00031143e80c03681c142c00504280c9640d42412088080f2003240c183c0554030391008035843e480340d46c0000c0e0f401c0e141e138015003501d1420940b21841c00459034000b82c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 911495935 1250 911494685 911494697
    0x90b13020f0f0d0609030915180b16051c0e09060d02090c0d05012d06050f07030c05031204031404140409140601140901061706040b030c03240106 64
    0x200041e40d9504021500d00c000342c5400a24611140010354103000414025081904110280e01010340c050420000d0301d40040e56403a50720380441c000c0300c8642c201c2301074480101010800744002080700d005403800d00601c400c0c0c001100c03072a039aa5030400049040c84c800f040118100c2d00c44007500300c0c0d40d07100000700991b04001a46010300002d1030588000e1400f17030180307404101081c01103c0d03000c2101c1818885440901c150750351903003c0c80c01e80d0810030200c3c52110240842d40e18002000682c14101e41030380d035500c2e041c503580c00032102d0140c0c0a40b034200d0502402ca0940c00028500340301402110700704100c91350091509013400380044490094100b1007a0082000340030b40c4401c040c01c2c481d4400e0540340080c14024038606032000b551168005a0180301c1d04000183c01400118130741c41d19501511001c01590ba504025260ba100e1100b0898043c03c9000c0059400e040503032245e200b0b00801411603200005550201c0d041400d541e074143c4032f01c502c000355140030104032402c0078014102072400b1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 911497185 1250 911495935 911495971
    0x1e060912050313030e130e070503071202100806010e0406060e090a0e191406090706030e0304030b06091b030a0b0406080a3f1d04050408040510110d03090b 68
    0x8100083e80b0030700900f4009a00f40d0100c0c0703500da0f040c3c4e403a6212084802003182c44444045207030b80d10114896584030f445034041c04200c0202200c031001003076901418600b000c2650f60320664440d54000c20716410400340c156205403640e0b50340149001403041e62546070300c42a4040a110300960010142c008050514090304c450420000d1140d00c610781060825069141a01d0503c4028818101c202000d01c00d0b9828041103000c0442c001044800c1520100f001d140e52510441d02d0380114840a007038000301900094060420580c0303268406015581c01800da28200c0c2c20401a8005681800503140d981c500321100e41403070720400e00688000c0000740700c0b081e06a80c4100b0201507484050f94620389080b1070740850782c420545001c10201070041380202c1901300d08000e00c4651540380c10500d100e5034910320b0116080078481d13a4080c82c0c006100c6403400303040105004092546418a0040011402d90003250020500403084400610381d4081031500842c1041e429a08c0040d000030002030b010140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 911498435 1250 911497185 911497201
    0xd0f090c0e101a0a0e03070602012423060c01090606060e010815060a051603120f0b13021303050609101d0304090f0204050405041103100b0612041e0609120503 70
    0x481c40010103039001650b189003100303045520710042200942c0607c9800780c01701d80d8a8040d04101c040c011203000400c40701c040300d04140d041c0000d611405200182a803c0c04400c0d502c00441622164000f4005924107800b0741081400c40720310b00c00903503216640310750500c103042d8840003250b846207007440c12101c41d080007000b155980001c143c005200d01c0c0c001484820180c024410b4800c040241c05a41c2407000031070602074004200141c0034640390349040f94850400c07007148290000043d0241110030044e40030242c00c0000c0d44246080041d1384c0c00540000009442000100c1c0308045400251003420703043d64042044c1c490b5043c00a2200200c822001c4609100205076021203281403008203801c6c4d080c18880000b80700c1d0f070701b146400c142002c0c1080188a40d04101040707842c001c2d41100c000700560b103001c200302d501001002d503010004111181c80d103060400d580d5002170140102010300401c003095034a01d40b010314021290652141e401106101c000c1100289418590914030300d58940070780 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 911499685 1250 911498435 911498459
    0xc081201170109230f07080708070b12060415050d060617030c0d08070909020c060405210706150b04030f0311070506030a090302070f080f12040e0c0d0f090c0e10 71
    0x103026050304030140700e030500c3d10200104203080c5c0c515400d442c030399070b1a00061600c070b41580c0034101c894821258006011a001c80448000000d0000010280c0c2c07100010040601310354064032560100303490002c20a9a1440100e540b290711034200001c5052030b150346039804202d00e00c81010182c0050001200400c40400c034802e01c8402413800d00019a9804c0080d204140c240d042414014804154090442000142a80104c0c00341007280c00d100c0d00e010f00c40341c0c96440b110780300004820902000c0002481c0d6003001400e003000e2242031030741c00d4594070032840f40c2c0c1160b07005550300102c50724902c0c00d03d07411480415803001440c0c098480d440c20040072414038880039184400030f59440305058281482841108054810007034040740d91070795440655034400e100c9075003082900441c80030304070b8031080904680490783e0611502503030b5a80d111041a4070340001080b40c160540700ca118881e445410b10940300c803284544030f1100030a05003510300015180040c030303000d4100c0c1034803402e102c14001d00c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 911500935 1250 911499685 911499713
    0x1060e042a08010902210702010e010c03050612371202010b0111010b0d150b22150e060f2209120203161e0b0f0a0b0a0b090108070c081201170109 64
    0x59070752081f6207074610124014006686031810035480c00d130b0341f001c0c61941900102d0245004503100400d0991100180e515400c0c0641026009010b428030760a0b4100c103614500070f000040200981d100045c1d40f24050400c0c1c51486100050b5901c010180c01b42d07030480200d0761182052002049144080c102142215101c4440540b408031140080f1205281a42003205140006040f5440e00c0020000c10060014490720902d4a40c0c00c007161484111307240342d680000c40344043d43e1804207841d5001401342080000d04101d070040d01081105c5406c1001c0d2820400883c45a64005101716043c1082c40b84c030140d89601c6400c54004218030700c940040e003803a1990103500611400c0c07400e10340d0850104440840000140034054200030001200301122211380302d408260030922054003441c00300284e0321014001c1c3c0031518001c4c00b6920203548201c28466100341141012601c41c4050344510440c0d8100000c400b01d0581000011b21070080000e405003503040d4004002e00c94507140d6510700f20080d540c6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 911502185 1250 911500935 911500987
    0x106081b071b0929120705060d060e0c0a090605040501020a020f03010209030f030304051e19080d0624020d0507060e07171e060c0301060e042a08010902 67
    0x2940780005024405180d000802400d0310400000e13203203d595070141d0380340404c00454540540c0c010241401c2501c21042c0040584c809041c0321800e1070200032a0f90050000c903a070159403450086440003031000038a01804005030000c0d2a0710035904010508501c6800c5481000b00511080100d41d80000d070180005604640004c04d207480343c00800d0090144c101c07580d40c58401d0036005403c0e940040019401140202c081c0da10000c40c00c018401d549040c0c0d924203d19a020440c529034909506e256203102500c42d121903482d0200b41c4000406646c000e4200c01e164809a458420b0f20b540c101c00034404501c058000f504200011141c003070000c1c02a420054449922005c90f80b440345818801c18014000e50b644006040021912841e641d030364100d60410180d03070044841040280c00a0024072130b807140c0001d546181c1c20000100d034840c5c402110b040c0c000d601d40031064016951400340000c2d058040c0c14101e03841d03891140050034000103a10564507144104442c21041c281004085065020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 911503435 1250 911502185 911502203
    0x70c0504050603010e011b09090b0a05010f12050f01051305010506030118060b030717090615060a0e0d030305070306060815060a0c060f3903110705030408060106081b07 74
    0x980002c0f0f80949400c2c00c0e019219460004000f076008950405452018000e036284d0a1403170701c03085583d044456140c4a25407101c0c0000e000c100c198420301040064004525011030401c0380540c012007906d078140c0d80c1e19042005080140400d050441d40040005070b000000c0c449035140c1408544540b1040c021224601c480b096034010420391a0800d00082103040c2c0110b50741d15200c90020603400300e05401003c0f222000c004112402c030300042c814003070603041c0d14130134801050b2030400840c1c0d400303000120240954250914059540e50900e0581c444c001c1e00c0c081064034100c000201140e409401500c00d03c01c0d460180448070300c1e5482d500321541001c0d1401c0c0e544481c214425540c42e03010050040c505810440c00740c0c81e1001c180c0000d1515921160546401c0c46032129018030185a0401110b0b802c0642c540c00310002e01c00c0e007103440c4440e01702108a00e841440d0311036a0031544a50072003d01a80f006e030041008a81c401d02e5070768010f005101c1c0d1104000250003c221070705c9424005003000c0c0c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 911504685 1250 911503435 911503441
    0x60303030c1d010503090a241409250b120601020c0a1409280b04050a1a0d0201050d0e0a0b06010504120b070504150314060a21080706090b09060705070c050405 70
    0x20005421481e07000036405150901c92100c011420102c1c00b01d40580030304000345000c2707800326950100d00910207640a040304011694114a8a14560310700c4140302004007000100b60000300001c0400c40388a912004841c030b440c100291608020011650080190300004c1090040548000c4401c2c0381c1141c1d5031801c0c2e01c5136440e28102c862a0400c140d00003c000c1c0315200c1c5a440395010b60741841003590180074503030301d0b80c00900c102c8000c1020484030080b010900005440c025050358003451050405a0070076680e281d2300c0d4200c420503000e0282907849140f044c801e0004042e40a0f40c8418246045460300f0709000302c3c0d4040c6248040d0040c08100780001003009e940c040c00c00d03500904514405201c1c80c05542c68010040c10041d00072443c044500404128a4180540703c41d040e0780480308101c8040440f1120b599051901280c195609a01845404e0010f1164001c1c2044035000303e1001800d4100002454103000e0040e11400500c20100302c13410000b4003254210080741c0080703900051641e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 911505935 1250 911504685 911504701
    0x114070b0106020f150f190608162111010c24140906010501301b020f0114130809100201020a030c090b04120215040306060303030c1d010503 62
    0x1014881005011140309400810701e02e900140496050100104485244c84032502c880003106064030301e0351a04d8032100001e80390004e1107510740c8941c01e0305080042c0c1c2907a42c078005424407803080080a8550408c650411081143e00c4e1580d003003214110100800954580c0d030403e50001c411030b40790500c038a038181c41e070500095102181c081200c00d90403510495031010050000d00600d10642000c41800f00440c020b600000f800a05071641070711608580c01000b0411140000002d02140d034544400710110f0310490a401982c40d42c40c1e0510000541c56003000000c2c0c28202a00000c54080e80752801a50395803023004070301038002d84030030711040710780c0600d0501000600c180880b09401c02182440900e1040d0b05600424406201e560104611008003104079024140d5106188041c00e060000348208092000d0703550b42107100400d0888180500c06182d1025003140c1d0042d101c2d10360315101082410307018000c0e5808214246400403041d00e00c1074100c511001076400c1070303042240110018480c0f03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 911507185 1250 911505935 911505937
    0x3060d0209190c0509131e0e070909050c0102061303050414010c0210120b0607170a0203071b08060c0421030e0604031410060305060a020f040b0a020105150f030c0114 73
    0x5030301d0a80302030000030750010b0f0103041c0d5840003203030b6400380901c224031200400c494450360760f00c82c46d0044c1a458000d40f00084101404041e900c594003406405400201c440e403a1040c48001403090014000360f20fa51800a4182900240414036908400507808006035001040301c096503d8450130292480d00c0300c004035060103032100000d40080c00c1e849007501803900000801054058404148218070480c0e041c082540560000144400004c078001c0304c03604042400382c803403184584100ca0030a103c3c0e4035101101c04049a40720904140410b0030301030000c050201c20b920411071441545454a44001400d10b020528105070104488208400800d4843c034144034901c2320041040b5160394480c2814005454001c1008285114010344a902c3c040240203070300490360804003400c00ca41d03507070800201035440100c200540800801010400d0701e409400740155034026400012540341c051410058207104500151003000c00012000c0c403960009030540d01d030182864041d0801a51100c9000c2c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 911508435 1250 911507185 911507221
    0x601140d0f0606050a17060106020111090609030a0f0c0305010b0d03090b0901170a06080f0d022a0303070b0601030e070311010509010c06020d0c0225030b09031e031b03060d0209 78
    0xc17002080800181d52003d000b0150740d240f400314140c50484e40d98200903070880d0300c0c50303864280c401c000b400f0b1850940727048805815499000f80a440769609a0b580d000c1007840e20031001c85800034a5002802440030034880d080e1100380c00c0d10100f10143e121344000d000140d05108070303400755400090480c0726901c60050200461489240c02800d81030042d2800081e0005e80140c4405100c1c10008544840000500140311103c075000340807001da005107500002100315480c403038850300d2080341324244e4604100408225004c2c1148005a04014000400351a40200e1904e40f550000c0803d00200d0341000d03442a1042007401e1065490203410010785003031010080140010f07102160701c40410700181c01944485400350300380c0d07176441c0fa071001c5a103407900302c03000c81c2c1e480760f52594090000444024403a0703008145202100d040070480f03510151071140300450364010090120602c6400d019064070140c410740c1d00307407a1038254949400854400078a01c0d00181c071402c13103440842c14401c0c860307440b003030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 911509685 1250 911508435 911508439
    0x70302030709091509150e0a0209010509180d0203131413050a09021201201602220e0a0c0801140f0703110703030501050906090112030807030213170601140d0f060605 73
    0x50030043c14400c1107240c105519002c0301f4101682c22003100c5001c260008403940c000d08e440201d034200700600c02038004c02885460340c01c8d4081c4c007102e10882c040100801c001d12941c0156500c072100340201b80384c0800746d44456000340343c031508440b841d03032490001c4071445440c0400040c19641c240303d64025040344500a500100c015184400800781908503408081c002d4513003900c0310140700382c0c1c00440c0c8100c0981d120b224900c441250018500020000340700305d0701550300340706001c81c0e00e4801c0c2140d40305d41c1c0350595070b4010004c10b030070420780030f44000007401c240000b00300c0603400311106440604014100d420848600c00001c0c0c0582c081c0d484001d003580c20b800c46617103807041454050000d003003e004a6100726411030024800d842c140501c90f058505c1e501001925501d159025a400040a000b0b01c00385030f024803c1981003c030703040200c4005c25071059616080300d405003c207420460180c1000303101e030088402e038541e2611007000c40300c26140d00c03103566500324055042c0a80244007a80100b0707 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 911510791 1106 911509685 911509691
    0x312010090b0304050a0602220626090a0b010b0406020c2b170a031e020301080606061c110408010e0a0b06011206210506090703020307090915 62
    0x740c3c01c5407040007240c0e00c02a4075a9510144e07080340500b00605107180d0002031418401005250042c419070500140300c1002c1c0302071070201007010b24185041c0000c500440d4000f00c2c100415941c082d00300d81c40b268556103a040d07440c5107038464814030300148617003008528070b0302d002220007044401700003c0d2081035080281401c00b1888000055a415a040e0706d100b04c0200703800010420340c5615607001404100d00882d11184052032010b042c0060b2040c00180002d02000a040780c00070411520a0b80307800b84200441d0b0805104549050303030713500f0020202911400f0101500a81b81e8020080c031210100e40c00641e903c404540001d0040c403920800b04042c0d500544420710140000303580894541d440d81800d510200e2499850001c10001c0c4041030188a002e009040d00503000d030001d881d041c1c1c5940c00182c2d4417807003070007608609503442c4108410840e11003007104000301504014 = true := by decide +kernel

theorem cover : BRFrame.Cov 911330935 911510791 := by
  have h0 := BRFrame.cov_init 911330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 911330935 ≤ n) (h2 : n < 911510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
