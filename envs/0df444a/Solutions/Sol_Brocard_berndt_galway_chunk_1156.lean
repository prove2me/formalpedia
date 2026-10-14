-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1156
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:30:09.37585+00:00
-- url     : https://prove2.me/submissions/af099766-1fda-402b-8cc5-db1ffbadd280

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 207733812 ≤ n < 207913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 207735062 1250 207733812 207733831
    0x203160b040b1303050303040809090f0405031207022a0a0f0e01030809040603150c140910081503070b120601030209060f0a1e03090317040308010510030f060b04051e09 74
    0x1481c150b960840140f80b10103541c2000890351289403903d010f0019a003d00b44242c003543c41d66002c112802261143c10340642e5000703000c0d60408070150001071688800030602011031050000c4414241c0c1d503449002c510b40c0d1491780c1e4603550102801405281c0196a000204601442008002100014000c40c1c1520b0b03200b00ca450765480880c1c00200a0f006a400280025101c4c003e40611a9040d604c0300400001d140c4404c6070f0f005002c00703c11002d00402500c02d401000c90110351400c54490f02c849507021644422141203464604007003441c007417035034002000340074002030104065201003291650080e02440c0030343c900650040031808a00542c4582100b91001203982102d07a13010707199450f0b03220310307200b141d10282c074801c0c01c020050280e200c0140d000c24840291480144600c0302017522894140e101e9042c0e80e4a42420b110140c10304210b0a010159501114100c40d120f80c09081c004000c00701c0741d96281c03410725080010010000c1880e100503499240501000e07104d00d04202c1d030015144 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 207736312 1250 207735062 207735067
    0x709060b181c02090c040e07020706020d2d030c02160311150d050406050a0e1204060e0621070806030d080609060105041707031406102714040203160b040b 68
    0x40507504198084000c000c2d40881e020042045c002c10071005002262858213001400b6204d146050b6258640e078020140160400104400b415020707052080800ca09020030442c900c00c005000c2481c41c44044100303000036140c40400000d0303941040500c0160070b800c01d40c0b03015145944e40c1e904140001500d1a4050134014034101c010200042c00d440659040c254103020910702490004000c101c11100210800e2600a8072380f45280006031400d0311052030b01540d49440d060190541e060750701008169400201040b0320b410000c22804107559074a818100000103040240c8081c2444000401242c060b91000c005140c01c154428003245e0440401e0b11444050344039400125003d00c6150400880341c0b08002c441901450001084412207000d02200c400e5001501c00d9503440700000d8803180030401131039009101100c14249516060f0403180880c0031000c101690031000d4640102141c014500342c18200b1042d800c0a100d0f81400b061168814402e19082c2040080c0c1d50156005002405501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 207737562 1250 207736312 207736339
    0xc15010602030a030c0306170f010608030702090c090a2705011424130602071802040315050903160303090c0e240301020d022205060a080f070e0901080709060b18 71
    0x7030388598080c0a4962800c8c41c00e10303810005607650003906a09903d00e600c3d04000040030f950200586200e40e80c002d10026061b1030398824041d8640000c000719900c03800d20703140041c101405d03d403840d907079147c01c000c4001c0e08008a81e00d03d00310740050b84101c03072800220461010a0b500d0328005440c0c41d5400c14042220600348204682034000e003418040c40c4c01803100003050f0303203800140000889689a2300d06281c000341075101c00036400340e4440200400382150791401c2d41403403070b040035600c440b06c042201d04043d0401c1c114800454181d0060b0003003540c0720381c4078052040008019001e425a2001d1600a0401826001c129001445500800d09000220403070f00d940c2901100c1c0162136107401591030340225494501c0203c040c144014038606801c8000496084c4202902c0240545490308065540c0b40c05e030040304507800401800c2044040040103c1d1551200601400390800e540107000080c2000b01e020708a450a4022088140e0188104151021031402e2244010801d451008076100c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 207738812 1250 207737562 207737567
    0x406050a0c06060b0c1506040614240403060606110109050c101b060204050901120209150105070c06020c2b080a0908030a0f1b0510110705120c15010602030a030c 71
    0xd41001e10203e900217a26031301c0200001d240410f5220040b003051850701c0d10010030040314170314030840900910307220940c0d4040c0342076032000980041c1c00c3e0f4a0288640c030b00a8401c1d1035409034108541e4207075a00000d00140e41c2c0b002c480911161444000c0084c420310791a41a070301c100141da802d11805407078421003100c0b485007480303620090b450382140703403220901d01c2c0c400040c1d005406002d00444060000280030301d03100700c1004410790040c00c2c040850310b4040001308447c495501e400d05000301000610700040c1401410b90081079254041c1200288400c10498850914074900400c0340015031503c04118045841032811603016040765a00c0e00341140c141c6000c20b1680c448002400301040c0c1c46911500002401c907003451030b68840080880f020201040ba01c0c00200261090780290348d90500d00520ba4443d140c10000b2101a90815032030380d40762441d005d2146900c400180010401c00800d8408000748083c0e1401c45a2110196060403002583c0e800780322000c404040d10362007994a42230 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 207740062 1250 207738812 207738821
    0x618100e04050f06161706010309051005010819050309040e0c0303040303030509060601110d0f02010209040603050a0b0c0906030a1109040612020112150b0714150f0c0406050a0c06 79
    0x815040329000380d252605080d40c43e1010f05543c2c1e0940e004120014031905510310543d80b0311492900e400210740060380e91905d00e020014929418036690342e600c1c1c0302280080011509121041c1408a03096040100e507a040994912030f110750303030081071924000102c000c810b58404100c240d030000b8100c10b010300450302d0400c5c02c600254250000040100c2450343c550007480c441d808000841c1c0c0c55840340001140c60301d01c101d01045141e00092070b40d00040c3c1c070450a81d582d6100510001d8100980b0f81300040480c0c580350320485481d40f02000c824208260003180651021802802c242041908070109000c0c1c40010958550940d0300e405200b202e0808405440840001900803c5816120440c582d48102e9031401680440c02048024034580524001d0410315442e0320045561a450400c240285410100040300e80101036907295600d224208806912042c1540c0f00c844a400d205200d0b03210a803000d000006014010001440045c0c2c10000f200c1c01300c2e103a454411000780003400c0100081 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 207741312 1250 207740062 207740069
    0xc0402030c090d0b07030b060a0909180203060106020d020c0a12290103061e0501080c0d020d0b0702010915050c09090405011407050c010b031f0e12030903040905090105061810 77
    0x5245a5100c1041c4913043e03402c540716400f10303101000101010800c0203524001c0300030b40d4002660100d801d00c010303403d5400c91241d06641d0081c010240340135600090034450b0907000200180d011a180c0d81ca095410802e058a101040d904104020b0516413032010b601ca0304c02001c4d26502d40e28140107011908288900b5220a24080d0100c85503103e1808202030704010440c2040d006848010b01114203481c0b08490484065400800b05501c0c00003d011050040b030205980c080e00c200c26000c007203443c0c8124244203070000d500000785e030b001d98940b102d030400400180b8118180b4150810003061110412a107690808888002c80c40e41c4518081d4050540000c0700c880b5261544107000a990b0418080c15124955800a100069004060642d501c0003000c1004c440e0081c00840025140154071101f02030b0030180599502841c012500141c1c0d40c416200505542e100007810443c591691152a40040b89031009201e2418000002554000300c6003100a2500310a00458117982c140c0181e90001d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 207742562 1250 207741312 207741319
    0xb031306060602010605011d03100f0207060204030b0f0c04060801060311070807050a0c05030127020a1203180611033103080309100506010c260316031b020c0402030c09 74
    0x82e11014001d02a103200c0c800c8030301107400c150364202603c0381c000c0014503510000e0014072000851050315805001c084001d080d04990820414000c500e807800100080d6008030f200420138208812513030300b9107500412100e06a06d090009001807076024041c2c0d4110345291502040d2102c905000e01220712175690010420704001803101e08001021404814290040c690310341e00c0d60b03591090600741d600f64001c00b0b5411104e02c410302c00341040d66810220070790000d08134100325629070380c501c48032a00489050b0080707403441005d01d000507401400c04026100628201708240c0c40c00b11456540c0c0100640d110300c082c00356001e6040c2040d03940f1490076541e841d80c061a9625684d08024031141c0c410745040c5600e010700503912401c880c1e14080c0e54022881030b985ca00420807513441e2280f4007840501c40e041c039044242c09040113411107502450080c07501c5402c040c110006024041d080760741c4807400c482c1c0c4803c0302030ba80341d03010313004070700329001d01800e90300980d40c5e81d11503003103890501c0750041c080d52 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 207743812 1250 207742562 207742571
    0xf1207121d0c01020c01170c130f08010506011e050a17070f02070b030105060a20120307020f0706140d0e190201170609060f120109030806040b010c0b010b031306 71
    0x10840703100e01c2106100e8212800e4400490411004984039185111054080f9801108140030320b21100303861a40a0017980017a410020451b01c05c0412a4080e40701400d411030202c401d1000b05800c1c481c00340c00801c2420700d80d91039015214214154241c11000c1020b0041c08501c1c0340556000c0c0200e4141308103d52030b0503016240961b4080c1c8840f0000781e1440c018400c011003c00c1c60140c0c0411241640d8004020038104000c2120440781c05100c15100312440c41d40c0240702041007820002100140b000c0b410342d584038541480000e02c1c00702e404a40840c01d900c041020440075420040c601c84181c1a003400c190703103175804c20149020702010b107004c000502c208c9142c0456510303014000d40609200366500f0740c9403000c40c5084c480101d41a05ea0b680d002c1c10000200b00185040006d04414140141c8240b89410803440d00c1030858400d44800e4011960070801c1004518180c85000e01000e400d0030f207203689405544911031102c405000e4601042c800002040c0b03900c0032400280c0700300364006018070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 207745062 1250 207743812 207743831
    0x1810110f1e070317031803030103050c041404020a090c02031312020406060801150c030c020306040c030b0907030f02040b0411030106050c010f1b08060112021209070503030f120712 79
    0x9039200c00e400341c8181d550358800050000700307402003036120441c1e801080006500070072081c6404c459001800408000c00e2001c0601000e074002d201941c029401071010308407844900c4140030503110505411840f81521030100030040c0e075244286d20030b50319560790010b804400d540040e481c602c24012088803602d002000042d6140c1c0131041c40d8000e520a071828404a940c540302510280d4007070003040241e0004100f1500203900c203032602b48250780285044801d100390740d00800d080810030384094a00c0462000d0620070b0061a41105402012080080034014959141e0350221034400310001e10a5490700d02d0821346554941001c1c2404000005140e0b8950b5500e2000d8000d911950b140d07409035080c120300a442d18a036100f00303400b01880401c81c90501c08508411a40110002e101c281804081008000ba4440c0740c0b014054480d0a21918501400d080b1621031070b20b40319074045d61007588204014060914503006650202d0007c2d080e40969032100a002e603441070522295210103480d144a20 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 207746312 1250 207745062 207745093
    0x10140418020306120a23100e21030705070201050c070b0a08090f0c01050301260102040f0e150d0f030c1505060f0a03020a060f02030c0706030b090c181011 68
    0x70350240c0f800b00c40d51018643c581d90103903141c600e0f000002d0300040b410b12080c2c0c12210280200c107800858803042d914802c81441d2200c2c01c4034024510750f41306c1d500c022504000b05405905a000060780440c5560851038a020300078124071507000c0080c100040030500488100013003111801420791180a81c3e1a090500c030010881c0d101182c1c1c0ea662440350401d01134070030b172000c40c4140006030107950700744c84d580c02c145074501c0c00c0e590b0072505007180030001010403140c42c007072020700003524800d04035810252500001c3c0c2144003000d805c9641d0744219110000c0039603500200c048040341c0c0620410300001da2401c1c1a01c401d5440c0c40b0103090210914000fa550700142c0c0d000d1440b4450441d03d81441c10030403014000d005143e400002d4001000351020303c640c0e401400c0d0901240400c0c8100c0c1c1c0780c980200d440508080c416071010700400e49800704d8821524040000552010111207901d0404c0d0166031000c41c0202007008050007034500e480818421031041001440818418049690030313050109032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 207747562 1250 207746312 207746317
    0x30f0f0702010501081b0d061a1305010b0307051809040309080d0206010513111207030603200f0108060a03020d060207170304030e01050306040204120b060915010e211506011d1014041802 82
    0xc40cac801c6c8044408103903804c90078410b483c140c94410074a10700b10b540313800341507a003030348002e0320800e43d4100042c0440503585c0f010315a51046100c3c0da11034410900d800d07011441c040405081d1011b6411800040c813150f2540302c0601c3c61103607035034804030b42101e00c04005556031217201c0f020017000d11070004104142c0d416400c40030407607101e241080411410014040c80c0c40f00318440e810307840f540c0c4d40720405042d80710380032a0ba00800001c0c1301445490340c030f90025a02c201c418a003164104d8001c601d202c01c1c171801c003004482d001500040c0c90b26528250360003c26a800e2040060b045c040040301062042e11a94143c0b4080d28040824032181c06890418110b03c10f411104244039104420024001104a030b0800c103110106840e05a241681c103030401030703c4403040220701c02009a400e68090405010040b0300d4009200c448103000743c0c104a00010404841c006140f121703c1c1c0071050403041d603140c0d5003000c91102d00b00d15202d40b00c00e4030f240c3c041c1e07500d1160754810004400710903601c104c0d94089a00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 207748812 1250 207747562 207747611
    0x40e07030e0d0807020a030c02130212100806010503060a110f04080102090f0a140402071401050c19020a020d060b0102070320040b1905011d06030f0f0702010501081b0d06 75
    0x48408000400408540b21041100c400740180c000b00380000029008d1000d0b8501c907840109000141205401d01d070080743c001c001995503a980c0358042c032403c0d6403401ea900c0d000d4510341c0003500d0701d50306200100380c0e10140640003440d803d585038603204180121005072030006511b41c5950741c3d640d65410b1414040c4d013000c080d5501c81c400400d2441c482c1c0c908181e02d1422075000f44594a070303403227110301000002c2d001400d00f0b4800d060310030501d8035541001c1c410640300d0358120500d00d40701c004455555401b5a4405000d00a65000f50900d4002d641c907003900e0380405038801c00100d41d040618004034103010440d03100905120040302d00381c264104d108048100400c0641e010002003120004010340c88a41d0b85103002c0640c0e4030031007406254883c206100c810810405010207452164001c10002d60080790b90008188032441441088001c200c00290049024070003401554101481f29460f5201c2d220142c61350700140e401c81030241c4500102580180e040030f8204010b461a804058403240c5240 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 207750062 1250 207748812 207748841
    0x5030403081e0a020702060c0106031a011502061321020601090e0601030f0b04081e030a051501080f06030708060f0601020606030d090501030506060d0903111006060c0f08040e0703 79
    0x10300040c8054880001e880092189280803003103611210f078144025480f0f550305036042142000240c1d4030000c00d00400c40210312840700c00c1020055005400241c0d4810780016003a04255410703038140e6507000800941040840042c1e00c9401994600061141308101d5045480910320190b00b003007030740208407141200c3c200c1d041840460f06138440144c9841d8240401800c0782c3c00300d4818004629442c0b809a405071240b4079162801d1103562402000c403500200c1007150440010402c8010040b900641d030f04003200034445203001484a00280885500508410f60f90103e40001442a503082002100419405081d50202e085c10b00c5404843c400484119002d071281c000491854280081c500711005010750f41c200c00c203404c04004401512002e8011070b0b0110050100d111410413501c1481100c034841d495100c3d11070401000582444101028840440c1c134002007000480c2d0003a011398101c0e80e1046a1005d001c50f06c0c87c0202040c0619007024040301005005c015000e60150b0011050720280c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 207751312 1250 207750062 207750077
    0x509060405160b0331060b01020d030204180c020c04180501110415030e16230603100b07021f110c061c020702040b041509140906010303050c0a02090705030403 70
    0x240c1c03003412180c810303c103801c8100307030410014082004051940024103001103401c0c4041c501e001c00708a60788407001c81990303a941d8548046505680400108003d81003d040940c1407501e01803980c24031801d9610701341d09042e100d050381d0b03200340e10a0016890044004004121484601922650392581500100d520307618044810700d4203a1048159000c44140c0c4454031040340f41642c0c128007425062a0051031746c460260754080e07034014100144060f20743d04030501d1071801030a034101c482031100d542d5a4011142082400203100410160005485408840c207540c3c00051010507081811803191030030719042d281028504c940c1c003000c0c045208107000c4c00c6a034240d1020042060512801941c402c0794000c0d070800d1104012a600588000c5000400000f01080074401240996926115080e00c210421070181319514882c0f045010000144444807050315117900d00300d55542041c08082e007402000f044030704c1c3e08401000b107403c42e264007804908075410b241c00054065002130b1070440104130075 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 207752562 1250 207751312 207751333
    0x2030d032003090a1217010e070f180b0c0a06020c060402090a05070c021e191502010608121303060603050606090612151902120604150b071707060509060405 69
    0x3000142d0707005468000281c9600ca88a0343c0340d1005e1035140c0702190a1084241d00500b41c014101c03140e500030000422440000d152861004103054280d00415050000c050202c00c0c10b4041e0101c110141e07803000220582d81d5841c3c40241d0300d00703645410000c048500004031041605008075070140694130a40f2092841d4441581050595508882e02400102050844070140c582003481e428070954090310511f00108201c003040c4800031480e140c03020000082c50030446041124504a00310815200030031840d410051030503141c0035001c1c1c0c1c80c400e80b000450740724520003014501030003e43e404241003181e1a5a4034100d922040d085414a03c03501031500019a5420310b500030381c14800c0e10308054600a1400320f0300300901e1a004c1c1211080c1e062400c5155482143c62000344061070b40045a150340b8502038080000742c0b503001203143c06132104004200705100c007d00594000c641d20010500c600c10324080d03032207074074000c1c104041c100c541400706002401c4004a10140554011010341d18009176 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 207753812 1250 207752562 207752621
    0x1804020711040507232b090203070803090a030b0603010213030501061a07151d011d160b040605030c1608070c05060405030304030201081f06020d020f0105150f0d02030d03 75
    0xd94680c0041d0a00c02801c010310f000310320030010100943c0b81046e0082c0e01101c0707829039203603410141c010b480d540d50701e410580540c94100320f41d60041100764001c40c80c200e00e81011034440100e612004140000c01c8021804540d004e405031819201c41211640100741e490030a240600403138814200f03d46008003800880010081c102c818207a08404a0b44040d12540c41d50802482c25808104078a0b48641c192446c0245c00e000760b800c128941a500c020140a400030541004c45030dd007036140c000303210041040400103440940d4110b03a550304081351a82c0c2c4880d42d500d403d203d40c00310041605110600700c1c0802820002810020340540702d80070a0a071940103106243c4114010a649540148404c200562081034030300da0081d000141d600314102541100340c80228150440b01c09070f00b182e200c141c001075040009a40800b000d000030f10146c00d01d804500c40c49507003c004940030b00309403440c808454a803c096456400d502600701d400388d0b642814014028404001c00d6012420700000200310500b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 207755062 1250 207753812 207753827
    0x203120714120a0c02010e060c010623030a0311071a0c01180503040b070c03080d020a110303010e01120201050c0624010203121f0806040605040b010504050412051804020711040507 79
    0x1038182c0b011034070b00100c550066401c118898012810007066503004203890300c446c00649160300b480c800200702c2034206181e403102c0c06201f4500c4808030340d81c44480f800702d0f80c1c00580840700c00e07018101005c1c1b000514642030306003500740d00283d40e500046100180f02d03258000050404140c804000c00054014080c005003540070440081d10650040c401401850100d20051a105200d44110748409690baa01d82e1040d030003c98000c4000750380418551180c40e003141d8812107007069880a10725660408083c1c005c15001800b0f9442008078441c0366078216400740080326002c61001c0b044482c18506009550300091569a6101130541c0c41c481d00012540004151011304c0c1441d1584c8515585000380c500303440c03424151840d030340010204c00285618050002c2d41c02a4056940032586e41340508064900c1c0b003060f07100301e00440ca440c08002c041800405034242a18640c0341c0250b803030441d0f0b01c40d03550782c03950402107940c4940300140c01c0007000350700140e410b540074080d6820f12456071105d10944160 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 207756312 1250 207755062 207755083
    0xc2312030f040b010e1902030703150806040507050d050307031b0206030a0b01110109080301120c0f030807060b0a0321110d08011d06060f0705150f0a06140607030c0204090203120714 80
    0x11320340080010720746c0140c2d4019551000080c85c000422034100a42022070301002c1d802403c054118405100c2881010300101c805048280c032001a12585580d43c0750b41e1b4440c8060240410401c00a000c1074142e200f640c0c40350064004250702d44905080c0da0640042034200ca12034003144d403180480385055010f0003080489078000602030709603881c0c81c078041c22002916130226071140d009140070500c0c484204062010f580584011901c542192034060101c070041511075100c1d8001c0e000030800103075000c40c2494182100da104d4140c0c425208001e80d030000304103180005a00401031100822a80303c45241c2c120340c4081d000080304400c00300b20305178005007901d0309604031400b0000703511400c95540003131080340c0c4138104171030702402e1f0b050b50003410001c182c507142803265103e0240000390302c4600425003e802c007010302c050400ba100d0001491440ba0107001018081c1c1840d052040d583c859215a00355a0003074103944091131021401d00d90741c3d0280c01c04032107140040103168009e1000041d000f840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 207757562 1250 207756312 207756331
    0x8041206020a080f19110408030705030c07140f060702040f050108010e011107020a05060304080f192304050f0a080703060c0813030e09041b09060f060c2312030f040b010e 75
    0x419004c502e44050b01d5182c000f032504080030440048c81d800100000c0000b103010b0b20296440d000120407840c2480c1041d80180c485a20481a2a074130b40d03a28078a040c80c403c07045a140d81d030f0340c5107480801d000e0100008411800f61814000040390300064001c404585c52080080050001d6910b60b076000e40a104006904015003100901084c10144019a040b034002c0d2500c50804001000c0301025034840c0703d140c0c01584e003005424003021340203032241c2c3c1d11000c2c42e20140e100b400302c44120380080c05244035551281d20310444070380301e0381c40d148002800303003d1240903070741403544074203055010303000304000700d0001034000700081d4900e41c41001501d181e079410390b118900202c1e00c404005010750007800990300d1704c0d1020003400c0a407060201c51130040503044004911716140461941c0a0580c0703500c02001c1c4004101f00d00002140041e6181030703c1c0b180f019002c500803045000701c1c904410b401c003040340c4407000024800070701c401c4003000348110b1041c4000b40407030382c03211040161510140c45103800d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 207758812 1250 207757562 207757591
    0xb0c060f041a01030c0302130905060a0f020405190608060307060909050c09031c030c0509060322020a03060e01110f1903150f08060106050702130908041206020a080f 73
    0x180300c59400399140e04240151168458640c04040e0100d07056420b07841264421205142002142068149070946d028101c070704010701c50307440d142c203038641c81300401c9043c00700c2c0d68040e60007d60410b0390540740074290207042d80b403001c507400c3e1511500c0e900600841c0007142884002403224900080d440064944560b04d0400c110f01d001e5500d800b038103002d4110896501c041c002c07001f45032410401c00c2103045401c0b6445007107400d07030710018084481004032241000710400903901140c50b6a030880e0f03007100501e070700c40f5481140d042500f151000c003000c0003580300590580010900542d50401c280c0400d03440004c0000c0b2110b50003203d014400c024420149040621a20f0100481281140c1c409001ca06000c00e045806078250182c0f10381c2500a1030740c5500c1da01080c04a0381c010048130340503125908289190600540005140d07400b01c405000c00c485e00e0300b1003501001003880c150780c020110104007c60071301c00f62038403501039008400c03100c0020328240001244040f486450a005a540381000071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 207760062 1250 207758812 207758821
    0xf011b020d081003061811040c0903020f060c070f0f091505040b040b1f031b05040e0a0b030102030c0c0607020a03052a0a080702100807050307050d1803020601050103060b0c06 77
    0x2200c00000503c0303180c2e020304a000020114034203001d03940003464200c81c0b1101e00c0800d454403008981720151010300a903e0000f640141640014041054940460b1004c034448a440000741d601d100b4202c88410501514400003108003454000d1003d0300c2c041c80340038000c907842c0d02c50b08040700c6d21b04560034200d01c20581c08001d907040130f910180304002c3c050f0000c986a491000407800354020002c05560602010b0380c0b002809600d841100354848242e18603000c4007009003001400d40c0114001e4501e00d00c2c04c0400b08a04182580c4802342c0740d00d014000b5526032401e80c000100f01c8d080591901e45030700030380000580e0b00c0e1002c05e81e03860340c13645625510f003050001c6201503c20220305545006400c40e1030041c906908081201400b054072652145070380c2c180d40c0c03041c07065803100c9000610038003922200340b010f6940c000c1c06403503101d0020300d08640c82d0340083c803591010707007100c0c480c40b41d81454050000040c1a80030a6003810b0311400e0300c0a11240d503441002814a1180c28403220380c035003010300400e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 207761312 1250 207760062 207760067
    0x30c0306010c05010c180e06060406030209060c0604050c0a080f070314012007020f03071805040f1202060f100308070b0403021509032a03120c040906080f011b020d 72
    0x1103412040600d03100c05260300990380c8608403000400c0300c1010a00c01680d001c40c807050301c4d00d200083c00740500e042180d400c10300042480c60245008401c1410780200d1020290b40301c0d07009a03001c02d01e07000c00302d4180d03003003609040d070f100d644c480390313a0307010300c1400f4804200840c000440d50103025480e402400007524580b03c0c11030403951804018165520360801c40b40840120080002902a603110715a950700688100881c100b00d00b000c0074000d41066404126080280380340c4528159506004035082c0c0d11840c00085405044400503c40d6404401c0e05100c00d5001401c58403604c800005020103444952031840e0860f598800100032030000c000610029035140c0240d600710348280100c4191441c101203601c40314104a8a64210b50f0020038080b80329400501c160301e07150401e03408183e0305001200001d0f03c83c402c0c907410101c9030000c0d2000c00c40403006a002c03038000f012146001c00440b5200c0303098589413032200014100960901c2d011460803000c01240801d10f642c190000c00141d02d02140a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 207762562 1250 207761312 207761317
    0x105030618030f0f03150d0b0408160b010b131410110f0706020a110901050d020d05101107060e0f0a0b22060b091806130501110c01061a0f030c 63
    0x65072000e000c18089404880c5848004d000402060302c4099101d261420b4200108148200c0c00c0e40324404900d904004908031a200c1900a90014440d03030b0b80b45260b0f00c189503a01104440280019050000000c1c40ba001102810590440844003039070545c1c1d41c0c002c80d2460340900e400c0b907401004000b902013070f14058010700d0000a0031901755018013480c0d1210301e0405115031301038005031300b10414040030400750b14104a040e101c00c403480b80c1d1075418040031554091610800902072501865004103018040208185880200c8014003000c4035120b00e007215038001000c212007003410001a2060f00f40d002c1070000c90500c011004004482a98462401c4004042c1140583d0041011300200c0d07075040700300074440e01e4001e032404240c640429040c030101c030760010140e0841c00509071007004090400b00d092500000c80301394a00181d03081c0e050a900400b00405250441c82d00015056020f040640103a411035100552880c9030207011001e0b4011845004090350074003d00b000000c0290036044003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 207763812 1250 207762562 207762601
    0x20d0507060605040c050310060216050f180103060623060702040c0c0b01030b1015020c06090120010b01021e0d2001090605100605071a1e010b0c120301050306 70
    0x4040b9100d5910740101d41140c2540030310300006440001040341812a0341445001424280b000b0030300a07001c1044400703110b0442c01014403914261180010681d60781501607204030741c40c80280c1d60341d652481c3c044002c101074401e103a0440078054002810b010300c581c40e41202ca00242070b0600d800f4640e42000010240d080d212820310030b50208203c085144498918065486803403000c0050600d8410f001d641c10081c0e01000a00048030005042141c0c0400c03810141c0d281501c4080c3c5079000080161601c1c4811040b05d00300301d0401c03201d0701c11600150842c4211410a1b02590a10741d4020704410b010203e9209818442d4041d09040d544a40720fa40e03002d0210803d01c928441c800d01400103c0d013525014881501c1361910707074080c040041310b6900311200400349810000d103001000d5070b440b151005010b0070313044000d02c900006040681e40700301448012688038001809503843c0c0210880c50703005860100040c0c820802d403440210700a5088074140e45c1d008000b060319950300741e0306011141da8200d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 207765062 1250 207763812 207763823
    0xd080c03070804060c0302060f070f180b0d0b040b030127020f0607080928090203090309060f0301030b0105040204030b010509062b0b09060103122a030c0201110d020d0507 75
    0x3681c080b4881c44080c2014000568a41060000d00e0070000c0c940b21300030380070480c4880317001c0501542e180c0100c4005400c507854100f52100c0c45890300d5110140c48942d1003260051000100104061032681c000154603000300c508008582c01d24007410f08841e1403401c17021203c250031070541600c0c0c44815142450510060011a052105001142c100c2e04200402c94046002041307402c076510b041c1010a20b00f01e41d080b1103d500b4409502c00d4805901c44d44281c150442d070002c08546180018002c446a16601510a50399004401c074003c079103510905c0259002880000045110300d42402103a0850b44c03c01e5080085900b800100008000f01400306980a0030900441070b51a02801540d1000c0380480b005070000e00080c1030585030000e0040440c0510b4010100520000b021700d603010560122911301003081c180c005003040058081c4841d1424103040501041c01016885440e03000014800c4c9d0301c03140403460043e0415940c828603001e6402680240f050b00700094452000f910203076005c0c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 207766312 1250 207765062 207765067
    0x302060f0705030406050322031e090b0f03010303020601090209030a1202011404080426030d0c051225050a0207032415030b10270207050f0109030e010504050d080c03 73
    0x165a8540b40d6849548031710086100403040080d046a02c105000f1110415101c100c2c042d281550f0041130b03c0102c0301c0c01c01c841c00001c4030100c001881007110300b01510246203a9581d0b54006201d002c4250001d100c200e00602ca0200003140c00401802a100c500f10050018401000c3ca6528490000b10b0060804110341d640c400702e10300154031560140c02140a00074080d0b55500300100b940300d00912310502241c0360010045e10024240000490b64910482d11b80003805c1d107041d4004440340d00c1503503003c5590560101c1401a86400852025003140c03040c1089040310403030390420f0f142401040a0710002d40c000704020408512103030a080f800c80e00c001e50501003001401442811145180b21070503100310b1451061081003850341c2c6840c1c2000801e85803c000364908019115034440c0c500d800d0491004040701d100000e21142c042e0b0f200300340e10605071003043c040003101d00d0080c414140c05030300042c0d110b1850215540190b049406886000c3c0c100740288e484c1d5181d0715415802032018a601d44000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 207767562 1250 207766312 207766327
    0x15030507090c2106061202070201050306040b0301060506070b0702070609030305030f1f030b100501030501080a080d14130203070e0108100203130803010303021e010b010806120a061a1203040e010302060f 89
    0x20010180c3c0c2d0380d28288000a021400e2007002412002c402c90b049820600c100408400350380c202090b45d80c070480071540864508145008603015151300d910991304a003000c6260810082071054103031141a25501f118200d07036031948121400840343c8000340106c2c60400c08101050303100204990701a0840002c0c039404000c0c1c840000c0c43c00c8080c2d00648405403541c00740b0031030600c150f6440005040034a428071041d4103145010740c84840b06ca000420607140080ca80300d03110b07500d800484868080074403001891500310070503050182c00c44e10032442400342c504041201915a10290b050300c198200408200f080c45261500a62002e000d180c03036544c2403074103c400501c5030350046020b544a6400340c00340314035541c42d000380100820803410190b41400c551402d03a9902003403440d0301000840f04c5212903503440100e40d01b07000d400c00d8060103081c104200c42410f01e14240095110410540303050025481c02d400540c3c5a025a004040304c171281d00c4010401740c0781000240035189407502c07106182699 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 207768812 1250 207767562 207767597
    0x1120303090c1e030606140102151f0f0312030504050303160e03030307030209090903090d02130b0415061d030a020108071e020604110306100b0d0e010603050a0615030507090c 77
    0x4401048044103c109a410701c10050340b0b018100c01010803001815055402d100044d4032664412074240000c0818000103406a012081e10b00600c1e030080b80f40030160351a004804042400303404113403484029003003001c05182c803a102e62403280340c01501450454549000d0070b4903898000345031808210304028142803a07034040c802140580000c0e1401665030b002c100900426001c020603a000d01e13001880440034603201c10807224802541141c550030564917407410180104010316100741c100345030909905036081440d100b08140c4241c0d0301c511900031840ca9440003070031168540a49c0680010480b40015401030750b80c0c5070000318500700505442c41e4091485a0b254010310040c00680c4070105200c00c0c0702c0c01003c0400200c00a80c09041036280549124134207110038840d24500d6840098100381d4515103034088602c0051000c000d0125582c0c074100741750b481a00c1c5505030707015442c0c03c0003c560611620f07000320840350f215003d48169880c2280c048020f24249103400305000c4e0050852076080c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 207770062 1250 207768812 207768839
    0xb03060102071701020a03050c040305100b060408030a08070e2b030e03060702070f06050a0806120f0712060e01060e07121d24010605070f06060302030d170f01120303090c 75
    0xf019500068079403011440003010303150007400c12510300004000c10700100318041111203143c00e2000020072400381c40004208984035a41c0034005a000219100354010350040070b1500815041e665051941201d43c1000098207400450444503400d058180b41001d03184103003003464901a050400c1d09142c9a40800d040000c207e504c1c00041c1c00a00d01030000c0c80e507006d04000074044900e0054203140e280c140c09401c030040035149030322500c000032040c008003004025103086440300c6420750302450703038560010080c24510300c4122910750a01a1005031030344140300d058200c80785618400c9180c0c650303200c255048035030580c0a0b103a041c3c4a00349202c20b10030034220081c50500b84402840801c4029071030014007807021348082e1441e21040c0c01005004d51010503260519040140307a411000c907890004000e15140d84003e402d4040c2618100a0503007080003806204d0500c41c00f038901356561403029140362424000e46a032a80c00c113441c0d8020900c290b012001d190b20800d00b00e10085c2d100c0da290080070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 207771312 1250 207770062 207770099
    0x5040302010e06220608070507110103090f05100605130b150d090206030f07081302100e030102070507060e0a0608270a14061f150f2304170a0c0b0306010207 69
    0x1840044c1080166405500b540e03008141d0310b04603003402041d95540094010102e1400d04240c2c841d00d010050084e2245100002d40d801003c60b568500c285500700e028240c0b910900b4410200501000030780d140500809a0004008003405402003003214001000d4100170701e4890407650328010040141c0354100110b02400342c003121803003945031030034004100c401e008004500c0320800c0075841d00161282444004500d1550601c60707410000e25001ca8020300030604041c0084c407a1100c000355040d00a001345003010320565410340381c19120b000540f40303144150342d0840c2040d8490080708222116580c01c02d000404031054030840c4095840741040e0030403107610001075401100600c00c0b5041c6001d1001e100307031024446a09417030310302064100786602020350030b000d000350620115040c41c0700380100c0000c0003140e4031200300c601d4403085240140d0014050034001100742044003c020f13000241030141154000c4412200f241001d100310b202d41c101030b002c01d0640c440c0010100e004440e24501c001907 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 207772562 1250 207771312 207771367
    0x71b03020307060b041505040e0307050a060b010908120a0302070809031006050406171e03040e01140a0b0c0a0f06021e12070c1203180b04050109060e010501050105040302010e06 78
    0xa031952070030705004032080303d40050711882c07074000d0960302031001b440081304642d0102d400040080107072254500354401d0b0341d40204070380100d009034420400d0f90b50107000849401ea03180400f003034403135658583e25445c03911110030403c814000784d207199200750010420544200303080c81c01e28129401091508403084e82c2d0141545d00e943c814071031410a84215001801e0303241450400c0003148a100741c40318000104008070010410308400c1c04e8804104a900800001400a0b020f603901c00343e131407021140c820602e204400350900024482071030020b40b0b01c001e4800000d41240c82a5644d04216a41c506000300c0d00c0d80d409101c4410518007458030f10035220301e0121b00c682c7d90b00c4402c460403101c1d04001c0002040c004034040180c00303d64130780c0c000c40d0814004d04000480b000d01c1001c4807501c1c010f41c50010110740098042204200d03041d0413200001c0c1c0f092000744921051110202c0c240c880034040d10340040c0c402d01041000d03600c140810b040440001c1d144910f880100c0d648903070304800003a4107240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 207773812 1250 207772562 207772567
    0xa1509020f120a2702041506050c010c0c02090f0402040905010e03040303020c031209010c0c030b190c03111603140310030c0b041a1c0507020708011103010b0d05071b030203 76
    0x1801c081c4050580e5100a00e103104002c540482d01030104401029650700000d105050401340854640740c0c0a281c0c80c80044115071186550780100401a50120300091a69401c00b400b40c19124003c0d440428103941c02041901d80b40e6801e01c046041d007a0007031081e6406900c1d0720015000c210b0a2290311100200a00a9503070740382103080c042c3c42c010580044a00a610006a00716507141000550f000c4000c01d180c0300c2131003002400c02c01c4000b5116003000d01450050000d211038424581c003040c90082844405100101522400ba411501801d5440c02c0600040205a44891207100d04015240c800c0c1000d03550380c401d840a0419941046942c2c41610503c00810700601c0303400e0980000522025500914083c20258030a4601101072803000044801103058800400d1905030703041080d07080b02c0b00300700e80d1811003c0299100200e200b0718080e546030034001c2e4024115007003100c2c16070705c02030304852400c003d0b451243c00800d0014405e004001013030380c0300183d9141c007821030394100340a54025134 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 207775062 1250 207773812 207773827
    0x90d0b090f03041d060d06020c06060103051e01050103050601050408010518120c0a111f030b090703020406020a0b1305100606090501030501030f03030c020c180a0b06120a1509020f 79
    0x1841c0c9980c8450761011903206000410225801001810107000c800125540c41d40b07070040451000143c036040100361900126144e000084005025489007000341c3e42446075850b40c4280c034180c00c202d900c44400420040005100c954020f410044c3c00010601d00f69240a40d1092101d084507000e40d0003088040b07885202d03115800b000c02c0a80840382c0c121405915140c4030201c800e03503680740003c1c01800c602c00002c025009980f410000700500301c003101c0e80344504248140007402001b5074080703a071140038000702050b0354910a2098a080c0c40480d0020700c41450180c480880c034203401000c1192901401c007407040000d006002040e01650300704808101036040c2038010b0100d0b52a50420360405181030010000b180881c02c1003006607170113040c00603800c125414120b00b0608001403c94108081b00b81d0440000c80070f01c0d5041c07140390f01030010801d10980c0b07070030420380b4442e60b5095001c4a080601051000c540c66100d104010310a0b50144140d95840310080b0507a0005890400c1801c804902103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 207776312 1250 207775062 207775081
    0x110712060c0e090412020304150f230a050702131803020c0114040e0403020106080f0f0c04230a06030b25092603040f0e0702070f030b0402060c0102090d0b 68
    0xc9010301c01c03400d0261102800c03001040c0000b00040003c1c1030902d2000f00624828000c0c03084a000d404910062041c4d11030507440a0070603e4030180c1d000004080d00000c01030b4180000c58441c0e44040b640c450340c40c041d1a0704040fa0036802840003642e005813a1120081510194032a22102c84480c1d600b0b130729802c056040280c00e1111040d0064148000c0001000e02c03420401c040f90f00341c41001000103110b480300e0074100c0c01000e040e0030408152280303801e890185440082c074009001107080880d10540007550501040e01d800c144d052890710251564480f80341000c52841d030b40702c0b04040000400070750f20f0b103031480400f02c00e66100403003042e0340c00c4c01c0409c09482c4c800c0400107242c905280326880c1c40c0245042c2450407801c03003041c9610a50300c02d003282c0f00003882201e0050218090302080d19803207200b2412007401c1561000702601c2240d00001e1480c40840d01131707080301d80001001c5900e60b29a028820b4035440a2100111035608001020060b80d07000c800c0c001c16409410144c8091601c100107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 207777562 1250 207776312 207776321
    0x6200114010e0a0501081903050903150612030405030c01050c0a050d0512010b0a121a0d080a20030f18190302040606170a0b01050c07180c090e061011071206 69
    0x30f08185814900140045a0001121103d05801140042c032401043c00d0880e094011440c0e00ea40c18080c4130000040301d00311b000114020101200c44a00314a1a42801580e0740310728401d941e095044000d2035002980114081d08a941d42c01064600d00c0800e942c400b4100241c04100b240030480218180c10310921020206015040820026291088072607014200c029094185040c8644900c0b8801241300101c6501100c07420150403030700054007500c0c00311842c0d00301900ba40d00103101d01c4201081c01004118010407210484c000d14a001c450468206441d882642c007200420004002501e2a4035a03400d06444c240f02c0050818080c0d0952040200340e604d503034003120802c08101090068460420074840e08030340c07002030008051400c40b0041e80e20b03001d203a544204901500800064020030040501c0c45900190307402c0009407904001900c44c500c1901a46114800ba000058140d007405420110560358a00340307540c440c420400780070726001c1990446c40c41d11910301840c40401289015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 207778812 1250 207777562 207777571
    0xf0303070507060b0907020c0405041502070803060306060f130c0504052e020313300819050406120b031006090606020615090402150c07030309030506060103090c06200114010e 77
    0x101c4172400d06100000a41c0e03581c01c1300740e4030b11442d0343d60b0204003001802000c0f040c0c0745a01c0f590554851039030307043c9121550030032a02e95000703001d0500010418600b40c8000c0f40011001020758030a080c015407494010070010fa001c800b40f01003000003080a41d11441d041d8903001403d00030301014040e60f4030744500c42c08a00d2800007554400d0001e014248070389210201134410034109160788061203180791400000720f90304c4e40411038410f2400c80c2404800350043c0070075140714215990a91283d9000c490030712641c440c010000d01c0c2c5d000881424074042c0c11080748414002c2c22140910102c48688080764001d03070140e4411035039450100300d80d1343c042c415540c0c009a040742d10801c1c03207503903004618880001000244110265004406204001c0060307402d46052070701100c407607030348074980941078400d80e00050380c803441071000040300f40d8480c1c050f0150310b660040b80541100e103440c1094800401e0089104038a010002d0890002d11091103501c0e031404507081c00d292154500514440060409013 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 207780062 1250 207778812 207778819
    0xd14040221120901050708040e01171507080601022119020303060f062a1e030901172d180f0d0c030c08181203130312020f0303070507060b 61
    0x180548854038001c6240b4600c0c0c1c2d1821100c580e1091580012034281c0704041004041120201e0042154101404010705075816082c0700d0344101103141390a60b0f80e002072a20f96420700880d03000550410704c034203080c40d0082010300440b6130360f585100c0023001158002100000701100850030f01d160001012801d002400140050340c41d509102010405250040132030710f00844001070702803605240c120000a4096803019040002c60340c40e007000d078a42d2080e00030404180384040850780b800c0008812504643c0c8144c489044894a2900700348a0300001800d040e4040c0000c80c50506070456504041c05030400c0d002000a00c1c41d00b04200c0e001c2480c01d1445480540c45200802c003000400200e41e09503600c0c5082600e010b80d10b84c5421a8901c5c4146c400800c440c2c40810024800c0a1412402d0031502080303420b511400c83d04080c0070780d01d0003412030900440756040820800300340003120302e62001000b88191440d500210300b07a00d1a550065a1040008100242c00001d1043c90300c0341c216501e1044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 207781312 1250 207780062 207780109
    0x27050c2b0f0b101409070504120501020d0b09011206050702070504020d05010e011a0307050d060506211b0403150207051618060e010b03091c05040905090109050d140d140402 76
    0x30041138011801150030501583c04600401e03032290050084e0750060a05003440400d8110f1490841d02035000907560000d56810101c4020080c5490381c1c0b03107070582d0125015021608166159603014080103000d01055001c2c8900c0440e20381c035180000c000032034060300301064030352418880401d102c2c0142c1c081c030320350032a4400788600c001c201d00c22240c2240c0c1034a000394840f8169850030004110a601072035100000080c651840340d004446442c0c0504c910242d8001a0384d101264108101d4100b10f10000180800c001d00020b4292a5098482401c0360b500605101083d078901d8500018070005848d140c07400d6000300080c54034002c0a004000d103038841440050700c0e111080003040c0040c082c103110b01c10080009500300c0003c002031100200c0321100202c0b0b011703007810080c2a59000c1e0044030456070422000466150301401a4050264400300078149094456002ca888042800e410390001508000d40040e004582c000d502c0114040c1c400030400d03081c64410800d00c0707000e04c1c00d440545e00c40c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 207782562 1250 207781312 207781319
    0x7090207050c210706081e010303020c01050a0314010b0c1002071e0212100b03010b0303070c060e18072604020a03030e0d06050a27050c2b0f0b10 64
    0x200d4000303003001094072420070a403ca900e10440c00700f00b1032100c404038454090f0000700d0782d0b8030400c84d034022821021a14080c0d11100d070440300550b000d00018001d82e001e14003030410f5500c10001000e0a00e0346250000d0200d119036510b41c4990300a80c407141507100d0204401d5440e0800740100310044d000c0d01c104516041d05a030311510600c0c0a04004025440700051000542d120050700c1890401100c05490340d00d481001c85030020004092000d001c1d44c03070242d11183d82d04001080f6100950452203458001d440e01d40c0031194842e01041c0603030084000036501002c168a0100103014254986803100440910800c048645408015510420400d48140000350700c032541503a040c0c0e9058a81848454403c2c1c0100c0d205034520400104601d240030704000c2410301580c040b90316059052246400e000ea4244103138042040c03880d01030900e07007100c440c014852030308520015a0b000140e010745121290103e201d0f800030b42d5120700741c6103100c04106150400c258510340c0f9a1081d044007030080307038905 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 207783812 1250 207782562 207782573
    0x5090304060e06180d0c090b0316090216050d03050403030f060b0d110f070c0e0606040b041404060f0b070c09110d0b0a0e0717070503060d060c11010501061107090207 73
    0x2c802085000707400019900203d844007034413200c12908041c000c103e41412611308050302007018400c1042003450840850501d00d03020070070010209200445250180c1800c254000a50040003450000510388407500005402031003001040e14642c4c800003114030740303402c02805950b2400303091030800d85480c07410b210f4800120165103801c20031082c00180403140d404406420b00c034441103000c0100c8040b40a404101e1101c0a070b03000d88a800c96050780a403130741014080702e401940600041e00105100603c5029140002408a00d0004001042e450f81d02d040f2020310320142d800148020100041401c180110201c0304801010054400c101162000d001c26a042c010781d2100f411140e1640b900841d143e480c41c2c4a6030240000080c0f5090500f040300e0f008e041c00802300c0c0c442d8100d403485000244018055815030344a03d00140c0524070459065503500010030919440b60305201c0f0840c10004200300900ca6107001e0002e80c0c540346002d5142031096460400a540624000750040001800103803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 207785062 1250 207783812 207783827
    0x6031803030507032004170c01020303041e0209010b2802100b0d02130506190311060703020a050717010b030610090b060c01020c010f140f070518060301031101030509030406 76
    0x6030145030005003030702d4102c02103003c4c080602c0059000700090185000c82103074100108101c0c1e02d050f02482c031903a41d484643d46c9404001c11b885015030402d2001801042c2d0b05211007400c0481242010900b4901b980003030030465013a048060011004110350203075004808440c4100c00d1914030072804902c1401c002503440c0c81c406800302441d900d4100304551910f98581003880a41d00405800700d5910724070725000144000c4440c203114040c0440d603a43d40a0114220900b40c94100782050504110390082c04200d500c0110100c04500c02c1d00035030b0780031550600141002d0041400c9a0651502d144030490950340f940c003445100c0d0f003020080c85400500c3c1c000110403210a404041150701c00e100001d01c0701c1c000e000440d680c95000003a00c41100d50b06501c500c43e0035468580c100a0990b05a800086d118400c850f000c199051072030102d8183c6008401804001d1481d0110340b05048101000c103015405c04c0e4000c5444070030f1001211003961b018001d003507000c2014402542400e1030440000c0900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 207786312 1250 207785062 207785111
    0x150c0a031220090108010501050c0a110112050709030b090d12090302010e070602161a0d0b0a080d020307020a1e12050a061a030d02030c030901110a0f0b040501060603 73
    0x5459464499564000660a2220403039440b1806003030603014100342d010005260000d01e4004c00882c056002c1e40c01d96000400f10402041980740070360752940040703150b50003103052101f0042078007081718840c0035041c0300f0065542c0304041d040c514a021a83d0020141031a0040d07084151209402540503000f10042c0218a60104007040b05003000d0f40107240c0c0300b0b420b0440d4010750710040740d01170300040c80e0f07a84040d100108070303044e03036a03185480c46400294415800c2c0308010001d5400c80d0501c0d41110114110040840103601e03620750000345481c0d0318500c40805a013007c40e0300004d5107030a88501000b003040804800708644290141c0c84850424084d250b25080001905018030a04104108505138880c90401174400d141e0500c2c007058402a14a80c828400c02800721a407600c0171060340c8071a41d1010086061154000c0107403070400c0d8910b95403006225019240c0c5c04038080c14010070f1024001e0b1501203050815080031825201107811003010706003401d107110410750110742c0103540d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 207787562 1250 207786312 207786317
    0x51801030b04021c0624140d0c09080607030c080a09030306210308060d03080c2b0f0b010207050f120c040207140d0908061306020c1f0b010318111c030e150c0a03 71
    0x800d60f4400c075407548d01035101010380c81e44c0744c41d100c1840e181e00404814260f9410000b21412699010401c800396080391540c0b000142070407001c1441c000c280c0d0840719501d807082c1008500306e51150500200342e40740100c007814900411440b00c1c281900b02c0c92294205800390341690500e095610007525510340a40480f440f00310000d5518140b203501c10520650f5036800e4180d0f500d042050341c000f40684408040100034915140c90134010390300001c3c21600300c40000d004110407120035401c00c041c1c1240d210301d6803201d004454a00140e580c2c1c81c0700408200d885145d100141c0c10014800a20b40514115a0002c1c00280f5500b8002c3d4000000c007298040d9031802420b1804009103020006030140101100f11480f440601c0ca01c40c07508911460a03030040c401d8100302004c09400114280c0340c600ca9002032080500140402007614000480798080b0058107543c1c0d1030514800d8500307003161400c01a00040e46040d41d800c000d14080200c02504107000c0d00c2036044c402e0200c0c46540301c00107100300405 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 207788812 1250 207787562 207787577
    0x50705010e030a0b0114010f03020c070905070c08040902030f1f051e030a050c04050714030a0f060e1f15020316052103090705030607051801030b04021c0624 69
    0x1802d503410040342a8641d4000c2915400d540e41d03c0a1212280e580c0c0704082c0841d0b00041c001c400c6a01c00c0c800d0b58000381000008180c03180c80c2095035070080802504907c03c0105500c40c540c046890203000f000100181c1d00010303668a40320001c01d11400c4085c2041410112111592780d01e41c994a02500956404440c05510201d05c0e0500c0c8000b8031400d400c0e0390f058081c41d02c6480c00c1c00f8001c1030103400003c007910140200c6d0f0f294070f070032102d003000c0f0441071042010031b02c0410781c507140c00c1c2d000007003943c03c035100055400d03103d00003801442c05c11142c2c4020701d4056030700b002090f20280200c500a040028002010b2945000084c0d00d901440040c150740700e2031a066030051110400c2090405c132481c44001c102c001913401050401ea100f00c4010400e48100388000a640c140010142d210700b1032036031690b04100c0c04400880f040017a10410b42c0c10991604d005d8041036a43d4401000e80c0001005508500045c01006105a528075880005218016010141c001c0d003001920f104550840c0341c0b200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 207790062 1250 207788812 207788837
    0x306040b0601090e010909230a08090310110d0605010e0604060509040b090a020a031401030b01060804060209090a06090e0c1f23070b130c03060b130c1d01050705070501 74
    0x80f041800c95004c2e0000900c1c040c0002104000c1ea805280201d00078054606000680031008200c2030785881e10748a2640500b90180104600034003800031035100500340d076540300580c4840310517503550322004c0303403075400000e5403494000c0c46205400c0189000e081940e4840010000a82c0a000758802c44080c480b00180603442d0f5541c550190700a004014283c00700e0703041c044c0c0d404009400881d181d4002c07a180008500b00e219444c8006812030364020562545a070910f10f0850b1505400780c400c50382a602400308089a503600003016105034242c0340005810f0f4540f44071401030350340d001c3d000382c500d0f00b040d00010110381300d8003000f0900584081e0004078008030100c00301c0c0c2081c0c5034a80342100e658036840c2c06510b00722040040c6035003400340c0d03109000c070388031070700b0030402c08030b000400038140800401d0030000203056400082900d03034024100c85044d00c190701084140c0741d443d0502170010385141c41d8516100c8941c0c400c00e042000a1801d1030801d00e05945480c1c1d61541406024180b240481884 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 207791312 1250 207790062 207790067
    0x91005011409060613080709060e01081905030c0a030806011409010f030c09030203120d0c0f020d0e01031b08090601090204050303040302041802060d0b010801060302070506040b04021c080909060f0306040b0601 92
    0x840d0485158151808519a24084c094540b0000e008e5007862606080c00091490351450540d8140e54078080070f88880e0401058205240f510000211000d000501c90014812010b00c0380e070889038040d071603c0300c0070314145000604981e142138807040290b03000d0249080300d99101c2c4101c42400c085050005409a4001c000d8881002c2540025890700c250105008000040800b51039030a60340c035028400102140c81c283c1d1044601c10070600185c0c0001403107032205c1d1054070440c961365018100007070b008486604180d202c1c2000c1141c60045a030400600005980801010b401010b80f400c1c11400c090034500000d03220720032444060300c581d8550240264002c841b2104000d401d500030300c1d89650714103414a500252200d201d440b070104030041300004405000b80210707038101c1d500c5006007406543c0c1d81e480013140c0e20003030001da802c898042c20101c150800c2e803007114809401201440d4845c00107904220314030400420682c00761142680c180800d0f140043c4054005a10007540145a078820f07004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 207792562 1250 207791312 207791317
    0x30218010f02030c100207170705101104030f050303040507080c131d0106081b03060403080a0c0c02060a0e0a051906051c090c05100804240b040905060910050114090606 74
    0x13001c3c5809450383c180c030385034503550003801d02901c9546071401c1c0d204529462025400340000103401604490450350495007c1c0d800f007000f541d80c52112500381512038460501c090750400d411070340c030381c800402d002c203210040040c6001050610002e00d0f078400080d000c04e40241c4031892000000c0d4031518050902200c003003a40e03070100861070080000075501d0040641c0c0d800c81d102c0f690030039002644410600c1c100843c51500c215015129810305484542d0030800410351441c03e0700410002034086001641d8040090407040160756600da45543da0074100700701103007103521040c400c00046210308000410988031108550090402d1074990348c018000305070010011041c0b0520750303e8140b1680800c28103500321390945005944200351348643c600140e60031348083d5006044100d070112940c03c008000c141084058a01c060b01003134042c0300e035001c02c3c01da5205600440343c5401020070801504400c1058911000608409010329494000511040031615185c5805103400c04002202034840d0402c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 207793812 1250 207792562 207792577
    0x50f010905090c211b09041803080108071d060603060102070b121909030212130e01030501090203010b061314010c3207060806130b030d0201090201080601030218010f0203 75
    0x30002003860101428040c640c001c0d03413100000b01c0c1031501e03031540e0741e001500f15108000380c0d4082c0d001211400315060300303074000ca61510350094135540d03503aa11902c0c180e41e41c01e401d80b084e1102ca1003541071413001402c0400c00d13003100f242c010f0802c406012811942c940c0c10341010064880503940d8841c07000403030400b0455003080d4950fa100040b0280705601130141c16110f0a80e440140c04c40c05418001c203403ea0b030f0b4603000517005074006403420141c00c100344020107880302510041016a5500c040b1511481c40c00d0b4416541a59560860000d40c02c00703005034000b1100403070f00c1d07a20f0000d8030394500c1c00c90816402401d00800d590200c000031a401144030307a042c1d940156601c1d000843c0140c0d0030b00d540c0350080719480e00307510201080a900c2030005280b0140c440c5078644111a599040500c0132114000c2d059480840d168241904141c42c2841400c06041407a400401ea03d62a400050003444010700780b141094410082000246001e407001889042d003442c1c08001400741d20000c0386903018064 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 207795062 1250 207793812 207793819
    0xc050a080c0a0807030c020109050f1315090908040807090507050f16060203090604140303010b07080313020d051b060909040818060a18050301050103030801060810030b070302031e010b04050f010905 87
    0x82e007101403541041c6d40a010901c00d070f899044054a41c024040b00704042c1410b43c0d009002c030b1003510a44142900f10700008944c00c3d172054400c075650400ba0b03090301e40d00c023020759005100103001e000d410004d108102c0070f000640028819070514040003009846260601c505081c1c2c00720b000f00d080d51450310440c2c50140c00900a54603420002001515840251412030340ea120380c0c0c60014003640c010050b2412a10003c5074141895219200c0c02c0907a44014602c2820314111104040165a41c46030026924040c0000341008450010030080050000120703034403a140a02840b416940d0720030145500551040881c0d40343d42440350000ca0708008841140d502200c0803034149503181d0303c041c20a895550550308101c040303a0314000d250807110203000c0600000c25040040c400740380945480f40d00150282d81302038285540303480d440008182034408500003600082480105050264000c4503a900c1803e00728480d494413184a0091007644a0790340101035500c0404003581c0110321050003454041c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 207796312 1250 207795062 207795067
    0x12d020c07090509010b15030606070c030209100602101118030a0209010e0601030c1b0b0603030c0f0c1002011b200a0b0a0c0906020c0105070c08010e07080d0c050a080c0a08 76
    0x501d001c0010f00022540700b00158685024030302980303845080c1510750b5000303d01e420f2641c0c68903001d04c4800d5008400c103580e0324801030030000c0140c98010280c2d200b41c1c4901e80f0034600300d043c8080241032903400a41e40e00136038203160700a01388072414012900350300c0030fa8058a0030403107070782e000c00e0402c1c80c28200070391b0001e030700e1000064015501d040c0d144035080036030f01041050154441522240f07800d805500d150f0144911440c0081c1c45245941d4008200504981c141400064203038948007000010462176080140c0d4052141084d08415540408a0000f8032900c002d10743c56900c940c0003403461000700090524154910410034000d02d0003000041c040e6820400942450f4100340015140001168078000c50009085d00c60100c941c00c2d6441c690107001542d09620044645801c818016540114400e100195502c0e091240d10407101c4400c0140c201c083c68003040c942041c004803e100103100e0750310035041c001540401c0300e10506910000094031003242c014581c4c134000341904014040c4000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 207797562 1250 207796312 207796319
    0xd0c0e0d0305340c050a0f030b15011b0c08010c05120708070e030d170a0504021c05010b04020318100204081e030c030a0917070509040f1416050a08012d020c07 70
    0x40c0c1c44040d00399802640c086c0c4000380c0c3c03011540008080c9202c05402c4c04503d00c042203402c034250b04880c1e0708210526280045030817a58000e0100f081810003200c41c14420340040120031004c1c0100460401c0c141801c6080c2040780c1050b221404d0000c000d0720410130488001105140030b4402ca0b06410b00c050116500c6140303080014003841c07118101401841e0051000568803102402494850382c0d015003540200d40e43c40541c1c074582d10740a50308490035500d8121401d41a140d501c041d40c0701c1e0764880401c081504099403410700380903443c1000c600c1107004010901001c071001403428a600070001600d280000f01f200c0007400e6009160040a85000004000b40441d6010507002c1c1641d182c01c2c21500382c1086450a280d90302c40e24800c4903040188000050003003882134594904807402460100313414100d400d219030801d03c0564501a003141d540005122504100d1038110203091142d00800142c1c007688510030b2583c00b01c00c05031a070561a484c900b000743d905074064520756144601210480f94070b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 207798812 1250 207797562 207797573
    0x90b0f04080601090606020304211709091303022d120405131b030504030302091f020f0705030a080307090305010f0518031305040b0a0b0d0c0e0d030534 67
    0x34420050705118180011590014502c209030484100c1e40045242607c1c204c0c80841d0800c3c00c40c0e030b40404c04210620314003c40c40300c1c042d0710446d25040c0000d039511080d8608001104d1409401d5844030500c2c00c1031080001d800281400300304801c444001004c5046881c10301c0b8200640000070001c1c010907000362510751912001e44191002126040c0c0c103032482d41084803c0340c070309521401c08015041c840c004042e000b036101680042c001e240c0075181030f02d0000443d04030749403262646001c14260500a0001c0d9041c00340000300d0603203602810466203000002079485890b0080034006040010125171018081d511210080d940140203004030b0400f01d40310001000c0c00c440b1504410b130341d21282031200300c1c088119140349144801c2c2e50b0000382802c1c180001412004555504104886230108580a0710400f0305243e030200403010918500d0008020030f40385003140d455008040c42c2c50b500c400203402c0300689509120880e0520421401c0782307034080400c030b0040c03240304c01c81c0d121820301c009112 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 207800062 1250 207798812 207798817
    0xa231e060609011208030403030b1309050601030510060b030123090103060b03061b1206060d0212180a120525080705060106080601020304030201140705250504110a050a090b0f 77
    0x120340e012003d82e80c840b00718940004500f0014801101000020000b81c040d0344000c100b0781001d0021418400404151001c0f031351001c40c240c402d5802900104200001000242d14080e40d0f0360060200b6440d108058040340010b0064401c16020151030a81c0351420034010010500000c3c511103655950341004030007048003202c02800384c01074100090380422018800a060390048481b0b500e0050a00000c2110035000382000e40e00400c10007030041d10461500181c481d4002840300e00815040403001407940344a070341c2c02d02c1c5180c1c00030395100f8007060799040a01c90403211400c2056940680103020400030a07140002c1c1c0c2c0039880e29222600707218100c070140c01d081d44200100d0b00e0700c2e600c803c0d0684545004507400340c0164002c000501c0154400e503446954601402081030400c8480d50346c440c10120151854131100000303984801d100c801c03412885000307001c103450400403103403100b802c01d48900c1902502c0090110008000351060b100d010f0140040000151407621084410030404032503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 207801312 1250 207800062 207800071
    0x180b03032101060318110409050f0609011d07050d02090a09060c0e28140a0b0a0c030219020108011406120a05060a05010201180b0709080706020109060606020a231e06 73
    0x180c078100a041c070012058105c018026009030345202c03265240d40400c0084d2030801811901800341021103000c4102c10050940a04d0012002003011411301028500300103010741611415405604100300c0303a00c0d40041202c01036010f0702c2c01405540c4402d2042d01900d803014008040e02c0c508000c50301526231181003030825420868a05490300c600080f1901501a040800304001c2c240400c00c010a080c02c0c000401e40300d401402d0180c2c402c1d41c4034000d100d40e4004512a0010940d208501030815906200952100c032800d04242c1148100d500002c1c00003c0500a5611101044285900030f907560000c1c2c81941c071000045a45a1600f82841c1014080a0324424007910f54844081990343c0180141100c21694060012a5558546440c1181c41c4007400e19014008025400b248500007404140052300f881c0e0008034140341140390617401c13079910790b0010045400011400e0300003115202d039041501114203001010740c2c0140c01041c1401010f00e12540c050b00107241c20740e086080840c500341304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 207802562 1250 207801312 207801317
    0x12050f1e040e0c07050601090209121e0f06010e07050a0905030a150b04020c10020702120706020c03100e0c240a080f0603010c050a0804170f1b0106180b0303210106 72
    0x320f0312202c2c054021406104402045a00900300512040c545c43e0b0252458103001032560700c000203c4000c01e4100a1710101c1c1c18013a00440c0d940e404c00400400c400d10b0403124810080185616000200c101d030000600302c00c0410800207804c50600d842160120040c2c400201610003003445c52600740700f424181100010610304061484c4460314007882914400018075000d41288030310030003448000d6200e014101da20205100d2110203200040003140f014100540081c41400a038608061420a03ca0b03a03440d8218100201440503c03404a404d14070904151081441c10b0740c41c401c22030808040c807116140365480850703280e443d03660001000d80104e81d106e0700500551181c005250a071070011207400c000c178400b0080203001c98481c3ea0242d6000b4000c0c0f070304040d400340360b000907600c40e44184820740c81c500e4049046552a40001044166800c00314003c114080c41c004004909040d602d07a00103090f0317617404825401c1e8a06000321141c0c1404103d07009124154081c2010780c40c0c100b03003d030400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 207803812 1250 207802562 207802589
    0x2070f380a08040507332c0402070b040c17070303090b0309010603080c01060518040503041a090a03080a020d020f060a090503090a09020c0f0304050a05120a1209060e0d12050f1e04 79
    0x145401007e404068001d8203482070740784a000005011401024100150065406c01c8032001154880d44070500440c41400c01c114030b41d240111210401c0c0c6421607900b461380044000704002070300408168101e88c400322904e6220f80e034a40349913004041d590700180c21800c0000d08000f107040b040d4004c805640088401c8103240c5842c4000112200302100e0060071a80108001d00030689941002d0041103044c41307115140c8100341c40411282e140d26441194509804a0b4071007401760140125450300383e0620052403091b00964202d645c460300500290101c9580d6650b41052080c107004444a942010b000d24020070394801d610343c000e502c090325009144c02180c9105c1004031010040320101c50300105418040c038105030410200d003e00c10344145603803242510030000601c03480400c021440c1c0c180c5850348160714010020340340740200340c0c6040c0f10b01643c004100010300c0c08a86205401c0b1240740c82600e1b2800c40030707200b600b0b100e07100d0f40640850300c50f881e10440c0c848090007001504c202d01010319 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 207805062 1250 207803812 207803909
    0x40f39021204050121020406230903070603050a0207020301090c090e120d180b19060b0a140a03090b090a170c03120702070f380a08040507 61
    0xe80710300d81150240e07100320303081000304810340c0305600710300801900a990b01d6141203268000405c1307a01c95800755001c1003402611102c041c181c00143c0c0c0c19004103c100c10b02d0b0002002c00a0b0300e52055010b180180b40d61407000c23034a1172000c0e5068502e4140d01030000c0007001c101e0704004050b4945c07446240311650400400c5165080301088210080c403501041608010381480000b0240150054882c414010b401c410400326510074900e81c05030003040c2c06c650078a402103c0341d200361140d6800c01619a0410016981840e500c0702108088d00603290016031201480801140500700015010709030162190a000c82c108010074045243c521507806040380c0c04a076040c55400e800303007103021039103504140b11342d440c12507507844856808140362041c0c1303c5880d214008c0055590054211ba0090940700310b54064001c04080c0488480c42400c214128003416100c03020300303a00c28018100d0800a003100801d00f040010840c060251290303840e0b035014084002a40912008152080e02020201da0a0381c1d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 207806312 1250 207805062 207805067
    0xf030405210d0c020d1e11040b0a0b0906040b0f0d050a0501030c05060c01110301090905071208040510050d09030e03160303020319020a060608070e010f080309040f39 73
    0x5064500300403015140c600c968101c00d0750508a8030b5001d81c5c0102e4000001000614890450000702d220040404140000e0b8100040c40081e402c101c10300861802441c10b000e0381d05c0c0070f8550111007005028540d01e58012000c190035000b66800b095122501081000128050101410410712364840c1007016503038104404040e03490038030000d0100561307820148035504000d40201041d40340c400c0045814462041c13000300d07903802641b0444c00c4581e907020280c2003010520841004140b10b0110502c407008503215401648101d20415106000c200c03640c1c2002400385050b1800d1051105080000203003d00707019010504003d11148a8092003841401d92140c0e0b6941d101505e82590041d81004000d0703140481d1090f0b600c24602c15841400070b4040003401901904014003a8440500000ca290040c01c080703805040e00020070b030b448100e10a10080303400005842c2180c6003202c0200d00ca289100400c00240310400d003020380c09046002c609200d40081280d650342c1401e0a1003101c0003144031004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 207807562 1250 207806312 207806359
    0x180709022b05010311061b0a291501050901110d2d080601030f0b0a03050a030e1e01030b0d0f0507030b06010e01121512050d0305010b0702010c0b180f030405 69
    0xa007098140c0305c041c400d6081450140c000ca5240b48040c40c410203005400302c2c60403031612411984020340c492201214103142001e01c1a01280600402c05800d042d00c1085110070340d4101c05040000110b6514284da1042d0b43d151507210301c00302078883c00d41000b40000c0031240201310480100010000e108075801d030b620f0000d804102140e40d03001c2c0c50b485820045000c0d0450100200c00241c4407941c4d175080d5a1444c020750000c0d80b04100802818032240340290881c5902d14503644691031603d520310081c2468081018070b1902441d0029140c000c01d0300043c80303407000101c040e24040d1014000000c02c00b000031000d003928010713858045647da981c4011510403824001140c0001c58403548440801c1594005514a400214590005544507902c0604802c00c03441d0035a025413250004030308143d00751040c00d0141c0302c0300d4003192500c1c2031500060031034400c03250000d01081071140042e10440440000044030b800020503502c0307080440410030b50701c0d041b50249510030305c40d00c4520488054003291 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 207808812 1250 207807562 207807569
    0xf0a050105030f06060904230907080303042603070302071103030f070204050405010605030d0903030f0804021e01020705030d020109030201060e0f180c06132606180709022b0501 78
    0x1200380c0b441c0e0300d00084035a184030180802d0341280d402c0c48002902c0c0c0d50790203900810b001e088141140c40d0100315558a500b00061300142e07540c0c0142c5001d010142000c004c0361b500c15005001003c1d11041c0c4d031441d41e422030030b160001801400100501c402a54180c0082c10801c0c010006894586903080c20107441e0301c03901e80c4807008401c040041c1c2005050036003002d50f216002e4400000d029584402003401c00700702d41d10f2038000904950041c010990020204036a00d02c51b840d2060261a203a03011902c900828410104070445031a8800e1903a0720820100000d0074028050369a14103203e070000c0d0207010a1003045025500741440402c21000140c94244101c60841c0240c9680c5c0702d03c58011a500000408184680a402d2060b0002d44880e401800c543e203052109510282c03412055078084801c4000c1c030700080f40000c0407031a0380e02d00043c4042d004420840c50100c0d030703041c40b4140c1b0300e4941c0e5a404113100c1800481c204043c5548400a0602c51499510b03007032047d075194003448122a002d02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 207810062 1250 207808812 207808817
    0x1e0519080105070e0325030f06240b030406020903010b03070806190b0d0201050717030f060901080a0b07110a02130209030118051506040204170604060e1b060703020109120801050f0a0501 82
    0x20300c00811b20140c134001c0381031295002240f15a140d22070b25903000f6600018019284a501c03440302542008403180317182c25400c0c1052031441c503513080401840441c800a4000307464541c001c00e41f08c4869400b9403041c00006401801ca5549643c2c618900d40c680c4400c45040ba0706014218860304005c19900030544a0000140288501200e940c0150707490713000740c50281c0381142050000c3c0000940c68000b54014504c00d011821a860b01004000301800c05812800321900417140490001da65074041c590031113100c0c24108039402e4000003807840c188000001950002000d107003520350141c168000e00c4030200a030028408800c0d004030008a000c080c0724010501d51080024a82c0c103e030b035130325203500810028005403515503030f001146100490341440411a0f00301c0c6042c030080040ca44109103510420501800b0149000018043c481403a0a8114020f5100140c85000c1510030b501150901d0b80c09040542c801040102c020320716402406001c1c040c20102d0641200746c908040002c0403a003050307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 207811312 1250 207810062 207810073
    0x10e0109030206070602120109061a0406050d0c03020c031b1507020703080c011d010c2304050108130c03050a03020f010213151e020322030201091e0519080105070e03 73
    0x60b4203102140d4410542070ba18036500744106d0074410544419507000b02000d00d00898858249006c80d1404003040c482d000e00918104010041031b84c01005941942c480c036800000c1040b020681600603129101d068007241c0000100d00c09a00e08060600d80041000821240401001443c0228040c01500d0f402c015a0040008000007020b10004160980b2124008505030b10105100406850b4569103c2400d94403a0700c1ea0fa4602d500c070450a080c002003c080f038025800da01c0c0c0d0300d4103600c50b42c0105810130819000241810244110307004240740d22a15041840e5038070308185440f501c2c1d85004074014010002c0031491984140291140750241e8800011240c1c945010a2042040400c40348140040182c1c1c2030200e01001200c51982e6105401940c1e5841701c0020303400140e03060700442142100809418009030b40d00901000c00c2d14201c49070304842100b600c1521008015071341c03140358800c209115080303030311101c80140004c0758000d200a0042da198603100f035074280c104100c0e258166015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 207812562 1250 207811312 207811319
    0x5090a1e0b330403120305091f0c180b120f0c0307030b011205010b0301060201060f0815060105040b03040303021803030c060601050901030e160302032107110f060a021b010e0109 78
    0x100c541008582c4590000600c1c1d10100401c200d40da00281d0050316080b5083c101d880000341c1501a03a640801c64030b024000e00881040b51320400700600400d45e5010381d84038013840300310b402060a503d09100c0840f8016065a452881e12115401803c034581d0007040c60003c50b10f0350407164242400b0700d194105c654219036814100318024420768401034100701d0841401d89103040e807071080c2e0340030708100007007035a6941c144000a4252a050380c044542d00304044820080d0500118000300d10003414110040306464880040360140590b401070340c0e81c00c8001052200701501940203011000702085903203540340a040c10181c41e030280310300184046e0401c2d400079040f58410001048100814100041c6801a1000003840d0600c000c104800c08055802c0070f100b07500d001c0046c00300c0d2a04100a40700c1c40403185110184500130709500600d14048100e03100c4080d9100c001c4007801e854044d103260340360b0051810003907032481c4c00032640030011084008004594400c070450009a003040c3c590400c090328 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 207813812 1250 207812562 207812599
    0x141806070804180506040b100504090b15130302100c0b0a0c020f01020c060f06040204030309062607020d03050114010f05090f18040c0e0f01091505090a1e0b 69
    0x10409080703440c00030411010031441a504044019001c01400000e01440d01d0030500c41145c180000701d6105807248110400720640c003404440a4491000303000c9110440d410200d02040c0740d41d011640071140200320002040c42c44061042101c0c002c46166801060030b410036182e0510000e00605020a0a00002e281c103965801c5420302400f20701c1115401c5000c141c119007217800070301805415070055030070322044050003401d05411980c01c07602146014a95640900348128030320840003400f01440004480d041c011605d95180e103100c0aa0f14001d1030104002504c40e01c00c01044d0b00401e14180001c00c644440031403101144906841301600d16840c100d0540740ba81048011071340c00700211510748410340301c0039000003a1214818140c0d04a05043c45d11038218001500711101425100d000c02400c0342d51a4600ca044608141c0000794203401911440e40204154005a07008541a01406007640c044d80c46050941c2c0c62251014111500b00142c000b503c0c070341d4040c42da002d400b999010107a000f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 207815062 1250 207813812 207813817
    0x30d1a011416080301230f09070f020a0b0a06050301051308041404060b0a0504030b07050306210a170a120612020103110705010f02130501110a062408070501141806 72
    0x34452a000482e0825603a56465540c0260080b4040042588401801400400c07440450712421030368003034601184401f01e225520010b02e010200402d481d9080901c900030311500a0040e040b00f81e00c502858681501c0000c2c0c81540b1582c0d0003907103000009400d1803400b00d544007a055014050b50700c0c040c94141c100041c2417001c0c1849a00907680c84ac00038100088100078035200101d9261251100d1540c103011240a40040c8040103200341041000419a0b55106e071114083c01c03039281c860012104402d0038540083e010004000e124a5502c0c54984410000076103007541c3c0541c0d940321480c082c1e52444003507a50b00d210b03042101b842c800b5000c2c015802034000104804403406030314100710040d2103440c291099421040e284c40c2d070004a0f51030203403018400703c0c09000c1c01e0078400c41c0030514011482d40c9412103080a401d55554003014484070000c00401c0f0003030594001ca41c2005034035510201d071100700a1103051b01148419600600c00c004040580b40301030070f00700d0200d8202d03c450040c8266070707 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 207816312 1250 207815062 207815077
    0x90e1315020405030304080f161404050a02070602180f030a11060705030f1201180203070519020715050310080606031e07030f0f060c020712110f030601030302030d1a0114 75
    0x15002c0c0008561618200301420050002a0042c69814a0380360080d05003010342900e0a610340403194140000c80120500c0c40c0c4180d001e5030300092507651002d10200034000c118009045030300000f00301200c10900480110400b00c211013915100d00f0500800d0394609800900a110136010035648035549090300103031400314051f50030b403480c0c0403001e006542c09901450340706080030540030041c000c6603500d600d41048200c25890451a60500c420302400d64055110183c1c09503811204026a8070720074001d2030010200454803c00e043d08400c00603010360030480e00703100d0a450384000054030311400034010f030080d800900500030300b45a4540b01c1c506400102d0f000b4082c0c0c401c200f80000012000b0981e030040d00d0241034001084201e034500041902da48074040c4085502c024000e1004038414201d603044d5503485001d4181c07044810020500c81c50224103902d6041c003d250002090580200081c801d04c00c41d01020021012800d2403081006400050680011081c50750b000507142d6601c02015034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 207817562 1250 207816312 207816353
    0x5010815030105040305030a0c0504050112020306040f0218090a0c14030903070c090c0e010906051c0e07090b19080d0311090409030e0a0803030f0609071419090e13 72
    0x1500c40303200400c0c2519015541100018400001c01c02001c03618810f1000209591800501e004d2401c00028003450043c0d8151484a50000200f88513503107a42c00000141403080d0305546030310202d4103400c082c0049100305030141c0c50300f000107002c02400388210a000c130f0302511113064500a881001c881c82e0002840b880440c84100700d01d002040c03019038150300a1229440200d01c1801c801c000a1003001050301c91030520050a005012590b0008280c54203c202c0c940c4510510b40303110400c1c070141034515403000c0307a030064030000f0400350580d40000f4030101050b9800320003c01d0300300b07400c0364400d141e00c100c01c010f8110340c1900d034185200782c01c000354180d10000c4160a269004000a003100c1c005002180410840341c0c0a51003824100600d40090a13000c014504500e003d0b2102d4800200040615128208040000702c1c0c072409101d414000c1941c000841e9110000c0004d9800c2c0003000507071a90108c2e01d0b40c04009107000708038640394810041c44250080e824100c1c0e80e05009056001c2c0310010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 207818812 1250 207817562 207817591
    0xd03050603120d06050f06030720011401030506060a0b0a0e131b1106070f0e0d2603100e190902031f0504060f02040f12080d0e010b03060105040510050108 68
    0x41a1240c0026001d8640880400541c2c5072405c000c1110b0124851001070080340140104881c0340e4000c0c2c8034403005030104407200500001c2090031801042210000faa644046800200511a00190142c4030310030036181e80344110b440d20310a00e02030050281c01000180e44151030361a03400c20b4074a00040c1c032142000032903001580002e4a148035500c104503130004040580c0f051403d101040415000402c60500a0200003c00d9006084000f4034510b6406000101c44610401612614060300c8143c80b0050001d5203000140ea8102d5038410394100d040c9845038807000c01e030314040b643c08500030184000003400030b00c1c121460310090700f503500043e1b03854020705101481d021030004100d07040300543c0200140307500e00340c41c00784125512080ca100340140f040c0014041ca030300d9031141c4019034160100e101c1c0420380300d20f8150410b10a424a03c07005038200410303c10311440c1504039034206a011015162281e880c1d60074001150000c4a03400c3c401e03284030b501001154080d4440541045e1008080c50 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 207820062 1250 207818812 207818833
    0x70b0d0618140f0618100b0a020d0906020d1b050114130203010608060c2205131a010c1707020a03051e190c140d02030d020f0c01110d03050603 63
    0x507410004103040c0700315a0b4a401510284007040c46959900c841d00207000751050424034040b80003500400e8091082c0250f11000c00c0c0111004550b0340c000300039003218181d81d0b40e008113009494840412104010446030400480c00c2c80c004604c1c031600c00c100b41e8818481d120351590148640c5075018050780c10b03540c0c9811070410040002d2100b0310410802103241d84403505481031600f140d001b0b50012405400100c240718115140804a401c030000403a000f10b5502c0300140800428005540281c1e403280d1034804d41c0121350b2040d0466040070504141014011000000544100b03980100003008002d0180d01e04981001d4200a040302e240094460f5416607142d40d1200d00e4200b50100c1d1091112070701c0082c2088103410400448482d007800b0b61111a00080d94844c0300100c118050048080088100171480c0c1e2039092145600e01c3d001011901041e02c11800a52192004111074005000b00440e14550394090645a002c0740007502c02400800c2c17209a01710000c00d406000c0c0d0754140540350150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 207821312 1250 207820062 207820079
    0xf070e121203060a080a080f03040c0905190c02061317070b0f0108160602100203280c0e10050702090606090901091b1407020d0507050a0b13090b03070b0d06 69
    0x140e00740c007085555241401000c0001d4011140c1c001480d41d40080e02010000340074806640d200051144107944984680c80e21040d0813000e41c11074a22030f40342c5010031503403081e5045040c0420b00640c04c1003000d0314113603a04130303101d00040b9602c4005040003211800052071300e80c0194003600c0404060781c00c3c1074490391170150a0070142c549280d42d5400d20700620151070705100030750003044164200300180d40b030804040d4440041149d21040f003580030000540b02e41c54002c0c00402841030354001c10744e90502e510b00200900c440602c41d00040c8040810828a0500720a5400c1c4000c803611000d08003481d80d400c222a241c0b004106d150080424801d0311382c1c42e1950380c00c480c003030202d2000200e03454403031081c03200e1601550100081004080e00710700314080d4680d421960700c150166100c120500c0070341032203441d18083d58441c07a080040b0300d1000606400a2015149140d25200d01400140c4d60725101e0007510304034808141e00da00b00210400600014400601c590001070070003007031946e41e90389034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 207822562 1250 207821312 207821323
    0x100c0303020f0c0c0406080109020a090203040c030f0615080105010f0b130806040c060e030c130507020a051606030e0a020102121305180702012301060c0305070803070f11060f070e12 80
    0x1c0c000307644001d14403105885c01d07001d00070181c94944003c11108015400060041c41c9a02c00d460507a42d000022809010903119000040c0d500541c0f03507220a80d041c54a0b41c003c00c54980e004040c103040010100b40aa810701904e412205101403040d156818800e02031a00e5002a124000007d04003100165620080c003400d44140c0c040c032216407071103160000240502e03034145a21442500020300407001551000c0c018000f103031400300005510f41d45d1400983c40c11008100281051094810007000208210604002c0e18480c1d50f00384441c04c1143c00d0f8640c1c6a81099000740903030030a2003518004449003001c0d02072040001a00e10010380e032480420075030001d200c0c3d200070304015542000020740c1c090066252035031070358402c0304124942c1c1040300b88000060141c0f80402c4079111444041c10720480595030083d400009050340c0703040c22680a40041541a0301c0b1000c1202c1c207801c0e800982e008030324603114010800c0100f42d01d03139272000100d83c148001c4014541c4404480e00c0d084001070204507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 207823812 1250 207822562 207822577
    0x60f0f0a0b13080303010602031605150f0a0e03030c09101407030201050a0c020303040510240f08010b09040b06010813050616090510021218090a020a030b04020702100c0303020f 78
    0x100e07595407050502044076076085500490700c0381d0f1007040100003907039000040324024041141c00301c884250034540b850822900c241003038030401c4543c05001107061041c0c3d006005000c03c2408014072840284919100d00089a03029170140b41800704501ca410044180348082c5164a44024100203a580524054000c0201680140c1d0345004102008025101e140d064050790f000842c214179055030349907500c64100958200040e10b500d501280040d1040c0d41e91040f0040401c29206e5546032070b5040c0e1071891a100390a4a582004048016410403803c0903000c0d40c1c003c0048040b070364a890040d1402107000e04010010f040c00d042550108400348019800780ca040e440005900c0c0550310000e00200715600b1551050220a22403210507800040302a016841207030480d443e10040052442c008074400c840c1900a04110108201183c00c0d5008004114981c2c90420080b401c14003804100c1c000d22000941100d030010903030103c14000e0418800707035842450007618180c00c80815a90b140c10212 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 207825062 1250 207823812 207823829
    0x50904060e060f190b090a0f1107140c0631090c200304060237050a0c06090302060702010503090f1006170f0705130b04021606050a0c020303060f0f0a 66
    0x81c2401051074110002002e0300c541c01105100e020901740010b100545e026141c0800c032039650f485250034698039044400d12000c80c0303640b01c2d11500b0300c0c01c0014085030445102c03082c1f030050703940e40c040500c0d101d0240c40840c8600e072107010b4010130740c80401081648208004145403807000000400d04118020b1040c3c40c4020740e2910303224180b03c0300100300040c0008040c141c41c0c1050009100301680080c2c0003240b130826000c6902801124000a80401c00303202d200840708500400304424007800090b030074880ca01c02d1840090a0744d0708c04007100d1920003400300030341c880b8042052002540c440d03c040c60f0420742c983d069402e84001101200d00d03042c44807000586030b40e01c0c3c01040001108075100d41120440707a80c0580413500000c88456112502d41c02001e00c1403460319103c0407440c0035680b0028800d6400350003159116119807840c07059910f00310080b41c10a00b17040c001071400c50f50380200605855079400031411600d0315030400c29200310701e00c179031604403400c9450701855544401c0391400800114 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 207826312 1250 207825062 207825091
    0xa3c150f061e0510030c11030a030207140c0d060b06090910140612011a0f0724020a090b0d0e07030c0305010c110a080d06091e0c0c030801050904060e06 67
    0x103007080b5608940021010814078911010042525a180d44400c000c01382d26001890306110a0280d038090500c1c19214002c0c407010842030b00d0182c059000b000982e000b81c0205030b0b12941e6032465981c0700d00718001d20350402c001c1181c1c200014080c0d0800b110100c8018071550030300c9440804941d4880c0102c1d448440701d5600c0008106101030b0001e1030000d01e20558000e881c000341403509005080040c070420b911042ca40000e0394404d40e00000391030007410149001d5644503000c1c180820004108040c1510342c900d40140c180e8603580600c2200c501c01002d44031400203501d0418034140c9a0001290303000d03141d440f070b42011018001030160030080c505c2155a400e0050460a1043c03c641c0c0c40c1040e8420b11801da1a2494002c40014032842441c0c0c0c460840c564901707143c0701080c041d200544c01404598104169079807000101d0062010040c1d10b01410400c2c0d4607600d9007240c4400e0915405004a02c101e0300501c120f040819120340d22501070134000c100b1410490040389400d500311403010118010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 207827562 1250 207826312 207826319
    0xf14010e15060d03320a121b0f080a0e010e01050a060b09060d0209060f030406200f04090e071a1206060a080a02070303090605090a3c150f06 62
    0x340080e6801c01c20030b81c2d40c3c601043c02580e000e041c40d000300780c0f5041264140d0008070400d64004d40b2600064030034070b145507260740c01e101025214403080e8400005560401c1418650300030710080104036000241d640019000c81d4800903a5202400380c054541c807504c60708a4601d0701424000c0440740c0010000014140c0360a1101900700e80254000425015040050119941d2903c007903904210646c4401a41c4450718000100148a64020504008008030421080c451a230b40281c14030210941c009920603405006089148188004190302c018180404d118000284e482020314140c54005c40e004141c94401941501200031402e080c41840020140491810011100c1e00050f0503201242000030240c40505201d00c010060075106502040b401d05051094100c4014190042c20801c02400c003180c10589440c1302d0310050301e801d014041c245401d007860f80784444003040c018032041a00c0641d00c3c001084800708841c2a00c0c485004d904803042041d661281140102c2200f2000814525 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 207828812 1250 207827562 207827593
    0x40201090e090a03020c030307032c0409080705060a090b070f020a020a0b03060a060212070b0c2206030c051201050f06190e04060501030b03060c0f040902030c0a020601080a050304030f14010e 84
    0x8041d180711f00907002800468006904590300f00b00c00e1400300c016518540100d880d203a02c24500c00741c01c40c0d1203400c243c4041c05104101d80102103a0f4000e0701510156034030008454140c03102d0b00c60092a4030090300005070054800e100c200d695108510640300104820b40000d1843d00c036581082e125490004217001d003c0c175050070780c00d00a2449002504202980b02d02c5009940280074000c3c052641034400240c0c012892811540d014010b00034212400560700722200030003503075026500110f89015007549600d4094016110404c01c40c6448690a80c2003005005145c2074101c0c199400ca8014040c6210031103200800302c40300e001c1962000003901c0e01b4810031041da919079204505051500070400283c1e10701050055000c3d1810701c100380c0e20158015a100640f240364032070b080961004c0107011070488128010414094141e084030380076622165803c0d05c1c1c019054001344283d2040004000089428900c201c0d4640121400300c02d11100654590a490403040401c150b0780002940c2c604006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 207830062 1250 207828812 207828823
    0x1d0609031c08071404031209080115090f1104050d0512030901151d061e1e0a0f06020d030b04020702090114010306080c150708190c0605090309010e010305040201090e090a0302 77
    0x2d461603c10003010803814418900e1096006c00fa003a08842080b035101e450007888083c00824400d0000c004600740031440034a548424062070503064200b00d4441d45940c03e50289880c0403901c161801d240c14945810000075519824040700c1d24000e00b103d4194060301e8001451003803503010700114403116000a901c0388040ca6400801031000040d43d50322030000c80c10400c1c0d900a900b03454001035582c0d800002c80200d018000480c0e40400360301c1151043d00d02e441403403a8651015500400050b8440803007108028041c041c80300168814020b110042d40319401502c10220060801403800807540c001c111000b4003600300c0018401019909066964544124002420024007618000d40c41d6000145480c441d80030a024605012039a02c060101034402c071a0b1050b10310034520b14000d101c1380b000d081c80f17600300000d0312103520700030019840d240080202c44c8107020580d074a11850f0003583c0190020000600142c1c1001038105000c501200800c10613400b48100c0c034001c15140314035103402480e01c07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 207831312 1250 207830062 207830071
    0x50309120c071404110d0b1305072705010f1413170f06150f030f011404021906050706110c0706020330011205100603080d050114011d0609031c08 64
    0x4078982510403000d1780d0b40300183c41c6040960312011818044880c0022280400452001a40c92401040c0500f19403c60103007014183c04100000d04042c3c1610190180c0d20340c0c1c41a640803814a05415440038030442c400040d81d24219010340c1041e64885140305015481d800886401c07400742280902034034101b12942c180154500201020701d8190b038004089800d1581c09401036620807242d0480343e40a01810046040c240002c0000c0355103401c080007a003000743c4003640103003032880608020080304030361f40040d690320b9112103180181507981c05008040c00540200503040c1488144490380044c071207035000381a076038019502c51200c00c044403000041d091200184030700302c032070040800e05983c0d140c0781120f500240040c1c1d45416400c12904088603480c4055900e0718041d07000c0304000001c00500361341003464008000c81d07a2110013000c200149a580140405d01c0820242e400010250200040200141c500d6081070410004a0b160120310b5080440307441d0504107403c045544440041d500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 207832562 1250 207831312 207831319
    0x30f070c030b0a1505040e01021605010b090108070f0513090803090109030323012d06080106030606090b030a0b06131413050708070c060b090c1306021c050309120c0714 74
    0x5405130007003000b0000482d2194502568681c00b010749011000e43c1540c0c42c1c1c03644507060f1040c0039071918180d4002c101c0303002c41502c02c4605000118000c040022501d056075114021208414100030404c20462a90354109108948600e02d1000013103a4101542c010b1030300800210300411145006010340baa85a0120b8012044640c6281d0311070110104a04640e2810502c19030190201c00c5c81584c40805542c1d20150700300c0035000100c8aa124002504036400c40c0d5041041c962a02001c4039092034070b10902d180c500d03091012500e00c0040b41e1001440c0e0600a04141c5441c802c002d06240c03041c802c3e0300100101c0055060b4882504050f41507490741c0c2c001050411043c54a680090b004e0b080c041c02c5c6a0802061340d00d11400c000c040d40c803c3c4004880281607160b00d18042444071460782c0b046810b01e00803039185c44000784440c0006400b1418100c041c5a06603c2800500220303a42c4e08020540e00c4244101c0c070380501c90001000c010724841c403100003d481da09040c40141c030911124010800c1c003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 207833812 1250 207832562 207832571
    0x408040518090c1f050d02040503010219030c08070f0e0a0f080102070611130317041d06010e0d170c10050a02090306010609060504090f0920010e0906030703060e030f070c030b0a 78
    0x91051340c50301070b03440d01c050604940f12071100895400a000d590010354040d880001ca401054141c0003196200c03088994041c17185101c21101291039000a40c1d00c000031994400c1c00c07094440c001c1e510700074603801c09001c940c210365032825200c415949035404810b240c4d50009640c018000140607140e01c0c07440011f882460a003140f172584c58203140e81d2001404510348480300c0304c64044030008541c000c05542d501c100c8415443c03c4400d00c0503800780c85103800308003038041c004a02e0034403654503054a42c10103001c0030545d88540c015080f542c00000401902c1c0103041b01000711403550312865003d9078200d0001a220030103130b4107041c5401d02c1078005009001d0307d00001c00059901800301e805403441d410022030b0a641904801014164160f0010310140b100c10080008007071403070300629102c009903178150b001d1582605221842c8025500700d60942c03c0310009001040705038010180c3d0280250840c3d1810040040746d0040340c00c0b0700d0048072079680b0204100306000c5203d8400e074201c48030620400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 207835062 1250 207833812 207833839
    0x606150212040b030f13050d05042c040308070c050a080301030203070b0f03040f06142a040806040807030c02060a05030a060605270a0902040f030203011802010807080408040518090c 80
    0x25814080109117401c0c0300c0403d40044e61381480f0313a05911a80c0c0e4400110780c11b000041c48040c202d03130000e01440015040030b10341c1d20403400280003049161003800029030215122603e048490480040c580c00502c0403404a00000074401c0001031130003401000e20035242c2d415817040500300380c1d550748109014070701400705541d58081d01045a0b00140d0081e00e1801a0443e8170302007001e03280c4000d00d100304001032000c10030485200c06c4000540e8401c540708103000b0300f40d808000c2240c0140c1c040c3d5070196011000241c0015403920040010a000e4181030401d00c02d1980040c1007a07100c0784c03112000a40100c02e008400c00907000320400b030523a03820450f051401740005041d140905203408030100c0b81c44008072000740c640310980c1d4058005d020003595100d4076042c0d841a038244512040780130b0742c40c000100c9078007a1391050300300d10542e0587d10f5840b07035140d40004a07440035000d48180c950f0002040b0004440e40c07800900400e01050380a500203505c0c210040030708090030740410900640d000c40900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 207836312 1250 207835062 207835079
    0xe010509070b0717040905062119080405031e010506030a030e0105030a1b0c020f0a030b0c0a090b0a112e021b070603050f130b01170a060615021204 65
    0x1d0030750780d100941035100d000c1410322400307540980c0d804480c08440000c022503621001d40141c0d00c20310301a60400384070004001500d540c585400c02c5110141c00404250084402c054115412039005a914500309034407280082c0c10800c1a0204280b900745500b1004c030052420300415070700140071000340c60110050b482c060914240710319090704100c400030001d404184c050340721611903080003401543c00c0c1044980a802c0c0840348606a2051000300707904030f20351900322a0802030701d40c80b4284c241c41c1d460300070380c00303200390800070500d410b0002841011590035514000390051644030341d031711420140070780885420103034101005040d0710380e004680001c507003580303102c0348201404407030050f90b694541e1001300c0818442c10340044540070388031000415660680010b4040c0006d581000410344485244a480410440c0000c00b0460382c0001000080501c880c40420404a0780546405800710754030607084601d540c110300708a50b4580c4810039100d40c10000c0c15403002000104a01e01800e100c0340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 207837562 1250 207836312 207836323
    0x607080601080a0906050108060105131118060d050c04030c06030902030d050a111009050d05070f1b0b070f0b0106110307062003011410030606081306021606050a0e010509 75
    0x34140084000440c1d044029903000c103112980242041145503103544110740c27070705002c1c440c01e03100d111002144400e0901510418501a0961140070700d446120b1851b1000c09450034031072176214105000b61511501c6500609100d0809078206035529810351400d0103011100b900548201890000844010703200041c450001100600f040346e10742c1030030002103030380e5001e510f4901c0c0300740543c58660b15002d240c1d0b04000c980c00d11840542d82001d40514044642707001d080300c00740c500045072903068045451a03080300803410280d581c22030026182c4070545000c1c2d00001040b03403105040258802440301090580b130241081e440c148100c048486092552401740140107003640f03541d50380144140c0070f0b01400007540c40400278001c0d165a562440c00301d8203400f102d020390040718980300c030051f40e9101e4402c00c0d09603406611017001d10b40790816203800c00801d490046404940c20001c01c0fa05419120889400138407861000c502444d2040405003903548000600c00d00b60304140600202c034602140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 207838812 1250 207837562 207837571
    0x80d0f0512220b0a0b040e0d05030a14070f0207050108010605040e0c2b050c09010801030b0a0e011b0212090a0e1b0a08040224040b0a0e0603010b0912060708 69
    0x101c121180c0c44440c8402c101100a00303a00300e8805084052004001c1188410b40c03007084c0850003040450404000c2c0015240303402d03602c03c01034103d0440d80708450300130000303507030029240c04000691148100c90701c0007403001540c809001c00c3e0030200c08030701d40e0390401c42040070340740a10b083d25480d4540400a0420b004e00d000751fa078078410500000d40091201819200368a60290100006a40555006040502c001a000201428240041e080b050403c0440e5400301060b520100e03141e1071030b140c101c4041c4001d0f12089405032100c1c2d802c0d505400c24002c80650340d0303441d060300011005216000c1e14210130300401c08140f5a080c04003d0903945c2c2c3c0c942c800d04840710380c081d1908aa60703411503004513080c041c0311580c0141000c2441d801c07095001c6542d6118920a4800701d40b039070408036201c01488000030f4074400b001000c09c424420146990003070b00210440f800c09400c2e01d075074000015420f40090704180c05200700440d41903a68075003a040001e00a51600180ca064240058002c025030b20042 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 207840062 1250 207838812 207838837
    0xa0321062303030702130b030f0606060306010305280e01060906120b0415020304050606090112020a03120e060403060b040b06040303080a0903050d09030305070e060c06011202011707020601080d0f05 87
    0x2200c2041c561000e2080310200342c3d0080c00000010283ca1404004110030f0582c2d42c0648250506000c10031400a040e0380030740301c010020f40c21030765510011001b4100007004d903640c0b11240d008010042d0040440c1c3c1100b07070380d00040445d072206070a4690782120f0686e030000000c5400d02504003c0c0104803520301840301e4102c98646116a81c0b41810a20794440300c0790a211f8501c00010041800030201d031080c02024211001c1000340da075115218183d0040400284d48219104401c00c00111140c6180c00d100d0084c0c10400c0d0802a540000340c0070b038115603c251085a10740c00c4015040c5843d00c9034440003603044400c14201070070350320000c02c01580200043c0c0d000350781b0032003c41418003d0040c1c50044410210a211805051034010042c000503607855001c07070384e10400c50703025207080d6080d59501c0f100c60300203045903880c0640a008600c6840020380c18010601040b0080400c01030301705103c0d02042e001070002c0c0d4500700741c041c5000c07901c005000420030070001181c45154003204691122440c01d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 207841312 1250 207840062 207840119
    0x20607061404060605010914011704052a092505090f12030901080a02040b0d2a0f02101401090905100c020c01110703050a0f050703050a032106 63
    0x52030810000c2034540e0503800c5040c81d4804210402038183c00c03840c15030783e0030380c0d5441220750f882c88021303400840741d6142c501007110100b018401c0c0303d828400660080c01201200e1030403040003105070f0340e40041c00884452114079000012942040480d194101d46140c68203d00d0581c100607038164a0602e2000342c08100001a480c510759403071303610703038600c41030000c100008030644003030b05039078950000c4011800b040240e0001801d4640f98030a583c12200144120382c945001240110010f1000351003481c50240c40d07611210001c0300004a5444141183d00c688520140481002c1d14054000344520f0400b42402d0603c100c0070076060200f411668801400302d240a054a0024108605a284801d20a1074620074900c01c55000800c201403c20a0300d81b80e0054030301c12072084d150305035400b01425030303403156203000002900d04500c10710041c002c20a8484182d181e03540c0c50f050207a0000d0a0340001c08580e074520f550a0100101b00101c10071610800c91207241200700c1071586034100d50340740700c040304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 207842562 1250 207841312 207841327
    0x61121060a1505070f0c0e0718060e040b0301060b0c06070813030c06181502040f050f1807110106030501060905060907020c10030e070807090c0206091504020406090f0b1002190206 79
    0x322001d45c2a5000005050711900e800c10309003000d1080707440d000000e07042c4c04072512664540c000d80044d140e941e650203200000d14014000035005a0a0300b82c0c040d9031300c6600080c6041c40c03602512124402c078000d0a000c1c18800c100421700b04010344407560340d44040440400194000c3c042c0d0100391350240010400d42c10445005801010003007000c2c0c070050754504407038041e8529900400a0382c400201c071850064a40b8107011415000c040c0a581150494540c000301c1101740030500e510110758035256030070812185a80e07003074030a29801110319079110b05003400040e0150023030540c00202510b440c1824a02031000030741d40c0b0080e09090b4042c045110f81c450318184a42c00c40071099658004483d8084c0d980c0c89019540d410510038090717090301c0d040e1014a00b62011404034002c40c4610020886d0f10603048070310b071031564084c0c02242d0043d600c40340001c18141c1e80c00b07290151080c044000403000c1c29403060200f00c0024182400c119000201d5140342c807184484982082c03038064802c0c58840a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 207843812 1250 207842562 207842573
    0x312071104180606081c020615030c030a11090109050903071709030d090e06030d142208010c03052d06030c0a03050703060e07120f061121060a150507 66
    0x8a00369a007410103002c00c05a818401c00b03070400000c0310300c410120303560b45804090994403418150000b00c010f070040e40c003143c84000030b42d0400c1d03540310000341910481c02c640b00000346840140c1c00c048032904100c3d0741980c030920346030301d10500401c5070403001d00040ca0a6120b1540b01e104d003400040c0612107010030200e03103e0b110019034044100107421150114040c038000f401002d0284a6810078420035400240a070034040303032484608031103889221403207042c51500c0d10340c2e03040012900a90341d05d001221403004085050200201440070000030298400c0e540181683e100802c2e400602da01c00109280c581c4d9500f000307071441c4460b003051201239111000000d042450003115281e004102180220500c03e0100c1d00740112849039104100c1c01d2444044e01c1c1d101da010380300e0341244090840045002c01c4407180d00405641c807a5400013542410100d009610743c100b96048204000040c16550050b030a0b60b080c2c54003c1400c86510a640f0700e00055107200c0d045c810480010050003003201c00802c030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 207845062 1250 207843812 207843821
    0x305091207031e02040b030c0f0d030e090103060209031b0121061205070e0703060305210c0709061701060308040b070c03120810270e030c01020d0603030e0312071104 73
    0x5500016246028006440005426036a200168411882d00b08050a54600002d034100030004c090010a011041001004020501c2b440b00f0b809100e041c44061a542da5a2a026030186101d1140140c4852925080c036180c1350090031100e0140500d2400c82d507035aa00f103400341200d150140343c00c2d00038100085d0200051702c05035200c202c441808000c040c0811801255944c1a101da80d8298502640ca4010480030b880b060301c030140c8103821019203460740350a0b001061095600d520034203458981c00c1c98106140c0302340b5130303c035065444e40c526080c4108840d881c2c200248000580003800500c0c01c5031240e8603e48114172564200c00c0e0b0000c5c0a0701042001c0011100454001400405c2d81501100c094840c4104992003100e1081c0c1074000300351134022080e44990100103140440d02c0c0740c5d003034110800805103100c40303113803904c01486403c000d10790900042c004422140400b0031107514510340a0042801c600d5140d01c203801c0585064610390312034082e148a20740010315400c0b066110004100280f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 207846312 1250 207845062 207845069
    0x602090a0801060f0929060304031b11030607180b031e0c0913110d0b01030216080c0d0f050711010509090c03090d0f1205090f060f011509030305091207 67
    0x25400d02200180030b0111100d5802155405070040c400391140d03081c4204081b10000c12044040d00016030310781182485809545d000d4841d0504980e6558613038030880324042082e00071100340c040c07120031310002c3c2418054035401c03189504202002c942c540118a0b100d0100b40920707030403d80040001040c6001c22a84051031001c0c90400d9501c03401c110f40591010b51103114640d0055044070343d4182030300d000f88240703076201070303001961800c04002d0810f07440500740544046041540921014100030080c00360062451305c00c4000c165510f44802c2d0365410a01122100b8090140c260180d008554222f03007181d603101c0d031014500511030448001621607010360f213030790303600150f140080056000404c0300450007a04400201c031041c910b03080b001c03160340d02c3c2555500001800b01c0348140c00d8880c560000d9421120348011359402c04001c2c03450700e20381641110340b64100c554001c010001c040e501e000902044543e86041181181143c030301230715034458008164050081d8003030a4003c5e0b00c05016800c0076 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 207847562 1250 207846312 207846329
    0x90c09090618030423041514120304050306013b180d0e0105130306090b070908010b060f03070210090309060f05030112080f0c010c0203040303030e0c0a030602090a 72
    0x2542003510016581e04000c0798004404608a004091200300c004241d4084131001c113403414000d030520b072980d8020303521458034a802607202c050800303c061091040c107010b0503142510364031541d405030800c0f0300701110358030510264000708028011500e01060b403c1c15600e0106580c65071494140410025810092403003e04440f803080c03849840341c0825500b40151681e17007600055200b051502519140480400008500c0ca440110030950040c2c001e006202c8261081000140e0340b5220f030f0f42940e400c0d080450728120303040c0070004c00c41d030001003d88c00f9151001c000c025142b00303600800e40c580700300600d5283c8030b0800b000280304180700f041000810b413400030003031148805600d0040c103d1078040c049d60002c98514800c9103d41c52041080e20f040315041403c44116079641d49a0b60410303405010318140e0341004003c605a030200900589018148070b03030007107641e10b1841c140107049881502100300c3d260000d0f8105000f039500e003204040bd59812080050760781407401c0000760125241c1d807080c0e02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 207848812 1250 207847562 207847579
    0x3070b01030b1008011506110c04050c0a08010f0b0306090c190206070908010b010e0d0507030f0f050c010507050307020405311a0105010f0c0503091201051602010c0f08090c 76
    0x4004480300503a02036a50f4005050559031502449402d0310480b9070010303c2400d00c1c4804100d594031401f40310011001e5a001e81d12049000d001040503110200c48195034944002401403000394095185070040c01281c130743c0940c141c24407400ca510f41c400603010610451410010480da40e00642c1250111102041c81080440010501a40b00c3c90100c1d4051b000c40d9950000152440040c081c1c480741c804140d445803c4d140c004000c101c80344450640c2078a091050300303000300008075500340f582045070142000060707400c034500d8071610300340e101c448007410408140041000a8400000c0e9241c3c603504650206081e9500501110140c0740302c1075880d4001d0399020b6429034040901104071019008441000311107101e82c0c4591a04d0744203109090014107030105c20018540f0072041181410301c00d0080d01d10303101c11880000c0b426142901c0c41d2000d65982d105000f203003c1060b40a034103800d00d0340020b0020a01c240c0c0c4c00f40c08615280300d04800e000f24200025100079080c4862003503c08000d21080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 207850062 1250 207848812 207848819
    0x6030109050a0f18080c0a050d210903080105010c14062815050d061b050408061f1403070e0c0309070621021606090b15040b09160203070b01 62
    0x1500054502c1840c5603d0f0450700c0d02510140e000b07404100c10900783c48010320a182e0351300b007080c1d03110403408a000e020301c0c0c0c0e000001800501858600b4142952100741074400414204d1000003640001e010062500301800300107600020003034111102420210709082c904d0904490540c940051300c00c0a0013600108001180f01c299000c1c0ca450300c0c1d1001103654800071800320100c43c44d0b1000310303108040d269406c000b186440050105c003113104010109075181c1010081540844260701a03011076004101805500002c006181d8800b000c6428002286400711201c10f5484c07480c0510307061142c84641451040d1404c01042d0028814a00c040e00a4540082181d805030010340d005c0c0510300a0500c0054081c2c03003480000c1184100079800204280394032905070003980051007602981580d514280d0124007144590101039009610141c1c0707504d84520203000144c070403401144541d2903e05c1846140d128030314129400880d03045052800303041e4540603442c2d800740c6500140503844620011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 207851312 1250 207850062 207850079
    0x30312070f14030606090f01050c0105041505090c090a0b0d051605040e030c0d0c060603050d02060702010b151902070f03080403020a0506030c070b180d02010209090106050705060a0b0f060301 84
    0x5800042550703481d032030b00250030040d07041d0b240b000b6925203602040c01d001c1c8016034a00301c0030016a00c2c80c141000e038540006030070300d2825950122025224444004c44010100c003c0d030007170540c440c3d00c00b000340c24040daa80d4001100f040002d008103c026980d160342d0519522100000504107801000711401034108040c4c1462000780760056601030340c03d080c010101c0340b030004181c6806661040150030344002000341120600c140700701c180c444c1e03902c078040000070903018002401001490b034090000780c42e10745c1c2c0113403d40300411101401124020702c1e05490b00240001c3d87c0c00e0300d984041c034584883c2054001c0b40b601c00035400440310180c6074130000003004080c01c02801124825212003402070354440801106000c1202c107080c601504020110000b0600540c2d00e9102c1c0842c0344880010509640b0945081c006c1900c41340580e50002d806401860802c1001e4010510f5141241c0703071452035035a440c0c035081301074655040300d501e4034840012a80c41c0c15041e0404200948056100d69403100308 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 207852562 1250 207851312 207851327
    0x211e020c0d0302030f010905060301090f050c1801050a0302010c0512030910151208130e07050706061a12090102040302040903050d05061f050717040e010e0702010c0207090b03031207 80
    0x200e5041c460381850140260280c001d69110307041e00c100310030702680703050320720000340a0003040310707074195a688040c0c00014190078180d40c0e458020001400064000ba042c03110f40d01c030a0192014496041c401080076594082155003600c1d0b0a1034440541c02080c50020b02c0e04045420a003041e440202c10000c005400107000c90659003102028003058080c0c207030180c01c1c41c01500400003220940c10708100880c0b441c800900200300c0315038a905620f9603403480c0ba42c02c010700b9600740e4002040000c41d0f00610a40e40981d5000e0003502c001c1011504c81c16134425481e105100180102803d0030b00001c440c0c2d802941501c0003150040d1050202d01c4a515005040307030310240148101c130386048003103031950915000c0c140c040e24005c070600380b4100c49100d0076102500300040444000700080380910012000c1d1010340020880000201c16a5043c0003016504640c02400034003160324140d01031584950004119080710004031000030704100502c0804e00310300c12001d40043d11081c0c0e01c18811041d520265 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 207853812 1250 207852562 207852577
    0xc060e1807020312010b12010636090605030303061806150a050403030f0c0c0603020c07090f020712050703080a1104150f090803090d060c030e0d05030603060a050106211e02 76
    0x160151160381b40d0741c10081034026160520303008242030005000880c05201d401c40044652524043d001c0308107010542e412200c840c04041420248100700700442e6913002d140301070305040300514250b1a05c600400c5403124545440a9005500c2c0041182034407070410340c0801045008809076564290304010f00503901900c002c4002038002c0c0100d4029501c2001e0703510629601547d180c2d5518903007003085000e5044880d221501e030141c5003001446004500c01d0002240700c01c000541c5640709410300300040d01c103040f020030601104010800001c2d83c410343c020b901002c0000c000a100301c1d08030804081d406143c00089600c4c042c0908802c005400441407841515a81c0c2e0b500d2016440340503080d202d004072140141c102d10100c6a010000740140c0196020210919001449091800c001d600d400d03a5a00c009011490010511400303003014480c0644c842102c3c3c2d8144a1545000c0000786440f49204020350003a00f2000910a8198190480c450302d40000d0070841c081c944102140307009620125 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 207855062 1250 207853812 207853837
    0x604090c091401120206030601120b0406091a0f090f0403090302120a05010c050915030c0d02040605040618120f022d0306090a050c100207030501020a0e09060a030c060e18070203 78
    0x2c0c000600a01c00111080400794080c0200d81540c076003400549040071580020080151074138100e0845840701c2c800d0b0340040c2002503000c9a45c14000b01e054a902d80745252490007152a200c1e0a0310b07988684048681114a0300c0081c2d44035030340e50400302c402b420b003900300079409000d1903060341140d4400a81c0c04c8080740510020000d01c00c05a1080d20079200e0750890541041e802d800c13580c07402c0d00c81005590f011145004403440c20f5020b55104082b40d003d5048440491004941405a154440c4a0102481000000032021414032500b482d18042030400144603032010300e020011511212008149281c03810a4542003044c05409011088601c442d1a8024490030002031380d010800a151042d0300c1c0c101d00501a6170103e80280319030300e94403600f9142980305000f400000108244002d10480406686a07003400b50340a0801201402c041d0840d8498815080e09101043d022900c4000301c642074102030070803114981c0030403a0b840c01c51042c061a10401c0b404c0204050300440280701900c85007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 207856312 1250 207855062 207855101
    0x180f01060b180a050306130303090c0603141305120a18080c12190201080603070b0c03090429100903080403080403060b0306010311130e06160e0f030a0602030604090c09 74
    0x501548425601c1902c1d1715034420320104050800894243c04a11300034900420408450345031000a104c280d0b00110000703945000003010203003454030380c0f5005011800780068011058840d1562012400e41c00026600006064619180100030b03aa11121401040b480404e90301d0342580d4480340d0500c1d08c107005440d20501507490940104800030700f004040214281d90b051074004649040c03000b40542c0d0948205000403900d0b00c48031025150500701c440080d84d07110000420300064880b14030f4450a614400c0c403070160b10b0406542003e03400700d800d0343c10001c20f000e0340d50100d0b5659103c0c5d1010f000c12000050100a1003a0719004105131b07400741e5030030300031040010709040d40d50101340300240c50785100b1409140503152483d0310605034003000d103011034000c1042c4405420400d0a540c56aa440910b51064050b503411050144c4007000840d0400700c690114400b007610340d440788100800480d4004001012a1b49035408181d881c2d8000261002c12503c40c0c00000042904240001d5200c001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 207857562 1250 207856312 207856357
    0x50105070e0a0306090201170f040c060503060904112803200a1505070210021b060a0e01030e15010e2202010c080d1407020a0c0b090108180f01060b 65
    0x1c55602035094406003a008500b0300d03503165038004000d0000b0490412854410b0038000d804003030050f038002e16401c445640242410b01c0c04000c0040c0f1540554280041401005a00d0340c0c1c012030254090741240c0d40d1031000d607130080007481b011084d49a4111092608ca4050300410a0740003036000c0e2031150a210541003400004002c98401400d4401d0740700d64101014031030080000e420308001402402d00e213061841e581d0000d40107040e90700e818001030f480070169496109400c40407000004095540915206c000d060041181480040f5141410341390a1855a402010082d4440f003e40398041c1007110758440a00c10800d10040d82d51210581007545a012a01d990052440c0c0141e4161580c3c2d13000352503a520341d140c070f41000d240fa10740c0f680d54516070000c05031a88062482030350b1540c0034140349806460040c0d1007075000c1d013000054840900c0341e800240d803c22200358011441a03400030580d07441100103840c014201c072000d00907508040c4001340c1d214040002d80100d82014032040e000035035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 207858812 1250 207857562 207857567
    0x8010f020306061b01060509040609150c0206070c02121501060207060f080609190c0807030c0e030703030c150204090207060e0f06041707051e01060503160303050f1c060305010507 79
    0x400e03200e1607440101001894100d01004104e145243da07200004122940d039100002e52107001202c082d1074003615215483d0800c0b00c240e900e9508044080020040275400c520000e548101c014002014489640420001c7d503945110040c180d500c1242103858000686030003640200f001c0c03041d00c0161065100220351103010341c400c1000d82c140c1c1d40d50b5182640c0c600c800c10050304409004014500d00f014000101a51240181e090704017450b1107005d50350a10440080c203e80b043d40d01d0070100705414401002c10781d0702180841c01c0303d40500c0c00d5501000103040c41c503242c0170005114100c891002070002400f060940140c0041030180c40c0c2000010b401c004015281d01011464a40c0d42c2c209038000303000511030b685000004010a208107040c0345456440b00d00d09142e0004c00c480c040180f0b5100b0401042c02d02454020f02426006002d10041420000381c2404041c0130003014031a01051030b9615011002c1516a4a0002c2d0440340c0b16480d00c0844e6401400140400e64141d4200310000d0303080307030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 207860062 1250 207858812 207858817
    0xc19061407140a051b03220f03080d090204021201060e0f010c030e0111011806060509330301091e05060c090303040b0d0b040606180e161209050d0908010f02 69
    0x80c1410101c80c030700221440f089400c0e921074aa05554215042241407183e0420000382403040341d08181000300d11151642e11110f414070b03a000f000b40d800303c1c0c01c0034000244418150b03460b07224200c41c00b085d490828070026010f4000c201c001c40450000c40000101e5030f61102c4207654984d0195500000e6803840401140c100c0ac04550250100705c8034150410194440c01c0c0c1460300300c40c00c000014006030103109401c0e180b46032503802d4854540300c2c0d005110900e0500b251a4001c51140b094441e14015108030034440741412081d01d00c4840740e010070054580707080d00b10708541940a00341008100c0c5074151211000c2c2c00582c00e941511440e000504042042412102840402001141003c1c03820b042c86242d075200c0740d100c2031295210301e503c891546a60141001400980c0c544818405210000400c0e401c401c0d4001c00043c0f00b80014071089841801c00130f48408441d1400b40035820000200d10050011524002c00511030280c4001049078000030b0700c416908204000e204409500001d00140d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 207861312 1250 207860062 207860087
    0x708031914160f0215010f0602010534030216030807110c0109050d0501020c06010b04051e1c051903050901020d030519240b0d050901050708010306020c19061407 71
    0x208003150408402d50056811554404080c4100c1d0494004500d998071003401c00c2c3d00000404400000a1010300d03020b01802c0e41c440b500c10b03100f18807074005840c24420000031030080a80c5000d50203080c841e85100381c040b120900d8440b8003c5176007241c01e03d0000d0443d1000c80d00c25000420908010500305004903510f00700500503580c03120610706220805c540b2000a45040341d1565003045040b0458078148003c40c000c01d40c19140f207442d280b80400344401c4003d045485080c00112640400190342c50041d022541880341402c840f01e09064a085031400c01001602c0115182c0340038080d08040e8400c1c0144120b28007039095403200c3c0c016501c10f0f01924401e41e80545600e80303005500694020641c00b030a819103043c080109030441600407014105440d4000554584d00052070030500c00003401403a0300321418070020070203454400703c0282290b906000c01001075400284031460140e00700084035061400c00d0919003440f06900e13084000b40000e1600c3c00c202c00e03100000854040c0a451202181e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 207862562 1250 207861312 207861331
    0xf0b181504230f0a03170405100e030d06080a02010f02060c0d05130f050d0929070c0e01120b0f16030b0a081506031203132d06150503010b0a0303080c0708031914 71
    0x10302003c2214001d804860ac40c0c222510040c4100d00b040d414031302801000b454214051304203080c3d140001020420b014010000b9584090144498010504119014404000c00c0019032340c81d00c4200b0181d02c030b80c0307070009050000f2071281072044c01804680202c000100d5210361940c140c2d102c41188100c0f681e401030403c0b04682da482d040800450310010b2810300d1007804221040c544501d03070003525031020b81142450407a031800e01d604208607028401e8000800d80c200703458901c0e145907115084040140c07850101525003101c840c141d254025264050841c0500b0389002850150344640c0038181185c3c8a80719205800c0c00007121140a402c490003042a00710191035040640ca0700c12100c5490720100cc12044141004400103801c001d010318964402d0318003054107031043d58010500c2d21640c1201e40700c4c1e4503007125071005603114404242100da0604042c0303c660348800c1c841e5000e0282100191100c0c20000421064001a00b507483d00108962801c00c010b446030300e8000304600301220f00001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 207863812 1250 207862562 207862573
    0x70509090919060b04020d060602030318070e0402010e0d080a0309050709090f0b1801050112050c010e0a0614040510020d0807020304120206030402030a0f0b181504230f0a03170405 79
    0x4507105400c2041303031010142001d840c0c00300c8034074940d085828542c050001604080240081030100c403480382940117030400248241401c090042ea000540070b80001d060014011791110b480e00c4400d01010400d03084409e150b01d40340c4000d0040c01400a9100c104c1e49402400004034a428140c4541411241c00081c0c07801c00100f25a51603040b10005801c4040c3c800a002400803110024001c0b18060000700c401d460380644545011458a07081691007414890003010303c45c4951a104580300841c0e42e140342020001c03c02c090004551300c034a800003a040b02a0003c0c1d0074450b900054854046030403a960204e041e40c4100c4126200d00030fa0059103030307900401d92102c0161400c180a542c105000400307a0300d02000c1985c44950b850300844003103500c092803c08012880e441c0200308016200000d029142042c1e2100e108400c554000300001c0059240c1d20000c1c1e000900070001e050b00940744c0c0304071041403001c3d0303044543d503181d0503001300c001400400203082e00c1440505000d010310b82c010010031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 207865062 1250 207863812 207863863
    0x60e03120d05090304181d06040b07180320010f050415140405060d0e01051003031e140a02030706180f02091b180906040203040503030406050613050705090909 70
    0x40103440c000d032004010740310a000200b201e01d604203808620f40e00200c40020347e100400c4058011b90940d441307542d0780386c1145080001044000401c140c1c030a40c2131900750207104189285a040c15200d0700058420010712171125036460200c8000f02e0a2982602d804c0a20214904121518440d40c05588412150129503081003406807203070f415121138000202d41040c2d11000403c01d035810400716021f04646402c84209226403e00c541c80d007004003018a07200742c9080d62001b80031950814a2000c140c1c090401c00560b8500c00d0104403440640021010b0b81e41015a4000f940d80d080003500b0340750103103803d08a81d00741007070b0603080304669405041c0f50364440e0700d9000c100301da0000402540014000a83c503000540554006098100d0003022403c0c025501c030051100c0244020041406203204105010106000005407079002c0c1d8000b4010401f1744d5802d02190501585900206609080500340225941c02401800d0710120030b0312400120713918071007007035954140e40d002c054801e605c140558 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 207866312 1250 207865062 207865087
    0x3061c0215030403120c020c0a080318130b0d0f291314030d0204140301020a05032d0703020406020616212c0d0809060604021804090c060e0312 63
    0x4581c000d00904000d545c083d0400c40d20b10648010f1a40040160080100c000c903d1038105581400382c0001002103040c40702031030b4075038512900c2030340d075a1080002400e400000c0310b464100800558006d0038848009105140031128a0074240f01151612000300021a0715030000d0500d80840c5030b0340d030544909890303911804a07401e0807104160744072124486001c21070340c0c00300000c0041c04414403005070707950301d4110b4414880c4400321100f84281d004002d8032801a40c002d0603030f5003000c1c1e1060103900d110b5003220341003210301440c08003810030114881004003981c2c0550140003119015000c0c0d0301265515207031000c0d0821801c21000c0880c0388640c4404ca07048040e00340e030002d646026800940311030007520310002142000e9112945480b4140c2c0040b403660180084c0c01d680c8052308042c2c4d46420110070807500c443c0010901d138000c0c0d0307000c83c80720340030316081d0784a4080700b80140082040076003a090844400420340030f10750204a200301c40c541c05050006044800300c00840d070250900c0b20b14060f8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 207867562 1250 207866312 207866317
    0xc0c0105160f0c080d09080307171204112b060c0306120b0907080a03050403030305060109031b23060706050405120d06080106090603020f0d020109090c0503061c0215 73
    0x80709406948460300000156090600b0300c102405900300c440703542e10707110a01c1d25040e80da50100b02049401c001c01c101c4250000705840350b080d48140a03020ba0001440184132a000d010a038000c010b68580a21092055150100e140800c064841000d5032001c00ea050004840c4010326200110f071580320807010848070351202d60441881d140102e03401c0d40d181e025065140107040b095401022803800c2c4000d10f801040014005c1a031480908518020340c0c4000d04640114800507080c507071544001640d41e885010003c02451f804405089255010f0803420000300d558040e08005045442c5d214036404404629075246000003460246080303d0f03555200c001c0c2102801c111428450209101030018402c0c024040c5c0c400010702c00200907180403c4d090039594581d001d000306a140140074000750701c0c0c82140c50502c0340c0039601d451009000c0d00c0101e0310082541e0000162a1514000350700881c5d002000703601501d41100d00095500345c040490616488880e4000e40c003a841354900541410041301 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 207868812 1250 207867562 207867577
    0x90f0906090a0921020312060103050f01030312060e090c01030c0e0a051c020d08070303052503021803030d0f0605061201120f1e051006180b030109080a05070c09020c0c0105 76
    0x20380309007010000801c41c2030044e0035030304070251708081507400020b0b10400031107900031000d20302800749040c541c0b0000c074003802c180009020840d101102c02c8500820703810210040220f641b0030001890140615a140c42d41c0100d0180080d0801410030071030303840303121450542c9400401500341c2030314000801c005941d0301d400214115070125842000b6a403911045c5000703500801409649180500d4014100c400c014041c40440182d04400c46101c0030405400c03518201038240183e5460200e100d1003011b1030740d0300c1d400b64144400a42c241c000300083c0c020001a050035034091228079141d404001c140e00072860214103111841004101c00ba00c044180c14803940580d080b695400500d403160401d04e11046030344071030060304071644000c100e01004070314200d43c0954020064075080a00001d01d180c82d141000012a48440080c0750555080d803005c280d60794848842c558404072800040c209030450042501c4943e0321507000914180c041c004c580b1210343c1c00c0003501c020141c10b030065450350000c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 207870062 1250 207868812 207868823
    0x3080106120606021902120d0e03070609080a060515030a03050408150637030809100503060102060615040902030108010617030f03160e180f0601020307020102071a1905090f0906090a09 81
    0x110589000171f00303100d01030340000a55140c01155425909140c81c03c849a80480c00b0004501000c03c00d0500100381d8000c29170340941c1c0400c1948403580d1010000903501d49155060107100640010550010001e004550707403081030340c21840044034802040c1b0001c44181d078000140c8400303a01240a032072242d1801c8601348110840320040b04940701c01c203044a80003240c0d10100064041814608040d1600a4000328074100349941b80c078800003511042c0c09008140103103c842e00308601c450800b001d5074082e00140790215142c0d0f039240c0380280a4011407040011070fa4140e05070b0703c000311010007181e4800582c0e103521491a120101003c07003400c6405004810085c0301c0d455003000b03030344914030159440070010708030702c04d8108203511446c444400742c4064195801013164800507600811040d04232a40000050b800c241b03204150f10b50740c49003184140401300b840c14020940c076080000b415104d1400d03034001680c0c00541091169254081d60501d60100d0b0a1002074805441c5420104a0500c142e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 207871312 1250 207870062 207870079
    0xa0b040903090e0c250203100216120e2706010203030702070303110304090e0a2003070b030901090501020304030810050103050c03160309060606020307110a0b070803150a0303080106120606021902 86
    0x14204c0180ca08a0035405c8900901480070786003540b4042041c0c0c80c801c190400110f141014002c8101c1003d141000700901c02220103a00d00c14150090316142c4015402400c0d0000d40941d40a0a40d2094803441d1400500e102c00f80200f04607520000a03a8801d9284d50001e0200701d007191001e444506000c1c502c4d0b44144000c22010035400c2c400e0241d10b10683c4240020f0684441514000030031400c5860000107901607a2045c0a070380e9000a1010111402130b152a41c0d80c0d1501da02c10340c09010300c84006009980000f00340400c155001c10800d01c2000c14641c80c03002d186d244c41c011000e13500c050300c00c0902c0513010310110780217144101c80421400d55500340010018841d565070700c140c80d00c50307001801680000c140c12050205201c030725001003100301c42e142c6c0f6141c03e04180003814051107101030030115011001800311400c400500c2c0b0107240007000d14080603503d1074000e10300e000c2401260300007000c00948541c001003e000341c03c1640e400f030300540504480a07001d00000702c00c02c1030a0340c2c084190f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 207872562 1250 207871312 207871327
    0x60d0f021f17160309020f040501330801031e0b090f0d02011407080402010c0605010902091c030c112d010e1e010806041d060a0b040903090e0c 63
    0x1032450080c081408415080010700700300602611106076640702da40148941403c21842a8034643e140400c040300f0300f40003030100e202e800400c00e40300b140d400d07854026207010300114101c04c0c09403806864480d41c21640404400c414030804040e181e42030320102184005c0300500c0000d40e2001004000445e1450071101048a9212071460107410ba5207c0b40940028440c0b540e60001071081c80c0b031200944c0000d112280c46004155001c800c028600001c124440d800b190441e8070420385003010a402c07043c1030245503110700c501b800a42c4000f0381d030341c418101c411b22109400d152000e400540c1c2c4d0903031207031110103480b0707140c00c1c0c4842d1a05540702e07440154040d4081880f230b000504d483c1d02824411010019070402400500800700c2c1c2c0e4825482580c41041000c440542c0c0421300580300c40031701c0c010a55807103450118003c0d08007202d01c9a00f44a03c0c2082180c0208002100b500c2400724120602802175840709110444201e0040034000501c07080d0144060307800c42c00c00350381107103190f505649407403003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 207873812 1250 207872562 207872569
    0x60f040b0f070b040b0106031506021e011104171e1504080904020a0201090213110a0f1b11131e0e0304090608061602060c03150406180e070b070b060d0f02 68
    0x3411102140c480a00740011f100300b9034113101714440d00d840d03102612280d60606801035507a1a40c86c0d0441848000300d1000468490290441c1c4100c003204103026031140c0c0c03120014074420f1451000003030300b4030031000c41b030b050b1510011505140d1070346880584500303c00d4482c200701c812401441a240300c8002c105210082c0c5661009080460556000044400841c410060742c8208640b203511810b00307010201e1000000007003201c5060207181802031448507400d1050340c1681100c900002420700344070401051002210008104190856241030340d4240b1204510032035802c5122868642c0313040408002c0082d05500c4070fa003210301c0c038007164101a1391301c03444400e80c0c04030b4110380501c0d00f2070380130701029079043d003a01950b0342e5681c00600400c2c5450288101140001020036408020b141240245510344d41d101501402a500d050281f07840c80c407894001030040d040c1112020312408600041100102c42680c00d401c0e880704040b585522030904201c04407080420a4031005002468a00142d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 207875062 1250 207873812 207873833
    0x30903060f091502121303090510020a0c06050301050f011701050402160f060b0114040503060c03190510080c010c020303041e0801060602011a0f0f1e030618060105060f040b0f07 78
    0x84003d40090b955500e00c0a401442200150442e820301003020f10000020b03130021103600a4640986060710342c80c4418208915141c2d42041c090407420300340c1c4002c1000350b03101008505803001074801c0c0c01ea40c5810001100c91820780354050007200c51800051040c2d180c240c00a0006002c00c890004405207551500b040411150304100c500654a2000004030350f080f804000b4603000a800b003e003807c0c5060301103034855400174513440c0440390001c0010300301910356051400289030301804200525000300e642e210700741c260180f1601031040c50360001440d0310075155280342c90b80c00b0703010314281450000091040e15254088040e0444200300105d1448000d2007078000070001a40007051301e403001c1c580318480c0fa44036002c0c18081c1c0c400345a11406525034a81c081d0807840d046d504038002c002d2210380581c0c00761850642030350500848052095008940c20a02c9800109009443c2245d9840040140c3c9109030001031001c0c001c10720040001d04200030107000c2c80c0d031000d5105480d000195446600d00d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 207876312 1250 207875062 207875093
    0x41a060102030310090c031508060f18030307081b030702160b1c020703030b030d020114010510080f10150c0c0608070801030f020406030c030b1e0601020c0405060a05030d0207140607030903060f09 86
    0x2542b226007001540102140c41075003008103ca111f00018602031101a12440000e0108080c45002070101d034078154090300000c140a42009042e480b82441d21001752501c2d11040d401d200980d05510100726202c040c81110030070401c040c22841e90b084d07c0310409001c0d4001c00000c6d42403580c3e07074141c1c00c0c081d1420321030340346001c20580c000100c00819145202d004081a04101e0107045801069001960081030040d000308a00703040d50300035922410b110301541c0c1d8680102c2c5003d440300045130801c0d274008641c600440c0c481c052461850b43c07030b605c046a8001c411116180003814540042002c00c0340454031080503800504045060340d10b039218102410003692045502c038031a41c04100340c011340e079041200c600301d06000440050801c600004d640d03940d440c0300184180e59580104866a55052095005040203820794a00d40c42c0900060f458a40b01d1280e01d0481d40341a5000780c581c60007030700312000350380d2544903102e04c03a0440c3c40303120080c410708482104160303680302c0090200d84110111180c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 207877562 1250 207876312 207876329
    0x20a0909140106090b0f01031806020c031c020c0706080403090e0c0903010c09030804050402090d1a041b051c03030212090c01090b03010b1b0a0605041a060102030310090c0315 77
    0x781c0c910901508660380e0750b10a1200501e40f0801c10811341c0d0301504146800800d20300880d10801c41800c00207080050030f03004095620001d1461050356000c40680104039060903231502c0303141030003400c0d4203a101c0c000500e502604090010b10100d4090308000c0d030840d000c0d160401c00c1546423001e01840071020b4a130940404000302c0d40d4551403801340035111885900f031504e1001646103a0712082a4012805200c4c0302c0c41e0081225100307a180c1c03071070107840c0b1500b24204d42c040c0c40c4640c68400c0a49000d4a081d91984180b000d43d5175002d0143d00c0081c11100050901a25040c0600d0b0040c01c40040901c00c904041c1c0030489000282a00c000c5203020340c0410700030340744c0c2103003010001d00b0140d10b03030b4440341c082e000c140010000e12a03003406555a81350160440c800c0201c25410450808403180700081c4a0307071500d01030205204007034805501c80e19020300904141e07114000103a0f501d000c00c03200341448101e60b141c14014044181c0142650010b00d04010410490390762100380000c0ea29000b0358407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 207878812 1250 207877562 207877583
    0x1404050a09020f0c070608251403071b0605060a240302030a09050114010509100605030a0e030915040905060406261f1b091d06030307060608030c060a051003020d020a0909 75
    0xa09601d200700e0004000f009240d411528800741c0c00182c40800074443c0851680402b20000e0348403070040c0034803090210b0b42a030942e007108040c601340c1c0061505940741802181500e9020528a002c82041280050030380c281d0586400071080032001f0354002030038800050740310858480011800d00407400e46501d02d0310400003960415040c44102d40c0001c1442d0440c15040c0c0e0204903094000301166002906440c021030b6192030b1520041c914451800707a150005c00030480000c0040c0e07000c001e4016180042c0051106440d45801c10050b03d03000e02401c0058040c420382c908075107441401ea8141d401c1e818054a603403a805803241c08c0e084180481e274100300354a03003c030f6680f10a008100400749083c103090100e4002c1c103040090344080009612016002d100b400455040e917020000e030748171254802030501403c0e880c1c40b40c00340c490b040381c090001944254408542e030040356010302807240b1000c0d00c014a515113543c0800c6083e41d04000d00382e8100d4201c3d603000c100303407003a80900004180110341140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 207880062 1250 207878812 207878821
    0xc1a040303050a061a0708130b0304030314040317190218180115050c030d02070321051915031509050f03070b07050309160905071404050a09020f0c070608 68
    0x1400e682d8024140020b0034036281e4240f04000b82815071241d69038140c80c0407a2200b13464a4140755610541d99001d2113030b4400c81d400a82441244000e503c210304c2035800b840280e6031008418440d078410f07100280402c80002a80000031142045a40d1200e0304612030f40c46d108000100c4800c9a0003003000034001448030072110a1400c1032070668920040001d40c030b1000758500005a541c04120858030381c1008030000704c0d07520b4210304005855001c84064003c55649825140203405440801814034100880203c0d6802c0d1542a10038240708045401c0c040507500c00d50f250b0b02c1c0c010001b0100780c081c001c03145140800480c41041100f907482000f030000103840340c407c0c1000c914140850040c84400d510800070100000d0031900e010350080501d091403502c07520f0300f803034560402d0651041d11800541600c0c001504800d036404c0a40904c280d925803200c00040b04003032407583d109030300440f80c00061030a01007000d605176900602c4a400d184100506003000380d07440e10705007101a0b0110001840070414070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 207881312 1250 207880062 207880067
    0x10603020a170906011e03050d0302160b010b07151407050a090315051b19050711030d0c030f02010209030c0613030b010f051008060906040c0516030909060f05030a120c1a0403 77
    0x1144e1025506d4200040d0b0751075a40d60039924802101c2d54403c0680105400003008000000c60043c83d43c0044001d1543d80c41d00000d40700c58100c00d074180c1d02161214040c0075003840234440e00740c0c001c035040040c14040d9035080042d10298440c01040040050138400000429540342500c00041c030640780109007400c000985e000d0b00740100608850042c001c01240304203140300d907000189501d103803c2c000d40750341c810b0805501c000694a02d443c1c02d4007a03030075618030040d03011282c0b2003c01d220b80c07242240220403401c00c03400c034001c490045400d1f41c8200040f151900c1d10f0006005180b03001c950703422800d81c4070358a00050348001c0c1d101c24054010715609016620340400035009182007494110b440b45080c80002d95442d00242c1698015956480494482c911940032034005410000742400300b541c251074024541116482181035207881d110002c03c00411041035681100c400800504400b21303585c072102c18004007854001c1c10f000b8010250000201c50b40701421041e1401c402c010698601400e01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 207882562 1250 207881312 207881339
    0x10260706080603150910050106021606022107080c012301080102070b0105060a020a06110702040b0925090503070f08060a05010b1b010f05090d140a08010603020a17090601 75
    0x82418001c501040046030b4500141e844c0d4140c0101d00710000e50707103500311814203000d0009958201582004000301d18180c002034036001600402d079000c188290380c0c4004036140c214401030580440d000c9600a6001c004c40005031078a103008050070b91038809222101421668846403600302030056501030a0a00d0440d08898018140100203620f000c0550f65507042025050040e184643c40100d4034a00380d41c400c0007a0f00070300768080000c1044901c40400384555402c0700800b03d2242d0b060040b11404c2d410035410032401405240056003140d4890010b188040c44200c200c0d4040061400000440b07680403c0b0315001031082040c0305490600341402c060501000814001c2d40c5400c040040111414183c12240760603090340008600c03210340e001c1107000d1310512484042981c1420b060020b000d43c0814041000c0c4203688031a102601d0340c2d080740d040f03802000c02d40c2c4040348907000108211402a00100380d01440d030b180c44103c00b45103000428140d40c1c16241e02d4040e500c0b04005001140c0902c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 207883812 1250 207882562 207882569
    0x12080c19021e01021f0b040906050612030c030f2b0204030606090b010207030b070306030f140d0206090304150e09090d09080316060902040209060d0c0233102607 71
    0xb462048000080041e40c0c1e000c2d0040d180f44030103420000501e40c05e1441c0c0c00800c0e0000018070500c8040521305240c00902415031744503100d80c1490441405110000080700d07510b00300034018605103030807003c419206400c00324020003420100601042c0703510740c3e0690410602e52502d4010303140e030700b5810002c0803604146c02c103000043c40e2031210102681c001500388210380c0c2c0300000202c99550341c00b048014010310b905c001c10b43c801c1234403a601042082d80702c0d000d1500041c0304807020f10046084c02c82e50760805542c0d00075950000c00050041c040039000d1700044040c3c60030400038080a020100d0b1004000319255405600940900e90550b5030080441c4002c0c00080c0041d802c0551443c1990312248185200034035603607a03495440c04549898050781c02004000300103540f01d803c1c42c0040d00c050124405038000500445034100820300d00f001c288011302800500e0005c41003800c07e1100754690002d00403030984440548000340111102103400c0f842d01411700041041c2c910100710515200d240d41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 207885062 1250 207883812 207883849
    0x1c08060f04060f09320609100909081c0b0d12031b030203060a05010801060203040b1e04080d08010f030807031b020907030b090f0405060f07050c06010f140301050103050712080c1902 80
    0x407150a12113805002403500803030107c49250181d01ea243c080e02e130041e5140e1007180b9003400c14001b581171192000240910300c565060040c09200300051410407900c2d44080a9440740205040c280421050000510001080d050000d0781c070001340c41500200f050045220f0010b90000100080307420482c41d4a00100f00070300302001e1030350409a01035100e004030700a010304045c0101e4140c0340e05d19014408074000c00c01001c0143d0b01d41d202d4030031903203d0240707500c0c039004203400d0300000603682420f048600450790421006400c2401c0c658040310720320542c0780c0c403c210b89101050030300580da4001004e0b00444194400064a250b41d4040c4072420304010000c0c4882d000741c00400000c9040460000e62180442c04000d04070341d11141d060b00d0034042c030848001d1501c141d50000c144034000c11b100400303844040d00c1c51032052100c5c9040509030768007400028103940158408101c0d0b81c840140248000b449211201d04116070100320502c1c0181062450101221540f100010343c00e041140009800403030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 207886312 1250 207885062 207885131
    0x23010e061b0705010902191a07030e010507080909010f0f1706041e050312061518040209010e120307021203190c032006010303021c08060f04060f09 65
    0x203048080d40340c4441d0316003034440c54000410008101007948000c060075801004034034403015403261540c41e18400d001e41140c0103014006030480022040a4a124941c595100c0c440c4c503545000444154000c13000450b41d520050000344d2060391002d942601a00c4c090b02444045032a00e02ca080d5004c50b994840d45e00325010a20161040d01c0100701550300c550007841041c221507819841c2c400414004001401d0340c0004180c1026800813410240d004070002c40e0018903848040c94810154490201d904015a40c2ea130307a01032071410030341c01410070a00141004d8044401a2002ca450700b003201140c11300c6500001543e03011031411481c02219100e9110080d814817562070310024031b219500102006004020464000b010b01c24a1200411684000040c2d40300c42d403881640c1e81c4181c20b020480150046045c1504049410b00510380b2a194a035071f1040305440d040144291040b01c003001c0d80e0095126417011408501c0f0201d000000c000c0001e002940210a00001510041d01d010241e161100e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 207887562 1250 207886312 207886321
    0x1d0a0c06170f132f06030c18030106080a0501091506030c03080c12040905040b07050a0914030f120418110d0c0207150f02010f0b03030a0507050a23010e06 68
    0x4440405034842a2441a030515441c0d02c00492054201640001c1c800c00e500201038000c4c40700507060039007040e0160306015856040c0410090a40000c4403c07030744095082c806800c41181c092400458042c0240000500070b446080e854200005e0520980343d6030f445640700001c000348608000c00100c401501088101d0a6a4807410300103110f20026005400224010302d02d11003d00181c911400c4050034107a5aa6032600c1180213000704803006d842e202403070740000c0c14160003202240e00180c140d540322400c0f20305012401003158010025290184510445030649031010441d408d03500d1691805141c540341b9080401c020401c01c1200480003d04040000c84200a014103403844a550706101042d41c5018a00407840d12015038040b00c00010034010f54052503030010380d100320740c0503154002e1000f110301c250100180d403440d000c09c5030075500402486440700c0c4100007526110b440f540503680a006903844014103031040e4038002c0c80025951490b0041d610702480382e81e244805803800307480c3c40e02d0b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 207888812 1250 207887562 207887597
    0x140310030807050102040902030f0601020c040b13110d0603050c030d0309050d030504020d1703151804030c0309080f03210f180a0c17071d0c0703031d0a0c06 69
    0x40a12004000403004034401080003802c5d01681e001c0c05a444c400c54a03842c0402e094001040c059a210303026020b199040b02407070400b8041c0006907036020b02410a102c40110440c40100321601582e15800310078441000580c1c000c1c01280b0055005400804150b1a5401010304003c4007030151014145000141c400040000c5400d84a04406080001e1159a030740041281c0040b2500010403441400386403015030302003a406036000351201d03804040d0f034280d44001c0c01002009407400401c40031030303400050300003441600110f5210748a45000704c000c076901c510b5a0301c0c04a10138251005071300040395050202c120030045c559248000c442815550405554400303c0e06030103040081954880c12500315030f80c408115212440380d000d03031402d00c0d8555071110480e9040820030b140c0203034080d80500003001980d40742c0702e0758519211011800b40c0c0c0c0303580f0b08070782c00c0ea806100201e081c07640340c0113610740ca501c008201c00002c4251001a0080b18034925002c03500d684a43c1010003403020aa2602c0500013 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 207890062 1250 207888812 207888841
    0x9130c0e120709020d1806090606090e030403060c05070f140c06030103080a030c050c070b03040b06030d0f0e18150301051b0a1128140304180b18090d1403 68
    0x20011034005a480001081707160142c40301c0013040d10242442c003001c8081008550080c603599000b0f09003000210b44901208054414000c041c030030550052000f44082441e50748614460303041400d0051419401c0c0d6200b03420410b29040540c1e0080400d130130105910428040c445c440c4404891071031856055079603034100c501898003180c081554590b010101503001d58204c0d10b1941c030100848003100d80e160030103902c0303620846007140e061001c03002003450ba0030002000d4004a07110f4071142048d0b058600200d031043c0b0b107283c00a40c400d06540f40e60741c1f98010700c002c079070013009506099801c00010300145825500c0182070b280028201a600754480c0301040b054403160001031401d011195404080c0910b08901c001650344604032524102030300c0103c4010300310b10248140d8040d5108600090700949074011403044403003603110456500c4150803250700c1100030f0039004003a442258a005605040c1d200102c601503155031009030880b800c03d422501c3c41a044488035011072a61400c100817100c101c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 207891312 1250 207890062 207890069
    0x51902010c061a060c100e0c03030f070305040f1d07110d050c0106080f010603030f080610050c1e010e070e01120201031d01150e061c150209130c0e1207 67
    0x190f58030700000c1c00c01c4000381d0708049520f100604407512840c6541115440742142102140e02c507103004107031301d125403011035050740030072000f4042c505100170341c252902c0ba640020f6048042140801c0041500c52600c0421405007002e9444285941500c60112882d8880901104d09002c900052014802000269a60341813420702d0010344034150300188038050161908144401c0c05619000900c212056000104590181c7d4945000c9004113009940b40705003654940d820140c0f50300103c070f00c0d0740600001c103022001602151070091503030409008038082080465080e03515180c000e01e800b42c0801106002c0c005640d4044029450b24400c81503803005100c00a0501d5200d81d005210001c00f0845c00d462400e45200034084980ad5186941c41598240a0340078161001404184203061440303113440209485a00d83c1002a8580c0b6142035100081282e03040c090303002c01c00c2c4036154031034030180803042c00d9520010811200c66000905260140e000850142c0a6820050900d400c00525035045 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 207892562 1250 207891312 207891323
    0x6080c130b1b0a0609031704150504021f080105040b0a0b0d050c040e010602060405070e060607060b0f1503010315050403050a05090d020a030302060906070203031311040902041404051902010c 84
    0x1111250091000e114060540c4001e05020f4121000f040c441c4070380214201d1880317540c6070f82d081c002020181224aa09031005800b2110300c1184a40e98422a409140c12a00060000054403941480d684d01000d400380d900c00011000c400411003030405010f843d201c0c98046941034149414440c40441c0360084080880c003498032440460140ca81420449018000c181401105580c607010040d69505d0240c404880d144140350001403e0307a1482c09440c0103450052070b00c0c3c80c1100f145c446001900030711080c1a0700030011710741e00b8010f41c0c4003d40c1c2540e03100a101a15180c3d8950f040c000004130050343e0400480d818001003000080c0d1080841d081c3d0100c3d41840c0c3d07118417400000c51401c00c0f00d090025085001c4840100c140341c1c002407003521501016040302c2c02561086000ca0b240e004c192a02500080500080800281c0c80030461074255005040080c1c100c0460300010300750b4030800034444500104100303110501030203001d40084009600340400c803000040d400240507401c0300801616 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 207893812 1250 207892562 207892567
    0x6052407080403050a0309061115070f02120d09060b0d11130902030a060207061a060f0a2d0f0903020f04050a090b09010209030c0307030803070827060106080c130b 72
    0x304000754040d500a19080800c84409010515028068407118065980443c039a01441c000a00d00050961103140c1e2081c8070030f8980d164003805503800c280351080401540034544d2400b04050320b490107032448140d595004140801507007009000c544001c0582c3c2d010781c00c0b0050410200d0144400c0140c1214140c034604107011034841e4010044c0f04c42c00e8000d43c1405041c0c02e80c2c0a215094001c0d0035402d0050808100404645100250701180c0c0c0c001280c200e03200380040340202044070b000e1b004081c82414040d200c032540c0c1c8124240742000d02c82c186851284d21002c181e910b688400c2c1e00b41107840d04d081226005040d50005441e6407071545a1030b200b5034aa42c0000c9444902d42c008042ca16404002400300c2e04218000e64043e4001601041c024441c0c145504068070700050528100e0b5003000c60300d499901e4405044030b488100030810b4000a801307025001041c44002c00d683ca021003820064120342d4100340740140703e0f4002514075001c42509122403800c1c216048038400c101d4518140740c2d036 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 207895062 1250 207893812 207893827
    0x309061709030f070f0501060303020a0317060121060504090b2a0904020a09080102070f0b0604020406050906070c03080705060415021c0c02010b040608060a060602030a08010306052a0904060524 85
    0x40040201403802440c44d42408c01c0082003603000203d40b08654440c0c0c031012001d02908007081ca502c0c0e0200e48840c000b40344094007010700d00c1d0088090701e60250260340800c0d0103450b040490251180e182c0c044a5030b085107820418080490382c8032600101c03024030840c1414032950100d00d05805213032482849542c1c0000c0640003030313014076442c00c01401000c00039500c541950525518588040c007003654030441c64800507032545054400c8905850550700e5007802c200c2c03484244640e680100e6400c0310403400d020000b00c0410305100c05014018817400c01440980b8241c54419801c02c441e00e58003001e2801441016802d190113035081c2d4136051807200008200502038012400b42103644440c680041c504070f4042100385010070180e02c20b1008079402c0c0b002c0703503840c03400320394a2064641241c0014603550040c0001002c5820454006d614000114240b040212000180501e400c02417800100f002551490300c3c00d03d4050741d00204170440c1e07000c10024aa17101454080348100c1400340c100760000d82031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 207896312 1250 207895062 207895073
    0x16170601121a010e0102030a05070303050c0702120a2a034101051e06060d02210103021c080f0a0507120203210402060d0c030e0a0309061709030f07 65
    0x3481c024909000d401da0140c850040000e4840500d400201945001c440704d50000049900c0c840e501d50326186041c030309440c02c40090001a04504a0a000300040c0c0302607078032415558003101d10b0304042c0c1050881460011001c10082031100300206d204420505034800400914084035004940c210031410741036602a02c03421150004613410b4886003039102403001e50b8080d5030740742540100822881c0c9865440c4160381c05200c4640003454080c2d00060801d04120340a440c002401020243c246842c150a607c0042110b036080c5644001440c010001c2d031502148401c44584044000304000c50241c44990b003e00c604040e40100000002e803810100303201d0400c07201d04503041201c4151801903144025140c2d4086020750500200012611788030030014030b46c007801141d00809541c0350007041003951018243c092842c4061540e01c5c0d0100303102e41c0d400e0040b00001442640c03040f060724240316000d88000610600d03200001480c404103d190b034000821280c8141c940c00e0100d0300c41c034151600c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 207897562 1250 207896312 207896327
    0x60f090e0a03031e050c04081510061b0501050a0207150506011d030708070315110c07090515041b0201050a180b150315010e01050d0f02010804060f0204060c060516170601 75
    0x13005066143c94100140308440f503020b0429281b0030410380701481a091030400860006403921103c1c0801000d0070040c0500a01c510317620384452280d041d041e41c00b10b032542400c60703604a8482200c65000140c00b02000b4841f408858006142c0702c04000e1030500c0c200082981a03050300005010000044841040d501000603074000c00b40041140c102d01c0e10782c50110b00003408640d008140070704143c400c0c0f4800d1028400c2d0b0b8054032003203008240700b51600310480054440136140030789440c410718081045481d00c3c000d03440c02d030b40c016541c4070322401034440017821544010710040c1050b01e810600035040311289490022140c1080144945444021142c03941c09140c00c80c0c184d052040d102c0b0008101e07e5032108504880d12000c0600060ba641e405024a805085000070a140400c100d4003006600030b41445400600031003001030300701480b55494040b41d101e90820340101c1da0744488c40c0200721840c0140343c1d004004003074005a840800300040d01400c001c100c0288407100e0140041d440d079104014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 207898812 1250 207897562 207897611
    0x80a15050f2b113007120602090a0602060601050304032f0309030c010f09141c05160f03020603012102100513140f090a0b041802240313080d0c03060f090e0a0303 71
    0x39029a40e9050307e0114003c3d8000d15130075004d815164800a101c900124090740b0504041e1151031440c0d8039960b048480803a03450207080066a024403107900d14607040c02400405544000565890044104162a000d2081c02081c108950100422045a030005401c0d0481d40d08490a401c0039400c9000608044404448140500c4075690f030740c0240040080d141c5074000c1c1d18030851003059141c19039281900010300010350081c034100010040d05024100d0b1100f41c401c01240c0e9204000e1a90024128100d0114141c00041d070200c0d1181c10303c129800350741d00504401d2240301c108503041020900703062078a40d4191040c8107400c009010301d01e20350000e6488c400b000308104015158060005020052721070f069000319403407000a06040641c02514030603000b4400c00a0569407131a6044246100340e89085800001c00c6c0700c0040d0429190091500c880410344001c58064280300810401c81e415621003080541041d204400001010032109603641d0585404607290303411000070318046200d4030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 207900062 1250 207898812 207898829
    0x120f0c030a080402120a02060708091f0201020d06050406140f180901090605130c05120c1e10020703080d020906120403020a03080a15050f2b113007 65
    0x905601070a5018072003034407a500c01c496082c81115440211030307491140c4900250044403c00c001804201c41c0800f8200c240750060500031440c040c55915441100c0c0325801801607900030a00b201034140c00c4c0540c030302410041e2030801c0b6191a20b41040000200b41c90b02c03078020702c69126903070360a4a8480da245808020300b0010211814417410aa000740100501500d115250202203120381c0c0404040360b80107030b00a2240c043d0b89060400300280308441c0c10340f9464900c91009020101e80b2068180b85049960f000701c13442025108060008c04100c250141c5e0454111140900001d1901d8007580d480c05020305005032990341d030001044d4540301e0300d80c24040d030103400e00400080543c001000c0741c1880c03181d070342d07990ba13502d4059401058581c41246e00c2c0000800c41020b003d14208104d8452140800410755500d11581001081c3d12000c2c1c6a40d04d5040005105075409110714034200c1c000c0100150750103c544c5004510181003500c107c020002c01043e000840481d9160801240c0003416090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 207901312 1250 207900062 207900067
    0x312033402030c0d08070512180f01060e1003080307050307021e0d02070e13030302030903070b04140f0a110103090c0e0c0901030e1204121b06080f090f120f0c03 71
    0xe01a42c0d039000004444110300c99501c43e00c00380d030b2140400e0382c01400c1c0c84e124682451018026880180ea00070b00380740600170701c4200c20144a400300f1202200ca44c42e04c2c0002081410080c0c207075824880285400804240300c042000021020300031664480040d00e4819129143c0f108200d0400c1c1c1800c000fa81043d190000400d207688010808445590094003214011b03031f999400840c15480854003103050007141c1410758080390003a0010340c0d111100d081035030324001c51a60380d0340000030b05403020745801c20640e541c1081c518003001214040300f6402c0041220741d020350b0714000310b01e40c0380c5815410941c40790125000c0003190030843e00904941c500c400b443e072030174400010b683d400180015000905005071922100008282094226507480d61285040e081c41c4900890b400c014a040303030151030300e008284400404a000b60007500d41590380300b901e8240700700700c4007075100050002405030700a0400d030b000124000880d5044680c42d1520280c68040c0d10a1a1309a400b0341501e8402e2030000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 207902562 1250 207901312 207901411
    0xe0105010605070212070608061e061b060601030c020c0f13060e1b090a03020f01020a02030a05100c03020705190f0b07200f070e07090806010e01050411070f11040b040e010515031203 80
    0x45103184490300406c001140c4dc6a501c0100460039540e00c000342801580104c0451112803e00e0314030704a55580240c03e1101601082805004442c5207601c036088000c101d0050040030001144001501100c00b184103041c030a01d00d0024004440c14400288540008100c05000d80d000340504410640c004040e146450441e00302103444540e41c03004602882d26040d0300c40c0110340603100b40c60100380c008005005d14040641c201c0c0001c95070740c03000c5d0380003d5429a080001b5410420082c4143c05680c1c43c603c1d041d221808001c21341c0c0200700700644540000c0c0801804940010b403190480c1e030901e0605c00706454048050383d042034917401050b0039004510020030704018a0503894129882a44c04100001c800104a0301da40180000100348407014054000864100c1c000300190020082c0005500040e00c40010300311241c140120b90140d448004002607082000302d15200f1082c160050b0240c0b490795000c40300c07e0301c402440c444020794038003c1c10f94040700d83c00d8001c840c0d00000c1041c405e50000b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 207903812 1250 207902562 207902587
    0x8030d0606020c2d030111070303090308060a030b0411060f0d0b030d1103040605220305100e0c0607060906150806090714060703120e0105010605070212070608061e06 73
    0x19a00400c00540314058042490b420300072914840701500101c002c1c06901d115410880c110302c40d070104d075030540d22141c0701c02d10608100020015a4400e440004001c1c030185130180580d18000c0c801446003034008070070000320b0580446660710a5201108240521075500044c0050040159034551044049142610f459042d40402000141103084600d0700b240540110fa0b4050003020a0285800030b01003005068010350140540310030145181c409036141003140290200240c2c400c0d54160301858120751340800034810061a5403011000e030402c450f01d400899880e1042d04402011745036507088120910007964071046090038020178104e5640d0740c441c02c1c550b40f40700a40f80c14050340550000007801d10100342c00100d402101400302c034100748054030181d078110003140702640380540750031001410f414284201d902805071a1165512050180140031003229040b01410b0107070700c41d04041c45a280c1000683d41d0000c4200c030400b0f480e10440c480c419020510a8040f40c1104000c02d01e00c2e210720 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 207905062 1250 207903812 207903821
    0x2104030b0603010e19050a211d060a0c06020409020703030501051c0c030f14070b0c120c0307062d050403080604090c05131103100303110318091008030d 67
    0x901038034122480340c45a030308140c00c0b159051103000e65540403c48000300c4e56000c08040100e240117a0a454803001c05444051494083e94140140105d402400f2242d103504845d00d6040c1c0e112481010704000d0640000c03402d81d2045081d800280003004610008103d00f0703404a401902441c03006648499651a000e4007a0a0070f009240c03007840d40d00f0001091800c000741c900d040f80e810030000d0302400d28580b07811a451503410010707601580070300000d040e00e00c1c0810404005051098555644107400c4054a0a00903445000d000ca070b00c0c02c211054400900105940e00580c00120008029007a84c0544440d9000d940342000c400b144c41d507104031522055400039101b5402611000120b41d2208100811601040340040c0f071800c01072003c1c003543c01c1000760540d122904d500e000440b05400310090044c0d80044510702036400b4111000d10405911200408492150310021410700d0055001c80b1751060000c04400c0c020b280e03003800a00b0300c0305403e107000e0007040c0d0001944d98844000c200e460140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 207906312 1250 207905062 207905069
    0xc0a050a020126060f0105090607031d010504080606100302130b0901080f0606070b040213061403010e0102030c0414010909060e0a1a010e041d030307021606051903050402032104 78
    0x4424440c80f03126a08114155240c5080d40403c0303007180c1d43c80c0c60400c1404400b079a0306604201c800e00c10360b8084d444401c010040c40740680c80d00211428007580e03694003102007017007080c10004c051008200c00307000003690603044882250f04c0c40d00696507850840c024056041c2c603020700041d00c40e0005403010154020011040d00703903190000341d0b958001480700108261740041e00800b0800c140c0c0003182c50070540c2c80d0804d04c000e1a20381ca185800c4448010340c2e06075002248006c144250b80704c014902407244c0c004005101d00258254075003104005a0341c0218490600351600c0324007440856881004203902070000441708001150b01d5101c002c00b035041c215440c54280b85040b42108007a400740c0d4405e410810140d45031241c40c0400402d000240c000080d65080c0d20040403031240800000744040d5125140c283d00030720030000441d1640041d58640d50106061101c104007120503940448010086041c15003404030300c1c1c1d1101e00c08a894599100300e000d03640000710511100d441c0d44c240090084 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 207907562 1250 207906312 207906317
    0x4050117010c03060605070f140615040b0306060109060503090f0105010e01031e0c0501050708040308070803070206010e010b0a0f12050403031b051606092108040c0b0702030d12020c0a050a0201 85
    0xa1002c900030380450b9803500500c0c020400900c08a0300088800c88107020051084143c80b04903581407034900d1514005448461041a40304004c000d01c1c1424804c0186024048006007100c2c180301780040c0c080005801078000b001390000001f2185c86041000c42000c56091008001d40d42e5506410581c20300c081c002111140e01403aa8000543d403120401c12070a40c0185079204c1e90380c41c2a0042d20b26601a800071188024140000000700c0d28000c064400a4003612100d90340e072402e00390090803c10160061840d070f40c001c03801401015070788401d8554540650405404480c003504082c0c528008000c5c100120500b00002c0204055264204000041c6010aa1900340c9607500c410f860078051a0720240400e06801e0040c0301084160700046681c9020302032030200e95041d21980c604a45003101c1000108110500384820880741000b048000c005000d101d03800d21440f940004c2d111440e100e6032038100501241d544441c4a0258103d130aa00c1c903d90403110181000d152072a11002280c0c4140e01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 207908812 1250 207907562 207907571
    0xe100c030b04150b070f300804200a090204090203180a03080423010507090312030605011e0507080a030b0f0f0d141903120f1107030503040c030b01140909010b01051e07020405011701 80
    0x14101d002d00000c034080c0364031411460401c0c1f040c1c1c000e1648484a2b0281d66800f8900700000a20343d44d00d03100800250501c110b001d40c2d6031900102090b10a0031f40c07500800307c1d81c80410341c0340c0441e510546480e00168041180000c003006603034545d002009690b202d801c2540f030101400b00b2550440351250440c1e02c5120b085100c081140010340807100350f0720485010070350200a2094202c0400f0700c0c0f5807640307a2810824107225694a8065060700401408404240d84d000349507101d150a141e103102440781192540d000140250105400100201000701005007150301c400500500344003910081d200c0040c00000c0c0240360400038001b10b880450803c41500e0300888649e100759600a0b6003079403d8890495181440d50b5804860399803000f0020f5482a581050100c002405041594001d142da000301c07100300c1500030208103501e5805080f50f41d035a803400105400d0350740c1200960b500b01c00140710480d405091403142d20b04a101e22100254800d152000100e0b295450348244011901c10800802 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 207910062 1250 207908812 207908903
    0x10b010e03011b08090106030605180f01050c040e090709022106091015030204080604080405040e011a0d02211c0206010501020307060f0e100c030b04150b070f 70
    0x60807152114666912075040310101e03c0300300d000d500c249030840ca00d000001125070343c03a141d1108856098403c0b0300c908501c0300000420000410021815030b8080e4020001030074000c03038003516441140300d00c80700d0885410004008110500c61031000302000c601c195524403544000c0c14400750450344540e0456000004a01c045c10300009462281c8a5820403088a50038000704102d07c842440e142c0c005c04d0b400b0032021480002c14003059010310302c0307000042c0c1c0321070511040001340c407191081d612590385050320840e900401003407120540700065482030040c1c60940046006000e0711850780c200309589103100c4003100000034609800441403840130044c800c00d104106c0e2103400a105d80ca005038018000e06000c10700542c400450000e001000151921844403440d0620040745240502c455132101007044c1c2a8060184a241920884041290088500b07000c03207580c10500484101c41d201141000804c048020f89010180c0c0100701429203450101c8611201c5911555001c42c000c0c4568015 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 207911312 1250 207910062 207910069
    0xc0a0c080c0a260c0a021924120b13020c1603081308030c1002091c030f020f010c140a0219050c01090501050304030206040303051f08060a11070503040e0a020d020a02010b010e 77
    0x2120f081e200712000d8445d0f401e5136000c1110091030214119010b4206900025490981b010348090b07049250b440c00800c1c1400b003101504418607000c860400905021400d0106e075a085a404000328010a005032155011100300c0c1c03411043d0b030070074811054207041c04028030140c6000780c294803480310b05050341c540c0c03201c0703100d51039004200203180300780d01c072003c40e18646860350054130302400090054450541e4180340340780d030182d4106041e00070030b8012180d000240e505000b07040c41403411f80001d218404100a00030607072030051420070011840481c019501500c00d101c100c0e00103c0e14104d0710003c14240c14030315143c866074092240800c0d036a10780010294000d0066900c1242c040d0094145540d80c0c0e10b054018240085c01c1d80c44950300140c015501c6421440708038003804243c0002e185503c0c0c1040d10030101c0e1114400d0807221001070220302c000690000403501034902c0444140c8560710356074048400381c080c122426003002d00110311203a40e05c4e41507102e0401c407802642d80300c0d1a801342200780f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 207912562 1250 207911312 207911317
    0x412150207020109061d091303020601050a080d2007030c0609060903030504050d0c0b0d0c030608072904090f050a1a06090409110604090b0306010603050c0a0c080c0a26 74
    0x7030100d401d02004000d01c60294030034000c00341442c6c6030700301041c5d4110b000030b42140e012a42440c06650003081581855410080d40e0f000d0881924007021181c2004074031551107586a590508024000e181c1001c0d04060030742e22003800442800b03c801454892400c1c00d0f140d0164002c0130001040300c9000038815110760030510071240c250710b80c00c0c80c0074241001d215511110301c0c0c040c2c68180440c1b40002d51501c0c0d410080843d004040030016a52015280081c1a51a2544183e10a9200340014041803004c66a4202c0080307242d5200d1610000e01d4201c0036032030040c3da01030140540b80142e1a00184aaa040300e440f4280310141007000300d4505190b60850a410b81c2c0407038020005218039a49820640d009210050203409124281162100016150f83c07103070b00002c1c5050b1f11802c125140d4142088000e02404090030144650f142c81074041d05503014000340c02042061050b00142403042e550b04450031400008107680071901c0a0820b105002030700405c0380c003016191000c0c40c0c00203c600e401e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 207913669 1107 207912562 207912577
    0x240103030323073b0609011407050115060809070501030f060504020304050f060717070c020d0206030f0615070503040b0315030a14010c05070209060910080304121502 73
    0x4414400c00074407584641d14045007015200c1c034130341c1041000311815010341c0c00580710b2a03d240101e9540351584602101c0c0c8000280c00801d009041d006803070b062140c408801c04d0700d0350300d8000312540d000486000d03059400200303003400302d0b6110383c000281500c4018000300e807058548000a049920a40b4112603552003641407021010f02488020384c000340318189041c1c00c81000000d800110301c0180841c04000117514443c045507a4941022130240d00501007603160300d04110300014414054480b10b120746d40350300903505a003020344200c13040154804040d5080502d0002c80c00480c1d08003401103040c110008000c040251420404410524000c00d0401c90b070814807002c960031648441c03648002c00c0f600300002c00c00742e01c42c60f08064000f0340a64202c03405965050540c1086541900100100d0000240004010ba0400c90150215025402400064250441c640300700e114004 = true := by decide +kernel

theorem cover : BRFrame.Cov 207733812 207913669 := by
  have h0 := BRFrame.cov_init 207733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 207733812 ≤ n) (h2 : n < 207913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
