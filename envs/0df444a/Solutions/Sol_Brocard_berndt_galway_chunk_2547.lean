-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2547
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:02:01.313584+00:00
-- url     : https://prove2.me/submissions/93b02a71-e253-4aba-a22a-6f2a7b9964bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 457913669 ≤ n < 458093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 457914919 1250 457913669 457913681
    0x11030309120a061407050913150609030b090a08190912141204050a06030b120a0503130b040b070b07021c0903020109051203030718050a1d15030309120c04 68
    0x2807000d07408071030400c0c24840d07507104004440c0c001e40800340c0d150030200300003041806442825482031103011110f941281a030307400814400503101031822410358800025081400c58842503846442c40400601c0c06a030100d800501164441c600c1c4c0e00309540049248507252009407508180b20300960045208600d090150707811070700c103103052144149413a130068200751030000b031092070010622003484942d03a01403110003a24103e260010300d9045840c0016041701072054030880714040c691115091003004002040c41842e521a24055550741d0181c0404a00c294030400c6101070007031004600180d0a035004a412901910448584500c0c801c03075007081d00520107024021440d07a50b010411542c202e0b021200920701100e8640001e1400e400d944c2d100d110080c40c15080140a5907200d2103040604030807400b44c100503104076801a02c4414a451005c149210007140e120b442c80041c1040322224451301c0c410308013034043c6044c10202c40500c280c00d010449812028000d1000e046c5590321188104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 457916169 1250 457914919 457914949
    0x40f0609061a040f0c020d05181c120e100e061b030a090504020306090a090f05120324131806020d0203180f0d05090117090708010e07060c11030309 65
    0x100100b200e03888100f004689001526040c11418401120342960300402c9060441e852410041d948000c945108410785000d401c04507072000e90708410500d0400c281c40a0105203108070419440240c90200c00e9411f481600f28065200d29004644008240f00d195149081080a03201c2800d0592040c00000082980000503443e64070220f030303440240e60b0040e00760005080503641180303035040031004110f5404000f403400321040e4507014032208004003800440d90041d000011b035000441e0110151040f1b0f88280c82c034440c02558011010001408080d440f030400000411045486024040e10805014421590124104000440000300701a8001000d01030900d9500580e64076100d0b0f034581c441d4500d0000c540496210313081070f0600104c0020440d00002480c2491a11420392200498100d00080003c040b405d22113402d202c1e0341c0c1c0340046c1500607540b2400082c0300d90007007010f035156030300144c1c841c1900240f0051000e5001c00c0300300441a15101c1c018056900e083d5904001c11141e0f1a80404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 457917419 1250 457916169 457916201
    0x7020a03030c09180e1c0816320f0703360e090111040e150108090d05030903040305030a27030305030f090a0c060c1b0509040f060906 59
    0x2124105a41840b95807106089403d2035298241420890b2070601c580100d408130090f90b0b5500d201d08004100000c58101515068000c20f4020415005081080a84510340d03a041201c54050a09010b002541014505e0001580c101c07035000c101c034214180032000100240c401000b0b008a80700d8a1130042907841c3c026161410344003085c044072421802480659032041005050881510040160071012607000c25200c0c6803540302c0c0d64089004201c160400e24080d200050005043d03502c960815211312510595aa4850000300066828140440d9118110f420200f04034040c42d000d8000745400c90040d074101ca09051700e80c0e64407880e40c1d100d1800030f00421182818682601511889242150401580320b85041d1460f50083d000d40005005a02a804c2e10300001b501d400b001c00451603115088444020040c1d60b03114082c003080d22090050f503404000d812284011107020010350112903020306251003581d91a140c1c40207810903544215129920b400504001c9840341c09105400180088 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 457918669 1250 457917419 457917433
    0xc151407110d051905060a0606200102090604030c0e180c040e0a0609061d01060302010e0402031807060f0e01020f0a14031306021b0f010801061b15020310080a111e090702 75
    0x82482c41c06c0300041c00d05001c00e04202003400050380c00074501c1c004803152a03881e0055001800303428064020001401d0300000e01080010034400304910710000c941c4500f211018540b030b01440000d00031543c1c2c0e41290243e1141ea40c0c1159030505912020300e0128000c1078520750082c3d41c0c1c075a030030340f10588421364205885400c0c480700041103a285003803d908400003081610319580c0003034400842c0c611554403d90b4044001344404940c01041d030010962101540c541944948002d040c0c481e40e9030b5480c0000d807828002501030b5000007844203204c402d21009040c44105951840440b00c002c01d442400d60205200a1a06805081c0713984080c20f0f00360080d00e0013041d294008045c840c914580340b80f00345010450b18001c0c5c2d8020f020581542e6440c078081900761850748600d140a2b444100c001c0c003480030390421040340100d0707901640c0104010419060034a68900700a50b58060552001d810850404100d042c10f1910200050001581d0b41d080d5484141c0707000094070110701118200c016801c00702e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 457919919 1250 457918669 457918673
    0x13020301050c07030c110d0816030306062f1c021c05030f06090403050f07111c081623060403031103090a140c030102070c151407110d0519 61
    0xc054250b001601e00c240c036003042e00c40c2d02c000704804012070020705410001c80e0411590384582c900f440b4516080340c40036a072050a400542111040c490064000070716111000c1000307449030003041083c040c011084500c1d4511080c00790302800301c000103400d8600c9243d8500500c5003214010000c410f0703094000d45461030501d012603840319500110303034040103070070030800521035503032401e0342e4002005540e41c03d441d0391203190a03152031003488000319050030003054140412480608600501c1d0091b00c111081002004441c0301800c0701c03d10041c41010144158001e0010a000800125005600d504078043c030310424014a802200303502c40403900080104420305415008010048a18070301540c91441c14556203521a4000c260003404208400b0401683c500100007140c0300440c000c00071565500a8500030132040014494241d040da000c0b24a010168003c8140b10310210b01c1c40c070f05e40c0c50030525955840b200240300300c075076900c40042e40300b01c0045141080fa41c00c0d00c03054074920a00d1750410b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 457921169 1250 457919919 457919921
    0x61b03101e0e070c030f0e010e040e01020a0e030102040803250b10080f0a0203120912060a09031101050106080106111005040803090124030305070c0b0d020406140a0e0616050613020301 81
    0x2051441071000d03020b81e401c00070341d106e60f5422002c03030280781643c400311070040102c40501c4829455540181403114179a11248103500518075000302e61140d240c5040d600c420300d030907401075206000d01c50700305100913411110303068015000a07113505041400007145603115810868151143e00c5d0407404000d060042d12802c2110130a141904c038020040300c900c41c0d0000b03a46921750492502074441c041070540c850340303510451210040100081e181c15180040c007500c020612414140d00003500880e940704140ea06220301c074140c4001382e882c075413142c1c20714074207865103680c15401c1003a5104020700c50804000620410340642d1040412a07030381c1c10020052820f6032014013980d001e82810002d1107624a20007100803080340e0341400d00c1c4c0e40b40d80d820b0806d0b1078925045d5200e0210f4a00c00202d40c1a0a000d660003041501c400340c071010508100c0505040752070064540100c0410395102c0324402030f25040c406025140c02d144050f02e0811515500c060405405807843c25000c1081450401180f1742 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 457922419 1250 457921169 457921171
    0x6020f03040b15150d0b030f010c09380417060f090d0504050f0a0f14040c050f0913270204050c0a08041e0804030308040605010503061b03101e0e 64
    0x3003004003100c02d040d110000341e12038240b04c5403990151000840320024001c030b030020550740000809031021840c89850a501070124101c2c45000181140c402255000840110581400c00182c03024007024018100d0300585100394500d40031007009100010780942036052151210f01d803100034101e035042c103603144141110081d00d194440c1d0080c1081c3c400d03e035440400d6504580c1c044419150314003071103000c079041502640080d50b400134240b80118001104c100c0707444000740242c0c0e040056000310001102c0c540292180300c10070981c2004070010138a043d14125500300400c2d8000a0240440061081c0388059440820803500b141c2d1905815890240300d250b500c001c020000514252080074010080c40c0000e0006203194140d4840e100111494042d0444d06036000d04c02e80d81c0c0c0c42d102d09020b005404221400c80303085043c0800440d8070f007004200b0600a1032182060f903181c0d12117818024180c0c0000300111030100070402c0008826030811282c174110041034500c403403035505040740e02d43c00040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 457923669 1250 457922419 457922431
    0x180501080c0d020607020d290702030406092916150209100c051603030c110f010f120b15130e041e02010507021008100e0412031806020f03040b 63
    0x44403620350107403203020100510030f5048070340302d030b07503582910005490704004800a1700da4444420100a100c03c40320212140701480c1c02e5802465580c90740407680c074482c9008240c0090a54181081030f0802001c141191070707045c21100c940c4110250340c3c002a038105900a01d4070b0564160203100344014100036174255040b02000303529041960001c02c0d54001c0c2d0403412810021500e58810602c40c09008500381b100b000c1c18561101da0f0781e030a004006051080f400d46400130707642500400303032600c0e107040540b401c410f0710b6585816000030b10598500c030f4041c940d8214507468100c018501d80c2e4001c251030b01240c030301e07200e25143c1f148912a40d441c121a50442515054280e0600001c600d48482c0c62101070074820140907609240e06c0100c84c035020b07a00000750421410042100c507540c000101c40d126945030900710282c50303070b2001c4200800f07a099402415401c404034200715078038070030340000d0280d001e201040f2079114076550ba07100403a030144010741014075000c014402004280c2041a40241d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 457924919 1250 457923669 457923673
    0xc08060a0803030c0f090613030b0f0610140c0c190306290402070f0602030a0f0b0102070311091b04080607120606050a08060307050d08030406050a0504150c140418050108 75
    0x131410500101c840c1c8031322601003045d01800b054110030341d920b03601100c02280088801101ca20750380d144c041c00e90882035440c00741d00090940041c815090107602a0192400d13a03540c18401d034256022215141d000041541450080d0368140045844072101c0840d01060000e4010095286d806c003841260048160711061034610b0101c00508424502c0d0f400c8055411200141e4401c1c103032074511070807540041c008100c1d50010080000c0e82c0c413181c0c424034650315a04010f02c10440c40100481e00c954460100910000503008020980d0909a021560008808400354640748440d80807200341e4200f503209045036405a020001000d9101d01c01001040c43c0c0e400901155003003d101402e28000d040d6002c0800c0307810000504654ac041110b0401001c010780120080ac1e080e040c103040d0f903402124255900c604240109102d80d14a01c12944905e4201908a681e051000740c590060b180b9a21810100300500303038562415919403008200620100d6581c0481c0e180000c00d040a8480591101c1c5a503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 457926169 1250 457924919 457924921
    0x1d03010c1e02070f0611010f0515030d090f03030503040c030c170c18070305040515130209130206070f03030b130209031b0312221401021603020d060b030309040c08060a080303 77
    0x302c01304280541c141c1310f0500f00128070442c5c0012841c01003070840e2204c0b512600f0181400300075038995244281008040d41070341c401c180700c1d0324181c505003094410a0b50304100c450041010920800141d90030600ca0170712541c00e075a07240c0305c000301e500e80c68100d40803a86820394403600b084000c1281c003002806c00d54820210000524904006800080c4200207250f11440010104401804508080c402400000040707003400580f00b0190142610b041340a40c0da6500800d41204405041c00da2030356004100500d000c06a43c0e80b04c03421070310200b04505240e2541b0f012034040d520900c05511b1284510b000503251000c481c101485e22140c500b4520001c500040ca015440d00c3c0400e4900840e94569441d030754410403001050040c00e000d010000120f0f14854020400303e0070211681d171002c200340c0c215044c4d0109001c0d10650304001b8440258082218050000000c0c2c00c0c1d0443c0f02c0e01007006040d070341070040031008a802d0350801401c48001900b06010000305281001b91400680034100c01507041d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 457927419 1250 457926169 457926179
    0xb010f17060408070501020d0c0503010602010e01050f070e03100603030e090c07053409020301091b050915040905041202100b0d060902060f18090a09080a1d03010c1e0207 75
    0x607a040500054181c2d01c0006036041802800d40458140048160b8104411039007030200904503082801868015400d081402c0c1c00301d03005000c5c203070244482c3c540c000902d1300d500b2401c9e41c1050441c480c058041c01100c214520558640c411200150f0198441c203075000d010b1030810040d50740050040c242c410007485101d0104600140d202c00399046141e09401c0070f00c0b115889150011010072100c1c0c5d81700052408100008030750051412a1114442404a280c03a170800d00402e2014030f0f01e80c800500306100c898014030707004001c001000c42043c0034038a0252140b2412050756411101901c03140e00303017010980c1e46a0f0411508a09000b14401041089000702c00905110940c08001d41050340705e14000d425941c40004840d400d01d546041150350b0036200c040740d0602c480c0303850101d100301e03140d20002c0d0164815001d03034007020303038095090303031520640c103805540c030750801550501040c058180c0c1e2003071034909200d88803540304548c940d03041c0c41c488800540350b08901c0b4082c000c11500200c01c00c000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 457928669 1250 457927419 457927423
    0x80a021813020909030c07031a09010513080a12020d0903090f06120207020a0510020601091427010f020a020102070501050109090b0f07020a0605070c020108070c050618070801090b010f17 82
    0x14807a60440f4661025212000c0c46843c60240300d01a180c24040c65200100f046a10301d040c1c1100c0b00e0a1031b0142c041e5403030401d00303401c0303480403600681d410a80110541c0003610100081c214041d150910003044c02110300507500301d81024860149071507903512800300345500316600c90000c1004030702d41b03100f032418006c0c010041224021000e05032500460030300c0c11507460354000400341801600705043d803a2170150007903803101c0a00ca02208030b8503164854500c00c403c2c0c40c002d44209170b041c81c5c0060002c0011960600e59080712030982c0f41e5542c41903043d800d00c080780000c042a41140e0300161303c0c1c901505010342102c40680c482d100c1e29141031000c02c002440d141d515a0300000c41940d03401543c0d6603070713816400c09041c0000108545d117450204040d103508100b05904040c000c0e0b8807400d690741c41e40c0c029588110704500c003408035400303440040c40203c1035900588119540300180d400d0141e40b140010f09503140d0300c1c0200d406000b000014841d82c403112902c40010043d8140c00811000168080c0d6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 457929919 1250 457928669 457928701
    0x50709060c06020d020d1407020604050615180a0606031103060f0d0515010b0d0c08091011090604080d020c011b0813031509140307200103060b04080a0218 68
    0x103041c032a0000218051180982c142c1e26603889070001950380e803038080c25610040401d03070039400e5884285800700b02c0c074601c0015580d2203181d200340148441d86910610041800040e50510f5102050036050401e89402204642c007482d048280800c0740c500780200a0191000b820a000d4605070a2007008210b55480c1b452000d4940d0035900d8451a8125017415810319948400c8020140328040001900e0711150000300f00d102c0842000f00540540c00740d084482001c01c0e42c0704a016030118000c22004001540300e010400081082980340205810100f441500194000e015980001612000c1203406001042d404142441d1000d4145a00c0e0081c2c08400c02018020780315040200d62a40019100e0100d08082c64120307511400a580d8840860050103907500c045402c8440c11814400b01a0000155601254000a02291074040700301950040003060f03401810191994800525484d14100400150640030060a850345150051120000e84a004003820b054000100130100010652032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 457931169 1250 457929919 457929929
    0x121006210903021213090b040b0607020f01021c0201060e01060f080f070e0d0501020c1002040f03020f28060216060f0c0c030209130201110a03080c2d03041401050709 73
    0x15000c01c45090403441c00c0421180b0301e009800000c2d4002007094158640400c407100c58070b040c0700d203142000910062740d4400440e43d4000005005403801450701000b9218018410310407620b00c4402c4000301d42d08050301203010f00250f5901c410602c000f04840b0406405072140b8140161403800414000b0b00e00328004201c100c08400c55408900740314030a0401044400000340010404c40c02420301c02c1c001e62050708550420f20540203162085820303402520202da4014a048072480d107581c00744140c041c0703030641859120964042c080c403181c1ca2007010b05c10014855100c03080490070a40b000e40b5041d104240306442e03104034042041174903401811a941416545052054403106241840c0c0542e0940c100940c003d00003800c01030400081940280c1c094001da0315030b41d021540120980c1ca900e4095030290010701c2400c0000c070b81c0100039004003001c0e221814017048004418240b070200040e0902c007041400000028041030110080600c00c22003034480003001982040440500428503a100b6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 457932419 1250 457931169 457931171
    0x405010509010f090816090b0904021e0402070212060709140a051c020d030302090310090803040201200106030c090507021902090a1d06160f14030c04080312100621 72
    0xd6110042d2103034a021004045c060101c520301c1c02c0b4184a1804603d69004901141d03140c0460341d40c151809070161402581c01601c5150007815041181c9860410045003d810035020054240140ca5051503000030001840141c0103e00b449074001344400c3e0380341c0c850340c48130040a4500d400c2c0da8030b4401c241c01b2544112546020074090142d2003641c0420b461000c0e40c0407243d01120030515402da001080404000c4003524110130100b4400c034210b5002140143c0400803d100140065000700a2481e04032210000d400f00380c5204502c40d401e450003500100c0301c4a062035020072004100d0302415070424400c1c00541010440c100000c101400244c0e4041d20941a0314017144000b82c460388030000c0d140030304403c0c8601841c2c917000c031a942d0b442034809402082070040f003140c03d1072089501001c01075450b41c03140c1e21590101180c2d0540d800142c003001c0918404c010010301c400c410002003410540c5240060030901d4401d81410b10f8600552100081c0506a1405901010304140181030f2204c5124 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 457933669 1250 457932419 457932437
    0x80f030d0c0c0809131e050129030a1107020619080604060302060a080403140c240912030c090a140909010c050f070614010f0f150f030f09051b040f02040501050901 72
    0x150900501540c8010108041e000c0c800c1b19005029a00105d059800c1c52540c6806030040701854a42c0e100b4100e560020417400b440891102e074015041242c03070b40c119149140c20400103400040c1d0a9000c42c0d280d0000c1ca000880182e1441d800903034540c2e10080496040180c149140c0110343d0034803c4500d03020401603000006000c160046051111400030700120f00d44406110120580e22003040000101040f0042003002c1e0b20101051024400d00091024182c0002c150242c1221a00b010303042942c1e514061019108644940c8403910041c42010440b207001014441440f40a01003d070610249904040c14401e803650018121103000320303016519070b9070740c2d401d040400090041c28a071002c000304030400016007211a4006900f039403120020764094507610303c1d1041e8840629023041000c6031444000d0b0355514004e5108804050b905400880e410203d40d0b40c060038041c1e031380004650b18080d110f100c41c460815100c3d55030401100e08003140381c24103000000c0d0031030140c8600e150401003416 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 457934919 1250 457933669 457933699
    0x91b050901030f05010b040501110105060d0b070e090717100605030601120f020c0601080f0706021b180f090d0201090b04020402130305070801020a261f080f030d0c0c0809 75
    0x603101c100c03c10034a4004000958554000b00187d90051041a0001c1da202d0034080760302c0411b01c10140114801000000b6444060751840550b0400400040c02d110307400e21102e08544914807028441e50075507803880d45840b0342500c5040d8290019141140c80d9401135004d104064005c022290400000d08080c0c09021507100e8407400392540020b100c030454000300d560203103c0e000050b824141e4262030143ca041101c245030647d0748081c58030480c0c0040c0d0181541e260801c210980040c040385000d020108242c5210190000070743d070079540520003010100030446030380301c103100003800c0e464148001c0c050014a40c80f8140c048501400c0a0b01c61640001c407520a807040021000040da482002c1c0e40d6001c0e40c6540480c001e42280a816010070300d0711354000b41140c208991f20211100c401c0c1100074a403a03011890310f101085040c10b2800414a000101c1e0081e0104020b01240070544000d5544000707001c0ca24080e1010a0138040034000c220304800006603202c8c013075440b461400d5032490304c907107000c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 457936169 1250 457934919 457934921
    0xc0f06020a0b0708150619090605030903040501030506040f0e06060f121e01090b090d080a230c1b060a0624050c1006090207110105162604080d020601091b05090103 72
    0x6204417590018001031100810346c034403900d4205150490304e4030100c80c0d680d284240e03428030040300c00301c806030410442070000d58004d41c0b0179500102c0242002801c0720810440c6803c4618022060805500a004001d401e140480c0718603114602955040c44446403100c030b0540c0c50b9440742d811044006440c180c4040441c4c05d50002c4649500503040c62482c2c00c200d01200c4c0c03640065155000000d808030001020041c440c0a5601c0c40c500c1c205019500c1601c22100c2c490305000a4000f041420040001303805141d04412000040c1c20b01c40040d04140c200348074120211600ea40c40242985001d0340d500990125022140e00c41441d541459503a8020510006041c46400b21509041a2a00c20301017a008003030350240c00d80605c181c01c0b42c117000030b15400540341da00401e645c0c0e0101d00b000c051000d001818000800d036600e405403a00441c114680140e00c10940c00c1038002c44040c1e802030316040138040d810400e06005210b2040108044000641482c800e400100104020321a002030a00c0a5902c6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 457937419 1250 457936169 457936201
    0x11d09042105030901060605120403201f14010608040f050109080d231005010c0812041a0a090206040608091509070617061c03090e040c0f06020a0b0708 67
    0x2621030040d01c03945840544280c000340d658900750361070500003241080c010f40403262140c074502d038900f26a035101d5a04540041c1c1442c0d209180c0420000c001c0401e04003041034182c0003030300343e03070345032000c8149600c03181141c1c0700c111207003281e01c08540100324540c0c002c07030384c245c100b504110f034070305803005a042160140c607514be0014112600098540c40300c05440e800707680703c88940031342c0c5480d800884403d0200d0480c02c2d2603849840340110010004ca6004070040d0718074030f10a55115040440c0d41000c0c0e1034141c0c1c12a01996622141660030b13503108140503466a000707106000400200f406034004c100540920f0056800b03018503000441c3c0032242c1000044607003c40c00c1510b254919104407407680320090791080c400030441000b014203000800c84d44aa2041e20050150000e105094000ea1803c0500d58010f0341032000d200c1d000724400115030721072031240f4050000401c00c039203040c3e10744162010a51242d01150050121400000c8403842d01c1c6800074110b1070a07451035210003030403000c9540c2c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 457938669 1250 457937419 457937453
    0xc0f08070501051803190305190920031507030506010e030d0e090703060e0c090a03021e0a0b1204200a17010501050d02030a0b0c16080d0b011d0904 65
    0x40040340d00c104010054100c18894209640c2079007045198402c070316681c0c05000c0080031920030b03441c88095042e01c20760165604c45002100f180c0706030400400c0303400b2141210015110a107514000726880501701080c81c0400300b069004151000400d90a12420340026003440101500c076804142241e104803060786080100905a43c0c1ca61014980900a50b0300c03c13107202c0c05420030740000f81c0304501a1184108a6011261310390300344e9201c504e468082d9000c20031540e40720801d030201001507200c250a0024803002c01c1500414180072400701f00b100b400690050003131000c01c0000c1041386000300c420f00c0e003050344403141c0400c0145160440c0c0b06005421286904a0040000000e41c03e2080c0502000100240001c00a5076260344c01d01a00020015029406610100401000425040140e6400b0420842c005e081a240701c0742d00028003040e00040d601100c0210317220303000c81d0942c81040c80002003400c145104121514800c0740414041e0099407040403650009418030081190512002ca = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 457939919 1250 457938669 457938683
    0x141606060302090f0402151809100911031008010c05040506070203070824060d0b0711010b041b12050123030f010c0804050f120403080a2303010924060c0f 68
    0x11409034030740810324604071821b84c820000b0050078005081c000c0110f403a0580301200000080c0c8100c001d221885002078803d2015001445001502d80d00ca44200703440c0080d81c84200782d60741428000c5642a4aa03900b000c03499914090800c6c29203034000044804030360055aa5a494554600001e410081c1e541e1040300c441c0200c5010781d81042d01c6050707400240140711050003140d150b200c288138040400b410f00409480107500860b480c40c0c001e00d080c0a1968421001182100050700440c00341c0300f00c00c094005407001941621880b5400000500c00c2114603c005c200c25898401c8415503084134010707615003054062414025900c2c14041440c2c0c9400e98002480300415032607005041e5030040300d06460310b0080c1081101400004181016040c589103026401c060550300d812607a0340c45140c444041c0801c40c2c07083c2d038140c1d00d00c40e20504005001d001c070f2030304c075850520786c6e50903030310340e140c80d02200010300100703c1d00300c1003a115080584401d0314010643c8a05403510840e503003220380000d0110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 457941169 1250 457939919 457939921
    0x30d05130c060807030e010e1510031a01030c0815041202071a030f070f050901180305160602120906070f020301140a09051e06070c02010909020a12060614160606030209 74
    0x70030f41103565980550b9040e0360822030b011807625442e080f1407090308420802e4210000420304c00540c00c0066030802d5103100320b81d02e060307640e41d20101c8605918161901c0d40c0a100010424010301c410f102d0000c26445001d880c01205600500b003102f0b4005000400e89101c102040755602d200700111409019450154000300700b5428007000340d42c0040398454042012500001c8202e84500301140908060f5201d280c1411041001035583c0140160103040b101080b20001010440410160412510b030515128040e42040d03002030520010812150301e118082095000d0780d140c1d481282c1d901038016001140c01030380c600c00207016000300526526400031603c140b005220030703640495082441031044842c480e4005c80b181e1200103440c60341c070446412010009011600078112090600d01c145491040a910307140d0180c105e801c6036860f0340004071402d0388900503150610400b00905440e00740421f10710b0721681100d2561007624450480d80a501120710100141c94002d400a142d000b0249040303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 457942419 1250 457941169 457941179
    0xd0c052113080102041406091302070602091305040c0603060f064409010902090a33032009012303120a0f03050906072601030f120201020c030d05130c 66
    0x10750840e00807007505c4001030324001242e06d8020112a000e1002410300104889c101540324000e401081090320003d408100d251207640c0d80c03c27164100f290342070314002a2801c2034288a40d2aa903290050001c0c0351500e0000d20030300381c402c440c0c0000c40d241480c3c43c0c10040041c54020301181c0744243c10645d41c88109808000303140854a5070f01c0c40076480100c2d00d4290351411000da0070380c0c40c680000f9422144070300110f00d00e08800d80090000c902030b058880e480c044400031501c112008141900c005a1503181c050082044099180c00c0980c01d41d100c003240c5107400000a000000c06105040c136881c001ca21280201241080d51140740d80000c060b01d80801d104d8111100c0d590000f24000300003684030031000740040c0a0b101306400f8510310001880c0c1c45c0e0703540d030058540503400e082c4001801e44040c540c0c007a0152000e80309010b14440e441010a03401c1030f01d081054008802e0003103055900501514010120002c2a1226808006400700d03268982d4400744080740415000030340040590080030030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 457943669 1250 457942419 457942421
    0x13090e150702070b030c07050c031b0301060b0903060a020307110a0b0f010501051c050c0d050a14090f060a0c0e040507080f3106060503071203020d0c0521130801 71
    0x30001000d0811a401540c41d02000c98980100e802201c0d41200e050010030041c2d00c001000e046014402c44c1101d000c1060000080c0c030f0b105641c0a0403001004c03c4103122301c035041c20301545000706480c008840c02c1c440c0100000740c640700b0040500f140c00340c0c003200103032955100d00c0740803c1440b500402d41c0c0d8900c20609000740f180c20216481c65044610780300000d100d501c00c0b0b04540d40080308095650a034a4112060405003201920011801d4000d00146200b01064410980174000c00080015450b0041d00c0030041000001d0904400383c0186950030000d00d03010072411340c820399182c0e00280c022003062050310302041480800d034105262000b04144990401582c50040b04144c0259116545400c0e03940150b0507034030f500d507029000d1004034100c00d42c040104205294424000821217580300c2c40480d151980c00d81c0716800c1405000c60305014150180a828101c01e071b5454801e60306103268440783c0d40c030b141280e5400d943d2038401c00e00c10441c400300c000340c980000d6170403094241e0540e1060054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 457944919 1250 457943669 457943683
    0x10b03012f0d1e0510050d050a17130602030405100c03051903063b07121d03071b0e010b0403030e03010f0f1e2c0a02030102032d040b0c13090e 63
    0x54041c4035051800314951601203840000c148e4058011724800400359114070f05051145880c44503590244041c2c180da084042d11200505540c0d4015500e55103481d04000d4000d85c8802d1400501c12000861408a07511408507004080010010982c9a0440780102c000302103a5015504440141c0300d5201a0040b020030000072181408490382c1b00040100401200282980e4110128144030031810707080780d5640007000256010082c80182050070b150306811540103c60880d40441b1000480407850180b450100207404455208061917040ca082c1c81e0b61072040d404081c0a00000380d840c9002583c094000e9800785a08000604c1440108201900030303080c601c000b5a0442541100c000b80a0000c0c807c0115404c0f41315000021445500d5110100201900303007962580141c02050303003d40c0302400103600510542d61981c0e500c0000d1076a107401d1100f04a0304405080804003444041811240d0035a0042c040d42d22042c1d40d103244075011503c048144e03101041c50744c24021300019003c4045107007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 457946169 1250 457944919 457944931
    0xc0e040b06030607050d090c0e0a06211703040503130810230106030506060d02041e060215070521040f1101080108070e100e09010b03012f0d1e05 64
    0x240005890350402c0607120340b8100c5140b070008a0500c90241030310a180c00011061b8041c81c05000e4443d00d9006240d9031900486440003501e40b6000200400400c151030070f00f6080a2400015901ca410313a02c0c0302c030504100c00742c6101e040c004000b04050001c20f10854200f07a0f00080650380841d542c0c1401a207c4440c0071004000c2858040c2e10318030924000c45900007603c0000325803030f03a6828100f003540148000b40c50ba9820200c188100039109980d88000c202800d8001220702d040c140c040c1021002811942244045420541d8000c1220200041d019003140319810880e865042c07240e50101c0e68a15000460130311081002480148035003000b01040c480c0c0140103080c11640414010340d800a000e205150071796000341802c0120b031481c084400d4100e1000f58005e00559075604424200080540d1025000d0b551651030218a00c2c00340324800012003d41102c20040e1041d600400c1000d100d1031070f002e100c507000146001c07000416441078140010313200300c415401d0b024403001001440100e9030703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 457947419 1250 457946169 457946183
    0x7030f080c1f0e031804020a0905060a03060f05010e0904060e0c0303042309090a03110c0d060c091a04060804080d051603060b130506181e19050a0b160c0e04 69
    0x10f4031440c103020040f1383e1404002c0301404900a80c1c28140802544a11625000c100d070503600461103030b88020040c182450b80da90042051410041c403250b08110300e5000354140001704060660a4803101d402c5684a6082000007030490001d00105081c10201e80d00154540000079021840d8200d202c12245000440b1680c000040e60540a01408005c143d42c40341041c2c0c0075401d0f03030000030b00c683c0a160114181c0420380d90b4000e00003003c00d0002010101c202c60880d1501050038001d070380121440c0c0103049012402c0da00c03801c1c40245c80d18500c5640119010000414002420720880f00c04940c411248024200031520300f26904424266042c900000040d013001c00000e0b84a504d84240c0d002e090400b01c0c4583d565241104101e00c42d800070305424003007512142e520f06e141c1ea52400c41b607101c685549007528101c41c0c0004010729980c6009032580343c0d0011007070030300079603c1c0c1c0b0300d07000151559294081c0d41c82c0250a07495a0285104000030550400200c0100b01c00800507041c502562044103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 457948669 1250 457947419 457947431
    0x10050d060f080307080a020a0c090902040b2209020612010305010e0f1c260f07030e1c0c0302071707030c0501030c0c110607050304080d02070f060207030f080c1f 71
    0x5904070500040307101c1c40000e0b600034040d0700e0204441a00030605e101450040700d24102a03541e80c0c0410022030703070103001410b5841c0001410350400f13010f080c81a0a00300c540301c40d1114003060707449021000407118458903989188050440d250706040b280080031603884214150395030700c2c00038003038042607551902c9400744542820240c1000150703085103160f0840e40c2c3c9100c45009008031042e50080104800c3c44d13404000e03002e000000c1c0c16070f65002d0003161180c2c41203480d22140107001d44100000403038041d80300001d1120312507000950380040d400703980751a03940d041e00707410308a141200c1034000c0c2c0e5042102a01d68a91000001807841c03ca91241e81d441007020399440043d01204c0014129801003001300c813200c1e0024140490752045610028001411b11509423a07852454000d81c2000341c0540c0580d0904c0c60060701080307120010500c01b09005451420414000d4441c8041c0c4401020151005190000c01c2026400c1d5040d90141d8001c0390222407542900403e2900f8a603140108185441 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 457949919 1250 457948669 457948679
    0xb06030f060106090303140d0f0e011d060423060708070f031a0111071509210f060f020d05160915020a02120c040504030503040b0606031308090103090210050d06 71
    0x209409040b20004e0701c5204040c0d241d62816205140500c08110000008001c07102201d40c0d140303d21041c2000b503001c0010500d440a0f0f4080c00c5800d4003080c41800b4443c0d000d800b03520100001c4550780241e2040d078031820106545041d0080b40001d904008850007654108500c080c1e00201861151815981c2c1e103580c0d01080200f40d0440344000c1e5040c442505c0e50252103081e5014484005030b9001c841c04450000f917460b2048449041000d07115030000d00403107070411400c00300c2008000c1d01b0114540d011f460130003030740d40d91051194550000f41030640704c034807a603084112039040c1c400700240327020203020510b0401040072500c0c801a04a070041140400d000c15040c0320802d0104691003590010203001c176058082191121203519a19080d104016085415071668040c090207144651115501c0341407901e03049142c01001004103016850a008022002c031200392100d8880b60014000399a4600e00001200034044a94029400507405c10491184a0303014008281000000408120b001d40310 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 457951169 1250 457949919 457949923
    0x1a0d05071403220501050709051e091b040e01030c05010f0f02070614190906110102070b010504021b0a1b05030a0210050f1c0b0406060c020a0b0a0c0f0b06030f 70
    0x1003659a5500042c8001003c84504040c0c412a001e01101c00001442c10341c2c3e02c60742542c0c030441e240300005d54010410001800c1c040d4941652200c045000d503081400e8001048451500405540107200c0394070004c225000c00703008860103040c075440702c03090035038403400c240340307035004901c034050000c1c0c4045548914a4403d040d185450034850b40980941c03881c1040c1100c240501218150595030100610090202c10510f14041d42c070054451010315880d00f50054003034000340b1200d0ad07c61340100991400241103980c03035410744000b02e80050712402c7c0a00903d6a0851a601981051140c00b08007014848455000101050300c140200311964032481890389466100350000c0d00010304040e0b110700c240c002c401901c2d42d82001c0800030705000a096685400405c0d00d02c00030195980c4503414996420f060190102405d03c50400c012038409a0340464408100f80c07195603000b41000c922a0f400301c0c46004401a5942c0102c18940f410440303081c400c2c0c0e030300030a440f01c41c46845494041c034003030100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 457952419 1250 457951169 457951187
    0x11a1e180915090105090601120f1b020a0503090d03090e130c0f080601050402070201270f060305010b16030302040f0608060f01090501050d05040302160321020105011208090a1a0d0507 81
    0xc00380100c1c030300364071700401d0000b044805051681030208980e0310516980d143e00c0340c400910300d90500859608103500c1c412840c948425216030441d0400d280b2000440c50001c115005c6540c2aa00c60040310a18107080390320b17103013540000c490301048200384503403021401d8800b080c182c00b0f20007555119079507031007014103041e00740f10f480700035001000100070502e801e6028141003401814a040c600380300110190b4014484a86a2140c40a0035002e001043e0842e0503000170f0040d44c1020401e5504040443c1c0140c041d49005000e80100010300104042c0300344c0541c0c000b04400b025804006484100c00744c00144120f80050140d00c503042c0c1180d02e0f6214200c0e000444030180c50349460400c84903121070146c88000c0c001d4003503204121300308003000303406401030000b1401036403c00740e40e14003503015152407500d9034496030031a0706100c0180150b15903403900d107a4440c1d1200545d65242200c0e0007042141031264000c0001004200403580c008158000030141621400030800c1580c2d2050816242c1c00c0c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 457953669 1250 457952419 457952461
    0x151a011806020a0f060b0303070b07030b180c1b030c010b15031509042108040213050c0d0f1404081c200d02070b04060204080f06011a1e1809 62
    0x4402400c0341c0204d0703110b20314040c0c064040d50002c269814003402107482c46d444003a08603620609642008005903051041001c01c040450300a201e0040e030f9410484103a00280180080002c0010060100c4000380400044005140e059940f601182d404c0b0900815608001b01e010f0342c000180e4007001d464010859125910346140c4021400321031050084424008204440240c4030001c8903020038100d180c4c0304c075000070b950f90300e25a0349424410f001c941b6480310490ba44060030002413241d80c0e031190041c0c84030321040b2100090640040c2c00c054010348034a107003000c03081d2205000d000501400740014440c0f00440c180580800c54800c0801080780d4410f00740010503c81c402c004400d0350051001412a1024610b000d0f013010290748403290500d100f610100c50380d40d4000f0741001f192105101d481181001d0740060682c0c2c0d8503204140b200102e04e2034121103000c0000030780004101c1c41589201e1590b081c0c5400c0c6860b4045520304a01000750000b040744600f030100002841025220340c0d11001031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 457954919 1250 457953669 457953673
    0x203010608070612050118111308010f0e0a020109060f050403020d0503030609011d0601030b040905190c05010203040602150a0e07120506161209080f130e0606090a030f151a01180602 80
    0x144402c43c40c00020703d901078804031302000801c20808000c603417886d01c50250ad91300c0000958000300300444c00072039400b02c5400703115410178041940541e80110b580d8048522900b84030016040c80e1004449900c103a8100030f500290b5100010144072000000d14861801a41c0001d402d988880d007500d0f0111007509000c001d03a1940d000125194481e41240c1240f1001408c0400c4100c40d65807041c0c18940003941c01481c0c1068903600710f05110545013144011700c0280040c40c606030421400035181c1c04c00310402c540e10104400800d0140b1403a41c01006038403d00b005861050b40c4940525403a0303550704400b07494a104030004200303418642140081e054480e52102008c90b10703914400f40181c01c50319419140300d070050010b61404107610300185600041e850001c041507091510401c443c0102034983d501521044c441070016840e200300d0201640d030000d5100220030080e2800010f40103c03030701f10f602c01034188481d0f150291000000411125801d1700c58001202c2802c5440e04603d5880c840e0800503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 457956169 1250 457954919 457954949
    0x51e0604150809160e07050a03150e101413051005060a121505060a0c14120a11070605031b04090c05030105010f0810090f020409023f0a050c0702030106080706120501 73
    0x614020300051888c00c1c3c40d4207002c00c4544500f19002c0c0c001d80160700c100400ca55003030411040b00408170303c0300060060194002840100308011800c0380c45010720f0480c1c081e50700e1380420440100c41c001d140040c20024007466461b07286810003410300e40754844110764a410b225805004800304002031003a41d42c050301e120b040a103244011105201d11410541d1012610455101419806c0c0b04c1c0040e2502c5940310709944400c1400c1c0181140c411410828107500309a170b007841100c0d4400110303900640c0317044003401d191160300710094052240e944a2080c1d10f260081d0341c4034140d04000514101c61090f01c031101042c174081d41c240c1d011401180c2d201d10041c113088040c0840480c56021a0011694bc4801401c02d0b84a00410f03007280c0c410b11030030410300c0c52070000c480070b18406065440ca4010003500341301c442c1d411180c44850144068540e6203450b440e0320000d901c40700040c058075043c54004000f4001139039581c00b500d860344054082c0c180051401c0007106060341a0340207840c101c0e080d034001e844e04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 457957419 1250 457956169 457956181
    0xc070201050a2703050601050a210204021e18090a09210c08120906070f090506180d061a0105090a090b030a0c03060c0e0a051e0604150809160e 63
    0x3000314150f108051006102d4511003241107555540c101841c400c40003403000d54142800c22150954641c4000d04000510010a4a080707080341c031324810690541d405601c41c16030001481035203c002c520b0002514012030700d00041c00e580d10040643c0c070001da07800409511514024825113421106c09404c0c0407054948041078040e428044134071001030729203141c00400b40c0e030307845840b41e0015600b056101d085405000c40484184207003508441c1c0c83c1024003c44d07680c080041d01e003013082d100b858898400841c41c065250350b1149103988200c001416160300714254030b05840104541d8013148a5806a942190015409002114003600d0000c00f801d048a2800310380001400c0c505a98a8042c002c0e140f00d8000034500111044c040d41c400c0034041010101e4a10003000e00c820414440e10440d00c0002c10400c60b143d600e00c031024500d0004401d8800c6000c603000c031f507052040d54842880d551701603a0f204071080d07016615034011000c0308180d42c1110340c00c409044040344a40124600d01d00e8010100321 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 457958669 1250 457957419 457957427
    0x21110f160b1908040c08010e061807030b04030f2a05100614130605030a050a03030e120d0c03150f080c12031234080f07080115020a05010219080c070201050a 69
    0x5401172280a02d602d500303032240c480d50300b511040c008600003135100406000310328039a01192403885020710b0040480503d540c803000d1440c10082d10181c20301c00360b45c1d08070404c544a03c9286919584901c1310300d840e4540b842c0b050b14620341150040d2001d009a040d86001c030301c07040c0a03c0c0700302c5111081f4500070b0044641080005034249030500800d41c1d80e48000550f03904e092000c110194090000740c004400d040c10080d040c0c9020310007510301c80c0c200721100000c00d048101038076400c040705203000410080c00b10080d401003a54000005400322035810003c1d4200b600c5150009803406282940c004101d08405c2c40300505003641455440c1c0c1090040080b0f0704800000320340d001464044890300b00c1e40742c10910340401c00c1344044d021070480010100d11099040405950010004070340003410303240c41c500003040c2800600030303601d84034480003500c0c2c1400c1c42006031251042d000002159030340030315050416009605044000480e03846000910884440d00580d0007640e0180c4440f850040e00707941c11a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 457959919 1250 457958669 457958671
    0x1e261c02121309090f050601060c05060429181005042006070c08012003161d061b01060803070804030b04240608100921110f160b1908 59
    0xb144403280d039400101c0fa100307800f5240c0e45a000d030300c5000c4000250309100d0b08001050700310405100b000c400ca20006040054469070154026014803020b44509529140400310100c074904820030290070701c5140c2110040b003004c4090200100c41401c00c4d01403c00d42a1001207801500307010422920002d0342d010b00100d0300039000002d05080c0f40020b169203294110384a0340180c0901c0e99104409068424000356614680c004900017a0644c5003d4542480c01c807880e804141c108240c0700c8d0f90180721500e0b14054100d00e0002005151100d094503140c0802551480041b51b0540c2060000502003402000722541c8039044001d0a00c0c090840c0c0360044150400350084a414500e0a90940f10400c6d49c0c081687d0003201c000040307071081c07803d40000d2038480406c07400c420103481c2a44100014503c03c0c60400c184010049031010045140701c01d80309210800483d034501d004600c90b030a905100820991040f803002000420480c0d2a641e00701d01c5402000301d006080c2600100c0850090300440040d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 457961169 1250 457959919 457959937
    0x2315090f12070b150a060c060b0a0b090415091e060e04030f080c160303020d060f15200a03020607020f03180613050a08011d03131e261c0212 62
    0x440180340c0134102082a41e141a4002c3d00046c2d0103002c200e0400001340101540310f41e04468620100d41800a104141d101c1c000009106540e2130b8050040e0010399000d04c0001d04a5050403c503444e4080e4541180410400ca0071000c18545a004100c0d001d80500c90f500079609941d03071140c1015003000070b07a0400000707006001c400d032052051000c9101030801140010384a0b940251f10384208a244c0c50036100c0380c0e0400100c504560030240540d03a01013140029603802c510b46440c0707051303c3c0310b50748101005d4902421514001c0b00310040c1810380009103035010349615030031950321166412403552203001d1500f075140e5060840c0f41c002681e1800b00e0241c5154580200030001090f0b0b941d0000b24468540d038040e1810b40d4403001c4910800032050078a030991640003025500d000c044003401c0a90103440d015041440059411051035244081e06110181c9403440806022042e05030a03519088400151410684038420025042d0103000c040d0f0082c85400b9001000d0700310520314041d220707400c21115 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 457962419 1250 457961169 457961191
    0xe0f0a050d0516081b060a1a010c060f14040b010e10060c080904050f070e040209030d08040804030b090a021003090209060111120f040f0503060c072315090f12070b 72
    0x90f14001c83c00102c024078000748800340043c1446a01400306083c050000d01e018002031408641c0692480c050f842a1102031091030602d039000710a18015004020910646500e5843c0210b4040504401c50445020b103002d01d2080315a680c0c0e5842c3c2080043c01212418080a1500000c0100d1400307040030340c0c1c9181c45142c2403800c0104400c0410211201102c0d01002140d646007403040080d00088106d41c0104147c0e8290310309004800426a554420650502040907543c002018000c199040d2005036a002c00d851485080074130704259188070b054816446500c0036001003480030b001c1c3c0f05241c034a9030701400d1070080f40c2c2d0741301c0191001d10004802034000d00540f41886139040c1d64000405d0500c0040d98420b840300d00f403045050a41c002a08154000c0c2d010b1000d1058209100c0c041c1e40720258071801440840c1013050441d407444110034003019031407280501c100340c400e02c9640c4e02c40c412141002150441404030300c500340c0c4c560030450300c0f101f84a010840e1202042560010580c4a03140000e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 457963669 1250 457962419 457962457
    0x160215091b191a0f0a0f030b01050a1413080d020106150c0b1308160c18052203170408030f0c090d030c020a15020303040309090c1d0d06020a030e0f0a050d05 69
    0x1444c090b4403003144840000d121b003c040403195010303c1a0015060b081c60480e0a0030390b0310390b01030454000280c0e03105280401240c54020466441101005856a2016940318146222029019000b90301402141c400c1c203076a9510b1003407152035444482038000b84a4180c030b89070807003000d00c420082d100541d0049000c211045649500c20b0300c0c200b07810302c00d450032803515142c1341c03060458113007090b094801c190400781441594403914550606a132421f819507164001c2c18a81503461000800703440c014000004100024040b0500185102c0c0d42c12408030140f81d0f41d010b200e60864407840c0d1066a000c00524107100229110300070680d501d41c4041d180014864840c200440203940003030b044001640300004100030140d20078420001030400000510001d18021005062400881601c403505808000032000c40e40c1c039003000103929600140708655032219000010090901c3c04161441d83c03140d10002c0c11002d50001d500c83c2e0042d040f0004d81101c04170007208035010362103002d40070b903552078401c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 457964919 1250 457963669 457963687
    0x10c0c200a0f091404030206070f02030c0a0605010e070e0303040b0d0b1801080d05040e070f12062c010b0706090f12020a020406050414160215091b191a 67
    0x807210030082e15140c240381e02074500c0e00e1181c0b41611501e68070381e002084036409000020340c00094682d00220103040c00740c18825002d10483c0345000c0c61919000901c075000c420341c140300496100c281a01c8060074814981d81d1400d00035a0610400b02d6480e8156104202c10010001503002034001c0644110000c50845070800005103e02499000e80250a2102d401007040080801203500401c41c0b41c2005030401b0703d0004032003030000d002856082401040354000f1a0184115002e041098100c1c8080141c5030b100c0855218104010100030949001403005030122400034005038100d58100258074034209459580c8409410300e404100d8510302e61046080020705081c40895200210b540185045102c0c0d00402007580c40940c0f089026621786001220326844242d01540d00015050744502d103079174801c030200c1ca07110300032403540d10103141c000500c500c903000801c20104203d0741c45410409207010808109042c003421072010000a2803020411a80740a00c0c06500b1214a6622041c1801901 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 457966169 1250 457964919 457964929
    0x20a11010e0c010201150e07050304080f03070206060a06050c0c0f0f0901090218060306030a030f0e030118230a12020705060f0c060a0506060a030510031712060102010c0c20 76
    0x941c00d0345042d0300401c0e01e402c0e05582c24410514801c82c4900031080862a020a00c0e034524009400382c410440004001030034080754200f10b80a219007103008543d24a04141e0094030350030706940e00c03403180007070401c000ba2240c4214103a5080300d40b884080c1113425051004c106e8100440c58225800034402903a420007a91110005d078001c0c040c0710b2000d030b80c82042910f507042c0c0c01c4a0100a6202d42c100703005114160714009803180c065036060800303035a46100e80d031094542907592000c003941036003805031070703015000c0c648070802c50039215030742c0d4070382c14000c1c1417110304420f040c141c00705403644c0030740c082d0004201e020788048108038090064035682902c1e070000c295507034010740c8aa50343c1c003c0000e641d580c42404101ea1a03002000c04c0c0104a5401c0c040c0010742c0380d10400b006e138001c142e00c0304046020380014908240041d0f038419038200c1d0304200d0086d180899084806c00360034552580f000a0184d50043c00755a218800c1d540e1048100c82c00b0355200000b1080050302d95400098820030000b15440e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 457967419 1250 457966169 457966181
    0x60608030301060e0406061202090a0b030c1c0605033d0203250807050f0f1204150c0503060915030609031309091736100f0210020a1101 60
    0x402460707481d81071801c050810400d101850b40294035140d001c00909601c81c0a40718117a1032044096520040100001c11962080d009070034144400400d012a000091008041402e81582c20f084c20045600c100b90071520a441415055005220000c41071010310880649110b4402458503e41140f02e181031840076000390340c45102d65000003440b00c240494503c51243c544807802c1d2402e0781c1030b46d510090005030050413840a0200100f001350041841780c2c15191240907100b2625110f544100c8078041481069800755030421900c0d254002c82d10f0103014484400d915500c40b545103481d103400344861400b00410f81a0022111104c914007950103012180c0280303145c0c00116140c1d207071480c410280ca401c90307004040040c80c000400000801c42101c3c88820800944602c2e140d8200480880032031512141c1c05881541581d0444128048081e440a410800703071003141020a140f00c06440402e0384100c1c120241e0f1001115450454441d001081d20040c1e502c0c0a40e0070350700c41d01c481425151 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 457968669 1250 457967419 457967429
    0xd0302100510050901080d0207061b0f0507050108090f190305091807080106110c040c0513090509013605011e0905010f0513080c03131205010b0312040519030606 71
    0x801d480d002c20451401342051409040d00ca000381011501e5010080d46e21a40707840380000b480843c9a540c4041c3e00154408540a034104400b50b010070170718079100c0c2d101d0070359008481c081480d0b403001c1348001100213086c4d02c0c9421410010040c07105a0441c1c00c100408500046080003001c000b040d071503460352940c601e4608070354500840d25045c00600a000e074001600048200414000f0840c103809000070122008003003900c0000740c80b03c4e5900300316014841c00c42e14000381060300c100000c40660a5000d184603984010003000601002104003840c2d0962080780d10072142801d00c055065101f058001500c148107200004071900484040e41d034480313100c90f101c10200c1d40ca417412401e200082c06850000d40345002d04001d00e00e000c0d414100710018541001d444594007080c4800c1c402810800c850b510710300c4100da15134060b035034032450f800d010311204101c80f15400c00d0031004140c10001210200980b4082d9120b08003420702c0c090100520101c4055503220888040c0040410740c1c0340f00d20340240c6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 457969919 1250 457968669 457968691
    0x2a0d0602040e0708060402090a050904060207050111040602010e0d05040608090109200103060806040308070c03050919050415050a090207020315090d08070c080a080a2a091e050d03021005 82
    0x4600610701a04c0c5580041c4514001d0340100161822076581c032015405685003141d03410007507102c13410400b009001c0c40100030015860324074002400e8042c600640b08440c039680c024007040e81030943c030a48a843e00312110012070821321040c001d19001d43d418940c062214000014844e40e542c43e00b801030010005150385200d00380c260111310b5640f42c00f07454060010a0700512141c142075400030a240700040c6000208004280740c0c004041c0300c1d404448100e50300078072481a81855a0307440c0503400c0d843c800c0d940b0440c43c10030003450240040740c0140448100412503001d440c40e001c01d070006544498000caa26002c0d00b10100d03420804241d0540c060b9102d0301c001c291070408240c0203001c0c880c0140c01e00042c0400c101040e0b000504100c1265046591460a044143c644c3d800c81c80140c000a0300d400e8001c401404c8240d6000400802c0402840c1c05135580c074001a520034074038801401d07403000c000409140c1002841641448062020410b100f40b04403181d06895614030001c86100740c030040c44031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 457971169 1250 457969919 457969921
    0x60c0f0c03060b0f03010615110a0b0408030105040e0f06010512070e0c030402040c0531170a0b1303020a08090a17010b04051503030d051906080309030d022a0d0602040e 74
    0x4d0812410038070302c1d040164003c00426041c1041d0240e8003409046a4040004008080750002418016007100544c03120320a11075082034909601580c00901416000d24036018510b204c805000030307035256000b0044081c120316400c0a05202c6100803445600c8a1031148580000f011604404814841c8150b004020740b60300303040c4104000e80e62420700803000c000d0144041d101e05001e14002e8024005030700110029880e2026800c00f006015070300039406449482481c0c03d00200100c2d955900350321032503a0b00c40564a00c12003500d59560380d400500180d00030314400c0b00140c01308000781040d6400504520110b5514010321741294a40c2c0c46050a594650309440d00c0c1d07050078020349411020384944425469018030201c1e9481c028092409a515103c0c4085095243c0d02c10345110107461503002804040c1d250301845076a58080308c2030b40d02034070401c0c40a800d0144081070b4191041800503100c00000d80040c960b000e68800d032040c8a5106041d000300c08009105440108000c10a0706444212 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 457972419 1250 457971169 457971191
    0x9090f0312010518060604120215030106113f0c0712050c040203150f040603020303030c0c1207080a050d020412030806030607080108120703030b0604080c28060c0f0c0306 75
    0x4424240300740d46200d40036540034484540c1d103403000e03107040d08c4104011026441140c00090340c5048000c00c0020381d0200000040303041c0382d01040d0141500410740031110b100102c0c1c503001698440a0800d210104410014601c1c0c1c2d20040264a60b02400c1c0c1c04a02c0c140700c22116124106583c951183d00e69854203000c65003088014000110040001c03a800c41c11403400c14412004a11200c40c8948140041c140c4400300356543d40c0f1500245130040e044a03128030700300c0003242099001d561070011521030140b001140c00f1f6008120b82841d40d10466107803d00b802402d040e030361a004000036040d019001c1c0004111407060f0501d18000502981d02c0d0000d03410100149030400d034000c6d10040c10403581c1c0c0010b0008900000b86480c0140402c440c40766203100c036003030450003001b15290300c582c012000500080c009100260031403c2c040e0484607807a03010340d0320074081c8130700c5420280c140942c941d60100304401c03070182c0c0c1806035060180c40101c600040300d81e104140000f694008503003e950b01c06507221 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 457973669 1250 457972419 457972429
    0xc2a0e0109020405010503060d140a110a0806010803070204200a0906201c0212040b03040201030c08070e04091113050f0907080c1e09070203030a0c030501060e09090f03120105 77
    0x4018414507404500d8941081e00003001c2d840002c06980c001d01c1c0142d03041003004010342600328100d4540007512082d022601c2d02548400c0b941e00824440c0d9400d02000c981003501041c03060407071350440003d51502c1c0060782440090090500d0f01144c11000d010740f0080480c1d907100400f030101c10b640d5140181070600304040e05003011180d80100300f600d0646400d103200750000c0c0c5404c0d0101d4044450110040d450022440c02c104015030f0040307400c0100c0e001030034440503405580941d00c01d0700d060017000392640049030400d030102c0341c2c1c00009a1200c40322815003440c0d400024440e0040e500c04495840f00c00c08507001c2014484640c072001c1d41d620030440c203800300364001500800b01c82c0152011500c1d081300c0a540c0c5c1c50a8140303034230400707070540f03050009024208191025040949000d030702e4a0200c5019469800c2155001c40140c20014605411882072103404c2c10390394035465880e00c01a0780001d0100c01040200380007000d100c0c40c0400c00c01d0840070405440308044030501007500d0741c103100c2408 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 457974919 1250 457973669 457973671
    0xa0507200703141e2a090601201f18080711010905180714130303050c07051507030e0a030209010605090d061d0c1009210b01091a0f0108070c2a0e 64
    0x46071381c0401d121201410340d10914040c1d0000401d00c9c1440401128000400c00103c003614075030250302c030300c0b0001c1d80c00480342488805842103e076020044410100900450588883c00060ac108410884440002da1300880703544000018500030b070800342c680c40812002031080b09210b010601c040c00b000b40065010106144a9a6034401a810810300d8403002c1c5c034905480c0402410321502203030044024104100c20801890000c0c6000170b2809903007007c0c0030a038403024041e0300240c058258401941454091501140e0740680000c4e00780e0720f412400c0700c0a4024003816a030108101d040080820030a004e800a003803003007840840d405e0a0380c020039181000c0c801c4418010440020000070b01c80e080b044005c212445100c1c017083c0800c2401d400c242c2007807814030003005110440d0000c201150568403000d84000b00075240845c241144041005c40c1010404150000d02c0395000544458404c110003c00c40e0b1040c0070040c6a0450b44d446848041545d046144664202e07000c00c21402039000c80072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 457976169 1250 457974919 457974973
    0x6010e16021b0f0301090203060c07050f01150302010305060409140f2e05060102070e0f060a050102031c110409020409020c010b0901080d05030c0d050a0507200703141e 74
    0x140540b45414903907248100088000307510031a01038401c1140c80e10b082d003004580680c0141600d0240c0351003000005990040c0c0c90940c0c140c4200e40480d00c5603181449200049000f0909501c03000d0300e141c2c0110007800c40107089a801c152512000b0340000e02c0014000c40301d079112000703020040441121180340c41009101c6aa1407042c402078064280b10300c215802091031450303000704030b0742c4e41c403030050703141003030170b0b401307640b10400d03081c20410170a10440313969000d0348040b00d0502c80e19a840d8012a500d00810718010300c1c4204074101d9440585669110382400c20740c2c000e115062035500c1060740100d811540c484610240c00244c990203c1e00284250611040308550302c259035410410050341c1c0f03195840a1005101000021407114071208003550300c02c241141041c0070300c2c503002503044c020b840282d0359040807071144080794200002100c070325015444580001e013038841c615151703071107000645201140035008056641c01c099a0550401420551182c000c240e82c042c108840a03c5500d0101c00c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 457977419 1250 457976169 457976173
    0x302040f0b0607061109030d0201060f0f3501060b0706060f030b0406051e1302030d020102031501051e0f071a060d080c0f0708071e152006010e1602 65
    0x70104032556890140c4100c160001d0002030a4108070006451922850812540c14031494009480e060b50540000c025243c480202600700c1e07960700b410303410040060181611085100f820703915140c1510101c1481d001c20241512140c1c07003042da01d2400c4030019000700f803c102000480100344401402048000c008039602410054550303101c3c9610010003900003030800b5100c3e030206001c1400c0c0c1e40c15200440c407211213101a4141120b0035941001d01040490190103184400c40f5004d00600c2500e02c0303043c2c1d011000111000340801143d0707552010f1210b20741e58a2040054104181e00e60103040c90215140c9981e070742d611541090300c10644d00800010062000a04000c900d0f2107001020024641c0200c11940368650701d54140d080035140c0b001280a4440d01e800011040e2000603100c0c1107821022145004106205d00044107220234010703030130f6402140080b8540d181c4151091002d40e1031200c846c2c0348510b0011510b0b81419000e9010100680141080c402c400c90344051828100001d400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 457978669 1250 457977419 457977431
    0xc0219081b1905130906051029031302030a05010f0506090a1a010e0d0501090803191506081306021201031203020901080109050606070602161a0c070204050a0f0c090302040f 76
    0x10b002d0480350314010680621010241200103190580201801a920440a1000b40384c194804c4580c1c3e04caa10a1f10480b5098000008121070049003400215a03050452440c40e45c50200d81e41d0b01246003e02260540304041e00400032640c203124071051203c80013070108503030a01000b0044003003809449601420320307007000301c00401e00c40070307128591803000c0c02c200d114040e0000018034a82e40700038000d0015400d0119038030070040b00300e005521540311074042ca00c02100801584003151a44000d002c21122425010704c0428001d03084180e000b54402011200c60140c2d54421003a41c1003c0b00040207404424014010011104010f208440f010310f402c5003440c601d000001c08111041c0306020b0030319612808241c0e1500d44004035400aa040b910179981c074000c86991050014a491060340d421400d52150040c104448100900503400044194182032086c1c0030400203100c0038001d200d060380c2d12220b1b03e04281440c00785500098840d00c0e1180318510b14010301040d05d85101c1641c0d4041e24002c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 457979919 1250 457978669 457978699
    0xe09010c031b0207060e010c02040f050f0c07020604050d6911040903020c0f0603190b04060e01060e0405010602120414060403051204090623010c0219081b 68
    0x1c0c40804440c086d24004414400d51801a11890720502010f500241001c0001c07409080540007903008104200202030b41740d503205003020143c001e0901c001e620000c208401c01c2a864130780896490280902d800d0090740c042035000030112594000c180544000c5814180f41000c00c2c2051048144125510402c20341d11301401c40980c1d5420100381104100c004c0c84039001e0092520b09200ca50701c0151003040a84079038200650340b441c600c0c403020b00c910510080103000b42810019a40544e8802e4000001800702000d004003401210068030b401513039949002440846082410b4002c0415854480808540a003400705940c0c058009400b0342d407040b045003c1e00400d48c02144c049816003404106041e034032100080047c45968030182081c032070000740c20800e192000c0208112000303440100089540c2e9950651000e121009a000c003482d80040c500495003c0ca0440980d01c0c4010f006a080808000a40050502c5600100c103103520a160003840b500c050110b2802c1e0780c60884402c1c01141b11a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 457981169 1250 457979919 457979923
    0xb04032f0f0d03020f06071d0a03380a0e0d020a03090b07150228140702040515031b010f0e03060a0c050d02030103030f0801061706090c040e09010c031b02 68
    0xc100542c0101c01d0007016906041c405d100e1901c0d200381c0303501618058240000b004000c05034501c000500c50322111008030651600c04509400c403a800051604006aa500503c074441a1100c011721656801506048049444c0540f288109001c0134001101076005140504d8480440c01e201c0035940310321940f001080d080b401c60822200000746069507460240b0701210564103049141c1d030000d0000c40d04c100c410103807660402000d0b89640340001c6118102c142203e01d16920070f40c560000800308490700150411b0342200764800c2d031401510407030304410b8003c24a0124089409110b800b64065280c0c85980d2015a60158410b01c1c64168800b0382e20700700007038a940004d0100703011183e64a04440300c090140b42075800c0300450a01c00c540701e6a41e4200901900d85103203488002a2510002040c0300d030248031660600400e4030440112a03461000380b002c0b2041c040d204509020f014030001071001d0802a10074401c54103180046a51055440c01030242e8407241c5c0c1901400e03d114072152034007540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 457982419 1250 457981169 457981189
    0xf0c0f060212072607050d020c061518010905040204020c0d020105060109050607020105040909140d050705150f0a0e0705100c02030607051207260108010507080a06180e070b04032f 79
    0x8a0f044500c1c00e03191170a054070180310300c18202544034000b0414490764100460014814010660104013001030f800c104019034000c1c1d01030089102203c00180100030403030f4070466016101410040c642100c01c00394501d01084c0c40048801070391203004000b0156401600b9800400042d680b403402c3c070a403940060000d000314011224820390321440f00050002c061892454460420300740d8614148542008096034441c0310250361500c145050906141072a0441074428a01c030b600b00703a01038407040030700c0c0094100361011180c01c0c81111808103041e51000107220f0350b1032464aa1540c80e01c43c51050504010300203240c08248201400345e8080300320300c0b2006a51007503242c82c150364003a003410b0040051004114030507550091220011892a105500083c051b90042e2101c074116a24102c0c00410b4a441d4016556141d01a071007c001101c4a500f190110140c181c054801d800d0301c4e84110034440c0c001780d10a03191103030311614482c0303280841d075a000d082d4401c1d12460300c0380b0110000416a0468 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 457983669 1250 457982419 457982477
    0x20406020c040f020f040f090c0e0904020d0303090602190207080c09040b2211030f0726070b0c010c140406050f07051e010b010225060f0c0f06021207 66
    0xa11142c2001e5010080c4d411100446100120152030300d8850010381e038030039214018181c0c1c0a16203000136124600072040043d18090080014403150398035800d0101030301c4030070400c405150315403860400180c0103001401c6050700e0340d140020781c40d4000b00000d240154070b901c4242c10342c00c255003000aa44400a110340c1c001d0300040c00140c01d0325000c104400307400c824a5203040e07081d02a02840c040001450790415590002c5046500880340403242329100c1d00d0314030444c0c40840b100c0a104030101e1100036046402445c080070b0311025669039541c58800e03841000d0034440c0d0b940d202c0040140c260031046201240950050040c02c044c181b03103000c0c005106a054000e0900303400300d844420050100211128690186111036400950b582c110b4060315016444a026014084050756050400b030101409079048c0754460400c3e600c1c02500382c501505d2200d00004000c4c00c0c01300c036004036225404143c0fa0318070801c001690780d6102e0401030b88102d4007500344002c100350304080c880c4d400548130040040da9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 457984919 1250 457983669 457983671
    0xb10020c2e140f040603050103030e030d02060105090c040e010807030c150e040213050402120906090a03020a0b090c0d08030a05061c0b06130f02183c0409080903010c03020406020c04 80
    0x282000c0b080c0001070164880002420000180128007598903400c828100c030300c42e40b5034102081c2e001c020181c07181445000d80300142c2c040702c010000c920b084124640c0000e113a10302545056210006d0300c0300b41e40c0c03d801c081da0300e62103e10f08100700300040c0341d084020b10340c1c40b500351400d510032000184440901c9002c3c611032500030800d40c1203e004440c4040051a00a004541d00c01c988000e40000c0d1004807600451030042800140900701c02060703a000703ca030b15501812000c90b01d0740d00c1402c0800064400b100c54403c1c100801c002d80c030b4040010320300c00d00942045071640303080381d0040140c544c0144510f001c0c0c41c0c501c00c1440b0710010030003850782681d80035280c248641e444c1e20101d07250400800a600081c0e040000c4070003044003640c01401138120107a0140101b010b08000e00c000c8060300c3e900c50b003000c002d5101c0e00041403888011401602002420103509200c100009800c2d07440620007580e010200280360340d12498244581e0a0700c00040c1015400c1c103160440180d1039884414449001e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 457986169 1250 457984919 457984937
    0xb04171602090a0b0315063007060906120e03040b0a080f01140f04021e0315030f07140d0503071203060501030b103603050102090102060a09020a0611010b10020c2e 72
    0x55032001800740c08c01c0c07100c410350004900320b0344111425403c04004030380f03030703024514003c160b640c400c10b00c160036105651110b06440d070446121000410b00041d2460b01400184008140805032000034408007000e5503421096051000103403200600c10303403004014112042c04071800343c650440c03a08001c001202c0050700c60444030704450121040030072406030303020000104048117481002c6d034022048141c04690140405a100a42d240210300541c220325110700c80100140c80c00310110400c980c4501c060b0307820a00c030f07a5200495034a240c0e03a0000820b0300d0358000e000b556454440d12205100c01c54a02d24500250780340a441d58460131002030501355402034600106092680403048107850012500301a07a42c0d0408034000c1d00481d007180e00600804012902042e01c0b4014040101d40003451020030b580707400c8003035031a407031080f601c0c102c155241d07000c101455a03640c0151103160910b8000e00b204001560030400c0031101e1094501250710306001d0a602143e5402c520346000f5191708150080e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 457987419 1250 457986169 457986181
    0x10813050f150108010606050423011106040b012c0403110a05030c0a03030e0601140d1a0a05040c06020312040b0c0702030d03061a04120b04171602090a0b0315 70
    0xe08820071014040e510500580d003000482e800c051038100d600c084001c0100f079480b140200d82a1140f8407603101160a05641741f580307070b050001103940141050401d610700380e60500d40281460021281687e2001c080b45c01000410040b05c106114505140e0034200d10001b90b62007581c8550000d0030123400c2228100031035241d6042040008205900314089135191294900820f035a4201a501200024100354190005000001e4898180d5a010030b940203003501e0b001c18401407800000c0c00b5203c1c2c1404140b41682c1d00c03682e640907070003002035010101c0c280c13400303003080846101c4507840701d802c560007004032680103a054048160019032004601175107131200c90340c1d00c1490141480c00703941402900c105080341505503100004803a52960f85081c103600c4405183c00c5400b82c0c1c42011801c0c0c0306583c0c6030001409000e801503101c1d10600d810015480c0c8a512034813660843c02d8110282e004c940ca00d4010b51809201c4294030845500c0180850000040801d8807081035414480030000d64202107a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 457988669 1250 457987419 457987423
    0xc030e13020c100c2d03140106020f0f070f05130609050c040f0b130608090109060e0106060210060f0b070f0b040b2208090d15022208060601081305 65
    0x90340000c103015500d4268040d103194903100c80380110f000c40b500e454001d41c2c240340078903d4088400b40c1d0f850102d01000d60749071020319101541544134101565968260101c410795007499003e001141d000300590a00615141d10340800e0441c041250340c0a04000c201c6040c80c0070309001501e00503524100417040e90074640f0040e20342078118500b900d061400b04030050b5810310280085800002030400450741d500601819442510100034a4a2080f0350500c0740c2d5005d0320300503802c00c4408000080305034603034640c0030443c2c4034030380b41e016643d44a4004000705a4104545840c07012643c5040019618260f01c002c0d02070780610441c0440b05001ca003040606c034000e07401d00700168012125100c3c0b4a00f500d410081c40000316001c000e101c2400083c1c900e0110960017113070780c40380e100407400e00d0041e0040030092005c0000c00c0441d85141d8242a07052800c150b400500310001c4101c50500c60300300b1030f900b000c01203003040d00540d1050b401141001016030344003018680250f00031240f03403000110350625074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 457989919 1250 457988669 457988689
    0x71206150c0c060f05070803090a02031e010b0105040b1602010210021206011b0b07081b0d050129090103020901050c031303050d0c0b0f090703170702031204060c030e 73
    0x21590000300400503400340c211962452651050340c0124015480741420354600e0fa2207031550002440c148039400000711184021500a070000080703803140b140950010740745c00e00a050b00404004580f60610560800f4041c045000c002420b1050805003044080002c6018200d44a2540e00d031032082c42c420342e4002d00040d140442071080640d07960380c55550724440114141c8005000a07002c41303440c03040190301a90008006da000ca86150140c031401d4046650a1025100c100c64038000300b103030215000703050000e08903007140c0130010400e585405000c2c02540c0c02d0a0a01c9038a8501c10a401d10503505a005c50703200046c2400c0040c2c03521100b0004885034060180001224800040c400e01301c0c1d0202103400007101e11038002c5501845c6003a00460340d20840d01c1000740311148075000f2560720a580701640364070048103c12250480d03170b2074031040303080b92160855048258000552000f07605007480160080c1d02c0301805640307400e1a10760010907400191801604114101000030080e03a2881124 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 457991169 1250 457989919 457989929
    0xd0510090c0b0d1e11030a36020f030c10031a060726181c0b180d090e01170f0f030a09090603021f030204030501060b07151103071206 59
    0x11501d624114001c680242104240072202544d0894000e03c000030500511900030060525181542c892030755480191220741c911701004e9014a44c00b081000e0440001e81070a51545c0c205601700c80640103008001c039101c030710640690020503018059456060081404500314a00080e040100c5900b03100e0600e08445071641c406400154502400340b101c04c09640041c1007000c0542d4200044608942e0380700e01e03180d00310783d81d1041062000c0b0345000b41e00f010100a04015480803002c0703d03076074000d40c0402100d580300c1036040180c031601203417401c004181c0d14a44e107050045009007840d0200c1e011850501c50718031182c40740044a5544017061014000c4186402c0c105d8101140c85402c0b42d840e030300301100301e00001c5c2d558400050040c07414041e0710100c0303402a0170503501c00d0484288410b2002080015002d00d0380800000000500900c038a00c010102c4400998540b09a8600b03c141c8000b41d0b580481c160b030a00b4000d87c0079241500490f0340110444c148203a05040c8180d4420180545500c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 457992419 1250 457991169 457991189
    0xc031508070305031b240403080603010632040906090c0b13090b180708160e150a1e0815040e0c010e0103061e210507120c05030109050c0901050d0510090c 68
    0x150381917081b410a24503020360321940300d101c01e6a841c0000e0608036000c80c4188124611540d0404c2c010100c2c2588404041c0031804549811580507400b240c242c1d0045402111056562032000c820720092048034409889900001894800c14110710364002045000311446141c1d90705400d0119030303c0500303000d07488104540c2c00d885d61410b004083d040440456041c4403181c41000d907a0204c51040c5101c88d800c4000401e03101d860584104002c0c2c1d5500014562410f02c251000e001506110113048104200455510301409103090381401444030001c103034850145003800185c010b01c20700480e803400220720a107414a540b032107081c0100c0140c13469501c048000000c0d5026481c00340081400c1da07003a00e01090500f2146010041942c40040314200090000c0e00041c40900c0410394241414080c21301408440060f0b907110301c002400c5605110003103910342d020f15598410307820446515401003000f21102c58546401c3e4840c6510b45001c0b007502c101440e070300c0b40383c1c404116000740034101074905401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 457993669 1250 457992419 457992463
    0x1b2601031e150b0108150d060b030f030d15210605091f200309031605011e0b011106070f0c080d0603050a03020f0313031b08010c031508070305031b 65
    0x41104014030520f6115400034401c400002c00880900c22110158240035121002c41d40c1d09881d81320080000004040d03040c0580410191450341c01c101425a48550000000b00b202c4e070781610240801559010b0300e02c040b41c0a22440d90301d10403c07a10954145c02a401040a5481c159240c0c104150300d4044460424100b50300a07840050b0b90008040000c1c440c1d25a042c03100221000c40180000ca42c0303002c2d90f502c200a00c0035201d008041d0031982c00e210300d00201d00c02116140b0400c01a151f07011a40003e683c1c3c440c009655a03025250002c1901c07040302400c070b941403011009100003102001e107414054000d6141c410002070398201c60912200f50410842c0b42c0d00c904e0060344503c0b504002b40c0c010b1041c4511701e03454140100c1140e000b9550203400ca1003561440e41c90f102d0219146100d4010201e0300200020000802c4c02015030034800c660340003a0b02000712211981020301c6412541199000e55402d0002807030000440703240034402490704000c12403a1000034540a0005c40c50031900301110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 457994919 1250 457993669 457993703
    0x3090b1c06080d030609050f061009050901060302090103180b0610091703091302031302010807030e1203060411040803030a09051c052104020916020c041b2601031e 72
    0x100f030010b5100c8495409100782652a0f100f00c0690301e090f130382c8081800d0250042082407a01030314098805205080101c8600e0742d4000141d002d0000344c0c080c00210303400040080103503030700d48620900b51448910b100b038000c1c5e49031241c402d1400010b1990f40103104040034130b180350b409149104020b00e02c000d000d6101c0b840003440301c1d8403a000100503a0040071400c03204008800c65000b500c2c0300308409112800e0710b4540b07400454115202138641424995074200d00c2c000c0d41014050125807800c06114242d41c2c1c00c100c030a000403111340540c0c000035501b0a01042c0502c080c0801243c1d080032912401080c01000c90070014244140d040c2110703024024007020485e956048000b40c0455001142c0f0b1074814417111100019000003203400030340c80010f00307000403844e003009848160381c1e40c0c4520444801100c10303001f00d030880c2c00e80404040d00245001504009641c0000e4851400d8003034400c8549844a004102030741000601004000d5001e22600035010044002c40200484d040500310398484411 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 457996169 1250 457994919 457994923
    0x5010204090b0d0b070e010c060903020607180b09040e01060b0d060515040509161803030203030916060903060903020a0804032604120602130503060c0316030903090b1c0608 76
    0x34825010390303900740315030440585091010580c815410a503191304982e14084100c0d00314807100d4549040c000b005101002003034241c451075103040d1003a0020105414400c07005030840348480c803420195609818144040404e420950328044401c0d180803800d00fa5840c01d240c09042d0302c0c1c00104060501180d1507070124a00e4001c0011100c0944000c0e101307602691400b4650300c614020741d82c000c90000e01007001c2607241c48800140700c0a900d0042c494190034a00d01503521880d9000b5030042e403000c020b118220384c040c0b0a19040b681c200c0d1234555298a0311002410411103440042c180d40c1e903540c1c80b50b003494000d1000684166000c0d823105d5840380c903858855050b2110010b00e5416500f40600004407801c208222410f444c007040c2103000144141d40d030540694088142c105100114003400507854904100c501d00490001120315140e03e0300a0000c01022900c0126104150605102c5000309410400c00ca041c1c07518005000d40c0c07188260203888038440301c070501d528880d1600000080311140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 457997419 1250 457996169 457996177
    0x3080c1603021f06140904030c02031006050405090f1f0e0601090903030b090c03062b080714010c0c02060a030b030609070512030315220e0c01030b09070906081003020d050102 77
    0x1445083c00607030040c010003030040303e1660180c80e030006500000207950745404250300340d0040c400e28040c5a10040d81e40480d040c065100540c882080d01c0340c806100d94900742c00b84543c014603c8005000421100701c140e542c9075000d8031050242c9145103a82d08500d00c2e1900080c4800c04140c0441d08656950113141d03000304955601600001e1901402c66031914010b0180350042d03032900c0f91681152540d00030066240305900c0c60341c60181000b05402c1d158001e0b55a40750009003d000255110720442c00c3c1003129401c914015407043e4500b21200302010340049000c07041c103405075019030300c80038480010f80041070f80c186640d615100303401c2001138003800052482c0a0743c000340c8401192403d00380c4030641d680000d4800e000d500d9111540500780f420804035001039407a0140c00494900ba030349050760b040711203082d800c9503070b90051b1502903002d503014001c5021004068914030420300d000d4500400ba10540e008005c1040018000300d8102e0070400d012030301454006191480c003454510b4624001d40c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 457998669 1250 457997419 457997443
    0x61b0322051003020309060601120e01050a0212160219020f0d11030d2a1b1806050f0f190803042301030b010c0602090411030a0f0b1c03080c160302 65
    0x503600d402c04426038420300030380e8012030501e002000b9640381c940066800780c00d54038003074200c680d944c04490100d10090250394050746800f0001a030350716041103040e0440b44c004229045d072104211056640d540d000402c10789001a0340f245482c0c2140c148000f41e026040307801d02a80c800a111500d206024408050924a80c0c00b00c0c00c5a007030b02d81a030001d0b03814003034401e200540042018038030107101c07050510015003a88281c454a41489a00c10a00c0c40902181c1081c4002031110250702e586004500ca5800503100c1112402c404c0318001c0d0009106250628019000d120800001c3c111140d00003010005044982c0a0380e4465485200d85000250403d4014171f2001c031086180b90380303500070300c101d40301210183d48070044411185c035240080d600101195810565500040100359050390181d406103011703080201f801c040d007540d0541940c4862020a2040f007650310100e160202d500c82c04140643c1c541001d181540d550742007408a80200e290411410101351801c01c1099404603c803a0480 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 457999919 1250 457998669 457998679
    0x111e0f0906011b060e010e06041502040f1e0305010c020d08060a0609030f050309150405100e0f0f0307150e09100509011406070611030603100902061b032205 69
    0x496014104100da1806855080c00704005001006030071207010000ba5060b80035050206000e03640381000d40c2110300881e03000c0b0040c3c000006100030891861800c1e400381100036030941c00c00d4201a454801c100e151300c94000340d1001075500c0c55030001041503000046070001e000b00560035a50303c010b51200e00f0204034100054003000041d01d50310340806c8900a0f0b414554400b501c0c1e82c25039031908040503800506480c9444180040c81d41d0b0758a501c01c80c0502402c141034141c45034070304010b0011415101ba072207400d02c00c1e2072419420307035201c400408007881800c075100c808620404020a04010164018040c115500d000070100245c1203400401000800d8801480c80e0341c83e41c10500c1c8600450140c50f621003003600040080402d41c07084130320700d0396004014600e4201a0755071142200c0820004518950000c0100180d916007400a07459154000c0c2d000d200540745540000c48500c03a4107840600003003440c00d00c99a0344410026640071a02803007800c120349041c0f440d0603d0b02d4090b845071911034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 458001169 1250 457999919 457999939
    0x6050310051804030f0c050f2a0d06150504020d020915120f060f060c060412020307050a1b050a0e253009140c030a0308070804111e 58
    0x207003409003151404592820b80307a001c0b40c032213540440740d0313080200d440001c015036290740e030001c110140316010320b0410040c0140f146d04141e43d1035041001103508034594240c811191001151224680c100045501c40c00005006d01c1152001881c1c0c00160070054100340702082c1e425010070340f42d00402040c98101e03415400140ca5004e00c00b610b01c22a5491180c41d142907001c40c0381012084202e54011701300030003080001c11800d010603101e0f04039010f411030383d6214078244130a00c13100004030080c110b450710240d4a0f0070b0f5113848003543c4c3c1999210081180e4138858400c1c10541c00e0580c058040d0000425007000d43d0303580c135001100c002c0c0503684c04484d152000c00c0a400340c0c20012041030a00e0041d203450407400600d00700c003a001d11002c00c124414940c59040000d0601c0f60307104198004d071191a40a07070307086c0800140341c071f0081c4054030603000e40d00141e02d00c0c022a070015405580011586012099551280750500500311000080c0b90031031201e10824550b40c649002407507101805a50001103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 458002419 1250 458001169 458001179
    0x2130825060903030305090703060f050703051006022d0f030a0f051204110a0506031003170a2106030c2301030506061b0c03070905010e010806040b0c071103060106050310 75
    0xa00c0c00d544a054003041d400362080002a0080c1c20903640195110162085244c1d60b0300c5003400d41d001d100000000942c2d440400038007a4144c030072030780c01c0410f0780c2e1007401c0702d420010080c2d43c0380101c201c004018059108401080c4408194140c6041c003001c0130784a100100c3d802050b0f9031703046484144c021403404074110b80301501c24402d8419100c1440107450090300c80d511407010795512070728203d420280301400842e040e22074100440c01041c40d004e9038500186103003031005840c854260110450142048209129a4025031030760001801000d92800702c07501c40844401040c855000a0607800355904c00a003a5000346180b210000030392603110b407401c90340b40045003110403c4035419480401401507800301024882d00654132200e140c102c80c18031841c0d5000902d84002e6a02a9410a0300c0b44e0040c060008007500745401070600c0350003440c45003403696541c000143e0080074606125030101e1800b060145152814820350300280a82e401c039616142c00521a274000c98641a500300c0d0180d000030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 458003669 1250 458002419 458002483
    0x4090803091b0d030f030912261306051f0807090c0f0207090e07211e12030911060705010b0a0b09060403080a11030415170f07080a021308 61
    0x326100d0051103040786908654017560b1104010480004140c1d6a44103580000c0c0c020740080210704903516048072039400048010b0705641e0502d031600c811006030041c400d42d02e244684c1505103a40c0440003040d9556401c0c10030b05003c024040d11450b040c003040c00000d00d58070110b10078007030b69004c5c5402d02c0040e201b075105450340d0301990401c1006900c0301400300300f00051a402202d030806440b05580d1819513800c0614601811111400301442c500b030426820003c0d500c0131045010030348029190130f000d48e07864034889200004013501c1071640ba0288503082001c07218100003107040040c6100e0710344d16141406402442c00703500b018040e040a0310003007045c2c60007600750380c0004801450180b03440d0455844075215004003040f5000e1212007034110300c8001060002d400540241c48007400c010a4072240108409182d00024046021000600410f80c0054003015070201050400c1e40c0705840d1480541c000b0320802d5600c1c2d000014903140440c00c20008104a9a20007408804006003150f45081c5d407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 458004919 1250 458003669 458003713
    0x25021305060306060d0c1e17070e0412140a05131403030406120608010c020f1203100909170310080601150203041a0408070608040201120b030316020406050409080309 73
    0xd41c143c0c440c00005943e4a4203044601250303100f0f107100d820450313850010301c007501082054a403008903507060500c840314004030310a41e100c10b14402007100710f1800f040c801c841c18010b0000762901040403020542d0034054040c0f500752045d03080146644e00900742c4001e0860b0400302c41156a5010b440c03001408529488000524202c010069440c0c54503211b0255041090f01000c00c1031780780c65450009010000f07100f5607000c0d00058016140c0103101000c00e41c1819040b45114185030000d02c14020329441049034101078803900b0700c00181342d42c041d08091014580d01c2682400c0141c00104015005600e20030380002c4502e81e00c11501c00b40d072201420103818070000450001a40184000c01c4100d1141300360441c801a0300001f603280c0707612031550504107001c503080070000c60050340034441156842a10f030b100c0030f1308540c410070a40301c00b0b6001a85034440c1824282030341050411100c1596a6036001000034100200304001030f0060b860308070b05603001125481c00c1d5014403508010500c0d0900005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 458006169 1250 458004919 458004931
    0x12072006090d060603021002010504170301150318060504050705120a0f030e0a080a06141807091d06040b0105041805121e1201030203011107051e0325021305 69
    0x107030401c081c410501c00c2c02400b20100382c81d00e41d20388200102580701e5445203103c2c0c0c1c01640c00418185003606001744410f1a010b00405110f00820040080c050819034458040c0898900031464800d0012280c4418010b482c016250728a82001c1c0402c0081c00a6040200da80c02d031040c452461001d0300068440000035009080400d0b60080000028800d032000c2d503806000a2004207803036111494540341c444011000c607900741c1d9610010089500c1c002c585503021144070034280b4194140d104c415200d0065224848000d500c40014140b00c902c001c10b01404d030340841044070b240346080d003800340d8414401c0c803400d4001c03841c00e100008000781c812510303039030650404e0050108984030021a40d847c3e00210750404403402d542108101d4240140040607000e80d50800440c07254110300402d4219050445030f0207181d5010000c1c000003030300201c0d040d211240f1411000b0855090f000c08581584a003007080c154040805032450441918000d00315102d5000f500c10006038414080030008803030b010743d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 458007419 1250 458006169 458006179
    0x312041d06040612030509040b060c0a0b06060c0d051309110301032a06110f210708210114040903080609060d0204060b0d110f1e0c120720 61
    0x4034000e1500c408150395044480a040080c40582d00d824020b0003074281003040f030005400040000d61480c01c0d002c0c00c0054036084407150303d4824484040395886041400041101e003c010001c1c20940c3c5410540700680c41000607030b0340c1044429001480c941c402d810b00491801e80c00400b08128a0920500031400d2958103c0c42c0340d81d0a50300c0d04076900042c1d090b1446025207402ca9030b5848100d107002d040040043e51107144c0042d0664601c9410007406440414030f60344410300d03450300000020f0007101500d001e00c00b02d9584000e1418120503500c52080451f0910800b0201d00d1921a01d80c0c2929040741d000102811040e9001010003007595040c0c640030b4001000300f004112940323002100b0b65000790f00180b03100d1403500c250740854241d030107503846a000414003080c910301148490180384a08884006040d150075820290b1728001e00a030001002281c046121100c1c50f80340e21400c03140c907901108100c0d001c0352540d54901402c0e91044004a03800c020030004440e140d07203207800940f01044c000389 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 458008669 1250 458007419 458007449
    0x60806011a030901091b09050f07020714011103031611010207110f120f030c010b060403120c05120412030f021507080604090b1518040308160908011505031204 70
    0x4180840d400182a07150203550307500c286800145410621b00800103c00ca1664a4518121a2104841e40105014a44400c41042121160b404500b04043d00c4d94404d02c880c41d02150360048401050220804c24035200020030b00c080407114410215002c52940d503003228110481110303a0a034007a540c001410000c0c0c2d0641e195261a1407500c104483c04050204500d5034410880713907244c010541e0182016800004810201d03a0b401c1c01420540c1a0aa4506251074a56078a04210880b20b191900402a03808640010410140005d1a00110741c9490545950f01da10100040c8242c044045012418030038044140c20300100340300044810a14082c01c03281d0300c4807000d0702c454000620b11503203d03940c1d18001001400100b01c0034001c001c8800c0024a0711402404d010741c460b014600200c2c6400b940080000095112819950100d90200322110030b40c80000280d03081c40050300810440d500b0300c0c11460051006004034002c56004030200d68210b680d00f0040c03601031165000e00d45a07545a04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 458009919 1250 458008669 458008709
    0x5011407030f0c080a090503100b1503090102090a0306140a1a090903090a0305071d010b271206040209070302030c2502060a0809010b03060c1611150a0306080601 71
    0x11803210b10124072400d0440070003a180d40e8541045c0d20032400780d404140c0000c01030080f802d04101c60b100c05081501c0400106540301d0005204018180d0303032400078280040010603004007901a1010104007074002c1c1401e41e2280f070994007618403146a54510a80400000d41813a002c0c050004007030071003d48484003000160502003c84c6004116861610003000744608540341d141054000710b0040c0c002e07022040c00e041c5031242c036403641e090020784180a1001400410361100c2201c43d1100c05042000e07186039a607041801c01c481e1400c0d0181d1100b40c0d401140b990340400710b038080c40345100b203c86018607078034240e09400300c1c04107840c40b41001005000c50411080740b6100003610306006003c01d903190740607038000746480e40705201040006121100740024900240500b081402c0300300c000d003400d880d1a14840365140296010b81c2d0460200c110030405102c0d114040c65908803000e07010019a1145500c91200ba038092608880024948403001440d02000b0925505070344003020b0381c040002e501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 458011169 1250 458009919 458009927
    0x1150806100c03021c05040e09010b18071e0801060201050f0f010612140106031d0c0f0d0204090609110a0806010803030406091a01140111160b030a32010501140703 72
    0x4003404409500c00c045c0c3c40b03d91490517000041040703a8a540d410b41d29400d0905200075010f0161031000c040c0e040001c00003c9640c2d04841140b1602c9123038102c003141d50740d09001c4078054a0708684844241c03017000303100700d450b0303101c1e4195050f00d0072500284001c1d1500c2e00c41d60b00c0034508075108510310000d43d00510543e4403036140d01040c40c0700a031001c100c2c821000c004580300b20007039100602107070381c8800d0405400c2d10005409260700d02e0300064116040e64002040029211070081e62140d10201003980455540c0da01c010601c58008000b088041c8103441c18850341d008943d8140e01c1041d0300c00c80040d410384002a543e040c1c40f00b01000e1400d5445985c3c4110181c0410340e030072206011081c8445103100c1a0011460081085c0c8444d042d0f01d021040025000300e451410740903842e0004ca010080c981d04500000d02290140c0e00d65a640b0369840c0d010314014848101441c0b41443c08004914030700340d402d0400b90780c0c2d02c007160302c4ca051a40d90b500103403404221300174580c0390700348140101030100e801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 458012419 1250 458011169 458011187
    0x70605030703020906031303170f06010c140105100603060b2803061d011e080303070c05010605030109081c06030f06020904060312050c0106050108092505060705060115080610 77
    0x410300b00541860320325000a42181c00071107180a02454500082c000e141d404901d58546500440007000d03141030940c100d0490000046c541c40c18001c802802404000b4002414040040d40d600200850304014482c00c00080244c492107000a00342a400314580700c4010440e485480c504005401c2c1c540110300d98080b0713142c054184000d143e0740703420000340401c0d1000030340e0200c445280c04005940c1404002502812051200c2040c045044d0040c44190400001c423a005800350400c101c00c0403040c40d00034090601a001140c03d9420700c1100d10030016000050700d045a800c460f9048091801d006910440b045444003922548000d500d0401241881d401030041c403c029002050064483d2a0b0f80c007040c0e070a049100000d0000110911075407020b10482c0040d02c070034a0280700034100b03010000c3e0f0303428400e081000d00c40c481103040003880e6000c0d1700e950010400035180645520131804e0a41d01c4807024421813811000061019144511505404c0c0c03240f40010840318000680c0e02003200c0010f1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 458013669 1250 458012419 458012431
    0x30603060a1b18050406080703061526120f18041103060108040c0503030703050c010507140f1b0105011403071505180d060e0609010605030304081c091802090a0b0c07060503 76
    0x4103440100c4c85481c3c600911028040c2c03c001011840c0c60f5150000850b0300e07a540c248036030034070100c1c14020030b6207801d02c0c3d0880480310103120070743c901c142102038103000188040082102001a07400c50742c41c0d9100c06001121004015003004a50400500c020b440020160081741d03801040003d001d0b40c02218900e810a0041c2c001c28609600d4002191460780050410383c0898004544410f8030a001d000b9a503100e01e841c58074a400180c0020710310801d004148607540c0d15036000c58242c25400350b08541c580950304031002404035594a007500d410300c4c1050311205020703003e02080030401c8401c1e0a07110b0140c81d4240c1c2c1c0c5030301d40107062030b46c82c0c0c014030420803481c1e210154894840115a0901440c1b500d105400d0240c1041d00700700d00110b0841700140d2041d4000d400078401044038010120301d4001c0400c410701c1c82840c0c002c2408086070a04816000030410516201c01c6003002911136014140e60802a110804070a450300068030403401054414503465000c81d100b400824032600145030000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 458014919 1250 458013669 458013707
    0x140607031e1407110a0f050115050d03020705040b011107030f03030c1e050904020904140906011706040204020c010b03030403121b02061c020904060306050a141006080403020304090908030603060a1b 87
    0x20280c6c0d030b840c846803100c0002551705a4444800304000b01d11104850000c3c002200d5650281031256000ba4983d4414420580b1a6a0b50b007180d00069000300800300440c40000151600345840345001c1030780b085901820340004e840e104003030340d2030303400398800003408520350350050f19100f000d4500302c030181d110b0041160080c1e000d02c07501440391180d0296011641009a1500301440c0964440e071404405038421301c603640e1000b0012042c3c01001c5400c94000c0e8068a0150762002c800c00f069000d021107200741605440000350010901102c2030604407404650703030301c5c18002d074168908034645910821010707500500401c08803641d04039440352000140101017000d81452540340c0020100ca03000c0e070040c1c811685800420881046d6417140a202c80c03003c0c01403158034206150032103a0340e444c83c00341c0360078441d901c3c000c6030505008200355401407095100c284064461480c000c0f603182c0060f15214028421000802d040310300900541100045500c10580d6902076101c040b201c4034040070b5082654 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 458016169 1250 458014919 458014933
    0x24160309080307021b01020601050a0504111201080a12020c010f0f020f03310b0f070303020f031e07020f060a1806090501020306030d051305010c140607031e140711 72
    0x659401d010354030a031441d0f005010b5070300f1202c20600d03071901050301035070454100c0e400500107a55404003420036030300140d5002a4009070328801c10181d2040c2400c800b0001040c0000140605002a291681a20843c1829041d141450099a541c00e00048860200d44011b001354030980c82849130440390005403049506e500420801c890940d8042c40c000b58a1640e401c0e0414010010b2040f883c40039508180154025071406500903024040e260628000d03400000d0b64109043c82a01500c00641301400000d6481c1405030610725000c0100c00f9000d5003481e68400102e0f05800800d00d82400c00d684800380c04540d403156010350040142c5039081480e08000c01c41400482d1151288540003403140c00010307540d0921204052501c0000701340d42d03040090810428550071174a04c1c42c030086a0082c201454200103510b030126462050340d440010a109000400941f140d01d504090710800d41c0d480c1807228401500c240c3c909540707500800085040444003c25100e500c00d0610864100402042d1b07544 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 458017419 1250 458016169 458016173
    0x1090b04060c0203091e180112140a1505040606120f1e08040b0c07080601080d031503060905011a010c080726040305030309060a0903020c010e1c1424160309 69
    0x2c01e6920140445c041c4400020f0542a080c9220b81100b01d951078400c7c9441c0c1c0d85400c83c080c4002d10b420000a024040030288a010f07410100070001c0e42551005c0704010158a00005030014601290151901f50400c200054200c100440c50410240c01040c0010740c01019102c1038042c0c0345e003c29450f00a41c0e501c1c2c0d0342000c621240080c001411128403c00c0e91800021825884c150316600003031155000000104032850f000501100b4004003420040b0b09030003000d044403000e07883d82c0e10240009040001d00003c012065100045106080850b1402d21890350011218004c0c0180020000b0408101000110381080095560b00e20080c049926802d003d000000e202c0c2c2056100722850f502c00f20a01008000a01c10154444622031080048031a15100227660f442262582418420b80340310f5410152103056640c04150142080014402c000e0300c1c207000031b801d0350b668400950241c0d203904138080160801d01020440d08240030701c01622010481401c1c51701c19007000b000e2640d10481c0c080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 458018669 1250 458017419 458017429
    0xa1203230405300f0c01051803070f03030216030c0204060b0f1b2b020c03160603021810110601050a150f11060403092115020d201b01090b04060c020309 67
    0x14400540641c61a04d90250700010740c2542e101030199282c8802103034285409210020964ad01603400c40194881c1e21002c0c00d05800922404140d030f960740340c04540300014107403c040000c103003d00c01d031000c0058680d143d2025000c0d01800c1454405904108404940e80700c140713903002e0b04420180c1c150ba40031100740307415615405201c49002c64160403020180c03241c68040c07020449130481500502030020102080140300c0c170f15401f4000c181940441c0c01d1800c01080d10345c0031300054000c1d110880010904c81e01400401e141c905c00440c40c818100045442d041152501044440c10000301c010900c20000c182c8050f09200072aa041090480d103224440e202002040d00441c0681c441e54285400c0c01d081d03252508a03c2031101d00592302e20819000036806911f009a20030000200580725012038001d14054411004815500031140040000341d4200000410020321401c00308080825001d00550a1f100005000703001150740d2400a400b08042d500101400247d0344150307860000001c0001d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 458019919 1250 458018669 458018677
    0xf0e04020d0504020a0902090105030a020a210f0f0e030f0a1205160e030a11100e18060406050a0806011404090206030a1d0a02210a120323040530 64
    0x700140d4848091100307604190444901a154a040941c6407252200c0040d0084c0f00103004044042da0000c1c4400e011841107840c83c0e10002c44142808072000c01e500820701030074403414503144140c944824603080c01c3c540d104e4040c2070a24a4041e606001d10100702c0c0000c2d8015010b42414081032081d00c4500e40340a00c166840303100c20000700d14003c054500000c280710300034040c0c0b038040d0344064580e4021502d030306800402c09038111200180240030780c07400c80d1300812100000b0740001d21140d290b1000d40705100d02d01c1c03003040141c80c20081603954904101c028001c42c0715500007074010070018012490701203030041e0011740280011580601e1039000c286107600444400c10569900c10582c90401081507041c090041604010503691003983c0008030b641004c00c0030183c0d81e111080b1540c010f44028844540010b80124030b20a80d0349501c60060b001c1c20415441155410700b03070003060450301c040110380340503a802500500d060608109518591044461100c0c10380c1165082d485501c82890700070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 458021169 1250 458019919 458019937
    0x1211120712050d080604020304110f010203041a030a0e070e0a050a02070f14010b010908030a050c01090501060f03110d0c0608091608150c03040201022a1801080d0216060f0e0402 78
    0xa2500a41d0040700804440001d080c5610447c010010b20010965102110080201c00c0b20f581c0006501480181e195104550100d440b1707007003c40804a071158148043d52146031480014000800e91601a6032105294040d501c1e6a10510001c034000b446103521190788004080c100510301026600e83c2445071b00341c008120781d0f496907101800382c0c6490a01070030004003030030708004a216040c56080760b224003c8100040c200700000c00d1010304801e0940101203020340240080000030b85070007158a20000e140810344504103140b0200d03c060400c290031420040d00010700403540c41c10602c00302c9a885024042800601c100c5500c495131540c4425905c00501c0307800002c0c0380c5403c0c490070321805004010a9006941c034203008100c05070340c000c1180c07590926000303044050913900e03142c1d90b04000380c401071003a0040d08070511030380c0021000d9103503810384030b09000b00d907000074003a201241e40d501c02c0011003d04143c1140700b00460b600480001ca269420f03401e1036400c0c90012000b15040741c00041e48 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 458022419 1250 458021169 458021173
    0x2d06070c0f0309080a0c1d04080d020702040612380a0b0607050d0f0e041a0402070311010f1d010509070b2a030d060e0106021504110603040f030801121112071205 71
    0x420080e03c0102e480d40e502c010b9600c8084147c40c90140c0b0b840005000303140e1075103105a000074403a030465407582d01c0080500321a61a002c1d0000e03142c00d00030105c0d03032908041c1c1358403940c4c940310903004030b1a85446070b61b10070b00140e1000c040e03a0b90020900a019802100e5420010070310045002031380c1405030a00440c0b6560300c41e08400852000140380d003d21f66100c5000d40c0ca012503401c0c00007074544801003003100c180e030090303030300c010500d03044650098843c0c210780c29500e000041c64006a49401c91200d0300515986c5588400e030384454242201d00c1070b152042c40b6882000c0170000040208007803c00e04007410851030b00c180701124042c60224161117800c8482c2c000045140d0640032612a0801405192120401c55818440081d64032050081000d0310150680000fa041080c20f928001c00f0880c090000303602e900b0145010320b01624900340031004180c40e0400070507601042c000440c180c0b40c014030f680b00050304070380521004c0380d2070100280341350103841c101054100c1d0250710525006d00c5040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 458023669 1250 458022419 458022443
    0x13030903080a02100614061210030c03050a0c050609030a021005090406080619021e0f0d0618050a2c030403051c03051b03180c032d06070c0f0309080a 66
    0x2841040390354030342005401c80014001b50056403207503401d440c0946110612072a107511039a0110001c4074a613031001b0b2625110241c04001c010000ca400c10440344904001d86071207842d202000300c1c0c1c0c09200b00c400e800d580080094400b5107081c4c00010040c0c02c8606020745481c1440001c80c003941c0954000311842e52181c401d000080382c0b15030300c2038040501c410b02103007410400d0402d5411075800e9100a2210040451b80400e5007041d88120b900b56150818100001580c800c0c24070410600510018181850030000030444841800f60028444070204000303020f800070105503030400c504000006c801d10041c000400024420008611042960b40048103058100e2070010140c85c0000e10b0036180d04100c03802814020085425690024030165071807480d8a80c08181c50304e03056150721074039454400c0100c204a034039080b02903404100902d1b610700c034008103444405580c680095032803030002140101c0c8080070a0440d000c400c070485c46450002c0000d41c0e68580903151100e40e00081c2c3c2c08180180d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 458024919 1250 458023669 458023693
    0x1170a09050708060f070f09050402040e060f0102070b03010b0708070501050405011b030207020a05091e0f010501020d020c03030f03060616050d1e0819020d02070c090c051213030903080a02 83
    0xb080003814007000800491528600b030052800e4007401007000c1c810025000519680207940c0c01000d008060001c644540c0c3d20040100311140643c0c001c0d004400c40c00d1140401c0d440440e114098614900c0e0343c1e80b4591a040c0354800b958400e00081d200321005001d40e000040081c01011b00846c020740001c504414841e41070303410320081d140c030710062500c10002d010041e04c500c030010301140c0040390b24041c00d60314604034008000c0c0241d2041e02c030303020f504104002074050403403260688400b079007254004030720180140c1c1d42d2084202003c0d49540240201041001c0c1c600c001d56204030054046170400454602c0c025000e01480c0003224a0b81181b03962076049036102d1030b05039007404e03820f040c102080e0803802d011700004c90182240318403072110454849528925012581d462069130303000c5640302190b00b0186004075040c0203000480b42024258100c00380f0480c180d90f020848800e842c03c0391b84070345170290303901400100300300d06011070300a001012400b0017000c0c0640da88560050080a100e030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 458026169 1250 458024919 458024923
    0x102040b07031b050c130b09040609050708011109190305030708040501120209010804060e011d150c270f04020706051b041202040f06080601170f0712080901170a0905 73
    0x4010002c0c07803260040401c0f07010900c00200d100512200751445241410a102d07181d0240000e40091500a05480184001c000156000c881540e004000755100a500d840304582640c0507440c1d51424944240308080440c40d00c003000c81708003800c100c003081115560b9a40e030381c01c50b0803c2e40207942d54a000310742000a542c0200803208101c508440842c42c0003480030001e4152280544090400381c1e803141c45602c018000d60114000d402c88004c4083c0a07460144226039500310744a032100c2d90001034021450581120084d64001c01620715425030300151134010004680c3d040d00301940c0040e4490519481303450390b02c01003001038000c000c0843c0364035011540809007190541c0c058400d080c204401c0100000e00d59030150300310b5046401068440090200c08040d00141e00000f042c0d01865000050b41c8501013100c0200c00c0d6201d0a035400070800f6810151109814030a0900c1420802228000502004020300b081030741410102c000c011590f40310700f11403604072080400260365005601c180002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 458027419 1250 458026169 458026187
    0x421020d18171609060f0b070606050a0f08011a0a030206210a0e0f0f100914010c0f120504020f12011b020318030c060712121104170307020916110102040b0703 70
    0x4e050800d1042038a00000406541c0386403164901c90480407804000b00310720ba800540041000500101d5510703154004210b9501462158000641c6000d00c0819800745032800f2031300c0c5c440010901d920982c0b850b000c0c4402d0344e02c000b5003001d200072001c450018a4071008503141c080e1241c00c8000811781c100211041c5440180c6406062035071140310b1040318120005101c071350561403200045018855450000d810702843d802030b88281d400c100d00200c0b810361003681d1480b11030a030754800c6018404038084000310740c0c00b50f501031340007102c600b051041c03400d1080450710746140e000c00014850941b0b8081d4020340030002c450a006800005250300300c0b42003170300515500d003802c0703020305800da0701900051014070072100000d10a1091502802c00940104500b02e0030034100309080c007180c109034407c02000d510501510042c0f518807006541c142c200001654049a80a0889441d5844104901001321b200b50f6010082080e030748602e81e00c296080c000342c001000003090703007911100e940c80c0240074092 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 458028669 1250 458027419 458027429
    0xa030b1512061e03030301090212011a070209070504120c0e07031503060b030319080901180f02040e0705060a120b0f01020a030302031314060421020d181716 69
    0x240907003401040ca4040391608400111104964041d650f015401c00c0710012000940c940804400021148000e80050000102406007441140e0329044811501c20001c029020038400500500f0014244804019004601030034003504040da5602c10408881180704101c541c501c200104220291400031020741108507800d0034408080211010049140c031480007800c00d544a02620344951824000c907807407400d01d810380d089040e5000d88041c144503810343c3d14949940c60000d5401c650400328000c2483d050348801107079401c03202c0d40c08120192282911415060044810010b801e58500d8000d004e040820303201d400c600d400b100305c1c5408940b2012201e5000e41e2920400843c2c3d6070f030100b00c4c01c141d95410f04005840c1d0700d50048000314081c41c52001402c00c90841500c91550000049a61040d8071690385a0400380b43c00c0036010040c443d840000700035a01020039600e000e03000d49600310040c0291141140e0032a03541c8070031040c00000c007030b54004540080552001021032706103800e020340303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 458029919 1250 458028669 458028709
    0x501260c0d020d0f121107050a03020618030c1018080a0b0103031110020301030c030b1e0c0d0b06030a06150e0603180c1e031e0c0d0312020a030b 64
    0x4411038000c00c040d000c0d00340000b80b10b240b000900004000d003d00404211079000442c203032014140d000040c10942c408400104188145180007500e8a030003554681902c1e0f024120b6070500a00007803401007440030442c0c0c0d507814000d07031001601d6038581c042d01c0c00210f091540c0d00d400c400022501489100166000014981c00c1040c004010a0b44514840c0c110b07981441c1100100d064562610308042041d1044a110b90000000100b4045400f0b041003e40e802040e40740785a4507809015100d0780d60f01841c00c0d80038008200041c490100c800060b2800c0da41d840c4011400445042c005135043d8012542c1c0c03106640e076101d00380300c1300f000303c1001090b48200e030a00301c0b070703080000002502c0c6001c010280120040681010180c60009002d9019000c03030160036034a03c0712000070405000510113104034024400c10013840f801011401c1d180c0c00740c00c0b4880203410b80d000d03c542880b00c510300d681400d805204000000c0c03400300c0a2031000301301000e89683d00050840840c1d040108114000070003139031003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 458031169 1250 458029919 458029933
    0xb120f06270a02010e060d06031a011e060f05040e0a060e010b04080a021003110723120f0a05090d0809030d050304020102250902040806010503011b050f09060d050126 73
    0x1091001400d2002c890302400c1255140314104001102e500c21903001510441c00c03d0000002c001c0e40c0326002541c40c0d9a00c903100c1da0707607803074400c406054022280c58540390310503400200641ca02032145407401030180e1500300e00e46600d0f1460581070807400e84000344210f0355100c08200c5108103104c1709003d002c1400300c05140034030300f91f0010b5071003016080180c801d4645142c0004003d0081c0e010903108001000010385407012410011f802991040ca098000500002509020100452299100d61000040a0400c00c80e45091141900240c003646c3c1400010030031145541c0d1512402014984225401991001d041d000d0500b405846843c80701401814824007006070380114500a401c0ca034444214580e00c0b03148005c402201e000c0d40300301076451001901180c156400320b81c4505954054000b07100c014130705180c00354a4007042d00c2100004000340302120036036005400501000000a143d50f05240c5500910802c50388281e10800150455460a92800e04d071101880e1006100d60003034509 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 458032419 1250 458031169 458031241
    0x203010b010507030f030b180f16020705010c030815030303090a05150408160c030204111324081008011406041811010c0203010f141b040f05040b120f06 67
    0x18409010740c040090540b11130004515450344161040d40c2304601c0100c2005041c4089107080d448015241c206100c841c014040440c5400000c400b0100c6006179217482e030080494408544204000d040d1040340210078441c941c00c1d0343c0030130140d4021441000600080742046c0382c0585000290a030304480c6100503010440810300460655000d002d0780c4100849100b071305e19008800540c140c00c0294410700e00340c07030b4644081407030f03018081440241a0f401c080d07545507405544044d0404501c0c800b000e140749464840a0b21843d40d880d0896440c0003a5080c50b511209024291815408003900c1c0c2e07045801040482d1805001c4c03102c0000c2078003814007030403000e502d8503000c590b8100801414404440b10040440d24251310903d040f581000c010040e104d1050101c46d0700c640e09907003407074a14003c1e0301042c11840c803010031542240d200008504c8440d1908040c040982610303010380b54464404000002e080c01e0512001d007880c803e860142c00540b9120382441001d40d40310791244024440d056441031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 458033669 1250 458032419 458032427
    0x117030307031d060a020d1503081801020a14030a0e0609100f020c06030f0702011d06010905070c02040c1106070e09040803040c05130e0c010f08040215041a04030203010b01050703 79
    0x3070003080c646400308002002028600030740207424841c0003507228200802501252941c0a44040000010140000c0081c40d541c00840d803100d000140040390b08000182805000c4655401400c0b01030042c0c0e440c1d4505034449207000e4018158004076a000050440c40580e40000d0440d0303489402c545090400c00340101054010f01c50ba01c0c040e00303009400c0e0180c4100b0b40208042130240d2801040656285003284405446100503203000313000d9824088aa5428a000380080640e0602e160050549a280001e0a00031b02005810389040c080d141600402603107842c09240000701883d02d1b42e291042502000c1c518224008160108102445250010380e40c0d40c040340b25080354001c0d00c0181c4039111420f000c40e1500c0c03039900c419400a580c1481040841c025003040c440c8803a00019142c220b8002001501c0303d404c0311403000c0010384250002001882c1c00709003896a44292500d5a040035115694036010400403c030b042c2c00c5400200e000c0045240c24041c0482896080c0f0300541040d0f2a80c6e0050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 458034919 1250 458033669 458033671
    0x1f030312051017070f0807061b0c0b0d090b0624030a023007140910122f07051504080903010c031e0b0a060507080403020a0e01060801170303 62
    0x408441c0d161808101401d042881480c0a0003c42582e41482ca0118007819a0f481345882090a0941c4c5510005803080c0041444001ca400f60345801183e4000d064a02080c0c40c5107100489407a402030402207030a49a00014141c80304405030005841c07030040c1080c2d1146400141100c3c428041011040710400d513084000407854011110b06440f5101c0996600c0640108140b030f0a0b4040c2e4039040505010022920b8065503031242440011343d2a1640112225056946035000113401041030013120b041c080200940700f2000d107440e020061014001c003058408a1000b80500c0449a45104a035204810160a007d4078112610300e402216500c3c65107456032383d02c1100e1007030210000a0144124103080311000000103008200601d42c1e003c01038024966850340e20320104c03016001e0a403006992140c01c0c8080c0c0001d007450309561400d141210103900c0f0b440c0031251070700c05000000c010b0301c403018035030043c024403641d00d50950304145000b402401d05a1000320107480800044004140c04022a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 458036169 1250 458034919 458034947
    0x16061404150e0f031321050d080901021605060601030608030306130b120303041b05060901080415090609050c0f2e110f010605100e01080c030912070b1f0303 69
    0x40b4503280c000605604001d030700090311010b03000000340c148202055012074000d458507803844c4503100940301c540c81c1c107100440c10003d00e2903120b1001004030314000c074400c13540082010005441c041400440c01c0481c1900311044869a0100b0107115240da010702400024140350700056003546001c1d8005201800ba41c0310011480360b503042041c1c1251500707806101040c000c0011260359042c07510f440c0ba0080c540c07082003510105000000f04c2d281c600340088401c0141305945400341925191500c41960400b002c902100aa441c46000009031081c0640c041e41d5024802030500c00319008148440c41c032a107108a4441e5000c20b9880d11400d400c0c3d901d4141c0e10b005100c1d081d01c01261510283c400ca4070011050b201441010449015100c05400c41000c2d00c0007078070302c41e00c1c100c6402c406442031f001c1c04c070740b06000c100343c0b5000440e012240c0003d1944080c070302c41218041440c40b400742ca9180d110303550940314060303100200182d0204640b0b09840e803450501d41d00c0641171850320014200d181428407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 458037419 1250 458036169 458036171
    0x10080102070309140634080708030f0106050301030b0f0705040f0315050109090c0918020909010c1106010605180301021b07300b070e0a080307060e0d21111606140415 73
    0xb00c40303000140114500e4046c3e40c8000d10039a150303500e0810140300d400c11900741c3d501240038000414050300c2070003030b223048a60010080d0f01c50741342c940014420750710040441c000c11005000000d4180440e01d8000001c501035810442e201203550504402e480c1c05801c036132011810300a00d500000c000c080c00c0e000b1aa6140000030f1514a50a0086c01283e003091004e54089002801e11003904010344c07000720f0781102c0362201d04a002001030a141ca030310003449102c012420502544003402c04400d2481e5600d1001400149042004a61214100050301a1400da507201000600098000c0d42000501880c03481d04801504201c1d1031150140064160062095003840041b03242c00d4005c04104a01e04001021025840d40391025540c1d25040b105007500c940341003c0c040c81d8070f2031303000c20054010521a5110f41640304a1050305900f80d030202d115101c1d20740c0c1c806a0907180c041800c0600100321964446541c02d0301503050000c2951018204041203105090911001501c0b0b1034442503410080c500c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 458038669 1250 458037419 458037487
    0xc100e0112020f040e060f03010b011d0a090606020c091503030403060b011101050c090310060f120201051b060a0c0206070c0b0907050405010b0901022e05100801020703091406 77
    0x403481c020740540c035110b200c114404103001c540140c201e204580304041c1034803808600c1101c40c08050a951790f00c4002c07804500f40d24155492050003000e207020300380000c2e2801c0000350361002040112030700f42d800000140c012880c1d400d41e40c40c09c103a01d10b40094804051090000c200b600113510b85c0314611006028950300c6075140f240da4060304080d1040c556450081005103051800a1001e40c454001c00d071113400f4810060b81f0a402511494042d10701d081e00b099015410520341d0011408012420380c18047c00b0700c0065010f002d01c0300344c04d200741c61200240400d81000c00f501c0041d00d131900b016a095402850400c000e040c1d00c031022400c000c0c0c01c9440c200701a218414460b0900308030b50045501309041070004a00c105c0080010440c80c13400b0f074200e07031a03221400a83c03411112000d0901110403004070b203400e00740344a0b4010a8128082c0000f0480803652000840d089074040d01d000c4010580b1110100110480510140c5c4d88180c20b0365241d1400503000c901000c9500304601340389031140408 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 458039919 1250 458038669 458038697
    0x708120703090614040b16150f06050411070b06030c03100603051002040b16030912110a0e060a090e2407020609011a1309080406090f0504060b070303180203120a020c100e01 76
    0x7c5025900f8075080041c20354180e0082c030401000e07102e01052913182d1810500c0000311070a241c81860519400e02e003406060071403e6481703080001002d0880740d0b06100d0b401c00501c8680e828071100900d1841d4900010702545035261103030600700c0b8034141001032403040c802044400040300c1290b0f8403032000c2284000504072403500341c40401c1035070004014030030919060001c1050b500801c20640808503880e90049540c1d440a1a880000b10752254220349102c00c10020a521031300810030001c00c10040c0c0380c1c500c5000c501c21600614078000300a040c15070906000005070140305242d0000401c0000780b00d00d0b40e03186010921a5081e440c007500912034920300b0030b04000160700400a65506c02c0c4801e0b600c1e542d5401c020036a207054082d203844800c403580002280e00d01031041508448800c8041030034000e65450550040040395001124109032000c006c0050380d00780183c2c8140421461400d4641450307000091401440d90104c1d8040c4541142c100c4050341c101d000711100324001d10384400504040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 458041169 1250 458039919 458039947
    0x80c12041209081b0a050d170f0f030f01090c02011a27010909021008010f170f060702010509010e010506032d03030a0f0c0507020d11030708120703090614040b 70
    0x10f0761000c401409002c0240104001c12100001c01010458010385541d460303074204840000c3e048001081500d03410040c80108030791a001d02011170818191500b028902c610804169004440c100411008000140300c81c0c03000c0d206007000b55545100801c81851201c40480801d809010058070991046224902c0325041101c5841d064820443e401c4103541e440d06a0000380001e801c0480c850f8031601020325205200e140c0c1103040b503d28408014a02c1d18000c80346068010504002410f809580349d800030120b010840c2c64050301c4c00f80d000050626002c4180b908440c5155030114180e41800d05000d4070340d038005240301e58912801e8200780308138080300d003040c0001ca1442c0f500301d41d8080401005042d00d91540a400d078240140c40520180a003180e08980ca40b058040c000d51029403d02e00001042c1c01410101c110300010b41225540c5440340b02d503504d0700c003036988070303d2410000059841c20140d00c140301038006d051a0070121a103130304180400d062406540981d24140304003040e031000070505 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 458042419 1250 458041169 458041187
    0x1809020f09120c091e0a09060209060c07060810032402070f030e1e010c0f0302010e1b0f010509010c0308060d02131401080303060307050d0f061803080c120412 70
    0xd01050907104855190b54494040705141485021300d0380020b8558210110140860b400014004080da652030142200508680c203042e10015801d10490140b5221a0010b1681201402c0146403e034a042c90081c41148001c1402001e002c0c022000c0001030913500322210422051044e003d07000801d00011002030081b41030150040602c903522100f81600030400e800040f10549649603044800942c039607417020b10406150000d40803017654400700700c03018550098a4070034400894000c001c8003c042c98030301480e40ca6141c03040c41050030700d6589806655094191002c1c00c086060444e44400a4000a80c11002409200a000019400f907807030402d954941030b4010040c0204100030000400107048010100c03000b109a60700100300320000000362841104000e001b440c2c000e08007010f02811340c00440381240c00030000d038650000981303540262070400800b683d4480b11100c25080045c100c0c04003900541c03440c0d80c100f0060501c01558003d0030390082d040f620f81c50681601070030444c0c40b80301c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 458043669 1250 458042419 458042437
    0x806040b0415080d17070509120303100f05100e06032508150a1401030c11011d06011409010306091e05070504150b0d24030303020306010306061809020f 67
    0x454214107402c45400c03100d064054a600c03404940d500d0f614240280d07914019000c0d0703103c422110200103000f0611560040001e00000703450f101c08d00003c1c40c204ca00d1600f0503201400024840007050140030007000c5110300620080360b00d86582c4018072405440340c002000c0160181c0c500000162001c0994a20720701003620344044000760070380d01300b00202541410740301449038000300350401c00185444c3c00300f070080d03039820108003c0701d44400005500404071040b429061000980c005184200b0038071440c4101d0003130714400d6040704654002c0904000b0b050b0055545048090500c803525181c2c01180c43c1584d81c040340014038140c0ca4285142807016494107050040000c8403004104000814108102e03101918280201540e500109002c01e0050040707400741d03102803090b0320500c241600a81c8003000172100d103125440c0740e0550f000383c803641ea401c2030f40403c1e000400d01c5210f5070306202d03410051045240c1607000c005a003d6104281c801441141b6003180c020482900c8c0d00c501ca0220398940d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 458044919 1250 458043669 458043671
    0x100e04030903211b05100c09030f08130803032802070f1b0906030305090f0a0f03060504032a02010e0f0a171c17070504121401060807080a030806040b04 67
    0x50790385560042c031200070180b03c0000610440b081840101d5121542d108264400040c20030551003541c184010410080c0160404c44d00c2c0800002050044100c2c040440c0600c040c0781c3c1e14811020142c10901c195031050184d58001c004000300300110340f101c1c5001e000f03059840d03001e40368080c2c05071020b07009444001d41368503a050f5900341003200701540300d4588000caa6160340b100369a01007800407102c8510000e404640c4c100818616850150180c0c640400001e082c008102e84481c402d010046458000301d90843e038072800c0c00305040c1c00100ca00c040e050104845400c80c1c0d070038403940340e158a0004c0700078180420003c4d0307505280c2c1ca560421841d080b01030400310125030b40703141c45511a03c00710028a03103401444e600c01c59002014820003100445a180c19040d0b0701491110391076000001e041008000d0203120100d000f07101c2500c000c45031070042160102d1444640c1816023100c41d10380c00034001c1e50003954100850100895003808c2c0a0301130810b118103642d5140810080e120b0841f5040d402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 458046169 1250 458044919 458044943
    0x201090c080606040b190e040c1203020d110606010507060905100c0201060302010e0307060504172811010c05062e0303031407050301120f0809180717100e04030903 72
    0x8400d00040340b5118420894003440249680c6007401030043d01800307005000700070060305200d8401a0380c7c0c4560014803e000000c502907840e0030626001024120403001a045181030300080d0758841c51145610700c0c01d2000e0602810070000281080c480c2d210000c1c111500ea402c043c06000e0148800032244440c1102400b500782c400300c00a000780300900080380420000c0d40c041040d420001205015a680d50712840c3c07900c0d05003020400b0100e81101840c205125800e0035482d0010112050343d08403040040c1c46010903054a400c041c032845500c1040c1c100249146210042200020442d40012020009420000180c44100e00020000020010409800000004059156016214802c070246410020f5228650105d590b803000307101e02a0700e0080021103001160009041c560306500c41c810722803600034902c02150140c0f80c01c403c986c8008906a007008074594003d01c0e1421060903d11800046161440f1100c454501d60300402100c4804d00001804143c000c08982c406181c10480420710 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 458047419 1250 458046169 458046179
    0x3020405071e0f030f0b0a03080c0708010f14060102010c1205090a0b1f0b1903180b040b0106030b030307050304090903110f0d02010c1d0f0f15030a050c160807030201090c 75
    0x10260560400500203171a100007022040658400c40c0980c03040106110a0980f6580314500c00350030a4101c2c03845406100c40004082c01c0901c03480d001018401c03c04034000c0300c9001c10201e140300c0104000d0559051052942c02541d00070617644507086c42c81c900050030b0300c0c1d550070b4034904200c600700100654082c000b4800300b036400000b90041c56072072851240000f9120740084003140246045071a0201481906190703032030103a0041c00e940342410082c0c14030b0b000c068541d0520400140d800f626403403040f00051000c55890f001f51003d40e00203500551900d143c40d51420f035203200c0c1d48980c45000740e03106407040825200d0350014a902004a040300c6500d90400300c215280c41e01c1d9203502c4090361030800c1c0c5582460040802180499414040640c000d40e0882400f2034100081d080c04c0c1c0c815820611900c166489500011144103050b030f44035140d03c0c201d840141101d9014159828502c4148039003105031781c034100c0d0304907020f074001440c0391542001e18041e800f510000700001d04d025080400818 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 458048669 1250 458047419 458047427
    0x712030806040e0106030503270d060f050f0705071502040503030c0d1e090b032e060e0d080a050a0e1c0210031a01050c1f020406090f05030703020405071e 68
    0x7005540846080008040d11071440703080382d0391448001c010390002d03c01e8680308a42e0076a0010812498540d0b80d006084840c0003e007901075125040350030315a05c0700e0381c10140e1214494075511030403c0950760300d141440c074009480da000f9404010400032640242002c0e000aa4054900502018003145c3d101c802228a59440e20082a40040040c01c0150518401c500d03d48a1000042e000d07103418244c542002000300003988024441110400c0c5c0001c0b43d001413000c2400c0f580c0c81030801d0400e5041070b00701200100800300f0a40c0d240e00c5a54051810804550b0400840b03c5400980c18025602d070303c1c0140580f83c0d1b007080741e00710764441c40e81403242c0300014000254803501c3e0320840307103e9031180403030006600700e94135000d40015211940308444025400b440042c071140c001c4404580d00511070f15101080c0b281c4200c48130f1020781c2c021400304001a080800400500106481c7d110700d1402c1602080c1c2e1103100d44000f038440c98480021540d0140192842401c42d000b6410240318080c0304200a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 458049919 1250 458048669 458048671
    0x807171603020d06061709010203150f1207031b05061e07020a03060615110f07060e0d080310090b060412021c0803070309021003140408030601050c070602010b1305010e130507120308 80
    0x80079200b1b40000d485c0b090107208a07031280b1501030404060700030b01014004a98040d4003625004080d139062155010020840078000f940700d070350842200c110340c500a020040c003a41c03009001e44020301c140380603a00711040e11411040000c83c0c840c0c480c05c540c00003881000c1da5900281c070042c034007000860346100042241780c03820095120b480401000d00100c80c1d5640951450712015017041c001401038601c036080040800400030580c021241c02c6460701a290f5006031944155000c010004018400d094011a9a8400c044074024200751901d503c4000c42d00400710001c0c402d4844200060000d0301888190f22800d4002590035264607008102900070160f42c43e00f644211800c0c801c50014074440c1c017482c204103007540c80c1510035440750f6450188036040a4102c50501c1400d201c84110b2a1040000000401e6a540046103100e801c8090004800503420701d002c103503042c100140483c0b055000300581249544c3e11521840e1043e0901c24200007440e00300c094007101ca40e51400c14958452905 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 458051169 1250 458049919 458049947
    0x409030e100f09050603190e010209060a050301030c08071a0901091703070213050c0a20030c061006050a05040612060f270911130209030604120807171603020d0606 72
    0x142000e6071900100885d5010469a42555180103403030303080013101c1508856011a14140007608054140e130000300550131118942000640c0400100244046042000010401e48016101103800c01d04184e151511050320750820300c80c00940200f49074410150000144405070000200400303a1048680300e07401813805a10900d01003500c40c070b41074030b54807e0900504100050b42d180190f001810b486002c4900601c1880251510110b1110307001480117040310306c03800d00503000c07610740589203d944521a0708548d0400105002a0002c0c0c1d40180460302660307100c2c10000120031108500320040d040c0c54000303690418100d9000038190115000c40468649160300c011940307800d804180c0100c1d620000050b2001240da64402c1041c14800d28241940d51080b40140c984400180031a191110550b000c980d0b0355400e0000c7c5590303542c800e060320341040642c6044020607103144902c1e4000b42003d80640300e01c0c4924030804030598003d604903840e003484114103004282e901d02000c6c02804104c960 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 458052419 1250 458051169 458051177
    0xb0c1e120c121c050f012303070306020408240c04170f0d050d3204080408010c0801051f0e0907020a06050f090712030f050d14040f020f120c0409030e100f 68
    0x4a100146800c2c1000e050715840284240340c1080082c140d02e490120344100d0340c050140389c4002c4042842c2e0700050000c0c1c1000340c000c080300d0444860442c5110002440c460b040754038a001c0c0721490450000f207600715915150310060740500c444600b41810307031102d60300003c9e109100032810000d8124014001102e03030364404110310f1030300b020082c903000304205000381c4404000c00070915004c4540d00d90f6412034028803019040945442c031807801c4518940540010441c2080100103514183d400d41d0110440b01000d0803503503804a001400702400c41d810301c1e04c1000000c000800c414420007040078016048042884241070034004511a1001951200b001c0d004818001c1542a10001410039940d45552907020344400b800c0101c1c1e181e001500c4114541d500c07408114040041c2c0c40c480760255020302202c006d0316180f44104840f0003e504202030040d407100c0800301600a012811074203445003610b01003480c00c41441c084039525000c890941e841003c00d40800c0c03003d94042c41c4c0341c15036101912 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 458053669 1250 458052419 458052421
    0x10603050d02070806010e090a0206040f090506220b0111030a0804020f01050a0206010b0f091002011d010608030909151c0506100515090301060306060b0c1e120c121c05 74
    0x201c101d8a03510b0307500034a040e03644001d0040191441d8805640d0b40810342c00b05860381200c450b40014402d6110b0781c0054508040384809000441c080d00ca03041e00700c08100e0b8035941c0700e408002d000403190341d100c083e81d003030954882c1c1c0c50340b959018002060202e0140c030141c03540ca100141d40a4909271040d68268011021405a419254020340403606d03118144e40040c0389c3d030781c038180e04401b40d0350001c2505d00b045001400000400d0300c3d1a113202101009603000400d42c80340e40c2124424011740b60041b400c15a04004041002c00030210894607440804e6600e215582d03074100042c2d4203080514240d54205a04002010300a081ba200300034925221708180c400f0740d1101d08012014246034020160f1011940c6000418002c1301c1005001003000600041003859480d1076410854041d58401200d8800c000760704091a2020b110151445500c1402c0000341410003802694441e161014801903002c00200300c0c0c0f0048081026107000d42480744880c0d620808015400548462000c2c01c1d900d07141814 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 458054919 1250 458053669 458053693
    0x90a06060e030f0618030c010606030501080f0c010509040b0f030a0c0608090606150a2d02011508030a0e0d1e021230040e01030f0c06050703050f131701060305 70
    0x8580f0800d0910300c180200501d441e1411903040c0c0076007a07422070f40c0f40c2c4000c1181d25075165081c02010f00500c29620001120341c541448241018054021442150001c0c505154140c1e000000d540c081103068500103983c0000d003011403001034030346141079494807820310800c0803c4070356000d01341550f44503900e800d9982c940c0035070555600070a0f91401d40c409417244562404015180260070010b0091601050200c0272451514400e10054020003040c00d201102d1070302d1940900840084140d00001e80c0840d9250814280d140d00940d40320f4010802e041380030351610ba43d440d081d101c22940040c0303d241ca5100440807800e041c03800c0c000881c0103000319080041400d00c0802c1c0c2c0d03020043c0e144c03101104907603550f034140709001000d40b0303541035502c0c140401b103510000c8242d074902852103084030084c2040c207801c000d03258444550040c0100070f4100540c00c00a980304041d00c0c1075906001c0b07c00d8071034041c5640020305c0300143e00007048542c2070400440100c0c0054201c84c0890f80582c068400c41003c5c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 458056169 1250 458054919 458054923
    0x4030501142e09050601050d14220b0a0506010c080a051c021635030603070b030105130f090605071e110c060d0b03071e060203030417031302090a06060e03 68
    0x1202c2a003a5030030400b0741000081100c0c1c1060340d002c1d40500d0018942028620b000c01100c000f5403590054006031800c001c5102450741d04030358180402e2042c50b0300503040e070366186541c1c40f00802209045881c5c9003c00c0c5103902890702c3d4842540d0007100d45440d100403100003000d90704405002c42042d10740d4003c02720401c82d0741c82111170920031321f070041c40000c105441390f011403007040004004200061503211084030f140d60a01d18444100c11120f0350382d0400741d040610380811600a042d680707178104010015642c2d00c1002120006000b40301049813034681800d44002c20001501a0019045c2002c101c200e50340807942c84510850b0044419000c880e84101b00c03110a003d0800e15100d501c100d2030340120789414800303460302c0882480c011402c50030943c040703414008590321010180e03102c43c0340804d50501342000d040107020a4030080d801c6180946400744020110172158010f45c1c400004900d0100c0c00044030245290068210041400c09002c0b003001000310344111000100c120341510454900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 458057419 1250 458056169 458056231
    0x609060f131e032a08030901080606040e0f0405032101030302011a210304050406080102090a0602010c05120702100912030c0c0b1b070f0c15020a0f12050403050114 72
    0x11035141a841c182075607101c43c000100040340c0314441040e60b1004c80c3c425080030042c009444407402658590388107034005080000f001d001248545006d10090000c14000b407030f410b6101d1a03411000f4456240c0d82809421485104078465010140c205801c200304280f02c111412031f403095000700410300c1c101c92086000c401c002c050560001800b1208041c51040b0301054020003100401c1d280740c2a0745e500014100c030301541c00800ca694001c1101c0c50f452500390710700f00080075035000a002c0010310704401412403241c11558081080810b0101d01554800c20055045281d503000411614040e81407162070359807019185030000e4181480c80303000511401c2c0d4445280c1e4400c07418030641e2142070080750043c9505012001d424014002100407400b8a10320000481c0520b00440c00e441c18100030500c081445000c1c5003e550100c01400e0000314241230401a05400c010031004c880c1526104440703a2041d0791000e0000c0d03007003641035460192125030f40c6008440300406181a0401d611004100c040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 458058669 1250 458057419 458057459
    0x22b060903020a210e0f011101050a0b040b06030c0f13080105181c0905100c080d0f180b1503011509021801030c0f0c03031e0504021513140609060f13 66
    0x503c41845c8070313401c001e403a4000c00c140506110007031640303984455084a80031200010110745a10f2100b51030700b41817083d0626018150303205072640c80d2420443d20035115200848500e5000051502c410510301d910040190030914000d0025041011419642545001c002c4016014140b4060b500001c240e01d004001c5c1c06d42d48911504529000411118051802c81c240c1841450b1000e203000506140c0141542d40c0d01301070024000126102e02030840e5205030501101010102c1d01c0b00204d40ca1a01c0c0c00d610900711a2070140c0c9041a00109024060100c16110400e1400901040c442c0c3d20b50080c0400d40c82c00c0d06003034440c211007001101550b401900c0c2c0004503e19503408234451b40310b02814030704180242800714014050068000d60740243c01762207000c0319aa0b40030300003145842504091014421102c40d41441d2403902404a80d010a08c10f0071620703038592403108507d440b084d003507440001c4010708154841406e0703241d4151a621941d83d9100145403500f012820840e10055010b58103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 458059919 1250 458058669 458058677
    0x9030206060f100e0409061811010e090606030a060801051305010f05040b0c03093309070303091202010e0303191806090306020a05160606091107022b060903020a21 72
    0x6400f400e410b0710303050079071240c13280c020361189001004120a8043c0203019004120580000301c0d403414000302c404070f100c1c4400c3c10050310b0070041045030740b00c8244a4102c00e0480340103543c3d032203c26090b4010030b22644289450f501300420001100c82800400a031140070780001d0009840401a207030444400700d50062481c25040c020500d40501640a55800100c2800b1611100035450a0072185503d4240d0145100000301840500e03e00b2000e54641040d18440240140d5041d6036016165201c0c1d801226401c0c2d005c08c010400b907a00c01c0721043c0b011840501907950750344c41003401b14145080008981c001c1040d00d01c00101450110055100b00d92175551510419401c2d96506000f947c0702d0042001007010501c103503d6a4003000c104210b100d03100d4040080c803589080d400005030303000105192400341c5c050000901680ba2440c0d017580e81344040301c03416042c490113815014201c0040302d020300317071300d1804086c0d000700b40d00040c4e607c1c55640140c0c400443d601c000d980d08130400014010800010f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 458061169 1250 458059919 458059939
    0x6121103090604080a0c0506010312092315091302250b062412090c04060303091203091d0a061a190207052d0d050d18090207050109030206060f 63
    0x2c1107844002d04038140e05e52802d030605030910b40380d0902c1d10741c1c00e0300281c601044d40c155030a003030341c0c0002000e03008046402c1a0102008a43c8901c3e1414118821042c0640c6070008181481699001101c12000d0010211496215040405070007500701c24210070111110320340740c844180004000c038000c55441500011980c0e603074010f001803183d0148030a919603100e030700070303994070145c01c006030810081096803181c0c5498242c205625090b6403045c214043d41c607283c01800441e60103210344082e070307041e88140c42090b04940b60032100001c0c1035000ea01151450410072240d1040800e41074001c006c0d2100900100d9241d0039000d1284c94100721072440c0d80360070400c2c0100400d490580504441c854019500115590360210381d81c00081c102507900c141c6800d00040e40d105010028103001441501c0d1801c02e02e5a5a5619a4078002c01c1c020301c0a1013002000300d0300c403114000442d80030300710105065441b40803074a080f81c0a01520a412009401030000151550a100d03241c2452414014441904 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 458062419 1250 458061169 458061173
    0x1509060a0c06150b0706060905060f041a030703050d080603010b0109091e0c0323040804031e050102070b010501081503100b0d02030601081c03060602030d0c020a0c06121103090604 79
    0x708000c0c0c0c0c100c03112a101d04010902c0f122015000005054030080c0715900e03800340c0350410440e5210381144800f5441c3c6401c1c04640e8450300716140d64100309132000100d4036440f11004044a0340129116031502c1106804020001d020640e1050f11030551075811321034803981c0c200b5080e50100c0c00c038640003600003e020000201c40d030b00800d510492483c00c1104030079803c154130701950000380c2d811000c2a01c9044941940710030a1403101640741002c05a005810035aa400c2035038400ca200213081612500000d1208040d019621610698072030001c41d03941342c1501c1c1c1030003101000d104d064003149011001507041c2000b0102d0550b42c50009028140549021b90403900400600e4519500603c0c0b00d41e20600586040210502034480c1c14002d02c018114275142140d54501b6a000030105400c00321301b000281e40000540d168640e01140210703861381007000880c0340c03520f60a00642107162000c400200e00f5048040c13203c01071000034090048030f41c100c0510008d44000e035801c08141e4085400100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 458063669 1250 458062419 458062427
    0x513061130090d0204050703021c090b0f0711030309061e0601090b0a0210090501020c01060b1603031e1b030e0102040e0c0307170c030a0b04052a190c021509060a 71
    0x1c00b040003c01c5200019825004101183c0045034504d0210303500107210168001214000742c2101e43d41401401721043c503688007084030501501001c034204080717011851080c025944001e07078204c0340c0100d944030300d8a00d140a40e144019903441d200030740c1c5d5008081c2c00d031061201c201d10807101a124101d1645c80d1064000301e6034010b80c2000308502825003000315102c0d090080301400c0d80502c00141e250200591800d0131a211a4405004894200441c0b01100d140102c001051034060600007000381d880e900da0010f0000411140602c4c615040380e196021050710b101d955100c50742d9400304000007950040e54200c0c444c0c0c2c010746180407071550000b03205541d00c000440c2e121100e0700d0500c121014069005030414030a03036110348104004030030491100e00c07a2040b201e520034101d4050105d400d10b14002d8801e0100350300c07001c1202d802c80602a28035880c81049480101103c0b00344140b004500b00300030640044180c04030303c20790300f14144210b031400100a0364103800b0000c050703034a451082c03002070f1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 458064919 1250 458063669 458063677
    0x307120306061b0f050304180605040c030b15070512070609030e0907051b070b070b1f150e0d08032406030106051c091205041d01030803060609010513061130 69
    0x4405c1d101c1000017081c12207408103524205800000c001c99081d0030001004240c40c11440118105460a040d155880d5102c00068440503298161907584030500e05040342400b41c0549074090071a00011002c0400c403080d0303c1100500d00983e40d242e0061060760802440340015601c030000607206204624420107080104079203c0049011280032654441c13220070613404c9444180c42e01000d074010003c8641498028940d1704120705241c281031400c10b003807000c448420390800010460080e06010850300e8401c880d2401c103400c14186512860306001d03085444000140c0c40101c072200010b042074a080c2401601c0c140c40c071580f64241030031003c5402094060490703621090f216120540540131030101100e1041d404640e507074150b91207050440284a0341d000740b062034001076400d0010000700d580081900e0b0085811135110307694013002c3d801200c00c0d000384203031100c0c4456044400075909411502031144541220162608800d209944454003003c0006919034001410500040303441004020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 458066169 1250 458064919 458064923
    0x180302060c0a090302090109050103031404030819170906060103060501031a1207090203090601050a05010c0309140a05150d11160b06060705190309050f0a0306090c05030307120306061b0f 82
    0xf000e202d03030340d80002c1d90f899004e9124041940d9140c0041c0141640a02421100355007580c906280a01d107507101e11162003504901d4600410321071740725800910440c254104001e20010601550070500c0080d500d903c010303281140424540100043c40d540640684070205880700d402503100d03001941442090910582030300404c0c000c81501042c4003c86201650180508800405d6198102014400c2e030700c510b03030441030602a400585200003a8031021903416519070020242c1642c4c1441c001c03d46010150700815801801161440104071203480904800600c14805008400e0306d040e0700c444510030804c44100d400f0145002e0004502487d91103034004201501c00c6141030280d403940c6042a01d00c1020450103542a69a03800b0b15510401c4800501030803a0090110b0f4440000180400c0c414030002300110b0321800c56009200c02d40d46401c000f008054252a9a11140c0c5895002c200c8100c020001003480d05602051180c801d02c551180b40c1e0100401022004060300e0b140310001d542c21007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 458067419 1250 458066169 458066177
    0xd1b03091a1e0c070501200d0b1c05160504180605061309060b0901050a1d0414030c06010e010e010e07030207050715020321090606010f0c060519180302060c0a 70
    0x2070308104034002880742e100706442c3d1043e035210f86503482c00030f095814a505040594000c043c1000318402c0510450f40c040441e40000240a50314402080d1801080003d68010541c910707202024050082642e03140032a1140004241540300c03410401100e0600300f80882c0766100c030000e000020f500746d10070b9170001e100030002106078003803201803025200c40c02d8040710303c152542d110907050f0404031121409030a0441b098007006041c2a036038002284612500078524040f08049414007841e01392400c0800301080039250b031a440c1112240d6100821b21030740602d03264107030000800100b0321141a060351040b101c88146611040c1d0110065040480199140d006000d00094071203a2000c501c9201d02e200d8001d19210540031412203c00754031901002110281308041180c08603002c151994854800d0800d10700040c0340590407202074502c1c2000921003403a0509000d004504010010408041110140702d601100051500b20b0020b0002c000c000da132080d03000c40d043d80d034100041d145c2e024283c50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 458068669 1250 458067419 458067451
    0x10605120c0111010f02070f02030606090f150607140715020a0503070206032d01090b040207050c0114040f060c140f060403081503011a2b0602130504020d1b03091a 72
    0x1c5c2e00341280c2c403240c01150b001540d154400c0031030a0a100c0380c3e9014400300c40d51112803803c1c1c10100349130500248641c0b01c01e0302607101000c0e40d0b03a510701503c01080c2c000708540540c00d8103800e01d0b55103418500400520390444592041850720014140c900035500c0b601540c1032000300e500340090384d00050240e21400f40310f19004401309503e00c2d4145100c40d001044250305500d0900c7c000103c40513800258083c0780108a0000460340024823140800c00a103461000c10000340504a010301403904088807100d64820001441c0740e005a605003561302440e007450184068007030300d654074a100c881d850ba0a0b002040044d0209000e41c1034150702c800214102204005140002401c42d00001c20094650f018417182d21068240006015258420f891400f451580d0440c01d4102d8002d01490081050341c00294540520003044a10002000054025521540c449030750074040d0120340019040c01002c64104500103100740143d2010a411901100e840c0540d45111a880039000b40080c4100c40440c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 458069919 1250 458068669 458068691
    0x3051210091a15070b011503150305010912050a021e0708190b130206070b06060706060305030304120203191b170301170319080a0e1e010605120c011101 67
    0x1019507402c0c074011580da031503980d0b4074808110810f21201503c1001c000140282d10010390320400d0745054030b0a128070441203a01d4598100c0242184154101c028403120300c001041040c1500030250091203100b43d21502008000c040300c0305d01840134020010780c03144503a07020060340c0785100c041d403200c110181d60401c1e4580710000c2c074050b4416140303c11207003d60503100038041c5454031180c000c10009407030410407405400282844c00b400502415107040a00410000c0e81e0700c504480762980e2003d008c0c8811556400c249840b034100304c0b0192040302c0c0d642e2050b000d01e031000c004c440c00d502480b1604182c4503051042111f03031500c0200b81213142c4a5079007415001c00d07035030340352234450a0642c1085035581d8100800c035968500a40802021030384288400c0c80301480c8100c8072600b450f07003850b00c030701d0541d1008004405441c02d00c2944005000382040030403034001d15606412482003c200034004d5507a12004e01c40301604c0d448150880f9004800c0a00b0036601c030f040e400051681d80400859100420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 458071169 1250 458069919 458069921
    0x21c02030d0905030705040204030c051012050705040302011d030d050c120f0a0210020405030d121e020a110f0d0f050c070b190c0c05060904020c061906120305121009 73
    0x1460740101e504004200b200745030400040014040030350301507003458590385e6250303c1a0700351b000340d0f4401c13174001e105510301510500c4c10040d80c826070b000500c00b038284110b01525550241c007003640004c0740b481050403018464107101142c3d440140042ca88403d103850104d0742c582001200900382e0140c911091b0b103c00011000e4440c80c0d03030a6100550710fa18014000c0e181c20261034100001e0b50052004100c80d80e0701003050346101e519810014009041d210307640000700182145032892101080c940480c442d21607014010600e025110803502c8500110255a56400c40c400200c5641c0141040c030500307440759001311a07110131800c0c51410322140c001c85a04106258010003c85000400c81000000c00c0c44410481c00c603880c101520f4105080d00c0350500110b00b401518018000084d01322034585965044414516960f016a40b2030b080181081410b1a8401404034041d8288034000c00c14448107441e842c002549900c80c01e1908a9500c09040040c80c0100000d040854208000030b941c091 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 458072419 1250 458071169 458071183
    0x20c0c030c01020f0715031409010b0103050a1107110a0324060e06060702040e12070602040312081303180b1909060e0102101e06030507030302060121021c0203 70
    0x1110181000250600034103141511054081d811503220a0814010315808102081030b14030424003080c1550750444183c0c05000303001c0b0b90b181c4081c004003c00400c180107504c00c00f900d2000b42d9007804145c43d990380083c140c0d04081018412100304110500029407020030440d80d405000c0c046510880d52070312a00740c8400300400c990196110109000400900c510030080138040700a000c5c04181001004540385008020340280904d41e00c41c48400340e80020003403d04c50142003180b482c0c6d21801c3d8601040a50050312048545200f0240814851400707804040d20509040342141c40201362074508656440076200300c0007110004031400314900d10660024810500d20704160074214111030341c000e203594032039803118082040503a50141103030b03408280c0d2092491000350210f4203560103504254405800c8285480851502c100001041008a02001124001c1e000e45409030b07a2100b06803010355106c5140c00040c09032901c41c60040c07814092441d0400d030f04554058020100e680401e1030405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 458073669 1250 458072419 458072437
    0x1505062508030705120f0f0c092e020c040204060e091308030106030b13050402101103040f031208090a0809090a0e010f05180c0d0303020f0706140712180b06030307050102 75
    0x30000310b00a08004207941c3d1031b00492030841005071407803d8401a00340800141c4a1071000000040c1c0420075070b01c052084059002041d0003c05070040b12040700105501240f8060141c064861910302030725041c42503400300d6040c1e8440300f01814006040200c600402084a04250110840400231401c19030203076000c5c2c800c0ba10006000081c010410503030780b19203098026203504043c1004011f80300c2c010306503144c03400c0742808046070300c1030f04007581540106c0d009920481c61651002050040c800c000054100154072040c076a600c44d01051501d450b1903940c003410100040292a445003400300c159980103001d46800200b0503030f1510002d080d540401110051241c503030781031000c40580d070002d4002806220000b00141800c00022420b1060400d5000c1c05150b40800c0b01d15816150b90304031505580d00135020061a810040222042e0310140c80c04400184250b00c01c003c00b00d21441210202d110041c1c08104115103580c4102040000a00c001d4050105121300d50014000340080c088043d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 458074919 1250 458073669 458073677
    0x2030703050601080901020304021810080114180d08130201050c1504050d020c090a09020a0512060910090819051605010525050406030e0c0d0b0a15050625080307 71
    0x402c1c940001854414040d2444489901c10824040140c3d51003000c0c00d9088200000c042e0155178980e210044100310b603100703100550174000c80c0702821000348844c038480c008403000c0c1000d11001c1400c25039a491010340180116001c40041000044c1140034401e0852052520502e004d14482085007032150780ca80702a0b1000e0f241040c40100030003840a61044081703032005012950740400040c0d20004042d059506a56071100200c0035502c50041c80323400f0f8a00640f805828942c04d01c12035035038090465201da201d001e1207848400825041c00b40d92184e6406c04081802c2c841502c800c2c41100c2c220301601000d2200803c4100341883c164440280a54000e00001a10b490215201040080c110380e101c1707040c81c210040090216008410b440a0f1841c1e45000030385003001240b281e15021a1040041e4026807101c0c002081015134000c1500c80c042c01d08040c002c3c100400403489041103640155035100c50f00f446003100c0410038104115050404020707400e14036049441c0c14400ea4400e645000010b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 458076169 1250 458074919 458074921
    0xf0406020f0c0f0307051302090301020a0206070306080c0f1324050a08030307092606040c030201030c1422030602040605040303020601060903020a090b040b040606020d0905090906060f060705010203070305 90
    0x40140000030302c42e0b41c1034540c3c05440c1160000641c40d0704044c02154803a03000d8189042001c0190781c151010000090021552100c00c3c2101035582c201c11a9480f00003420060081444040411201d9014201070204000c0504441c100b182d14801d000b03400134042c2e5985a014141607150291200300718203400c61400c49401c11040c40701c5a0900c0d005000564401c0050004042e4060b401000b01d80000e2200c0030094003004030b0711000c1c0c1c5440e1a1000521851017440705006040b006541201e01c07d880800a140c11304005403000004007030806c2000c0c0041c440c0c2c42d203107594014044625a001b881c201426902c035580c5004a07042500002d000031000b180500c00c0540400150b805000c0700d007024048a80385900081c1c132101c1ca03004004107643c884015202a844c1d43d0040101d03030000404c10300c80c00743c880e40000d543d800700ba01541d0004145071400030310381c144810001d000e00482000360040b80c0d240b01c00c1c01012018001c401c2e81001c010030118000c40c0c020f20155005e036607584d03008222 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 458077419 1250 458076169 458076193
    0x301150f05280302040b0117070801170a21021912110303010b0d0b0a090e0a031b0503090904050312040b010603050703110901080403050c1009021503040c060e060f040602 75
    0x4a0120032400b4030400081d02d264a050a11801c1d010341100d5045501003610721500c00100d0701e1040010800c00042201c2060000c802e4000815605841005070801c010080d8100c1890f0340d880d0001e40900b100c03000980c0060f5101c091660142045c5940c0102c5265400494880840003051a41521009000074440e036500b54000d58002e158018103000394115414455035451074895046044511903850102181d9611100c0030751000f81040301341007000b03260310302d460b5444244080301140062610540c1319413206820700051070054104000b9818254030105020820700d000c2e10544440c4400e0050725007018010340c1147c030541c401c0c14041d03500d503d000c80180c16690041c1c032400602d42480c042840b540b03000f1041c1d0340084c0003403034002d54a41b11401c05403250b00c64840c1c1c0c00350a000e240c010801c0c2d040e8981048030814030a98240c041140d0b1050001d08901080d03800030588680c490042086030321031000520001c400070001440c10b003020f1030041081d44190300c0440540c1000b115201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 458078669 1250 458077419 458077429
    0x90607030815210606030607140a030b09150102210409020f070501090f0c0e0708160e1207060e060702060906180a1409101503150e090102090901080705010801060507020301150f05 79
    0x70304204103034007c0c10103040102c40900b19048c2481d03a4139402502084000e00140b1a80191520a901034040b03000360501c108a43c0540d001244a04c2c003610418480b400d1074039013000a03900d64600100d02d1400d280c184030321100030b0340c40307a1035400d603000c4203014003c0071400a01c14140790510410384413100c4040e5250101900206511507030f1400c42003000c001c00150003008296020302c2d0760035500e81301d0030340400039184a034025040700d400909404810742040b000043d504242e07280c0f81c44199030f103c008020401a4814208007e42100003845251920b0410f040500300c41c0f032000c3c3c1683c000b00e070080c0109001a20381d6215840c1d40010f0081c007405400c0202480343c20040200d0360f12040c50510310383d2070071825007002060805036554103070049410030918900250401140d0940c5509042200038041e40001c0102c0b03114001e4640002100c81d000038246048178410f84602d05680e29100041d6899000b030842640c15540320710710403207000030a06004002d80000d001000c4040d04000500c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 458079919 1250 458078669 458078671
    0x308030a02042301050706020901021501060201061d0903040522020c0102040306061d011403030c060c0405030c100c11010306050d0c150e0d110a0f09021e0906070308152106 76
    0x142010854a0483c056684001207070760b070343c4c5c000d40056603503046280100c0c42d000b607044d0019a49580d000020803030960641204003166100c2d1000c81080440c03c01080040310103a6180466034800c100c10842e0f801e0007010301540640000225561120f0b500c000000e07a80015051059654000740074003c2046510512010341a0178180c5011010030f40c40c00b0048040c180261a5603c05400341010540c3d401c2084862000c012415030340306043c003100f180c01542160084da03109000d11030103c1d55500b49402105004c031300950b5110790550480d10b0315500e10b035100010038101501c0346000301d40c9844035682040140d12411035160014034212034088000000b0803140c0810074001000c880130f40ea101c1010410f5034000c5141800b4980d21400200b81d070700a0f5000019014800300300055481d05540a00b00c000505401d202021228600302481481003032145035210409121800200e445003190a40c090008141000d02c030100d03e00098039074151000d00036580c414070a1040400b81c09000f42e07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 458081169 1250 458079919 458079959
    0x30801060306051c0623160e0315090102040f0602030a0216050d0b09191b060c081c0b03011e11030108120310120c0518010509060402090a0308030a0204 67
    0x204412410100018420028054003c00030050301d40003a05020060f40a0200c00011003110001c400c4a44e042c034986406c21034460031201d00d0743d501d58032103a018285a450f000002805050088000e80302c100c4c1824010b400ea495540d824080440c6010301d1150350405403109400668a500400100070701d014180515850103403042c58040240d03886090410303256590001344061583d40e00d54032240b81402c15a441907440030000c92600a10806041202100001d100700e00e26540e182c80b0b0984815200f40d1000345515010069600e2154210703403d1907034400355000204019080c400042d00390745402e441c00c20100646980300d40c640d80c661145440300b400c2d40b0341d031a0441d071501c03520507250800f01b00c81844408002000507112141c42150b440581212042c0c1010b90003941000f51012956000d29130040104080c0080c4100704080014100c0760010038140c00d9964420a010180d0040a101504211884000310001b00000080c51055015607001070300c07145089402c10200d134860b185 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 458082419 1250 458081169 458081171
    0x6010507170f030a0b0d020a09200d0203040519050712030c0218010501020c04110a0e210105071106040c270e031e0703090e100b0318060a110301031502130609030308010603 76
    0x4006c00588236043c00000b103c00c04500000c3c0903112010011001c0307807000f00070b020380d9000030b450381440e0007130b41c0514000c0340140c040b00c942043e0000340e600c0001c02e110010b800360380602c02c1003099a515203044071049109150950345030000d540404d40c020411200c222140700004014401c55070304210000300002d040300c0500103d010202081074a100c3c0c0d0b00c0100c10040084509400358a40c014110001c0e00400c803862038084030b104c0c40718000c0c8416100000042c140001c014021400040c3c03041c000c2c0e411501c01c0038210316010303a41c445440c0c4003a099440d40c201440650407440123124203030001042c140507540d1452000301c00207180d07003030701c0b4417601c080390511490003c42d9100041c10240c807008802d180e2907480d43e82c3cac00c64440545503c034201040c000410442d0324808a050002c01041400c221495070303d4902c4800d0075668a407281d204103150038001040415840112481c1c8030b0203822006180003200781e200c013400040c50f008100410b0b4104c80800406600c070005500411a91070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 458083669 1250 458082419 458082439
    0xb0a0503061012050f0a0b15190e150703080109060302211204061d040c02030412050109060f0c09090e0a03051c05010605120702010204152d0e040e010e0606010507170f030a0b 77
    0x120481d4040c000d400d4855000110f00c1274910f6006000d41d0404610042c10b4113450116040c1d1040300e64052242100015240000051024110302405054036401000440d000313041805038101080c0c0e403440300c0c4162161214880e485c3e0394040040000e400d4503581c00019016104a48900504221446018030b26000b01020519404410384041c0d41006090356080840da04096026100707080d400f074a00340c5440f1840280c2c00d031662200700722002d10348030702d001c880d5280128012034130705448404c0d040d00241e98040001c0d10400052130942c0c03031260300032606002c2c5100354040300c000740c10100106100242200c0381c40c0358403d001758002d41903c02035241908002d0440c00c900782510601c0c0a12083e801d1200a61000c0c0485141201c215808403c003540076004c000d050106410046024614001c0444d20b4610f060040301002e640c041e0081c0002d844040044a00743d00c07064040d9105817120f041c080b44007a0700001014024001c1e031501d0b460341481410502124080d10b080c900c9403107414 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 458084919 1250 458083669 458083699
    0xa020403140a0f1b180b09060a03050322152613030c03020f0627061b03130f061d0604020f040c0905060304050f070b0a0503061012050f0a0b 62
    0x1641004203c1d90003c00c104520503a041450488443c1d07400150f2015007050300110100c00c1584150501ca1046030140d03c0740e00d4000a02001c1c0d00540401b41041c0c00c2000846205099081c03040c003103c00c60000390403916a02c014a012080d01c06e28900c00083d101c00c041103046e01241e54007a090060141c0d120041e003070103503000818100ca40e10050512500786045810705000b40f19000382d004441c0280c40705490401c1145440c0c400d0500d1400c105522709030b409401e0440003d030b0a01c207411144d00000c144c6046000781d441030b0001041036900c0302491510400007071044144070307000c51081501060f0002d01d07802e03884441c102c0030210300155004604200150759541d1000c3c2c00040103840000c0d0841e8a000105d40030049904504e42004d030000a100401c0b0001410341c140d009400145c0f83c69607211803060540d07118242002001800520101c0c4491610200b01e0384285654209084c070b400742c40a84400340d0380c044441e0302c0c2a40d0301204000e441206401000600b007021580c03124117040701c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 458086169 1250 458084919 458084933
    0x16030215280902030102160506070507081b07180f060b0315091503010e06060316060f03020d0f0603110909030c100b0f0925030b0105220b030a020403140a 68
    0xc407014020410000303a54030148405540600c0b00d035030f00540203564940941403c1c00c03d941c20703607400722004e10854001808584c410006c1c6c5181680c440c40461414142c2040c1280503190031030303940464041c5600c001101c00c61801624902c094250000c00c0d0810740006550484005500c0203002120800420844804d4110064104c0302d00311801410307500c0c3e07200303c00c410740c0340301e03042a42540c070b032180720780c50f20307070001100c40c40f40100320101e440c82521210105200c111920412000c40e1959104410715806500030741090341306603034002407040c01ca00d0312000303450a40d40140c4144038420030f00c1c0c1c1c113818980c0085034889000c85c02545811201e08016990790404282c0200f40c1c2d0307a904040740581e0f030340040b04512002c010000c00450070240c41c000d802044074115480c450106506101d1264028081d140d0180c130140c640c58100002124001001e601800c111001090781307120105080b00800059802681c3c200c030f005845a0a604d0031300c2c4443c5182d21000e1890303105800c910001162 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 458087419 1250 458086169 458086201
    0x40e0109020318030f040305010e010e1c03020c070f05122d010b28080705060d05270d020f0a020904080703021203190b100c060b0d0816030215 63
    0x580980140d03241e845843d4501204040800c19440780400034441746200d08103c041e0003aa406031000700280d603104c5071303034900b00c44030b612990344950130010f003001800c0c41c03140003c0c00302802410054600b600009419090211035007100c81101d040c4003061109051005840c605001014005d03c88009144158183c03130301c1e92400400d2030300150300600134400003034010200000c4090511509248413070031101500c01c0348252041c810044010005141d00c00040c44004c4480240410f80340c5014090101301500004240004840010020b084401e04952855009032442c401803d090429064002e00b8440c0f00170007007686a100031011800750342c4065040e5006903020413515641c0c00319240907401c101150794544203a05011080210003514058072400d18002c59030704105281c40282086110200342d1103003000030341c3d04613440700080c48075840b043d10303c08014620f4031002c0442c0d41d101d40951000400b0746c00b000307590400e08209501088104078010f0384048404151401801c0d082000701 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 458088669 1250 458087419 458087429
    0x60d0308061302041d010302091014092518090c09050f15070f060c1706010f0306180608070b0301062a0804030b06150a17060a050910140105040e01 65
    0x10303800d128504010b215904580040503440c0d84000c41c2408452140c035960402d100c00d030b000d030106800040d001120300b8180c08c140c800f11040300310450030a40902c09103a000422441c05500181d081104484200c1118010520603548225034a107240c001c00c1d004030600e5000001c0c860520585e108001d80000e1030400b41d81081c4d51f203e00340d8045e6000242c450082c0d02040406007800140b6909010b00c0c11141100180144014003585a4083c8100c0310f102108180c40240ca441e403020410661040d1002c81142c1c54520300410741c10b4640c800f51249031086c6540131405079503000c0420081d8401d2014800804107540d01d0740c250343c9000300c054035604140310214004028a0784035900790701c82c5030400303251980118000751156160724000c110740360207645003481020301c1ca001d02000160a011114040071320345da201e0400450109840021502400817036100c070708200045925100d0f161524414555120082e01031071500ea2468550300960034058100142000103000e48051014010304481c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 458089919 1250 458088669 458088679
    0x2030f01150614190f030b0d0b010501030905010b03010f0c0e0406080703080309100c030b0f0a05010e040902030a060903030b091f06050a020a1403042105070902031906080a0b060d030806 82
    0x1900d8070918400c40c4c41426010b140d08421048030716102944000f10704010381040c3c9040100e2092903080200c500c81c503850003010500d071a00107100a5104c0e03040f480600d442000042040420300c0c00190945021044c20040940d0700d0400103a140e5014004003c071100550302081101c3c200011a80c0750011808003030701885002010664103402040314210f980c1408004204030f45201070020702805013034040521030b81004500c0c0c4510f1402d1f540f07000032284140c503407442841003001440042d100c0b0400507079141c0079000520012903140c0c0110340e01d5074031a0340c1c0001d224036508100a141900902004560505000f00c075520f00340b080d503c042a034005050054603070280081c12031030003c04480092028001e24068000d007140000030344103684101f503403480440c0846404401c0c4140601d000351040d8820300302000300700c05990007507801020020f00e0301d00408041c92101d00359400d0391301c034044c10f5010100070014440e60000040d0402e908a502d200358440c1030310300800c2c1e004045c00180c410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 458091169 1250 458089919 458089937
    0x90402090c1306020c041109130e01020705160509090d05070b0417070507061b0c14010314010f030510020c062404090605090105180303310f02030f011506 68
    0x60607801561200b40031212080c10700c0e03031200e100a44442502c19264010303030a20300b1052544051005a940030100940710f510b04400003e0a800039040d8903900b48d01c1558200100004a803090240001d40600001298081e61900f0240700c03800c1c0c1c0062200c0480d803c02d04481c10103c6d405001c96101c2a080001d000c001e40325030800724034403004070300071441c001e9002030040104140400c0e00400c8034496251491a40d0301106200c1c03040c40c400c0700c003e2148044200a010b86c239400c4608281c003200615002035080101c3c07c401100e41000c2e081442c1d07020340d400703041040050410420796000910a029401c000d5088200c44d40d4123005007010103c211030258000110704040029800c0c4080100184500301050801c40020003081d1880c840341d508000c009602000d0111403a04180721010003145960783e295400c4903880c5503911000d16040540822064241d41003004c01d106502036440045000d103544109032614074003140002c41641891040388050b410844401c0440b1041c0c2404c1c160 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 458092419 1250 458091169 458091181
    0xf04050c040606032405010207030303020d1413060507020307020112020c010f0f020c0601170607120e03040902031501090509010b09040e0d020c01090915060c03110d020d1d09040209 80
    0x40049140140d5001480c0c40c40000d500c50340b42c1c014529011400e070b500034100382c0340115680900b0540c000d842c003507400020100000b900c079038010140c1d50030140f0006248100c1680b8004000b801362001d01380c20b2649041e103c140150b500c1419080140c0d0700040d0715001066001034120014503102140e016401f01d843d000fa1031080d0000385038a154840d0420001405210410080d0010072007010244954030021070140c12100b8a00400d80c400d40c001c0040b0b40e1402c10450f854036007039101255098443c6a0300c08010750401c00340000d802c5e000c1001d40c1b40d28006c00008a584070340f9105504001c401039040280b0b40703d400f50241950108082d4a544a00140100303016007510461806144141c04101e040340d0703408120005d244400343d86400e0416074900d958410b5032043c4140500c240e803032000402c007050040840308502442801d1111060000c26a4036060103e2440741c040582c1184140b688203a50003000c020326207500030a18060040140003080300c03410010f00003401200b072100401c1c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 458093525 1106 458092419 458092423
    0x3010c031506090b430b070f0c03030b0d0c0909060605101715060a020c03060c07170f070c140301360309260c060309060f0405 56
    0xc14036407209191008042200103610030000881c100d40182402d44150448002c0d480c0b42e21244100305e03081000550400400c103008024844800071031107504070500a05403030700343c07800080c80c180340c8020400d4910480405004003200341e05c005a0705960780c11072141c0138401d200034060380e0384d41c800788400ca1143c1c1c540b0740003082d030081c0d24441c414642004640d010046003105441070740707104c02098050340700c10340f50030058004802300b40b49800c08010090f0403070b001d521a585428201c7c0c039000c0645510071040300c007070b410000f00c031007100c7d48100c2038900a5800410f1001240e41c0c840b038004860740d603104058003075424915004030301e1890038003043e40385c805e6001806a4480e00441c0c440c160810103012024040303444804646284080208905171071544168082d100141c840585008400c0e1038030f80c0b040c1410401c0141107000410b400ba0020804680f02015886610301a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 457913669 458093525 := by
  have h0 := BRFrame.cov_init 457913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 457913669 ≤ n) (h2 : n < 458093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
