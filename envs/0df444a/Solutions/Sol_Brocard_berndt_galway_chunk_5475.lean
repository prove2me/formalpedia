-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5475
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:59:10.068055+00:00
-- url     : https://prove2.me/submissions/63d016f3-25db-45cc-b46d-9f3877189a9c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 984532374 ≤ n < 984712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 984533624 1250 984532374 984532391
    0x80c10090f080703020108010b040503060714191e080906041410050c03060a0503150403050c01090803100e0603060c0f0a03110304050f0105060114180a050916031a1c06 74
    0x8240000650011400c2d640810414800e6680100b8003600505003203c10fa490141001c0c0465143c19020b01041c0c141700158000c0c0240074074603829070f03132600041c480040c0b40d090000b9000303090200d600b442410100240034001e40040c0f1650405200f0158140100442c0d00c50340e5a440d8004600c00340e0b051300303000709940d4080c10107650141034000c00c150b2200a48a08044041022610003640640d110380c0c07042000344040d070059401d540d44290141016500c4112029005014141b80d000042120f20b002003045481e114103c08030040e20781088507905c560b034509007499541c0700260f580c44d002000c00c0c1b0400030f0580c100c5009008102287c0750105d00b0065001021140d0f0300107660071590307030704106000c01300500700b44101a8000030928040864003401c4c845049248514501d80c103103800240c486140720748030501450000e1030054110710851404030100d1510454601c14280001c0c10000c00b02001000341c5040c18000d000101150820484407500c4084600303400b104441203910340303540 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 984534874 1250 984533624 984533639
    0x1c050c130329070503071701062118060509160303080112031e031b03020a0e130603020904030503100b0310090519060b0c1207081218030301230a080c1009 68
    0x10b80c060200364442c0b50b22030030300c0c42000d0508240d520340301495600503c0108140e590111310f5402e5009500c3e1042e5185072100f40060240202440402c41058540032140410207203503c0745203d00d0300403007920740001401c9005403400d52148005030010329040010300c0001c21000b102c0a507135102e400d104050400020000c03602003406090a00425a1018070101d504035402c1c00800d8a0030602d0300b14a08000510041c0c081b443d05030301c09014002d401c9409070154070951041015680042c40c5102a2600d450001c005030720031144e01c648502e940398001246da41004c10f0340e0044588200740030049050609520050078001e121400c040210406500400124860315001d0051250203e40d074600c81220300380ba10180c1c502c40c3c8040c84003000700390080b48080058070b01c00c0c81c84041c00000c80c1c485521341801d80b819244c1c507404500000000003200d0000d150303420b44020741011f0071080d008074001040884000da100c0c50f101e0340c221080c040f58a00d801d084100354144541054100181c85081 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 984536124 1250 984534874 984534953
    0x80709030519052e020703090f1707060804030804080a02010b12030c0c0a0f090b1302130311040c081803070c0f060e060423151c050c1303 61
    0x88406030842900b8050041c40303000c1c400100d00d42c0c401300340c5100d03c004010641d121a5100707001102e2032640410b007042058400c0202100820a4000041c6e60b151501d43e6906c001070000702c0c5000300d02ca240b500054807402025030b28895601622046020f0381c0e5a00c40215552010030341c603046540e50742041700c10b0740d900d0703540000707051454005540710701504084602d0000428a218412454242e04104c2800c0c070309500301c181d803c3d42e0030100f8140343d4038020074100041104096042800410086401e20a01a841084034042c032059a155a0001c1c240400c81d940d5420304e01c0091842000102280890340c040c000d42d5500d40100c03440c2003d2901d9400382c046103500148407801c03003000200201603000720350b0302c0b954600321a411728162804401c0482380c0a2030115602a01c0e0341444101039640e140d00c0e1201c0050407a4026544000c074403d8506114440422032a01514080201c2c0f640300d48130040da100c824240082a001038216155907a0300c0030b140d0520340c481c00d181d0001d0050b0310484003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 984537374 1250 984536124 984536143
    0x60f0c0f04030209240a0806060d060209060705030703030f020a1b0c08010f0615050306011d03010207060914100203090a080d0f0c09030c0501050f1603020705220e0105070e010807090305 82
    0x1c1e6517007984003035040d58024400344007040b03101e0000c203401441560720200d20707a908480300311f4480c0d000040310300e8213a000c1c0c01015500ca0b805035010903000107120021000701035452190781c0c1044061110710f500c0e0124010b0042100004485605a2206816100003846804c0c068520021161796070082c883c2034958441c00c40c15065111003041103513000c0d243e240400b000d010b0500905502c3c14200080800f0803141d4030385842c486100c0042da1f035403007e41c1200d9015802030b50071701040405040c880f070030750390000c19410f4910850b062022140075a209480c02078030f14002a00d80c0300d1032030711900c21a4104410381d5428980d56909001840040c2c460300182088035100c0c481c80c02d01d1400e08460070040d582c0642d051140811003d181025000d080310419200e84109407400c02140c2801c9203403400f55000690000c028200b901f40e000f0444020540000008006009442140c007151b42a42d10542d824008500700110111b0158007648805901039900d14006040c2e46d62070301d4036441d080300c02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 984538624 1250 984537374 984537391
    0x20d1509020426030906030a1b0305071b03091e091508060c09090402042705030d11090a0302010c020d0501141b070506042307090c11060f0c0f04030209 67
    0x2001c00a154035a07500f4080c1d00b0008201d50751044241c1034030f94582c403d1304d420354410701000000800c07403440d6900c081c03c030844040c00d6403d60303c9110000703002404240c2d049800b145943e0a20f542e6007000c400705c1c3c403280e58142c2d44c845126240c20250b8001d40145059103100c0c0141107000f00e03d046140c8500b6400c0c0c10f00203807060400e494588040c0c1042806060100d103210704200100141c0c0b01c003d001a0880d90550b000a40d0030701c1c0f0700c00c62406402c2c00d003008404810500c1d5800600c800007000d001c00780384202e0200050440b00340f42180700d10812050307640003004140208059801a5042c1c04200d002814a507040c810070780c0c4071400c41e80554403026080109106100e40c948001107000b59106103210914a406031a480e8540d071031500400080200000c0c1d2406802c181d14003d0190b54900200f00321802242c43c0c15402010f4031540b186940000c5980204031100480020114029814411a603006171116644d8000540c0701c034661040b0030380f040100000603140c60380e00500c02c0020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 984539874 1250 984538624 984538627
    0xb01030f1b0f050c1912020d090b2506060906050d0c1a0f1201031b18051b0a09140a15030b010207050d03020318040c090e1e01030305030703050906070e0103020d150902 74
    0x118a401c00300e1b4114070400703004560005806002054014045009503001d21054079291000042000c0c02941d007403000e03501e486652100c031820400f0325044042a0f504060381800700c191558180001c0501d5004040c0456500100400c81d0b28600240c03070014031951000d040c5071001d01918840d03203a201c410904078a1240c40300420078482e03944d00d0450400d101d000303c141824541022260700c0c81d0040019440682e031000846d090300d84000d18280810340c038a60003070300ea16031740c0b4014118050038440c205aa00c2810324140740b0346011441001620710085c0f04015850b06550200d0007010300c00c9095056124078171000c54030303559254100e000184070750300456a8007100446002081e0340500302c1800307641895480c070319041e004080c1c04180d913505100c08006544240485000508104c034042000040c14004418554880011842410b2548041c070880e1203c602c0c1554690084440500190740070032074030701542c0b090f0014030640030805000b18140003110504240940941c0c002d04010b41e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 984541124 1250 984539874 984539923
    0x20a050901031412070c17011410140913031805060706050115020c0f2206091409061005090402030307140102042d05061308030309010b01030f1b0f050c 67
    0x104028030207008580c41d00c05400e001a07541d502c007003c8600e00a58000200a08195405103001d41c4910403240344c0e41607401c0c240c01d160014442c040355034012f00c400c030401217103481c44600b009840c9038003910100c0405a6280040d440032288413816407000c0c9001074416400042c00cbc1c0c4c404016100d40c0303024440009095251488151100051180f40030035900041c0311a095556008804402c0a5081d50030010340d03522a40700c0303a1603298984e0038614885c036000c40448c001c4179503440810395100e515001c00603a25995615691900221a01868500105800e000341c1c11301c1480141c0107403002e02101c0c10f000c225942c0d2215500500c80075080c80e907000c1420403002c00b0320260140c1030000c2c2e00e40c82e89440c84030341c0c206007030450714007441c3c1c00f41c4400244155081d50007a002c10050148501340c94882c101142c0c1307940a000e8500000d40000c0c18900025003040681c800e54014a070016010305001c40d0516054906582e0388906074280081407010404d4000c007448240481b04501d2541a01004e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 984542374 1250 984541124 984541163
    0xb09030a14060f090a02090a050a1e050105010e060412060216051b030624090601050f0c160f080c0d050309100207170102031006120f060905250e0904020a05090103 72
    0x40044c403506a0340e01806125000da1280300300c481c0c00581008011600d903944110314405014051980b44440424220020400440da40081d059410980e1560641d59981b000c02c280c81c01280140c1441d0010403c004c00011a6580140410221140070030b455035002e0b11140c4c1868031440f84501845155100824585014001e80f070b4070100c40b101c500034610640e101030000c1da194a65950050800102184250f8082c0713042e038a5a40703885041030307668004000c080b41c480310950094000b68040314008a04052959802030030745015000420b00003840f04100108100c14000546807070200b003112003480d07150507101c8a91015142c000f0b0079000e19280c240044403080d03140250482e4410702c240030320004421039030412a0b9561800c140c94811007800c4c40005c03c0b840090100803440c08e88001380b900d240c0e420903031142c000c5241c010381c041a6030010078005200c081003c8000340344085001518a07281e0101ea40040c0054490f407005525000400c182030380c06c2c2c0040d5000980c9400a42822 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 984543624 1250 984542374 984542401
    0x5010c02060705130614070f0c080601090903080f100302030d030c020c1c030f120507030903260c071103191b060c0204020a0e040603150e011103010b09030a1406 71
    0x520601d4501e2038004104401c00c4141000d000e035004002c01c098140c81044810003d1f10340301c0f500244100a43c0c2814070304072600a280c0d104281c0b0070300031240002025861841207605a680544a4250315130b905480a103040000512070480401840e1005c00942c80c10000100824055200010a81100040030b444c040300d003510a80304104e0762180703516a43c3c48000b5002d006a143c140000c24003401c0c0401d4440d010a600c0c0c3d6001146414200b110040c0e1580081c5e90755030090b22000340b581c1c810f9202480000114001d0202c0308000d1000c01e502448103001404d18500501c4c43c0070340c0f500c0780c40000e81004000388003d410700300c0410080040c04180c20300ca21480c10700301e0048031110300d04180a003d245503000040d201e26404034a6000135405141c0da0184220014400c22003185c03289890035064000e80b0b000d803600c9280c107000080c00ca10501c121041016003000d2603095038a001d0038900e02c0c1d403049210a03050b01030511810f001a0700d401c00c5124008411010348401d1824401c0450744 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 984544874 1250 984543624 984543631
    0x30905120d0f0e0307082b1a060a081b04050303131a120601120e0609071502160b0a0207030515011e181d0a0c090f0603020312070f080705010c0206 65
    0x454600043e030182844004100c82c5440e03480301600c0c7d104c0b80088441e0544100d2000900115031259000890070000740d800f0800318150f9001c0c100303003001b5110601186010388800b5502003410b110100b40c03002207114407021078070104080c0c41d1405803a0b801081c21358000120f0030f000c50082010602040a041d80070384035446580d8029424403603444070b22040d03044007400c944e0500a070004168944015a081000d46019910489a40781040031100759210700c284907450b41002030740c035600725040c408216120680d11548080c4c10950806140042aa00c115200010340c4554800000002c1081c4280222505010034082140d0702d400e0451210344c02d07031906101511011001406030818041500d048449030030780c0010100102d0403604c401c924982403c1a6500c1150702400c1046442c03611300040e1400c203c0b040c4180103a500000090b1440e900000f907054200212504905008002400085000c0d060b0020845141d0726205110792181c41d045e03c0c240d440b0baa07004402034042250a41 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 984546124 1250 984544874 984544901
    0x1050301021207030207020a0e0108030d1a01020c01080a15080a0309080a2d0b0a020a020c0a08030415031b03091208010e0a0213090c0801080f030a05071101030905120d 74
    0x64044000010750b415140201002c05150b40450200c00350744820840001808a0811040032541c49804455403030700006a9810780034180f02d001d080443c1e10304840400d006068000301400c1d083d1000555107800010100c2c9081c598a20011513002099107081e4010060480a018043c19500303008201e84080d4000040c1503228907005400038030703000030540180085010f0b0040940361641c0d8810001c49850015102c2e405400900c03144d45140e80c0204000078031703a009c6945984001050002510700e40c41400a1904180010040c054030503d2240780360760302d880d0010b5440292096450f010107800251000039907210511320402c003902c45207071140445401c20848a614024118a090f4030041a0980031500030415181c4100604120b8000e0301c4120000c2c01140c005150050007410241700d180690301c92080000000c1001004540702c0180e00c1d500c062038030300d0035281c2c03a03240c0fa0082e4400b810550381e11000800f041c0288548403030043c0341022680d50b0f032140050306040c3d4881040c440f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 984547374 1250 984546124 984546127
    0x3080403090611030f070f0213150f080601140315040506060918061914040f12050c0a0b0403110604060903020c0a0f05090c13080307020102190b0604090c05040c080f0105030102 78
    0x6458840081915885d05000c07001582d26081440c1000b000071480c0c02c000c3d00803620151580d8064503640110304440740b1694a1042e85035182d041c524400800c0c400c24426030081001880411a5a21090346104016044490955409040702e0030218210703019a01c94100c2000c0c44800d240c440d01c0d1170b410000c140f07050900e030a8085000c0d515000082c0c0a000c14004c1e0b610040c00100c00b54102071003910004807969418546030402e801c81c03540c0c84000321125621600c2600e010342c0101d0036907094620390401088194403c0e6140019031a024009800388541c0c809041000c4900f00041c43c4158820100418000a0740c60041d14110800701c41d40d22071851900248144490284088212241280c00c00919220f030000303c3d03514442c414088802d554044c1012540c0000040288200c0d0710030b03800c840344842144613004030a0407140000307007040300c0c4c1c0c800b0505520b00f6412030341a1902480c03038108150398880001d4115800a0480408150b844040012903402446e482c1d006040580095 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 984548624 1250 984547374 984547397
    0x307061205070c110f0307090c080a0605090f0a02180a06030f060e0108030901082703070506060109060e040903350115021e0330060a030c050f120109030804030906 72
    0x1300300550141e40e410b400340320040901051990208001c2c402440315000030007003280280001040803c0413a8a403030b000381807000008a40c10032a183d00d00c5410718240d000140d440b00418080a94004401e81e4003600d0081801c124650307030904980014000d079100014900400d025410a852682c0d00003000b10500070010000000c000c800c440f00c90800b4039048003039668102301c816046848540c40100031201d803981c87c1070030400000402d42c1c1405201150311540c5d448004454541c454001d2074005048541c0174503040c24560001440ca61103070600420307480540350440d130010307001403081e004070342201079044081119640840c050050004240e4043c001c00130080c2d56035282d01c8040c6051202e01c100201017a5003030081c0c501030740d1002e41481c8040300366214400801802c0301103e0180300510046011468004240e030112a07124016801179403030030b02000395040d01500300c0e54114000300078082c9594801c0c814803002902ca030b00c5448581c10705d0309001f0403040c4076400c20810300031a040c11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 984549874 1250 984548624 984548633
    0x11b0804060f050c07060c1a090304030303020a05090d03030b120f0a0807240912020a0210030c0203070602030a0e0f0a1119030203010e010506130204030f17090307061205070c 77
    0x488054a90320b040150121118200448141c0b188a4019140340074050700840c03101d901c0000005c07114041c00341c0648602d581421141c1404e0300380c44c0801507501c108001c00c0028003e4028084c0c4270302c10305005007030100404c08543c54403018141100040d94070840781041c0c0c0303800300705482c03030500da0790003014001010300c0030030b0b81c842480c44054240314000c10358004100d410041840d40b400720b061703031001102040180c000600000c800c1280c009803903141c1401e50728030014003c40c0d9503400403d08100448000d2041d00140b60041d82c140850208011000c0403426600003140111032510700041c0e40e089064406041030810ba504140c2500032428113008200560101c10401204480c0b2456101c41c0c410451070000d082e83c002500340d420164001a101c006611041c8030f4642030b035040e03120304100402501240b0841c0002400909142480d50204000010030170f40008a910f10034a08448000024070f0f00d076642e40200c0004249500005071103140e405200d80102407414500400d007501e948 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 984551124 1250 984549874 984549877
    0x180608162d3b0f10081509060d0f0813060207050a0f0b0304061a1201051b1e03060d1a0712180f031701120309350a080301060905011b08 60
    0x10752040860554582c1141c50381c0c1c80703900540c8040300600e501310110400001a2001c0c20803a843c1110303a0b40d040c5140514105008880d1207080c0040041c1032095081e915481c51340604241a104950140010340003029958a0100500703901d80040c07001614140800c071a52859400055100030344a1007004049044401c0d02c1e007140c0d01400214048180080540c29400d2561246034400d024002032501074106500c1180a52420401012140c0c010042c5050f10b11a52140252100d5120780682c08a1000c10145402c4003000b09600102100d9485034489940381d100c00303422100a0109200c506500000c01c1c0302c0f09020030301c06102180c40800c448120303009070100230305600810511070081601c200908580400201d0b0074480300d50f11400c43c4c10b035150034041c0407804030350800e41c040360000310082e615103115900080b5910701880c15004103481ca40d42d40e01c1700f089200301c090b50000140c20790040c41c060300d580e95903211140d15060004001401e0748011440c00e00301d450b100c4000c10081c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 984552374 1250 984551124 984551207
    0x30512090328051b030d0f1b0311060903120a0902010c0b042906040c080f061002070b040b0a1409090c0901090905100303180608162d 59
    0x2c08019024004031000301103103807040002091401512101580d03c40783d14000c0c0d920368010307800c54922210800c030070758189000c1080000411580110400440404005440094400c4c82d00035002c3c2d410100303c514000c81502d10010b1900007080101c01d080540000070fa020107449030a1040e000b0301c1e00080d0483c3c48190010303080340500d200060503c40300e28850040622400d03400c032140c1000d0607402c05820020303584030344502e040100710200301e40b0400b82c030f40c0074a5501c0c501800680301d4034200840380c0900c0061400751700401c540081c1e640c1d0341c40c014100400d80b44101c15654001101d00a00c03005941c801c551484a05214006868403101d5025601a0113020305c65074900c0c6c880010303078441ca400ea100d1351840c2e007003100b04841c100240f4000c90841c0d220f034542d48915a070b400b006c000200030500460000940000014200d00c41c0d1070f8004801c80c0d02800c00c04500c405844542144c00d030b80e00c21407124548003080090255903c40c0d01c01c011401003c0520300024118100a6940d41909 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 984553624 1250 984552374 984552403
    0xf0501030c0302121006020606030a0b01050402030a09080a18050a081e07180b0310020309060c09132903032b0e03070f031b240f05100305120903 64
    0x7400d035035412070300070350448070001024009150986003030840400c116100d0b020b086e0050040202007149814009040c5200c15032140010780030b40c1c00e220a202c003e410080204c4943c54556000d100400c054100800404e000c03a60365011844250b240400014242d0303000d1409000010380400081c8004100d0528401c614900d05d41d011020038541e514101554200300e01e009080702d8480c0002807a5400030504400c281c06981401c4468442c0c0012400103d504c08007c1d0412400030b0202e1607408010088554024022402d0160340380d10302c0d040b00c040d024a072483d070500c40e0400300281d4202000c45a003440460007540b5002115102c02280e451000045c035030001d01c244d0345030a83c08035403c03901303000c100301013201d80705c99031814606000e603a010401e4010170382200c150102c18030003440d5800c4003038200d0b00c580b00245400141c8030300c4013030000d106a4060754031030400021690714001d01d4019240c3c505080700040c08c2d418643d08001200905c62000503041007074640350f0b1004108041d031141364 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 984554874 1250 984553624 984553631
    0x18020603041511030106050c071a120c070611070203011a0349090f0b031302061204030e120f07050f0a090507050a090602010504030909111204110f0a0f050103 70
    0x45200c1d101500001020074819800400013046e03840e8082c0140042c40d14000c00c1301c50711541c82d4401418807160086d005011402082840010140c8600d0903030800008900c07035207480440d0700d4640449008805601172245d0000d08082036160034024403442c04000c1824149110074600025994100b59409480c0e2401207a55180c02410541d00010500c0c1c0b8040036224a811076203140d9a0b105c04088088003140b030009001c03c004007070041c10802c0d00d81918a0b10300e10349407505001d802c411503120803607000400300503022004060702d0050b80103a2090322051111103d00c0c0c10042c54000d00c5c1a038400c1c0d58050404074000300d00010320001200d905854603020701041034085481c01d100e5030059181a42440e041c460201d620200511011b00305a8410b0540c0f6260442282a140152800390000d01425070506c10303120542d0040038005600d606592034080240400503404000311015103179219252207422050800201e58a1a50f03003c80e00e0201050038070003848400129802050304041d0f6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 984556124 1250 984554874 984554903
    0x2060f01150207050303031005030d08010e0a0216060c08090601060e0f060903010908072009071707111005061e0619050409050c0304021e0609060c160f03061802060304 74
    0xd0140f0405044054141c0340d513131801c20030400f052590380c4103441c0030384108540c1e050118481c40c140741c141d4004415082550300da02070300c40060341080200480800030510080c000903500d104401d1540d0b03003611a04000c2c504080760380c1c01e020059014000384a24070b07004040a564051260700c050400b11582ca40311580c000c0443d006002c0604002c020040000740203061041110082c1c6220b94407600850458a895050144080d4140c03001008541c1d00d42e200140081602c0c9243e6100016182910b01040311140f00b901d400c04003008402c0c0c4555410502045050600704244903584e45801c0b80e4103001c190020440b80e06c1150413204881c880d203485020542c1c0b00d1012507004204a6000b44402c0c14450515040380e84203540c01c0748690044185007264000441c440da0300c00b00c000340050f0030402541c082c080c15502c898a221810700825041c0a2190a130300fa400000e841110080f51080d070652401c00304541d100098031f12061000d000d0302d00143d458201326548650302c103891146040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 984557374 1250 984556124 984556127
    0x30f15051302151e0c0d0f0e010f180b0c0f01090c12030306030507091b020a050c4f02040b04050f0f04051f14060405190905040602041502060f0115 65
    0x9244000404c20421a00d402c40c400400005030011401410640d600e40c0c40c0d0980646600310140004004202c140d00d1140081d03025142c428035000c1e42e41068442c48442d4507030307004504800d40005280d000007140100d4108000c00c0b88030019174400d4001c1001c2c6105884030280c0c1c00b410700c5441001040c0c10b513001c040500c00c2d00304600460b8490200c07201d8948449819000e4841643d0001c0d042d5820020340b0401880041c04031995070b0003201400035010b1080c1840480c02e542c44504c0100d160074244049078140040c045401c54100081198419100a171110021000c40400c001c41c24014401403040810312012201202c00c100ca00782c1c40e4428140c0441c17505598a02c04540c410300e000b04001071940e40240c003d0400c0105a40083c0302512030707011034018541000500c2c1c10031000d100600103030420b44280b08000d002446501c8203190348034240707400c0c0d6401701c40c21030f18550081810010715041001c0d54030285041e00140c04240382050340046406c405209280201c074600c3c0d40d23031511a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 984558624 1250 984557374 984557377
    0xe040b041106041e2117180a17060603030a0905012604051e01020f0403081b0a05070302270411010e03030a03060e0601030203060d1202011104030f1505130215 70
    0x62a440c3c14903901061480c0d443c0300c152485100355001511401040c1c07003810b243e4645c4040041d4071000f0500d5281c80b000c0703014000e80000141c542c203d00044469001513490a80400081030000030000014206130201402d0180281c0498001e034020300101a1541d000001c40055039000e1030441080940001c42601d0307020300d6030301d032400046a05c0c240418401d021510802c003410111f840001c1c00304440000d8200e10800b014030007840f8091100740b0015032880000c083d0038403141051010350324681e00503400c0c16200442100c15501030b0004100310b060440312140720710f401c2083c51021201840c0b07916603800c002080144144010321401c00780d0780c0140c2d00c9545000c0050100c986841900301c0103030062009025503c1e201181c1c00001e01c0c00c1d0302c81e000b102e20032100609409075980f4690340354550680e005500805654036200035141c0750b02e2450151000754028000c269404506003030600c1240d80307003007480a40714100010025400000402c2000c4c0e26410748130281c1c22600b040d0f840015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 984559874 1250 984558624 984558629
    0x61c110d020c0309030c0f0f0913051f0b0a030f0b040311030a030f0f02130e100306091217060312071707060e1504170f090d030809070e040b04110604 66
    0x152021646039100e0b04000050040b0032030a4048400301c035280c80030490030304154132a0991182840c0c41c03051060410509881d0480c48002e041d070f804d03c2441d600c0d02d013007062407a00d000c072200e000c00310100b03071005d10301680d902e80d1010754502001d5400c41c0c44045075584400340c0507004881c060082000c140c0320380d000218410245c0180e82d00d0303048070394006003d404965580300001c0c0c00c00081c7d101441d02c506c204c0b040048890700406000f8030b4000d1240c0c1500f8001c01c9400b50f80c17040400003000c900c00703026082d061032280c3c0b007110030365a44242c0508030030403030035110301c00c3c800f204100400780e280028070441140c03800703043c1070302d9030605d00d0816461000090300c50f07000080170407513000b0412640c000c0cac140002000241c4400030464038100321a0301003203802910070f0b20400712010741200341000130885040404141440c01405001081d00d0054805013100020203010800a032108141b005034040d11824245500600f0940c44002c400140a800500401010503182e11141e4415003103800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 984561124 1250 984559874 984559897
    0xe101211010e13091103071a0414060f03010608060a21061113030f03080f07080105010c030e1801080f0304180b01091a0d0f02250623010f05061c11 65
    0x898680c520b0030440005c0b510036958001c1c425070f200810500311504d07501c014020b440903640d040ca407420b010000c0001d07456016a03080141042669a0441410020340c064201c130b841c0e03641c4504080c01800046d0b52194080041c0c800070701c0300d0078039441e4040d141500c026003000001c42c60344040b1072540d06601c10401d1040115501724000010000d00e4005200454000d1300d41c00310030b036911050301e83c030003030111540000240d404005200070340c0560110f49010f4064540b42d40c41c1b070220b034049100075014110440c00440744500401040104006625074206481c000d503003410314141e61181c91150500591010984511a54819900c00c03c29140281240030b002a170007500c0c0d41c3e00015680c07105c401c0b0044141014141c0c14482018001c0b600844680240441718a2011082100807104003804032507d9803600c009000756004092103410290405098a260f54542107808425020075800103004020078040101820325819408507100090030000c0307200002d82c26140c0080c0302d030202113017 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 984562374 1250 984561124 984561131
    0xd030e0d050a060e010603021008040507090e030304120318031202070b012303070f03150b031b090a050615160203060c0705210307030c0203130e101211010e13 70
    0x101031200c00680e862550340a04010000e288031302c031055003a6000c40c000a50040d403014060940700b881499100c0c0d010b030041c01071f910315903140d401410036a01e0981c0312000c90b600210a100910041901c45103200984c2e040030080c0e45a41168006c04039074807034000d41448180c41025036200e04c1034045070086580309100c2c50082da101c552a19866120501d119030603c40c824190303140303080005012042d20b091080c0002c98030320b103070354514020000c880f20444080e141c00b210801d5071020014540f54a9500c01e6001c00e50460005011440000034070030103109091a05000c45515403a1030740c0c0310901181e0320b0680d1945455103031112000744010081d094407454040004500f6402c003e041c0c81071080043d10f2142111048840003004418031503e0200010008500c0070781c080c0c0c2c03001e031032110180142e03030506600481b2210040c180d98800d403510aa04410007409904401540014090b01c1010540302e2055440310212480c1400d2002c0c10310400013209034055549001c01c0e650510b00c031100b403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 984563624 1250 984562374 984562399
    0x10c11042c060708150310020a05120412020d0206160309020303040f12021f0f32040e0115020d080a0902130c0807020309092205060c18060a020c0d030e 67
    0x1a03840c0c0c8100c8a4100240d4807001046290002d243c11702c0c0400b10080c004d100381a040039040d002580040c80c17403800d0000802c29807031800800e0045510641c060b415001e01d1003134001c000303800c0c603010540160441d040320b0100003101d10406026804c00b0b0b000e290000d0b8014243c400f0900d0741c4680c0c0c002002c9034144d090005070b5400f040d00d00902c1507100340c6443c088581d100340b103602618295041c120200e2107800140c4c10161141c100078402c00d114500301402d02603e0040303000c15401080e1104501000000c0901c41c01d07902c02071441c0108541e0100c2c600385006084000c0d00e030a458100ca00030002100b0220b80183c480c1e070400b0345032a4004210143c80704d03140e82c111004121900c11800030846a4001aa40c64008002c3c0c3d480b20001401c10303902c540c2e40404080404085d10a11240101c90140305008541c0410035648035455501c421940c41000392104001c5a1a411009204001c10861140800d0340402ca040300a20240d80c0c00c51843c1491905542450040d4941d94000091500b207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 984564874 1250 984563624 984563711
    0x408121e040e0105030709020f0703080a02042105060714160614070507060e072106090b070f091a070b0601020a02030d17130c0605280e0f010c1104 65
    0x102c3c102d400807011074030815918030b004406ea000b546040f00c00b03c102404060003090003100c98551000410000500d016110015172110301a00f24003110386441d09d84082003002400c220b82c036000720701820410300d04040c0010b451818400c0710085061800f9084611082041a41008040f60b8140400d21100c2c50084002070054120090544510b0b04119400710340f80d00114145003a02c4003225004403040d46002c2035001d800a00c0411210a41e6803030f4468007103000102d107030b0b001308141d0380ca10b80d001c50031002c0101100015044501e4000f81ca0701c90020710952041265445a8060521a607594501c00181d040c02c41c200000394240c007901d10789450b02d66110b042c420410000020140e1a62142d0205014008210340020142010b0030381c203111150244002c0c00180c1003000c800440c81d180c6015451400811880020200300940c092288c245059034060111250a20341017113002800d4854030305078602ea0320700c94000c1d607a03240e1645940441c0c10309092566200c0b90080a80c1001c0d000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 984566124 1250 984564874 984564899
    0x51c0221062d01080705040e030c0d0e030f1c080702151006090605040302030d0c262106090106140706020c03040509091b01031104180906110408121e04 67
    0x80c910389000c1c241c40100c040002c0416031410ba402513001822a1401e00e0203001c01000b607401650024403083c1302e0549c40600800c942059900b8a584032820042050141850714810180144d42504115041211000405600c00076115145410354081e111008182e081c00c4100002c41914026001005443c3d000c10300403000303d8606a50306604660344d00c0044a05003e14000294160080c2d456019070621a03002c8600d1207005403802e0171280340040c0203001d00c988034655144214000b1a81400d005080d240800078036041e808000d81c40d250910014054280500a503014090280b1145440c03190b0b82c42565140f99010100310b65030b0204410b081d07a0381c0c0151140a208205035000a8100440400c0700f411114180b01c4a0440d41409c800640103450882d400c0340e007544041c0000101c3c0902140400036001c515400045d142505007440000e4036017961140072811f0b420001040031000024104030044204444251502c3d180e0386403145242041031000e8400c01c01240c085401180c0c0b00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 984567374 1250 984566124 984566161
    0x2070509012130110a0b0406050c04050a030c0f0911071b08030c070509090a020306070e130921031824092102120a050714100213051c022106 62
    0x4440340304c2e80e880d451402e13598004a4000418806900303000c1000503080303403c507075007100c0d58031031345c50a16850b1000b041d034042c0e05500c240c502030300403142089210340088000c405402d9108040c084901200002007103480743c180020520300e10442c584a60042d042108405031102d03030b040d240d890054404240c0d480c01e05020700e0b846100d228000c904c0502001845c0a502607010b03001d01000d94030340790140d6a4118a90301d9541040c01d0354210000036001d44101c00c1c04603c14024017402505d172800c51014131071100390a105051604e040b800000040c0d1140305080340d48040a00800690302d882010070b5001800c2083d85641452890010400380b0b05040a040c0d48442000305c02c6000c42e00103d036192080150308841d04020840103e003680b08500400800e03004503080101e02010315081450554800120f091665001c103c104501c0700300c84200000740000c0310800071819000c10a00c19000d00060024465040380c6504d080c1688049400c04d0107010341820343d1003038a0408900d1101040b6034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 984568624 1250 984567374 984567377
    0x70506032a120c0a09050a0e090c0306061309080d090c061403070c031d0d06050702010c09030209060907120c0815031b10110106090c02070509012130 66
    0x80c4281c080666000103884180021100114180d11a0031445810780c1c0404c8804082240008000c40c4c0c0740ca43c03000c818020001b607440446240303808d103011424604008580c500ca82c100c6018001155604662880300d01c45407100024820031170301d00750390b60703116030788808440b142024182c8007803000c6040c2500c00c559254641d100c07540340902d845043d070f210848201011411100c2e000c8007017849103c0c1c010740c8142c1c9010304040d00d84a0400200040407048003140c40c01d4841041011070f40d428020058410001c0c200320f0040c03403c2da80000e01415000f01042d0003580c0b42400141c80c40d20645d191300160360800c600b0001a119260020b124560489640143c00310004000c81e103801c00103091540e0105000b40080302e202c0000401c8070030302042610b40e00b04001d038086804840d500303104071001010078000c00a10800c0d9414040d0400b0b80c2030344058840d00385000104408180014424070040101e41144a0492203203882028008080d0076a501c015031208500304140050100d15030310141d6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 984569874 1250 984568624 984568681
    0x1095409020108070504031e021203070506160509150c071d0f0c0405031b040b060c15090a08030a0903090b030a1a09160e0a05030d021c030b150a0207050603 69
    0x1d07840c017560a48560b00c03009040c0f50310802c8503c0e101510400c0f86011610060103261829030422403c2d25603080140305884c031360041c20910003009401000307585240428142141460740c000002a0104020b4480d25640c400c002440c02e24842e007400060080d0608820310305007240b003040c0e800e11264084032003510504070305020584044800c0b00343c1c0e04403030000b0010719003000041544400110903540c200d0b0840c1c1c640d00002041c0c6d41d900007409040361844001c0c00031f070494040618103500c3c0038002e1003254001c0b500c00c8011581100803070303030300103120900801c0951013850103e900c0c038034983c0b1065100401000b404900c05090300005a081240031400003040300c814100b05120000381c507803400707012503811841640d60169003031030000c2000500c1d41c0d00303d50351034021a080c0a0304009610042c0c114900412680110082c0b203030710042a40307010400d0030513030b8000c01d170701300340f0100c038402c81030004160080384910800c4400040c010140c0865120309084141c401d14440701380301e0055800c00e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 984571124 1250 984569874 984569881
    0x409060b0301030c09020c1006090c0305060402070c03020d0f02091e180309040f0906060b0301031407150e1212190c0c0303050714070305060601095409020108 70
    0x400006482c181c03500080a01d03465807404200c0d4000b540424440b00307842c050340044000350030030351081500030004400c020600c1203603600010103c2e44010405441607205211110108000180d84030560303070b0540309403440d9051400c0802c24180054002903001c0c40c00c60401c20400c462403440032100c2181b07840100e0f952a050882806c0c0d8a100c0200c28690780b0174802d10115203815000340c00d031615202d0000502c40c2d00e40d01e407032050707c0303c94108150180300000100b08101001010000c0890032802070001c15040c50a07800c2c2090040c80d4010801c18080030841140e902c0e80710401c401d03031180c0210380480749442246030158101903005c00341030405032401c1026038081d84c210000c1e40d0303001039403079141801d544c4d0540b01900040016031700000069031080e0b0f0240308101d4080a50b00400081405213402c0c4001080e050480e00b058594804e400e010078181c400314079001e800c62401048401e2a0070310711008501840d0040d22040c0c42010511451105a0f1580c0c4000c58540c000c0e6a055a542c0c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 984572374 1250 984571124 984571139
    0x60606020604120f030603060f15050111060a2706091101171603090c030c14040b0102030702130b0d23071a0901050910080901050609010b070305090d020312040906 72
    0x18002c44001e805180b5907503440340c01d684103628001d450403c0c0e003000224662a610f80400b02c480080c13020340f90381e07a1401403031710054071115107900600707013460810110081940740944418010340380105054941c1c40c3d0704044845d641c610010b20490340f1001c0c4801c406820681e0240c00500c0382a990010304400440141d44152441c0c0d0504005e0190b071541600c0d080740e2601100d5100ca5030000b0550740e81c11110026001c80f03d4000110300445c40502c3d502d0030a2403401c00403103540419841a490490764000c1a41c010040e0f40070740d50100d4410070a00104010035014080c0014119030001c5d581c10702c4030403c45800c10200d480700c0c8041c5001544661013910603920102401000820804403c00c0f503420b600007402880390300f006150840c144050b2402190500c0c2c44020043c0129210401b0442006400d100d00756110408403a031004551500e0b40348070301c27486640800340c204540040c00303120603100d040e804241e0a50243c115441d00d1a103c1c1c001120350014081c0800c0242000d00005450 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 984573624 1250 984572374 984572383
    0x8070602030f070914032505030303040302031305030703020901140f030f01021b2407180b04090e0106032a0b21070305040503040605210106120c09450906060602 71
    0x80d0000c2d0042c0740d007240042c04a842e031141e042103051003087c2c5140105031503c05001541c080ea209030002c5455407070741207864400c1c200d11b4100c00c2c020b03481203d0800c0545d4408070302c00e0441e050004000c1d0810421030124084003944000c280c0c1611542140b0701c07042605600400c4801041038050030034900311002103840d0990060008014640c90010032002d41916020980101003418400440c0000000240200480d03900c910419040490100090559400b0306100e1100300c00c020042e1303901b10b45e203150410902030303200428109201640b8004658a4850038003400d9080c003515111000c1c46601012406c103440342141c11101500407899450103801014011a4050080d50805041c4034003240c140d000825145c5c07080c4d50000c400012a6100200c06000c0d01c019940d400001c81103485441c241d8004c0f050180400200110820204100d0382010a029014500c42a40d08000b0103c080450b95510111141900c0b46480000a6602603114011092095405206d000d565801c16a102c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 984574874 1250 984573624 984573659
    0x602092409011205043927020a0807051606050108060103210e060f041d0714040605071202120d02072001050a08091c0908060f0910050408070602030f0709 68
    0x7080c440742070a020844401d0021b421540072044803d5040c2c1085030383e1100f00110354004981000c01c00d412005404a5441e02d80780100340701401e40c5048019103000b0800b01d0021320030b50030400040303140c0c0580d03094a079541c404039400803818407907561168039064940b0003e110403280220003101c0c0c902140a6050b18094444141c2c58245404501009021860b8021006138200c00e1080101041c040c0410f62206501d0301a1892948146490030020b05000002403600b00700312814441001010391040032100c0d2241d024451702d001018a0030305034035001060340d800842c018003064842d0402c1184e80a844014003401e1003400c08200b000010740f040903442d601c14005442003021100a900804443e07400c001c415080782c424038034109502d450007507142d01400008001503c00c010f500c4d02003220036007024003c0c1009061703040c00c004940d0317141c0c2e5182400341056242c00004090109980aa030856a0041c506544c0ca00c1c01d1401d002e16000222540404181c070440041800700480304039449 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 984576124 1250 984574874 984574883
    0x10b040b0102030d0b0d06180b0c031b090a0305060108100f020f040b070c3b061c050312040606031406192a0503060108090c01020a060209240901120504 67
    0x94403913609210005001201c808607041815000b018000442a100307031420348010003011414140c21345011844550080c000c490402003c1c0217021034000d541d0000502011b11456403503a43d80101d0110381441502d600c050400e00408000080140c3d000c6103c080782d20030300c00d00f048041103128100040307004a4a028505250601050007207501601c000e0074018000d1141c072220701e9036502c1d80490310030541d110075034809512001032a00e414032103003641540c4500d00110040d00c5d240700810340c0d07268804110900315110010400602005004984000710101d2800e101c0346010704062014024034031007194011a001c8140d02201c00224002e806030444940030b001020211090070046c1641c1e50b005400804400804100d200c0d03c00005065040300f40ca500352039103480d1001510041005000540e2900210940c0210380e03800310f603a00c0c406a00500040e140c0e03452070080f528516245c003100c50001c4842e00b540d0160860940508021442680c030381c500181c0083c0710005641c81178900a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 984577374 1250 984576124 984576127
    0x9050f01090c02010228120e12090a091406011202161722080c0603040809040f0605180a0b040b01020a060b010314010905040b06010f020c19050a060809010b040b010203 74
    0x803041d1601e810042070494940b0026040807221108201c928544900c24580031000134004840325400c100e6000106032030b80d500f004003204048000307440300141c0000c48100d420010701207040d070b9201880795000d00b6117558100a100437510704509140c000341c600380d01054401020340c9104810307008442c5138150300b40700c0c020b40891998601d20020f8040c030303000200d94018803030b0505104040503907458411031000f0840380e41e8540303000345044c0100090b0a5004800030000c000c080351440302150700e071580544000034600c0d112099440180301039084180c1c8141c503034941c004814110641c1c18026020f0706030802507104100c00700400c5501c4507e500b805030b004600601c02080b00d0b6440300d80c880c20181000308140b01c0c0d064600705080300036001880e900b41e450382400144403402c403c40341d009a003824554039440e080305020f1f65030f0011038201442040305400c803507400c41011040000402c000341c880f544c101e8030342e4409054100110b806180c41d45c0391811103131542c681402110724414040e0040c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 984578624 1250 984577374 984577379
    0x11704050c010f111002041404060614090d1202030702030f010c0c030c0516030c0e071d04230a06060813031707110d080f0f0103020604360506090109050f01 69
    0x5442c00d404001c0b00100740f0045580d1380c40642c9050013500300e0341c505020300590380d03418040f404407200c492001c01800359241400030300c511600402800400a80010301a444491364000a8030640385c00000401d40118010301c0c80921b078000016084c400c5c400c5065030f04441d00b890605003251071130504540000e99a400b454042030042010070120b5015105a500c1850340301c149d00740046040e80200d6824292040c10044400d90924a6030403448a1070314102003000c9000c54402e00d001009228410340d40ca04c00007408070300c080d07a40009200307518038000f05444c0048481000301038600c0b80c41c0200b82407000240020300c075045c0480442764951549942c10700403800900c0b0703042d0024429420b0100c40d55031083d42a4040100b6480d419847e6074284042c0380c80c1c40d8100020f440a0310040d8804c00d0788005100503030324501038400341c581c51502c0c8005190005103100028065611000251000e011b02c250440d002d604180e10900e8269031a000603603a40381c5d40c1e404c5070307030071903002c2598000c02006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 984579874 1250 984578624 984578627
    0x403061a0609060a0302040806070c030f02060105010c060c051903020918130f0f0c15091e0303081f0e010e06060f0703180527070c03091806080604050705011704050c01 74
    0xf52004e5035030340c580141002c1e21034810a181aa0585100001c00ca030340f5848000c042e888031900074220b01c10b1001c0c16465140c00c0c000303403410182c084024122501c419070b00d0722991050080c0c42182e0404480b01d0101e840c1c609015000758008522140200d44800100350300380c02c00320940e8010705400c5100d141c80f48280d10f5488408901c0d40d13003150519140f220700000304100a503000050074842ca1001c070080550000170741000029030010f44200c45d01c440c20000c5d82050412282200c1d01030821101c255502003c10100ea40d00c03105654281c0e040f0203011400e11000758141e4117a0350f50300c4000c0c0c0d40f51984c50400286002e501260090f0fa0700030001c02e030000b442024002d94080708080c0c610000c588031000a50340c110000000800c0210b42d401c0000307181524410150005443d080c000d2030800035480082000816008004400300c4040e001084403075603501c400020301c030b0001170b10403e06051624944540151290754001040c0c00c0e001c0380303001000804280180da2082c010040184000d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 984581124 1250 984579874 984579877
    0x10503041403191101060611061314031812061b130b0d0b01020606090613150503030703020709060509060a0504050714031f080106081f061a0403061a060906 69
    0x440030000c0c0010702c400f4140020a160048060b030341c640b00c41c0410145400140d003101c185500c0309040043d041c1041101140c04503015030010a125014080e210040c1040701880700345240100351803000213407203000d100b00c03001c00e491481c0089680070850b0300d048021658401c02507a0454030000320119444291001030300603d02ca108841081c0a86503844103c80f00320340003549104034441e1104e00341143d40d0303414443d480c0e000804403880c42d010b00305440482c01010300040038452941d0789168550700703119800034180040038010b007200e03030391451844c0c000c1d2030350114401c9425071424400c1c041840d10300149040e02c40c00d80a00302c0c1c000c292414003013001402c00540034405101d81c030070f900308401c101800114400c801420042c2089900c0c0c8140c610000c009510210060f4900b51081c07254a8001c070710180003404000e104100c01151000e00402810150302414010070301d500300442244a24020b00304990050340e0800000340c0c0351008088c20800703030101d56400310041064400c2c03850b1250 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 984582374 1250 984581124 984581153
    0x30c010f030b0405011701293304031419020d08072102151e09150403030b010e01020f0a031d060c010e0d0c120f0c15090c050f01050304 60
    0x607012652445520108040b04c2c4281c00440d071070002c01c085004400301c24010400b01e03d4070a040341031480703450284030040c0d49111050902ca03d0080b500703a40882c200483c4802045450300748259014034441c910161079200307200c220384101c1c107101142640c801c0030031300da1a01021114403c00c035000e1035080055a43c0040c1d012100c225003030141c0000b1814442c420344d100410360300c0d400004503107180c0207490882c00f0159886820081c00401160503c0030100c5c00f101c49601ea210764039a00c49401f81030804100070001c01813034011800b0042459803640244004030300c282c0b82c411030769200000480c0c036a00f0605130810300b5800748880b04000ba00c2425030403040e12140000d003040030005030000f14290301c0641040c1305a9107840550f80c43c064180582501130455050080602030140c1e140119030448480382414041c980c11140e42d0302d4003a5004219480c0c1c4050200900074016241200410080600f07580407400510003203070f0303410800f0f0038032030f03114058590608541e00d0780d5581039210141e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 984583624 1250 984582374 984582377
    0xb1801030b10171012050c01030506040606090302270703240e2a12010819170c1f0c3002030406020f03100303140a050d0902010c051f110405030c010f 66
    0x50000460a0410303080c170000a2044000e060341c2142030000409941001d080e003881185003040801c000717a004070085003100d034103030f032280c10b424070b02540181c44500c3d01400c2e840c14160a02000341d0242e261340000e840101d04c030004403020083d0661018640c0d9117010342040142c5040108030304411060204100c2c001028110014240341c210310354260f003149600d907a80c1c0000c40700510022005018002d00629040a8201b40d004151580e10380b484103a283c00034808400520312900e003600b40030243c40440c50b1154140485000704124004003140703406880002c9c104076040202d00c0e19811110410782c4101219110402c50711400c40080d40050000c6a10031350803c6212400300c001d00203948500090204011400d26504000d000c40d920660f0350203e442d81003002034421a00a01560401d107000b40c0300056080c2c0c0b80c030040c3c410011140019141384104c540e15030f81c000b006801e02c1c004001d140340c00d0002c1000003240c3c910b1800f96009040d4503400036203601c56654411b454500c1d4400a6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 984584874 1250 984583624 984583651
    0x204032a0807080304170d05040510120218030d031a1e03010c020313060f05190c0215090315010e0606160b07050403020114071205130b1801030b1017 66
    0x9450740c05203407440c160b0108005400200b0104908843c040c2402c42e81d50313402c4c01500c2e144048100040452041e030083d988101c40120039001c40c10300c240f43c040025280107504641e0307522285580564411840c02e8a8800d1003807440c020f6459109004010300b0644031004528040c404404206c00790b04107000541100303104c9400d003400f03580c090081e03080c194410b80280d81d60b59151044145c58001c1c1e6040001800f03200c04106400310741c48022a0000c1e00410b001e03c1103c0306000003118450079091019510541151000c81a1901d6100400b07461030200c040710070910191014000d141c1091040c85200750450f0006199414140000c10b0814034030740c4900c040d11515a5550b26200007a42d1010008134040703420310455800404100c03405030f44209042c100381c100d0380c8103200c407100040c404041010115484064011210740c09024011414440e600c502034070007214030140d01000002e0000342041b110304140d00702441074559500c51a502c0740301c9624005000c1c1c00088002d000c103400a0070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 984586124 1250 984584874 984584879
    0xb0612041202010e120405090106090b18130e07060207121e02061204060606080606030f06100504050312070c1d010332060a0c0905030c040905010615110609010204032a 74
    0x40c0700b9440c81442148175141c4071820b01e000d2101840d016042030050048a46050240f890380f04151800e0004004103940312000ca113020454201d82c130070402000d5802c1404d030300100b46002c5441c8095640303540c211a40e0341d50310b80c441c80c5620440d88016000700e04698103546030940c1e02a80351031700390001d0001c0c1c1c41c01c44450340541d00e401e012079095034219624101030051591004986406c0b11085402ca82035007070901e280b035084480503200510179151080400c0d0024050010b03280206002000d0716685066010003080ca07a010000481c1c0b0740c80e0700d68010480e45203191320800c11512210078440f20340e0841e59070b5101058007660354080450818030140d031144110010000c41d2a03160b001d84110300b44119154140c07940b0b04100400c0c8000f904003404151000a2031001d0160b040314081001901801c0240c0140313425085045194843c000304424240c10015501391a100d000c00c803000c0d540d0380ca05681c201e010b1404028408400035002000c02d00d94160f01001031015050a030810b0759 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 984587374 1250 984586124 984586151
    0x70c050a0b0d060b0a05160213020d020d0b0a080303131b060c051005070e010c21020f07080102030103020319421103070f0525060b061204120201 64
    0x5969034412104910002050285090607010315001001600000c505105c01c801c0c0c05091405210070105070b140300740c2d42c8841959504203112504184200c006c5680303144001e286001380d44400400d0002c0c03410101c001c41c01d820040240e100b100d081c10042c50454550707000b00d00d03014151000903140540d80c0324004110040c80c5410b030740200030039215820030004501e445401d01c007901100f451550b10781302c10030507001d401105010811909203030010b1007002a24200d07241440a4290740f006540283c40091380a400041d040c0e1094503802c2261855540c40104d203090f44000d00009401d0b4010509614001c00243c401c00c1041d0301c6a402c0010403001e0b1214440c01c441d04180407a045c0c001120050010240d00840c00c1c3e889052860034041c070b881d01c0a501015200140c1601f00f005480c0482c001900d20990680d15608000b1007800340380901c660b00c1c42d02160090b04d041d5640c6241030310100d01d41c6000304c100d81c502c0340c20f038081c004140c0d50f94032100359900740900070340155501d0f24a00b54111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 984588624 1250 984587374 984587389
    0x3060812041203053a1109090703020906120123030d050a0302090d0203030a0309060f0b0901031b150207060305010906080a150f0606050304060c03020301050616020d080a08091b0114070c05 83
    0x54000c10112038244002c5c903080240c62040c0010a02c0d04002c11185005446005201c0e41c00320540c10f02581c1e072210030340800c1d1280306180107203000b41c0c1c50340c001043c0c0e4029940f00c00c1525544a841c03480109640c81010788981d040400b044c0895420069540003c0c041e801500400a00400746081b030320301900800c2c2154440585030b00001d03550303c0164100305003441012078440080001b04500101d00012444008060202400010781c54071868108189000c000000e442100c1002c4524040b092020f59900c0d041c1c011207012030b00f40800800d1540701441000100c43d100001000000900d0305c400e18520250f07001c07010346584481202c0120b000e140103031002018282d841503624605130a20380700322a0107408440030503004000400c80303940c81106403420348013499103003c080e5505100040079206c81c0a801420307207002290b540b8074181c0060004c1d1080303484605481001c00e00c610134001090f00f84a000307001c0740c1c4020a1101c5641c40c000980a4103108503035000510b40c07540c0025022 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 984589874 1250 984588624 984588697
    0x1051e1e0a0c030f0c02031615021c0b060a0905090714160501110403050a0201050f090a06080603100b15220902070c0b0f120c190306081204120305 65
    0x6050711020324014040c1d0621034040e106a050708100400001180c0003512486101401508400b1398040d230000d0000a514084901e802000300710369a954800e001c2c0603441101d00300e2050545049200341c154200102103910640c4030740e40704400c0d142802c0800c48200000382c000c2d002c01c019070761003c041d080760400410300011000080040700929203015425074811f0006030a5000701400200001480001d400851550900300151580a408510000c0d0302900d61129030000c1c0201000039041d80000905004100030340603075010b2000c1090040c01d0721079444020713401100d5131138000713030014500028020b03600d2403c01ca0300084030402d0000b0740380785040e003000c0b200f59070000340304041201c2600304000600c440e9000b02c0c103010301448481d14500070391411140050b00080096000b10841e400c45072032f44140e0101600444c41c118000340101018000c01c1211b104190601203d0500401035408403a6100080c01025816a178100c0b4181c0050706c6544079a40c0300c0900c00181840d000b103102c81e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 984591124 1250 984589874 984589891
    0xa06020708070503030f04050d1401050c0909090a02100302130e011d090d0806040908040503100906060807350d03090309090204030f110102250509060301051e1e 71
    0x25000d04041c40c0e582408002d0b8041c81c481d600801401000c030645009950842c1d1003150100c03804107180c101070b00d01d0107040f04c1c41c0707006520308001c114450b80c6200240119100a440e81032040d0b850170103950752032084004c06540500c00b2040c5001c02d5110b078009044a9551441401e141c0c0c0e0f503940050102042030b00442c20102c21048580101408006020303417000019000701040020380e80c02801200b03015180500460315a007104042c03028000c12200280f070003408403056076124140940003407400c0481110820704110340040d0b0324034001481d1040d81c0d041d1188220000c1c8a40048da020030341103040e120b94010100000e03650a10501c140d12030549181c03004619040b031071034028000c48050700702c010340c2031043c0002e102095072001286d01c01c030792215501c01074010b08070040c1e140a40c14210090901106074440781c410489a1050303003110030545201c00c0303d44441c0f04040c26510300303c4030030198400010170b0115040302c82c41c510381c100380203642483e40b51b5404814a444010115060316 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 984592374 1250 984591124 984591133
    0x807090810052d0a140609040b10180506030706030e0d0e0a0e0412021c08040308042a030b0606090f22090b1806044b0512040e010e13020a0602 63
    0x11420205000e0040381481711210030a407841d000c800a04010406000900004000400201c445c02440821800f500300c0700821124840705072910806030004450490080c0200d07440016501c0c001e004070580030b1010360180c520703800000070489031900400303001ca9120060802c0000e4480303a402400d401140a038084100c09503000d0006450405c02c0300a15050415841448140700c0d40448100e40140c2d2520b00140551105e090540100701041d2081d00100864020107030307840b2900d0310b000120381c4a040c2c20a070310340d5541c0c200441d5014000d02260030840e0118441c0c858505004084480b009216641c00e280004000c0407007200e8451000311504201c8405000035101d6140c8003460891504c001000030346050b54810422100d0107164040c0c0c02d121014041c2c548030000702508501c010010710250000002c100100106880c3c8000c0d116401004403914038040f0110444041d41c80c0100c00d4074060746040d00d0b28a101c0401000f10014010719920000143c0d184017481d80100000c0c2e0092 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 984593624 1250 984592374 984592381
    0x1a0d02035508180315010501270302010c0c090203070c11030a02030c010305520c0f060f050907080f0a1104110906040f060807090810052d 61
    0x50303041e01c1c1e814120006007640c0703207611450742801031010741e01940010002c3d1160000c00c1028021409415255414028056100580030190b20040c1c1280d10036079501d5045450071840d000301800ea03000741c0784100b5040c4030500165000b1039428012901c0ba80c8010b1030b6960740c444400803070308103403884800295403810b45001e101c10004004ca0f103410032006044809165070000381c0d0b911107950084e042c50744540001e103c1c0800c1c0f00c0303c00380d104100142d002e03080c09a032480a280c060105001c0320603001091a200f1071a205009502108582e0346504920207044e8441c01401320981208652440d25074401500603855402030f00d000390700c40070050a005080c0080c0504107030400000750440d0b8041c1030048003050350700000c62007106055400003400c00e001850325146124101285030803150000c0e0004428004c12120800c450b2280e8440050303880e0b0940883da004e0f4144030303c0109a0017601c4c040108074069000c40e4100f04042404662024180d801003070754006544009500250f00041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 984594874 1250 984593624 984593713
    0x1e03090819050c040509060609060a080106060210060602010b090117161701060b210408070204110d0501060513260d05120f011511010905031612031a0d0203 69
    0x81d0ba1802041310140482c1c070341540c0d581d41d150300c0102800d2240c90030101003011911556440406001d8080091100c42d40f120006583c64818030b0b25030f41410300c0c2c00b0340019114418410103910060040030000164a40780104544d08400341707080c4124055001c140600c14400c00d480d000030848039a0503070128a0310719440c0d003181c07034a0788503446008080181444084400c05640040c202511020384903468a05091596001e0544029003091808000206602186010b804a6800c01a00313210607038840d802210799000340048050043c407115018860551810700c1c0301c5001030343c010074408148099040b40d1414030b05648540c0482d0300052035224000200111075030000200c41c12210a501d0100100440a841104002004030300307440581c0d0500c2c00e4100e08600e6400c00c003220b03259058590b90942402d0010b00c1110380c00307a038547e4102002d019003c3c0c0f5124030f070889581604151036500b80b2482c900042c20480c0e150180c200480c44000700a035041c00c5184ca110010400d00c80748690 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 984596124 1250 984594874 984594883
    0x30f0c041d04050d020d020d0302130e040303020903060a0605031504050a0c03030807090909080d111b0303011d0907090c0207031a010905010b0705030f090a05090a14131e0309081905 80
    0x4c02d9011900044103821440381c0000380c0d100000c807140380040c2c1e619419581155812501d400128404003c60309100c14140d1540103414806402c0f402d886449e210b0501c3d0354215041442a25019005008460b614250215400d83d000340128195019048103558040c0c042041d50811070200e06a9010702015660ac04c185c2e00103009001000c00681059032244444c9008601070080100d45480746da0011000c2403003514a04459605445901032005401584a8100b4020402c1e031303404c00094860b9080c4100d01c001d015034806d201400f484c9007080e100a001e440c41007031110551244080000028154090b022180308580c00082e42650601f00d07403c0903642c060380520004401030001034003050f00130080320080d28040c031240740d403140101c01040c8695426030140d83d00c04007000401059407416080b49004403907561808c0520358400c00c114079180301075900a0116540a61050518150028001d00e40c40c007900344100391030341d181f4a440c60005180d00d40d1a9903580c0300d06580c01c2000402 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 984597374 1250 984596124 984596143
    0xc0f0207121a0711101109040c030b12010e010c0e1e03010b060703020a021c0302120306033a08101403030903010204060207031109071704060b0402130f1406030f0c041d0405 76
    0x10411b001c85400c201c5203615070300820020314851940c6001242d0080d010754080c03403034940b0203400c40100d00342c006600c40c000d2a440202c0d90f415420849100e2440d0b12420307000004500040000c07001440c00707046501860401c038042ca41565a03144485807980e15000a4030580f4480d41c024102400700d4410b209071003401001c02505020705080060009402292051280e04603001035a203079500c10000915010551508440c400c0c0300d010580029082c2c807811980b0340d10a0300f503204010040b018112445070084505003400c4507812801d010a07020041e843c0047d40703000b000c8a040000180c006422640a82d20240c05039014507420801c01441a4580c40c042d2001c4851104510344124042d000800c12040403010241160016040001c50381c08010412400b900c00c644640d0180310802040c44c03a4016009807640341000091401c001c40d814107140708015084a01319104c0c402658030002c5c000c0c0c06401305003002d000210700044040c0c22038090314000d006611032414a41401800c00c10000b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 984598624 1250 984597374 984597403
    0xf0b0d0f09050a0209100b0d1d0d1e170f06010906020a1a09030d05040506180106080d200610051003090c1503020f04080109060c0f0207121a0711 64
    0x308100001c102c000c078601e80604d03010b903040c07175881c0d48003105654040c10b590401207c8680106500301c11301c1c0258842c8840c2650988221000d03103007440315550b00c594003003601002500c0d06240b6000512145041e81a9000c58181090740e03403011800340004080480d00203e016000d58100596507920a6000000b48024005041d0b1515641c8454036521190b03080030166140d03001c0440c030500020400c455045060360020040d40c186860015140c04083c0d54101a280a20284403051001889500700301e800d0000248400c0072004019106440c40b541d003a030040781e00b211004002001484982d11034103841c0740030340c1b44c03e09040c1001011148030301e45904140c50700660600281e000e103c51010307038900301c241c041102000c0310304401900c110b03600e18400180c00b040026040c2e80540290540a2141d0400c0c441403e41e1002110219070000c510780040c0c2c0005002c000016500a010b07015a00640804400e404e0454500052200c10f440340c10025202c034040c100720301014403401c4041000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 984599874 1250 984598624 984598631
    0x20c0606060717090d0f03020a0507060f05030a0e0a0c0b0d0507030204150c020f10030501050307090e03040e100b1611030d02031b07090501170d03020310060c03090f0b0d0f 76
    0x182c40795001070f8861a8044209000010760568907907886032058030240d4030851032131503c40940380003134451074484c0c0121941e100c2c0c2e01c008540c090050382d401d014452582d486508546e00c0074420409860300000b2120305000714565003012540084000303002d011904825580c2e50500c004840441d0401401c00041520501c8180980c0c400c005080d0b08540740383ca0018001d250358000503c68483c40d00019038000d460700441400750750550803c0c2d0403190103d00b640c0c030f00340e640c41d040025150a024113841a80003048248a881001d03e4120307045415002814041c07500c2c1d00d500d40183d4401d07291003155405039000101040820384d0107012034002540034288810006002039501c4c05103411801d512401011482c1181e0b10810401c40200071032242030204c1d583d950070b61400e8079a2140001c02c540100e1090002d90b074001d00032a80509416011014050b140c16004ca139098a030100450810500e21400928041e806443c8000f802c410841c681e80d4040500a070b1080381c030243e541c520b00604 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 984601124 1250 984599874 984599887
    0xe010206060d021e040f090b0108010509031b0c21061006230c0a062306010c1410050a0c110a02062209060e0703061403070b1c0f020c060606 62
    0x1902c0d41500d5540d5410f58043c5016144c0d0034003c00351400c100c008507041450855182e00814054100b00c44031070107040342c602140d8940301c49500781c44088407000f0007a401040300450484c031110f10400301c400c1c9207003a1200128009c0010303201805c1a1241084122076040050210b4410302c01d807504691211f051035aa44e2400c0d10140000005800500c465068200340d414054140780407603150081102c1550380e10001c03450080c005040c9118840034400702400e0301c40303045c1036554406004801c140c580d00030101c5903644490310345040c0d21031641c282c01303107000c0000395000707501407603016041406000c20204034036100280040301405901500c1e41c401e00300840503844100899000d8407a6211185010466000010300303188a0b9000ca5a424540300c0d0000d007808604000d06e004502c595400d000d00d650f1200b00c0c420000c0001051075254004c010100030815012006181b8005904103a8414010300e105c0c00e02140c0c450710a0070080758000501502d0758030240b0001d41e0101040703c0ea68200b0381c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 984602374 1250 984601124 984601129
    0x2011106460b010207030203070314010510030b0f06010c050105040f0b060a030c180212090115050402120a09030e150403021504060c140c09040615170c130b06030f070e01020606 78
    0x1a0900110200303180d40b0300c011060350744284860806180c01408843c0e60580c0c910308042c50b611010b48a0266500e0800441c8440b01d169240404403500034003603a810b925881540500032201900081c140f00039075501400041003805140d115901800110700c020038603050007500044000c2543d03110b640f1a000520003e014049100301780e40c00614a6000300d804018440002d2103000302c556802e014103c00c000d2076aa05402010385039010a190481a036911000c0c0030680c0640c0b01c401c035a51600d0800244949041d0380b0446a850203458507664400001d070104900f0f107900100da003400c1200140500c20f5003013051514100320191700216141c80d103000d82c02081d042c192507000304000100c0070302250202c0104000d8080c000010200d61682c1014074003000146142c041c2c600300500004400204a85104110f00c03209610030b018000c420300d035004000490400035501000d80755108503003071450311400b001d140b10f40350b850700340d41042c2401e04018140480e00340a060456100408101c1240c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 984603624 1250 984602374 984602491
    0x15030f0501060e22080f070b01060e1c02040f0605270f0906221a0702160302092e0e0f1f0905191b0f020c0f060702011106 54
    0x41030701030020001065458030702c0842c0306c0c0b070304504800b100118200f82440036100905048030083c2d200c1c1c0c0808002c460902c96220004c222851088034004032041c094205a000b00c14102d000e02000120340e901d460001e2000001d500550340d41c081658480b000e02e0a0011070503030881c1d07449038103a10b1341c030b05100d4483d40e4000043c034540d1406005103503601e0254440300c0047c80e0715800303500206403580172207036000c1900c401c840d00b10052143c0303a0220502c100881200d400d803900134140301081d90383c070300700401d00c22281c9041e008108030000030b810b06070740c4612100740600020724081541d410310849850082c01d001c1c2c80303004207041d5903104042144403469200103c8504081c04146a40d0301060a08284400c4083c40d00d00350510010f80801e0301c0c0c40c40820000c150030303182c51400085402003281d0350fa02480003190404411804081b8500c0d080d0060010700e4814075040604801000007181081801d0b140d92060b00c8801413020441d4444400c07501c41003800d0b1401c843c40e8907154207600c0c0c8a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 984604874 1250 984603624 984603661
    0xb01030609180201051e0406080f1609060f020f060f01030b18060a1805011d0706050a021f02040510080406060504020f070204050402011112070506010b0a050d0f15030f0501060e 78
    0x1030040003d4202e503902e450300c0c604c00305d0742c06e800c0003540c55994850008c0c0c02010201d03402d07802640007400140ca030110080644001c205036665441450341803110035904007000701c249a0643c802c1420140358004100003444c840c481d00c4a603003409500d0351510303000030a0041e040c0c6c0e0111200059400320720030001043c0340c0c031480c03e15001c9030000300b00703010302568030082101130525402c000080d184140300000c00307194603020074200c41d5003641d140001c0721540241d4a111006800002b401110200040da0317807004480500c100520f003d503180e000419044071068035a000c51402070802080c000c461207070000408040d5400d40c40e100103d0703090380c0c0d80d11600c0d50091046965001090640e4480e0b2822160441d0010482c0c1c00b40311500840c5107683c1082508540500c1a9000458079040d4070046d02c82c044a2500c80c07a01388051050444003814005850240c065503a041640103000e08100210056004a0014040025500304035080d203d0681003d0749140e40d00301031100002c100e081000e034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 984606124 1250 984604874 984604877
    0x213090c0f0c111e031c020c0d020301020c0105092503020a180e03040602010f0b0a0303020a080f19030b031605092206020a05040e0106020a03080a2d0b01030609180201 74
    0x44841e600d00d02540d0010986030301ea900100313001c031840040c0452860300c0c031106000724100d882c003580c0704100b02107155a200b54000140c01030300040d5842c3c06c040c00800d00d071910081c0050300700a224100b0b282101c000b114015001c2c3e2090160159000e001c0e0b104002206000c0c0c002034003d42582c02140d01c6400d1403040e4035420300c126001d0406020994440124500c80303d003581d42d543d50f6240d00034041c2161004074501507180101c41c42340352904551090849515401600d2040300d107859a01d0107401c4079052030340c803400c00c02900c4080000b90010b80c0101400e618000b45802c00d00003810f1a00e10034060240d0b0f0300c0c50031a018400790b80c07424040d03680005071580c00c2003c44440128000003403d021401040c6500119064802d640c0103000f4001f0368a200e102040c503030784e82c1c1d102260b903503eaa54010f408644854046030b004040f5804c04182c108079403030006a0101c06000103000c861181c1d070f501d21916039803141450207680c140644c1d03008001d420b0061048040312000d01c180411103946c000e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 984607374 1250 984606124 984606137
    0x10e07081b07080d0609022104020904060c12060f0303121503060b03031317010b03150402040209012114090c15090f13020a12230603071502010213090c0f 68
    0x10100091403045403004d0030961014008a942c5a00c90710294115803885084019520100e0001d0456070041c1c074410fa400070b01d604859100c5490344001480d0b00c020300010040040082841c00c4041d004110003810740c00d00703c11100349075080c0184110300b001000c400f05820180e45003810a01c01c000c0030241d0382c00920014210090000091035441884c102941c4907a07031110000341180c41d00b641c001c6058648000f0302c032418644003056210a550654180c0300c554010100380582401c1c1e0107081d9641c018103100794445200089400c0c412152545600c0c0f15448030040030020406501c0716401031801001003412038100400030350690b041010459031094081152034081e9540e203240301012201a014024039801c0c1140c1030b0103584580f400002207482c185078202c504020b881000c0000350310300d01410b2044034884070742c0c03a0710b880a0000b0741d051144000c00b10300d481030f503000d0340100000e540005a607a0b0f0107040c020101c8040c1d90000c0c2c0301e41d240041001180750408141e900044852a050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 984608624 1250 984607374 984607387
    0x605070c02212e15050a06110309120102130503070b0405040f02090916020106050a1d0910050c121005060307110a1a220c0b0d02090612010e07081b 65
    0x2289814000e50500143d400f28a8034000d40c28181e2a074100140c940240c288240356842008900405403442400e42081d581c3e903007000054407681d482c0c1501160001580e141800b104002550f80042619070000ca950010b01141100000c40450740140800da01900401d45000c19140190003241f248030b010341d89030b05c1c4c0c10240300351a0b4111a14132074000c1180c080d5041c44c03039944c840080d5079943d05003d0361074000080344130704e0100c540d142280d0762a00c040c840c00c01c8243d65000c0c00b5201409206041c03150707070983c501000013800742c04d108100180000d9102c0090102d24406124068205107c80800e402c0a000d03e0b05c0703880849034031000e07500744003000495588260340b034410411030240c484030ac8030300020482944460b1240c05204142002e220395050b0381c0c00e000409048007001401030f644200100500c00c00500941081001c40b140142800c100c00c0100c0c000b5030008820894400c130620040c81244600c0e01401d401005a16204c05030340b800d060044119005640c0d0880d4899010030070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 984609874 1250 984608624 984608689
    0x4050c09010e0f0a061101091e031205010f0302010f05090d210e33070305030f01060509181504060902360409170a020c04110a021203041a090303040605070c02 70
    0x8c2040d81c020760380c0706904640040c0c010052882c4104500049201c0c0300c00c411304c1c1e4607009013416900410f21030000c40785150300644030039030017100050510609025401d40c50f500d10884211550050702c3c1550405141e8000030b0420314015002d900748801003100f038020f82c90740010403019a408d10500210440021402030243d01140000401c4490001c0c0c0c05040590090103107000b6511419011980d0341c9481c03041e07429003e660451900500c4a80000400c0c00d00081b070690000070b104905000c05100300081800d651141c1c00c100140f980010741c4403800407480340303041c4800008d80605055114041c030040c5501c140070040e144241c0e1100000e20a12014241d407480070030403960302c946d489610040c003a499034500740c8141d02c200d10b4500c2c4100c01084490880d251016250301030040c00512004100746600050410f40d500c0c03000034805048101c030914458003c0b0540e000450700c0349041e10b004815914000c221408104524010000584a03400c00305030a00c00580310780c0d1640c1d1070340d65 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 984611124 1250 984609874 984609881
    0x9090c0305060109090b010e0702100c0e040c0c0b01140a030b07050d140703050c0910120b0301020c150c120a0c0215070f020609010204141e04050c09010e0f0a061101 73
    0x90704a0081c0c0c030002032044c00325404946150303c6600d0b16003450703036104140307001004129054005604281d00c0180a03c517141e00854070310b40d1070b0510048a000301c0380818119840740850001055080d00f40000b4011365240407401030410307050007440c050305107000c45c00c0c10401d80b00040095200c103021501d000d00400c1030302e10b08000c1200400071310000c40000f02c032850f000d80358100484e1034100447e03400c1944400b1a41e42d2200941628030040e458007080344c0b04691961090780c4544c1d50244846d8a603001c1c001049525107010007803480800f00c00e8505a4000041d05040c030400c1e00b080740700b0b060300c203050065500c500d0840d800140c03100b82600685c10050843c030150070901c0c1c00d6040140068020610807400011a0300b150030542e203000b00c043c200d229a0285a860780044011072882d0b282c030141039800e5000d10207000300383c8640b0300301050560b901625220b52100c0301103240d07142c55a2290000c045200d0459100c601006d5010104010250600400042001043c84407214240941 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 984612374 1250 984611124 984611129
    0xf111b010603290f010e1602010605060c34030303090218090601090b01171303091a181909270507080d050a09060c020a032103060b0c0709090c 63
    0x2a1040d08500403440b0240398070b00c51054410045000f5808504030300005440e10b4140d94400440e030752a80c4441ca1f02c40000f00c1401c81c0a4210740d2a1440425940c0740c0342c02a00500c2a50030040c6401980c44000c0d440713045c42100050b014041c8a08a514511010441c00741100e4240c00e0010f60300e071013030002c54800501c2d051040c41003000082800f000801c0010303510f040b99007515041120301070341d100440d01d11841c40041e43d8040310182c040b400803014540100b0410b44a030a1886240da51003814043c0d8440c1c40b02c407070b42102c00100f406585100742034140210580304484c80c004240541240103050800c0e0b00803c0740300c80d5103c4400c00103489584101e030081440c12445401403646140c240c0d9109228052054030b0b00854070b03d1440b40d4050070680d00d801d1040d0326401241e50400200312401c003204401a179201008140000c0450a40d070140c00d9010481c0340034056200c0081c0029068903120390007940c190354100002c03500100003080f0b560661310f2504020a04103180e00f41580e0a450300d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 984613624 1250 984612374 984612383
    0x40f0f15180c0816031209120609050706080606030a0e0c061305040c08060603070302070807320d09211403071704051807110618010f111b010603 64
    0x1200c0c12240044000d152007103100b003841102240c0c40d080c9064886540e54001d00f820301c1040803c0c0b0001d140c50408094112080c036000920599a200c6003420807a181402d440c0143d4812080092020502410307014041e2030908082c642000000f0805620008018403840d0b680d84a00d01c1c4001c2d414030045080759401820309841c0e1241c104011903900c0717148902031146140c03e03404c2102501400200b84502c20052150b400e540d00c07508258081e40c401c80c400c0f40ca00e201004500300103035a526032298182a210200d400092580ca04000e90700036000c005000341e800440d50399800c036030190707541c0300b074400707003d04500300e03401c0490541384604e10303400700400c600d00413011a10101400000b400030140030740111710840310000c0c0700315410302c03a40c00f41640140d00200c0070001854480c1b00c141d0091800d1500d80c0010640d8034425017062001d48540b060304c2e18100c402c81044800f4040c040b42c1c800f0b01501040040f000844040c030320310840340c01c42e9044000c0c15003408019400c0d4800740c02903822 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 984614874 1250 984613624 984613631
    0x302070b04080d080105030f0d050f090406180e0c060a0e0a0e01030b0609010f0f0b0912120c16260708030f0a0906030c02150603070909050f010b09040f0f15 69
    0x102d4510070744401660f40301d40006500c003000010145800118a5440440000a4446030008000444040c0c0c42140054244201040203038219110745c890500100190300c030400a87d40d00c4803102080d40c002a920394070590059042219641c1e81c2c1c003c81e00361410500349596689003420100e20607070074a03804240c2c9200301100020070700840c468421b20800c401c850b45c5e8000d030780301c44c2c1c0c5100705a503a000b5896070084071107040c02440c0042008015005008140301d8100300d400c80b40f80e1410b000c5440301c2a03003403000708002c0c1c0899010404080400b904039050081907040c9002d4251590143c50b0081b51850142c03880340e83c40200744500e0020b40850b00c2621360f9014208449002544601d5050000801048000038000d10070700c100110385595501822800c0606070040c0d804a0000c4c01c40b640c1801a5007000508030158828140000d110b18054000100300d85d07078181c00c40300c198100c1402000200708202c00500441c2a20103143e9100b4000070303042c00ca5003403508040d80c9207008020340303614 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 984616124 1250 984614874 984614879
    0x6030f080301080f06011a0d0b1e0405010b090f0d031403100321081503160806011809031e020c1c1b08190807020d031110110f070302070b04 62
    0x50080045069440501c00c9400c42c507134441d1001e0340c40409105600c2220002850504201c000000504110103006000719001c1c2000001981c202805500c8500c0d840c02c1c020401d4050419014103401850040309182c100107848010031103810f0f01c019094828006840044c04140c0603100400e00c0c0c90300c0d000c1e40e0380c0760f1030105411400c07610280029038940c4c20801140d10703128452000300c024401503035192619a141d201160a02d10100540b40c0c0c0d06000b10065000c0140e04410004e005140c10700c02414154540182e144114070180900441c071402c1603400e00229821031005a110354284401a045010b00365003281031000c61007038503902640318034101c24407110542c0400005400b0b8002240076001c4c1d000c0c4000030410502c55211b90350084c00d80289610351101c4000c001a0107540c0341d0345006060f41c0002c0740081c0403401100480c501ca412164004003c22000c0142c1c100c0c80810414582264100c0500d4055100f0329511060700240c920201482404401d00620500c0b4000361100d8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 984617374 1250 984616124 984616133
    0x90b210c030a050a1a0409050c10090f05040b030a15020706060e010302010e0405070e0f0d0c06030501032d060b1305010806220215031b0403060912051201090f06030f 73
    0x90099804042090038000030440204d800c1c07160140e1070b1108a81c00c00d54a44840070b001c00703481c403000c007699203015140342e002c1c0e962078038038480388482c4160303503122106030500030800b5005000b034202d140984c0ca4014203524039140018070712259504196030000d40c412850440019200d1804000d103010704240c40052151540b01006040e82c2c401d03200c0380d61600700c2da014801250404c5407100c1c002441d02a080b000c80c00d00380c3c0088584007003e0600200c003001c0d92550401102d440c0e0040340001d0341d80004105204501c0010404200ea4000e070404003689500010039612035148084c2080e980c403038001400c4c0d81c07020010302c040c1c84140700a100c2d030360b598060319440704401c450f024545000f007184040f034002c424055038203140d802482400000011100c2444640001b003c2e4030806511012515a440303001014000462080c030021805c000d01e40b4218009860100e030031400d122040c4403400b800941c120302141594034410002440c0e4000b00c207000c001d407555074000303003a01303185004040901 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 984618624 1250 984617374 984617377
    0xf0d080c190509010f11060109050603030f12040b16081605040e07030902011101151205010608120a09210f0602091e0405060d0201170a1b022b090b210c 67
    0x241c17100240a414200151500e110850300032955800003c01400300403250350265030001406011241024500102c00685501000040c42c200c580002000100054142990303804103041c070300101c28201000015000600140c8550325447c100350075101c6980c450700c191b60051010040f10000d500300310380050700030b02005100340d0001d40004070104050344d050186001203400ca1020408551034010903d8194152a80840c2da65480364000039050500304400800100d44100c070544d01d028001000d00403002d250310541b03181d0300710381740488030ba104160f442003110f03003000508219000c10f280c404028880d128031203a108800d00600c90303100d00030070a5100da040043d41c042289485913420401010b001c580002d0024564110414188058501d80790b000b0341c5405002c43c98420130394090039042d0141e2584030040c1e202c0521041d03042503098103041c0540c00300c500070b61410808000200170070014060700c00d454400040c40c403107080a008041f000d058040070410f00c0390920003a41181d6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 984619874 1250 984618624 984618637
    0xa0806150d0c03060902091c150924150506030a090c0618050625080708120402090703050c040605071506060302130b0423030f101506020f0d080c1905 66
    0x1a2421301c0100d00f0360000d1080365641d650080c0a04600c0800381da1240c030300049207100f2510401010025003219400e03018100189200c0c000070200903180070301e0300240c0c54040e00416400c0c0d0030980c00700c100d070000d500543d00f910015200541d99a8071900804098020308000609440442c000000c04076440008003440300b032081142c4000036030b94010885140101d0082d4460300c4684600300a241c0c0303540c0d1a41082520641000341060b1154407003540c6c44d00800f4400780044000030412045191400556902031080d0500b040507040108004001d40954080c0c041440400a5518240481301800c07008000782a20140300054903030b203008020b500040181858081804030114070100380500359801c0d9005164041041030b1014024840b1842c1030001c140c050040b03d151200c3c99009200404c4001e0200c080171a9049200c0321000c2800319590110085400041845190b004049a9403440b0503840c40c00d20155280c3d00d074004074034481c40c64040781d184450000411001d4100018220 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 984621124 1250 984619874 984619877
    0x3070609050a061707030e0a1a0106080c070c0302060f16050a060510060e0103110c01050f04020306090c1c020111070f030506010506070812041e06050a0c0201110a0806150d0c 77
    0xb103a82d0342c10b01a02c00c03007070540034200c007000351100043e40c151080c0c0c0803070074460000c003c40341e0840d00c2e912a812550500e0154000301c281113401802400d8001e01368a41082c0c204054034500312031a16031000501c0c1600000303100e24000109848054000c070f0644940c2241e0008490410440c0d00d051a41e0b09504072003100d080c0d0404c2c0c005045091408a004225000c036103500580f185c031100110300602600c503138000c8003c001c0c00b10f120025003d1245a00c03850901c0d9040525061a004141c58401c004100000340d80c400c2c00c0742095a15070703a03104400745241007681850300c901840165441504400242840c0c402c02c007000034441d140310394000c01c40303004900756509641c82c0c0007401154820006c0103080b081040207400c1000c02d540d54400d500901076500d120701ea2050160140620000100590f4102d4a64082c44070801c240d103c6c508a0f00c007540020004c16445586d0888180166031042c001d02600a0000306c02c0d89400c19000c500684203043c039551100e10003402c00007465114903800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 984622374 1250 984621124 984621139
    0x141305120102070c1205010906050a0903111903030e0a0209040b1006020d0c0308090c060406030207021c230309060a08011e06210b15030123060304030c0f020307060905 74
    0x80d00c560040c800c0710026a080003103d030304503082c6a40002803020013002265150360381c8503000c000c50583c1c454107001c0d1595850224001e06142001050441e1692001c0c03c80e400c041c860300424014200da460301c060303040c20003180c00301d007c1501c5400e045401e80041c7d00701c040b02081104002c165070b000d0b03201c0c14474403081c0d45899444034400ca90b00d0342ea0990103404150403800000102c1d020344402c3d5400001c40080300c0458401c440820f4440d00258007072004290042036105c110710b0491041c0c0b4070385003001018900c40343c00d51117030100d8103800b030000180d85d0321082083d2201602442201c00c10071317015008990320426003d0081040c0c00900c01c800310b40c50f91104040300819050291001c569403903130340c0105c0450903801d41d03500f02c00081488619560741d5400400b036840d5070781031240600d0b0407810b081d02c0f5072511520701c44006420740b8084240100300500855550b45000760303900075030540361010303510b0000d07c5c1c5112042003902c0040d606104d10030000074001d5001ca244025502d0544801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 984623624 1250 984622374 984622399
    0x120d120f02360328120e03100203060906101101060e01090608060403080f180609070e010e07020a080a140324040c2c060408030a02011508060402090601141305 70
    0x1151000b01203110f54550003829000302d651801e400008141c080603040c00b10f501e5000da1740c0d4100040711204210203c0d0700d0307064240c1c85180c10f20070407400140c0c482c410744c88c0d45005000600c1c1e05d01c004146511814000d8058039a05114803540f0b4205407480d00200640b585410f10000c02c40401d02c030301134205040280225070004013007802402a945910789103241d03220740400c1c66650600520000001c64414404d1054003000c20920b030007601140b01070820142401c201c000a0181600810801810141800a01d0340e00065061506400404490715104c0300350341154040a90200b03a0040320b004414001817040c802081d0401410340008a6a09804075040c00117a0f5106810340d80440d090220820800c040d41c4508010f101111080303040003840d0f100001c0311900f10390002e1075030b03a00c0441d207145070703a4091140c880d00200720b01c4d07100c2c0c10318900121079a56810042c07001380180c01c110046080c0d0303400340043c000702040c51000b20f510b074001e403884480102840d20030a4429120800b00c2c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 984624874 1250 984623624 984623707
    0xf0309060603120f032406040b030a0c03090c150207091a0906010201050601090302120102090613080613020a14121207020a17060402010518091014120d120f02 70
    0x12554001300c00b034242c605543e24401c1807001c40c43c01c61001003021082101c40b2110750344140040000c0c00700180d8180e181d0425060300c0e000c40c1c03a400d03e902c080c0f6203002c0c41c8002003680b0402c17200484e90b0002d94208031028108040f0704003580d540c010f091781c03030500800901c07400c4560320140c24241d09848180141e910b00c4012802d9481c01c0c0c03422401300341076072800e101504200720009980c400303440000d0b140006800104019a00c803825100c0403035403000d01031124110902c400307038001100940d807480420042d0006412a440c5101c1c518180a807103654410741e84480c18603850145240c0d050f641e02030070a004000d29070b80824002c911032031a50304027095034000d43c01c0212507003c085000700f109640c0c80e801980c07540d10114404a0b03400851204100d299113000c603241c40340d072560203282103403031034440c9062078101401003062040c40100c1c014a8086400104003881d14090b00d00142031802d84003035a4020900c40503005070183c00004c5c3c100f641d0ba03103000c02e03c1c80d6035504241001c0c11401e0115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 984626124 1250 984624874 984624877
    0x603060e0d140a0c0b01150f0311030601030e011404060b031203010518060301140a0e0c0103050903311203030501090207020306070315081c0206100b09150408010c0309050d0914060c030f030906060312 88
    0x1107801c000d0340705102050295201764011033f400308407003000154848824003e1840c1c0700d811501141c00c01d0316124910140d00702030081842c0c0f030b44051911400d40d410301000600c6404070540e00301007003c08800040e05541d0940110840a0003030313000c8070701800c05289440c050304030440f11700e406103c1c2d408100d056506c24491700703110325645005142400d001410741c0b00345e101d02150145e030100da038000c100c0700407100e006054001c002c0c6021940c00c0740c0e4a850060240e9805030f10840c181403041c08074a01584000c900300c0d500c1f030103e1500049000100e4001510f40c41e03603402c1a040392107080c01c02c482d10041807005000c103403081d800321600d996030880d4620078000b1900501ca410704040c0b080542c40e081a120070800800200f408505294030303219101d0071589030306132401c0001d85540c00001880024084000403040380e2418000b9541402059845094081d0f24036005070f20010b001d14641e04240140d8401086540150f42c1c2c900b01100b080da61a803064400034402d0203824440c0010805060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 984627374 1250 984626124 984626141
    0x9020a051206101e0320091504060909031707020f01140f06060a02071401032a091a041a09030d020d09090501060f120608010509010603060e0d140a0c0b01150f03 71
    0x108110b6038076055a90322043d05000106c03210003006080542c0000c0d90307804081620840c000d41840110400020030842039400742ea00140a0718a0b001d003000c0031a520080c0d40069910681c40050f076904c2d1003401304d2410989503105401c95107407800c200c8140450401031030044020328141c008071713144d010800c030b0340d48100da186a0140c0d002c410100039400c1005407190b4a40d405040008413014401d0b42c1500d4030008804411500445117224144550404a03140103881e040c55542c3c5100415140c2001900c00c90040c02103507058441848400d0850760f04403103901a002d010b40b8041340300e41c6800795441e60303a542c5810100310345480116a45030300d481007030304940c0300355500305480c00204001e80d00c1100d0301c4140122680c4807840031400043c24015a80611405000001c08525605000044540782520900142c01c10040c150080703521241c0c008402046022440d62543c81c400151113550010400a04c400810800058020308103a0340007208400e17034640010900c159030085003200c040e03030f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 984628624 1250 984627374 984627419
    0x9190b100c02011d06030115080a1a0d050c0d210f0c0b090a0f21090806010b091c05010507080a2d060305011103180a0f0609020a05120610 61
    0x1c000d501e01644c41038201111904200c0c107200543c06440300814000c0d1300c2604002800d1260810300324502c1d9010508940c00b5080707070020004050f440007684002c0c8136108065104400302002c11043c09000d000c56800c00c0b0380200f00e03850000d40c42c41c04a8900c142a1000001106010725200c002c1d03001e150342442494440c0e6a4820101e800d9541e070744081c101508100f8a031040440d000001514a01c014400d240900c1148050700010b40c450401200d03c41c10540412080510401c10124000345650544250f80010ba0703c9030b160801081e003402d0a56860307001401013480e101d05126040d484203000e51203070b550344081c555488681d0010340d1014692083c2c1d1f607250104e0301140070f0740e2108160310340107000070210340c059607902c1e0345081d24403020803005001000024000040515101d4140001c151000303003403258003940307905104c1c4a40c05805810319486011480446d42d0700301c1104003510f401481407003480b0b42e50895030380c0d0b010100c0f014580038410b841d02007120401140c8802185464 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 984629874 1250 984628624 984628637
    0x1090f0f1a0c030c07150f050d05060609060a030c03060b07080a2f0f0c0102010509060a0906110a0c1518171201330903021002070509190b10 62
    0x1001518090307400c064010090420041c0b0810026180078001001000884001002c03182d040613403008030078801401c0c88050000ca20309010f00380b5004000c0e2100031892a01c00030300d6030f0740c203008030351355104098489910500018420880c40d42640c00b0728440700496400f000304544408918969104d806000b9054510500004406500c03e00540f041c3c00c0407825200703100c800e680129400d01b0210000d03886160011f6a01c2c40c8030607020400c0c81d180e800244020321071400c028181c1070b1aa40040c04005841c0d44540e40c110a00400d90401c0c03040586c299402c3c0d40d14500080010071002950310219140e0b89840004c13281c501e0316001d020f9000e503040c0303440c1c2910210351780c4e04c848049070b030510040f0b016803d200d455100080052024000e051441c809004108032032002c100e441010844001040c10344040740c5a182d0f4400040380640e0760540700c90000c1e00001c2005d80c5012540d42c000b603840b00090003046000b1000e160f041080c80d908030760134890364100604110f91115910980b100041d0f4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 984631124 1250 984629874 984629879
    0x90902060403060c1818050f070503040311030909040303020c0618120904060f090e0d080906160c06110405030c06090f090c0412051b1c08030a0212040501060501090f0f 74
    0x19540725030308a01c06800e01c88440c0d85c03510003020365056194000034828000640c0c0306486090350007207540c040b8803030150056030720f0302c8a00078010f40030181c00901001102c003e40074650ac0d0400442e100384038024112032891500d071500070081e600066035520703540035210204080b00c403030a40c04842e800811b4068148500203809400d11030300030311501c0303a00548a4100117400407644442c41c024010141c40421031041103558a4900302e401d11082d810068000c04101e03018a01003445a0812509030701000102c40b0348108071030742104c100c006000039280599001d90400031400030300c100c4605600340c800c03c51001082180c1d60103045840f68000e4200e11440c226031070a90302040c2d001241d40100c5041503210f81d2015544501007904070b450354001703102558076101d0040310366851a0121040c0b10030741e4424920015007030356018018507803800400800c4444031aa01038880391305c1410080503242c9824181540680300511506002c5143c850000c11141c81e6800f20500307940f24180307101400c52 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 984632374 1250 984631124 984631133
    0x7050d030b04020d020d0e0c0a0806070f030b030615030c030d092105030703030501051c03050a0f0207090c08011805270111040306020c010b04060501020a0b0915010e04030207090902060403 83
    0x1c0121540150b00308009150104d0070b1000e0550000c1c0e200000802075000341140340781508200340144102ca80950402c020540003400d164001e80070300c0c3c1216642c1100000358046c001002035140d15000e10400c200c000032003208451b000c16407c82c00c0312440c0764004241a1103147c41100c00d80002c0410b041401000320320012405d00f03000740100c40c4c50210081d15000d08582246804600003501d42c1c0c01001b5501d40700c3c152100e4070f58006078400c200d0000d40e901600c2072040c04081400c1c0990100e0b19210b07203000b840a4401032030501c00c2440040301011004124020034014070440400b424403c45a0300708030701c038842c807803c210945030603510006429005a0021007910040399034039044600858102c1c1806040154411800540c807100a100401e0030344000c901018000d505c0d01400f0030403aa40000c507041c2003034001c080b0f06000c0d1580007000782448440b040f046c0d5648800340c00040d80450700103110b80302d90700a50940e4441900c4a09401c2940c207512400b03075110000344801e2001c41e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 984633624 1250 984632374 984632381
    0xa020f0f0303041509050105091315080d051c02191b060f0501030302150903030601050d110703020d020d140a110f0607180b090a0902031b070b06041107050d03 70
    0x2104010804400001100c000074a15801508450740789001c030b0f80141c05142d08220110043d000c00d0a1070781c00d0800d407002088146081c4038003084ad054940240010311202001042e02900307000003030719030412442c54003825130b50100c442c0d650040550344041c1c01c0b5106610a03568018072580c0c0031032549040260444032010100450031050001c4038580000840902c5007025901103c1404900741d8910308010b410404800046000c1622102c2003001810700441165440082401c180d0340301c49494045100500900305030780f14484002443c10141900019148105003240c0d003110800b803031100c2d0807102e040000c00062140c200602c1070b904030a000b0076041c1a0b00b56082c003140d040f600007040c500d00e0b041c015121000402c00d2070701412821000d03d09031002810f03076000b00380d10705918080854102c0c40603100d0944503035408004227500000380c1d10300c2c0300040061072540d5102e6200b0304001c000c0d24070584940d031150345013024505665556605a170b42c1c950704200a021111742120064014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 984634874 1250 984633624 984633649
    0xf050a05150c06070201050402270601030c0903080d0f061a040e070521092415040e101407080124031e150602120d0908070602180a090b030a02 63
    0x104009200903035041c0b41c1080150310031445680041075608144c01030000111080c078140c0300c07110f041030024040c1048610f107035070842c00a10700090000c000603421a004400c980009000070400242c020300300c04103400101450710b50110030000d442d6119824211480d200740c030302017454024801001002c1801c84080c0e40081281403003072400c003082d2422500d5580c03909101d1080262a0140162030104001c100ca60b0a80c034138403040c146c55070139103404030000018202514030071403845250040c0c076030703800080a50b43c0d91002c444505d0a014842c6020341748100003410350000520001d40800d00c6504218122811382041c000c010525102c1d807442d8050a514890074103403241d40340d580545020003c14a0b01c012a040010040d600444103100004070740d00c00c038110b40c4041502d4481e81c0101089030402c0c03440f00e200091440183c030700143c3d0303400782907409000c10f440031407000740d044148510403447c2d50003125501070180e2075401d0302e011124102e0305030760113034000207070f500050806400c0c9502 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 984636124 1250 984634874 984634909
    0x10e092109061309050412080105011d03011b0903050c010504050112020d1d031c1512060e030f04080c0d03122712020d08040314092202130f050a05 65
    0xf4001018a1a8014024580c025002d6a5840c01000706002000c680f801da820b0051414201c2d40d498200001c0200908a6003110041d0a5103600c5030740b0b5400754851004821300a05888200c1b0034030300060181c4103103101c1a20180a02c00c2c94000945c0f01f4070880c1c083d40e00586a080700164035000000c029006085161180d80e681e02d1000c0941d0b40014401210036080e41c02150390b401e030741000107801181400c00210250520303038580e40380040610454183d80443c1030301c0500c0401400c03c400649803545441c0c0450100040d5884011382101c01003041c0e6103c0c078201c035990b60141d018400910b00c407010280001c2c0003103240c1c00742c0c007a80b600b200c01d41000540c48131a102858002c1c8000c883e04d0480101c810080d110b100300031240d01407000c0d40001000f410400c21514103914040c001418100400c80341501c0026181070302e546032600708407210740180003a800603603c001d00d20003d500c2184c0c0089840b0200300005103901e0654642019180003400550149280c0000d010011031085070b00c0c03a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 984637374 1250 984636124 984636127
    0x7080706230d110c0a0b18030405090f040f0b0c03180c03101121090d050c061317030f18010b031c051b0a02010e100c1211070608010e09210906 63
    0xb42440c82001700100082c011140e00301d040c01c0010400380707459258603031914a40c00512041000d680c4844c51070b03070302c01540d204030201a030b00c41c6009100311040314002020045c004041c803001d4035074100950305c0780380c0c0081c01c041c01440c07005103517649038a600300703495040c0d0100c448001d01c050640c1000f8540c03a1701061403401d14004101c1d00c9503250b82c502c14031070740112040400500d00020001c03802c80403a5410842d03c0d102896041c0c5e40c07036610003041c00b889075410910640411a2144041465685501c19261682407a41c90300d1002d090a5480c0703002d03000182c0c01000015010312402010315802002001b041118900d00f50150029641040610200740801800034030400c07081449140c15401a11281406d880003409030400020410300650308004054280c1f03800404455010b07401690143e8282450740d411154111400c3e44140203004440d4002a22900131880d40c6c140e64024100c210140d82e12240680e8400380203007940304141c400c271120550490744400411a21074040c041a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 984638624 1250 984637374 984637387
    0x12060411130e0604020a0f0b040303033801080a060b040905044707050711151b1507050a231c050604050108280507080706230d11 57
    0x250304841c01c0030b80424481d0009010041146040c482c01009005549940d0360464100183c4d4440c0b40954000203082c10344c2c420039440c517001d03145554200c03002d165451301c4202440c0d0741e204076001040d0406501182c500b10114100c10400c1c003c9905031010400342608003403034080484094880580142e407400d16401e55903403041c004000000000018030642c655108c0300b41701c010803811010b004082844040014030004031350140846900315040f95929072403a0000000410070a202070181043c1c00001a841c0783c0c8090130742c00c54210000030410b44208400702c0c03210786008401100c80c04002081085035800b2a8002d00f003802d1000303844c203062280104021091400e0b980610543d02c140b0f00d40800315001e0240f82e02800740d21280c181c5083c403081d45040d100303598820500f45580000c02c04c072050103850700075900d8004c0b20f0a4020003202e400507545c0b034660303850340454043e4000050740103045041125001806d10404000e001c03407180343c0b00400101ca00104903150b0031412444040080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 984639874 1250 984638624 984638659
    0x7120f0b0d050d080a0c0e1215010f092009060a2303010f05061603110115140301060b031312120e010f0b030d0504121112030306010e12060411 63
    0x203030001d05200d800102812090210003521102c0001e05204c03106042803444101a980a46103000c4040c05481204519440007292411700302c00c1181e00c024111003500000d00b21100b900402c08482c2d95200400000702030800311145544068001d801c1a01c0c10000741843e41003503001001c1c0d480e5142f0f0202203007c4d003820070110314901080322810305500030005028943c0d50390b003090011714048600524205850104140c401100301c000f070140244001c072040d60303040070b4000780360482c00c401400e56400d0702c44d0405510224030340780e031034040d600e4074a0100382140080d08072070161a80344c40b010740100c20380c3e840b45080786000d1040c20411000328282013840a02d800340107a00080707000041946c48080030100c1c2255810ba000d584030345e220000c120181904074089406603040c0d052040720700071050030090484d001d0606c42070381041c0141d54481c0b11a00c04000386009030390990742d401400a0b86401c1161507000880984459041240070a0004691114008000d94013800307000501005414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 984641124 1250 984639874 984639889
    0x50303010b030a0b090114010f091a120105030a08160602041a09040c2c0d0c06090824070305091513051204030c1a04051c110907120f0b 60
    0x1c0581c420402000b40300300c0ca94107000e411684c030340c180e031a44080c2d072410381100000d07285014058140701418031418070a602c1849450003401c041804209031045c0c15241a64951191154420110840340040b46034071303000c54801310803508407071494206000c05811801d5504040d90403a1040c2c2d0070000002e038201001c000302001c054401030262107603502c50a103c15180411010300800c4003501e00d118003000848001c1c0ac00c164182091007481001c03002042410020180140a9204104001070000d911024403000e6030030703030401d464a4804035400302030b03011104c841095540c09031100040380b4611a501c919802034600040321808982c041203001c4005042c0c58035411400001120310521008000c02c020b10030686444171b117401e02e03548400c044020640580407004660444100813111640160340103400d00a05a04881102c2d614110720008804c00c12149121a042100900d01e02044001d121701941d85507800740014030f481c41002002c46016105003940c1d90a50700180c1c1d00c4000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 984642374 1250 984641124 984641129
    0x4260604150c020a03051804091502220315020c01021b06060f0d1511040f0f09110c1c141801080c0301120b0403030e0607020604060b0a0e06090408040305030301 71
    0x184141440c0403501250010b481c00580d9140a55000400350000a03030302c40300b107a6500841403041c4c0600490040064058204c01c1c601812900c50b0350b2201903072405903801071007085005410030401d505030100003d0341241620010341a920b007034401c0705070516103400a040c8641003800040c50a50f403507444003101c002e10100c0404561000302000914203044080d85060182103a144410b01815a45c0801321803a040341c020f032036900c44190b4007283d124441540c01030300c0010080300003035403540c07803942d1511014445c220740b907414800c0079a4070b150a41c003183c0f520300801e4041d003407040d10b850510000034003401c06541001013010050303100b4030301c0c0301c040d0106590380708501c0418890140010300c0e03100d01030f0640300d80c081d04000412944031050160321802d42e00009142090313403582010360090480d41c4400c4c00710700582d810800415400702d40c0c14426481500c04009000d080e00030300c56050150300505101c1c1c010171000c68814501840d08551183c40344d00c2c09450180c50359581d0381503400aa = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 984643624 1250 984642374 984642383
    0x4051014130810110409090807021e033a140f0c15060d120e0a060807090b030108210c0a0323090f090a0b3f0304260604 53
    0x14402030001a0083c0002010450202c4080c0700441030009030382e1080c45244561030803103540310303000720401980f08103aa128a4000b000301c0d03891040d0400e0a0352415040c58003921a014582000e40400314205404118000010302e006c0341c030001c850a46017405165403841e040c4002409207002c2007041c07900030007801d50480d082c0b0f0346071503000120510b03000200d004140d124080300100001911000d10154000707400240f02c50402004400a0701c4105000500360780003800f2040c0820100c0d040401e42d8051000c503900d40114030f41e1102c20303084902080c010b00c03606130010880710071000044520a99215031603080c1520b0505580c0440746410801030f011004185042d18a03d0006200c0355414124024085050300d00440100061322940a50720210721405c0204041440221141c1c4490b411140103003405604c800c614055451560110035401054607880c1c0304c8880c0307034000704620081d0030701410043d400c0c18200301080706140c021000300c04070344402c60f10310810341c4030802a0750300684c00f4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 984644874 1250 984643624 984643657
    0x2060a0c1e140a05150403090b03010b1b06040533010806010519080307171e030a0b030f0705060f071b03030e09060120012a031404050304051014 64
    0xe00c0c24800205151820a0580c3c004010701c03004030b4408603450800802d1201c5000d2255079078501915000c0380794128650000012001050307841c0410002c0022211401841965500c11030280b59500388c2150300070496000603c0300c3c200340011035040a406075000c41d240144800784200788408403400d0384400382d180d0041004021310f04003500307030909070300c206505e180800d801c0c542d89555a00c05d00a004082501010200000c20320000580341e1641e031013520031400750600c0c00601015001034801c4d5101d00e241401c000c0f51480d00040340d1998000290203822002c1c036020400c82590000e141681c411882080810001030031080e0410410020000d01340741517066090060405000c80b00c070030301900b54241882a945c2c1c1000d40001010519000502c9003811800e005000d40b0484030025000410400072003400554428520780032541d9507410052041c00c1c24000e454010196409420350304100001e000360308148940030107004070f07428035031001e000310710f44000d4a91100c1e001c51a140903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 984646124 1250 984644874 984644933
    0x20c0d081207080420010c060c0c02130e06060d02031c02070609060f0e22020c06190516050703021501080a0b0705041809050109050601061e020a08030402060a0c 71
    0x14200701603030810498603056100303181ca96500c030b0b5010001920341222540003146290303168440c202031403640d0b034842014030840c6911023003e0035004492204030b11510184c05000318462442c803400340e08041c40801000315450381814055002a94901a81c05000e641c0c060b01d00000003d2028008900d540e00a0220504c0c148009140b01320541141c01044800d003034040046512082c00d01050b03404903503101600c03002401e6a03101b0701e84950a00704007800401c101d42415004201c49220b01e004500c0300082d1400c4202c440d045403030413260740c802e9074071490507000c81754171440c05001b829102c2d004581c021320050014040d400c400368003180d81507000c110399804101050703c00b150840b5050902070700b8507060242c1e0036141040342040100c000e03641d401741000c1c03180940100000f40c0c0c0020a807011540c5030103000340b2000718a20b80140c8209a03410180d151440040c020100d02c0e0011541801c0d42c4507582041400d03400007080c0d4003041405c0c070018001c28604520100c2e6045e03210084440845d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 984647374 1250 984646124 984646147
    0x1b220b030a020621010902030610201f05010b0c0a0816211706010f050c0115090510062c0f09010602010b030d09030b04170d0905010c141c0c020c0d08 66
    0x80d05820401c6c0150060043c00041d032146109000a40b085080c4100c40c04100c6036800c181c0701342c901202d07003d846030380503e0359a490543c000c119041d00c1e400b020b111582c2c98041d100828420f640c890300305a442514000041425030010b4003162408200c0c0461140c2262189040320300940e061201c0c0b00417800c4441c264603000303901d050725401031075600407483ca4030711300180000350304400307c2007070000005001001c1682980184620004480d82c44011900c941c880f00080c903003260743c2036007429a07032400b048581c040c14074070068244049140151544041d01254002d42e00030f5000c1d000405400800000d9a03000d500c540030780304e541d000061b50201d4108052500d0600c000c0702041c1b1000070030030300c0496070340313005280d201c0d800104180e01c074545000030a00502c00c0000c10385041c0c1c40d000c00202040419004690010003d984a1204602d005102c04403032040a100700d079880074200e010541140d280c0c210310406410f0b8015540c8605103403000c6050241d080400f101c1220002903201500c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 984648624 1250 984647374 984647437
    0xc0c060923030c0907020a08041d10030b0105040c110f10061e09020705031902030702150301080c040e120f1c02071203020d110a021b220b030a0206 65
    0x407001a0002000c2070752440865242c0142d5034031140101c2e404000241c01c00d0007003221004d090350200d8455a1540c2d03815a6000003100c0e00640602041c081001c9040d0062a01506003a00d4024019040c4c90f4030300300401005011628034030092204001c041c8602000c248040030289404002404214440b8000c060803640c01c0c0d0045004090018082c40c810120114800d09842c8902070041e0303100c409081c003520b1030055460700880c4110791704800e8282540400035100d95031007581e0554a40c1d205550301d0030b01d408240180c600e1640450044101d0f480d080e004002410004c40a441e0382e0100840c1841c0d15a00c0700740c80129244000030b4100300b2118041500d004800411411420440d00b40e40301c44810003203501c0b403020107030017040150058a01e507101000c6442000b030150355070076142101039224105800101c0106031415981c40003410801d000384810400382c0103070f0010640c0c1030500300040c208540300c0d64241c8100c804900c0180c0b5600010401e0313418403c41c20340301c0400b01d981400382 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 984649874 1250 984648624 984648659
    0xd5601231f1101150e04060e030c030a0215130308130b0a092d080c030405060706090519050c040c090810060e10140402070201030906052401090e160c0c0609 69
    0x982c501510396410350041d000203010ba42e0380b0005d850b000d44850405001411540307041e5012400005100c0716801c0d0300200606161a154085d40c034440c02c0d001c00c82c0104903040320a045200307940e008950010340b00385003aa0f8032401c031451100a08900d074990103002441280d1621300c895442e01c5400501c08a80090460350409854040b410302d810000030890890400c401440380b0000b01c0c940c0780b80700d814402e45000d01030103850141c6480c01400c0c070b0341c042c00010000380c60300c1c001c008101c840e0781c4141590400c640e0b0403600400e0748000b26400d201c010081520408200040c514010034140d6041c0848040c900040c1d402140d4203041441c2c0f064840f1000e0120048071002580c01c02c810130070088a090580e41c2102c006131038902c6800140c0240002e480000c00b5a0300d004200105011084840f04556824200c5890003101880042d01d1800c0d40d4000c062500d5901f0000030328490160f0101c0c920914107140520000b41269544001e200103074000300040b801c030450501001c074404410006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 984651124 1250 984649874 984649907
    0x80f0d05010f14030f10050405030417100b0904020901180b12030405030f0d0807120b090a2a050706020c0a0b040f060b0114090d5601231f 61
    0x75040c1c051071251b95034201d1919050103030758035200020203000c414820307507004001d0306035181504d01409a038103449404130300e92101c0c1940b1301003603e00181428501c40340b00704c0c4c0c040c00c1d11a040c1d0078510414010600054400c43c4540c699010481d0382c0c0356106202c80c20b0085600454465003060101400e100507803c00e4121540328084941c681a030045515401c1809030800c11845003042c4440005070401049241d00b1851020602a854a03e0382c00211101ea0340046050780006109001d000b98100da02e40e1000a0402c0c050710012421135802401041094821100b07408859a14041b000c0011102602d810220a071660140704140c06903000a20007440c00e5205440c0b20007008038207020300904140280780c14000d1004100104403414404248404511b10b040901c0c021040103c000c58182da031090160042110580c815a00b0700d038440c9400c01c03040c07000b03031b0800e091604140152076514105410340d41e40d5252a80350f801c40c0e4003407061900104481c480101001803c0c00604450651 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 984652374 1250 984651124 984651133
    0x906091109100806011202030108030a112409010e0a081803060f0c0a1215030203070e07080c07030c0813030b130302120d0905010236030604080f0d05010f1403 70
    0xd9075166442c614000042d820520700390b0715000300407a0011000d41044210320b10010001c1054007001021782500c2d001075803101100e45050314110346a0341c11040e080c030360300c813600710524402900700811940100d0343c01c0000b612003910222180703440d0611800381c404440005810400203911484868a0700c4294003c144505005690040045008014216641c1d01040c8100c10358440c1144841c4211213200a01a10741000d0030320050201c2448224864850070074005508250740f54081e20078481611040c00c280c0d58420010100c6d409080e0444c1001901d107401400190a2006440d81102101a0f0341c05241185000312a040c4050024500840c45480c0d02d000607a000030b244003041001c03202c0302d0710b5950004042c0064050a40010820350001c1600160407406d0313103280305400b5804c60607884911040c020004968649040f890301500840000f80206240c00010312501c4124200a03243c405460825000c454080c0c2200d84040850341c410411000412015003602d0340403005030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 984653624 1250 984652374 984652387
    0x10606051e04060e040b120106271103130314040e0a050c180111070302130f0b0913170706090c150203160210170906010f060309020d0b18030409060911 67
    0x140026002200c2c141c0b1594581030b940803d602c7d100644190358a03410024404941ca0b000010b1074451100308000d04c2c9162100b0000302c84219008440e140910100c14a02d0340d12a050a40e015500c1020180c0900000d00d15502e003500b15000280001e258014035481c2505146170204203440002d0283e030814101032007200c8213075611002c180c0c1d107584c0900700300d4240b842e025070041c10700c50550700c0039502c004c1c02c0700d41e80c00d128035a80140c00c40034107441080000015440c208040a2001d4034400242e888000b0100700041c4c6120701c8010081420510f24200505565900180c0320f112508860030154000200010b1448203121030044086002850270400a1200d2040188100c02c001e4070600c0f43e0142515404e0082984540703641c0991a000060701c0c0c6405450345e121400e101e000000f80c0d01e13810000c7c44a20030f10410b1043c65008204206608164403040c08050000d0420070807060403c08903141e0f80800c00081c0000c184c1d0143c046003140ca060b00804c00c4401481052000c1c00c07003003104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 984654874 1250 984653624 984653627
    0x1e03170c0d1104210c09020c100b01080405030d05040809090c070302070906140d0212030309071401020d0f051305100c020102061e0105090c091003330504020912010606051e0406 78
    0x5500b064a101404140341315881c02c060910080c07a42c041c0c16158400640009080c1021540b0038040c1c00c024000e0149601c81d2004555800044501170321981080c040443c000241d80c20054000340100380c80760800c0300940006050041c10742d80303a400384200003035000070136405210079001408010310401c10030f458400320f0490280380400d110312074a1041e217480d045540723007001c50081d25406d10840c0c0c0c0703d1415050041d91100203001d40407804109401c6007640e91320000c6c4004c1815450f5880003480c0c90041400d8403540c1004900940080000601088030b80764100d468003040b00c96510484400c0990001a0900601400481c00700005544941c00c1c1c1640e2450a4111181a20000c007039603207200c1c0c004014000c4078505540f2429000880c00c14a0303058000b03128002c02041c03a03414402a080c0301d001031000c0010700e0042d900081400f003040e40383c903034080c0c0a42c850107010720501001d4404c5143c2100d510380c02000c042400418082d45440b64611004038001012884d2031616051600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 984656124 1250 984654874 984654899
    0x1205150123011b03090503070f080a230a080a090609030507140a0b0304050307031b050a061e020d05070306050109142e090806060402071e03170c0d1104 67
    0x59400300c401c96442041d440c0c0e44a40061541c0f00c0c40c805480c400f42a09260003000007026208062103403046c06408102c46003c0c4103803008540c60700c0028a8903a001c4d50b241e00c20040060010412002c80c502c602001c1041070048440c3c00d4894135000b999100703620070281840c0e40740d800050030031101c082d05000041000511a003510103a0358144100c8103c600002d014080c41d820491620300040b042c00200304000014200261103510f070600c0208030950450701c149048100549154060407174200032500701c3e032095503616000d124440c9282041207110050ba0f0040001c0400d1656510800171250307498421100602800d2a0641906180800b0403000045041a01d4441c1950307a040781400c2d50842d0f5421161041c01c91601c2c6030f00c56121303018014403114400c000c0140591000112503190a100705c0383c5c819805029003440e07085072904000d4580e00e10408070b05220400c224809803043c241d01c07584c4210785040d1030a60315448400c030f500558001036106051000c0c14807007130019006005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 984657374 1250 984656124 984656159
    0x1050a0516090305070b2209060617040f140102091507021806060f0d0216030206070305010e1003030809030c01050f1905070e04050a1413061802011e020f0712051501 73
    0x21305880b040d081d03a145503508103c7d0100400784010040001d42007203550082011103419032220380341001e440d2041c0c5214002102d006000c64a40025200020b0300054140c549241e40c00c001824813401e84c000ca00841c01c2803015199103100403c1c044c08519101740c2c105407042e50003c2d001103900f408000700e8078074003078815a24a100c80201e07441c0314002159068035805143d40000d4142103e00d814040c1d244c003026204c0c0e100180c00d0000101d540d000c14407600f07001e0095032407003034900f51668404584002003d8030750400350100301302e1425014400d026141c0078110300501c048480c1846244105040607007190303070035880e0a100810815503046901e5020444060343d0100f25580d5003880d50300100342c1c0c00c2d4803540c0d92a4000a01126400c0c890401c410306200b802c081265040c2c50004086031012104020300140a0401240a001c1c2c05403503140d00341600e00441d01c039404001c42c2c040c208001500040d146640e4180c0e24400c1c000100321070030610300e140b01082c52950400090001108221 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 984658624 1250 984657374 984657389
    0x509090411031c12050c04090902010e040203180f0a0507060806010c02030114060a060c020a1e030807030f08070f1d19080a02040e0d020604020108040f020301050a051609030507 78
    0x200004007800100710300007001d21801000d489804920103045030200090200b5100002c40045512003043c0d0640b00340b0b40a0410000d50904051418114034050b0401810483c100003001c900d00d8841d4403240051801641500800b20000500d0b090303491610804200100c1d159110f08451404a04040707a680d042d04d105191103465543d681c80180c440c6020500c0003034156290188d420101540401c1c15806200100c4100c424150707100412200000304800295001078803680402140c82902c0420303424013143c801103030680c0d58949465007107800101c82a0007241464805010982d402a16941c2c4102103041c410000c0140706c03c02092340d42075000c0e4211240d403010341c100040d0756000c1c00b50011290803140b05505034a0742015a142d00b105503080303000b2070418003095895179020481d405070000540c010b000e00d0707482c2d0b001140e1688002d001599242e0002d041d002c090b071001c0c015940f00300712046010589090009102450000100c0c4590403c54080420300010703030302040c00c00488188 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 984659874 1250 984658624 984658639
    0x518010c02210a09080615030c0f0112020901021c0207030c05040612060b0301110705070f0602071a180604030605071707050d0902060d1b090e07080a0c030e0303100e0c0a0509 77
    0x1105420f884013040f50f0081d03102da10803002000224016401103181901064068581500c0d14805001d15500c1c4140c3d12404183e41c0140844111200d5018004120052046130070744543d00c0f0300020710182c508003040c01a04070b05014010300000c1c03844c4100030101900c040081901c1c2c072400300944854280000c18281c2c60b512104901e907800d4020001d00e0140101c455a0340ca1140307000d660300c40091195416039442800700050090001c222402200e140f1111030509070048402c11810364040c0380300000038029025200764a4031010050700103140b140c0e00004042c1000c1002a000140003a00c01c0440b881c0341d81081035580d031001c00d480a101c03144102259121003440002e90600032452122503081c90b020051a54421440745148080c040d074a40d018000c4d2240d200b07840b02841141c2c05400b043c1280013095451449030700402842d00b113450009080380c200d00c02c0500713560041d81c0340344240c40006820b1001031140040356400038441d00034640340415603000a0300c43c1c05228a6a0306c00c011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 984661124 1250 984659874 984659887
    0x170304020a0b03011502100b0d020904080409090c14030a0c2310080f34020a050d02010f110412021504080106060507120810090f0209040518010c0221 66
    0x441c2000c810140c02d020001d2038503517031644a540b54040c8407030100d500621070a8184024040580314410300d90700040c0c100c0e80807a0980c1c0038485070040280c400c80d1000020440002c03901120301c6100450741c4100300348600301d880c00714091001030700e4800c0240710b0313040a049103000070003047c1c1d110126010307000b117840c1c4070340d0030084504090682c4034016002454a2081804554041c0c206446948080358400e010b8591410300c1e03000010101481500d6509002e48045403a20040107034840c9105204440c52140c640c0d480a050104102138000940c1d103604100318403032000c0c0903a030043d003404951302e403e25240c0000d074400c0c42c40306140030b401600d1401d20314034404140300031240030344112002844040e0795044018155403200d02c0942e506080440f46440c140d100d00b054901a2a000f03041144072800d124014004043e40b81240709165801c0000b44082e4545001d024498841c1d5400d280e4840005402c50f800d4640d000041c81c115040708a0350a400000c0118000300c03030700256000e42c0c031a90b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 984662374 1250 984661124 984661129
    0xe03090a030506040b130b06220e0c0a05010311030a0c020f0303090a03140304020904170415020f01050c1207030902040207171e0405062706070b070e030a17030402 72
    0x8902004550031055184022040c0100050000d0103184117143d15046541c83d035040c1ea81406160200800c003040311404100c251411024841c0c1203407442030b1012520a2480d03980040314030304241c408041c2c001c165001940c4c54458640c00040000f03080510452030309030000b41941c03000528084107180d91b10b20140200d40300b04424068542c3c1038007220350701e080c501a225036480d102a01100014400744416403c4c0d038140050760300603640904011401d45580d914a1107200000c60f002c00100d0081c040012151520442c0c41d04048690b005094040c6005030420300352000100140901c49040120480c02101d01c00b034294802d00382e01c0e000415804034400100644100140581380c1d05c0c2140c00d2906105034140204045042200300c05806d40c00004500401c0c051072151507407040741880014644902016205140710b80c01c400740f004402c4a000141442c0c000701416500c072180f034000c2000c0250041104040c0f00030403070040400140b00c1e9140c3e50800070600b11640300180100100f011034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 984663624 1250 984662374 984662377
    0xf0e0c040509120f0d0b030312010e06040f020a0518030109050a02060d060f0603020910030b28030b090d02060f010b03040f03030e06160e04150504090807140d031d060a0e03 76
    0x329200c00f1039880b14103a441c0c2c4581d801c441a8400700f01d01c0c00c8050826480c000040356074100038802d4500c81da0f0f1802c10b031446403090003410903800c5611a0b0960200c08450702c01061103411949420343c80742c905010803c45141c031560854000d038500011072010640c00240c0e0307a14643d040b01c0503940c850f903518a480c060b1085600c003020b04034a01300c010452a8140d005044486010303102d5002c1103282110031010780381103001e0180c01500c14100443c1403800c81004000f032420307241c02e41e10115580e50303640d1410030003103940f06d610350003006551080503414400e2030340000c400400721405504100c0c1152440c48040c1000340401d208080b928101070194101d0f1500c90516030a8a58901e06880d070000b40e02c40c10000580000d040350864015490300f0302c43e16120f078028044119050342008203001c01030201ca902075814090074002c3c0400910840c01d40c40c0500001c8000d4603010a23000009015200c03490100400f0340d424070360015110200050242d0702c5000c0e0074002c60401d44480e40f09086 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 984664874 1250 984663624 984663643
    0x15280e0c090c0313210e0906011d0f030a0f0f0605090304030c14040b0415090c050a081303180609030b0f0403050702010e150a030504050c06130b07051f0905010f0e0c040509 76
    0x39410392171030000c0d860300a50718101d28142030b03650744c0c2e40341c0d103d2004580e080c1c0300031800205001518ac004420b400c0c408142501441c011b41214024241303920b45900c110000c0c1d03421122900b58140ca4810410741e1300401c4d800154040c0103504050a40d0381c0c541d120310f250f0240b80e600c3e0030450b94131031590781c4a403c02082e05801038070400921f0742c0d4504608548499000f90403820f410a18080c05142c0b01e20100e9103510b55a0390f62002e03644801800240c021600f040980070002e11505154411181e501d000c00280859260080c4952542c68900040c1c40e005000c401103030304104c10400404c1d003000480e50321700d9091a00c90011490900041c095150f10102190002804182c036010b00da05035001c075000780d001d0307411a8100c4580100f00260340c41080030f801c0c103e40305003104100800001000d00742c800d105006441600c4034120100d5441d10300b040e14038241c1340d1104411024801d0a00c43c030141c8040c2c1c4c14003032250a9000c014a5600da0019015501a654580010b8031516040c4103d800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 984666124 1250 984664874 984664913
    0x1b0f0210050703030c0206390f0c0d020106030b0411030a05030423090106020304050d151b030b04090b1603060b07030504050117010815280e0c090c0313 67
    0x910305003100018070301d8010400403004246050354501520340000b40c124031038000348000c0b001000806411400b0b031102030b4011061201000160100b20300d80c0005040103030030040e42da0b41c56100b0f500c40b06140003810400182075914106051000c982e13000c1c0c415031301a40120124820f02440400b00f860400c2c5071001034100c0c0030121700410028407035610340b01d03a806a6860340e0003040c1c1e5241081082c032000e105000c0035038001c10040000d0b0814140c1044038900500300c0000305000030400c1000c0e100300c2d480580e641c000201c2c81711200d58041c03084541078402694104002141d990751551034440162000e24540207007090301441074400c0e0400800b51482d02d11043e1149064600909550868003415010401b0618a140d4070141d03521400c3c12030324000020704001c804206074664084006d880c12240c8202e1040f1104080f0360aa0402d8400d0031100001901140715101503081103102c00005229172104010b0200207a0000300b600d40041c40361a24134401c01240c5270034080c0000081d00c801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 984667374 1250 984666124 984666139
    0x30b010902072a1701140a0915060b0a090816060302090d0f08040e06030f0d0c03111509070510020703170714150a020304020105030708100f080f0c04020702011b0f02 73
    0x100d4070524034508000c68494012161680743d00148185c00d880d03183c25810010708920700020019030103a080340c1c0e0030600648046149500ca145041d060728825002945d0f880d50001e620312046030301c40901d400030090318010b814a195900f0011803020024456002055004076920040d0b41e030307012f6022050f5900c600b0002c1c600d07a581c5040d000b15001407245964400745d500004500b03080101c1d42c2505044000040e09582942e45d506480100608600f40c0c204210b60070261005041088400390001188800a013240f85c41100b985c0b60014940016000c0c00c80800f9800e46607400241d4401680da00c0b4200401b085d1401040007481c0c0250200135000c0006c1c4011402004008103503011603660040400c1d03195540d9604400c142d12003903400030700260042000900032172040300f0140d04400c1a07200c032500107a80e0601d00c1703800d02e0303603400191240d044490b1405018108000e03041200e44155000d5041c0303044c07038001806425001003030100f0034842030303001e208102c41d02400c100040d80c02001e0720b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 984668624 1250 984667374 984667433
    0x60f020c010b0a0b0301050d080310031514090f1f1803050d1521051507020d031d07060f0c02210115050604150323160801030b01090207 60
    0x502801c01c1150b014000c4101c1c0101044020300e1404883c140c0da0701404419000c0c00075550052990320040211088055020020001030304003400792201c802c05030408034030908030340080c0342c01c41009008603446900004da0225250008289032400441600d849071144800840100240c01d1403802a80c000c10001070701c0c0c0816410101421002194041c200001c1c220b120216041c1c1c0c0060040306464510300d1262001d00488040f0000d10350f01c18019500303c054120910303a000f210560340800540c2100090008080e40744c414007a104081000415070300c03441299464a41c019401036070300f00484014581d00c418020707944502ca40c1da000d0000b0140720030788019002012440f441848040d420701da81800103001400c5a8420344100404031807500346440240d20382e003407040701e0385014140c440720944580140ea0f030480a190307540c1150810640f424644d16005019454020414814007500601c0410340092803541520303405400140e44a4060a0006249161048140ba140f84c6480b44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 984669874 1250 984668624 984668647
    0xe0a240609050c120f1003060b060d29040b0609242b0903020d18030219090b0904260c01020c0d0206010f121b030819020d081e04060f02 60
    0x4014004c84502a002d0f0f80c1c64071005400004000c0c0c5101c0074080b1101c2d018030100e807151340140d0306244000e154501d080d4800340120141c84800700309600e100c41241c1019624610a54412403910003280c0402a41c403000c000140c25000741681f0034050010030f4a030841d040c01108030382c00c40740d9840d01c500e40c80f240264004080c400c40c0002d09001c590510101e020144c2140c041c09206c02d601d600070b0481c5141292084a81c000c440c4508218203100c801d001000d81c6405268100207044400b004000b41d00301305111054600070080c942c010a0103404000105098040c1050f81d1040900c600300200c2c05050712031294004c084403171425504c0040d03001c119040014035100c1c1c4414030780070360300240c0e40e400c60155151034a2044c0d180d40003411070362000050401c4655a14071000280c00c40d801030b2607460303504554000d80c2420060500c203151702c40c01c0c95010003002400103558500b05c2650300e03142c40f070402480030420401098540c1a00030601300452900300c00d1440b2000c2d10b0440d02c6600c0000c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 984671124 1250 984669874 984669877
    0x1403090c0604090c0f0f0804060c0e040e0f060c070c03080c0309060d05060306220305030c0c0102191206050f0f130e0a0b0115140c0109021f030e0a240609050c 70
    0x2c104c0810005581c8407090350240031390044407031058980c21280c2e40e554541034042c0c80d03404000810440010031200f0b060f40c1f18841d0b24403040320b0074000c01c40d070201000c005103400b81c083c2045400c0d0805110341400502d441001d4015241e00c50030709511000034441d001d240d402104002d83d404100402c1d280c080d8009a4083c1c4d20583e800c508540345504e610150400301442040c185002c000a0300000003c280514015600040329a595514120044400c6806c980200c15402e441d22405a003034401e095010f40510380e0b007481d00c0802c200b41d074907040c005840d6026541206000b44c100649070740e825564045150717070403254882c061102501e03601c00652a03441000301211001d9009002160001200c0d00400200b4035945a594404e0013042080b82d154100c030003044100c0d0340300c001140060325580b00b01b00c442e210800c3c41c40d24075440e0710405009c0c4e48910245070440d600540f10800130a44844050000c80a520f201300d00300d0b42c082c03950b5400303410780e40c100e4000e1504005c28409402460310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 984672374 1250 984671124 984671141
    0x3140106080d081603060b032d040302012903100b011b050609010614032d0307031d060915090126040b09030a080613020714010606090b0403031403090c060409 70
    0x40d22000c542c4c464900750101c2c1c0f0907018031f4029035014000034200c09800c429044141d0207103140800e0345064295400955801100c0840050351142c450083d03018003102a4100c421075105642400112103010940d03c1c10b04941810440da01c0d00c1d0403010a900401c00045c1d1070748412007032200c1d0310450070305e40e669103001d90304600650f180140c0010040440700c01c0d80500301000f8043d001c43d621446180551502c10b0012801134000340d41c204041c120200020100f45200307403244c3c198500ca402400300c84a90709403083e801003004101781c030801d0b40c0309492508a102050613035519010102d004840c042d803000c04a5249504095a050a45081105072441603101d01011032507035940c015550f0b12806400d0b00d034030200e00710ac0089140c618010801c010014500800141080300a4031008040d20215000302f400b41d40d500c0d0f0902405601c044100c01904400315407a1800f4915a00103080102d1004440417241021001c0f400ca4103090204010b046070041c025900c40d0f8607202c0c0300000b0030480 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 984673624 1250 984672374 984672391
    0x210709080708010c0e09060114070b0403140f310303030e070f0b0d020d140f06191503110403020d230d0e060a0e0306100f090203010f03140106080d08 66
    0x2070320002a1aa0140501c00000c0010380e42e0100c0703030704032500f07002c4030031000303000c7d203040c444100a1507031064081c40180c11000d010b0108c0400c64181400e01030060b1030780c1542c0c201c0d40d1500300409102c5402c1402110582c245188000d00c81c580d070640c0600c0d42204680440c40140d6800c0070002c01e040e4560050006840501f055894142d6920049203101000307103d07590316100300f4810320452000b80da01034100284194170208441400b0151080b81c100220b803e042c11041640500c40c1c80d0400c800c0301104040d070840e803151102c3c1007100010030040c1e50000340c41015154005803a07103005c000c2c20794004590140c80030302c101845103400c01c1c11006034000b400850340c0b001d0814102400c0014012200c5000741c480c903025104084c14400310ba40699a44400e0159516801065840030005107102d1034a524145030380c0b901b842d001c2c4030318100503444417822900507c01480303c600c400b25214222544110856100082d114181c0d0240200d9400811140640341c84141d0954000c510b90780b081c440d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 984674874 1250 984673624 984673633
    0x306010c02090a061a1801050706020d110304060c1103030114060d05040c0e0c090a0626090309010e0d0b1617070e0109051801061209060608030c06070c03050304030521070908 77
    0x48405c0e03000c007400ba551041c2c04601d417540d0140100d5005400400450380180400b500e40f000c00401c10b07040e41c200d0250883c40340c2d0000100401c0c411141720700d002600051030040c0d901082c45545603a240010302600c40d219000098100060361400200d80c80081e84017800c1c0300c3d62400e401c02c0000b1024510948405120050000d071031560007804a541440c0010140176169052600031244002c8800e0120004240580100c0c60b500078907800c5072040140c07800640d65409401d00040036a0560699240291907020705807000821842d0815401070000015203c40100300f5411640192007644200008120740148070001d50701a0f0200001d100230f0b202c240000399600188032069050400c22040c007620747c001171207821310800620429901c0418081591111616554115081a070015030180c1c400641c040c00240e060004540c000300c2030814024000305a1406441071000a100404101c030000720700c00c11460300d9501d0202c0801900111a051500440140410b5020f02030b1400c0c074130a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 984676124 1250 984674874 984674909
    0x10c1a041205040303051806090613082802130b060307020703030906050408031e220e010909020102030712030612080307080c0a140f040902070803010905010b03070c080306010c02090a06 82
    0x2d804642c1207aa041d07513518680f84010110031030301a1200c036860760114007000060010fa803928080c1a016415080d0015910302c1d0090070351401c521001e02030303401001806009038820108159540b0070317030152044240034030882c54a00c01803440c8400c25620036030100034400d40c1903000942005991203500d69004145d11400180d440b40645d01c03811030b080e40200062509051142c212001403924009075606101081da50219240541003951400075080d110801030088250030850041010540030482e184060300001c1d200d02c284c000c080c06218134000080d01c606c0c03007540b041008000300c2120045518092600003c0c0f0b074415204c501c00030350302d06c010034000810300d4226202c0102a84030b007030340481d0b00301c0000d00d20b070000341c14200410414440061703141c580d80002c0106074800c80c101941c82d070400b02038108480040c1c01413502203405104002c006900003a00c1c4030400e806c0015142c4035a40c1c01d004885207034141500a40051512003805100d044035081030b0240c48003448103962464 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 984677374 1250 984676124 984676127
    0x706050c19450b090118080a1e020406090902030616300509070f090903081902090409031d12030d1d191707021509010c1a0412 56
    0x40e04101400409a4a15904070b00800e1640d16035420302c010070014084094901e600e8486920300d50001910140c009800d032400d41e48013125448040b00c105200b4621824050002d603200d41c1100700414582d090380c080803844070200b250352541580180300340015520740d040e1801501049500b00c0c000c1c440c103c080381281c1c01e01c5200c11294030195881c076454103020003240d14424008800c0117224030001c031142001a5090084522404004004040c8185000d0040c40070075003035880511018a00340010b40000c3d400951590440d41900c00300303801c1a01d0041003002442440603c5601c14506100b083c10103400004503444050710728400404111041306001d1910000051211160010000c4ca03440d402c143d40107180c00c61500b40c0b10b00c40785c000d850000340781070110070a51041d520003c200344c0401683c000051400c1440064440c1030514036404292840c0c1801d82d09103421801181140303150344280f0560340c281b90040f0000300f40403140304500d60008800c3d5010380d00307000c410760fa003000709 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 984678624 1250 984677374 984677387
    0x10806030c0103051308030405011d070311010518041506140c070504020c030405151c0614040e030910050c0c0a03021503100f0305151506040512030706050c19 70
    0x104405006401c1910415004400402008111440d40d6215841c0b90300400c485030051131285108400000d50f17088d400c400384490b810314031603030344440d0f00442e02800000c1c1000d0b0b806901c1002801c1c0261201c00c5905000000902d018200d60403629101e00050f06003081060030040301d03503c0d00c50101d2600803403103250701445641d0200c1d156a1041000b00480e007086d500030701150f030020054030305107629540028810007040c401c50000d203002150f6410300b1024800103424141c62080b04004682c9000c842c20940100201018866613490501207400e00060040702d6901e400200301f072109882c50040644290000e0541e20744e244500d9075850100e041003060301007a00d0300141410f1408904507001180ba901c01800b038001d00c90560b400051003001c1c0b42d100c5014501c1540585004120b07900c0010010304010281411000d401c807080c10551210001c031000e83d102950036803104402c0030300705440c500c2041d84c001c0c502d620300000c02c03440d0b4414001900f80420080b10502e4251840c0384100e451 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 984679874 1250 984678624 984678631
    0xc1c09050603042114091905100809010507050406082205010510030c14030601030212010e120c06090c0a120503040f0914132013050f0105040e070f0306020f04150903110108 76
    0xd117000f003010320302c07910b464403845d0703c40456400e954400940b60741c0030482036404040600040b8200c0380910202007802e0007582d81c00f0102c1d150641c01c003403510100400c401005070001040100b0342a42520081400c140000c109812400038009811b040340d1001400900d44410345841c441108003140c403207160361840443c03140c000c00420451342150200011401c0c2c2030a294503540d81c03405440d1050b081400440c0200c000c500c0c0c0340b0740310400100304500344070004189420507000100040e841d580c2e0610b14809455002c50001e181070b01034a0158510f20951300208441c9901100014000440b41c0144409520500d00102c80d44c07550045180242030a8000038160304e56440088075200d4000300c074220b035000003800e0420703400e280d100441c21100e003038520341c03207840040d0014021402d00f406011440000d1000400382540380c203038040c555003030f140801000150005801410303a008941038401801c0080c0880d5a4808104005130905c0c0f4944401c56145004240d004655801034050510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 984681124 1250 984679874 984679907
    0xb06010e03060f0a02031f0b21090d03320703060608010e2202060d0504050105090d0e091b0a030e0c0607081207050426120c1c090506030421 62
    0xf001c0d2607200c4500040c4d00020408910f40359000c0644400c03e01eaa0035000c0100468454030303030b0741d40c00800607039400c800c0e600045480c42820f0303051000d100381c00203490355117082600d0002503441e4844010303005a541000d150503410f182c201021801c00310114001c0c019002c5840410155554640a03900404248607001d004043d03100094150019071920b503405940c992455070b050b10490340042c03740d403c5482900040e42d034800802c0308000342441655040020722004094145103c80010180d0100c600f00074013a507018004103103041c12001d0a90850316444940176190b4408000042c01014503044010891003a50300c0c880302400e004003182c00c0d054011043c1c9203000c1c5051941c1240c018003034030381c80801008000001b0a01440312129007003218100004e4070400440381c50700c2c9410044144220700b400c0421540d20880400138500040071000002013000d51910003044d0b03814807840d840a60490000070802040000083d0181d4801c10070400041503504010380496403c0c48030108800c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 984682374 1250 984681124 984681151
    0x30a0c150c2109170f0c01051317010902090c0c06010f0e010b0a090f08070609090c0504120f0213020d0c08010302010f030b21010b09010b0c06040803130c030b06010e0306 75
    0x40200c001060041e540301c00c5410400e800d11394030800c02c400000c1520603800250400140042c041c841808a01010720302480e0480c03d20241a42e01c10f8520101c1c4141c0c26005503031045038007000020341099032425002400c0c02c50f1860254200f0003980d11107050809540100b200104006603c003403800c042c4c401382e581c203007501d03800e203400420f803035000c0a00d41062110640d400680c43e880100c06401400202c4054020135107003890203090f1480d42e402040c0503030308181400400f03a9104003601c0498101844440c1e0790350950800303000e00c60401c04065040349010b009075050b840141c0060031503603014034040201d081015000c0350078060a0000034000344545541c001d126100c2d030030541351080001c0404070455680e00000e9200d151030300507000c0300d035180c03000724180d841e0200c20307a0300501c00d090501c1e18004480d000c460b00d80030000e000800d10301005c000300d1144106590b102c501035903c404403d5010780c403400e14041c84041180d00d45e00052002c0410344081c00c020850500172003480a510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 984683624 1250 984682374 984682403
    0x1303140301030f2d290f27010606170106080906060f040e100c02071e0303030c210f06151b080f0301060806040c110c010f0905030a0c150c 61
    0xb42000300a0384c0300c070b8090003ea0a0440c030344802d040c40c5040040d20540e4440404160055008200c0a450b400051502416010000c04d13508000200d03500100c1c0c0c0303604c3c11562070390b4041111003c8603030400034015868627002152503504640c240504c581c1e40300c0c41c80301c541e80e0f03428100c40c084c00441d144c0a00c2e401c03c40201d8880d013408603501a18000003840415281c4102020500c2d0006016100e401d054690081e00134498062004402400034565801c05180120381d104e03050b0445440000d00b015039540c0d6601100f4480c07281400c080c80c0d54500403408808008818024103001c110546101c2e14000f00060701c1c490088541000300c0c0316466501c0c100c840d20030800c2c400d802c100c809a4100c041040500e1104e030200b0000e5002e0005030311740c4401d608003c01070104851410b02d041042c0080f4030400506501c0000f0401d40100003481c00580c00c00110708202c4c2c11610961001c1c3d0140325815840c401c0011150002e425a000a5031b01c0342503005a4800311a9400080c1d030140145640030b503070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 984684874 1250 984683624 984683633
    0x5011a0f0411040b0720040e06040b0901020f0304050f010f050720010f09030f0f0e3718110403110d1e0b070f030c080a020c0c04051303140301030f 65
    0x9030b2018680540301801d01c0e5440694000da544a040101d40700b1003010320317141c110100e2142c2451040e100752410404455030080b09540c48402034270140c200c428281c00a085074000f50102c2d40e900080c40d00306038403070411340f814035940c2d19050748160f002d508113242030400700b44901c42c8a10038051070703403801b80014a60200511881d80044208030315501c4001d82c3c079089180c1d02405a03c640301e0390310f500680a01081c000c0c401680c0c12000820003000002030099030350f03245125440010014501d005889a04400e1080c800200c1c1244a003200c840d50002144400c00034401005802005c2c144447d0120819101c81b81c80340b400003c1150010441000d51410250048110188a080d042c642070310412603c585074402005c0031070b08441c40404100080358002d050000031001420248515408514041c204010080c10850420790100b090074041800b0070500f55201d00184c81040b242c1040044003034031514402d800d078040b6818025081150840c401268104c1e074000300800d0b284c891542d02d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 984686124 1250 984684874 984684881
    0x1c02030f0c0c0312030420060d02090102011508010e0c0a03021809030d02030c04030213020a080a0b0112023c0301060305180f060411030703020d020d061103070c05011a0f04 76
    0xc1e840d002d1069440455668904201e0030014260a0101c80d85a181038600138203010400541c0c100d01101d02000752801e03460300d0003a80c0c0d000c40d00300030150300c401d41c0e600100d00600c49108103c0b142c203030500300010702e80b2041d0700c80c091495004060b100b003070503c0300c2800020202440000d4008217025108500c2090121103a9000150141540d00d0004005044804ea80081d1414015044005400c0045207403842c5028552102c0702810343c01c28000900180403014000c044070100b680324800b00582d40e204841c0f000400301c507000c046403a0200241c1c0d079030b410705014480c0468401400241c0890b147c0000740d034451021920190ba25503030a0400880c090040500402c41d80c5d0140415544400410f120801e02215000000c001034641410701010f44014251098001c1c0c0001005001503140c04801d4944203070196000120b01055142c030000034480d1180003000c0d0360740441408000d5502007406240c0d1800f90009011401494170503502d00e049060000350b01405400108185003425003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 984687374 1250 984686124 984686137
    0x100b090f1b04030c05010306090c0c0605040204060528081c11120d050a060504060b0a1115040302071701051e06010e0405090d080108060906040f0606081603051c02030f 74
    0x101c622520380c100e25440c80d241d8005400440302400c80381e00901c40c550380341c4034006c01850002c01c10300850205007005061200314100250203607403510009401d64459401c6800180b1000c0d001c401d100420310741c0e183c40d00d50ac3c6080300410002500c800074030305000140d4094812000c3c61100c01e000000042a21040421250401c071405640c6144041000c04405070421900309640070885240000c030120454289821051086d4a411001d0000c07440007400d903200440c1e80d0500445150a22071070f24a0904402d03180808109038404000c201540402c00008540c00340441c58264160044804e081c2c0340205c070748000e0b9100d07001040a066445500b219041704041c1809482076030703d0000320341581c10031613180030141e01a0b2004911980d02118260040c120440903000d02c0c00d1600c49a51a55409880580080c942503442030500449a01c1580204141c604513011100f20b0702408810380b08600c07090300c2c035004181c44440012600020030040d10300300d501a6181411031140e1040c1e03030304002b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 984688624 1250 984687374 984687391
    0x423010b060a030204031b081c1b060b1c050c0d080c010c090f121101050915030106031d010516113f070b130204020d0c11100b090f 58
    0x4444004598480000030028000380f960b01503030b00c3e81103017041d02035140859030300c0154403a035002c10000403001103010015111031041c1000da18060030011107812103420240035a890801401000700007841e4859685200140c415011856400c03480b03082d00011305d8800b8100c1d40003950800070700d14085100c000c42910500456042c5141b03100c501d030840348054410404209032603030a1000079152a043c00c02003505240da294080c1081e03841b018410850003195050040c0800c080609541c2c200101007a10040040140c9942c5d403003070024003504030f18060488181529080740c0401d80180900303403240100e0540a004e0004041c421104405076500c3c210990098200750038460810864002404034402e019a15100e80c0c004040c006001980c40c1c24180042040064000344101d0b8280b54460f0600c4d00c0f40c2c3c5901007500106010344210655127117010303e0091040034480d04003407504000c20000089400e45500c11200c50100c880040c10180d21061140000e0410f0f4040c448407940850f89 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 984689874 1250 984688624 984688631
    0xc09060914010c08030a090302060606090105040902030c0403081602100e030c130e07091505060a080118091e110303040b040302150d1103010e09010615180f0906031a042301 76
    0x280e85071130f10f07144c200f507801000307150711100c0c01003e00d075042041942100c01214200e01d4100e6410020f040c5105621901e140a0740200018009a007000c1c19a0011500010340a03a0b50000325030700d000c04140194204d1050f070300e030620b4038940e074031481c220324147d24040e0080a140d56460200702d03041c0303190510014000c0e1105da410483d03034410b2049000810100002041450304510100007004a82e085140602810b0104490035540524804e04446000005801e1001516030a8010300203200d0081d10f0358040c1ca030002c200c11031a00390a0102ea020f203100d9402600008101030301d034420351049040141050000340094500b0008052031642c08000c07640c03400081c50485810740d03a81540c4042c0910022004001d1840302078a00c6034031083d084000c124590420300110b83c0c0c00d5030101d140b010402d03540484c1014180300010385016003200000400130b0740c0e441d104000a013415020031542209000b000c2d078520b1501c1c03081580142d074000c044414104413080101c41d99500d040710500d59648 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 984691124 1250 984689874 984689897
    0xf0c031506030c14030601150e09072a020f04021b100603031b120e21030a09090b280e090607091d19021201080c040c0906091401 57
    0x12481008005028080e4045800c070310b181080c00a00005500003504040720f01003464a981d80400c003241900c501c0c070711802c0b072180304890440e60780c80c0614589811141c01c20074040c44a1300a200100200401415400111600012840840c0c080740f8000d40280310f11a1801c21458160050114030154441d842e1105100700c1802d441c00e0451080d22068590700d030001d009040d0701c041c45180207000da54103500041400d030703610030800c550f000c50f040400c140c1c11442611961044030001400c00c0900d80d19860b250714182c56502c991120059002203070720000c00040a0109001d050090400240039160504a400900c0039001c2d645007510b84000e42c80801103074601c0c3c0d5580e003070301070300c0c1c298014481d034034102c140a06520b869401c03043c01400b00d26800d41424007446180b40c1d1014089030303841d603011224003480029024a01e00b016002e80440000f180050001a0040450400b244c040c045d041c1c1c44907080e0380308110340c00707a01d0018542c0345082c0002400c0a00d034a0440c501032600c1e140690307 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 984692374 1250 984691124 984691133
    0xc0a0305160623070c0c0501050304080f0316180b030f1f0807140f060d1a030118150c020a17070b07050c0709050108031204020d080c0616030501120f0c03 68
    0xb485043e04002c1c900080b48032400014251141d40c4c1c1c080410300b000c035000042a2211580100c49100301410010000005400c100100c41940c2106c0f00c0e07400c15540321305105045180101b0b00c50340c00c2c0c0020b07500354a00c80e11003210b0f11000b011100b034510204e20355218501c01c0340868200030b100d03001a488030088140d5110800c0c0c0181d0080802c0310240c4401814003001200c0c09960011341440b030005540310b00c4055592000702c0715000341d11382c4e0000d55040d03410002c2c0c410781000196140d00d07500c0c02c12481151800b2001c9018051710038400d040c6420f5041c002c9d0422074082c0b00380100181e11929a10001607045007600903101445910a828040c1c20340c0d4180703214800711030846c0010700118071211100c20400042026100c1440107001e40d40c14910025039071f01a0a021901e044080310201d41907440c0e018a130601540c0081a45944001540186945081c142e0b000403c03000010040c82da094424441c06068420710582c001d1041c4140d1141a000049010103564000b0200700000008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 984693624 1250 984692374 984692381
    0xe0f0a0314210a02060603010b1c170c01060608090f1905010e03030a1a0307050f0d1109070305090f0705130519051006020120070209070903060905060f09030c0a03051606 75
    0x4500508200f0750710089108000d05000780078146a0180e030525243e824a50f5520240e2400510141d91022807036015081c104490254408901116000010032035802c502c190010f406507007254440f69229110341800c2a5915a59081d00d5200d400c6000c00d04001a0400d010321b4000e4020800490801155803e66066500a4451102d0150769000b4140e030000b070301c000260301c840201c001d030541c945420301182c4a42c0110110038401c0300301d6a410010031041c907014a6484034090302981c1c80707103007140c000740040c1426100c6420360702c038510144030621b4000514000b55040a8001408803e048110801600c0083c0005e646000c001c100d0150381000e80c4a1a881032404080c40100d281c41d082d40642101c1781801200c01c481400c405031100c0900c0310082b13560155069440746420f648140044495181e5500001c040e2800c21110900b4807c00003501401605540c1a150160f01c2d01140d480e03580c82000c520900c940c02004100000c0f90150010302503a0745001015908200140e40700b0045 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 984694874 1250 984693624 984693673
    0xa050903150901090209011203020606041104080102040e01060e102a12080a05150f0607060608070905040b061815010915050c01050601030b130c020102090616030e0f0a0314 76
    0x540e5603501100151b180c1309048038010407402002c0240524261002034482078020310081c00340d43c42d403500680b05a42e5000300c400900f8850001c5444940f20489000500000c0c880e107800509000141c098a141c2000600c81c081d440c0e880742104203082030b001089c0313003000c3c80c081d040042220650902154228140400300304841e0b41c1d400700303494000a81e40846002a0450b406a950403600c82c405840320a541702404030103c40680c2c581c510fa00c0d04202510b002e8204a5143c05614000101903a003070b085207000350b04c2403541c0e803000e544a009210b0700306094002c00e40041041c40110712040007100c074004182d001890710f40501511781c00d0880c4003401580344140024400240d5001078072003841001e81000c030034a414800c0031050070025409001116600104070f0303441000c903501a0007503049507225000500026142c11001307200c1c0f150050341001c00da000c20410480303481c061038505070340d0621000080c0440c000d02e0458940c83c90711043c2640182c114881c14451104519096041008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 984696124 1250 984694874 984694891
    0xc0915150e04020f0a0c05010c050a021213090c09032a0303030209030109140f0c151e040f060e01120b1f03090f06060f150f0807121109030d050c030a05090315 70
    0x100410500e0803908407042d2049d608200081030102052040c0e000c80c1c1c0805c5920341e002865120183c8070751801103005568005103400f481e0103418801541c021001204503402032102d800d080c7c480800704660300c03403501c10042d9030090003482840000c4c0254040d19600c003003c3d00000d0b103052950380c0e005102c3c0148020310001d50060600c05076903035041100440028081d9298606d6a0460303c001c2614040c40292400403a1220500c400440c60f28007a81c0003060505102c0505954507440940744808440c441800103230500b4000880e00102d00410303d4226006c2c1503c0c031140c01d10703010006400c580003440010191102031000201c1c550b8400007440c6401074900199251403c1c0c1c0700183c20700154014244005100c02a059054202c002d2004451060900a0150303032a5507080b00d9512060b04880640780c0743c01c060024842c00b6102506414000f50101c401100e01490700f541c0b9400391080c0e00129038410004c01c04080c0c454006032500000240c11540003d07c0d01d00c04440b104004c07101401e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 984697374 1250 984696124 984696137
    0x100e070e09071d0d050d0305220f120806030616050903101a090403320a0804060c0309052a0a030803040b060904020d120203090604030c0915150e04020f0a 68
    0x220600c1420070b48800185080b04e2244c8241c0e01c558415490f07010306001407040c10794070b2000800c000103030400941c84031004078110340c01488901e05a03a46840c000d0382681c1840010b4420340707550b8040c80515000b842e0040c02800e0556410110701d415140a104170001c01009201c600c180e510704000c4489141603101d00824000504040e251403e100c4003e102d02c1020b4a609100100ea0011959502101c0582491710f801c071000c2d80207076900131041d00c03400307904000184048003664020b0350309005500c11a41032008441340c1e18200d0654040c3c841c09005900200130301071041804004140000c2615445a040f0241c80c0300000c07000342c06a071058400e107034000304000801607110190381d440034085072190400d041075004214a80d1010400070b0240c1e4110308880c00140c002c00544110840c02840303d960f85490745840c4035000c0d4948a0141c01c1c41c10482d180d003002030826500d1080c1d80300c407130241e2081801d10b513040b6a10000403880700d230403a90802c1900d05049140c030090040c0030301600c841 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 984698624 1250 984697374 984697397
    0xe0f010324080f1207030c1704080c09090c060d20030112030e0103111b0a05061303031407050307080c0f040e06100e0603011701150807030b0f100e070e0907 69
    0x40d082180c06070300d40b001c64000c0c00380550b6080f8844c050700e455942610340514405001d15222800400000c00951900707804100010705407030000f0940180e01041c0d640ba02541c440c0d59500c3d07941e82c0c140304400c1d0700c10020711a41903a610141e100c415048060b040400e4100070100201f0f8035035000380c21000001b9101e2913884103058010b08a003012007000c0c0307410421420b440c503800c8001c0c02110003002c4402c42c2410788000d4540f08209031460207805c202691494104003c00450601c0411000c40c0400c2c204821000c0c0055241c040c41d228480b41e4903524999501c00b1421140c200c8014510116080103211420315004024041c03c080d080b0820002800e080500c100300c2050561060881080059003481405440301e005590440303031802c8407040d000e103514a50300d0240ca0320034102400c00041030070000e400d840000d41c00c8210381c080c8480481944444603413002800080f103542d040000c0040c0104002d65525048551013000b81c500350b4107a2241c3c3e00082c0d8101401c3d900c6030001440003080c07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 984699874 1250 984698624 984698639
    0x31506020c01230a030e0a1b0f12120305062817030304050a150603060f0b0a0b130e0606040306090b01060207062102030c040503030c010f1505010e0f010324 69
    0x82c1542c0300c004020200c00e291031003c2025503446520301103c105900c501000e00c004d00b00300091100c1542c014100c0013070802d90002144005010b1003804002c140e1a80300260540c0700d8800c1404168219400b920b28084240094029040281505800c005400f91001d901001d088084030704000640d038a0030002c0c50314010343c503810ba0410361503076150410420300001603000101c00d003017603a00041480d1340340c401503d8036005000603400a802103041c401540d00030031142e8810300814030210b4003000030702c1c4ca1714058003c5004048048041c044040340910090049612141d4040c100510702e515182d2203030754103003c1da5240b4204840c205034150042c003000e501400120060b1449282c01c400400804842c01e40e041c0c0170401002415a002000c035010741c0881c81294040c1001604a81c0d451b0309400349a402030848e0034500391a00c4c9041c1d5045a04011102c4001c03c5a0050703440e0614481c10008121100c0300100549042c99a0f448002c0b007001d4000e600844096200c2c0c00f0740010f80c0c6001e00c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 984701124 1250 984699874 984699887
    0x3030503060d172b1e0906110a111605130504020a0909050c120613080d0b1002060a0b0108060d02040c0201091e151b0f030b1c11090601020607030903031506020c01 72
    0x20500080d0304189404c4045100c05c403541081030142d0b40c3c0460624202e082c843c00a004d0044812200c24001a010a0080c0c028080c00030f00c10183c0102d45500301040c90450442c0094080c1650100c0c03031075000200c0d02030b19001290070a0008011000320703596044e48000325000390710102d5007504019107001341480d040c01401e2a01107040068160f41c0f51110f600d080c60855190010b0880601107072009841c085503124000100014010106101e01208040d507150b00443d02e00300c045d4107020041e81254400d0105c280030310300140100c1d01e4180c0681c2040050490381003840d045640c0c8003008800301d80c1c0901142c0740d005440307451740100702c142c0c10245004116188140031081c01e01003ea8880710100420b070040640c00c5c0b515880505140608501404801c00c00d00d5014580e684c00614044c8240c00ba40740f050311400c0031144100e00c82041c80300d41142103c0642c0560060307400500040e000e500250b4416200c0e160000e8442c004070200c1c0d49100d1590041801039000e06003a0466581000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 984702374 1250 984701124 984701197
    0xf0a080d020c01020d050a05070801030b130c030507081c050702012c04050c1b030304022b082223090c0c030c0c0103140115120e06092503030503060d17 67
    0x600062b4540c1036480703d4504000141400e8801e024282d41501840b100213038003405142d006051b191410341d105101984d4407241d400c405543d0003100012103205002d03004445c002681a114507910141540310300b00c0700060b1400c1280c04202c4e841d500102c940e1035200c6d0911410241046586480d040300d0a00201d01800e20030205d00ea2040003400b026941e034030320040019458403200741c86000780042120485500145c000c06018000c200141c010703c660341401100646100d41603200c980e80e4580d44140e1020300520300800f41c0010500b0190304201450a034800d102d031401900e000c1007021100e02c2d6600440c030569550300310106140c5c056926002c1c07083d440a4008041c1c000703506104820203880007907080c1d50b060102e015003024044203079412814108a915050713401c980b8050074802c2d20380045283c40340300300c40e149003010f0204000e44812004e4941580d41c40e4215955001400100e1341408420b4600d10405002d142c045802c68004080000350746c980305000e00000c0c0840e44281c0100d0b03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 984703624 1250 984702374 984702377
    0x122414012310050c030f030108060c030103020d060b01350109051e0618010e040201080c0301210206070b190515060901120e070602030c07080f0a080d020c01020d050a0507 75
    0x4246044007408410a503004103a07003215200c1800040c100d06071041c2c40b89450300e0185020202e200c0c2c0c0c10181d4940918100c500150a5802c2556a084040e03410b20003401700079882801034421401062146d4890508484181020b00701d030401c014080030304242d05022070401e44c102e00042d500ba885071000490060005030030611242c10114003c000a061134420720303c1719a240c07030004155a540c200a0034000d005041c0308a49540c4445610400c10002c0702c09902090104011402e1114010100d90480f00342d00e220782c01028000500b8808003034059404d0b42d0103042407080d070000c2381d06607400d00d0003101c0002e203507801c56510f0403022065590040100100050501d495145030300d4050464103018801d02e450002c030051142414000e0158503c0701095102d152000f01c1d086400100070411080610115012a56a01255a40c1c0c096548804034541c201003000c40005a44602506038410940e02c09800e0806a0901c0c07401ca80028001c1ea4406840701c0600009003030b10300c02c1e5604000c96 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 984704874 1250 984703624 984703649
    0x7080a0614060f010c0c09020d14060d0b070c050f030a0302092b0b0a090b1501111603030e060c06070f140c07060e030307060216020a0e1012241401 65
    0x6800036080c11110f440c124148484111010304010f03a000401001c0c1c8103010003192100c3e48a81240700904142c01103403840c00040340811210710f0065080940d00d6403040300d040c1140c0d0758100c12036101003294003c9a481c41064003da07441c0209101500c1c01a034150740040e140c0c5900c104115100d110b06c540e183c507800b0b0b601c42040001c40302074242c0043c141c01c4a9000401e032960144040101207070072019010030448400e00c40503c0d0400094103103074609989194002c2d008400064441c00308544422245c01c0c40c40041001a024480c030103004500200796504003085c02d84034604080d4100d41c58000150144642d8000680106594001442c1080d205090404003e04569211180d01480040c880401c01c00c034520303034081080744c0005a0020056407203542420200075031600080f0120301c10b03204d40001140d540e0742d01e2078062084110800b4019183d02c0c1585104520103070002c10350740b05082c004c000084144111404559a0b00c200c03000680c3e688400c640c00d44a0303410b803ca41000d241 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 984706124 1250 984704874 984704881
    0x6020c0303060123030705031909150c18031205091305090613082205040c0203090a050405040c031101200c13020a020c040e0f060f100f030209130c0807080a0614 71
    0x50413090781c0d48000b81e030400d90354a0b10340b0f400044556002e81347d000390240c1000601070070400e90700040b081c6245520000e028964145d07806507000c81d2814007000090418903010008110948070300d980903000c90800034a844100808501c1440b08030f42d142c40c2c5070b91240306102801508200d046d40c041290181507801402a1355068124401d02a01c80c20056000313805d402c90b0007004410350010b090041c0300304003035403070240003035126000300f40207038420303c9410030000d404e0920b40100b03403003541c2c881d00044a07207041d80d4035100720650707800c4841c0c10480700c2154648031011012502290034099001020b5030882c0b5020000020183c0801c205141d00500c0880842c2e9000103892040b0502150045050007982401c98517011001d20100d8051050300107100c018000000c2e20ba01402d00c51401c40031194071000544582261440001d41010344c56002800e000071001f051442c2c98402e0f00309041042d5591090340c909585e03070b0030481440e04419224000c010840c0f0465008401d80b00e80c0b02410b1a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 984707374 1250 984706124 984706187
    0x12040c1a0906040509040c2319030f02060318010504060f0b191a0f0d0617030a0206072a050c040c02150c2a0a020a060201090c0b1606020c03030601 65
    0x41380b19450180c2c0200d00810100b000c00b9454802928000c20005501d020a101c00c003444440014018000c1c1001e07810742c1c2c010805c9400c90310a43c1d4205010380900c0c0c041c0e50a000159100400303d00d4459070604190314000c100307004e0503028a02914011810004082440c0c2c03c0300c000c500418410042d10310304099072040c480d8043c00b142c000039503170070341490f20502c001158810080b0440300580300051003a020246940310b101940c22490b400320035110001d8205030780e40f20b40200c002c0580c1c84640000c0b035092191070060400c2281e40c440c4800c040f400c1c1c070a086c464a015104480c3c039001800c1840550415102c0c3c061005007603c01030400020346602c01d400c1d0500a0881e06d00f20304001151108603500c20580804503244143c1003100001c50740700d490b111220749408038418200440c000642d075105018407103145401200040c40c4030314140c048022540916007421119030548030340c9020541c85d1014010011050300070310b54034605400010003148090140c06141101100c0b02100310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 984708624 1250 984707374 984707377
    0xe0f04030e01120203010806040c080303091b0d0618150c0504030609030201091205131a030a0b01021204090204080f030a020312060109170a12031811040212040c1a0906 74
    0x160036041070800c6900c003100480b0221007206142450a00000000495040c0000e44905c680d00034541076400c1ea4030b9001184c1c40344400d0754032481075840750140c83e0354055415080741c1c0d160300041144000790440d40c3c440c42542c0c4c102c003040d5802c450240b41c03042800303004406081c1d44404010200014a684500640640581d01010b412699038038142810503000354400340115400040000050340d1815000308143e000c4000c803007400c4c2c1030080000d4800400480e04001c0e200c241c800c1801c5980e07c08860b4010700030448014110720618034140c401d22400f02c0104007510103030802581d01c60502a0301c601d080c3d041850b400c40d642c010004610343c580c0c0403003540d01c142407080610856459940040350b800c21240c204228005203001d007005c02203000900701908901c15100c00b0036822440c1e030140c00f01e4107101043c0c1a1452440070000c0041e44a02140703c460900030001410190b400c0c10a403c0c1803c1150201c6030039400740001e001c5941c280100c00f1410301d854955034a041d103c4001300300c05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 984709874 1250 984708624 984708631
    0x41a06060a12110c0f06010618060c0b09150901020403212a0506071e0305011401050a020118060b0a08010213030b15031f0e061e0912070506010504060e0f 68
    0x141a96044020f02e5071100c9411504148155801c640c00926080001501d6900c00c1c842c080102d11030b80c1c409440c03804400c4040b0304031090b0b903d40c0b031400720160b1500107500e040101800700074041d45442409540b0480c8a19000d29480400143c03614254905449200617122005410311680440c6110083e400030341c0321010200c0480042ca64000b120b1a00652058298010440d01440c0100004070b03a0050b255410380315042e802060755100040154111003003030007410100c14400316625120750298004140d040341e43c1c030000482000349003031906450350380c0004850481d00c2d00f0007407159182c031043c07a80141070800d000b145400d04030054051984c07034601c002003940c580000014180f090412210b228003a018040c0ca070380031100251501e0340705a0a500420340381c5800141d00c003840000503528854007030390810324854002d4004c00500c000000382421003e2041b010300502604110018260043c0706000030403503941003000f008242c440c40d8014042e01014001042003030f4034180c040350340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 984711124 1250 984709874 984709907
    0x4050c0f010507050105010e04030e0d05151e0c03010302010315080a02130b09040f05060a0902010c06180c06080403022802011116380a0323041a06060a 67
    0x8035000640016602030080e4071014090754648400000c0004003030861511032446551440c4002c1a008108080d503188840060940e500202c4c1007007180005208194010a0300030840c100c14455004103c0601c4044440030300051002c4010411560180a45c07501c1c503c5042e07080300381c1c1e0700341141c1c1c0c1e0b43c907411b042010b8485c00c0d100349000542071480d030208002c050041d0036a480343c545400c00f440446a24902140d05100b2580024503010aa100b00341d10580d05139501601a5090344a00f03018100c40420740c2035003c00c6450303d0002030f0901510034010f00e11a1140142442c2604019040c0461010034560441c0f4140000c074840501f010018202942400c144001a10f4082c8061405591b0324480d50b680a121201041c0c102040c000c1032a50b220b20803610f1191f08000c82c480b03880c02c2e050720403a05d00c25814420000c6040c0a40c2001c031369401e413206a10340f0354140b082088410401078409803030f031201040c3c196041c034000e0300302e040c0d0200040d1281407400000080060620162540c2643e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 984712230 1106 984711124 984711139
    0xd060e04210e0d02122a01090e011707051c0c0f050d121101020a03020903150609071206170705131112040203030702310504050c 57
    0x58140c0e29180c03201070351030074040692803010049a000344417007001034000c0000c1114803080240c0c2d0002d8034011401c0b88105182860b003580007410010041d606109045e4103501803811030b00c0100e284692907552a02003420241181c010a0384950102440c0030381070005041244524011104407030043ea0380d00d002c08081629120705604140400452004111036440044200c216820f0102d9116030741c4030028226030280d074106000c83d901081c109a182810850411241e20400c00510300342071a20005074201b40044c000010000700001c400304120303190700000c1c02842504111004100e03d074850300d44443c114040d0308c0c0224407501031420400d100340a03404604606030511445c24060140d03401d260f81c0020420398051004100540058641100318903158000049040300394807d0b982004069a03401e1252a10070300300814000498000300780c2c4400d051044541c0d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 984532374 984712230 := by
  have h0 := BRFrame.cov_init 984532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 984532374 ≤ n) (h2 : n < 984712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
