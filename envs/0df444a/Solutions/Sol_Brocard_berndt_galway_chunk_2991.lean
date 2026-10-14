-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2991
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:20:58.564615+00:00
-- url     : https://prove2.me/submissions/fcf6973f-3899-4caf-8bd8-66ecbe811fc7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 537769784 ≤ n < 537949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 537771034 1250 537769784 537769811
    0x1020d0c0f0c0e0403030e010903050415180b04051212040605030712020403080d18030f0f05130906081b010207050909010902180a0c030612080f0c0f01060611060712 73
    0xc021040d8403000300860943c0782c810f030a40d40c2900311400c400182c100060000e80c4441801480b07500c6500d520b4060070607007001c0030f0440e2845142580300030880e00510041c08582c0d0805064024941810f07101e90f11410a8244500c9500c560054100c982c040072060030101a80c0088404844c081d00e401922600d80380803c4540783d042102070080c10b400032402000f403003045c41c02000c4070b00780081c013088004645118034844491580d00580071419140c404a00c00b8069440d859141100d450304504c1c19036500c0b94202400503035001895100d079501002e21811508115402443c408104203041c0702400000007503480d0785500802c1d000c8d188290128a040209401c00089540e00403c101c1c081304440d09080000c0c8411941510400c0c01d11802c40149802032007140c05550746a10710503481056038846810a521481c91030303030070600c10003c140c800300341072140b03825852139040046256032900c28010040d000358005400c40f5004101800145a00070f100c2d1051141d0000003c100d01048140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 537772284 1250 537771034 537771053
    0x90612090304270c0c051005060f090f010501271e0902030708060a140f040c1b1b150c060b04110414100f1413030f0f0b1501020d0c 58
    0x150401c2e80e050701c0006104202c02400b4101c604809404101102d90844c08030703110125100054915041500081404a0542c000c298002e6000d040c0044000350320001c900da09070200c0300c61180d4003c41005000ca5030b80504071100380b500e400301c0300c84800003c0304425001e0040d0310500c104901400814148550f213094004002c009001e011910307440d1418000e0702c5c8160031200c49104510320341011a034020082510842072a01403c0188010f0707152090100800494240105120503900402c10160b03110068408051040142800ba5886100c69407110107039500440a80809201400b0055900641c640212134100c2c9021404c0302c0403501190051080c00c0d0000c01e0413034002000f154080801e920100c1089050b19440d16a03184c05104450348103030080c4040c0014000d810113140105503402800c80348404000054805503265100ca01095150b40100d44e047c0701e50007200140144007d11642c800d405800030101031401c1b1740007c2d02c507220100e00320240912804010180092100c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 537773534 1250 537772284 537772289
    0xd020402030109051510020d03051005030601080d080601030203011a0901110f0115050a030210120b130c020c0103050c191707090512010603081c1e0f0b06090612090304 74
    0x9000319500e50316051110003401c012150030240f540d015808080030f0400100d40840c4200a07406442d4850455070110040c003805814004014400c06011409a5092000600078500e100c020b0000307181da2200070b0b04030b0000a000130b050510500040100d04202c460305144020403031169540c4090181c01603c030560030000d04811032240c10501440030b1015400342c0032020000c0002c00845594104001030856140802900b00410210400105002d0100d4001e600c500c80804910300c2c400501241300c44110302039400c001e070f0700c808503002c0003a0140042c0d61448820b180900c8149044100c0c224184583e100c01c0503450400e0032050a01403060300100b408580702c200900d01824040c40007001d056035801481d11414908400300034230081407042c8002c49a1042c0e8150034540c10944011b080c002c3c902c0020302d129101d5180034008d10603214042c81201050400203260201c8000f1001295420820203000d80010458141b0642c0c0e04820794081c20300760190b0b40c000707036542c1315030f141036000b01d9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 537774784 1250 537773534 537773539
    0x230f060d15050325050f0a030f05010203060108010b12070503071211030402030d1d130609051317070f1103010603151e020910081513021b0c09150d02 66
    0x14841111000350700605204a503000c03800c40f03401201030000c4649141c0f10314070700810b0f10015902003042d414070004403903407103c0041410b81c880c0d030f13640c803101944060143c0c112081d03507000081020b90341e0844a81405008400050341c2000f03214a280c0e100c1802c007800b0f040511402000040510340300d11044055a50501402c4c0f0119940449000e816001139400700d1103401401c1d520b45140d4030440761090000251590012112009000d100d01c6003803031940b0915042d100c08011600900d85c0c018180070b0b400b5801401c05007040c5040c188504251038a070340d45c00070702c108000700100b086000c031b008405821015a400b4802c1e514000790040035180d00061581820301c081802540d81d5600c0750124010030700c43c01c02c1042841c0380310022480b400e80c0e51503114010300c2c603104056100d4422240d01141d010301c1d210004203000002500b881d62040b0003013585800040c8198110146050040015020401440c1d004051b2001851104004100500304c1d02d8000c0390300d0881d910000400f4005401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 537776034 1250 537774784 537774791
    0xc04110405060a0210390903081210090203060a05010311070506041b05010306050a031410110a0e0a030201090e04060b190e060306040c14030304260601230f060d 71
    0xa1180c082c5d110440703104030032407051500f54684280d40b01514030f14080514209039250074410700f61030b082410784000303051003006041e01c004400140e06000070511a107074480c54034480e28110701107443d00d80554000070100c1c0e006109010360b0f0340300c0715400401ea81d024200030480751964455040940115800130b0312a01c100300500c0282701c080e40390110010411241000402d407584015400d542040c410b454201102c2541000410450b141c0b540022980f4010b4a0944492060010070b90700c106109801a05001501d2100c19810841c0003044034010f80305521480c0c82e60b000038050a0180c801c9044900706400020201705a942c0002600328006200c1c00a048040311a41749220307050080500c3d945420b004035400b4a40015018802caa102d03004550342c50038030285130001c130354402e40c1980500c814400860851070510040900d5010f141078018128401d089503403500e80180e01c5004031074101c0c60b4444140c00c4144142005503410340ea41100a9034080124045200c6c4600082d0214507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 537777284 1250 537776034 537776047
    0x5010b030706201612030e030706050c0d020105092e020f03040c060203120c09271b0307050906090d06020c010501060201050a0c080a1503050312160e030c0411040506 73
    0x1042903000e114a40458480041e690803480100d9548001c1c094041e204008010204001e6007050b8400c0d48031740c4603250941d61f0211a1010902c0d100b0035810140c00f00d5004916844069001c02c811074a031843c0d88000d0040c1c1c14a01201a03e40c0b40c2008904888040d082c0d00e010000f54410f0348581110f9a84000c5540d4bd44802046d500d942041c0da040364141c43c06440010414800010f440700b6104010946440d80c0316020000303810303803090683c01e404c10180c41045000c50554054103c03034290501c100725540c81c002d47c00c43c411061480600403d001e060091003130050380b0509451804209031052942c400321100001c1404c03400380760060065000040e6202c000c4410341200d41213035403030f4000b40080e458031101001540e004901c0b203030010340c0c03550004ac80421b06d034016800013001c0349400c4a00c543c580e03c2d100c5c2181d2000b1584d1503541240418084811204482c0e868071405910786000b00080840000343c96503241200315100d01d07212003541c11400070710380444004206c01041356540700f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 537778534 1250 537777284 537777287
    0x60312030501081903020327041406040b030115061404052e020c01050913020f0a0906020d0927060f080a11060721170f06100207061b05010b030706 65
    0x100074002c074452400b48032a0030203413901e40b00c3d42110482c1c0c51b40181d818414031a03252484084000b042d03074148032440140c0041ea4a461082101950b00c18a088110303141080600090712071040000d40207030700d010000c0060902020791942510424601a0804803124100350044d0165030070140d80b1903107a114856012040300d03200884040b02c0c54124070151034001040c0d03222003080c04018007003642002100151719000301d06012501c6001070060800010110301d41c41508212108408a08051014007110390100141581203d05150034032016040154400b5184d1505808511030210803101c08041e0b0800c0d0880005442100e0b4810180c555454039241e07200449a0301b50b07030340e0300c0d101c83c628043e00704881100d02c4c080c0c1081442c80715200ca034900403081b6100c1a03a030700070410160795101500034040b5040b80510501030003480c071070130010100318100e01200440c2c01958080307581004025001542c12001c01446190800006058284140500288003401d6494041c0400200e044e5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 537779784 1250 537778534 537778541
    0xc030d12150e0109020c03070609030c02120f0a060e1f0c09120210050a14071208130c0618170d020115061d01030b040f05010302040b042d06031203 65
    0x103040d4402402005421801c280c414105805400d005020b00780060020095030340041049035044000c403454402c072916210103c0b80b11501c110005409440c10b0000d41c40c0c000031203207080d030451015000f2020b40103444c0d5562850100001c18054a07a640c03031800c000188511110038864070503500c0802214919040280702450340e10000c540040000308000c103030700080701504c59001d014661401c02c08102912150083c4101a04001110700c0311400d070540c180152070040c0c0328941403280d134400d1240c040c04842006040003503100700c1c3c40308a0003042c0d04200303460844200b41030014110001840d00214000a50844c458010640158914003040094504034040296001300201010403240c14034143c61031040740f001940c011400502515001131248200c0d0f07050400003080d2940390042070640703071140c1072443da89a5170310042095013840e0140354115179040b0303001c01101c01545840d0010210200c0d403400501c58201c80d41c1082c3d180d41c0d0100c0c000d99000046140340281041c1c00401070f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 537781034 1250 537779784 537779807
    0x5060406080d17010f0506031915150e04291302130f0501141209010f092105040b181903050d09050d030503011404090204020a020a060b060906090904050c030d 70
    0xb501e10030300001e03d03174000c030820006941c0b0003440b80d817442e01c981e00c801c55104041c0d070164059607520645001d142505440080c01003900f8078802d007080d54188d401804800ca49c05c280c03070007a81004161442d0403081d02440220440c443c02e0020840009804100c89041d41d2402d6000b840c0f000481001044400205100302c5980000e402d00b881c0d02d8400440303840071481110300600388244100d400304480000341c2540500b060000190088204c82d454054601c0c1c0d4805480b2000009070070544411036550034278628002d410803900d4140b80c030400c20b400d4071585281d608203180c0c50307220340d02c96910400b064000c400d0244441d980d1b02d8683c100140c80d91011703154200443c03502c0000149074104580e40c00900754254a85a0541c0e103424944003982ca4004e01180e40580d944042d01c006945620240280380e406900615812140d860900c0c101c0d44004d610500c45c003010b1000c200c080c0d86200172038030140b4091341c00001a480e1071074224506030380e20700542e51601600c01d0101c08181d01c00d90b00c691 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 537782284 1250 537781034 537781067
    0x14010e010c260d1104060807050304061e1a030d1b030215011409090a050601030f0203030d050403030b030c03010911040c140703080f13050c01050c0a1505010305010c081003030305060406080d 84
    0xf04c0010305040c40840d20680c03140d00007040280000540a902030405075600600540740072824420500460312861140760000c5090b9945a000d903258452418001d003540400360014070384490513080260841d030114411412a203604010001058400d00244000c402c50380213003c4696103c2c99038107400301214400303034091400e0400103007034200300003a08140c264101c030191080d0307425a181e207140b03001003000c1a43c0500c410030020180001c140700ba688034901a960000d614101c0c84105401d001000d035000c0d119a04003400c403000315103202c2c0c0c50341d24002c08840000f505103210714150740040c3c040410180496010800030189500064460f1240180043e640410354800c0444d19140c502c2c03281c050b00603402240799048550084004150040303a080445040f864503643d9801c0c48180141200c030520340360001042040700900032040003403d01d050070011485d01812100d60039900c3d200190406450748049180c40d12035138040000ba02c00e01c400d8411041c0c4201028052042d950b20554 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 537783534 1250 537782284 537782291
    0x6010b0a0e06180405060f03030705060f0709030c090e0c0310020d050c03010b120903190e091b0307030c031509050f06030606030a0204050a0b040501030312050114010e010c260d 78
    0x70140d10307040c1c0844160000444401c0c860540e010103000c000c00c0d004000c82d4200d4041012000241d83c20400351170380300e1062009100b64584a40700c201140400381182c0c061060429081c00003504641c080b0050f600003408c0081d001e83c1300b16480e8035110740b1442c019018000d1443c0e07036070000b00607002840155420b000900040d180e801503c07a5031f100901c10548121004c0c45840d58040e4401000e6030440f07403100850b0305140e40e5440858866181003201c102103001c91800002c00e04012241540c00306515494211440103030340c0411041c03000510300c10800d940c4902424006000341e2050700450404031403582c0304c5e62a94a0500200003e0b01c040440b1410600050268640042c0b414805c0c1400742c054000303032000383c1c24880680b0000e0a00e6503c40c1c3c44502c0251540c5541c03207118000d50099469811082111a510b01100c2040c0c001801206044102c203116980000081c101c004083c6448445002a404e002d1601221a80c101d4804141d002d0f4002c0c59070700440c05000710880d03804080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 537784784 1250 537783534 537783557
    0x6070b010e0c040b0f0327010204051e0d0b1305010203310201020304090902060c030a08180307030e0121060609050102010e061603181502210402150a050c06010b0a 72
    0x420310b40c0624468083e080000b00503205004400b20040c50b08034100749006034100040101c48000002d5140c0725200e50f0b0760220f0100705615143c40c1021122404001103100c5449010215010006085014210b03a00d050041451641c0382e2a40c50442c40d0880001c6403a1f040c00550510704000070120740c908498946022200042d05640c84001c4c198160021860503107000030143c081c00395006c003aa0f018070203005003102320406000900700898942d43e016020f240c070600501e4950030030b0108040a174418044800000c1e08254604010402400c2c45071150f0002d5030001800305820f031012140b141000070000700c41d5003150041040e54001d030000d0048629032640c2964130380c81180c410f0b416003104180a01250300075405082110303007211003034030140764a895501101900d580c0c109001d90340003641070120801070318001c112a117942003810f45800e084d00000c035007000d00584913120000000d00d010120f030080c000c4403519150001610800d41e03641e441000c070b50304150108008151101780d031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 537786034 1250 537784784 537784801
    0x71b0302061005030303070807030e010f060e07080c1603081b070f02030f0f1e030c120406031109030606010809160f1a040807060e03030421020a0614070b130206070b010e 75
    0x40c0c87c803e8110381c1c2c07541504e50b0b07440401c6014000c814804145550f8403689004c011440d40100c1c4040d00341c0520307220490901c413074010048000109142001c1c8002c0c0a010710795441d4002c00c0c40c038070341c06203030041c0030b911362006509450300380c8035400e1a00d490001d100340401801c2e851300d00301c00b4000c40c1a11400d45103495860b0306d8020003000585182c000714440d03030140d4409502c22301011801c10859082c2000024490700d004202d1104e040c40303031700100d801c00810782d01d401424001c0c0d00341a10103040c1f00e05200070a64a400203808641445100390004140305002c00078a110410f072104018910f81d80d68401141042090080c010b1081800750000050160282142d04445081c402401d003d4034115048840d800203414066050004010001d40301c80451890000101d501010075080503481c4108020061194820818808034624a07045000b90300305031010960011a65002c55582803d80080c2c42045a0001d601c5400864800c042c01340c80303402141a94808080d5589540b02c5020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 537787284 1250 537786034 537786037
    0x20105041205150f060a0302190902040f08010b0105040b03041101140f040618031e17030c0c0c031c031802090103050d090e04080a050a02010e01110d060605130905071b03020610050303 81
    0x150646c003c41989810401400c018588198080d121200c4c0c01c1e80640b01c12030700342664855403120150f041204c5045c8650b02080c800d180194009084c001c0c940361420f040d07100c1c42d000017040503060418100038040517034000d021741c1060310300c3ea2014070351715002c1c090441159017050003403d001910303e01720340708034100c101400c1c02034a401c8000c042e50b80c40340041201740248000070440781503440b0860916480c039084059800ba24065420701c0d21030500002c0549482103140f40d05200c0c0c2c3c421141c070a465400000e00c02c412801c503180201d040c04080c0702414088994030070003074024404000010604c5400f00340c0000c0300f452036981621441e61040b07150840d040645d0050443c100c20032038124031500500c020514a10f5900011540d0ba8118241e00d003107a0200c1100701d2416000a212806146c251040d4005062075041c0241000003804014241c00700a000e0840e019a482e008030307041b14011604a00c031070191060899814445250094403000103961802007400341c0340f4041031907d030120 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 537788534 1250 537787284 537787291
    0x10e07030b091504170a020f0a06060e1e0c0f040506041e120506060603060d05060f070f0315120c15030e1603020f01120e070f08060c030c16020105041205150f 70
    0x405c0e44800310440350104c1c5160380542110400e600c10f03802c201100032811702128200c14060240041d010785006218145003000130024028025120400220340742d000e04000e411810108515403a8401e0242c843c00c640300d10340000380d010101150000c0c144040300c0c0031140015070020384203206544c4003144a45c001a0718001009070304100d002540302d0921801030b5900420060816544508030349880d402c0000a0b10030ad00720036100001c2080140c1c00c060500001140c52504000802c95081041240c1c00a4014003107108445021003062004029440018000c0c002c4510130103103801c040070b00149030313482d0f0042c01750141c80c000040308410000c00c4070450750041c140f5141d004800004682e10607100d040c0c01900307540d4601500010008201d00c501500004610000542c10000303030500d40f240c000c044009c503040c104108554541140e05451000e032440080c140880b8003071005030340070702840d0099000d0841504602e42840b800042a0b005401d1000079402c081c0c94189000e500c4d00000c6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 537789784 1250 537788534 537788543
    0x204050112020d0f0e030a0f050a020a0f02030f07180b0901050f210304060e010315030507050d140d051b121b07050603130b07020a0c0e09010e07030b091504 69
    0x210300120310580c264005008410b0140d10000b10046002013220444860061100c00c43d80007103031880c4c00c01d80000c010400c07030300e8508000d0b04204d0502c0009545102e80315008111042d180481e50071504c04100e580703ea54024400c1d1134405864a805ca5151940c00707940c840d503140ee100c0f84042c04d0401c2000359060354400390951030ba40070400140052045000c03880c0c1340c01d072101281b10302c1c8800c00380040e00203032985558150076010bc2a0004040d00d103c180c14151007030803007404000080c030005001f81200e00070b80780c490840306203041288003004130602c2034516005400c101505154040001c180c0b158500900710380000b854005d080d0740b0801014495a142820010b80c0d0107103042c402c1e01d0b003400d40c43d0000c40309a2516100403400c0e6810a03258551881c864080c004200150820090382c00040e03840105000038840c0c132201e00000300d510562021005071404908074090070340114014142800c00c0ba1555552450030f006260022200308071305000b5242c1c50044200e89004c407034080c1d90031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 537791034 1250 537789784 537789797
    0x1303080f0403050f031504050a0f0f02040e011e09060b0319050f0403120e01020f0c191a15060318160623120115020d170f09070f09050105030d0302040501 68
    0x10413520807032503001414107125260720100d5421560345501805200b0151500c002c2a4030303042d00064030640385280d00052040380184000e00c004198030886504440c68000c1c0400c2e0800301c40750458080c011327900701d52851030402c01c000c2541c10100005500420003101000300c0c0450300418002121000d680d03021100c0049001f190200b8494050b01c898034400500001c0e4180d40b400480c1d0072a8089039400120402c04107001d014200180642d000b050540c0c41315800004840d910203150300d40704000ca00109c5590008160101c11281500d50002d03400742c6503940e01d040c0449041d40d010150310714007003644100004441031382c09051045046600725214070040792181d050300c103406e62800d0022100d002c0d0034000140c0c0450303e100000d0013080e450710070300311480d0103000090820000b02038a0090000000b5440340954122050a174060344505031603140362506041c0070305000d00c907804005003a240360b00c0440c5104065010314121102102143c210015011060382a4080d030711441d40882c60 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 537792284 1250 537791034 537791047
    0x201140a062313020d05010312020f03030408070c051002030c2b030e120310240c150608010507020d091a0403170d06090606020c04050415020f0c061303080f040305 72
    0x10071092090b2901e0700030a142c1c0c2909030014180100d070410b000380c0b40c2d86901c480040042c094110000702620003984080d000c075102c0d011007142c0d24403015100030202d04000410000b80640009403501424004203100124081e80300004d50301d41002c440f85e00c0c076019040c100c0c800103d038000b400d20f41d03032050407189200541011041c0c00402000d04883c031680500c0b003180c3c29200c480d800442c4201c1d0041541c1c45910300f00020702615200301c0d103000e01e24469480200c0c8040d40c021040569403684940070ba0042c44101c1e60f060041d04075940218440d40c240010710100700d8003c2901c200d460401e964502003030f9038541d000000b1420032260750210000400040c000b15410710f5070706101ca810008858030300b55104140030110740032035012569042e59030b0003d1026550500c00c8128101d01201c05108030308058449a00200040014002003903001881e002589818002e4903441c1c0e00032001e07129a490f14028004000c0b44410b012000a542c0c00e000540502c01c10428501032030305075491a0a00e00d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 537793534 1250 537792284 537792329
    0x16230714030c0405040b16080705040308250602340b061807022802010f030c20240c0306101715130c02030706050a020f07030201140a06 60
    0x1010300031803641602620040e80250386035409198043e40c41842c0b032202d189404104d41e040c0100320341485080255190522000070791040940c1d054031b4104110655500c25089560b129840e010f03141219482c00040ca02e050150a5024000700180300c0c040750103003021940a066801c402d080462003080d42c0d001c00e0004101c5200d51168808405056180e140b0300d150303111001603404441940c01648512048001e6980b80600687c2d01030343c82d058019920b43c50703030020b40408800d103014020540e440d0103010f00305120b00e1180b0b110307903403641038420303c40d840f141140d80b9040304025141d01418802c042c2004510384880c480d11076080221000d05640700c1008200213035503542602e004010240c5032007566004190040d5014196090f0006c132500048002d119000981c5010102c03032929080039114841e0700401241e81c4a580850009441d540d10030500d0f000b4051160a1741e802e8001003102d8081580544c0444d900480d10a0402c1d00d55450501144c241d0b041c60188690b403400b01c071000380900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 537794784 1250 537793534 537793559
    0x20102070b07060b060f030a0b0405060907030f110d0f0e0c4005041b0602070e090a050118050601050618060901020f060a0b120102031b030901020f162307 68
    0x2c521450b40821a400d20100141040c0c20660a070000f83c0400002d2042c07440361481240b0240c00152004e100501d04680040d2100d10003c107180306240d220a10600c1ca14069409081c1c80a01a2600c903124a48160100c008000c0d07040001c0c0e44501e800d0a030450484006444418090020b114196a100100581810490310010202400085034020505030042158003040350803400b40090340d85401c0c1080e02c2a1580f0b8400a001c541c1d51410604c005580402c0034011340baa080001050364403400a114a40300b02d8103800360880d4039020003400480700702580c1d804601d009100722413041e40c031181040f07101c0c031644150445090149000005d40c0c10454003820310b104050042c0c40340d91a00407800e904000048542210301961080840c07014a811000032454010710002107042d49009040210b9501b82450000100f03c03001c400904551401d404031406100d0b0741007155101d42440071042114046040c040300c1c4415a40041c8011031071040104104104800050541518003001c1314840b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 537796034 1250 537794784 537794797
    0x1151107052404050a030609060b011409061308030703051c1515020a0c0b09030709090206040504050405031c050106081e041e0506040f0b070908070e0709080d030902040f09020102070b 81
    0x6a00043c04005141c0d907401e05108019030140d080480c0743c03c2585004c10445509803100d03410b0000c40e000098001c0601c6055505024055804559444141c80003d2001c0e08030ba02070780302444005507010030103500002030082d4001ca04208010184a4a0140e068075020940c116a01c54070b02c0e01006114459104d19410400c0d500688401a500391200f4003024820303000140410030000d14050b07070f0704042044900800c124035040000026030790000c0d105100ea071003440c0c03169441c0c1c5e0204003485401d0040301ca641030440004500105050190400782809114050100310548d000803084070100c00300860000e103d4a01c220703155155500c010088080c2030b6a20003100c1d298198100103107040000602843c0100c4500ea03d50031181b03400b441c1000020300003020000180400c0151203c001070400c1a140d200d04412959503401d40c08946112290340b11102500c25a001c050600d50507911401d035090007900c3c14044161110312110940e0b089880090050788048010000700c0240801745c1078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 537797284 1250 537796034 537796099
    0x50d090c08060405010605030c010c02060405061b0319090e010501050a081b0a05040801060b0c070311010201270212011e020c010b0a030b01170607050403140a06050115110705 77
    0xc0c516200c000c0d05191500844084035681e5607220300b4410340c501080402c8a1150900c1c2c03a0150384400e6001c5000760050348140c40c00790340040703413903207200300701b0200c60045421082c2140e44540100042d0502c10700c0043c1e00b4004280b88950104140b207892030154160754040e110103203440040c0d18101d411190040c9040924041341c0ba0040d00024010f0050442c018255591030300c2d1410060790508444407984103003001d4070204281c1c1107106012508204403a0030980001004240500503400741580e82c5074042c1420203034014a05140000340560b0403540240c507445031030048010514200c401c101c2600401d107a2005070580c814039180c000b001d000348100000b02d0080c40c9080400c4141a141d0400c480c03d05800c00144900683e8020b00780400c0401c0004140038104001e0141c40f0380300e580400780299120503903001081c03a042000d4603046502190400996035034850182d0001401034048001035050034010307507100000104c22003503074002132000c40403d01800e00c0420f01c0031100020907 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 537798534 1250 537797284 537797303
    0x160809040e0f010c090e060a05150d0216030e0409030509210109050607081609031e050d020f12070c1710050702030403060e0f0d03050901110409090308070f050d09 72
    0x910080003804050703503902c8100000b04c2c0044c0c181c1d03006800224150082c1c0616070342c110070001d140e907800c07214100701c1d0403c1d21040d0144116132074180007413147d01c1202425600000741611490410940001454040e64850348082c6004041100b62039454401500041b418407550b011854810f0b040e208031001c0e2a4002e541e10301c1401c000e404d580c6410310a84094000030b0030031811a412028507680500c2c481505c3e240408014000b81c2200d0b1103000160020f4450144450b01d044c2c00c3d0301d51540b9a4116048441a04441c0d00003591b640f001d4011701494059880c0c0400403040c06810f4814296200c840340300940d0a044417203d1034003049182441764401e02c9005044040544900c40c00703151b4a038095966181541010020f0398014403603140950f10515403085905004600584100c0fa40d00c1c1c00704860f183da100e080d0160144148940084800107800100744074141c2c4148a6513102c0c0c0c5408000381c1d40d046040d505c1040c0407403c10045442000407a9a0303a03e02e6100700000e510801c5004d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 537799784 1250 537798534 537798551
    0x70f05030d120c0c2102010c09030b040803060a1e03030f03060518070513031103070501111908040f0608060a090c050a030e030706060e0609010b04060507030c110303070b0a0f0216080904 82
    0x422860211805c44c03003c5688800c00424019428005c20203010540c0c24403035545890750f5501071502d031006102500e078007400b002051960751240c0041000f800c00c0d021b81045900f408804884d0b002151000724003107258003c0c4680341c24002d004800466000404c8502032090550350410300103030090001d02000010042c98143c0800b0310300c3c100145000382910011a10307110305043c40e111035900063b06210400b0018010305200203620700c001c003600c090100d10840781d0324145d0318501850308124139000c503441010545540c00383c2503030312510089031000e083d555109a020229440506110006a010041c2101c0d01780071b0741000c40c1000010088030701d000000d803546401c4a513581c02c4a803040b07560f441440641d18058040d40e000d0103e0302c803818070305860440c0150140c45024002420320040700070750300074000040c110142161028060b80e6440e081850401c0031940b003242c0903c1c0840c40c1090b2910b021a0610a4507040c801031240d0402e6404030703407030391425074200c491081c1d441916500e04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 537801034 1250 537799784 537799793
    0xc02070b180f0604120b0a110a1b120e0103180f0f03090302090709050906010206160e03101a120606100302030a1b05030a0605030616140417070f05030d120c0c 70
    0x40001701190300396222141618035001c64450406845201c6580c03c2003440d5a0118450080b41c842503128204400034031010028441c07031036020740c2c01401074040030110741011074210b805103080403402d0740c0030441e207900741245014400a01c1c1c0301a2441c0c42c83c15003074001684a1221582c0e0380c3c0a030034200704e419680c0d40010094a411a080c40000d8a620070400150400ca001c1e6508440c090001d0000c0e8039008405014000d4113424180401010000d04005518180305110482c51200c0c000d0202424030142450a42d4006150724007400d030042d002e5015042c00f1a045000c0c1e80c00030030400c8200107542e4210301039000503084640507983c41c0b100e2a2005503d091055180505444603900c1c0e20317080c0900801c541c186d90081e4003070b400013010030074180038a5410805074000781c100708001d00901c0b0701a41d020300840d007020980031403446490458442c000f568804840d000b07141c50070101d40350010306803035101d05085800400c000720303c0741d000101150170068082d440e900d00070b040380900d03484 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 537802284 1250 537801034 537801037
    0x903030c090a09020c030711040902150d020c010501081c05071113020405031b130e031c140c0904050c04080d030914101409010b01050d0c021507120c02070b180f06 72
    0x102d00211703400051035504102148c0d000000c90b41c0c0c216070070020003d96401045030200000c0403040884030000301c11800a503e903058840f40c05485008104c1036031101134466440c0c268403454201200246e40340700d882031050f800c0310380c110340c44000e036051580d1010500c820020081d060740b5a6640a020100d2282c03010440c1860364070b269a44005c583c0501024003004016806c05010f0442c02c08002c080d55000c00070480d0b190080c640c6c203003404041d04c03413640001810040031201c1113412607004d0000d055841c0000d000d0406040740c04209544408000e0b42d6113206034894800300da000b54603072007040b03806a0701550708140034810168441414018290604000c01381804400d41d03122501d603180804821141c0c0d203e2080402002680100340018005000749005a10345a1b21030340e555001510901000d0200ca91210040d174088c1408800a4500000300102030301c00c13451310540c90078aa01c0021548106d0703000901d01450709444410401284100220454002402c0c003408800c0d6100c039030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 537803534 1250 537802284 537802297
    0x206121b18091807051e040c0503150303090d0222050a0c03060f1a0310090203151206010e06102a020a1202060d0b041d06060a08060903030c090a0902 66
    0x6001c0001c0100c20400c880b40c20054011105070044a004682c81640016144181c407000ca41d13540d50710244038a100707509010050815086411f100a42d61344580240245015440d0314104c03074900807144060643c0d0380144510f41d50301042c01260900941002200c0d101c010001c150030703000100500305a8019588283d480c00380403940e170181c81c03040e02d03454841c4001510901a403165141c1c54110729070840c4041c00e0707840e840c00a001010410501c1102401002840c02c00d00964a0b80f40410024402040d440303143c50003514030076007100d00304e0b002007040c07410380718000c2117031107241c541c0418002940b2160820b40140001e0440b03035951188124070140705090000f400d04400d400741e105202e0b20700119030015602c4010318000c00010380d0b41e08140d0f50070031000075000801e882010001005000e40c41c0b42031070401d4420801880386000440d02503c503243c19124800d03075680d546c0c40150b80d00011503007005035070401d02c08500415502c0e0010b11102e100100304600040d15000004101c0c1d0000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 537804784 1250 537803534 537803557
    0x141e04140f070f020a0503040512030c190606090b0a0308030901060f14010f05030907031b030602070615080a03140306010e060c030c4e1605070b070206121b 69
    0x1410002d4850b4800345260401e007080c4080c03d5941400e83d2819074a01503802824400c0c072000c10b0001da01c04080080e100f403a030340c14084504800081000c2c915540c088001036886c1030529501045030314a5000782140c150000d4042c3c01d040740b5540324880c80c0d0b0009000c032101c41d5207400c80041c203100c94403800406400c006071090500e0003040c001610f070203002c1c1c1e8144103000c1d0038800c00c5180e00e404607080c0e040301d0f0010080d08103014400c070038840c2c8a00e107410091003a84045101014480d0720f620840c040b0382070881030380340f4a44520581d42d40d090b050070010005038510761142c4181800070040d40e044481814110442804a00050026008608503444a038008202141800d1080100600c03112101068240f020a00c81607028070030340007100007019205441e198803846071401000103100048600c00394440c0940b000398541810480c6065070305220310781000ca008071980d01201c0d1074560086c54546044550403c4403124080189074034410710030510f103030702c80300c0114004003d40b6031031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 537806034 1250 537804784 537804811
    0x70b0309010c0206131e06020a0f09050402131202040b03030406020313090903080a0e0c090702030403170f070f0606030506101d04050733050301030309141e0414 71
    0x390802800c48004950480c1150301500c144007103a400307031103022002900200780114410b80540412040c1407075003002444244009083d0965550083d210b280e43d0707601381e8802113040d94a000708400c0c0c1c0111031145542150a43c01000141c0c40f02840048441c8040d00104000100380c0000e03045802651210000d6000040c0712401c01209000c6070002d0301c041030040044149a403002402040300800d03480300c072541c2c0c080610000034108007400b95454014001c20451600c844005c0d180e420030710040f1101050720040e1201041d10406442001503590b510b00c0c01c1c250251980009070304100e000b680c00360303038174100803000c2002449110300c91801c0c1c00141805500e000d84007240b4800c4401d612003e20b100500b1320000400105071481216592194203081035001548500f400303030060903165080300d140c010001c030140c010001d14100ca00030384410800701e0381c0328690030346440708650030381d440110998910450310821032000c940c4403002e00000f0300c0b0526140034420641d000e48074182c80f03104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 537807284 1250 537806034 537806041
    0x909020d051b011701060c0b07020109060615020f0712110d0c03080913050f0726012301050708041a07080310030209090a230f10050603011802010f0c0c0503070b03 72
    0x801c020f024100c100c04c05003030492503243c010700134440b05601000600c00150700d030101c0c612030310075001960721a802060400c0f0a9981d285000301d9158815005005805020080c24008001040c1001141c0d10451100d40282982c0d0701c042c2c1e00000300d00038640c407005504a20780411408800d40c005144100c4650345c1d02d001300030801241144000c0340000050408041168008412a4454001c01d441c2000501003401c201c903581100e845890f61242aa0044000125181c0e03131504e00f43d40080c1c80e00c861000d600340d207004640c4e5203d1288080c25121042000b000102000301c1c0300c005a00c0b14458050134913559950f00b004c20b9006072203403100c0c0c64441038103005610700030380302c0d42d00600c0c1c1200500440542e680c48001250b031490000c1505810805000201c070414844505034065540946400e44400294000141419183d6501a602c1c114820610b262002c1180c1c640d1601612449110b0f1a01001160706954120741101c0c480b59100d0006200d4a02f00b10020140c02d00f100030a4603480e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 537808534 1250 537807284 537807287
    0xd0603080c011e060803070213021b010b090708090a03051e07030f090b130b0c031b0d090b090105190c06020a03200327030c0a12081e010909020d051b01 67
    0x220f401c01091001c1d150020030462568000b0440701010b6041d14201503c04d11246458002e00444a8120545680400e40340300b50b03c041d40f21203960741c0c044902205640301c2040446002e0b1048503011800c1e400240b45001082c007540190000144050213900e41626410220341c5980201004402281c00600042c2850b030304640a280500030740e910403418a240e003949040362000a1250000c01040014075180c0041c00384100c0302c80c2d0040070064400c00d802c801d0955543da409525410002d0b050380c00116031609214100c6002c0c1c44160364080c10260040541024440b410304403070103000d0394a400c04001082c43c0064030444d2041c1c0c40c00100c240510030f1001c40c481100d0000e40000e0703001c104000000c0c4d0000f40c08101241640c0340e03500c100b0700c100c0765146103100701e040075025031060f41c1648007000101e070850040c061b041e03035618426407074141440d01d8a5031350401c8050f024400034010b000c600320350307071180d100540020075106101031562505030810041440d0340e42400710f0844002910f5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 537809784 1250 537808534 537808571
    0x40f0f0507350c12100203041a0901050103030c020f0f0909030a030606030917030408120f010f090e0717070504020c1507090303140a09090f050a0b030109050c060d0603080c01 77
    0x81a0b40341e5050510792500d0601c684448403890001d03c5807403042c0e00740240748020000c0070a910441c210840d501c0c181414017141105400c0c0300a0203d0003081c0010301d05007418054a0b048907810344070702e95101219400c000d101016503d005030402084002c110340b5903504000540581d50a0001d165600000d0b0001801c0c0d17542904103406250400640000043c07014000024064055154030b40380e8449240481c894880d019aa8055a2005040c018101c0740550001e0403511685070084e42c280c0d84040480c02d4034114103d4400e6900072035400c21032280004189040d070b09183c01a101000e80b20f03000078089030820042550144e00020b816903865110301101038000405090030140399185035402000500d811480103080c000101311907203514010811500a0100c03a4014044801c4c6e81e255840108070445401c000e650034003d1540041c02e040c4107511300c182d0410081c001c0042d541040c040258001c5646641096844400001080030100505000c141620010400f024103c80d5450b02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 537811034 1250 537809784 537809849
    0x6090d1a06010f080c18030f0d080a110304170408030c0f0606010503040f060c0e0a0306020d1419090f0c031406011e0e0601030635011103040f0f0507 66
    0x6200d403a1600202c03143e000424164440500c00c000e075582d00e02100c01b01d0b1014203100c0c015030544103522240d5541400072404a07a0100c540d0b45602c03581d1f0781c843c0b0200555030850071080c04807408101080204000022a5100c00d020501c82d5103010703a501c01481c074550003c141100b154001c001c038444441d200744141034200d1424070740a4254107254403110984c0001640060610b82d441400c1c502d0700c3d0003003140038040c0200074009807825543c0e04140c0040c0d817200c0c03482c246803840c0050f6180c8040d6100041402041c10b141c0d5100904c103c0c191000060024010075039030b02003020107003400141c49a403042c014511070060110f024821808841c90048182c1003501d4411520791000c2c4011311400542d011100094503681864440743c0050f0002c000540203201504103030711500e40e0300000d004001c50201c0710b0300004000d26000f500c00742d0032155414142d06101308208046004100c1d8468621714044c00f80d03080034007100c2259101ca144c90125448001c1c1112000904d0042c40c050580f030602 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 537812284 1250 537811034 537811037
    0x1911060c120a03090221010e0708071703040306020c0a0c1409160c050a140c060f0409020a1e09030204050a140c0d020409020d1a0a060e01030b06090d1a0601 69
    0x3040e100a0806468450038440c1800d510000301d0720103070880c82600038245642d000f034a034041a4484145540d1840c034203c065800c19802c00701e510703840f5203001400e6411154500f015007201c0d8109103480340000c03041003440300184424040440032400d039100230900000d07640010803080c0030f80e25051400c28200e5000125950840010800e692221040d0580c0320941c007040c0302e80000b80c0b0f03178150395840c880071020340a03100300603480c0d0400460003184140c4501040440300098418000c0245c50f22502d0032120440405010030081110250041d010308609420004a1402c1c60440c1551040307c1c1840e190000301044020415801d01d40b2038030fa041101b219080c864a480200b045550b010040c000c49504640004c0801c0c0311029030b810380e005010041d03000c2d540c501d00440140040e040700000c000c0792224199100f00702d46010f00f0000c088485d2a1560044000c0041c0194010800d1000e01c0d608030b242041030000079a90420041c6102e480349141c503145000e00c202c4641d85500040400e070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 537813534 1250 537812284 537812287
    0xc1b091e06040507031d25050d060c0302041d190209061204140f330f070e180703060f061b0c08010504080409150501140d0905191106 59
    0x10191140e94200ea684458140c80c04a07043e1203620040307004012112604800718018103020800d100b01044c0e0104110205c03241b0040c111404004549801852107400d0340084145946400a03c0780d8100350030915180c1801801c0960310b130541204c1810030001000f1210105007002116140129110069200b006d0b085080140c14004a103091049008240b010514072000808000406040c03a65080703080098450300c0000c1841c10f6610700e400007501004118581d50501043e00003240448406c0c2101100c0d5441d46440c024041d841401900c241d0800182c190b04005d00d4036140a4424644140c8501c0441481d0503600203044a0540e08682c0341045520000c201459028070018600640180e0910490035145040040c02055602c511641d50038441007005001c50310300540100c0e40398041c2400301c1b55071100a5002c1e038586018880c00301e03500303921801e10011348001801004a01181c0003d10002c40e072a014608002e4060705440c961441d081e040c10003815100340c960000c0241d8205 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 537814784 1250 537813534 537813571
    0x9140601050a230409090b13031b0f02091005091b0a0f051606020a1101020712110a05010e01020d0b030a080318070b16031115010303030509030c1b09 66
    0x24003034400da020002c00c004031440d40740b68103864078044030b031511181c00c01d030740d61565102805800780c00c9040c41640d0083c40c01c4000b03250004001110301c0399030381c191f4496a5411601d2910f100340301c051a001d5a02c00d0041c0d40300e03401603d994980d6405071411900041d10241351904000149400525026104016000c0071248446010603291003c0c414109080c803c2c80000b000c0f99140104400301c2040c0700100c0a03a030500215500400943d26140d0714101c0305100d103d001d900380c0c822410014100c1030102c0138008043d02c107420100f142030052041d0784002c0381c2900c3c3c0b2403e40303000000c1e09885940c0018130002101c058410b60303a1404013031700034090084050701c43d10400d0000512030950b800c2c07142c01039520107078240000400f400d00c1d03e0300d03241c446d040304590340c46411a1203c06c4012030f01505004145034170000d00340d601203021481403103040e82159411000340c04041c02c0060710348414010f002c0c82110900000d20024210340040c40710b00509010400d903003001501c9c401d09803017205401d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 537816034 1250 537814784 537814787
    0x906080d1d04020c0114010609062c04090501051e010501090806060f03010612030e04060f0e060409030912030509030123010909050a0210080a0b10020d08220b0109140601 75
    0x207100c06007940003a5141005003002080c064810740800112075403a2004e400c03030004405000c81c0c113031051a910740c0d80054580b20181c600c80600040e0901c4103e441c10a0324205080c1d80c0d649508420152022510303125a95425082d20810343e1200800b0b40045a0384c803958070350321001c82c0140000d18016507020329050540c0d0310703020003400701c500841a01421106030f823001d41000c401800880b4492030750b9031660030014400801840d40d588920709004000440000440640d016100c03040312070070094a0f00400c0000420f0668821001e02002c0c00d07002071000360083c1c84406240c0a500e440d595051802c040600f100c54090b11003060034024411540c0c130110401c02d0a0540b1a091000240959681006807400d28a184000d40c090300c552198000c1d01e41c030511035030051000c2070090140ca1040001c0003100d680721410f1a005030b02211035147d00f5880b9048481d00a410701d200c0030040030f442e84405920300100d03401940c240c2106c1004004c51100d9108020342440075418010850405000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 537817284 1250 537816034 537816047
    0x120d0e030c3f070e090a120513030818180405060412140406030608210306220204030b04021801030230010920030a021f020a0602070c0906080d 63
    0x715080c0c1805003109161850104010100740c00b2000c0c000c2400300e5040808a035503400050060107141502c500200c0c60741c00e00007405d0035965034410360503a91f1214020341201c8580004810700307a02c0100310000808175040304000c1c41c854484254842000d5a503000340500100c180740381101c1f24000400308004501d000c1042c50304035a1105040e0a0401c80d008100c41c804070500710700c181707460000b47c0012010b42592001046810010583d8590040c021095804070420144d6a07030495080000a8451400c4104403030f400c51054a0004640b084802c0e41080343c020b60001c56041d100c1405120940c90038802100901c2c0312048850607940c15540031070340c3c51003c1c0c1c42c400441710b074280804649407a1a0344400100c22440000c200911090801444c00c640e11170b01002528000784210005040109154a02d240c02030414805240c402103401d01c1c901c4071550501c118040d8003804400104240002c05625025811050011303041c000110b0440d10907500500d0603501c4042c49101c065082003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 537818534 1250 537817284 537817309
    0xf300c020118080301091820010f0305040c060e1201061d13050705060a1e0e0a09020f0304081803100203040506060904050d030b0a1715070e01021e0a02120d0e030c 72
    0x141c04113100c0d01d607140340d4500d2404021f006114840c0c44c4040b04609107845150b999010307090380c1e00101c01204110540032205c0a0b6809002100a50710601440740195286041f81402420a502000603d080d150131241260000311050000d0064001e080012070f0b030306908000c0d40c581c1d18566208d6a500c1c0b13941c0d60b1040c40307041e000f4035020074841c2d80b0b24021007030080300c10195804245100406030004200303840c10203015124442c062808101c0141c0ca100fa036201041c3c203031900c4c1ca95140c42c1c641207815001150880c491b504240100c407181d0300c0a1008003228032516801584a061a1a055007070110003400c45004005000410004c1280000c035045050418100060054503038004104401860380000200720350b2044140c42030314000900403100d030700920742c000050721440805c98000010118440c016030140a071407440b00d03032440255090404c0b94044820360f81e40c0d03030301044034400f419070300e0340854025080341e40d0b1240e00301502d02150081280500480c50124000514004025 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 537819784 1250 537818534 537818549
    0x509040f0e070e070c02180f160c080706060b12011805061507170a110c03060601090320040504030c030e0d15020c030403020d050102070309080c010f300c020118080301 74
    0x40f03004c02c440d0750203002e03c4041030340c000d0448401c01003001703445606010280c8400d40c82059100000b0401022030030501992444d550300c018a00d803041e21100c1c010f8110b00010341c4c40c00d41d100c0c0005600c00201c401800f2040301d0200c106811b41c5007201000413600c3d18249092040c1c2040200107940c0d8400005031046030112850301e40340c0b1294200b10300d660391100d4183c4000d100010303c0c0d0612940010822444401400444001420403810b1603200d03081511403601003004142d0600000f00401c0980c0b40041d15041c5025100aa90300014155a016103050b00442c190b20b1010b004e1551010001d4040303007040c1c41e141c12001f2903544802c41d5501d00c298440382e841d400b0488040440d0f06100715401181c000b0550b681844460038950300070b51003500e040b404180c0008000600d61004580c0080509050316500b0710030695070802e494600900030a00814608090003106800d94008809010713180860b0008040aa8070400380c04c6440b1880410b0319480300c080749100141500d011030b070568111 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 537821034 1250 537819784 537819809
    0x405010c1209050d0c11040507091e031a1e0f0709230114040306050a0501080105010e0405030703120608060f01150e0f0d0302010b09010308030a06051813020f100509040f0e07 77
    0x41d007004401ba400b40960030f40e2260800040c0030026512080a2003a030b05442d0440c560341030400c00241034200d2621000700707083e0311415894500f54003c00220f50100d0341e8241d42c0300704110038030800c40d41801150898030140d4043c00344402681d000039030702d0151424080c5881712224409014031200703000903040e81000307070080c05a41e1442d050019070300119070003407042c00030f4140f4106d000007420003405156015864400001000480201d01600070754201f8041d5241003281d850840d102c0c0c00a4006803859500c0b0800083d4a400c10032a407885100f40484400707907541444040110000e845400b4000c2040352001c2006a5442400c28100b11400311101c101d00081c42c94141d000d0585c400e4104c0d4000c0b14100000709006100004502c500d90500c02000301545450810494010300c000032040c000d03034500042c2c170342003841c085d1608046c0020074040c244a5280c00184143d4454120440028000b045042c09400c00380250240404002c50904c205c100d2042c1c4c0617039844981c0700b4030005414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 537822284 1250 537821034 537821057
    0x3060c052712070e1515040b09030c13050a05060f1c050c040204080f060705040f030605062d0a08070501051e09030111030402011209080301060c080c060405010c1209050d 75
    0x2240b00003510414861402c1d01e030803507661120a203404108861440f00b034107074a02c00d800e051a00980502100c06000f140781c0c146824a40801e0341a000006040d4040c8206014200e03190ba8070100c8007008060410082668601030200c441544d08c09040540601d003500015005a034827589044258040307680a0384000c51a400c06524050b5641042e9811510005d000f0415082c08144601600f6054003258031648400200701e641d40f0807486018284007080c030040c0b0002d03a02d60451600410010602c2114161b10190101003041c07112050050140900010080d030910481d110010036450001d010001c0c42d040000c1e04900c150280030b640105c491100d182d070000618151030709000060002c001024020f18126a1607006483c00d07804100c0c1001a034841102c64001c412700a50710440031800c6034070300710b000e440c0a642500c040b1920507050142c1d0016020800806110b18042c5002081d5291001030240050aa940c189841d05003404500b002044c8000744219040c1c01625200e080d844 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 537823534 1250 537822284 537822289
    0x30908580f09030917060609061c06060f05031005130b0714040e041502030402100f050f0f0301060908061003031409041406031b090609060d0c06020703060c0527 71
    0x1050200010007039140000740300a0603072101d08038054a4900820f02c9004246940d51551003c003242c400b54840b800c40005a61800c00c01d4142c0c0340d011560092181e001c0d4169036040507151250400c4940300300e103400421071441e0402075070048414001c0c04111606040b01c600c15007540402d4064401c407014804222007610035041003900c006c603001c00c140c82d661100768050031203106035426240071641d006901c60a100501c01c0f0b90045500a00507100d54881480580d00074101015003030a1210034030a03880c1904a810043c096000e981c840030341d036981002d8001e482ea000b1a01700b9043c5501050070000e840f044400c442c0c2c162601814129100c45105d1030288541c0300f949422038002e03042032040740c0c03960b000c030f40d00a005110450030b031035000070405a00401c0c41c10640d100741c2c2c41620140400c01074108603500f0381c1c202101818420354070f481c0b46c6801c1c0c081caa040d401070006038000c1000b0070130b200c1603100380f011011040c42c0841c42c288030108a44003060000c000003110441140f000081503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 537824784 1250 537823534 537823541
    0x906170a02130f06050702010806010f08130804050d0507091802060706020c031c050f061c0305030a02040911180105040308030711100c030c120c08011503090858 71
    0x901c3c3e0311040412154982100411a40104604a01107440380001c101c2c0c0b5805206410203501e41c41d40c80d041075a40d1000501035a00701c1c41e0b02074904007410880450580c85100300c207100c0b5400352004241061415641400311a400101c03110f00d13007106c00130000180d0ba00350849910075040b440140c5c4851120418030b06500c034101014607000c6001c42030300d2001180c1d4220500c6031038204950f4840307a68a5042c00180810b0505079000000800a1000084d004001541e04880121001800c007030702e0307046413400c0352036000e02b210100301d0100703124592141200d440c0400d000c0a10740142070a10310350b19540d550101070403410074032040c44074848106a0800441400c40d0b840c2d00f0600410307150a80280c0148122078000b03000074000d608584841400e802030400c4019281c0c3d40d0300960b840c06100a48061004080100f0151900c42071004500b01c100503114540c0c0041c804982844040d059007400d0404d107440307000c000929192499041d013804901690210181d100d00481d0404e8148030005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 537826034 1250 537824784 537824789
    0x19050a030b040614130b06160302070f060306030c060201090503090609031f0c090b0c0a060c051b060114030d0c0204020313020904080a2d0f26070906170a0213 70
    0x9483c01e8000039000700007150600d05004159400d40007207002c17410704820fa405400c05940c204104010880e403658110581b00c03c1c041c02441901c0300079407688584807035496036900c8040043d84840060043c046002a040010801070000300a80d2031995220380d00d038001c104079a4824030011440039010348080c00300e00f101c8603840d4000b51403c03d01461040c0108210131000700040d0160001207100b29845040380c2181e803441c001031030041c0d140d60710b1801402e105201c3c5001c21000303001c1c035a112a2500200c26120f171901019126641c1403078900c03c02d80e0100c60a05100ba88000708a8400c282c008002c000016010341300560360740e462526680111200c0d440082d0003c0c003c90401003884640d4000c1d1101d860913a48072071441c00b44075140e242c5920b013a0540e50000e01c611503010b5949018403c03910f00711185040901d801d100584842c1501d6203000c245022107104a001c001c0042c1d40100d290002d40004d0600c0580c0f9041b0f4580010350303420050000b0401e5500142400340b502888100100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 537827284 1250 537826034 537826039
    0x6130309080f1005010f031113020c030d05010914010b1e0c03040f031a04022110050114010906020f07050607110405010b070b160e0904020d020913020102060c19050a030b 75
    0x360880782d2800b41d41c403030b0364001c02c1c00582c0c035150020510212100220003203982003211404003185110420081440c4140342c1c0d070540340d003080b10010405003800a020008007500001803d985810301000c02c1c0c03411402d40e1204e0000c0000148035421200090300c0018407030320300700c0000240883c00d4429134811041003031402d00c4041070000d00e141032050403800343c900c600320b524003000b21802e021314004000d8034002d50201550996103060000c4444800d20004042c0442e00c0c1a006422050110b0718203030080c203c00d9044138481005560800000c0300140014401464140e0080c02801d8a41031240a000d00ca000d00043d0b49050040f00c0000090b001402801088156914480d59040e580030101c21151020b10b5000901047c84040700643c00a03880d880300c00c40103510340c08100341244020400c0f1b80c04011204400c0258589040c03140c1720340a00254400d1080250001a16091006000400c0038604101130031440c1010041c440840c001400c0c02600c030301c58010140c5c054045120b01c030741c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 537828534 1250 537827284 537827293
    0x3071703100524070201140408071a0f0a051602041401030605090d0801060e180709060914030304060f0c1b140906100807111603020a050405060a0e130609320613030908 74
    0x309c1040c04101071048076071000c50140c83c1c410071605d800d030174042e541d45080110001d00c6218140d5000b41e005203038011a100d90707500b4030901540060222500c500c44511184080401401040038910030b003170300002200010414954034080c000c10004050180c0300030004020581c1d083d68640303101c04070f2211005854105030340740000c00244060000d01c180400251001c3c0c0c002050104204ae03203850400140c061498030f400c2990503034241219010100411000c441c805000c070b605103020001055880089400f00e52402000051816500e40c1542c41410007000b444400c0e41c85505a8881035080d0030400f03000e40c0c0c0c01100f0760365200030b03519500d081d0142030740001a210f041c04225060b00d1003100c40e100c07801c0c1c4910030b000895008886c03854000060354428003210800048159000701c122820b00c82064040e550401a282101c0085446105d00c056000001034400c40410300094000c0044040741e084e844202c0d0b8403400030303100b034520300701c6007003c003050520492034000944030840c00c56 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 537829784 1250 537828534 537828539
    0x911120a05030c0f07050111030a0e060702030d02070302010e0109082109060c010b09131101200304030c0512030309100213050a12030206180c12030717031005240702011404 76
    0x98803131511110401c4540a00c020110311507005911034096018044000c604003242e4803008e03520808040d944940c420b405004400045c1d0701000400390100440e4040c010291642c40090182c400d009640b50501244200c00d0280810003e501d05004079022803001050b50782d414948070714840c021125402c504002109107020303031705401c000d035150b00984003509039650709014818096240000103050075280d00c0e1038442d9610540c0c0104102d02a1801c5581104035048668070f50390080e03000b04c4070308100d540c2c1080686406c555450612120101951852801e0100d580d180d8071406403d0030380301e5011504038141c07801c846103031019100160122200d247c0f100c0301852440545042100103118080018043e5500422100030304c12000e801030610b501c4440800024160b2611001c40c180700502c0040b010445003030716100302008110899a407402c0100303160440c107205401075030140c29209107030f107444d0071400d01d104041400b04840d55140c0b000d901c0100d808000e09144000e0502012402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 537831034 1250 537829784 537829807
    0xd140408030727231002010b040509030a27050d080309100e07051014120601021606080402060c1009050c1e0a2c01060c03030e010911120a0503 63
    0x1c502401c01c94840c0c0d1150443c0a25034016407400c60302c40c0320f5892540004001814100c04401c0e200c085802c00d40700460310490110340c00c82044c40b074400042c2c0d11004900c0d640c0c1054494541c110080c034015603d0203031a030300060148003032a0501600d40908038508889036200f100307007001030400141054210703070440c00d141e601c940043e030380b03000c5038000d41c00f40402070310701c1d4440d014510030420090001d5078544020000010b038020070038424803905a500c40807441c2e150000b440c007a1003e0001e02c4840c20641e000a1404000c4603040c00c0385449020240102030300040005d501940c1201c141d03541c1c0310400c00e40c505000b011030503211200d040201c1281040700c08105c8855240702a500c04025107103410300d41c6000d2041061550f001054010180020001c071422040c551030300d000200d1003010448180100303240241d02140000c0c4400c000b1204150341401508001210304000b07002d060b007142c42e50000782c10522038030b41c45803045540700411400180f00301e00010b81c1010641c0c3d1103000c007054 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 537832284 1250 537831034 537831037
    0x14030720011215031205070c17070e0f0604021308011415030309010909050a1b020a0c090209010e01120f0c05120702070b1209070b04030501020d050114010e01050d140408 75
    0x80c074041807542d4201c0c8078100081c420504040c4483c110006002d01c2c0d0703200d0340c2895440c04140810004108403181c082685d26048200503e84034030842c0c486000d040c4c00b1400d0083c81d80104800c541040180580403804411054000c442101d00580e078150095107414201d4071540001455420120107644400c43c06a60703612400e00500c0742a02ea50031041096202e01c41c026095001c1031403910240544602d9620280d0301800090001504a1203924980400301174880ca40c030069000901d80701c10081610f024000030b1260034000d40c00c103500ca50019108035142e00203203040040c80c001c80c461180c81740d08840d0138240c410404000d140030710706005201b644004a42c4c01d4549100c0302180c0c1940c4001481c004449181c51414240703d803140416034020405041500d0303d12921801085181101c00104011031080c0001030b0b441c9401c0b640e4500b5108145d00c0040c00e00003810b101d00c0e1590300300c00101c1504100740b07061641e41440003812401003c0c0c80340c100c4a903200070b40810041180140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 537833534 1250 537832284 537832343
    0x32406030c020c030c03070e0429011505070b04020d0f0b10030507050303030105060304080f2703010e010c050f0a03060e0c0a1404031e150e0c0a08060112140307 71
    0x1d00fa5540a80c07000b0038190340e545004420ba030075071b001031002c10020036141d014940261040c1c04e010f0a00030345407803c42c40e8080d0b0301e01c14800d42d01980010025111030041c440e210595505240342049840d0301c0790100c1e014000c202a0203801a0300c2000c1c20017160110100c1c0d055842013996040d03090100b0319050507031290004482c030744500d64010509280010a4074102c600081074185995242c5da25404a82c0240320316054803003003400401051004442400c2d01800308084044109a84100700350a641260748408800d0b407408024008861740042290002c03812003401c541e50300b4842008400400c0703950300c07181a13540d550041c4084440d502000f01007904042d0703180042d0003481f1104900c0e5100f1444020203102a5207680822000e002007900d4590b400b4402d4608100c03281c181d1ba8041d125120848590741c1c102004504c040c1c40c045040801400c051002080c29605101c100401118200f0014201405002c030f01000444100100c506007a441040f80d0040400848600f03403000c401c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 537834784 1250 537833534 537833537
    0x20105150a0f1e080601030b06091305122208030309070602070605071e05150105040f060e0a09051612030207060c120c1b12150203040b07032406030c 66
    0x52600492a10380240d1000c02c0c2c6000c07020002c0c009141c101e4280d41031958210030700710782c900c01500040d454000d00c5000d008601400c00c8007900c0c135110003040071401c40240580309144a0f1070201e80802c000262040c1d000c008184c00350b0341c40c81030310325049203415031f0900d00780c074903110740c1c1d000c1204900400a1405440c0d10011101e016071128001e03030b04c3c0d860074041c100c0000d0051020b1004180f141c001c01008103182a6001e80e5050507840e400d0030b200006a08000320400c10004000f40c0c1001d01c00d40c1010300808100f0000c66040502e000c01403540034002c000c0807070303c64500e041882401e101000014440d00c0301400200c0c0d50f603101c4941502c140505030090b026200340041c2590042d04065140780c0c1c80f4140380c02d64120303032100782c81e040c81e81202540c003440020130302010f60080e602400040c201001841947d415a842c19045d0f6020a151107000380e40103109010002e180050b5481c0c00c80520f0802048043c2d47c003139011a00400c1250ba210b016002d503600041c5590140c2c042c0344c454015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 537836034 1250 537834784 537834811
    0x20c0a1401140f04170d18050f12090603090c03152a030402041e05090a15020702090103020d080702061306030e0a1722090b100c120302071103010606020105 69
    0x6868201000b4201141c1e0b52151401801c0002c0020b42402c42c84510a03aa8100c2c2c9070a140965500104a80f00034940e480766244410302603042c0035081113100e030a00c00f4100144818003e4103164276980c011407007007500580000c808503001c1001400800031909002c1c0c2101c40d806200118030041c11000d4030b0190f0f0b4122400d802c0c1d00e11500422940035040240c244a618584580d130a1100400380004104000505510f92044090142c0907403805090b4610090103408154140b403c08000380c80d1224030710902c108007080041e240c9100b107504498048072203018201c000c1c10000b00c11300c01c006000f50700c0540048c024056114801402050724102e036020040790343c400c44240e65a401001c00a404076044490510300e24501034000c0c00c1d90018a002c0c0e08021a0b440103100000700c3d6078002605003074507001540f5642c2864000301c3c15802c070070b1900c9038200141e1780726489401c64581c0b032001055000076040e01030291001130050021006802000400c0ea525002402003000740c940780c120b41403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 537837284 1250 537836034 537836051
    0x90d0f0b0109050c04170312091f060806040f050a1e1e0b0c0306010e0d050d020f161e0e10080105010503010207020a0e07021c08090c041e0b04020c0a1401 68
    0x144030366449503180d03080f413510302402c090760755007402c2d84000140c04a2000700502d02d800d10400180f039025000000061103400d051080000c242019450001c840c2440c007102004001c0000800c2c170b03000307508540c0c4544003001a040070741c102455400013911002c8183c12607010018143d88590b9103d0180421410805015a440505080c0e001019107040f050002295010b05078400440d0403001c1410110501c46030480810443d500640041d030f65a040091030703070300d41601400801b0103081202c000e890303480700310292200989228080d44000d00c00c00c444a14000c1070b100300c494040e0002689081143c0340c4030700b00b02040e800070700808100b942050f000086038141402a9407081e540103008010040c1004c9244450420080c403034403c5215000e0540c580c1803c04047c030402004a076517100c140d16190410b503113001c04500c1c1e0103004070f1400300010540000812104080c90f54a200401c0d203e4082d0000b5010b4054013043c402c003805114840c804011140800038601000c44000340607144 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 537838534 1250 537837284 537837299
    0x507020a1505030f060a05040c030f05010609050108010b031504020304080a020723060304021f0c05070501020c151e0f041a03090304051201020c010903200f100c05090d0f0b01 77
    0x1d100c101800c041141400032404095098510680c0030307001610488003d0b0f030300c1000801b502c550503611030210750f840d0481884c3c49580d00541e07000d400d80c3c0c01c2120f1703040c0c50a00001c040c44c06c148601603c208004c0085202500103c810b02c1a4940c001d0040d0b4036030600b820814032a6000da08690054072800c2c44c0081c600b4500303010240101c40744c441c0444410701c010144034a551004000b00d0b070140401042d1545103150241d00e24400080c1d03501c00d030721030110b49819071600100d6007009056500440d4082d103c1d5030340d04544c00c4a030141400b480c0d210341c0e2080a0758281c1c070640f500d102004501103400e8085150410140003101c80f81d160182c5448040788114416200c140c410355042d400c10017052180b81401480b91a4540b00c000006142410f203000050840c1c0000d9401c400003401600f003030907060740141e0500d800c1721000000d80346c90702c195100c0340c0d40c1d00e0360910103c0015454030404071005000d80d0035100c484401070819080e929082ca8508013122b909c110880305288120300110340030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 537839784 1250 537838534 537838559
    0x8011401091a01020c060901170c0909010f03230f06070f2a020d02030307060f061a03090604060b0a0503060a05010524250f060501061b02030c060d0204150507020a 72
    0x6000c1031300a060744285103000d100032a0300207400e10703051200c07980c29803044004140205204e00f01140d101d41c0c0340e41c544020060004810390001040600c07141e000d0011559640091800d460b29080715990310300601e000c00d040c03003d41403400c082402040d04009150350800000c901000e0680d640c1c0405100524248a00881c0000107072202000841e042c030040c181010b2855416000804590400106542d5902611103130644200e00545540041140c84070f0f0588046560303510030711b40c60441c43e000e421142d80c2e0000a101a061545a0440c0045929080f0010001e000040d007a2031880c0b400b0710a0784044d020a00c951800342e0002e00d401e80c0e9020700015403410429100006a190000070488072203920341c0c00d60144000740500085400007080340161070402407091601051075031410001400e103440d2210514480034807120202c1c01603138040795950b01c8040c2100d0880c1caa00e64402d0b420020b0003150003c0b0400c0180171004000b20750410058407009100700e46112482da124040d40820 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 537841034 1250 537839784 537839831
    0x110307080a2d021b03160201090905070e0409060615110c0102071508190905101118040f09020301291005030c160219031403070c030201050c01060801140109 69
    0x220501d04542d00081000d03074006104000d004d000c000001d075010510340303055030700105003036114012140c02c800440d41c010120000030802c0c10302c100951704d410a4040c1003007804d41c01c02d130701c00d0360f8074400041009001d91140002d1700140c0c00541114040c4040540541c1006a06c120a8880c010b4160095031000070448103035807110a40f060841e00c425400c0c1d0310072001a042038a0200d12030f00c2558800d020748a0b55403000d005a000300071354181d215510040ba010036421a242c124200540c1c0e8010125900c10f1000d550103440000e6070340300042600340240b45024000b5499400c000e03158140000031418620009403400202461401540401400201e0f418003400400c00600024203074444580241134014882051a4002145c2e5400101e4a843d10400071b00d810303c0894080c018040030402d5810410500d40055251021540381e11540e0103071072000904201001070309000314042034000d0001481c0320030082c45014040c0854001c2d6031424025034030304a2602d4514607480261040300c905 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 537842284 1250 537841034 537841091
    0xa020403080702060c24011401020723030a0605090604022d04090f0605090601180603021e120d0c02010f0513031e080c1e0d08010e0406110307080a 65
    0x70b0490250300f0b009030743e0010340e9090003a00803010000c12a0811240d1a030f4292401005030301150305000c1081518403054200504660141c80180039203400b04040d246d1200248284d00004201c003400289042c1582070000c042504200c24003803100700000e2000c1c0114401c50303209180c502041d01030050308500d01034494546050021303000c410f0502d83d10684d0000d0081c00441d403424142c1e01e840303041d5107040d610114998000c000401001d441c2c0041c4a01c821100d41051140c1d80c91500014140c1100a1995a0790386200650060070f50b0741c40c110607420a03440081d5400403100c0b51010f08050503000c8141d0120718154803000c01a8480c0e812500102d0032032103c0d20fa103a042da11a00140449040b10784504840080d80c134000c181958041c0c43c5011019000306004000300c0c06d88031040b034044e0080c03641c9078880c0d00c14a6400b0340082045040d01c1c46c8050b0405990341d02d04018018010301c111a03004450000203006400d948040f11032b205684142d000c1c01008002904021304c14803030760003803c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 537843534 1250 537842284 537842287
    0x91207060f14100e070c120c0b130302030708030c130b0d0c05030423030f070b01170304060906030b0a0906060c020f09071b080d060f080f0102120106120f05100e0a02040308 76
    0xf1130b0f010840499040106840c021b5803900095a440c40d9075070440c0a01d4010521030782484040100c131005141d44442800c020140100702c07507501964038015118010300f1503101100240c20f090503030064a5484d088800300c0c1c81500d030356101a48803540405900e0307201e207003050800d605c0305000d1421240180d600c4500c6a000010210300c1041c840803012611489000070070031450144040005000c0b160b00806400c211949881c81c1d441400c00c48a81910f03ca070001d120030406250811401c40886050741408030742c01d0240400140107002d282c100d495410310b009d10100d5602c0d481a0540b0046100f51a840158003211003000280700c4110f41460000e00320300d800f44100118120800c11040c840c51f080c5041886c0e204e80c600688949401c403c010484020042083d280100558000c1d542801c00851405450440b9001c840b04140100001d0025680c1a2a0039100503440b00b03041c40361201c8100300741c1c180903030150f02444c00f81c4141d90307080d14458082030242c0e1180c401c54003140d51008000303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 537844784 1250 537843534 537843539
    0xb0405060f04090f02040e0c040b030607081b0708030a0b10110c060a030908041205060c03010302010207060c031116060905010503011d09070f0b1308010e06070305091207060f1410 79
    0x48042c1034070580413220b604031906a0741c016151400b4514800c407029018001205040e018001201c006190701d511980c40141800440d58101c0c503034540144903100740f40c1c0341404240507140644105803005005803c00010069030740038a0388030949055044914600300e1110380c0c0c08036078107414076a061809030403400f842c80c0309e458010020036050703400e810301240316017107629010000c1e0417584c8800720003904030500c0d00c10082d003400101d40c400c0001e405e2500319415500000d60382c0c8018010101400f400d05491010325014054001d100d103030050440780251000c49002d03c03425001c1c0314108c041016214046119802441500e042e1004005010051040c003161041c02907405011100c580c001d807234010401c40f44001c6420f028001d004080b603230f0b0381d0924440d00c2e44045503902006d15a4900041d40559550100b452074110600d8680440c80e900c908a4450400b1170610340b0305020386001a04508104494225811040405200304582002c030003010700b10107002c644e80b88103802c0c200002e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 537846034 1250 537844784 537844789
    0x10b21120c0106090e01090605130b070f14130612110d05060f060301082b120e0f1510060305091c0201091a160e0f0d0204110406080a0b0405060f 64
    0x1401c5040d01c20000880e00994600080b4101c4150f4203860041d65150741c42801070003107a0103005e800040f100300c8051288850744501540c0c09001d0400010032200031200140c13903200e00e40501d0070711680c040c40d40d82c8540490076120307014001d2007000041429603542d64290080d0703104018840040781d0115103414845c500311b40080c14018807440d4003505904000d2a9900c410010758081c2980d0070043c29400105900c41c150032446548403403e80f0346134070650b01d59a51240d85503195000303074500072500081c07900f940e60070308076510a90b950a2061654000204090080950180c1130069004024a440c0c0d4412002d944007128214101e512034880b00c40466203035040d00b030045a0034400040d5a04d080e80c3c0d001000c440101710162031036034a106105803041c0d04081d40311210110b0030103401240d142c0e004107520207150b00f4210300c608002200d030000c3d5121074001124040000700c00b03d0340c03580c42e40c00c00340203200d00f560000c1c3c0c40c0c0c0c0b0740040030205040a00ca100c1c0620703170080220b16a40d1000c0e08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 537847284 1250 537846034 537846037
    0x90a1e0306050c1b07170c0d02060702150a03090b0c04050a060c0512030f07031b0f0311090303030406270b01150e0307060f23041203021509010b2112 66
    0x4489a8002c042281d0110741c00300546040c0040841000750204911b454407091820314070b480c0841c2240c20180000065503a410690b02c81154143c4841d40c45010030b000003011520001261031507030b00009880c0c0704817603040d4440c64001c1e01c1a010a015503c07031140f5201c41c0c3c0070714002c29412802180080c4062800345211038000d42c407400850303030b0403040700107014400d800030b48c2c0018a0139486024007801c00c1d0180a610b0000e03031024030303602020100c801c00928044c14502104145070355824003642c0c00e92010121242d0b85005000c0381d54034100362411800400f650200d0207110142e90b5500d07040b89095108c00c02c01d035038020760491034990030a0540208017075000f1f6001d086c805210b00c05e5665172020311800c4001d040649956001c0000d002016001c0f00180d0440c0c0d40d400c6220810303a04501c048003c2e03c0c1511400150441c2030852440e090b843c00f0fa44a4011742801808010080c0100054000c0075034a401603a40b182141d400340c4110685501c1110402c40300d40082400880d5102d4000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 537848534 1250 537847284 537847291
    0x901260c0f1921090c090509010603020d05070603050f090606011206080a050a0308090309010804110118090603060b060a020a110319050105090c06091c1a010803090a1e030605 77
    0x16100d0715009826109074655080104460086090080300d4004100000580310340c01498103c10b020309101c9070345102d031006007401000c1145179100d0115021035003d42c0220003450313000d46207005011807400c03c0caa40302590b00c104000a0700f0840000d0103050194101c03401409000000c0c0304070340340d0f580151610700075955040040c1d656142c00094540e010007062200d00e0241000e001e100305d050070020209003004100d40c145030300c10400e03803c4999005401c11307401070300224902d11400342c1030012619450b00d0a074140c82c42c111b141d40460140c5103a8442801c41340320351030400001964100b0301c45a40200d01315140542c000c10102c00214091a0141d00140307001016594245010b08981401509108043d601350790348108110605d04104900c1c09005401c07101d4905000c440000207800001c021000c04010020314080000c11014200d00c40f141840d54a03569030035a11801c3c100e95940107922054402c02c224100000c4012030425000c024600203518540c0c400d0554a681020346000b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 537849784 1250 537848534 537848557
    0xb0d020f070f030512060102030a140702030a0605180c0a120b1b0301080a0c08070302060406140f0f07020301180206030621060c041d0c18010318080901260c 69
    0x1000340d00000b80c0841c90b42100944242c039881d842c4c1000b440c07283c042d0700006142c141075510070440c800501d0741110112900da00381c0005907903222494030200703060520912006150504001c00d020303000d404400382036408245e8804859480000c5c000f045075007004d5114084c0040c0144c00008042800030b120a9030028001c010148034101203000700159078004d902807400c0d0f070420b54072142009014405c61005101c900020b01200d401d64001031010720a502c95202840000d4080080921700101a00c2d1403a4200c003402c3c4d114001803060390541d50260340100d12035481d021920300000e10042e0102ca2540d0040c006600395a90740b03080c8025415962904000d031180700480000b50342e02001a980308a200c0200c007521a842c0001d174403249005806024013000d681c204000c00e4a640704142c4820540607080c0196424605006031700a1a0f45c4122094104550885e1400d008040008000c4408281e0351020360005030200030004ca485081c3c101c016101d141d0124440f40203800140c200c00071b01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 537851034 1250 537849784 537849787
    0x615030f070c02040b0904060606260a0213030f05070f0b0c060103061109130e0f0d020c0103050406060e0a09030207082a030c09010306060e010b07030e12031b0f10060b0d020f 77
    0xc17100040e03d403d500b00c4046444d291504410700c035603940074142006d2039a036070702c0031040d2083d100818254228010000c4505641c082482480e404a0703041641c01984c00000342e0901580034106561038050718041c2c0103445640f04000560803401d8012250010380c2c080107000d880e402c1d0b82d240f9002d8854500c40040b014001c1c40350f480d856840c19600c48407008052000100d1070130000d5014101218444095a40d0300012a00705009030041000e8240600034a00050300380c0d501e24101004205a41110303030402020070801c00c401019500507600c95010b6002c4401c002d030f541100d290754010705200c003034481e001c1036001c1802c1c43c0000552554400010190780c080320300c030b401083e600301c82644203680ca44e45441003000945483c900e401e0140c0409032100b4600f10303e640b0007410700441c1028071030040c40c21200a529580c0c06005840c4849956182d104089103504209a940d541c8000e1400b40c1d801011284141108076200381d404a5406804507405c01c05c00760090310003904130309504d8010000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 537852284 1250 537851034 537851051
    0x4080d081b04060c060c0305040305030406050c120c031f050f0603041a040309060306050901321201020918010509071404090212070e0109050f0f1302120615030f070c0204 75
    0x72241c0900003910306981d801811a60f1403c0c03510965842103001c1c414180b4200c140804641d20070101e070351040d0006400b04041e10b40e40e072001058032407600038807c40d0a1000500455110a400640c010503000d82c0c10110318494641014042d5084e105456205a07055102081418130401071940280102d040c03006810916900e0032618100302d90450010b000100b040c041940c06124441c0642001d40f6107503095030421002a00074000f141d0301a4100707001c00a481a603603c03114180d03043d400c01901c0c102c040c0194050302c5002c0d4009444040c0706941804000c191041d04011450498600078803140d295110301d8400e60b03103503458042e40c0c000042c04000100b090303506400107112104485903448030614085000a0602c905100c1040c100140c1600400c0039649141d204000078104032038580164541100207a40c001a0034054030000d80049144034580702010031180c45510240e91030f1464541d0083d59140ba44011194036010607085004203144070311a6130211141d6102500004004c070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 537853534 1250 537852284 537852331
    0x1206050a140d050a080705070f060e0103110c1005060f030105090309190b0406050406030507020a15020a091802030405060f040302190201120f0501180213051005070b07020c040c0504080d08 83
    0x1200d098156103117040000d682042003404c112040c010300e041c04c250160305090110083c60069044d40762410035441c0c3c2560312950301288111401c50300103000f01c4840b104c10380c580c4170180104940302d80c42220031003180f074481c3c10180102d52059100310050b6150481010030880200004801d05104102c00c0002013400c15034400144090310903030300e420342c617030780781210090507600001c0c00740c030454004814040008101c0c0301c11031200001000c1c0580c881c9040d1100b00c41c0480560700002c0310b0283c0703450451f40202c0541c01140a5402207003075403400e503500d80043c0c81c10517043d2402001030f40107044540e0104e043c003440846145c814034203c21a681c6402100d1705513001444513101003039543d00100708146448107040c4015440a10640c2030813414403841c40c26034800d1150034010148805541801031103803044890b41c07540000041824182030000a6495002441d000d000341d1800807840e00180c010780c140ea081390000710043c00180010202150f80d03010150000c00d4000c8261844040786 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 537854784 1250 537853534 537853543
    0x60a09050f0613201309080d02130906050906010503130602040314100e0c061206030c0d1208070302071e14011802191412030c0303010e01061206050a140d05 69
    0x30821100343d0340710802c032410800f001000d0030101c1940300c1828011000c41c2d403200c040d06620550314840000e031020b868140600c4030301c100c400c0030002600c009110203816003c9040304055904402d000c1150507214402e001601e00300352041404100140000b45d00400d035503641c2070070184655000342c1055603e5940c3c0024401c00900c411407600410140408803000c1e1054010104521005004445140003c5001c2e4414100360441c100f03c820001203d0391401c1150b01d0a085029003070045800e001e0070440140028001d200303000480304008100310700e10900a0301d1103142c1080a000b007120350160340204040b62a202210b00c07014085010006210038032505240709840e0001e50006003039407040280460100d0b01e6030440c4110000188161242040182503940054500000450b004c500c00c07850340c001c007545682c40e440300200200380c1c1101441c0131412a80c1c3c507251110000074040e82d100c1030740c0c130602565410880810342040f030149070740161a03092002416900613a15a504d403e03050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 537856034 1250 537854784 537854791
    0x306020318060f15102001020318011e02090f0405281e090c080703030216140d0605060d0611031509071d0114031f0602030a02060a09050f06 62
    0x41d140c08106440000c0042c400298804085041d09501e49068100148501e219003a80e42c0144882c090940d80c450280c2081d0300410000b00341102c981c06c00e4000b280c040e41c412502c0c42644440c0c2d111480400301c0500500a58441031181940b46411314030b0508029040880e400d0ba11821610300e0f02e20701c2e210351180d1401440305c9062403200382545040c1c0e01849110300c0d440e0b4903042c80c0400b85000420008410084005900700200726074039a4205500c40d40d645030402c034464004c45070000201600066030050035004816404812941d0343e5204602c12489042583c00c01c2d44144210005000750b4062030340300034014480c000c0300c08240c4400e02164000d02c02c0740c00c2c1d503400005010070800c0440300740c009060201e07882030040c984004002c3c10084e8040c0709110f269886a5a02402e13801003511001e0720382541c8242c0e03141d1a0921071140324808240701400100014100412080c1c8040203c40c4038612913001000b035600c03054000c400801036041d00355424000c82201c00c04294062141070f00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 537857284 1250 537856034 537856051
    0x3120504150216020103060803090109030f1110050a0f080c0304060509031c0f051008150a0b04020c01090c0b04060f0e04110f071407031109070c02030105100e0a050f0c1303060203 79
    0x3e8003116440050211801d580003090f5640c401d00002c0010780e0b00040541c00d03240e00c483e0984550b401e0f07250081113540c030410b03c0344d40400c1c21905580c4481c0d01501130080c10500d60307a50300d0304004100707041e00c6884043d10120903018040001402281c101d401958002d000c0300704a0349001d03010b030750008021114107441d041403512081005100c00d0300f4041c0380e4009450b100c40301002d905d80344d00256200590f1010512025001001650701c012540c081002c008020b0806c0d55142c0141001500038031820b8000c5034140c0324030b4000719600703821100390380a0314056241d4075441515600252003a2502e480c01b45d038810344581808594481c1e44e17000d0034442c03050440031901c1e01490b20b0301d99031a80781c48000c1c90040d48804000c001040b1808243e1141c458151841c4046840f58482290700c0011008007075015800c08043c080348944130310303205089601d0203055000548a6a402c2401e032401600c2c00b901d407114600204403454034010084c584010b20150340300049550b6902d81c0d05903041110445c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 537858534 1250 537857284 537857317
    0xa0e0a020c01050606180121020313030f030b0303160c0801110a02070801020a052502030d11010b0603100e07050c01141008011b03022b02180904031205041502 70
    0xc5111803d0080c1608410219560703400c140d050071200b00c01e002c02c91401410070201c144407040301c1c9044c01200140110b01003081d0b5691402d140754040184403150110005050549039004042c0b080c4241100e11800030042d5181041c1381c04104035030f00d490b040a980b4405420b0000461070710034854900a0001d1060554580d5095040a030500015901111450340100444c0004c4d584c88412200c054002462401d400c0c4100070b4201040c3c0c851003030007901445440c900709441078108284040c4c0d02000002407205107612002e0000700e000a448410340031200b50000d0005151680645512482514240d820010070540c4a42550022600703041e01840900900400c03042c0d2a001201520b40c1c00001e002500c00418600603200810060170101540490013004000d00d41040c4441c00c95280d884242c10003581341204000d50000075a00390314541048480c841d0308001603041d100e160582c86840100810300e80780c1001c3c0c2002081120140c4a1101d0304540c00401d101402c40c00000810302d8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 537859784 1250 537858534 537858547
    0x1201050103050d051306050a11030706050906010b13050d031b0f12050421061b03060f0e04150f090606030308060306070813030c050a0203011e1104030f08090a0e0a02 73
    0x503410803200000d40010400304101551817002d545184c1030840700180740442e500c1c258034008072410160746072029414040000c0c0da4007031255641046005070311220550360103903038030400b113801c61088500441001d41c0c48041001a443d2600c0c464820f03d0203800c051120004030360314003800d02d8000307034100c2d41c07000d001d881402880941450480100040e0501c10b241c5818190043c1c3d01c441c4500c15a0200034800070300000700401354100040c03c10f4802d072207201003c400312000d809060030b80500c01050190301000601c007485442828041c40d00800820f841c28980c9005802a000d400342a080071611007403840000303480e600c102002103000c0d54800d5400c0c20702004141c10310802803d01c00030000d449092010745d881280c18007880e2603150400401982551400310b0030800e010002035815460414440c64014000810740d14010540c0f40401c202c0b075400aa1001500a0b4080170f0810004030f48840c000071110401425082c1c4024840008103548440703204400900b200d5200c4480e4001c59007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 537861034 1250 537859784 537859793
    0x2105010b0a122a0521010e03040e090a17070602091f0e0108040b06010c03110708031c050108030706020d0b090702100f06050d030305250329010801030210020c1201050103 75
    0x300c11110f069048103440c0710400d6040162501c199008003446400e0300d11203200700d201c410b102d44c040c007200540240721025030060340c19102c1c2c10070701c920400361070b0703e00014651401c0440d40300754460384210191240b150200359240ca40d00710010488520f50300b000008560b684416410140b6070070444134003070524019600504a100000889040c40b109005010000b078000e020954004001c0c600303c0f0351407555040c110b0b0100c00010b58112240121707200840d003090088018450880702a0300c84030544003110038842181ea003403250a880e50010b00c08080000d0b4184c008003810208030bc40416514071030000600e010700300780c5070000542c0c00a0701401c0010302d40d000e5a603010b1004102007100078036080104903170010301d400003001c1541c1d940c00200d0310000c0c0c4586810220002501204030440044060700600c0400c000140344100300e840c800398040401c4403414450010b0f90ba403803c1d0303440c5500348a00010401000000e41c05010400c845540318105401c0210320710f10008500c03545075040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 537862284 1250 537861034 537861053
    0x1b12060b1309020d080f1b060106112e06080f010507030e191202030c070308070b10062001110d060f090207081b0a02090c0d06060305012105010b0a12 66
    0x1c070710303045814120503001594400314405811034020416695591641d5101189441400c0382080055001080e85403000300000d0098141d8000ea00c422202c5550f1646241d90342d143c81800032402000340d0b9500720882201091580f80a85041c40801c449440300d490741c4c00e000c41ca503895001a951a010401503a43c140034003071945048901429441c01c22130780185460400310400f5160030000b2074482e06140c401c0085451750403180081e141d4194407880c1c000e0240d03114050542d08000528085000c2d0391078900000300710386094031154440c00242c010000e41031001809a001c55681d105080c0c10000d000b4010084048503e90000c0c0701030406250201c03105068020b200020f1043c03000c5030008000c001290761807a4440960180342404234030040ca416188100250021020ba045c041456000c40152010f031041000500c805134944104800300c46003489900b01c450a40c0e1948084001c440c0703004402140200c001103621003800000c035041e59520b03408280c20115540c19035051029a80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 537863534 1250 537862284 537862309
    0xc02070501030605060703050f040b0c060f0708011d0a150803090a090e151f0603021b060609010b251112120405040c1b0302060105010e01020a0b041b12060b 69
    0x2000c000040c2814041800d034010144014123000c1c00103048007c07c071004003990002c0028109140d134507808001d160792622000d0f6511214644801c0c0412030700e40c024000a410307540c0341d42c602d0048800090140110040107445c0281c1c141d521800300d58011102e2440102900e080f1004503513441c1c00d2810721176100d185901c4064202d280541c01c1502c0c0101082c021059515081d09008507100d50b80300d8003076050320510700c0d0100b5010103400a241505500038052418010760f02c001c03860041c41c1101d840d40c00807200780754010384080042c040111640c011b003039210b2100440180d480c4404ca003000240e1128181907480c1e0001c100c580050f40b0b00020710080035010300c0040c00e00e400d681c28a0000c10302841c02014416a00d0320318041d0001d220310702190004945842c0486104400e090103900c552081c0240760004a8008500e03d9950000600c102101c1d400112444140d070f46848440c60381c25082800100640c645000080c600e940c80108000c072030142d20001244142c1c40c0070000440a000d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 537864784 1250 537863534 537863537
    0x7110610140103051e040302030f04080606040605090f06062a030403170a0f140d09061a03030418090f0b010f0e060901050d0308060a050d05031305032a0a15030c02070501 75
    0x70820002800c503200d50205d1406600c0000e034280c560789003c0c1d00354010b4600c071103243c403004640041c40450010f45240100c4059604026581e110414001c0054044074411aa114544085107071350902c00c5c001c10f030b03003002c1140018505660014600b541c4184e8841310040354070104060080c4035031000500c05545a641200c0e24107158043c01800308049074103a102800a01070008044a4400040380d03100c41780840104186416450904000d007291600700401c5640059004061706000007201c00351026503d039441c5083d04403421a0241c002c0303040403914100310001d084000384001070014064400fa1880e600810b00b400990120380c1c50007060700d407042d81e40600410081d01c80c8440c2009071a0036107481c000696801d40410154040c0b81c0c49203401c05c0d8044928018041e002c4083c000e42d409914410210a80d9101055a00c4d0750b00409001c1e08584922616224849030640b90550301c0003802486141c0e684214441c2e016a45c0403135800400e880e05078807948240c3c18826440a450309 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 537866034 1250 537864784 537864791
    0xc0201020405101107030606090c090812180a050301060b03040506100e040209040c08031b010f140f040f06020d020a0e19170705130e06070509100807110610140103 72
    0x82c000052000c44009141c801400b00d5400a1100d1100134005c050281d030304072800707009035903582200e8001007800d85048c000241c102900030440440202d9040c01510708412154100403003000700340510324000c205d160744031034038110014060300c00703015440042003034000d255107034501410f02c2401e00300001d0101100c0070740c2000a000b85c4c40000b02d0301d82c110790107494450340f0307684610748209200080d41220115201c041a02180310f00c0c81080391406040800007030240419004900050703c4401c00207481d20804c01c00051140d07a812015a64007502400d46001104025224101264046820902d0b82500082c003105a603400403956401000d003502e649120140c0c4840c0b243c0c40360100d004120040148540301001c0040801550029020061000a9001038066014020203010386510100d008640000328090302910070741d903e092000e8107040152078101d0f8122003031072008100c44103110314400e81100c04001000300302d00c00c48940c1d02d00003109041c001d094201c000c6060070581018207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 537867284 1250 537866034 537866039
    0x5031f03061404290a0b0103020d0603051f0b0a05040908040902040b03060a050d151d03031009060e0709050607020a091b02010f0e1510030203030c01150b09010512040606170f010c02010204 83
    0x74a00544c541c081c40b0581c001603c2000100100c0c01303131083d40e60318441c10342018004018020041003000c0a0200d01c04030400000d5090611001e64101500d0540c4c0100c0e0100c040055050030303042410aa44502001f43ca41500d4107800c0c000c0360029007150001c0310300401000315500304081088060032080f9190039a11401d0b41c0d0f50b2010041500075800010f40300c40c482030552146141c02c2c503c0f91040f80c03d694032464284101000e0280c07038400d41c0c1c07000d401e0080001da0007401c0c840050082645a0b01c44d140726081c441030054903441020f08a0304071412078000078119040d0300c01c0f078000c000a40010603000206003802401e50f604030130881902c80c0780044014542200280e0310600d03200c2e00000750079607600c0d100d841580103810b40c4041d4040c0000a45048190010350004407004860941d0419550702c40000f186140180215a0f0200f00100304250f010806490100c3c0e00c035108110100c0da240c0c86070307585114805003680d480d50b82c1e888021000b503109000e020344071440403d80300031401d00d031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 537868534 1250 537867284 537867353
    0xd1118043b030d0c0305060319020a090509120309010b0f0118090f020706110406020f030307120218030712030e19051c201c0305031f03061404 63
    0x1040c03081000c0703051070642200c1140c42001c1c4241d5806200d1554204202c40d241100038000d850220340040c401e000b0305001040c840f0322045000c8030300c1c0e001b8204041550138507500100404c406041007400f807084400d007441c5031032542d004502c1442036070b0001c0707000d90640b000e100c62030066000f214180822405607a81d401140c0c40003c1c22900300c1100412170040b2000844002d201c0c03120007400d441e04204814100e0030401004000f1100c0582c2103c4294510b650369079160701080d90160f0000301000c3e108580c0c18520740140160340750b40040d1801c0b40003014002450010981d0010084841b0000a84189600401020720621055864030320142c0d41c102060300361822405003511518000c010b10901c0d000d11303c0401c00e00d0758405030600e03800d8030891402c001ca159183c0b01070710aa0103101c02880c41540120080b4580342d01d602d8040c19515070600340503c92690780401d04100010303041c00000300300c0c80e0048442e030541c0d030549541d450810307091000203070f81103082540d4070f00b080c00c0041103e80e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 537869784 1250 537868534 537868601
    0x60f0f080106121503020301020f07170403050a030507021207091e052a22030b070512060405090312040b06010201050928020103092f0f03120d111804 66
    0xc03010f1a100244c80040290444414041a08003a42640c8085910708080035050001e2074420b00482c22144142c00f40d2401340058032441c00000c0c001e03045649a940040d0080001d000150310082c6641a003552580005280c6074048c0d000311101070300d612801c0ca101100740356854042d450000140043c0c07a002000100d402c001007440315180354504159202a00702d84241e03085405000d4001c13064040920303103402c48034194003042c0c03100700344103000c51441405181159400101c0c081c0380851a5a84000c11004101c0140b0340141c0f0300040100c0c0c01d10480031110548202c1c8105e20403441c505141c1c00080c04c451008201c2d00c103950013000e0890307070071001695a076000000040114160384882c40102c015281c1010010845050142c4400c0b00d00d003072071040354502d01e50400306003601c410b2504010b40d6007d00c007a080d415400c080e510150701f008440080c40990440c01c2d005c02c401903d00b0740700304a6031013613249000b00c00e00a40c1010700ca1809004400e02014585420144809040c8092868 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 537871034 1250 537869784 537869807
    0xc0102060402090c0919050a05040612060b060f0a08042a1401052511011b06090f0f050607020607080f0610030b03120d0f060b0f0a030e0106060f0f080106 68
    0x1200f2a00018601d0011002102d20f4040041c01860300960340c0640704181410a0003000d100d00a181004540c4c0c0c1898440e0408648041e8014010132126403607030401060041030b400d400803420801d02100e0003188004080c2c8081568a8800525150601d2181c880682c2c503d40800035030a4001e00c03d0f4031007416203900b65003d03181010b410140e50f00c01a5064801c5140d0700c40c034140d03400702135030030b8600d245440c0d0384550041d205520000344900044071520440b603540400380d24140d2001000c110781d58403503019140301c0c984049064140d501d4071070369000c410f8402c64541c0d026100b04211554140074040e00150541040d141600348000e0f221213518000380140d0195068001031019503109402410840b80301506444103c690f00b5004261035012a030701e5070300e550600c96150801083c503c51042100c051100407401c19113480c041907210343c0045000020191900c0405810880c00c0c80369100a081701d4490840a03c02da400241030039504c000c1290500680d580104800c2d070f000b03406c1100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 537872284 1250 537871034 537871039
    0xf0307050d0b130209040308070305070e1e010905090a05040c06020303101502031b0303070914090c0901170901020a03050f040201140c0307080f040f05190e04150e0d110c0102060402 80
    0x480d99a400e0302483d01d00800030082c1d4004542000c0c0002c0c0740c0c0140065000303036410394041c801960740349825204030441300c0429400c00381d0480480040d6421440b8050012814541400007560701d600081f0050740580345041120ba07600c0601080161000f61440106800c2c000385055103804000c0300000ca04500c24000e9102c80b2124186180d442441110002d050080400c0d0075100c0514001c0d9803500126107400100315401c80104420703118007510302101d0001807180e40b85a80d0040481c040740c22001200f4148030891052b004200f6100060340c1c07050045030001610380000d2071004050b070302c3c0504850700403c085014800941d030721584104250100840c01640e8003844207200389944508107010300a1200812019072a240341002802107882c1121841407a0791104100701d01303c81028110400e03801c02060421898010208296000d03005030051040f0030903c201c0802510703004244182d5907000103001e103601d250404648243c060001d40200b256415040002c0d664585c09000a403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 537873534 1250 537872284 537872303
    0x18120a1707091e0902071b06050f04230d080a0311090904140f0f1f020c0d0e030307020406180510140405041e030f0305011d01031209230f0307050d 65
    0x21880b0f070391001074000805040c0030440d60740c1c03028180140c02c840084841650901750050020b50b141c400c00035902444401303081075250501d000d41e4031941d950b4107a0305030064170401c88892490356510049440c000d01170a404c07551190f000f180141210801d80d0915a286424400c400c00e907141c28502c258080e034404a20f01008022842880c81c0048405203000380788a0720171108036070a40030420070465648504d00c10402c034180030003d8140c0c01420105030316540320807a0105c0c5039200d042c1c00311000c100503040c0e0b4139200d02d03030b0045810b6a5042d080194170400880200c03810f04011b1180c503900c41c030031207440340c2c2980c1002c20000070800360b4072683c2e1017591180003107410700c900c41d038440c80104101044402981110316010f0014030410801c400468500b100000b00b6079803181107401080c5014000020030380c20f503a20101d600c22041018010000d00503004100e48180c0d01c001141004814480d050f80038103141004120b100e80c0c00a035020382c00180d0300300960f850300d1b0156050154080c0445 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 537874784 1250 537873534 537873569
    0x7080a03051b0a140703030809061501181208090319032102040801050103050706120e061915091b0903020f0603040816030e04052d18120a170709 64
    0x80c43c0000909015219040445154615034000101e144c1140e1107600c42401955030880000e44802040310001400e03d40c0d1515000a07600c0350500720880183d55804000c05500c55610b5104000e224504880c5040000b48101035890100203200341d8a0b40c3c0600026485a140d50080640c01b101c050003440d401400038054401400d501517038054002180208030640e560305095035180390354403680c008184201100c41c0c1441050013116103500e0100000c02083c0c5a141d00c0c0c80000b6103001e13280080d250307114482c00d81d00a040780305c180100820080804c00810100020420050b404008424011441070800041e10f80d03040d0040c08c03e504452541d103d0740c8a0030300b160f2900c2070a07070740c10f003070444000b04408058016581051141042d1403c1006590f5640b07042410044100000032501c0701c4c1d20602c0c41488103500b140d07480030204542d00303231b007000064090b450b10b00c03041c20380f407034401010070f00003003440c0d00400680401020254a00c4141426031011380078404502907501540c4240080c0d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 537876034 1250 537874784 537874837
    0x1409030a030f0e03010e0d0305100806010303080a0b0603040c2c16030908031e15180402010210090f06050f13151811120c012a020a0b03070207080a0305 67
    0x3e8450000e0040c0081c025442103c03505074440c61089481d402003464070010a12000000c84a081541c0300c0302c1c01420544d0070f41d00d00b522542c80c0280190191500c0c1c815403912501c80e0b001440c040c40c03041c010003110505080c0c00e0015019081e800314101c40c00e1f03044040117040507828140c0c20003030301e84c51042d48843c4c2c0d47c0c0403005094266006800316030008248034946180714031803043c1e070701e01031502c1e1810707143c0e01c100c200c044010800b034035881000b2052490903003038420a25608984140103d0701c800710046200f401740c1b08030640560b8140050516401070200d203000c2d00364044018a891101881c0c603000344080842441009042c088000070940c1020b0701c60352020011140040f03141c5071003426481c084582c486140b04841c0203041ca9201648000d0000426008109058440401141c0c01480d5907141400d260100308188401000807400b503280d00060101816580500b039a9038038100d00d000e13140c140164851420784d400103c0100c04294880d0540d0b10010044043e091041501c150 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 537877284 1250 537876034 537876047
    0xc0f05090f130c120b0d0209060402030a0b0a0909110607120c031101050f0619030b070507020301090209090a0b01080d140c011e0e0106080105040c1406070b15011409030a030f 77
    0xc401102d03c0c11010342c01051300003200442d4400070403418000154940207000d040400303480029003203000c190100340c0500c1c042c5c01660303001000d0000003820590041c00203c80c014603512410142d0354484802003440f0001c0500d0102040c1a5205464121240d4445581c0e8040c80380c10000c21000e2071411007010b110710440b00e00a03410400a01c039a0801c010b2044903000240d132220b21841c40d8440d41402c10400980c00d20459800841c0810311780e4500ca001c3d04d456100d95412645035603911120385c0140d4a605469004030010340040618003000d2605145890060701300f9402903005642440c0d8055004c91401d0703c20242080e00f581380c0d0705850200707000d054490907140c0500001307514041600d283d607000411441c140402445007276a03a16469080791790503176000e40003040d500c0c8107100c03040c5070f914641a00c8070040e080b02d00d88059500c03003405204059900054030550600040655a40484c00b480104c10096250b4606040800080e41e94600c0d440001c00b0b2040000700c629030540946c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 537878534 1250 537877284 537877309
    0x602101404030e19060f0806010f0215100302090f040209100b04090f090605040506040b07051804150305250608060d060905070f08010204030c060311160804050619030c0f05090f 78
    0x34855004662642005040500341b5100340340054081000108558414000c00840466540182c2880184480101d1b000a0300501400f030b034008040c0e0000050b00e90300100c52081c01c548045003a2420607204100b00050090500103488000316820701c580410f40040f1400c8841500c0006503d9040707080c004041c00e12a8400b82850b03181c81d0410040c000d02044440c810341c0714816040713150780c41040644082c01020200f9002501264040307040e41450b5020b25489002100d107071103250b58035902e22f45050540c07030b40958803201003c00c0018154a0000709000703031000382810301d2075141c5100407503040c4180100140c101c07516164084284107061001d040541446c0003d00f54540d11807072143d001c2c1d0b129100458810125400000d003880c400c1c400c685201007940702e418601a44801e01d000c0743c1c40390900035240e85404110009a981c3c1c0c80004118180d00d082058400130102c50b030140484410203440414413a01c07a028a05030359001081b9401084102d40004002001d0400b0401414480 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 537879784 1250 537878534 537878569
    0x18030a0816031704050604030e01090f03020d1a070203041401030209010f120e0618251203020102090607030908060901050118090602041a03091b10080c090301090c0602101404030e 79
    0x43d82484140000481c9992143e1300944805e402080c81400440c0c0f410418490300c3c900d0540940f00b0720061602d0041094545c2c054001c268502441b02c54014421000b550642c0243c0d000040802443c004580000407006c0c1c01d0804500740707088000042d10039840c3e19017250400c00b031044614620340541e40540c0300c0560403421240d00b0314103100b040501c00e41004c601400d85c840c000041c4041030382c00d00703d0501d048448851109061800c01c0002240c50880c40403425950288601026620b400000d08070b640d00998641360000d141a02181c24560041c00408260b41841e005000c0010702c0e4550404400b00b140000510070024200b1500074040c94000c058400030480c442208000407030040c43c0030702d03645016155800c0800e941004840c81c00040075402c060101600708100f030040d02707900e5001245030405440c201900000070708464030365500b22880b090301d44061081590401c00e080d01100c071200204140b10076521180e5a070b4a00600c0142003011609400e401500c944000403280b4254 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 537881034 1250 537879784 537879827
    0xc010e0604030f03060b16020f030f0114071e080619091a1221070c0b0a020a0506070302041d0a090803040614060409030c020103090804081218030a081603 68
    0x2882c0040c038100ca034020303660019003060300218000000108407640540c0d0810040305070115079080c801e00f12508500717a03034580900b001c082c049400038018845514100b0005c80510715008030054007035102c540d0711050350040b1901b80100307180c2144050b500140700300d03490b592654241001c20100d100c030f50000381040b410000300700202c04528200c0d0b1080d074401c8a104a011080303c401c103684242c84507001d001014091032a400481030040246201801004c4215055459603400016540811401401a840f103180e040a01c24203100d81d0340c21049928003540307000d240101c1b025000c6c240341c02c80881e1420305008507004203e140c0c04406901e9124500e01c0d03c9180609001008003042c07005140c550b8000e200240d05442e10b88644107215a15858a00990205800443c010860350504581404041002058501c02001070503c100d400143e850745d10042404049507406203079004500a0348030500c5100081d26110954805807132840200d03080352040c6c1130450b448461200c0740802e803200b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 537882284 1250 537881034 537881041
    0x1092003281b0c05010e01090c0e04050304051f030c030e120c030d05040819081902070c0e130203190c0e0c0f1b06060a0302030d120b0301060608011a0c0309060c010e06 74
    0x80029100f2640ca0183e0000c00c0801000003003582a00d9001d1002004241201c07014400c803030403403110542050103681100e0070b103a1a01d000ca00304a0080141c401510101c2070b12011042e414081c00c1c03100540d03403800348040c203588800c6607a9124032000504a141000c22070380034001041064601ca880b06c1c00c401c0c00242014108882d09501c20040c0c070501c0c02c6d0443c2da00e10810301500d00b0364000d07a0302c090700219801c803040c070100007504609801c4401c0e198060000607200c60f00b06e80c06028010141d002000b892540c41094908410940d0040d401c11920400d00c001c10000c0a60714200c3d40280259202e0f6620180d40d10424804c0042c0480040c901148280060410903119804a210b0340211000e940b54202000b45072112803000a46c50352250748264101807003030246a02c41103d01130302240c4001d903440040d09403622500700da00040d01030f90040041482000c8032100c14940380907080d103040c8810100d542c480c41070007001405402c0c00a44038112400940c002e0586031301c6c41e8103440403801c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 537883534 1250 537882284 537882287
    0x180a050f0418230607140a0c021c0821040b0606070201020a05030715060b0c0714060f041e0605070c090504020f030604141b22060e01092003281b 64
    0x45070500070200c40e10411001070352046c0180ca045200220071050a810203080c000c044440642200c070480e0421002d03d502c07170350300031a55984180248601c0b803c43d00c801441001c09203d281c41840241060031103018403000c20382e0707501905d070009015070f03d455940360540010b030320740003400c3d00c0104a4440090300f00180f001080880c0b82d9002105814480c8035070301c48054030503024209807065103411040c410800c01030315190310320071a0b002420345030030084505110180341c6c1080e4040250005207807154519800d107180f01070003400d581d090084c20000c40b500d540d81654981c1c0105010207541d58082070075551600107000c200700c2c0003000c0354054607080c5070001d440d146001040030107109000c148813441650025120000501a2251b00240450303d0301041400d8824002154a0303a07a240c0464141406504070b4040c040200010411000030b03105144ca4510103041401c1d40c980500074480f00c52140c84000c2409020141d0b0481c20704c0f5204214001013802900f02901402046000900c29 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 537884784 1250 537883534 537883583
    0x120c07141b010305090607030c090f0b040806070516080901020a060c0c02040605221802030d0207061206032301110408160f0b091002070b03010b180a050f0418 70
    0x114403096140e4004072441c0043d402d0350020385215000e90449000100d12601c242c0c40128410240e181c00b203103042d504c07003102c60381082680166078840000202131201d0201008459008901c1e80f805500c2e00240345500301040d07401250080c081a03002820140582c820460851700c2078000300204800444090040c05c1340d50030a8049000da400c001d0006002d00d0403100980390500e8003200390000c01141c00c1050010301c54080381c031400c02943e03a0b07800b000d030318100181075081c1078640041000343c0c20554081c00381d58a980601301c1c8581001410710015603c8610f10312185944c00303005554803544801c05016102859941c08002804a400545190b00180034000d2800b40c841c090200d54035080a810480c100c1e01484404010401c017440e01c5090403c414080b41d85a4070640d0a41c644902d40001c499000b1392117a9035407440841c182d204181c1c54402e40c00d494004071500401c484c500008030f503070741c80f628510328844e603610b124044411102c100e03d54030060740160010100f0002c11440b401c0c4c3c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 537886034 1250 537884784 537884803
    0xc0309050402120604230a0b030a050a0605040b010e040c1703160804151403060108040c0f0f1401050909150402070c09020714190b070302070b090d0f14120c0714 71
    0x203179003489424506030b0840c8003094441d0000e15080c000079a1103102c003501030121425040d4061103202c3c12040426424020550001c0c4a42c0000c03543c0e08041c1444100c085047c0c0040000503002001c2c400000e4148460341c00b29400517100920412120026a00318050004a100510410030003002000a00001441506d5240c0701c2d0304102c009500040350b00e00c0c00340311241d481c0740003080441e903d50b002d814140e83c820300c20328490000d15282c40d06030001c1c0d0400c0d4807030817889940002c18080081c2c01b0030700954024003880c02c182800e000340b00040348054041c1c918856803811000c40c503180e0f110380d0100c0e108a5004004401c0d01c41d61401104000d40c030008003524186a0781155000340c15001c21004500602e1800950142415440e02c61038100041c0074a4140350b4200318600000f1056041e55200302141005450b4910300349070081c042c00b04404000040010f40002c0003601080b5505803007904c00c4c005598451a074410b651481c05202d40c007c060b0000c070803da146240d034000000c8450381c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 537887284 1250 537886034 537886039
    0x80309130608061608130309051e031c0914030d030f23042013020901123308030f0c0313080d090503030906040603090c0302100c210f0c03090504021206 67
    0x41703581c84201a42140260316001000100c1c040c6c030400540c5030051902c81e552807644201d020100301c071400a1329008100300001016041481740307540158222604900500c0f005880686271444540069218040c0140c0c11080c513a44e01e510300744041d46940310301c0c2c10320340840e00040b040307002c8008c0361305140c401c5600b10781d89a4003c6940040038088511103403840d4000d80300c8a030b00c142c00c510500203900040c01030307410000c10441c00540f03d0070702d010702c0024200c40300482c0c5a1000c40c200041030f8038040344070002810511241005034170000401c460662220000e940c1d03c40c11444072180c02d43c8280d00c2e500a46850b521008a20700c7d001007a90306414980f600c551107605c0d911010325480e4020040390a510000a000c10482c1c0c6020340c00400c02c65209000740c0c2046901d903400a42c0150b5040f0504002421001c01c1c0d108011aa14400c043c507482a006014003100451f4014558408501710904002e0160017200030075020f4040c0e034000c0d00c0010400c1d034a90f07100d40628894110102e07626407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 537888534 1250 537887284 537887297
    0xc060f1506030204031e050307081606050c09030c0d03020714060903061509130206121e07020102030a15050d02211c03060504020a140c1207050f0105010f0803091306080616 76
    0x4204142c5088402c0380306c1e9100000e1428046507480380001500900004d00010303910342000e000188142c480c16100710184a070840d01c9601403405c1c0751170640400d21240c0129000c11900c004603400064920440b40380030410740000115501107005030081140c540e415120314428407030716030f000881605500c0c1080e0f43c014110303a282080100c4070303081e01c07001079044a001c02104001e0072503041d820b90b20180c149107104416130b084298114404007160b480c0010703517001c410f002400c8190300030705c0748070700c1600c020b041c48504080000e0f10307245408030000c0c45001c00c40c51412101d511103552541a01c504420317034501c0084110404010482010f100000900d001001700d2107180074401e4800a9030070765101c0e603110258080214440d40803607001b8000d803060707801041002c8103100c02008418441c0c009400e24052070b2440341e007943c0301a001116002c0210900f03105440000040d9440004103c40252890a0300d80c5408001d100c01d401048880c0140010450001c80a51003e00c10b220b45603250b1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 537889784 1250 537888534 537888563
    0x40203060a08012313120e04110d05041b0509010b0711190816181a03031c0506040203010e070c08040f080607020607030e03090d0602120130030c060f150603020403 72
    0x185114060041c0b851b403c07079903a07889540c850035414940013000b42c00018264031545040c80a43c01000c050034045860704200010401140d40400d80411310007000b2100c00d081c42d00040d07030180b05010302c08c540c6c00d000c1112414040e12150130512100050800b1941400b81110341208a00310300038400948034444156807800d09486030036023141c22154045d900b128007002c000004d000c0c2e405411881f842e00b80c3c0000000d0b6020302c028010b801841500d5125400c9000300310b002c4da41c0042c2014812481440100000300c801762107170f6071081c42c92070300041840c420b1801c0d21850080e03800c1403820541d6035401180b0360b040061138600808242d001c888003a9a0008110700340e0700c0c4680e5031041a0400d022001850519122110b0190f00c18900541448403442040e11a82c600741c0c004040d203200c6100401b144e4416039000c0b8402e6044603800515268240c40181100520450040130349a450030307030f0030740c4079801d40c13050310200080c100c1405825550a001800f0b0340003800151070303012416080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 537891034 1250 537889784 537889801
    0x207080309070506031608100810140612071a070804090c0e0301050124030f050703050417030c121314013303030f02070b1603080a09020f040203060a080123 69
    0x2520700c50f804081086120304c80304d84044032040c1028103c10a0124008c078007284105090181070201141d01c1c2000a00c407030161140145440e002d0121801519100d01940071090003259242c03c1e5428090185101c820301c42e9422058800c0d0a0081c00c0b0807804500440c3d140c21941000301641030580c1d80f00360140e100000c041c00c80e503003031090340460400046c17108559150030918100d035508a040000b0108000c950407025910102c43d1070300081d40d1034041004110150848800d01d104168400e4150b262042d041245441054140f0295001d1580001c020141c41d00c54124840c5e4419103107944601c0080b03100b4064404401009207080c00044c031520801040181d54030951074403c8054601c5103141c4007624810a000b180d17400b1402515404101c1c2915a0024a2105240140080101064180180728402c0a0300326101c06081400c000c000d6036600030404101c0b24201d40050385c07030b111540081d210606642c003400540d405d080c4401701a46010b80340100703e082c120580c028070b690b034894 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 537892284 1250 537891034 537891037
    0x20f1804021c0c0c0b010801050103050d080408181f03050f010b0f1b010204080718150e150307081516050705060a181406090106270906020405040207080309070506 72
    0x744844110402d040c0c024480d60b904080c041c940142481c980ba08460703100c00003d0082600300e0f039240ea442e08010402c0006c200003a041e0702c0b0301c0e03103046045401c269a4141c02c5206441a0701107c2022a0b2200e1880d540d10140ba1010001c41a002c0000306203180040c002c2c00e1300700c9000358010001000002c180f80b5001c11a109001d041c2840b914260180741c000c0c0a9190308070f1074800d259800d22000c0307160341c1e0400ca400040c0006c1561505041c1d4401205130540b841e16990054088001c5000c00c0000c0214007525002442d00002840703403022440860302c1c224443d8050b80d01d5114100490383c1c50306c0482800e601801512161048900400c0000d507614401e021001700254000b10010701e030210301c1e5120114100c0c04130900ca040d19800d446034000800c010074642c0050704000700384219103c1c00d12500000705545805011450b0500891240041036510320f502c41507103410040c4200002941107502070302004204640b5034695082c80641030b002200c040e1058824018049603501c1e0000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 537893534 1250 537892284 537892297
    0x30c111e09090f0a1b030813030b0a02180f01030e100b011e0c170f040b0c0f0a0c060c03020c060414130504150209060714060a150f0b030613020f180402 67
    0x43c0140311001c1e0590350503552a0030085034149000c0944800303c0000d540354010f010b060032045081c0c05803410360600390000e4202400d012066032042040c03246001c1d42d5540c180350b0407400c441c440d40722000040140e000e4009640e001070f450181e4501c04401803441e911580e1003a00a9a070700c50030201e06a0f4013031849a0039491740c404a011585a480000c20442480060f139503854101820a00450407040c02900113800c80540c0d58800706014403800e40410100c240c400c0c0c29001000c5005840c0c41d20a0f0004007401b0702000c220080c045181814000c0bc40d160700c0180140c40785a0395696205c0e0744065034540a002880b0f01400c0a001038822845e0040340d00913078102c600740c110401080c00e054001d6200030142c0750010001e004050219107550050407000200030b0140643e45000321043e401c680003004c1540900005000a00c44103811130008400d840114508035601d031184000580c05000041c401c0515500010750745005403001d038003400e207620700842c684221203130304d8003044142d00446 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 537894784 1250 537893534 537893563
    0x70503030f030a050c041d010e0c070b070f0e1f03110a090b0702041b030501090e0312040209091906020c100b030c1302041205160602010513030c111e0909 68
    0x600203d035481c81d440c0d0001d60401090300c80d00d8641a43c3c0c80503003103460501100f83c281c580742000100320080138031040c2c0e0303031001041001d203140091341d44d00c1c2d81c511517014045008110781ca14040d4401409034801d4148500000d00e0f000070512441800310117440002440310000e8100400e22104070b10310810350301071240036200c005209081c241000205c0e04240c90991f80f081d1a8000501184c85c01e0f01c1c01d004124556501240e550304101608040d100902140e603810f0340200008001c01203010501c0d500540d049450809946a104600e45070820440d0f4a40c0016000b031400010010f0680c01840c90f0b90180303040e81c00d0703501c10100010894052841d0650590844007858000c0d1401d017481d8410b030038a0050040c24643c58545110a1000103107045400d5401418200c005440c4501d400c0c00414880c402444145442501654032103c0940003c061207214000d800c104600300d1102156900c1c05000b03042c203030308840a140d6490708540041805054200045a40b00c0c1c4003045008605615 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 537896034 1250 537894784 537894787
    0x302060705030615030106030504050c03030f070201050c0a080a020604110f06120406140a0e0c06090a030f15050c0415020607090b130f06020105070212040305060406090f0506010314070503030f 85
    0x120002074032981d00042c00c00382d100302016100c2021080d14400f641c041c010a685c00a00c91030b06150036860705664111242c0319610a0200403c4c3c0354413803048840c01d980c286044c98940744008440c0340b5201031568000c00d24100403495806440d400100300d80300d01d00840000c280150342c5801c0c040c0c603455203011039420002c10020b0607550044c002c4500e4000b44242c01c00203940b4070804611402001c140d50161009403181c2a500b5102000c01a00d40d0410085415628110794800041d20304032181c803004118041000c240e1041c07002943d0130f000c19042c8a803081c003441c906200380a0690b40302d405000e01113102900280c041c1840060000d20401194a420300305904007454a101c0c0d411194001001d0201030001045002c0c601c1c00b1040100060740020400341014100682030800e00c410200c081c24050104001103400000c5807a00315811400018820a841c107000109101481001d0018480c400c00002001510f502607040005508203031420300b900d610030980c40b88035026508201090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 537897284 1250 537896034 537896041
    0x60a0c03120c1b0203031215010f08060303030a0c09030b07030f0501060305160806030c12030a0201290d031407050c011e080402091f0b09030d030903050a20101e0207030206 76
    0x1903031001c42ea030f281d00041c2101e0511f8440c0540544d440c4003142e1141003011a24000c0c0c20300e58200030450b030001400d0030110041e1a022020139070f03a002c000c015072a21519108080070582c01100d940001e907030808110100380c80c1181010b40505450740f007040d07506151200029169100748241703400b41723810321143c00050310281021034007500003404a90b894042e0801c8004aa40c0d00720140d80040c690202460f111522180068219813404c2250090716001c00e1070340c4c0e03e01c0d2500c030360040d03041012504050111918242251030710017000c8880c00c65a000580c03082030000009404586c158240d980c0042c0b210f41d5401050751707008026601001c14240f801107001850302151141d403001c4e0070300d0850b0009400020400d2074080650180304401e0b000135050b40c040c1810b00c403203c0d11240c80c2c00c041c0102d807055500140705220ba09039840421142011a410040e4402a0130000c5072054084520780740c0d80c100c5140042c0309141061f040460b880d481849280c01900946100a4041d0040d0604e41d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 537898534 1250 537897284 537897317
    0x3021c060e2a04030f05011407050a0507060b090106021606030b0f06091203121005010e0105030c16051c1b0b16031b1706030a11010c0f02060a0c03120c 67
    0x5285a040002d0110b14800c10040464000190005502450601c401c40c5020b05003e42110703808084602c1c1803090104009804d904481150015500d500d800d503600c3c1024180040140840748405a1151900d800050082e03070004101c00c0c1010a510450040e0f6903403501038045030407605040385c1015208921482c1031400b080a40174130b50000d408000c82e440042e01e050b00310b501040106031101060002e000c0b22410580551000c1d20085c2001c5112181360b0001810601004207070b090034882c0002c0000d000c1007200f25100103030303600c40b007240c90782d0381100010144403a00c9290a0001020100f6804401494084e191122504850b0390101c503280e407031070404801160049101815203036000c802d00650130400e10310f0840d480b9500d400f0422250f403008020030300e000d000306110364440e41100011800071141450030100034207002d01075101e140740400c2c0650240001075031001c0c01244040c0325541007503c540030644a81c0e11800d221601960002c00ca0368900c65490016441e85501001807 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 537899784 1250 537898534 537898561
    0x2091008160206220807020a090e0f190605040f02090c0414010c02060d0b061b03070b090c03060a0b03070302040207080d0507090f12020a080105042f090c03040309031203021c060e 79
    0x131303014915141c03609080d5004640038034042c1d400507600599603445110844024043d544642d01040c2c040d110000d2200b81030301000100c12405409160380744041001c10540d12841e86215134090089411898400310b030424503005440740710130b105a468102415913210f1300301210000d5004198070704005841a0340002416019180d5401200c01c1203e100540017190a00c3e0032481407000860f0742d00706624240341c8012024124020990101c001703010305650100308030394041041800051081f0100e0000703451324100754806900103100146040911102d4001004c80620900b014050f580ba0072a0455040100f8856102c0c52100e00d030081c070881c40c08007468581c480c001414001e10301d486d101e0181c00c480d42658212822140020207218002c122400c16040402c605502c414105d084000304211010040859402da4800000a01010b016029050207103800854145c00c0e404000c1c0003030005d44c003035880e0000011600f90005103000b6280a800309036000c09402540300d8035030042c50301c000d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 537901034 1250 537899784 537899851
    0x114070b04140a05010905151e04240518060c0d02220605090103060e1e0c13030507210c0902090d0206030a06060e15070f0602091008160206 62
    0x24800e090854020402c0b0800c16110854098400041ea80e03102e0f26000f4a80041b8500e0038088088420030407810152046483c103c0002c640090821030b0748900c4d014070014420005100b410f58000c452054110042e44902e102ea034100e0f0710007801104540c1d51540c0c400c0c045405610020040100302c164490540240810611140d00302a00859100c160320f429880c0340c00000005001080142040d81d00d0301511009007600c0c081d4150724100780c4446030784404882e842ca4001d8400101050100300307984100d9554415000280114545900d415a1540c00510030903144a010034410b40f0304180042142c88030740c0d4040c0101440510300034590780a500091403295012040f0b00c00e110158969100540c4190400080012843c1c2001d6015054403d000111801084040680f1910000b80303400c1b6250303071390807400d883d0301d81b8510300c1d0002c06803060914103500805500081c182c01a0440c1c0351501030440c20100588030024003c04a1b80e4450442e02c00208896484025100016a0410104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 537902284 1250 537901034 537901043
    0x3070c0c03020603010b030f0a060602032b02040e010f08010c02030901030c020a0606140103230a1e09050114160207060e0a03051204030515040809040f092406050114070b04 76
    0x340156a80c00041240e0003d80c400400082c00000b0028219034048003070f0b511603610307002000325505060000350b032400340306c41c4020744440305524443c081c041c40303521194941c261142503541b81e0f25000003650261083c0706103c102150103c3c00b040964040c010074003041155402141401c40d240011800391124849282c154041c0501d5100404c8403809130402038410706000324485e0181000060480d040144004210381e0b10720884550040c1c140103440e0045010790317001c00d01c68000303100100c0045540e2003074001149807905a1003000741c1900100008511542c005070789558590f0401a4000c460ba04200140c1140800340200340c00b5068400c8002000b5054030301e61a1250b44940c50a482107213108010600402c1c104100213040118070f41c000c40701500107500c0d00b0295600c0116010310400c05101c1ea031940501401d03544030754010b07061180c000d0348602003044d8005c0e1050016100403554001c45050032008181540141921013074424080384d01c1d0700d8070203140c07680406448040d00845 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 537903534 1250 537902284 537902303
    0x31a13020d0c03080703080405121c0506210a020103050c0c190501150e090606030102070308011716090b0f1507030c0f06090b0a1505090103110102011e0b0a0902030c03070c 76
    0x8542000043c5c014a842601d4545e280e00389400c2903450b003c1601d1010201a03002c000720f0903c00c001c003c030303c03120039603030403010440345c946c100050b021003180d040100e1030090190ad2903680075000261818514007c3e281080f980e104c0000340354441c481e4124501c17450b032115411403514040800c07906190750240380001350b002c00800f41d6507586405640541760804211050106094080c0040c0e60081c030114001c61901e4050f603400f40000380c05120b483c0721303c0524494404000c601b80540c0e940e410031000c140c00290f460b01c40940080074242c403514000d038540600a103260030850b51443d03440004400043c2004ca15550032108034001100440b000144a10400005a021302400019500c240d050082510302071003500e0854040780026810968400400c211648a02c1407040c1500d070400150301032a0603410041c2d01401013107403444003403c0114203480811f22194418401c00c01c007180c03005591a5584403400a038041611100080401040415000b0f806108480c80503032181c014103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 537904784 1250 537903534 537903539
    0xa020a050f0a09240503010509060403180902030703020a030b1005040b07020103090b0106090314010902011706041527020f04300506040c05030a11092a04031a13020d0c 74
    0x1c805644c51078131003035400403030702400c1c542000f04011003101408090740208410320b001c0d1001507907504003038400307000c0c0190b001000b04104040800e003070140003501703010740d56030500e003800600951140710710700006894000c0e40d81243c58400d0317401120305903980d0340900340b0341803107800e4420f43d119543c202d0516a5034404100090f045071140c6001342580e48805003100d29508291003115814415000d07940d15048200c801070f80c0203613643c107900d6820109071401d5a0389102080003400c017004001e81104a104000a0340c201982c90540008000c500c0724040554503260344041c0e0048110580610a05000c240b01c95901030007404050004a0480c440035003a564446a024850360410790301900810104070a000c001c040c00401000190001c04094000351120180700389203540c0303184185038240114020710448103842c00c07215030071a400648684001c400307021a034058401107902c0102e4414407107082082d101d110348a2128010f00c2c414480d00c1d41d080003040380031840100d4540302c808401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 537906034 1250 537904784 537904799
    0x100c02180702161503050c07052a090411010905060403110d11100c02011e080a0f021306050c0708030c030d0b01050f120a05010819061d030a05030115020a020a050f0a 73
    0x5400c02040d12802c2008010380c2103500905490004103c000a06008c0110800150f00098680d03083e81d0080b40c480070340c1c8030040c240d81501d20075100311030348002e0050a03c801d01903104a902840740098a59009450f600c030700b442440d01031840f002d8a09486031071400e4450801e01480d1003198425040805032501c0d03800000c0c040320702926410000741594142c41d0455800a001c44a405000c518031400408801d00040c511a030040001665544850300c4e050041c0141d016207a852081604102d2496100d0b5802009604030079002602849020030006400d4008000c440e4025411409985005481d8801c1e101030440c070100e0604000c000c01000024405040140c01c00c426074036101d40b2581041c2d8110710a580060300b01200c1c0c1d40003007005075040304904a04425856100102003a8582c03c01c1e10108039098580c1d00b903113140000581000000d51080c004c40c16280060040c50050b100710703900700e03503c80010f080250000e4440703405005a184c80041241c4643d001805001f002d502c5161 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 537907284 1250 537906034 537906073
    0x643170d15090e070e2e0602010e16030302060c0703050c1c0f0f0207120c05090703050712060303050f1c0f0209030c030c0609043305100c02180702 65
    0x1914840201440c2050010507554090855003e60040c020022903080c986482046940600001e0030601c80310800a007001c910310540b08192006607040c8060703555004040d02800c48181c0c2e0301d9403801a150381406001444141800b83c1e605540100315035a1035010005d039550185000f42c4c18080e00307008004060b10100a003034107680b0030650b2500036541111000d080d50084003051000e10000d8002920311960004040e0704581908900010300c091070f09229640140c2501b000f13400840c01e001300311606805802c6039005d1125551800940c02c45801008200d03403003400000e0019604020303010390303401d41402604c44884001d12103a103d07410f481020044504030f04044600d1600800c04541614080c8444080f05509a0160041c1043e403400a81e4034030400c0d04031307072086648295011025403a03803a001a52011020280c110b410f03018200048258180b142504c102006c03441c2190007845a140c4011055000d03001619180790f105000030340c18801400031046220300760b1082c208114116 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 537908534 1250 537907284 537907301
    0x30f0406031b030c0f0e01140c0309121b01031104150905040507030e061303111504060506010e0105070201030903140708030907050307050a0e0402040b0643170d 71
    0xc400080b066080016003200c0c50b8048240070500d450500c2c42048160000c0017a08520060f16000e48150003001c01603c89040000400e4880c1c2e9003c50101110f600020007800c3c00801200e0503401c0d00001c2c3c00140e5108d0501e00f65189a501041c082d800e1940030b9000b503041b44420518550520740c986034000a03009042d40c4000008100040c1005542010f1240c6e64001c0041d10341840010900700d0b180e42d4841d0040c0020140382c84400c105014544103180406c0c00007103000968440d64001000485042c009640980c0c5040c90103011803a03a43c020346c107c58407454186c50325030500440790019070041900c0c1c0c0054060020244100c0b006280c924020124107208902d02500c3c0e091190031945801d40715000603000b0b030f01001061045030303103840401d0102c0c0d5082132215040d954600c041000390840d803e840d90440c2020686044098007500d01000c40c5002d420a403c117550032000c580c50704440c9240c07458280c0c00221400000c244544c41610130b03030802e1440c8030b06d00080a0301d01001c486804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 537909784 1250 537908534 537908537
    0x50423060a0f0216021c08030702060702100203070e010507210c050c0907020c1e040510140102010605060306060a140a050a18031505090f070b09040605010305010b071103030f0406 79
    0x84080101d0021944035042410801ca102141420600408120b22039900800030b80b203842c04a14000d2038200f00004060055446242191282085480a942e83c48181c41500260052144402e207005083c42524840c00d01c6541b2004080742e08401500c16a005202c20b41e022072190450350543e0343c591051003171307080d240e81d115402c44400c1d040080c00c00340415001440b401c0ca036010b100c20503600041c801d43e0380f6070855581190034580074030584c0c4002060030040e049403c1204104802d140300717000500300da256160503900c02c048800128200d81103805003035801102031010400c14200500075250040d401c2c2440a18500c00c480c42e0b00c0141c01546074500003a0000500c110041c0c3e104186949215547c240d80603645d055542c1c00020503003400071048203550740e000040803941d0400c130f0180031035030440a44100030703100c06903030000d40d0148003928021401d02c00006615482482041d0403a0584d014490130020307250360b214840030904d440a070f81844140710f210b4085d098500104001c1c0801d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 537911034 1250 537909784 537909793
    0x806071d0102031608090f060403020307210c0e01090f0c08040818041802030c0d1101030c0e10030f0e0a03050f030606040f090912260c040b0c03121f09050423 70
    0x1b180130820841c20301c0320510f0041d10244001c00c0107031000100360003510031030b2071180d54001241100603140b2503100f1740506074218080001441c089280a420f060382c01040c800d22410918a039040242c42c01d140c03030400054000300c00100072400034405011005001c550581001d200300002600740c0350602c4594800f8108460352104628041003910148202035a0105004d803040d11010111221055440c0c141602c5451000c400d61047d00d440e01410360040034102039170030084000b8020708800c1c54442c00c0601d410010800c40500003a20100c1a50681d0f656281c141d0030100711940c1d030030281410390031203801d010101d40c0c00034559005c4080c162903803000400700940d090020000c03099641c94414004c4204491f070640c580e04004600d11308250000b181c8035101d015550819108035400f0310a00c00000c0f5140301d41d03100100003804a44441e0286114030740764140382c1c9a258032040410742403a20030300070805ca143c00940201c3d6010340190000c44880d09107032007800d40340d03a0713080614a80741c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 537912284 1250 537911034 537911047
    0x5011409040203120d27020a03030315170a030206060a05030c12031e0706150b09040507020705060a23040f0e1008031c0c0e030601060507062403020a0806071d0102031608 75
    0x3400941c01b41c0c910700700001d102188503801145001d001800041c007019120510310140041c034000071402480e49202d002040c1030f2105503213464406012048006028040c00314074036140c1281c440c03042c1c0340b0003005000c1c0560000c081042c1c0a2850840c5551400180f0a41e01d03428150724000d445070321000c0705d03507a840c00d052405c032044480280c41c00f2200c80300e03c1005e04c591023002c0d080d9040000d06039030004860300c0340d103c10380c07078a10701d94481076101100040240340740781e01c840c1c2000042e07520010034403058540071710141940074030b00504841c0171030302d4001c1001180350f01ca07058220988404030400681c81e42040d506503844040211005020800712800714107884c401c01600c03c0041c50214250282800042c5e00c82c90107100d080100040841c2840038002d07164010701940302c11050818004e084501c07200340800640c03200340e1245a04110001c0c0e0702002150292250751140e0b6a6200741068080d4180f181071070241140c110f100501c1800480400031b502030710b00c58052810a40c4412 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 537913534 1250 537912284 537912311
    0x20c0f011503021906080103080c030d1a130209060a23030103060c0f0201020918070216080a050114040c03230f010b120f060c0a0c02150d0506010305011409040203120d 74
    0x111013403246260340d02c5a80c1002410340c8802a207065a521908040e610710902000a246010b100420071015107005528610118068000c486d49001564101d55490030906003204900400d036031207411410401009603050704c60800310a0001c0c0703101c00c8150030001301c0502c50040d0000d8000711202a6124001410290080205000c40c0c034240700035071a09041d040404c604040e9065400c00f01200e04002c07a1a181c02884500b540003030781c80c0c0d80c050346070340e4003507440c0d13a0500700005a900713510742000503a40041502c070b124400c5400c1104054a50315643d42c0ca07910f104081c1405002141402100c5102103081c484000003407412400807500300b500108112004c1100e42442c2e403194000503404101e000049801e03a48000070055080d150042400c041c4d40d0300242580081d030010100030405940c070381040140001b28444102040255038003801541183e100b801031006110280038801c0c042d245c100081a40981b000e4280c44080701c3e44446580c40d44c125020a100450b100c1120782c1340031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 537914784 1250 537913534 537913549
    0x80d0209030c040e0316030207211a060108010b0913090501090614130b18030a1101050a061d04050f010609060e060303190804240506040e070e060103020c0f01150302 73
    0x2c0c5001c88080004c5014005401d43d00d12880c0c000c581003100b00380c100c0d0300340340c000c2c405040108016191240340048034014404100c1036040121100c04605030002c28400c604008144140410f8541001d26401d05510a1594200d0101c03158840382c08030703440075040710754091054000c0c0703e4800440d002c1c6440c80c025041d0343c06691081c4030350101c9410421410440300400c004c40b60010000800b60304e4540844078236100044c2d0008082c0b00005011a003154041034030007140c4400c038020031254907001ca441c0b042d152144968268001e4455051142e074000081c01908588202e007155030350560310300c00d40d0075075070141d1008014903541c16040120445100300e86511001c1200618684011503800c060900140249101002050300002e402c01c000c081740c01407401c8140914030842c0f0314108841c0042c0100301c4040340079504000c0160031010000130100309441600e05030901d540d5843c0011030003500b1030041d022031489841c0c0311079103c030340170304c0389018138440f409180d040d1508500502900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 537916034 1250 537914784 537914803
    0xf06030c0e0702060601050f160b0f100602121e1b0106140105030f01060c051203041b05011806180b0c030d05340309081c0605010309020d0609020a03080d020903 71
    0x25501304104008143c1ea00004451000341c5080c0f00d04d44a14041d440c000c419083c02800400b07028031913041c0260700d2603a0740503c0c0715003c4082d92580041e00c1d0003080f6103c42a41c1360b02d80c030801003405100d8004070064000300b5001145080a418201c42400601401039a8401c400d1141d54840042c4000c0c480041c801c0111301e4282002451410720b401251500d000510410702008480e0700c07607504105d000d02080c500104510b124903100e0501f07081c10b1041500c503419040b607000d100e000026295018840c80307150760514125110016290030001d8420345480f041403c0d05076240000800c5006003007000e4000303400d51200a41e100e40c0f8000e1140202c27803002c3d22817026103202000301a40481503a00d883c030080140d00c41c03440c80e900040e03010350240090710ba0080a07484045455290780031000920410f03046600ba0a1014503074800c0150200c038503845000c4d41044c076100b45500828006d402c29510030b44013030702040103142e4a448544c2640c0000c0c07030071709405800207250506403400b00040c00c40d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 537917284 1250 537916034 537916037
    0x27010f05040f030605070c08070c061d1f02030c03040305010501050301050109110f0a02010207021305160831080301081006080607080402091e0106050d060f0501020309060c010f06030c0e07 83
    0x18040c1081d201c0c1d9240a80c2d44001003070541c46000003494240b0035480703012240e6111002644920300f030300c1d101e202c003203040c081c85001440001c000d04803c140c91404140178a00540300040d4102404500030100d03900c4e44521007588400c125442c20740b42c04200810086004000000712035040108044c00c1d40e0701a88107400481c2400b82c4e10308003c03074820451f010000f40c02c0b8540d5071054405002c0c2d01a00429401960011032000b8580d01245542c00842c858000a01040b081511005056841c0d60042d90642441c0c8008030b01c00c9050011906800000c4001d503d007518500d90301e0351600b10a6200340c2100c0110b400c096800024038075a4060200903100c03880c0544a2858100d074010080302c4001c001a1090b00c0c0b0030040b03603460554010804c01c00301200f145000b0356845403c05481d641c002d02e0b00071946850160001038104903400060180c41c8168041d502d040c1882d020400d05800c850403c00842d560781d0ba007103400c600c89110f603030001e44c03182004950461400e4404810004010080e80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 537918534 1250 537917284 537917287
    0x1090c0905040b010e10230307020c030115060c110607030f0807020715050f160602091c0209010e042906011101020a090e10050a08010509160308030c07060227010f05 73
    0x92903a0060b41c50300380040700780c074143c1881c607000380200c41071b40681d105401f0040e44521f1013002080118001d621039141074089801d402e20100905089400959a5001141c207496061189604c1110884010360090360550288540c043c0010348a41c45641c084020680d035510070099560040040c9510003850b00191002d1440d04d4403107110007040700382070010000b00144000101141070165010032400009041604005140241c002c0d440354840c03d21a000d848108100400c1121751204e1107503018008034143d91801c500c04070204c5001c3d20461f22640c480315400c0d441c0b00f45103400c0e00c1c0c0b0b940440740c46005003000c10025100c00105540084207900402c8080c4015402108010407101520041d042c00d03a00c4c402011070284080c2c011a90100d0b0341040021510380c150070281c001c144902c00d552030800206680729684c0254440200a40401e000041a050b408400703484800c1c001c0501500e07090844074040752007403441c1144a00c040803010400025640256115800c0343c960800ca03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 537919784 1250 537918534 537918551
    0x203070905060705150a020d1a63010302010e0907020d0e01030e1212010b0702010206040b04060612080a120501180218090403170f010501080a0e1501090c090504 71
    0xc83d2034071188217624401150503000318242e1441507040b06d124075a020000c0107a94110007681d055620300e0038416210340c540e143c2e03104814805a500c2942040090041e004001c035144000b100e030500062480101d4141201122007896500d1400c1c0c8000c18900b1003800d1503040d03100250460201111a030f001d40e000c0d00820258503000906180b031280c86040080720008024012000307010040000d41c99400341c0785000a217110550040d00d0200340c1304001c10081e80c2c03074081000301750142c0300c40607005074801004640800c444005a0f41c1190003410007140154580c1038801e0180d040358411070301207800007440b0607003075801007403d0106a4500010320980d4905100700490018a0032901d001c10380c00200340b0090264804013200104000c0c0081090f131400307080c00350445107031140c0481c40e6521040000c5290051200c1c450507190140c480c0502030300d80810300c17001446511030034900703032040c5080b17001c0305103c034000540282002c02000c509c921a104006100d00c410303601684c016070034885074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 537921034 1250 537919784 537919793
    0x2d0a1a0a0f14071b0c0f080f030c03030708180102031e06030c0120030d05010906031e0302070e04140a05011506030614100909091110050304030e040b0109030203010f02030709050607 80
    0x212904070f0b80c1071070407240f6650070041c6006091910b000042403165031075800200602024104001c4030b01841c11740f1a807034403403e003c0c0c1d00d902c01c00202c030343d0541003000050720f1f06004254290300900352000c1031064114a1901038226030094a1f140004040307101d00031441601d12501c958800070540207006400807000000e40140c440345841c0c232004100c0054400b07203082c10001d0b074101c003010160600203542d660f0311460041c81d0030700043d42c5c00b0003003055400881c0b05401041c4c00f06640359000340145072800c4050200c1003005041102e04a1540030031100000c0f0030422108850b0180000007030b1010711801c080824099a804134091500f0300000b04424000c883d04014004410b54100c90b0702c10150b4411100c02096400c0001a40d20300481c200c1800740100f081c5420407004e4520700c1056400d071409a50138001243d000f00001d580702c0142d56070382069084118002010304040f8070716506d0381e0019094801c0e0303504404802c4e6001c000c001c2000e501540100003010182c0d40d0300e2a107511901c9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 537922284 1250 537921034 537921071
    0x3030c2013020d090b0f06011106040b070c020402040b121503010e030f221e0e13030e011e05120a05010302060a05070507180c0e01022d0a1a0a0f 64
    0x42400c01d642d0102e00300c032114849400c0b024070a40c0c4180f0045a51400d4446d003400100f09076500c83c00168042c1900500c0c9000150090080360881d03902007151399011801c55100c40d070040120b030002d8003071100080c0500201c026140c00c04a101e0f07000d003d807a18001581802c2800c4850b180309030305004201c0f6602074040110307a40001201e4a0503078a20b40030807440380e2400c1010240900240e00c400000b0000d60303c0142030718105014080c1840159500783cbc2942c0318100707460b4090214104500c28001900641a118040506050501030965030302d0a60380c046030b02c030308400b021450003d20304c0b650407a590103069100c081140100541c0d411a0003141141c0100c41061060020000b400420301408004032030003054024180e0b1010240c6040c03601c0500111421038020404980e00018198004120300710300416403008134003442c2a1341b044001d00388101d0040e000d14001c048100001c100c0119142c141039a080c0e4a0441c1c5042079404141120b0b00411380100141c03519480501c440e100d1035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 537923534 1250 537922284 537922309
    0xf04030204020313020d0b0a0b0d030905060c2b0e0402030702031c0908070602120603060712020a050f030709081b0109140f1f020727020a09080703030c20 68
    0x40c1c006880303545541d900340201c400d4100103584400111410410011000b10117032141a040c4030501200035000140101210303401d900501050f010b001c00c0c001400c2140182c8141c01c075840485903001c042807d100080c1629040c00c01769640741c640040401074202e1640c1c1070699040e10118a9494880700094880c001c104611030080800740b000d20301441503030000350840f900468030300d940c1c03601d5280c08002944540c60103081400e040000458500c1e01003041c81c410070980d01c40c940341441101c41e410080d480060fa407400d0101c14014450200b400c44043c62040000740c40f140d901c0e500703107141146050222800712400c107600302501c0c0f8090341e10642c80d1049680c240001c0802006c42000507c0000268181c82d41000d0341900e091402648018040c01e0680c03140c00307481c119a140c0703800c001e402d0200d00d45120910035800d100f20401c0b219134014030078032185140440740151103420707c6042ca04951700540005105800c1d0200307000c03541984803a4040450701c8105003528802c0850038000820 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 537924784 1250 537923534 537923539
    0x230c0d050601090806072a0f02040b131814032701050c01090b010f062606010306030803180105070c0515090c040e0106091425090509090d140f040302 66
    0x2a40840d025034001e402c510083c0c900c4c4001c0d0340042c038080b00010300480795001e5002c01000d000c000c00c45421985040040d64540114581d140c04034582c090101401a042400c1d030400c0b60408a2031440c0d03003d2092100504030118121410315090800420301014003d0b0b00d81030f5041040030a445c41d112803840c501420b583c0c0390440c03a95a0b000e0060350f03103010740704201e0b0055081608540c10445803540d00d50507941106607810b203480e00c8001c00c03a0803180c200c1040724000014401c1c44104800c050900c1c0e403100c4140341c042032240e26562881c6181d0001d8448010b10314008034440c13010756081c00703070031740c0881c00c0c3c036000c0103070082502ca05a4510800341c1c0d0b0890410308401150310503109014040115401820610006000e20503060003400c4a10841081a15001c41f6115254402111034058610b000d80c42c60310f0425800d0304105601490300b8041840050f01c000030f0140c683c42d681074030650685001d000f001100365400760a081d03841c00307018000c440402140400242e044141c409a0707806 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 537926034 1250 537924784 537924791
    0x173d050105040e010e0a0b0604092111070b0f07050304030227011e0b070606051e120a0f022b030504050910030b0109110c0106090c090b0f030604050a1509230c0d 71
    0x44a0128004001911019080c44c1252075021641051503001e6101c42c03000d540cce840f80d03001a440c0c1c95900c40e580c90091040f500000c012140c4032610b000b0260900328001c0007070302d203015660350000d018200c044d4844447ca11050100e1118040145203075030052501c0780250084072425103003108011414000c8a02e0050080f803d4800e214a650081c80a0800506011040d9400464003000040c10548041c80744803082c481a69042d0040342d04510242d2142030b1000203a03960703003007040c00c0804000d0440000f000c030184002c070446014080f48481c0c004c3d01c1307103590f039410302c805e000c01c11300c0090032003105c03072841901040001d04c903407406411102c24500c0041c901c1d00ca44014600c0e0720503031241008942c2420300c04168004a640504002c00071038803910741c4980c0e1010210300d28001e9200040c6d40400520004007907040c180c200603801160050000b5600c081c0c503071101e81041c4113400150020303640328000401d580082000600c000003120380041185000500701805104440c06e54100c640c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 537927284 1250 537926034 537926041
    0x21151b0f1b0609030d06080c370605031005030a03020d110a050a140705010c0f0b0c040302060c060403080a0902061909051503070306173d050105040e010e0a0b 70
    0x1400c0240041c0146904103079001801c0030b050340f0b035a80c0c02094645080038901040040e485000080582800c080a411035182c540d03124583e011400d065800340404003c011600e10300b46a105e03a00201521140d210070b07840c1d0414146600c4c0612203908254080e1388505403040200c0d80008134210801d1451815180f5000c0c3c40c030b030081c02c1280c403440040c094411440c4503401c100002c0362583c43c180382d030011200100e42d0b403c0112618481c900014104290055082005c24a00504140e0005c450302d0000d1505170340e50b001c1a0183e00101008031603070403001c188010107501282080c0c1140c014442401040d01503000104c0c0d61107500c40342490303102ca00046401a5003c0c458103001031800030102c0d2801e92599509205c80e0340200c0707540d00000e03e000c00208500380d10081d8603440c030128100503e20008001940d10a0303c3e0040000b0b4405a24220400c01c110706503005449540e00844001c82c40754541805d12058400c4041c01070300c60b90501a02c850420000541c2c10b0b017568201c0510f51103601c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 537928534 1250 537927284 537927307
    0x8090409081606090618080f0c0705102607170603120a0908011812050a030e0106060c1e0b0402210109110f011d0f21151b0f 55
    0x305016040030807104080300e04082c0105a0b02c00051310b40201001c0c070080800c0311040004440300c1c900202904002d006a454881c0e004002d4190201c0480459690540311800101c0c0351551844c3c0038002054505172105000d04a0b100c24a08401c1d00c401280500704140040c0c428800f281a018602050500148241d03900308000b00402000c01030250341c507001d4210080009400b80070781c0340c556003408100550915002901a184c541083c103070110100d0129048520340d03c8141d40100309525017410190303200c404e20bc2c5a0041241e80c407202c0481400c1e2400304004842c0f074400b24070b4140c8002169020075110702099521580c101c1c0c1501d030004a002d00068030300c403082e42c0e8802942c600a0031804020440e1000f203a8844100e0712814a500c650b4011a03807600500014000350030180e56906480c18034102c03641c3e001a00a0040f40c9428890b144001c1d40c00740350b10301184a9104420f004d46181c1000d1085400448140317403800001c1c21310781a0011849449918110f4000008800b04500c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 537929784 1250 537928534 537928537
    0xf0e07120206040509070e0312041d0403032a0f050301050d0615030b0a090b090604050a0b2a191b08070c050d030c02090601110703020d0314030c070c09090809040908 73
    0x60a00520342034550800e2080205806083c03580c0710700030702c40e9908681d1402d4482702034030125038800c10b07106005415503405005030400036004905050300d40e43c241981311300444014498be034000482d55080e04940e0070007070400303640200100600104100500c2243c031349400a501080e041080410584550004000125070660001d030420321244140710341605290482c940183c010142c844c02610340241c0c030354440301e0503140101207a000000450004002c1903000d90f00c80b2078180c200809072000d0112645a00d4080c1040c5084200020031240010702a01d0050041c0014644013480c0c606d185070a01160512071406801403c000c01c0000803c602d60705c00101030680a06800c1007507000345009008403440c1c2504070300c10303100390000030140d510901c146c0e850380d080d090041c41034904d10b80034400c0031028690243c04000e0902d101026683c640b500641c040ca6003421100c0e984c1d10306040031500c10200c1c0d00600c1549040c104103001040d00f0710195106400100d500017900c10052406100c0c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 537931034 1250 537929784 537929789
    0x11a040302211f060f061d01022406090c030609010b400b0f1b030f12151f0503060120070306050c0f03070c0309050a0b0d0f0e0712020604 61
    0x1580314240055458144000c400444400421010b0003204d803249081440c11616011b1200007499490392000442c10a81c0f070038425490600540c0c0044188007250000d2404220f24401d1101d258424001c00342040034119901204501b4158218101500003425140e810311425040c1070012944600203e509400c1203c844000c40d0303c0d610804080510411801c0c41d091040d07007410282c00c1c000780b07a0300c1040031510317580708000b01140381215480c140440d0884c020800b503d1032000b404076120b00c1400d18000c000050762941491860f00e00145d051400da8100441c2d24002e030001041802d000041e109051480c00c1c3c142441c0b07031a580c0d131f9001240c038040c1d07508000c003001110f0511444010004101041502d0241606110940d16004500014400c041c04590590702c104000b42e1014070601c00303d95018481e291401400ba901d0000403001840d030303000b600c582c04001446690180d00ba11480030010f440d000144480c01c50b8001540c2c0359001c6115000030708401c101102c1c210354486084a01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 537932284 1250 537931034 537931099
    0x907060e1e10031d060103020f01051806070b011a0f04051203160b01080d21020306150a020303070e0319020120010e010b030c0a0b040909020604171005011a040302 72
    0x64121100c2d030040140140000c101090a80c0c102050511075011620605994010307141032304220607680115010b07070260216401200410b058031015959801c01000024001c040c181055410503100e50811890300400081c0804108400d41168429a042c0d50803103504072641e005001c0762403040c60139031050200554030049070300c5840e0704000000700c905060714146401c03900394940700034044e500d58003210031541b584503000707109030200c0f0500e400440d0301c580098400700407054074600c0707150103400c107400303180158001208004880398404000e64220310700310002d008143c140c541600c10f241107000007a0401024174040c03400711000403100c10021021000030880840d254002500801c072141c0b9882c401d00855010101a103403807480c01c41a00c0e00c05800d40d18291030f1100150041c40300c9c8108a8200d0701c01e007c0010006030040040e1020841040600481c050001c032200850b64140c001c1304c50030307110a6913051410841d00c1510152a816101d042ca401c508541c0200200b070803038a50a03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 537933534 1250 537932284 537932299
    0x6030f15041e0e0606060703021b040207020d1101031404210216060309230312040303060b0c010b01081b0405010c0602070507240f140913060b0c060907060e1e 70
    0x4000b20b040e0722070030040c2c01220655401d51100010007070503218500b00030340184d01c00541e22002c104a580040006040100010314013082c503800b0541e0141c00180c21380d0501c11030080e1060558040c05103e482c101c04809554140ca095074501456040c001a410501c000811540d110140200403130000ca90407208110f05480e0394080c028054101d0f800111041e41900c8a02080005411200c45400340c8840c00f56081110f0ba14030380f642010002d2054041685031900015442800300080141c0386445002190703915020001501400c0050484020b40c00b000040380c4c1503800f45c0c0c05803004d440c02403a164001a110b070030309034084e0056030000b03803060040700c5001403010310003503441c04030130003c1000c40d40740340011405555001303244038001d0119000070900c86280e010840100358100e0018164802c1209500401080750f0b000c0d00f0048200d440004c180341d20b80003c1050580c403601550092841d40e00b055401000c040c0c020354414050050b203081c0f01051258101c601d1602100038042e40d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 537934784 1250 537933534 537933581
    0x4060b060d06090f050f01030b0c040b121f050f0d060615020d0210090203120f0705070f080106120804061b050f0c121b09100503010501032006030f1504 67
    0x1d8002c00346441101c1c641890a105034098541c1405464811004101040483c0e8030f50388034010031601c0203000c0c1150030070400c00803d1700b4504601403c11401425045800341c942450b4501c0861100c4008211014000c08104100c1d50f55502980110b201540c001800780b4280c90480040d10142d0010b01030035100e50080f80502c0d60009a0209010b065421210f4841c19038028400b11800700d40d01035016044200c000c0c581e01601c0004100d0200c02d40c81c40c40c42c3c00300075198141800c5003070f00145440c0981290401c4640e000740038001c09019040300454184025540700304052003940705210038000d0070301c20b0b0f110300f5440c580b880c0100c54101095800e01072821b021180c6400e003580c0d56500c90040d009004e55284400a1002d05414540b64010700d68000d444c20010113440003040e003144444c1540700450117440038065103000b1449904508002c0d946201400c03084504400c3c1280102000d10411000c0c2d08001d002a40181e105007440721401c00100218025140c2100c020078014410300c00c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 537936034 1250 537934784 537934807
    0xe1c18050618010215090606011407290603121605031e071b0e0a1505031b040c0e06041404110a0e31050901061203020303090c04051e04060b06 63
    0x40c2501c12426402d6070401600328407458002e10086c0e583c811594454000980700c4e5004d21160800b05e660001d0b6103003000e0082d075408100039010942d183c4003211f0b2071417203280c00c441c441c841038222200320050940b9000558010f50030f405041003550012005d0b0525406005042c400c4502c446c8815000c16100c802008210550340d00500e4121902c0e80071407025011b0f0080035001405684180d48001001e4407201d41c580d0103045036008148948594541c0080c071564100240305070000014184551103808008020803a400d813038900051007251030050000d0740d1450700b150199030940d01e83d150482c0c2d000021030014801d40c58401c50756000001d806a2040d004103a82100321030443d121807800c40c42d01180020401007441d500c116400356440d10f41c00c81c245030007075a80070501c0d0000245e8555101002400782c64071040c240c4c0035800c000148007000c0c106100c030203040b0100341c2e010b00c0b050130441103605550415040d402c03082c1c0a003901140400c40a0f40111030780410061407903403502c510481 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 537937284 1250 537936034 537936067
    0x60d050103050d0f09060504060f210c0e0306070903030c0501020f03101509051c0203010902100f0914060703050a1709010c03180b0c0304020d1a0a0e1c180506 70
    0x3c0c000860300c002e00e41d440c0180308000c00001c2e18103075a1142d04003841c00c103007980d00501220b125810300c000030580c55003501c00300da000070900c4414070005c610a4107108000d016100e41081480c001d0b00084100705403107401c8000a0100c0703525140440d6100c0729070401d00d0082c0606411301107150740003c24130001c4545020090190f0b05030302d4044182e0410500300340c0366aa840c6c032a6613009403004881041c4450140181d060f9940068000720f5816001d50000307011491080d03c5902040b42441141f00c200e51000103800a4005807155580c2b0340d14901c0010210f003d401c10003020801c0c000703103240f44030b88505020703482c0d8000b40424030070358200180071601922038001000002484c0c800d84800e441d248100c00e81c01960001c8140d8915129580d0400341a40b0061040e43c01108a12000d0001504245282440038006002c00920700b804a4810261185840642143e03806060449001d903010010038442c040c0710b0600c40c0c0000d03043d041a481008140e804541e02040200740c04282c4900c909 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 537938534 1250 537937284 537937303
    0x6150405030d36060e040e061b1e070b0f04031d0d0212060106180501050403151404080304020f06040e0a090c15020a0507060201230a0207020a14120c0618060d05010305 74
    0x4507107049592102c0140800ca80400c50100156409074000c100003140501400310390801c43c0c03d0b0792b45000520307502901400491840c50746501c000240384000d1010300c4500c0c03038004400341401c0506042a480040854945841c40e40f007144140003c002c081d540d00c8040c00351503030701804c541e500c8007908280c1922510241300740c0021075000c0e0042c103903028100f820901940c034140c4a03030b4281403c40d103e07015070711a02d400d00001d0a41e01c2c14800c1c1a03200c80e0949c244118440c0301003907500d25080c03051041e004884060780b4000c8070144410310002201031500c643c011401c11002504030300078240425031400d141e001c034500c0d9640b0910001015400714181c40c58034010300840340f20700e036101800c03800c035000e0b4180b040c5517070f40d009003699072201041030032a00300906d0000035003400c00070303000550b8030695a80030f041c1016a10041052900b02010108030540b030703e0016091880c00a808568548150303070486198200c2c000101e4255550841581c03464140041c0401071503840e840e083e0364840c10326 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 537939784 1250 537938534 537938537
    0xa031d0a0e090d0801081509030c030408071e0e0a1e021603030b0a03120f020f03181008270307050a08220f141c080306150405030d3606 60
    0x1c1200c3d03c1e510301500000c1d04a484010050841c00c00f40e0103a0b5507501ca01400c415904d0204010030030001c401000074001906c036003005018480c1c83c14980c81002c0d0301c048410303416410601801c1180c00e504100b055070046100502140650078502440880d28401c144400164804150002c218042c03444021300d0500c81d45040041501640800000d081031f0300c00241000c04440b42c5180030352266580c81c0098004d401140d407056210701c0700900710f800015420b00741c6000c0c03400c141054944007139940d002160a0030b000e407944c2450070920f104c01d8a4072502500c2c1202c1c4003080c01007a0000c00c219074400740c0040079902441014503004980d40e0084051614040d00d051540746007240e0b419150040b140b48810403003040d4541100c4c640400c505001079540000f0b011100000101d03202c51240c1d071140300b1a0f025070b4a1034800e04004a07109055144804d0300310a12050001e40c0f800100d006507005582000060005e02215400c11350000b168030003101e00b80c0951050282d0003a049003c1582d019 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 537941034 1250 537939784 537939793
    0x2190501090f0c050f03030c0d050f0c12070213150302100e0315010311010206011508060d080d0f060801060b040b16140a06060501050307020d0e120a03020606090601020d020a031d0a0e09 82
    0x1808040e40c80c05034207203401c05c8c0d8100c400c503c1e003600d00400c020422203400d00206428040800c2d8154100f0301d481103001c502c03400000d14901180f919010441e0703250141c0740704102e10020105050144807980c00000e005007070343c412201e540c6000e0907103400c040c10000d08035103050840c0c50b0581c3d03804500b1320040f01d002c0c52441041d00d141d80003040c103a050703c065000c00d180c11000303880202d40c00100070f0513942e08501d41542070008030300100c00070302030a4110000071401261600794142100c4243d07101a80701d9150000601020f1b43c110200c03411038900401640d2205c0c80540c00c0c2200681d60700008140c0387c02080102a4030174049284c62485025960411030a603491005441c0340c40212146c078016045440e00c2c1342118007034035551080010140503040542861007082e40351a0345c00c4029405030b84903000308102e600d84a5804d0f60b00560a2003e800e01d01c40c03d002c0170f507071854202001000d100509141100b480705185255201d40c000414826100d5038480c1041c90415040d19a84010b016 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 537942284 1250 537941034 537941059
    0x220c1a0913020c060f1b030c07020a080606030a020409050c0301020304140d090308030105040e0a12050c01060f050607141c08091011090d060207080304030f02160602190501090f0c05 80
    0x50791003a5a800b1404001520361952201c001c409502c1d40108070780201040c00c1c0395000b01c94101005140f080c00c0c280345080e51040940100a4050700b594041200d5a00001c10081c3d01d403004150840010340c103641c0880d0300d940307514150342017140740c51155402d58070100422051110003021902400c1c903000640300c2c4409140c10880c3e401c003042c000901803d104000400c042d080c1540160032000b860400c0c0d8403500320581c0c0f1242c54044055007140060000b0903020304c480400e00c500b0000b85030364a0500c10300c1c1d01d810003143c181d020300040035041c0642e840e8400c036a6031080c04140400000c1e503a24062201405c04040e00186003695503514a22540a140e00e40c221030348036480702d40d0000701e26079040901840c100903a00902c5d40007140ca1540034401c80c0c0002d40f143c2c0156004500c04c1d11080c0c040582200020b152840ca141c1031040c0102d82c1d101000026008203104141d1101a89400144d00303150408901400ea4154010b0082030b801c1201d005001c54098410240c0b181260310518504 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 537943534 1250 537942284 537942319
    0xd0e0d0c021003050c09061b150109060f1d1f1509050f370329040f0605070c15050108010605180a0203061c050105011409220c1a09 58
    0x11342c01c884224940404002d0001603240c503401074400e0003240d60280300703800315a464050a200125811410341c03102140140651180350044201920b4404290210245014100914011003112a442946100e40407856184074804244075803030507000703044c016a6a401e10810481002c03122200060701d176080105030b91800810008840341c00400744051491890a528010410f20b00a60322049000390080c03003040c24aa031020045000d4002d030003032841c400354504a00394480d464810082c00d048100400140e914070b0340340d01d450700704100142039035440c0760644404594100c007610f5400005904020003400d508840d041c0d8141c0d6000303002d4180d841040c002c4c030b05440d44900d0100507124001642810050b4080c65101400800050021400700000804c001200c84288c3316079448000501010040000087d81100c082c4c07402c400e589080810301002c142c1444642a00080c120500c2c400d0184908071100a07004504802c488030011424012070382d03100c500d20b40d0007441403201b03c00868 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 537944784 1250 537943534 537943541
    0x6092d120306051f05040521070807061202070203010f020f070204060e07050406180b0a121401030809040e0c1009031103070b03181c0c060b0f010906050d0e0d0c021003 74
    0x80700d025040348004d0401e20480300c440640e4029000800c0018400022141c4e15140a48402c800141540342c2c0ba10246641d02c3c106075298000d0002507214800c1004125400704484101c54201c8000684480c45071000070301402582590340030300c0e400821035527017440b4060300512415108540810800d50749030030120310b584080303e4510106505000800c015400350b01030b01c080038401c0943c444041c1d101c409202c1141c120254280018511106402c032607080c512900140810420081c00c00f0b616540d24a40a4814038100c680a2620340a0880c054642040030294403040204a00c03040301d44050014a002c034a0b00c4261074aa644448105190a02040000582e101210400d19540c3c44540000d400c3c948000c0721003171803048102d5041e00c110804c4820362000400d5071404248081c42c01c121080d104044c48052042d408210600400d81c1c102c1d080004442c550f04043c0c1d101e0340d048202c1001801c400720b07140d10ba03009208c44d00c441190700c56003485103940b00b00c0b403165002c29a49001c4044 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 537946034 1250 537944784 537944789
    0x190e0a05070e190f0b0a120b03100f021b0d020c0108040c0306200a0806090a0c08041502090402070804050306070504120201120f181103010b010c06092d120306 70
    0x724194080d40045403c00c048030070030000c1c20100c03803c881070b9283d060240403005644052044980402c51188a40d4000c408400030381e801501408044409800240c8440802100c0c194895940c8800003424074260196a904480b0b51041507121000901a544a02080c90900014042c0c1c120440d4039600490360240507a8000342024026802d558906005000000400d0b0000702503800396040107088200a10741010290340b000d4003400c1007010710020b1b040c0a8421103495041881c401d4a1552001d420741e4455006401030351010820344480300284a000c40705604140001042c0c0107100c020801801210001c0e0116110f0350368142c0111154081e038000d0306440001c11400001661098503107031502070008034001906550001c100044400c15102d0310100b07041c42c0d20386402e00c01705201500c58101c045d002031182ca0903a40000301000c6091000800c1140e951911009000c00798903441000030168000c9054611080d18103600300703e500104070360581c80c4141402e04184240120340c01c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 537947284 1250 537946034 537946037
    0xb010f0512040b09011d0c03191505070320090a0906050d0b150d0f021203041d0c0c01050712110a0509040903020c0415060206010b1603140405190e0a0507 68
    0x780354031180d98489000c4806451101d041d0b48501800b19540c0c0240025051011010010959039650100385070400c91601e86440302699120000c002007002d4000d41c88030300300540d00c00695a03541c0c6d0307415001007101c50b60749004201214110001b840c0800020242e18808851103607105681c1ea080d20181e50f214011f458202c080f245040000490b008912500000d461009042c2010f060011030305401d814881a07918455032480b1b04154200940507001c1c00c404140510315190405034800401486510740a01c80741c850b0001680303880d500001c3d24000040351000b40910305010340001c0406209a0104202c145001d4400704034032031410845140c10515205c1ca401c06003c0070801004010484058056010784100158543d0b1148581d10001021034851102c241c10403400030301d0204160030584400008005d00c842c254454600208443e41c9840c1c02040131000011000703a0b0300817617100c0e0350800180a4080c61410140c2d0111050b034105005a940c1c2d96100d100f002c0a40303d060b01c4040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 537948534 1250 537947284 537947317
    0x60618090b0a0b030c100c0803040b06010e01020f0c120a1202060613020a020a030e061c0507031d1207080705010501060201050106030b0d0f0b1003240b03070b0313170d0b010f05 78
    0x9406d003000210142e907101542400c000300c00958942489550044500701c904038211030400100303680201400c0e042000c00e100410000101003141c0b940c4c4e0404031103180c030070864070192113841c1608201d01c03801140e200316401c0c0421954034001e035642505444d0180b00c3d000104040b16010494400c1c0c0e6164007007503004003201c7d01c0070344041d41c00c0701da08281c403600326800300851041c080032124441d44034031490302c00042130b1411210042c1140c20340c405e403001c912544110842c2448001810702408042d2020720f136918140c6290200040c030030701900404550a0100001c2c9460b019800b05040b51050340302031081c80406800c07c40ca665136040000c281c3c8481101d03e00108200000040d0300100305020990066143c3d02c40000303c031082001110240c080c4000b04120ba0314070302a00d1406401500104401428840b0014003400011f04420303810702c5c03030a5243d00b4001e600d03c0603662000b0000d03401c0e40c0c4101d40c00c07a480150501c55407140c04254001c1003000800c0c032070003c0b00e21072070781c02c003069 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 537949640 1106 537948534 537948553
    0x30a150c0903151116060501060906090b030f060a1806051206010303020303040f150504031e050406090306020d020702090c042c040f060618090b0a0b03 67
    0x40410070307107580c100009104803c0208400b250490301040c81038208031010410b0040f400101c601e40c00e83d0b415841441a10b1b0700007410313a211a42c460079503540740e08055500d14464480c2401d83c400420001e805040e040703000e1904004000c00001c0000c0e569610a400120800c3c200d2031003d540c5c4c00104554600310b0301589030102c400c0c006d40503961644d10040e4990000070009040100c040f1005000c1000040b51182461150442004a403c041c20300501030090031109080d01181032400044041c051001e5408030783c180d5440800d01c40c25951108040c0d0031181e2548020354081c00801c00503650307004214419412091003a0f215031914031044284985510340c00e4030084604c03018040d001b0300400c0303550b200c1d0700a02c81000c0f078001803400a000740903a900000c20305074000308101801c0ca007038200241c003074081c0c0c4cc1d4000d603444160540003200c1c07241a00d19030540c080d4600 = true := by decide +kernel

theorem cover : BRFrame.Cov 537769784 537949640 := by
  have h0 := BRFrame.cov_init 537769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 537769784 ≤ n) (h2 : n < 537949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
