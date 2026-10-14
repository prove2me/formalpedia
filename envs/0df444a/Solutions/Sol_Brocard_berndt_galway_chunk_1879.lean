-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1879
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:00:44.783728+00:00
-- url     : https://prove2.me/submissions/f1945caf-d6d5-4849-8022-ac986133a612

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 337769784 ≤ n < 337949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 337771034 1250 337769784 337769797
    0xb03040b0a091b0f05040e010b0a03120c300305161b12021c03091101050705011b0e0102010f0e060f0c1b010f14040f0b07020304080613060b090403050a05 68
    0xc5810104060f1007480e019100e41d001d007035100301d5640e10624080500c000d45401c1c6001405d80c0e4104540c1131000d86421010000300c0750802401c4505841030041a2800c1e0040d61020b0501c00101000302113011002101c46901c0681c94100501d102082d81e08904440040d1680030301c84041701c4004031864420a0f004100c1800a003003c411040580d88038001100c074003a841015802c183c01d13052160a030491112024445030605101c808150703a1441045d00803485064184903001c0b824105001c025808410100880c03070806410381003810018045081ca0f00c6620f0041d800c1071040300c00500d160140c8004109440c00410b020f45952594144c0b503e0020201214441c050003480309401c11458281c0000040310b0000401040360100c03907040c3c0b906d14401281862598060100007070031164080f08594100e102c0601c6d42c1c56143c81281580301e1a070195806100b00310501102215402c08030054511802c800c12111100500b0710150031004c96015020480a0240000580c0030f64024480c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 337772284 1250 337771034 337771043
    0x14091509060c0a0c050321030109020a03110a0810051e0f121501080d08010b090d030e18100501030e10020306041b03020a0906020102131a1303050d08010b03040b0a09 73
    0x4110030005580d03d03110307000005854201c1e140d20100b01909007809008402c0b504000300900d0503a52140c01c600c280f0040c4a001031191340006e844c00c503940f003940304825100c0d05818041d640e17151500003c261400a842082c03211048000000c3d0034942218450000d008901164000c16000030402001c2d101a028040d005400701c0c2207000c2101080c0602600d062484410300c0301541400c580030328046422403001d00741f20340d04006104000d1554140c3d0742c00f540403951089000e5503440e00b243c8009001c00207603003208000581003a075401c0102024400d02b5260000403c0c9a65000110151036111224444c40d4011507050864019580c000396400300002c1d01c0805c139031580780890009080c04004820000703502046035464150300a9165006248901c0250b0a087c60710701c00d200305048034803c132185416100e0184603400080015030f60000d1000c03141c51261542c9080c0719445900c441c0040000454410003c0b40f542d1100d010380f4011a045002d8207490fa40b400c1d0104001c0903041002d0302e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 337773534 1250 337772284 337772287
    0x70e150306060909010b04080d02161e0801020c01020a0311040e0402011b0f062f2a030a020c01020708061506030405100905030c121c1e02070303050103031409150906 73
    0x140f00d4031144803a50003004080c080a503202d2615002c0b80c1001c00c001e222000b103400400b0342045005210034400151410501c44611052211510f207076012101e50050081e540085201c124400c81903000d0300280f42c0c1c51310b0500c00d02510310460700740b6105a00448068040b14400314015520640c080e600c0607011440020f0503440c1515290282180c807a0202c403d40e4a81300d0b03000d482440418181c61303081440d5813880916207002e43d414502e014010072104010008a21881140b01000086201290110030349076a16120b800c000d455104052102d0b015204110000503200b40004a0510609400c0c0e07503410445800310400c41242d1020708140c54610400901081044451080b20314452242c00150303640d4962401e40b6090005130080c6820b0101e040c428075001d0008110460071402d4840c90004e00082492049100c101c02030018240d414800b0900c4c2b42016050360085042c0c0c0c0c001d441e0301c90080302440c41c076590380c45600d0890360440c0714108403c28103007400c009030400203001072115 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 337774784 1250 337773534 337773547
    0x14120c0705010e10141302100c0b040b010e0f090304090b040204080114190b030303062b0503070302061b091201060918060501050102060717100e01031a070e15030606 73
    0x10740c00e40742402d0301020990450740c2451211280c0d40b01d0303401041c4500b804039200b80b811a101640010f269600680281c0400c884c40342d0b82072294200505195000785c5070b81090800c1d04050034844000d0082400700240c0f04041400e0840c3ca0756614840e00140c3c00075840c007814125038101a01d000d40c44039030006c0d024040481c48620a018030500c1c008a48110025480c18807115181c00010031329a10352540340400f040c4c00ea880200031243d202506845004000541c0c6128600d08111807081c0581c0c5101d60303000004014010004091940c081c0d404c454560302d17561231034100c44503560003c1d01c3c640000c1010700d545e4140500d40b26003925403400005580d6643d1426041a10000c04840101c0d00e0084010b100b0400c1500c1072901400003803005100a26108a0280071842c0001581c0031889142000a96580d81d01c51005c0c0a46500e88ad070986a5075286003d590b5603000d2080d0440c1c8003001340000e078034144030b54522981d10b180100303010040e41030110494400c0c0e20192213160415001c2190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 337776034 1250 337774784 337774793
    0x5101707090608030901020d0f090302090606070506070f09060327031116030209011a041719082502012007170c0a09020405060409020d0906060f1514120c07 69
    0x101c0d402044540f01559591240a000900300030003590208103101c06c0400c50507000f030f881140042920b5054910104980b28a0005600c03405940710062007441070700204581d4981c0b004041358060100d48502c1c03440c54540c0380580c01da0b83c800701c401c558800e504503018080c80c4008404d40d0b40c2030207030400e111078400d404c3c2e03039509265070440381481c070130704018041086041036000c0d01e00402e400c542c8803215160162401400d4490b5104e0303d400c1040c07000c00300340b00e500140300702c404800c02c0c1d003c510b00c00540383c038040c9425000400143d4100311008003c0954483c007100c22148a42d0503903a0080e110f0440400c681c3c006080324040c150351207149c4c0c0100e10603100e014141480c8154400030300c0001902410410445116080b014400380140700401240e00c58205590541d10105805070303e418510038440020b01c00c454010b01003a04101b0001141403600c480401660144811410344d1480321030260b41b03000060480c0350700034008008403034201c000200c105402070b105040440c58000e40d82c1f076 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 337777284 1250 337776034 337776041
    0x10303080118140411011101090b040b01050f010210051b2205010203040320011202180103060b18040b030304080d090e01050a03030f08060a1d04060f0510170709 71
    0x1100464a1100140a425040d03240002d81c810b81d800c00f0311540b00c04403400030003060058402480300d800c69002c41001ea001d20054080300042c64001c10a038030745800d20010340a416502911200c278446e0000c184d60503c1203240400a0041e00100850018030071508010040100b41d440400c0e83e4211340c0c0115100b41c0010441c502d58611017402c1c04500c503244141c1c1e42c28ad5884141990700c1040108000b58422110003002030401450300340d400742e0500140e90000380c89440840c00303440000c02181d003900d01052100f03000400e82e0700b0401d0988481c9104020720a840e010511501e06040b8502a403400e5000100c180c2c0e0060309036400c0540e51a920761420021800c01d00100e40300120078030083c51240c4503980108001c8601180017807868034041c2032000d400c0c00c81b10800082e20700151003034a079201402c0040c80300030094400c40c41c180001c407004400c142d0301101c5240c28003883c484142d415000c1e0030b01900020000d82d000919240c4d04c56030700080a080e2003450301416000288100c907620 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 337778534 1250 337777284 337777289
    0x301030f023f0706020f15091006061106010501030501140d02030712050703030e0102031215120d03060306060506070c180b030d0f12050912070f0804090603171c020f0c0601 76
    0xd41c08500b14103000c180d600305085500079a0455028098020009400054824030660200c5080c00261194000141041160464221500e08001000032025446200001684440c40c141c80069803540011005d0300c1081c070404116000401e109015454401d402e140020b00c024100e80110390384201282102005100548858012101c03c109041d04100c00081040c001d20186103011408a260030014a000c3c3c145000c241208066403003d0708d6080c520744032400c0302c0c03084444903421118000c028224a0208980b12410b0550025050a00c0e03404d0307408103903020700740b080d003e4101644445140a00c0b00412040e41d10780e40c0408040c1c400340300c4e0a81c05001940c542c0d07058491810040c0503020319664a9082501d00010072080760b0001ca40d81c9110503410340c07400d0391840541020b40c01480d03402c0c8003030002c4c0000100025505200d40c007000441303201d10110941c03642c8e910202401b5003e200740080940403021803101c00900c41c0c0c3d00170000c0c080403d00c0305040041c0c0300c11881c0741c076100340c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 337779784 1250 337778534 337778629
    0x30c120c0e0301050c03160801060f0e04150806160e031e16030f0201092103031e0f0212060a0f1202180412021207110d14030c0c13020301030f02 64
    0x10501c1f05420002c00e000d40d40400740e041000895140c410028004510185540c0810805501070100d03503403281c1015600c00c14105010410b036455041c0b01d03455034000c0e01c1880c1c20070729405078007495034050004030800360740080151200c0340758110008030007a00c19000c92461f01402c0d0503503030314824134942c2d4005507001e00849100129144009003030a10640c0044980a042c4166084081301e0342c1161220541d241c45e02007104031401e400c049240003d005c20342c5030a03042a007001c038840b0941c0c2c050180307a06d1040107071000d501e0328020300070712450300d00841c0c140c0100700e40203020140e0280b03842c48080344007410b80300083c0c0c00150484080d80b0141d40072aa940c0c0001021042103604010101c000d00c0b4240c4c001d454002d1566400c41d0308158008014010800482e1384000d00094034501c2080c0358003a41034a60710400094000d07259410030074100e108500c0400c0118801d5054030075039060307a03071042140e041071920ba0204075103d404420400f014181d40c1c110a0044045180e0611a68501 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 337781034 1250 337779784 337779787
    0x10e1903210c0f140d090201020f15040515100b03060a050604030305131e051203090303040f030314070b0708040203160b04031415010320030715020607030c120c0e0301050c 76
    0x2507250042203044200d41000c1000710035004c0e200782500742411034465a1074900300149100e0703e48010707400e2128501c03d108850150440c800d000d80b0002a805124038032035810368040380951030390000d07440400d4400d890481d55240051005031050001035800110051094200c9940e8100013086940180c004900080380400e034449250310f01000c84000c1c0242c1c60b888035003da43c0a49000311901c1c01d21815100e5a2500111443da00b81031007110040e1001030b09481c2e4440e2518640c1d104201c903480210001200000038030000c406d03d20541d202c4a9000302041c0b102c1d00d13a08005c503000d07000500140e034980600c1400c0103440c0c0c40410004014141000c980361200d02d981041030f4904424410414940c200000708403204104041d0181500da108c0e01060501e2465915550500042034034590140304e00640801d804803000040248901c0036030848003030b61341c0c01c9412003d4421545106021501044807001c1000f0b880c2c00100b10300c00507280500e4114100070004e802d468041d0351010340c1250 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 337782284 1250 337781034 337781051
    0xb0f181011060f060310020706110301080102070203150907120809030706020c0a060915051606020310031101020a0b0103141002040b070303060b0307050412060906020307110f010e190321 82
    0x42032203980d910a0342510f00803520b10300b0002103600c507070303501d149003c2240e0f000640c40104159580148501030940c01c0b465183d41c1c59138142c6000b50300000c4164071a06c203108109100000071003509104001e568042c3c0003581ca00050505600c65510044408190610000040e40c80810042000700180d6000309285642c4405208841655130000750422400f107005001d52501907104040c0d82225140541d5501140b26a0100c0124031300c100030041c82c00003080c001c603061192010000c0d00d01071200c12160842181c01666101480c01004204010680040010440e6000040c021446841c191001d40202c9155403080785c0c03141d000300340081c2e400720700041456854032881e0081c216241c81c1a103503040c000c1001d0542d000b80c1c802c5820364480304811008010701ca03000703041c0090340600155260b00301b084010707000104c2c68401c40302c3e92145c11511921004d05000f496501c80e030b904090042c1c200c40c01103c4581d800307030100582c1403107005200c100d036050395907140e00c0451048400001d240038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 337783534 1250 337782284 337782317
    0xd050d0807050403030512070509030a03080a05150d171605061009060335030702250f092a2102030708060d0f2012070b0f1810 56
    0xc00150411081020070300c814000290810b0440c0d81241c41c242074408655a45071007161548103000c0480d805028020414003019000380015000b00e185402c14002581c8094208501d074190504003640f080328103106001085025500d6540e01c404a8a034a140020391403c900451078000011a1964003d0080100102c44008480054040c0b20014001940740d6200c10810001990018a10780800c074080074105409000e41d00c1c8a0306c100c016076440c4c3c0f409200103515000000c101d192002528007640500461f60b00183c4152900603a0b14140c29003010340800c010301100c3c20002e00c61300c0f5051907004c1c429401d10301240180031555407502021074101008007041180009008242c010b200b13200340c903a00f112142e58000030a0720961a40c1c81036090503014001c0f03001010302840c1c00c00c0b2090300106809200e8014511080d01e541445800e1384a035590382d422940300302140540d043c84010210005240107002d101101c2112580300003c1000080d07000c1c0c200010305000c59040e008030600385 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 337784784 1250 337783534 337783547
    0xc07030204050a090b160905031e011a01140a050906041724070c020d1209080f1603081e0307120606170115140f0703080903130504050c07020d050d 65
    0xd03d0004040c00014150380c1c2e41c00100d07601610708101d642e0ba0f0307038000724042d1007209a0001000000d0444030040707a8215034034203d46106240e00700c075500300100344825420076500040380600603590f801380c0303c00c40940504a900248255010044100805001c0d680e8070030250001d00740c0701070712602d024030392110b60385001014104903490446a262801410100340d43c406c1c2d20519030f05154421050510000d54941a0b03841c0c018440d85412b0042c13a41030b03a0082a17034094074070881c1110302e05400380000300c0d55802480b515020305103980c402400020120030203800c5911010385411680070420015242c560402c5401c81c000800c0c10701d440b14180c070f260168170000c0c0240c0c208100460401e103041c00b0f01349414080d04111442c400c02c3c10201c2403040004c030000800d00d49000d40c488070400c410f543e01c2e40c0070240a400042500d4041030001030080210f400c100703074040018100e03078039290901001e00401404004005001c0c014003015845182980c46024443c40180210000c0604041c102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 337786034 1250 337784784 337784791
    0x52d0309060717070804031205070e13090c1401140a0f0e040c050d0509100606020601090e12190318152d1a03030c061b0f04050103090213020c0703020405 68
    0x810400400152006000040c2d0300d42100304d510b025035260380e072410161010208114024001031501c81041002507101114100c0940c08490868082901c11816415142010300141410040b0740c810080500300011070006500103041210000001e2080c0d9610394001203200d102041602c8100d10790700358483c000001341d40b011581004404040500104503000791f40ea160000b960710720110355000400c20041c450711000020a001e10f903260134009485000a00c02c1312842802c0c042c800c009100081400002490160007203410718944650f0070100d004c41680c08802d05541760f09400281141c6010785440e58081d44556146080c0c501481d000c4070008059520551501c6141c11140d480005811226084251000c941c06030410302040b003c205070003103c0c5d4103200002e5070940401d0301240c96880b81350101c680d1012069601c4000c003d41c0b10f0124401b074103c80030030040c0040d6009500480401e80007410703140b001c0411003080d8089a105450305407550384412010400c40c6058095540e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 337787284 1250 337786034 337786037
    0xd020717100c051323010f09030c15021005150108191d0d030c050a0c0615030b0f09010903050a032a050c0c041401050d02270604140403020a03052d03090607 69
    0x102d8050700c182c0221400080c0c4805042114001d0a0605036200e234090f80050758011810480e0151740356a0b240a4140b425000b03005070284581f40404890076200d101d119440f181c960400b481040401181e520a0041c41040700500c442641c1c1c0b441c655901c035076003c0d400013503c01142e04494600382403414a4802c2c05808241c2811510880c40f80d010044e15803c5410782041d058800107864100090305031695205c86448204200100348940e16403542e026040c02c1c1e184040301d8030f449581c0d03800d0344e00308180580415001c1000c1ca458510a9102d41c0c6a81d50342102034621070403040201c440000544074800006102085104801e141440365881440048a04100e081c42e218060301101005114540c850701d200782801056442e00410400060f50100e041009141200542c1c201c24805460450159180c81050381000c3d41a4007101c0c0255010307002080b0741a0503079411100740d070002070440c000b0494600318440e03003408080003504406c540b004180d00c0b858989481441c1940003401e410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 337788534 1250 337787284 337787309
    0x70e0c070507060f03090b040b06090f090d0518030604120909020c0a080c031603030e06011505030f1005060a03091403042103140f0901020601080d020717100c0513 72
    0x604005400011120213003010710300c2c41c00f08031068000749810240070f014580050200301c20050614060351150504070b07410b104603182c10748900c0c03000344115000c1240d9404508c0c1c40e48254024009825110b00c82c2000412800030751000c00d0a00f042901d0803540e180b00b920700c0066094100c14010003801c1c02c950b00f1820f14242ca20360559841d141240074140034000210340c00c282a0920840d40300da6140c008100b2480d00c01e1500800500c540000e0101c10300490340042740003030001c1300726030000070a40c0e00e80c2d055031a45100c103c030040c03010b4480348005101e03c00c0010303161210806441c22000703c2c2c82c0040d40a1641c10b0001e141c03520015201c035103400400042c003c0008d00440b403c200c400141e428110180680760642d03603d100c00d0108030b0342c8000890494203089240c030090074000f10a909039407244c1d03600e0243e43e54500081189101580100c0e109000290030b030b03c00b03a06100c4090b012070303440c044242010411184007482020015000151502482107820118401442181e8011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 337789784 1250 337788534 337788547
    0x902031c020703020f041b020d030e031806090d0204052e060503040807030e04090f030e0301051b0c071e081e120901020a35040b07080705030f0c070e0c 67
    0x251100001d00009101d0b070813900170709003a0b840d00e90246183c40e0004170003503e464a1840c0103580c0d007111301c514000003804c200c21b1000460380401920460700186c1e09031091b4012140400c00d0070380216003c00c1c1c00a031201506800340e0303658040c450250403121000f4840c002702c0003140d4507034400702903007480e56140c52004110b040d030301104480d40701c0e400000c5240c881800b4070703040b1944000035007240d50060811820340b0038001c5522a40200c140310303469880190800109140c00c4c4c0d0011a009503803400c00d00d284d981404e201d140140703111007a200950740d10f00d480314400b011000c1050000400f080043c3c500307000144007080003005100b440610b000342c00d4619524183c6e66030746040300781d01d0040b001c110240707244d00070403e0340719241e4400f440e4858000c01130640f0307070a00c0d804410091b50220294215692880c060112010382e1880c4444034030303003c107985a00029601c5103030100d50600c030800c460340d0140c011034080c0003001000c101800801e882c000d100c4c075144c603000d004492049401c0094 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 337791034 1250 337789784 337789787
    0x70608010f0806040c090203090a0506040c18050f06120f03040e010311030604050a08130312021005060609060729092b05070b06060415080612070f0b0723010902031c 73
    0xf05c0003203a84040b40580e403913845000302c508120030900c004040307210b08c00030300c030030441140c101000340c40c0001199683c0f0220f410140c401c4d1203080e90441c100f0035044001c2a264141105a140702803050700c12180bd60110100407840c5500c80c3d40541d0b90340d64124018010070040f80340300100c103241100184141d0401d510f50980700c0c40001c3d0001c041610000307611185002e0b0081090013960411812029908224400794079007000f5526000810714000000d42e06103050801d17240c0c4644c002d00100d04000360344d0364200003c40c604043c95941c402407440a40003c0c9540c0c1420300c5281d007280a0030b0007140c9040581c200c409109621401c800c03d008061b0b00559121040d03841d803d4000c9042043c07515410049000f500c6540c21602e82800c0000108000c04e80016800d40138507401e9801200c0d1380086100c035034840d4503901428640c02c5e0310140070803030882d02c0340c0a016010301445d84100700c0d829240344e080004103251170b144416519075050000794a400e2100c00202c05100709035645400e43c5000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 337792284 1250 337791034 337791053
    0x501050f0f06131e09020c19020d080309010914061003150609020309030406080a05040b04080a03060e07090f1703070314040f090506030c150f2104060b0a0b0f0a080a0e070608010f080604 82
    0x4600e23901413801d000802e654070140700a901c1c41c1c0109117640d8a0034065483ca01802e080c80303042d9102140800142000c42d4001542c030302c03030380c020346800c3c4800382903540703213a1608240c0c420014070340d40381c00340071640702e03081d200031030042108000850350340d4074007000502000c030000e00350403505140070104008540d1120401c0c2d8070540c80402280c1d1071000a00540091407241c110000e00c0c0142000c00c00c00503001307610341c001c1d10181c180765809682d071401e8425154200002c011001c1c4c2051003000d000078028050340810b15404c04d54907043c0f54031107501d032400c80701039480310125540350402c0c0a0350303041c10301c01125441420b03910140a1415010703461010710403141c4841d40142d0006200d00d040314000543e1900c0d46030ba5000c100542800c3c205034025155101500307115030040303800056142c0c40350049a460808184e800b40c24158950016248440001c0903035a0003500d5610f0041148400d00948000d003c042d2500303c1c195040886a600f40410b07a000210303103a104004dc030011510204 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 337793534 1250 337792284 337792303
    0x120c031706011b0501021e041a04120f050f0d230310030318050d05060703060608090c0d1a1006030c0215190b0d030509130501050f0f06131e09020c 65
    0x6080c0ba0903d80380c2e00a20441c6d800d00101c07c48092084e43d8211940d00600071a004208003100d41e901404011540b032103140b00300951003460080007400214403800c10440b00c0e000f50140c031035912540101da410324108141120009804800382ca40d084c90b009200207009100c511024154a4024407450000700e642c00042e05100900001e4000c10310100003880182070050310b400001c17a41c510706203503111810303a44580030030b00701500451120b12614183e88100c1300704005090001d030718014002e00c9507002c08191920f10904046402040c00301000714024984030a5000e412481c024005044640500c2c0210840d041b4180405403ca2900350f0541c0240c5070103030540038142140000001040b01140142c4c01c00b240c000c0b00014035802601500c061017068400c1c00c020034680c03840c1c10413148240a03440d40100228003510050400030000c06860710060a0303580340580c220110a956190395104c090306003082c4034880f601d9801e0300c480794000d00d81034005500f4030b501d1107950b68603106c901 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 337794784 1250 337793534 337793567
    0x222051020010c120b0d031b06140c030603060f010b04060809210c06010905130f02012c12120f030a09021804140d0e0609010507120c03170601 63
    0x750141031141d6020240c0c0c1114140550080180c000d020790080c1060041d07500b030100d0589041705208250600391820080d0a40c569600c0e98003071150b00844140400d46e010556919503940002c020580d011075000b030142d00788614040d1a841e0030000c00d450321304024145445140c00f00010000717025031406440541d1610305211005903a06505585450f4030400c030080281941c084ca905070701800030081910186034016155030781e0701c0700c122a082e501c060f0b9101d080080001c00c0e54020401c1d01c06414002d500c1450481c042c43e2a48594a0100034843d0b07000c0d00605002111080301d04d04071500d59a014220400b5004201c0b4104108445008038542c02400e80c8000000904081c0b0541c42108500ea0080c01d02d281c88d400d69005043e054402c480c11601148281001200f04000140070354054580307130307030340740140e8080c805002d0b0075045007048c01c3c10b22201740300000000c0e4013104610500e54669590b80c0400003076007001010002034800038001000c0f80018443c159134800501032010145 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 337796034 1250 337794784 337794797
    0x510031e050c090c03160309030905040207030c020405010f0825030201030509250e180c01051c0905010f0b0a1203081b0d0c0915080114030a0503030a02220510 70
    0x3241091410201d010141c240c0c0209104100311454a81001541c06481180e000c03084142992100f98110b0307502040160103d001c801d410002c600d4290000c0101d144240340003100201c0070360100c0d05555080e0400c5004641d40003050182e41020042070014550710a02806000c080c0b41741030850301800c0c000a81015100c40014000403410400010300380c40ca090328440c00d051004412307200b00424003d0441d4040400040740c174602c07034503811985040c0701c8405018103407060030054900b46e20803e54410a0320036070041003014015403044181150142c000071651000f90030a000842c0c0c04680c40e9882400d441a0a1100202d201c17a00e000c01581810200d0040c0c40e0b80e18142041c408002034442000c200040344204180180c2140d0300c0900b0310345800b07001340e80741d40c411007032110101d48100008201c040100030520145155542c4981e0140a0300d0a10078580c442c5800c503481110301310501500000c042140d149041d401e20015104d003050140c2e0981810000341c1c0c007180703018201081195 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 337797284 1250 337796034 337796093
    0xa05031602010603050604080304050c011e20150105030d050309030304030503063d050c0c09100b0705150a02090a030b180d0906090b030108030307110304030206070f0501051003 78
    0xd41c0f1100c040c5070041d0864035140340c18a007400556008481c204c4082c020010300e0110755016003042e07120341400d21512864119042c83c12a55080e41e0b007664509030ba0f403100004480b0306d0601c02c2200940011001c80c90660400301071524003840107201404105c01041044030528020007601d42003607152402650b00d032140400100481907000810100d2000c90b1100c010f00051340001a000e03240ba241c004072142d042d01000d5031140a4446031140c150050307030070503940d8501100d0041d40480c0384012044840d8440108440e550050701048903070354849080d5074a06d600c4d0245555101c0303010041585032445503004602e2421042c03000a01d013041e800045a0480c1c4c24522084041d440f98084900d200b0701c5000c010b01d50195880743c800070030710400002c605a003240c0708984c16248604011440c2d0385410305c0480c1c1100c00f1800302d10484c00107000100050356400010a80c1c603000b5680c12010035441c0c1800ba08440c0c0260400303503010340280c020170008826407000000f40ca14585a103620070b4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 337798534 1250 337797284 337797287
    0x403020d111609020405100c080d0b010504090516110703050d080408270f040911121c12110307020a02010e0303130305010c02010c0207030b040215300702030a050316 73
    0x155a03528000900024010200c3c600b030b030942c040c004403001128440802e2070441012341e007410f60303100003429940d01002881c521007440d4000b080c1a9506240483c50641d65071981012168107407218089001e0303840ea04c0c2c00d4160321000e450b5030202d0540142c45920319580d2015603c003012000a002d004120001400340702e01181034801591003500d850740c0c80004228072491030440601000c0c0702d10030041c080e44070303802d0510502e01c8480d8800e9007207428440e084104880c14000032900101442401038010b040e4804021032405c9200780d0300c0e9500c8504140b07038094260f6140c43c00c194103114003482002149075001890383c0c25550207007440a00e0b0b03010440444c0c110b1203522420744d0300d404842d00001c1002015404003c1e100b0581e4020864520b4413181242c0710580c500c000b51581d0030b07007800300b07000d40341400950400384d00891040d0f1400b014000c1c0b20500c065180d2002d501074891002c42e00340c0c0b00e403c01d00d0b07540c058114400f6601d4051803100203895408050302030302004560741d40a070442c6c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 337799784 1250 337798534 337798543
    0xd080109050c07120c0201020709090b0a0b0d080d09020907031a0f21031c020a050d0b010c060e0a0c08160306021809010308180906090f0a1509090b0105090403020d11 73
    0x15070000941e40d011044c02c00b0241c007040f100c1c041280180b140000000e1803500034402c0702c0007264460025055525003c0d01d4402401e20700104680c000f0a2680c0e00340091820f100800100075006804201d010f0716004104042d0b500501440c04d03d414411002402d00040401c68408542210101c00950401020454010300c442c51142c030400c0d030b10900100c801e000409000b81c04014115100c0034420601c040c07050f4050701c0f030002d000c42c1e0140183c1d41aa107650b04803000303041044c5018004052142c5500701a1031f45030611006c80e8112030901c02c1031008003140800a41003150081086204014841c001071159101c060b24003030740421100f502c140e4800c110807165400030301030681940c403410524483d80c800e056041d1505c0c00100500c1043c1028040281319090081c8011050350707445900301004c1800030090604540d07a115200702001c0b01c1c1503603001401c07400c080085c0010700c034a01580035020607040180709503048400c010021b80d0024024603030704e02500e81640e0106400345041e190 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 337801034 1250 337799784 337799797
    0x306010815060d0e211e070c0e01030308060910050d0c0b0a0302090a0e0112020105030408070204090809040606020703050a1410050a020717090f0f01140c0d020706020d080109050c 79
    0x1040d400a00c0c41e107408902d030012006070413524240c0e610001a0042c014170064030004040d1910818010030481820503099140f103102c030002464034040d26039407081d10391400d54002c0903a20201000503c03d15922244c000d5200c58103540003002c3d41004131000603807068074800c1c0d500c56000c0802404c00c22440302c240c40014011184200c0e01c3d40081c51000d4080e400c0740c54018050080307801300048910306502442c0c1281c90042000d0540711064004480d00d0780010815106000c0401c052001a192440b965004601641c031072034a8604240030403040e40c4441c0e100004660080606202040c40407030391000c501d5000c5c190b0101503000d40030050620070b180da4600c07001c41ca42000c01c66400303491f07001050428403e03114010b01070b007280c40c1d0080b18000c80d01c205800c1500841b12074128100a007000c401801c05040040310001d02c00342e0701c1c076240e0102910b1010354100c6010080c1094042102d0000303892180043c0002c048140030003481280148142c6101341d80ba43c010460185851049594 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 337802284 1250 337801034 337801039
    0x1d060a24080106031406150907030615080604050c07030e0f041d03120115020c1003020c010f0e21070303090609020a0605070308100f03030309151401140301110306010815 75
    0x40306030348014890007400780d0320007560040101e100e190070325200450440d203c0c000e08584040000800401d000341110005c051406140c1e45010105942041c03c1a00902d10340355500d203821403810b10107000c190f41c3c0280c42d407840c9c400140112400a40c112140070451442614190b84403250300b4005070241405c0f00c4248144020641003070302d070090100080c14050034182c0982010390742c0300e07055a0707482003101c5920010f07000140c41032141d107004003404220800c14640035007040d07094043d035421a101e035034070403d001d1703518000740bc40544140811900301c00c3d01900c0c4043c6038032412800210303220315000141059585da89940410043d640300311051500070700140d4803d622480044e145600a41c8190b000c1000e0a00040750810401c428906942003038107200314451442e50240d02501140800f2104140d8103209a01940f0862040494410b0030126000065162000c50343d109903007810540c2c060303414541c904000303190300303000ca0b50086028a00504c02d07607070f0510a80d921a41c90790343e059 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 337803534 1250 337802284 337802351
    0xc020d0c1a0309010e033103050105130c050315180f060109140a1a120309060a09030b01090209010c110102190516060c0c0b03090f0a0309091d060a 65
    0x908500846002d107224464000080003030342c030f002e00b103680da0f4020700300d210301d00c2d04c00a9030440b480d030303140041c0d6141c5202c42070100606903104d43e6401e095a40071070b0090396042071800044240f00d0702034100e01c02014190090b00510b206101a0301301510010310b140b11801c02204080d81c112010064581c041c403603142998099612000c00d00c01911261040444001d10b141c04501059507601c207216810420703030640c101c01c00d40042031207984858400d0051403400148507a1409131a02030081590b19072664a02c00823500b94607044460301010303085444502d106102c8804966007000b15006203d40101081280007a940c004030720380507103001e0310203400c003014581e9420007100045981c05445c07417007541e0720001e0b1a00c10859009119281c0980b4000041c1b00030000000d800b802550402c1400054880000042040d82e141032000c120071030029082800c00c00402c1c456105030768800703411160f86c1c070040214014250345c0700300162220502594404240c2d1840a40078064280c00203100580c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 337804784 1250 337803534 337803569
    0x60402090607051b01140a021f0209040908090306090f0709020d090821060f01080f041716050709052703090d0507090c030209010206073b0103060f05010c020d0c 71
    0x82021012101c5130902207101c1e203420141d41410306040e68000b0381a94010000e034000800c608464502141d041004164201b00e120b0154649000b140d00c080c0c020714550385e940c000c0fa014940b03040320050095100750000380c2220301d0b139400400c2510459407100300240e201c4801241190080941c0b4400820754000010401912016140500203204100065451035512202801807040d411894103001596041c0000d04000c060100550098041c10032070517038503081048592603500900103000e0806204984804129003006980d019014034a402d129a0501d4454941010851b0019254000901c40000742e40d840410940b8110680280306168102e000e003802c5403218403601401d0107a50404240c100c12070b00034000c1361151501039004010a58448804881411a00340d40c00b450118450541156031f12800c0a49030b90071281409111b8030a0400000d000ca03178441d03001444800c0252020007035aa00b01180120458054403e042c07140030a1030070941c0706015401c04806101000c480 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 337806034 1250 337804784 337804813
    0x1c110a1a0c101a010207051009300f14010b010e130f15080c040b011b06020d05070f03050f01030302120f1b03070218190b0418061a090f06040209060705 67
    0x40010686080c1c0984140c6ca440d00c06001081000d8a42c5801150444404001a0b000000481c41c11540d0341040f01000401c0314140d1031418a02c103050301c0700d4860f121582c003400800250824a00040d0340208403003640303040040c044082620072644a50b10300700c490f003c0300710a600074402d150721003442040003071044201500203203040e008a0210b032207030500310b000c036007807910941a0b40e040c161203000d4041c15042001180306140c21040703c8040d02440800c45003051406030741e020b48041d0b207030b8581400034540010100c91000f41072280c3d120380b03034004101280c3c01040c40081362043c1c0d10354690310940146c1002c00c0f881071402d245032a40f40e88540154001c40840030f446400e100315005040114143d0301143e020b441643d40c0e0f01b140400708210030300140c1c11b62109415210141c03012a80140d0703200c400f1204640c00500b6142d9585136012081c50081e2103021100200003220811100d061003049100803801c0180028081c55000407026020340e00d91042e00d1440f83d01c075040354103c3c904041c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 337807284 1250 337806034 337806071
    0x313050d020303071404050901090207080d02070804051503041101030e150112030806030304030515060d060e0a12020f062403030d1509060b0a1202091c110a1a0c10 72
    0x404000003605100703c848081c002c4d071704072011103000410b0304841d41d003000141c800a6019a108527288002003080603c1d08500b40043c2c80307078502540c440c035103661424040c40062607141c0720003450383c402002000002002c0200d00c111120080c0303400650840840f00603460007003050f03c01d1030020b0b80580001664501d8200c0c1ca070200c1d1280d51a00321907201e5409040c2c1c4d9001d103000007003d68002c0700400e504910a070082d1fa910050007442807464406070f45549084070004079600485410410078001404901040c802c04003065200400007000021401a201c020151200c14440281c415240d000058411000c850301001010340e66681910512500104821031554001000034640010071110900c01c2c202100c1c070303101c0820300d46800000b0483d0606421082241d03c5036081c0468070300c9460f044201d48034440f40328100c1400c2030940c200920241032015465105528903a8140039541260320407600756500450341c545c642085039140c6003401c140a400380c3c58540ba220000100c00807608 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 337808534 1250 337807284 337807291
    0x22020a0b0c0f011b0f03020c03040f0303030b0f0108010f030f0f1e0618080a030b0301151202010e0909070b07061b08011809050c0d02010302040b0f300c0313050d020303 74
    0x8000300140004c150400400880c1890a00d01190318800c44a910754000d030000d003142c00b1a001600c0c81e1640358034000c40445a141c0060300021341e140015052030030103002c1000c82607401d00344482d043d03142c5201c56124003402e000080c0741f0140714982c2c0d01000445110240b240d0392021300c50484a00803ca980c6126003c410700b5108641800b05226a403403038200c155a45a401c004460319000c60b06005601800c3ea900c4450f8141d0b40e81c10403c0c00800c810b4030810040c041026115085503c1800018100c54000750034501c03a40c2d0348418804a590001082006c64030040b06c03513034a480b002d06111008020082c0d000a09003034170f000b43d0900662162010b41a162b2045902c400c070134041401d001160160b200007403142c0e01c140070803040c0c3d19245441e40d005a105240151400e0389070004102c00b034024000c0480034200100315000007014aa01d0311140d8003540c10018040e64041548000c801c0014041c0102c0b120b00201040240703074140300c86c0ea40e8903001002c0707814100ba880c000030350b40d52084 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 337809784 1250 337808534 337808563
    0x3050903060a0605031e0a0b04051b030610090b01050708070b01170d090501180504143309060a12033b0603070507140a03020705040522020a0b0c 64
    0x1c800541507030030324800e410660301d0240003011040c3c0007510510801c2d10300700700c01d1024824928081c00123443e0344206440303144034002402400112910210640048800c4103100742c11140070400e02c810281c6491f411101c4001e0041002040000180e5061043c0714000d0a9110001180c10038400070900d958125001c02481840b134260001803c0d032507039919026400003802140b0100143d601c1520b0848070300414044100080e035440002038100d644022484500c0394450040120584c00c003164900c600c20710040c0c418010244141c1402104046d1005c140306840c0400810410345400060001a140c00712243d000c4a901d8200603103c03109100c46400b041c01c041c3c894406e41d1004451038030010b00322140316285100084200100d0b40c200808500c02c005080c41104003060341d0313003156000507881b1000b91610818906009080070030542003507024904220030700400d5801842804c05006d0329481c14074001d0038610015908203c03e074416120640f0101e00480c00880101e00b144800402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 337811034 1250 337809784 337809793
    0x10b090106030203130209041403070609050610030308190f0f021c022d0906190f0305040b060108040302010603170405010e0a080303040201050a0c23060906010803091e0303030403050903 82
    0xa6075400c806a110894204269880c2c282c482c0006041c01544960018410780300700349400942c1400c035103507800c031420645040d82c4a403249000e04c00d0500289800030580e2060705070f5a401c2d510090080c40020b024000540c440c91051842544140c0c07044c0140f0184030f4050003200d154021b44d40281d013003524121a00703141041c040c1d01028543c800c94441d031415036a501c1d6685006001414480c214145852007200d04200200407965050700604a035200d20500301e400306900000145068500020041454070305030902c40880c940702002e9911880c2464408802d680ba440c1c201d01500f40c42d88010a185001500781d140500c110000d0410750b5030130f131f0322048800c0c080c0c001c00505100c140301c0c0031500c1d00100080b6015512850040c1130f51460350a1440d490074407039076803808040d41c1c1d04140390550441e1003603100040c0140503041e000000b102c0181020350424025070b4603803081840c5c0503c40c000402c0005101c0b40c0840c2c800c0814403004050381c1e01c91074a42000f8190354000501d8521a004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 337812284 1250 337811034 337811039
    0xc0a02100902130e0a0206160b09010213051017010b0901020f011a040504020d0b010f0501080c090a0608101a0415090803040b090a03020d050109020406050d0b040204091b08010b0901 80
    0x80c80c0c400e50329001d400410f5040001c40711043e2034000d01da90119500035000d00c0f40c42c1c6016841700c3c0000c0c800701340000301681d244402410442c5480401802107d91a40100300291003000901084001d5030400c984419154002c41c82c00d9640040e50211821aa4841c20002540500d010f000c2c4c0300000003078084c1e46803030701404413603405c079a05110445540300c40344510142c13a007419404980d10600c00f60040c0c01c0d030161904c3d00120701000345d110240300903a00c80300b40040e50780404546d400c40461a00fa5040800380d800060b9007110394094070f01000310b4240040c5113040b000410b200209201500740e03405201c0100074000c3e5a120b40036100f4154008d602d4094094410306002c011030361a000074606180c28101040342da81e004503a519480140c040021001d17a84090700c4480c16032007000006404082d5105000945420f5801113203d400d141050740007042c55200490340c030640c1107400062031a0145002c08550802144111004a02803008221490150b12043d50010221802e01d002d80c4d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 337813534 1250 337812284 337812313
    0xb0a0302040510030c0809030a080a0f06051809070501050f0904050402150c250605030106030c02070e0f070801050f01020703080309070f0605070605010b04050a0b0715020a03060f15020d08090f03030c0a02 90
    0xc240f4084000190003c0000bda803117800b82d110080c05403400c800802c031542d5900000340201054000891301d40c84d207001380300d50706004202c814000c2c034081c03e2141c105001100440d26501403102c03d40e014940300e800050456456070411441c0e4140781041e182c895001c081d0083d40c0b820441d8600c2812031004c64002161080b071440203084444943d19146168203244044010f041032003404000d5110f0b40402090307418040300d000d80300e110001010802807401900c02890104180d101500861154003a0003036030742d000c690141500e411010f03480c0c0d25122110300c245809050340c808204a5100e44021503019800401021a07500484061125980354003520103e841140320b03e0b036104485110410410703800c180540a224025420504038446503040002641d11425480c0c0c002956001d003404007501044801c7c02811414080e015919560640655500800c051050030b02c000100001e122f10741c20042550b12410700c9054903140d060000403000581c00610740305016019803e038002405 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 337814784 1250 337813534 337813537
    0x807081203310503190f0c0804120c03020303030a090210030510141207170f0a0b0a05040516061d03012a030204090908071406040c0b0a0302040510030c080903 70
    0x1040011030641558807000a150942c8100815440241012a80150105070180058801164011604030301ca40c0a20801000d0340c800c400ba00061024081100e800b061451003aa0203440850401c414282514145414108100d51000707515200000c10004420701d590401ca041c1882555254007410b10b0b01c000750180c0d5002c4401c0042002d10a070100204024240040185240501070100501005000340c1c200881e941000c40c3e40342d8804106149030008100105c21800802d024001014540d44c034000c0d0110080c00c3d0011a03a1034001041c284a07044c840501000304810120214030f6807210040c22402c0f4414642100032074281c204420380c1410300800401c2c110f900d41c542c1d040c0303020500420000101070550010968240800318110310a4820340c1070550060f900070380c84a070f645c0781c00e52045200000c000440d8200b04107000006802070710b01d4050ba20300b4204c8644440d2208800c60007402568000c41d030055000111041013501035001c8107501c2c019507074210082c0c0d90380703179141d5030f9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 337816034 1250 337814784 337814791
    0xc0409060e150421030209060a02070e0c0a1211130807061e080406090305090a030c05090717150303090a090906060602070506090103051b0703110d0c03050a23040807081203 76
    0x641300f548802c0c01460f03480c800101c6200b00d08006050218043c08507a00390418a0b420001d0b9000c62000d01c04e00500460702c5074008650704149140c0101800000d140c058002d501a840c59120400b00c0940416082920b800100e1143c215030110f60304d1000e6540e4400d01d11450000c5001001007032020344445a00c1c41e41222030f5182c0c00c5041e2200c3da07c1c48010194170000760200b203001d100e40c603d03664444891030001d6000c0c030703180942d55040c03000b006a01c1c1c90140403c0248641a001c68050020900800358800e2010805010321042440031a00f10320540300c0c8250310a4200b000400e007242d05610841401d8011a02003021903112681669540c460f40a4103510003018070480103198802e030001a8000c8000d610242110b00c100c48e00f2070700d900174100480100b01010309102d00303040d0800c003140e080c240703900d03002e03141103090345015019224003800d00d803c03c40124010740000181e562085100003000701125645c030751f54005035071602c1d100e0090b500135000b40e001c004610100d05003542d01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 337817284 1250 337816034 337816043
    0xf070b1803030c220e131703012c060a0e1e0a020703030b090405030906090a150f1d01050415020f07030c05040e01331509090506010f1706030c0409060e1504 69
    0x141d4840c50803040243c441b120b0101c0e410b0200809803c009a6284040c5000b4000d400c80007019400003050440e40d024010345800e84810304001700043d9030f8501846000f01c409c0d02c11100440d440d102c0c61050f1000c0681070410008000b00b00344590140c49a000b41078079802a130b82040b00400c00c104015600e40f0655003e0520b6109001c00074080c542080140034842000b450403042d42c0d9108507041d000c0040081c980c0226040c132244543c0e440d000004405e81c0380c00c2c0c04038a0340c000c500c0c6001800b140102d005083c983e2036400408203a19000700800000f008085003120802503a80ca01001940d1040c020740d40100c3c1010701d4502040740c1405071342800341d586181c1030040c07120810400450540481c454017000d483c00300c00217105510191040404080d50360322600e0504000c807150075a01c02901d0f40e4104074201811800840e40000d003546042c00700c04618080340c69400000380f5094000c0200c40d4010301d014005420040541d0040300f00041d06000c1d5884100203486200c5420340844000d40b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 337818534 1250 337817284 337817309
    0x180509090d03020c070e13022e0c020d0b090c0a15050f0a020a080f0d05010e070c110109081002030103060606180608100b0301080f0f01020f070b1803030c22 69
    0x550719402034002d05580003505003240ca8440d6280368034100f40106940b20012004110f4064065090602c003000d81b0b07031f0310142c91000038100e801203014561502c02d80d6400300149840041c0855555100b070301060350f042019003907a03052595102e61140e00800a07113105106030359000a15260503407100084480685650f4108140c203209030401d0750083e007021085000e03140c60400018401001b81c01002080100d4584407106c1044843c00c42c1c0068022024000c0000f0404c20580c1c0d20201c100280e56000500e181e1224000c0c00594010b40170f078101201038050502c2071882c1040c00d0b80598120303030142c603007480201d545000680d0350040c1e02510344100030b00d454091224500030680550080b070004881250240e84480c280303900c0e00281c005900765045054001100042000070740c100c409030000841c60845101800d000900c50f14800500d41510100001e9101d9106428074140d010070300e007520350740c2c9004040c0385c50681c00700c03515048090b115170142401c00e0010322200141d402c84400070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 337819784 1250 337818534 337818553
    0xd0c0e011704060e030a0203031b070b01170c03010501080f0601240f0908010f0209031005010b0d0b0604172506090b09061b010c02010b010302160618080a18050909 72
    0x40c0281d10000d000b980c0c0719440e8414040041c03003c00041180d504107a025507181d040091806000305141055034400c80301c1402544041620085824110345101850703582c54855000c0050801d40000842035043d40b0741000000e04480103e00c805004a105d010b5034201c2c3c0e00e030380804101c0c0055852005035080c070340c0e0f000ca09842c00751080d41002811420007107001503480990f1801c0d0b4843d401d003404029000f00701d0780e045c1d0400300040c00f145191244103110a60522070003109034004c402d84124803d444182110494450004890280c03206010409000c4010681980d440d10010700c44a0203003a06c2c00110003e0041c02c030f140095070303441d6880500c090b00e030051a10041c3c002604142c0d000b00100820203144840c101220f20640d01480041041c3c000584082d00311242c801c0054141401044001c0a1600001e01c00003400d5002d00000341541e40303621202884d0944000080c11580006451658550080142e06c0310010090807800c2d4244c0303a50900000f642c042e00c05458a5104030001c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 337821034 1250 337819784 337819817
    0x1703090906120a0f0c06030506090610030905060c12090307030206060918030d05150105070c09020c0c1c060506010e03031603020c06070303141806150a0504060303050d0c0e01 77
    0x825041040246802e079540c451031842070800d006903500302c0755100005a0601003020420140000304014102081f60f0329150b40802d000030780003480244910f02502d400c0112034000e502041600380c015003110722510b40384007500188d60003030803100c00703103011400080c540100000880e159207605034064402500d41800740000311174050982a610300c10380241c07044c020f0b0200094007641501400c040795500300f4000e900301d0311071800c5549040040802101c0b012038a82481c90040300c8021a00503529040c0c041d034541440220103404e9030040e01d82c2d0340c0840d0101001003002410303000d14004c0096480d0b540056500e404509821505070700144491f00e080c400318202010424002d00603242c05000400000c0c085500440040380401da454200c0724000e4030b094105a804034245100c4034000d1140d01809039074035802045214242d00c82c7e1100d84082e1110a500c074028540030f1300070b110203a160316000d460f0b50420b64141c0f420615102401500911a26401824400607110800c1010a0002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 337822284 1250 337821034 337821049
    0x5060f030604020712210e0a14190302100506100c11040906020307090e090c0604150e0303190806010320180306010e0702070605181210060b0d06170309 67
    0x1c2240d1060b400d11009010812017000040080c9040e50b8002c06034200007000d000e210340d141a2075900070710b0201c1c1514000c0e030000750488100d03040320088118580031210285000c0c80c0384c0403a1485e0260500301400c25400081552800e415180b082c020b0396183c1040c0702640004199101c0020500d45600001c42d00114600c240d03250007400208001e00340d40c41d404181e80c81580d1070000100e014004009030140d94500700d401065003000f070804440f503a00014024007590080240c0014000c0350f22541030301a4816006201c00607068030380710089080825003600c20000080c0208485a000900030740c032070b21402401556070703031302000c05130601c01480659030040d2007001d603610a101080700c034607541000703007c0c0200300b4022011054a0071440090034081a5480402801014002c680e5004545d426482406d5403e1718800c15105440340b00324501003894807480082c03844e0244c08a81000c01c500182862008480240b02c001d030307502c0c80c003c0d2034080101c1118140d0001d000440e130780d1800c2c26 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 337823534 1250 337822284 337822291
    0x524070303111210231e03070f06030203041208070c0602090411030901021305031b1c060207140105060d050303041e0c060203030109050f070c02131d10060504020405060f03 76
    0x210b0345042000d100488501c0d00d80036200124080c400c0701d0100004222020324403103900c0116444000b00c803800340413945103410a4136588400941e4200318103181c401f08840c00c010015901c1c2502d00d42da42d0135024000f03520640f01070342d414803800704c000c0040b8061181c45019007419aa40301082c0c0c10741d20f0f54402500b04241d039690084d21160b903450100e014202440c090203e810005139220540600e4481c02d0112781c0c0300b240250004680a08541c0580030400e130000c0307003510340015550b0401c00ca540c0310340341e503900240a0b070720100b14a4184288800e503141092a07420081244e51509020009210403080c4024002d074410000200000c11081c5074280d2075114000700003400e001c42d0341d4500200381035046000180d1020004105000c02c1d4080e094010030b068116005c0f9090095006104040425000c0c0c058643c1c601c1c0c2d0b01c4444401e612181e0138800391000031140c6841d501c01c0c00d441e1100140010103140c106480481d031460a84229030440340d00402092070301080220305500b540000307 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 337824784 1250 337823534 337823561
    0x40501060902070507290304080a03060302060708030609010f050a03030516061b03050c071a06011403070903030207050301020c070513020c160315050702190602040503160524070303 80
    0xc9000040560301800908111481480640140d40c1041c07080060400c0c8440e202001545820708090450b03421400c0f6a00681c021107031650360340341c9a00c1030f80030f454a507000130340010002941d00140041600a18003401e81214032180e180d03039803036107620808dc4500070154480310b0011304000182c090b0000300b004140c43c00e50540e00b00182d440d45404c8401902a01809003010920303044802d41c1881817903032041c40820241d081407001d031603d4213810303440c019201d141843c14010885980c0107001e0003041d03100e198009a0749141000c001044000d40b80320803009485200c002240030302c0e041c02640e041101100052010703a280a041201902c1700d82030410290785c0c20096406615014091003503441c121610003200203140d45801004469540d12441c0f42c1807810050020140e400305076000c1d401180f00d8030f26840041402d1440091045030300043d45442441c852440d0b44c20f02c415007030101e41c41203a0010344030030890030035945891000007200400b0820015400040e00070390014000c1480e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 337826034 1250 337824784 337824791
    0x60e061809010609030308101d0a0216061d0a15110d3621030f02070605010812070506070c03030f02120603010b060f090f0d080d02030402130e060f040501 68
    0x2080d000c250100820f8011800080c0390003401e0040c5604211096005811001c00160301440c140e407041452031000c040c0c502c0c009800c070114101d200b01c0d80594407000d18401514500c043c50740341140040c0400129401d5616414541411106011449811803900000d04106968801070054000c003142441520003c1c0c0900840785107080174400c4200300001d082e103402414a0044030b181044201082c22285154945424000540014650b11300c1e040700b9141c0c3c0300f902c65105c5066011f000036090000300703207101190910620034036400580c1250412070a40d0004240700f100201107105d0540702600325480b14003c00c030b8a602c1038001e61f00e514000e01d000244000d82d03004100a03070307000c1201d156030368074210103004192a080c4101d500751401183d0451601e101200c41000303900550a80c0e61040302070411002041d10b584600200640d80300e980996100c6074404984003c4d0010740b0309034090b022800203c1e1a0310051f20944032806402001040a83c1c0c408942c01c188840040017158903548 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 337827284 1250 337826034 337826077
    0x204061407020406120605040c1418070201180b011503050603071403010b1f0e03070f12080904090f0b0906070507061d0d120e060f0103030507050c03070b1909060e06 73
    0x1401d010411703115118802c081703160309180c200300080901d1608941501d4401a0b9403018907500c000014510030201e80404c03016584000c0103a0050001500d00781041d5101c2070380c1002c200c0b040052605130381d5814000c03010040620b500303c0883d401110301395007603030280301c0500c0f492800105a0b60346813401000030480c00090004a054220240c000c03c000410350401f101c281c581240c10407403401002d4000b000d500c2e2800c44485000c8089204860103c0032a0402c101840204c0089609e01040504280404081c40c40c00090034a1000300c1a01c40769440c1d004540000ca000c1032013401209540d036228103007401612004001e02503426080108280b80e000100412030501078016042c1403034860004c860b20401019081d20884028040150450320400c290910303200003035415260549885602c40c0003500d40fa6148c4040c03012100d034544100e40c40043c1c400c8124004004018031000c954843d850803400c2030f201c041300b6002e0580411405040080c1c00c1c100305028007104040c0d004800451407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 337828534 1250 337827284 337827299
    0x70f03150609090b0a140702100903090e010e010e010b04180c0e030703150b0301020316051b0102030c0a17040210030515040527071202010c111f02100204061407020406 74
    0x3c00c400c0e8201c13240b40b2004100428044a4810400c420ba8114949009441c010340c00a407035241305220f82e030409030b8071600e40091512650510b0054043c00034440c0040d6107a4400386400d580910400400c0301241001207882954281035a084030307082035509242028840c242c00251610b1200181080b07038140c14280c9542c2c0c00c00400008500400040828081898154081c1c03070f110b07040503000b68010030038040009072056041d407003030700c6901d04203468a800245a0255802240c941c00d003035800482130043e000e0007035009001c0c92040b40c5594640031802001550844021a8041e51040b5048440344041d0300a81215522800807503480c222a94400c0002d4101c1c2c0050b03811007207100b4000242c0c070a0081c0010300b01c01020400c0000d10401c3c1c605004d00c01c5500d04680c000b410080c0314560340b42001000301c9640c070a0000281308080da100c40c09010401d00103902c20740d400610a55000f81c0700e5800b20700c00c85082e98030365a6407034040d00c9d00c0205505240d2203444220b07041030381c80030002481e030f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 337829784 1250 337828534 337828541
    0x170f13020d20040204050307170a0b150906010903120e0126040b011a04030303150e0f040c06030203010506040909020f03150a0c0e010e010e030f06090d0908070f03150609 75
    0x61180141044818446001005940b4510700281c000e510400c030510241e50009405412113a45650b002201c009044100307003400607072070b0001d0505d460f04052103003440e000301c4244030300340c02691100d0282c2d540400440c0c1c00e64036403201800150600f000d80c01c1c00d40c481c8451031211401818107003c0d011100326032852414500083d4011b910690051004112017922211300420314140400041d0100782c2d1001094881ca100043c20325607260b1040310268090840f10303004000c0b400241c10240352040c83c03254140d200f01d904131055036502401180450080c82075038140c0c1d401030308290809080000050046c010084160ba024030280080300256504000484480301400c94074155801d01446400503a9009541d0f003080c0501c00c008445172340d0344100d0b03014003030340240703080720120f203814000ca800c1c00030054800c21180628410841c0700d100000701d4160301c0310160b640e4020143c1d1602c200d034541c229400342d14507070250441e08101203980c00d090012864454040060040d55614204044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 337831034 1250 337829784 337829809
    0x30a080a020102040527010b0d0e060a0b031c09140414070c0c080304080307080f0c1b1008040b0402060f0c0102040f03031106130204020d0603060216050d170f1302 72
    0x141e400240c1404141000c0101d01b001c01914001c4401195610002134103007001405400c4101c10081901000000340d0b0308400040840c0078243c03a8682400942d500207091703c100803d00920400d82c0c1004410302640e0119106006a42c4646605040c020f81020b0302d520700e02c043d540903494100750240246e200c0150343c041c0c00e203521140400c50161034841d09108032980030300595081403108001042000c4100e03000c103039105a24a90350100c1d07400004203405801482c0402e40b060042e10351000d5016a03207180c2d01e0340200c40c031a400210b4207104070b6843c0000c076002043c0d11050000324005041000c0031381100406041460700b0010500031705400ca030807580c4121021040110100189504406010450120080a001c4c40c0c039045202021070020601d0082c0150360001d0111964075855021703001865001c003003599108240d448884d51113403400c10031345450040c0301054100e40e02a8588480c8103820b225003500c996030b6603c80340c9010100078080300c101c402e0510034400523034031030200300789 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 337832284 1250 337831034 337831037
    0xc010e011b020c030303010e0112081b011a0a0810020a0509180123060304030c0804092409050112060207060908030c070311010209010e090a02040302041b12050f0f06030a080a 77
    0x11035072440c203402483c00c202850310740d0207508200018090340043c5030340030707064500d0107402c0c0040700082d00d4030f9907962091503002d420740d00035440001c54480703041d00a05155a107061009044104c10401c0204003203080c480d100b8207902201c1d156170f400d000c5030090714520b8850f013031071410042d00c030020dd1103001403100c0d001003516500700107010022405140900c170349020005000440400380c04111a88000741024050004000320041000402012507014180c1c4610a200d01c078152650481c4120410703030111003005100b0740104151140d03210f903d041f14000521903100038010b4484000175030100d9402d5802a44460140300480c9a41009501981e280d00342c8944e00c0215050040008945080c0c03030003030b41d004200560071030380d00107102c03a01c42200302c079200c50540391000100c009125950000350040c0c20310720761101d952000c0d00840d1142c1b0050b00c0e11425002e039141010708544d421511560360107014000300d04010300340900b030381c2e008202404071444041203849a22441c0c0140c45402c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 337833534 1250 337832284 337832321
    0x201030f0608010e100e01090c0b0c07090f0204080f06040203070e0a0603020d08090f150405101b081207090f030b0403030f091b0b070506010317071401060617040b0c0c010e01 77
    0x590150203200e19140911244020032460026580e8402c041c2503e114050001d007010603041c0c12900144040401825100c2c0104100b074038400d840d0ec003a421610412989000f044034105005c4800b24406104650040282c2203e0b4103201800c0c5070440094039680400341e4802c07001c00180c13540070000c015240505007240d15189000104042c1e02d428000b00e038000c6800000510b425190340b01558282c1320b0888030300a0602c02c0c03d100b00c2e6050401c0c40c01101380c161941160081c8404d440c0284145c920020101030250f481020a5074241540d00c5a160f181f841d45070104040b071802068a50032a100c1d2030003007a00391881c0340c00b41c01c0da07680040594040040c180c03d88400c2c56149105001801505030301810421b564a49644800b030520010300040540e036a03854503c80d14030215440d41fa40018180b02800441420900030011406501c02080001074102403100c100007a0f40d101d0781e4002d40485c25607a8130703448580d15801c098040d6019648403412400003800c2800b4115074a4500d01409 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 337834784 1250 337833534 337833553
    0x1b0b0a0f05060d1214070f120311040b030103060f06030203060406050117010905030d0c0306030503160c0f0311010f05040b07110f060c0d0e0607080705010506090615070201030f0608010e 82
    0x94048070000b50210340700c1c10b0543c804000040b02158101450700d8181040300d1501d200130030038119807295500091001646402c0c41003002100040b0078401221350354204982c000c0c88d190a002071249010301941c602d02030004000040e401d400c0611400d4001c2c00100f049071780c0c0e80c080380c40c0c000306540480d507a035120310043c0268040101541601c4003000028800c00146880c0c5076103d1040000d01800c0030380300d4512031503030f5000ba0400002140e0000c101d0341e80300071000e0040d00c541d0200c03508403140000c81d00700264108041583d003007960740101801c07004403424130040da800741410b1066404c0c840148400600100c400e40601060f6004601080c0b0b0740440c10104221910a6604c00348554000c2c07103042171207000000e50080070f02c514101624154540800500c081c000e081000746464000248901080810341000d8054070003550340c0d0f002034071840100540100e07003030211040c0311420b100507009076100ba0001210070301d8003507000500680301c0c0030140c20340c0d1112403e40c09075405000700 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 337836034 1250 337834784 337834811
    0xe0c0411040506090d140d0804120201110405040c0e04060807030507092706110304080406180510050d180f021003110301050f04020d050702070f0608040b071b0b0a 72
    0x64021450000e108985858184400100e25004001400f801203449180f003004020340c07400f00c14080229501280c010b03136440710000740024009c480443e004850b610304504094014000d0140004131135200c9810300d030078074060100821415014404005a084104015884600c00c210151298501800c203140c21810414030b407825a61000c20340c0340c600840c2008180c001100c100c050741e01c0000d0f0300b03e01380303080c103000c0041c080714415115403079400800d010400202d40001c4c400c0703c9036500c0b0021042e85151780302020311028407403103402c50701401150440314811001000207004c82100003500c020b0560000c0041101004100c0c2c4c6440c12003110020352038280261200110a80707400e00c0003002c0103040c0c0300240018407400d40190a00c40c00b020461b9201c0e010355000041034542001140391811009603a11814414803501c50080351011480c0c070300c10008a80f040340c0101110b142034640e91001c0302d080f001c80322000400b1000882541c0001c2d84255102c1c052420b9031030200d244c0b01d0840c003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 337837284 1250 337836034 337836041
    0x120f090f120f0a02101503060c03020309251d0702011b0c1707060509280228150513060e030606041d190b06010528020307060e0c04 58
    0x40a00c035800364619403220004502258030b403250941d10a9110361040034103902c0d010000080e901514180a008444400c103480c10404132400345005004201401e042074040380701c192065000b41e040481d1080388110038440024150b003200c03e81003800c55035000c070b001c02140782006001c22300c900003003404452642400740722042c90400508400c0c07074400101c06002050120002854100390311008035071041e0210503129819000201481180f6107aa41e00c2c1d1124412a41c200194400d00c4001402824440110300c0b015406403400c07044804206080034580003101103c0d65084440c0b60100345901521814000c00b0102e480300c5840c0c4800d076014010450298011104110914031000540d6800150107500060142d45c0010070030820051041c4510710f05244031480e00c580244a17021064001311241c0c1d00c1c0c050103290201c0d440312401140d491080000400a0300015104400c1300d283c54a402c5820180310300407a4600700c03a65444070150344882940d028950804000c3c440d583c00c1a00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 337838534 1250 337837284 337837303
    0x120d140708060303040e070e06160201030608070506070602030402060c0d0c03030509120d02181002070303120e0a120314010303031a2d040e0102030f040212031204030309030302120f09 81
    0xa280e0a5450000b01195580c003e51264401060303455000c28005402070350801003401c00504225614901d268454800c1c1003001d008900003440c0c1a4005021000818201c003030f01c60041507a4900007013902c4050280d00041c209980c4010200b00c15154100b08007d20f00c0507407184d4454000001242c20040c00b1244000c00320503042e009015801700541c04901150010409031000584405514007102103124000031022f0300010340312404520603800045400842e803003980c2d58000000d0302d11504043d900489060000c9a014a480c54001040c0c00f20001c0510301c11b2a000580b500f0321030100005034000c0e4801d6011075541c4500400c4844d020310002d080c01c03000d449001103910046225a5218884003404412100300301d100c10340d9555680015041902013002592241842c41011903686800e507403ca2040c11404a00405000c01105a800d1040442551840caa907a510305402418803030707004800301035007005211304600c501ca014074080c9002400e02401403501030b00080c603000000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 337839784 1250 337838534 337838537
    0x2040b04060603091e0803040204020a0c020a03140d0207050a0b03060315040b04030801051e210a080d18030503070503070c1a0103030e0109050d140f070b07060c050327120d1407 78
    0x4008813000c01c502200707c0f0341055064800599906002000321040500b142c0002e60005230340000000784502c04294442c0f10103860156810a6020b003020303a541c0d560382c0b10385908428010000c110741480c030001303143d0000014042d00e40c00b00d0019110240000e0844045900909000501c001d05621000150240c0003c2c0d55007803260090401c845c1c0d4842025080300c1c890030b0202c00070504501c0c0d100070203240c501c1800c101ca000007090728045a031908554010f200061030100b00052090800c040c0840c22901a100c0f549140c85d090012a0540c0c4010304032401e01650f0140e480006a0f54440f03c50340c5100c81d00e05108a50440c64000d100c00040f489841c100103826074180195a40d20302d40c54000c0e6032101150444802506d1040c0c01c113006150820514040c1e1040041d144504030300a064044c455407013001130202e44d00c01607600b400141e41c4007003c00b56081865480d500300d9144280f542d6081011201035207048002d03500541c1c13000071852459520381100c0000c0600c030180051300541e15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 337841034 1250 337839784 337839833
    0x2010b061204240f0e010b0a0609060f09270b1e060304050a05160e0a140718180605130b0105030c0f130b070317160c02040b0406060309 60
    0x28851005040c0700050806040140e2041e20040140201031410110701007140d4240940d80c204214034008180c9084449021b500700854008107103850440b400a031030450300e44044a030705140b401c030b0781e5101da81910340a1115600c804a540c19090f078440340c02c4a104d00da15903510399441144d40a8442c4404601e0041d640403010140b540703501c201d9540810002d80b422900c80c0d4950410900d071003007a00002c0c26601420900340300744002044000203440c28001403a880e03884100804003160401842513100c07400317410128481512403011952445d4a070b08001c07100f59142d01490300c4040c1d1200d1600c042c00d503903440821044c1800b00c02510350b80e81e407140821070f07001d0540029080f031000500d44508a0800101b40ca40c0c0c1c2c18601c10385d50200d41031281415419102c414412580d40240420360109070702d841c04504481001c4401031042c4038040755100e104014a10030b41d912204210202c0e88540c82d009041e1480d112031044400030007030765801245008590400c503c8140b480d20000014200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 337842284 1250 337841034 337841047
    0x62202030a0b180a0c050d020a030c09090c0602120a03050c1c0509010e0109120806120718051501020a1b030b0a050402011b08030106080a0f05041406070c05100207060e030c0a0302010b06 82
    0x805c0002c00072200140ca00840a012520014003607800541001345070466081c4c01191440c81907000100085c0b1541c0400801a10b6003003c0c0d07941d504000b10324071a080c0c01c2051280041c4039802054010000c0041c0324184100c1080250800480505104c035007a940c4041292545090086101e902c680710b000b00301e085416105c03100c481203107241803030030f01000801050203074403980c50381004168202c3c1924000754072402885a6030341a06410b140d520f00700404140307484000c003011302e00080c0c16001000704203910341d11040081c40a00d08050905c040020000205031486803e40c4501034000c1700181c1441c20348005000004020211109021803a200000083c02442260f05660341400c000c07210340d07210f0320100050004011003405003800c10003804100034010802d00c9000086c0d0007568401c0d0399180c41104e030743c2014403020301030741e021040101c5111a158024a403090103042e0100c1c001c80303950760992450740000303012081d0b40d10610810b0141070f8284101414030804a52103841d000c1d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 337843534 1250 337842284 337842293
    0x30207170a0b0c0f0c0f1006080d0807020309120609070806040c120609020a0605120a020a02030904050606040e040302100f020a200a0b07050403170c062202030a0b180a 74
    0x841d214005081000c00408a070240001400b580e00d41210100d91030754074070142490381c2d00e6040e108104174481c4111100c4081144041c080d140030750306100020008400801011180140050914025804100051241d40d01c2d0380c0c10a4512200740c100078641410300e003502c1c80c607002d165440074205810030400d22001070951002e0300201d5141490400a070805400c0000007400d5209000790f100b06c0407407000480c1a044809800c80c0d80fa40b107c80950303a43c4501c640c034140d11440101e540103130010801d46c01646042d81c0099003040000d081c1d1410301da240e10390001000301c161002d901580c171109400e131140180b401059040c003035409080d801c0160011000e00f000c14000001840800b00c0b68100030b001b6400c1168821850700900c40e803146040100b00644180d0190000b03030365460010354404820800c0390229001ca1109000402c01c41e9142c45840c4201c4541c42d41c6032031000c8000c01d0090240c0d070104078858000f40220010195801c03c23040c0c0560419590441408940101103a83c0114 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 337844784 1250 337843534 337843543
    0x91e0c050603072f010203010e16180b070f0203030c01060519032324180106030803010b090a0306050a050601030b031507232205190504021b030307080403020717 71
    0x15803214a031a03c052500340d0b02c40c5602c4e10201c030f61401c10361010000054090032101918000c40b60000302020a007500c0204490306003100c00e14180341c00301e0840030004000040010055540680a4012140302550000c0e06660001c90401c1e050ba4440ca41400146442010405619440c8a14000541c5036030748001c0c01c1f049214900729142c1c0c80c18030401030042c0a00007801c0d04240341603030303030554450340490500129064a09928900d0410140740703040405120303500c2500d0700440d546041d60300e40101c12107564070041103150403142e00c610000004095000d014003c149065020486192900004040b15a11102c0e5442076002c0c48403417030800ca8004060380c112805141160018042800001002c4c2e011200043e080200107180101c0810119500c42c401001610340b010255580381000350203200001e0120040311103038420400c0d4a41680248815100030304000c580800c2112418155007080301d12101103000309042100305a414000e01019040303c60140d04141510803603d55203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 337846034 1250 337844784 337844807
    0x9010e1f03110702090907030b01150503010b07080c0609031c05010302180702030c0f0a0203010c080c03010b0702010905060706090b100b0703030b030a020a0f0602152503091e0c05060307 82
    0x505aa50b07112400a441200884903c103030040d00102103402e025a6556480030980310548014038400000302d4800354100c40c1c400049280c1e940d60b41141d00b000311324801d0b6481140202c0f0068010082104491410300c0094850030661000e561281a010306143c0c8608010300d04621041c6408014001a90350701c64030100040900d251181e1550b800742c0a914600c90280c0c410070741d01c600207598481210004502c1c3c5458402d48c002e00075247e00041c1030b0f504403002c0d1400301c2410300500040c0800000c110180c0070103401490301040c00d50703aa00c04524130b648890016122142c9509408090122012116070004005450350000d14604a960b0503d40160b4000504050b2030302940c011582e02082042042a001004051516030358401d002440001d40714070701c0980100d00d0395050b01e07140b0080c464410529503800f22100d41c00b10224241c6103050504013024199120222404034503200190100810a1905540100300c641014060f60001d680610701c181c004008105129034003240c440c5c5c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 337847284 1250 337846034 337846037
    0xc04061e0915270509031804050402011e050715020403020f0d02031f020903010203091c1403161704030f030e03030103081e16030203040f141815041109010e1f 70
    0x70b00c40000710100c0e080004008801c40884d007450103114441070080024491448680d11402180b0803440c11702090b20000c03280640070486408200c3c1c0c440700400c0302401114660b2401c01e1a00e01c03141c0e02c41e400c411101e0309918142d5408941841141072841c60341d03064090840706008881001c1c0d00007540c4241c0c2c06600e540a004aa440c800449160f4068580c003200043c006d645074500704403400e40c2c1e203041000c1440c04107025040e421794980104558054000c030348116034603564500d000100d180b0340b840c440c1420030442c8480034001c00c0b42031a81034041c83c420358451a49040c100d030b008040d90a075080e2141c3d603810070401000003616460803166807010342c0798114a1070403602914105801940d28581807080d403c03003480c04065002c4010420307500d0b054040782189072500008040300c00c2c038022040d0401c626085141702d4495124045030b000a80e040002d610129400114054604038212038a241c200803602c00351541c0c102805a075400e005071005a000041e2001d05000942c0b50080d200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 337848534 1250 337847284 337847309
    0x9050d05100b13060306050f01050604120b100e10060206010602070501092c04060203011a19031d030703170603161a04030c030b0712110a08090c04061e0915 69
    0x700345031201e04103c00d9035404000c003000320555a0a10201078a0102e8082401500100c00441c2c603203407490548003601c0300400e0410101c8107690b69041c4411000d82200b803501d02c0d032100042c1c9201e04c0da20b203134403510524202d03051091500340c01915001040e00300a00355048000107000f50b90780609550300302c5503000d906240248a20202d00303140c0e02c1c050054804080804108801d2200540003141200c4070300d0a01d4840c000c0081100c212401030304002501c5101d505003a50701248240c00611030980480d0351826141c04518281e440d60b40b20a100310041007801d082035008111844c221030744101d064000c1e01220304a81c1c60380d551001940222414103e0300d1409204942c0e044040e10f019552095803100015202e0034070644d0003008840441c0080c0704c050f032040303000300c03103006910340c1e0b1440900441c200036001c50155040c0a00a00c004417070302c549086001540c0d01c0f40034000081040e4171507c0741c0c02650318107840c011402c41d086042018106502e90240e00340c02801a4111801000c504 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 337849784 1250 337848534 337848551
    0x17070f05131502070305070504020403030e0613090608010c030b151903020906040f0305010e0c09011a0c01090b0612060c190e040e030a031a09010e1f120309050d0510 73
    0x421003001d0303a000b0108045081282c5a50740380c00007001c130b00f62401041190106075503441000103078412804000c002400310b82001c401414407101800c0c6682c81e00d000000f01c00c1d04c8040680c05c40703100307a02484882c0c1d100c9218003050382e0540300d0a03501d40300543d2030442901044d00c500841788282640111040f41d6611342030540c0348254142c521400008001c1d580d00d90361155400401103c0c3e00050b10076511f0669000c500034000a50403020200140c82e1007486ea02e440c0e24200703d10050711100181c040d003002a807005d85002c1c030031041218865a504040350420ba400e014109240146403a030b83da010001340070a001014040d14181c1031411500783e00740340d0000088030f0458010280c0394000d814003000350420200480502926441036804002c4000c8c06406001541c4120420340c1e0070608100040c001c01400648407580720400f4513034056426010139034900443d10560183c1000c140d007060000400d540b03c00300c0303402000d040300c48084c5035800340c680726250100c004c003541c5503c1e41c42011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 337851034 1250 337849784 337849807
    0x190203100507030c0e0a1406090d06060806040b160e010e0d08030a0e2413020409050f01060e060f011b0501090b15010206010b0f0a0804031101141f0b07080f07060908090117070f05 79
    0xd0300d00050b03214000b44401ca035a550a59510340d01613f044680c3e1001c0d5001034540c40c041d80d110080e8030700740d07560701b048900924010b551800758414841d400400701c01035200801c040e000250700400041d07000040c43c0b03407100010385c20901d40e214040f01e21a240829035507a100b0000c440f03900a100c00c0e001c0c860800851000270000c19103810000e045000d042d40b0344180d03620642c4031000307c842e801c02032552a80c8003010003d4003c2c400c0d4441c1c3c049400c51b019801d40d11900c00254100301c1c4035000015000c150780d1540083c91004032001e140f090003010380d0381c00c1541d060107024010301012246c2070505698000340317060381c0a008880c01c02c1102003030014040c584610944120462240001c110f40072207684081c04111049a0340c0c00819200580001c03040c3c0c0c1d65272024212007621001c01e080600302e90700c000c8290b2140451242400c4148204408103605116101d02c45106500d5565541d036006c0001d40b0031501c0c01d1b900640101030744204115941c01c404480c40c191002c0c981143c3c0c54210554 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 337852284 1250 337851034 337851049
    0x8060c0313020d061b030b0a06200106260303060a0b0c0705130603020103050c090a06052d030f10030206030601030b040213090606120c02190203100507030c0e0a140609 74
    0xc041d500108407483d40e01401030301d90149031641000344035038003100070520041e4103807002c0c1c45601e90230001840f02081481d11a0400124a818507008a03a00101014549082d9045900700c1c03801440d44a1003c4508880b100c0258800201030015509516200c000540300700303000d1207407a40310f03080001e0b05840d0340001e01050300a84001807405502d0341c1c00c100075000504442c04100c0c003081c900f0001c103a0040301001500c4411200906000c2094104802240c140c0c114101614424245040000190841c041d014020385051035900c0c2c2c0b6840c00018201000b800541550000ca04080f42031016840301c1d000c5a52041e400e080108001d0564000b0038000d01c00c0c500b103c207030f5a64001000c6103e888641002040311200d03a07650504040b034003000300844001a0482000d179000380c01401113401610081c28a1600060a440e100c3c81d4003a814010382d00304a80c11000655115140850582c2000030600e01d55020f942d0340d0621420021030348800e0540084141c800c14000c00c140500fa51031a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 337853534 1250 337852284 337852321
    0xd02070c0306050603010b01021f020c070e070c0320100b06160f060606021506041d030310150e03060105151e032d04110118140a05090108060c03 64
    0x4100c03054159803801d059005000aa66940c030a509006000e02c07150f200080040f444072120800111138411248504002d41c0021030102c602c0c05000000900f42103112031841c414034503034a8070081403c5500d00107180865201c40910840f0ba01c108414036030b1070004a0707100e00d501c02c002c00180001c5c5440014094010198900c0c00006103c090f0020020803c0100b41340502c1002c1c1031001d691070385810798580e44d81c214500c00082c0c0a00024900c6d1409420090240b81c00624183c03030400c0e00c40580f41560b0044032481c0606913100d5041102d000c4420520140180c0c500c1e101111001100010b03483d414180704051051500700d1904017507142d060200d542895000c1e03130ba0030f01040e16900050454000702e40c40b0000e040d00e190b50000c50485000204850b22500c141328034643d8846e50303050388203008212418100500c2200120750078031501c201901a000818010501c01e1074281003050f010040d41040b8098003403403004002c001c0c0005510381e0040f5012040e00c2d125034600104121043c81b80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 337854784 1250 337853534 337853543
    0x4140304080109081e07080717070f03030b0a050609130e070b041d070905090606070312020a0309050c040614120316060c11060c030c07050a0f1109010906050f060d0207 74
    0x994400e0070810054010200c01641c80d10403540416003095038181750080c0a4080c0024108214200009041d20001c18031401c580000301e007021083d89034444090f440a5040380403d0f603840c030440035842c0c9000001b0062208980051402c00d0300000f08031252011100c510750562035010344190b00c5400d00c2803001401140c640c00e41c41d555107044520040854004840103145d00c40c0216132224850200082500c01c0a0880050303525001c05100007588180780c16010014000303080c0704408114001803c088800765004034444034242421800d080300442c28034400c500d4403204001d88041030041da4011003049624444054141100c1411881040c0444070300492000c580c0080000c41c0d846051802c40580d145800c2201c031003825070341c40c82c00307491030030100d40d01b8000605150605002071080d00d1041040e541e4802c00c0c0d82e181c922408404404440070341e0761061440003801d02000380b41c0108104001444814580030120f03d40380641c0d41c14602a0b41c0000d2489012016034040f00d1615502 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 337856034 1250 337854784 337854791
    0x30f0a030201020a080108010b010f0e180405010501090c030b0306011401050d09260a02070b0904060f120611071a0403051b0a060f02040f09020702030109051b030c04060e041403040801 81
    0x640c60028003e60040380d440c2d002c21310041c00410b04007014807506c400740c2e2068640242c68016010203031030030022117a203503510003c05040c4a00420341244e4142c0694400c01c0003042c0303541490403c400303441085ea5090200342c03078012561000c3da0000b908030304452a044501c2026250100125418420702000390740c800d06005240040214020000d004084112218201228201c4a05000b8458084858016809041e0600c240c038000c3d8000c10644100910008100d90741c0c12030002c45007007540c42103003021005400031050199602488000c042540003140c41e282095540d90602100c103840407116012000004c0d04060048003120306154600c914001d4112201d210542c2c0d0f1141054111405400c00c1c103040c0e0183c5031802643d090b45e8030340c42a00030450505107a60000d421207001030360300d99200c1c8000d2002c607806100f80c0032211400c130544100003020100b450b241204640c00540a5441c00804120000300340301c40a0300183e000b202c214841c0341d120403252460027907400500141d444d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 337857284 1250 337856034 337856053
    0x130b060304052d0a06051f091b0305010e0121021e130218040f020d06030804060e090103080304081308011b0801170c0d0f0b0c09040b0904170702030f 66
    0x100000c80b00300500415405183c00203128407268000c00200d00d80071400e40c00b1003044400a0000d410907a8080c0c0183d41400444142070314040404105a101500706560f0304c80b840d0301c500150f41940e20040440c14144001e52511740e01e46640c56051096032012040020b0105550301c41169000c07034140c00a086580c00c2040745850220b40c42800c42d0380c0d109203102405204442d50038000c2d01d07101002880c0d0000e42d00020411300c806011808402d030109a402c03c481d85c0c05807024800d40c006075014000140e00c540c1001e5011b020700d00030307020f4280b10301a031000401c00100001300700e035442944004100e448101090510607480d820ba0400c044079404d1000e00400c110101c00002c03c0741d080341d681c01e0b08603641e504042451100000c401c0c0b60f203070401d043e0b04882e802c1500c11064518031401e8150081d481030f8036500001c0070f040d6012209600c00080c045010310f000d008250989001711007410050400780c0c2c421070201c1500d40103c8180002040c0c0320195a018401d0181074105a0250b41d01e502c6e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 337858534 1250 337857284 337857293
    0x70609061409220c1e1b12030b010807092306372309060d0501090204050a090e1b060c030d021207300626240402130b060304 55
    0x72031006002441c3c1e440c201e08284100c0c800e500c508940300700c00c1d0180d118080400c0382101c0080161200001d01d1505150800000749004080703000b00041d50750019522020800041000c00c0141404080105400b0140300041603070800020988003600c0c000118410940418068041d862402c50002c00c0107140003a011180320004048400301884e903840b40524031029514210301803404114141003003211a800f544e130000511010b20010710750b9023441c401e02070302c02c2960000d800c01c00e0219000314080202d8100060031501a02c00c45005100802201e810a40d49004007081c2c5900c000407140028180c0d12508115076000d0381d41001c2c3d968032002640140c01a500c03907013001c40b001c84500000f0300e05901c24040303c0e00e17042400070b5503034102130a240240680302a0040c296002940c0c3e140024190808040c81d40b10500000c030001e90b0410814440c0d4100b07490f0400b0316000421040860740d51159282c1d0059005070304541d031403240810b403000d90000300000310300303140c01c44000000c1c0003e01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 337859784 1250 337858534 337858579
    0x31806050703061a070204050a0b030703030201061a0301081506040e030c0a0b09030c060114061603110d05031005010c0501020909041b050f090403080a0b06040603090c0503070609061409 82
    0xc01c4991818440d0913a640e0000041c0d07003034a01038281041042c820800145420780066030401100c0d000030414818160010b03003088001d60003140940e640d50030800c00e03824409402c48040d002c0348041420740d0300d0003048a84826052100510000381000041d41a0341d40380e10104444003c03404076503d234203001c0340040c1d88844420341600c20344005800650300c2d020010440b042d210740308016203420703440c0c10030400a081228130034550054045c0107018140e00c603070a100301c0f03482c0680d50b00241401d020300b283c1e09044400519a08010041040042e032059000e0480125102842d0018480003181083d81c0240921081c1c55801401d105c240f000b0710403890100304074013104542415140707a0b00d000f08040c104140a005400038103a4001401280c059501c442d801181c007800441c0c3c0003400d40006109500c590041700101c0da840e000442808108074800380544001e500a107015401e142c0c010b411041e240c8540c8041013568407420316021032010650388946405842c40c0c903982440d0400f400e070f0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 337861034 1250 337859784 337859791
    0x10c02030901030f0606020d0807030609020d050609060405010f1e08031b0d05070515180a080c010b0a053304031203050a0b0a0312050403080c100e1f0b0103180605 72
    0x20300341300c484c130f48818951203804115211030b0024440400d900c1000e407a40c08005040c0d100349990b60400081021203400100b00b1040781250014007072408808004440034081c000d5800b42d840e2900501081d006408484203480640100d81100c14040090604003400303a0030008045c000800c4443c1c0c0d10324407c6072801e4038a08101691540948400c084540d4002d13102c01406030340c01950103400b060100100720341c10410b1042c00038040301c1054801840d2102410085601c1a00010300d03030244902840b84031100320741110581d00b824036003000200380e14245170144d505c0314070b0f0b0203801c0102001800f1000545c0c02544440351200e59905011f14120201541e01000c641003e0014018006901c00d007071282c0340c02844128042d0858641c1c60318000c00303a0340c0c2010f1100c10800030002c14000d4010700001c1c00200d005000012030451320401365000b840c0041c2c020750052101030390500010a42c0c1c00306495401c80040c04540180040700648803206140102004030002c4109115950f0480b030310 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 337862284 1250 337861034 337861037
    0x3151e010207050603040c2114060a05090d140f070b18010c080f070e0f0d0b060a0504021e2206020d1701050607080f0702090112050601060806010905040902030a05010c02030901 78
    0x8469a50f501808040d01c012a40103149480c2c02e101403000707020040200480741264620042151001c2d6a02201d605840b202610585c2c045c104114201da00350044580c80b1640ca0054841d8840e002c0010703001c90400104280c0611f004120003114008281c156201d945d08145c0301c0c2c0e25420320002581030750300131480c03071401035081ca04268501e85c0143c981c180560702d4140071509070303528202c2c00c482d00408040011b030b0090500d600f03020680c0e1507100d044030302e50143c4655031842c10070008000b0340100310341c820b80c040c1c0d0051048000d840c03010b100050090740c103000d10507030310009980301004400c14070410407940ca5000601140c05a40040c400c0c420608688071200d40790a400016001010244510341d440300d801c00c04003000503600c0b4050b04840105000090074030702541d0001d0301c820000d80246004484550300d103801d01004001007130050800b42041001414004002401c42c0f585004a5000b9038071001c0a10444d00c00f04104001c0c290004020803080380f800303900a440c1c1d401404880d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 337863534 1250 337862284 337862293
    0x21204060c02030a0f0f11030d0605011d0f01080c0d06060e0405090105012706050306130c060f0e0603040212010c180b0412030f11010608011407050c0c0603151e0102 73
    0x200042c000400c48024240036200c02070b074013410351400c03a58824030f50400d40c00c114021081c02042c450400c00b174002032050310008a000350416000500c0240454070440f05641d15244066494607080354103080703503100f840c142c043c0307035564641d0b10f002d841080d402c4910700307281010024540e60b008841a060950484062106032181e024003802d841c0203000d0080700c1c204020305840510022450360421440b29100031500a43c2c5000081c1082c004a80103403500040c030301214204910032030340705c0c090001828000c4406800640040c1882030141c80240642e05c008081000d65413441400d140c10000c0703500030f100c030f2100848000d000b10710400250080605100012900e6100d075001e46090700c500d403514040c4034003651411120340c000c40171b401741404091500c0c184822000e01070340b005840c4003000818114465035180590010050500d406c0000c14000c134010b2580102c0c440c802c8990031204a6129210801d2a01c0c0f0f0b4046000313070560003041e9201c096003a095640041c0240c127403d03000d54 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 337864784 1250 337863534 337863551
    0x1401021c0207020f0405060d05010e031b210901031811030c0a0602060a2406050a091406270604031b090513060e0705131401140f040b1302120406 64
    0x106038012110001e51103540059500042d0800d42c1c4001c7d4044001020407180b09030781e450303890071a03000200812403500009090b0701d451244006001008440030020004055021030b03500200e8490034810404640000300e802c1103a00c02e80210a0b10300403280e01100302c502c18030700b4015010402c005c01d4024018041080110315100f80d0407001c45440d60060051940c03000d1115000306001484ca00724440f451681081c20107142c0d20340d80207401107440e041d5852904d104060039440f103683c401d4819100b41e90711980c5540341d1074159a42c5003c900e403840d28843d54024041f13400c481922400b034010001103000001c3c03081c0403602403001c01c1480b00c0e4091003500c596241c81a204103c1e24409814041503103100050190b510400e8030071461010740303400c1a1a81c001640800d42d1402008070191900f00031740412401521040c010418022008604403040300031038888964a0103c5d813065596003180309040e11210000c0601c0303440e00d48110f684505182e0858540301080d60b00703032120751410340003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 337866034 1250 337864784 337864837
    0x31207081e07020c01050306190b030f1311010503090705040c05180a06050405061804090303060806060108040330020a020105070906170f0c120108060712050c0415020a140102 77
    0x22107001d02c00c540d0140012030309010055400381d2010b00421b030402000000804001e0341140c004001d00342c9114220b9407410031811094000601406250070710002d864440c00203409041c90385110303002801e000740c881d07840c602054242501940000d421038241010040340380c1d032103030041c01b009000004100c2140c10740d8040c40081d0501c0e000b8540880d6040100303021611b42a00980800c00c007181034003001070b90100108082c0d5007101e4048010030b40b141d01c240503080f03040c01041e9110a0030b282c6040c3c1494036403001011070441580c103903104134400c03465180c1e04107101c4d030150f2007025800c030035551030841e207400a008007030485c0d0030b00000b01444004160b60b0b1041c404038403a04140d20704001503803591031410303030000c034040c04d03c0f20201c604010300c04800f00e81d00010b50084c40d003070000d000940b0300302d00c02400d02600c0c5036418164528100c100140c000d140002d0784c084c0e0740c00359504010a440c03624182e160048011002c1d02b4028480c03d00ca14503403054000f8680340710417010205000106415 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 337867284 1250 337866034 337866091
    0x706050f0a0608010e06010902070503070c060c0b090a020d03030c0201062c0c03090d14160c030212030903070909051915060506190309030504050a0303050301030219150503070203120708 82
    0x80518a820900040040060799002b51038180d00804c1980e140140603038845610441d41d42c41742c808540f00c0e401d400c050003800c00d15954481d400b82c015015410103a03000681c081d1004100609051f5550791740c5910324800d500c1500640303000f0342c48600b11843c058840703a0413450700d100b05034200c1c00f0b107000561201c283e41c00e40b4041c901460041882c1090581d06840300e050100c84c08003198007e00c60180d182a007081000c1c40c03140a4400c504496040d401072100954001900c00c000394020008403a4a4034006000d4049400030303000052800c400e03140c4103041001c08030a601c6034030440603040051040d520400303584d9000c0c46c2c0080000d80c2c0d5440900106000329042c94128403218010001c02ca8002d41040b100c2c3c511901d480d03440c1644a0000031505c9105820640000d4404030050013103092401d81801c80c80b41000359071860b58549000b408090003038000782410810007002007607071035000700182c0740203480760141e01140d4a40540d0044c88400101d4103800407400d80001c0003800b512056 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 337868534 1250 337867284 337867301
    0x6110d06140a0f0e040b04082b050a05190f0e0a0b0702010e060c0403110d02040c0c030e040e0703150f0627050903030105060a0c08040605040e01080712030f050706050f0a060801 78
    0x64a0301c0303095031985c9800700c880b00c0c02013060742d01440402001e400000d00800d500340035502032003c140082c4041d810b09c0c00312440140349c580d68914007003d11485a140d0f48098540d1130f407010020411540d001d8201000e06240c0c2c0300602944a0300328040c1c108941200754901c11041a0b000f00070301c511850189a035104140c6e41940d07030f480100000d0000c01c1030480240c010340e81c058801096407280d40d01003421102c0704103421002500303481d003e07810168400e41c1403001a00403035081c0903400c2002e0180340c881d810340c80010110140e00c1c1000c81002482d4000c0c0000c80000081006465541d14a092010103030803011008080d000301c1085c5026038900c5940c0c0500c07150300055095a0800e01482800e600144120042c03100d117020b04400258400000c2001e01004d507222903d4620705401c50031400c10680040a0581000005000d0841d0601c000d14501e40c2601d025502e004080c0001e0b105403160420140c4190300780001c100303c8000d545c1096001d180d040d002044107541d5803c03214201d03204003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 337869784 1250 337868534 337868549
    0x705120d1b031107080703031d01061706011a09030a0f050d080f07090302010f020f070b040e061c03032a090302150a020a0f0611130501030b0409050a06110d06140a0f 73
    0x51204d100403d6129000c0e00c000b900c2814005000c10750146480500e06821610b0780745617450f400148400802895402e40c2c11a204008110380d50510201d00b00007405d5030354240c2807403000b00c0e244001b9074040049512540d0459006078152100c0c0c2091900d0300d92950308400031070054004104840da035802d01d02d04c2000c250742d031b00c442d490030f50b4011103090510103c036001f1403064030342e01c00914605001c51001806181740c120b594074600409113800c0d007001000d191240d03600741105062b02041c00ca1002150b07906140014a00340c47c0d40a0881d0041216110f5141a64445034104196040000c02c0c06981c02294a000004030151161089128002c07600f80160030202d2100001603915807001c100c184508404141c0d20b0100c03a0f02c12080e04203030f503841100742c540342c0200003558061003101c42000c02900d0a02250015889132a0350b401d880d4001010701c0d598500e401943d85c200780c2076500302c3c02980c8052010558822059640c581010000751040b80030580c001102c2504100f01811103030315 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 337871034 1250 337869784 337869787
    0xa0816050316030204051224010303050f3405060a02271206040b18060c0301060f0201090b010906050a052b0303060518191109060705120d1b0311 64
    0x40d001d441581054101c10304040c96004e00c0046695680d81c60000c08100f107d00c010014020301000d442c80401143c2200c0380100d13282d00051021030b13401002c48070358819010f02940c2c0d9203040310b00150186030055118803800c14115000c62045100c46420896134000c0b000c4070704030f4864540d01000c030300c01c01c00300c1131123041e21001700c06030503c1d44941d14a42e9540100b95001d9600d1580c241030800c1d4007101c0880d91303a072501080110300c1130403841c5900910b9001004108600c0c2c003054070b200c184818011345c404c4c0140d40c0c2d503084886100350008140503230301c4640d082c602d50f503480692016240c03a0180510400302e0302004902c60400b0490300c020f0f410080c503980256071010940c02d03401c482d200000d0302056218000805c1e151550901401e01a0020407074140524141d0f0091b00e810410f813019044c4a410402e001905c40000c805a03100114111101940d030f00b447d2624910f8184200383d410205a1301044482402140390300c02c04101000581461210b1400c450840440e4a00190030081e180c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 337872284 1250 337871034 337871041
    0xc0334080a0e100c1206030c080d0e06070f050a0c030804140f1c140601061e051801050a0c05011805071502071a0f07121206140d081e0a08160503 64
    0x4594110303078003240f41030401005c0716109449810030f0b14403e400c2a21100c000c40d6080000003410011282c1c50001d51501c1c140c841455400a026403060100c050440031030311081806100040c069012030b0340e4040c1d03090143d00d50ba40740101440e001449030a100c0c0c0d41c40c0400b4101410300148007800080c1c02400c0003078001c0c00c03205080d004018588151648180d017000c0c2801e10788101300d45d034041e2005849007500800c12101c0780c45501045030315041005403c0c00060f098041c1c0b4000b10000401c00d0a100e503e82078440c4080740d095404000160203903003010100c01044c80b28124090045004c0c105865030661a41c003060300d200b8584001100591004404104c803601e121803d80e20b46889034401440c055a4420ba45402e41001c4816901c006184048402c1250083c400c00418045044140040c0f0316000311035417100c0b85200341d0f41c00384c40c3c040d050320108801102102e00d080c2c00c41c52003030303070600345440d52078400c0e0030074490803020903403950125266149150b00350200300119a2418076603034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 337873534 1250 337872284 337872313
    0x5010507140409020a050c031c0f02090f0123040323150a0507020a020a0602010b130c141308120304060c090f030f022b050c15030c0334080a0e 63
    0x140085d210740c042020500030707030041032003e00086c840c0403410b80c0c07060205007541048208941007043c24070551841000707000001d40b10068040c00030802402d2908412009050400d03105500f24150351001070001808006c004840e003a240d180400240c00786600300701c08401c643d81b442c800402091403910360000a003014041e40003e030f400744152040d2140c41c40786501040305c420140d000480503035180d040051083c20b19003111402a20b20b49802d0002c011100006000302078a07030616000f000300003070601c1c0403868000300c1c00700134817642c0c1c1102e21104e04a8110750007a0801d446c200d95842c01c040e4000382c050310880500c03003915000031501007810300c2d40d640c0b40440d420402c0100e810411401c1d800450407007480c0304424800000d00e0142c1940350600d0458103102621302400e01ca09400c00303040ca403555003803082c0c9030301a0040c0303201030307a03a15089102c02c6070745a100802d21080d001c0c102c0c2c460f03000ca0000640c450305100c1e603d460039540c075201c00100503550305040071011548040030991004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 337874784 1250 337873534 337873537
    0x90105160c090c0509011e0509010309060917040e0c1216020f0f0303011a040b1e07050f0d030c080f0a02032205010b15041217040b13030501050714040902 68
    0xc078400c601210100b5501c1c0c031000c0583d000c03045014003049000c5801600c55820000e03000702c404485000f91240c00380401c001e0003c0c05549805810035a071964254208080d551141c1040d64226400500c400c43d031070b01c01c041c242d119000760000c440c10f4002190050611f41c059800d40101c4615001495403041201c1201e0502864004218818034800c480e01b1002031041000400c1000040c646c2c0390b0400124540407060b2031303401104560204020420040080705403044032051349020301706852412a008028041c40340c020300075001b103002c1d50000d034400003a00411010685c03428400c0c0a11070304192000201100c0c129004c0c2c0b0396100107540b6040a40c011603101218000700c1d528540c50426a83c8085990903044549030741d140c560390364610b80705400d420314806d403a0f16240b801d403c194510765100ca5030a40101020300d04600702c06042403541c1910050008804040d0701d600c0482417210b0130751003501c0705603419440c080c04960328603c100020b41c4001c04c41b0032040d180502d04070f50741009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 337876034 1250 337874784 337874827
    0x1704080706091104140103110a03080315060f0f03040201120c02060708061c1a010e0c04060c0201021f1b050c0c010804050a0c120506060604060c020d0320070812090105 74
    0x3c4010880c0c86000c40c0e035030392040003010504038108401c29070641c68200340240b45100703060b126506e8440e0400016260004417940101a4800c4c1c0d082c0e07034803c1000c903003a4001c1500d103100516000c00e0f0a14030422180285215074001d0782d80b04d00c2007003c5540801102d140120a00c0140c000b840050b140b24020390a0355045800905260703000100e03400d443c9a8a84054022215484501c02507068100d010a255014041100d00c440640c140102410755512a902c66030040c0401c041c10f00081d13a0003405004200c12441e00d41103038040301042040d0041441c15484600c101c145144050304030300c0b8205071901604400000c2c52407184180040d0f0304500010310071501480707188078810003c0c1c00d002691006005800d03030940d05040c14035185040003401081d49002d0f46040c0400c00009601140690703200360182c601c01c0795840c0130300b0b0031544c050701c01c902041c10060403d91f0000f40040002d92108480d144001d0310880510920045080e116540c0d01a000a006002c0a210248450401041d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 337877284 1250 337876034 337876043
    0xa08010603050d2a030806120327060306100f0507050616270501030209040b060706020a1b0237060203130f0302060d2a08060a0816091e11040501170408070609 70
    0x1607100c0300c6600545103072b12054040c54a9665007600c0f8010780d1804400700f406007001c81d086819450f1190200303a50034100c6445908012440100325011805042202e03405c6800805481c0c0610700011202c25000070f4044180004080400140e801403a10300e5100d400c1c0405155139841500d0000110b003e0f4018904c81036115654076a604101d6031604014251180300e142d0140e1551712401000d0101810841c2d400e80030020200440d0041c1d46030100c1010020040341c900769624101c14442c000c4000c2a0084000c1107440e800129100c1d400001803c0f0b0702c00100d0f406a46151180c407031f00a10445440b00a4000c60280315000100004d904860002d40804c1d80880c100c02c49155040ea100c0c00740b1000760040fa84010500070755050002d0000050b000503030050143c1410030040385130448592240d4002250b031124074502c804900710b603640350402c2c2100d0601c0f070925400000a26a031080c0f08031404981d0b58941400080d440c001071604c2550840301182c240100764581d41c01030944010200ca = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 337878534 1250 337877284 337877299
    0x303070e10200109020f310905150402040f060b07060b04090203030f03010f090507020d0c1b08010213060212160507030602030f1009050c07020f0a08010603050d2a030806 75
    0xc1100505509801240b00590004107210083d401409100f40707944003000d014050002c603000c1286600940f4005403501e0301c59070202210201ca04200410130300c0c00c004d0603801240581070750440268601c50086000b110104a021103a021881c1203840a101da45071207a4140030301d10214505078451141c0400160000c144410254006401d5601c05c0000c412811804801801451121018031000d040c592030700300180e0600d010081d58070790220f2001420002d1044004003000048182c0c1d03000c44101c2e80140c600146c0f00c91700303940030390400c0d0803580e9800160307180055818030001c2c0d0303c403040e5a50121a482c0011041916090b40070303419060f6054810014000001017a52005603c9214400001d0106060440384d1054100142e4822000141000d0074083c2d06c08161f0100c0c3c01650741102c40d0381201c0e800c02e020941c2c48107603a0080b06954039226001081c854081261540b09000d50b0340e00000318034222000104640362481c459000001095000002e0f0013110a6900006c006045d81f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 337879784 1250 337878534 337878557
    0x60409022a0d0e060f120c1b0a020a05090a090209010603020a1b030e090a0e1e0c0f0f040b0d06050405012301030c061d031e100e061512030403120807020303070e10 72
    0xe03117244030030390b0a03c68500700010391560342c122300c1e0200c29001c030b141000340c0150042500011520403060090300c1c072034003264010401410756a480741c64030390350203480d43e8800d40c1e50700070140c02034011215641c00304080702e000594207080201d4500c81160315488614032400f0031003e002820308000d00c070090940c0e0350300c0d0781c0ba00000104030340b01c524030040340c000405c1d50041e0034590400201c90b01550252100e170b0350910a0f40d551103421048a4420740d000101c40180c0300c001481940c800d68081c080610b04000e001c1030100640002c14610482c0200c0c000e0315030a07007003a102d15075003444050080c40000e4420b114540c841d2031041129074207524001070038100900001c0c00c004c43d610112000c441603980743e10030208107200d00c0700c070310400c1401040601d03028201e86484080060040264000030f05207020a9512500f2180d0b41c5840d100c01c03281c031242c0360301c1c0252480a0f803c00300c07808170300b00e0f0000402c1c903072001040301c3c40b030900c6555480c500b50b2441e0901000a068080b078030280084491103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 337881034 1250 337879784 337879807
    0x319020d05120a030c020105101e050d1b0e040b0604021308030a120e07031a041b0806060a0b091305040510140615091e060409022a0d0e060f 62
    0xb00e21241001080180d564002614080c04544015101200b5a410079080143e5806115866012902e504000c1140743c1caa14040d2000300200d074000550140401411500f44203003002c44405582c9000e10030368900c1d4132030640c286640300855006121003046400919903052540207010000c80c5072039038210064440c410b1500b5a04509103081c00100d0170341911440032031078010004c50401d00d1014001c11400c54848520881c1c4501300404d02d081d400011400b0041c0180c600784003403607005984e41109440781c2007140c880400381d0345180319050400c0c0101d641d01001c03045030f0003140c0c01441c2c062111003080180010705001001940d10f8003800b035520040124602403441110740c4281241000c3c5400420084030400905e0741d800305000c244082850354842c03024043d41c4120303802c615080b00c0300600006405103d982c121350a814004941c20724240c00c0c842e424100e00c40d601c100400c0004078600415900e2140c208060000f131210103081c1c10700d040200042040411804900340740c505031145 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 337882284 1250 337881034 337881043
    0x7021c0f0b0c070b1b090607080405030304080a060c0f12200f07050f06040302060c03100306020d050a18080a12091a190608030a080a1d030315030c0319020d05 70
    0x20300d402d01480009100c82080348100001d40c3c840d60000c400481a8281d6034095214005c400000d4000d420010748541442950b2058500800e0014100c1e6907031a2100c00c0c4540b5140310710011a05c41e414010b25074141805050480c221850590702c880d1601c604201c40c40c090601044c035034030000e074861030400360384046000418405d4680c0e412580d5502142c40c100389040700d100c0c3c0318641e940201c800d10001a9010a0f410b8001c1c500302001d541700d8a48500c108401c500c290310003005c031840000e00c440c070040c29070050b038456400c0901c10840c810072200c00b25200e074046403006100b42020001ca61603d03006a21841ca810341046c00056031403aa43c1e038080c4810240340014440d0007148040200460441984403640d9200b032205000c0c251520740340769a2405180308180500400c20700041701242182c0c0402ca0540f500c50700c0300d0340b417041101041e4807607100740c50a00f460701a21001c20005e09000600c5002c038003000c0c008110341607000c080400700260b1020100d0b44201d01400c4000400d50802 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 337883534 1250 337882284 337882291
    0x60303030506031002041d0718030c0e0705070c0b1303140f07060f1e110d0e030c01090602030913020f0304140607080432030406210207021c0f0b 64
    0x4a001640e0b0610030109450003045245005089004010621209a146a074010a81c0484c2400c0982c0e44030320800b1394030314400400d5120307840c0702c100c400018030510180d1001101c42103070038020141c030344800481e035a100d031450207403049548440c2004040c1c02d41d402040d02d000743c40d03002c03800c181d12555040801050b20950003450b50085004250a0070240a400c0c0100b90340d081c0703400c03c1801080c1c040e2500384005e101804a08042c00340f402c04034020000403000d2800030003541c9400d000c1042c040d041002400e0390fa802845002c04250241d4011030b920b20507510300e60000d50a010204082000f190803c15005030100d0f001e00991418600351400355010b079105030024811103808803d0f00e8030380500104000100075450b0103100103e98158445210361f02902581c07007002009003125245041d0412406c0050300c0001400100300364088440e805040030b020788a0340001544072600c0590041106c040e510100003245001c500740b80304c00f4111103500c117185030740a5000c0e42e1180a003000084 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 337884784 1250 337883534 337883537
    0x1314010f02090a0f050a030f0303022802150105130e0c0d0c0603050a05040f08160b010914060a03050d110708070b071b060f1d0415050102060c030c18040906060303 72
    0x2281101d900d280101e0b0f40d00103010074840c0400d28500c1c00001640c240d00d180b0001d00404004000c0300280f51080e0112502141c018855680c86210412254005180e1240001c0140a0900300100d81800070340c616040750350003003010310b1920030010071034010940464103004e00c0c884c2d507911a00300e484900002036081c0c010035040c80802d1401c1c10150030b0302d000030710b030340000741c175000c100320000b44100b0300385440c143c1051409464419046642c4803c42440d40301030041500e41d400011000c980d03410080e0044880a9600384586510003440702c90070080c08001c1640d08a0140481000c0c496665850608200412109120f039181c1c0450b0811185402100c1c1017000014043c0601008420f02e1030285100180c9181e02403500030001c040c0c121001140081009502e4500551103240c1c000b65824000100100840b12004c1c00d06509a1140d21802d8054010400010700c80b2044038240c80c426075048043c1498988201c40181f0b44d200360300103455009903180392403030100c4e610780f20b40c2000d140b00b03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 337886034 1250 337884784 337884787
    0x8060907080708061b0c01090f080a09080a08120c0f1c0b0105070510110904060e090613120509010918050103061a130b030304031205130e0108061314010f02 69
    0x401e0405800c1460582020072aa80f1a0041c00309403a007140a41e10004044406203440f41070028800703002d000480720140c040201e501c0307118144064000105038184040d141c2421031903481210680765400b0ba0f0340500445810311031000d20103136000c0d0707550740011a40a014605122290000c0d01c03501714508820384a20b0418045201c01d59a106210030788109003007003418101107a503030b141d903542d14000d01d018603a141d134421500070700d0000680e01c22540040090244a40750b08000c100780000308c8100165110b51000700d043c450704d0703a82e0704000310b4101031860b6407452880705c240e40380d500c0320046904104120720700140300c890031350208102c40fa090070085415491400c025042e00c00310a100426039000d007110444a6480f0b0f485610400000c18000c035001240e540040d041d40201e50014140640d0908000c000c05d40c02001001e074a00643c03040c0660648a44d00c01000d56130074082c10304150b0000c2d0100342610b008000740c003502445062468510400503413114290b420440d640400241c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 337887284 1250 337886034 337886039
    0x10215090105010801050112200f030723060f07080306010c060c02010504030e090c04050d17070507090e0a08070b090109122d02030708180603040c08100e06070f0908060907 76
    0x4203008083c01018075041088911840ea201d800d027004141d485c14100351481e403800c0c0c215480e0465690700c00b03800102900c0156548290880070310080d0460071844404000c01413603a0b10b820400c0c2c03005e0700039200902d400c2c4907031540e501c5480e900181030b850610514401c0c4c1f40010f2414040d600b843e1007a44d00204013410b1901c0c000d03140ca031b10794035080c2c07140c4030300d00401041c000400d040e40d0031600200d942464030311040c10b0400c8100c2c1c1c81450211104800aa400309101c400140501120400c081c2081403043c2c00d00c03042d40b5099000d40c000c008902c00c0040c0000301700101d203a40e4101d64032000004a001c240d50714030040801c0d100c00039000c101074111000c0300f000542c200c920b1300e8078000d1030f51000034031052000b501c5c1d10907028014620500892901d04640000081c1d5030400700145c4200e131380341480d052400341e00c0164450b01096228480c0d042e042107240f03001c0c1402ca441594000c0401e6190a503081d5900b800c40d2920208224408c100081c0440c42000711501894000d00034200850 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 337888534 1250 337887284 337887299
    0x1e0302150402011d01110f2a0d0305030c1204030e041112010b0a0903120806130e070302010e040b130b240702010f140304140d021906020901021509010501 68
    0x4035015880c1010a800310200700150743c03c0401001d1511804d14466200300c000070050303c00180c480710002091180341464464800c002540590030031403500f2400d481c640303c2c1c134654007484090243c00e400094500302d10b03001034080e5001d5070700660118070190801022664202e040381080b1400e400051110b0740c00506410544108060640710790851850059500f90b0784138048011f1003600d600050010b41754290500c034803420f0018540c0218011b0141410b25801004500c0955000d44500000c4103042413011580c03151900c1c0407121400b401c4113030700d150019039050101d00f4410380c105850f50900e1200303548a1500100c00d28113048c0c005055080e54041c400402e0198503512103151581100d89046c0000d8029120142d0342440d180704040d9190300119444040007002545030340c00030080c03004001101038001c600d62564022101240825042240e4460a207026454505003104060300460100e80080c6664041801142d500700c00321619028820000c0782d50011a0f5501c00042c4801d6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 337889784 1250 337888534 337888543
    0xd080d2a090e01120b160e06070b0105030d2d02070918110402090d080919080d020d0f0e120106121b060906050a080402030106170304060306050a061e0504031e0302 72
    0x1003404c00c401980b080900d0f0b03039020f0040006800001001c40044c0d66242161050b44462440c12014010507280c041900d484c00800c002030203514441d004002c82d40b54218401c00310848504199603104070040c601100c811402d48032501d07005d086010707807100480c01c8801402180154207020614402c42c81c418181102c1c000c02400303642d803180e4010081740046640c2c1c1d5030956030041d004600d459a80c0040e0300061056502022010a025900c0304000b94180340031410f101038151940989402c03000b80d41e412900c0568082800002c00d150031055170150600307028500c03030164101c000280711602c0d813804114481d45510121102106103036080710306082d01c201d02005010030700f8442051824004094075a014880050003081b4900e0001015507409422100092080c0d0b0b940c094089101040b4a440f944580254004a800c10100007694200030010300c08942c1c04d1380d905d0400d021040c6007090740c10414a542c6040180c1804040041005030032a007442c0303141c600120b0b191b4541c920740070303051 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 337891034 1250 337889784 337889789
    0xb0c070b040509010b0d02070b010b031f061b050f191a0903040501110a0b070e010e0904051005370e240907031403090f0d080d2a090e01 60
    0x40280400c100a440e01c0c0c800f1410b48080952403625809004808002030003040c0c0050f026151250000805415950085005000d102824140341c2c560703007031901d14408a0321a0400107030500b22100041109400e914100343e02c5141075a220841403004503240c402c01410140b4122000c0c3d150204200c01e0340b1107124000711107081c0614900d0100201910f90017240f040c0c07414881404000c04866100340294544142d00c84070f50003d41c10302000003800c05c1e852101203400315140a035130141c00e1900e443e20030722440e0b01500800744c01607400002000b508026020512140503c1080f2a100d450100d54105840f01c0302c500028001040d503c2c0c1c01503c10418120407960044010040086400090054540e94442000020b40c0701e82d0440791030700c500f903800030b04480d0080d100300c000d04030040000d00c01910111200c49154402c04208000170074041d60051180a0820454101c064150481d82090302400205407000000034481c62031040d00415600015281c03242c140081500403000c00e02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 337892284 1250 337891034 337891049
    0xb1b0c011a0a2909010c0b07080f0901020403081608070210180b0c06271209040c050306011d010306031410050a020f0715060b16050c030a03050901110c0306010b0c07 73
    0x50500034941c1d15102d20f80c00031407109007640005000035041c2d005554843e841588446100381a14003a80020142c0341c0c107681c140701003816040032445c102014003e95081c0c9030000c42c2d0501d0601101301c1103086460602c03040303e40e00d50500008015a40f002da113803120f00c0c0180c070703000d01c03600601540320341250780d0380c018400c0300909000c54900040f000411a910004540074200058107044c10aa0022400340071440984515913140c1c0e0940441c8002d0810070805480c01c1c05100405202900d040c0400c559280c0040c241c092103661000301612880d6104078103040000748903803030f81c89611003090144a41840740d0b01040704030100300b586200b600da200401e01000c50070b003400c00f40d00184078400c000000c1c0006520101d2440522a140d20581c024154031891301c3d501c1303002ca811800041e0b40c0c010181c840d80a0702c00000c00c40e0601080b02050a40e240e81c1e014500744d80c2c1d60041d0380010503c090413111b4490310078403500b03a44042000300d007c1c10114401729110130901c0e00181c81c001c2d89400268 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 337893534 1250 337892284 337892309
    0x10b040312080114121c030905011a0105030606281707090f0b0c0c130b0112060501050306061804140105041104030206031b1306050307030b04090b1b0c011a0a 70
    0xc101c3d0313041403100054004403400c24080101c42c01642c03401341c0035080258412050b42c0540c0e0580e8055205515180c49000240140b0004900b0010041d244030340c450b02150b000c00009203030b49080c070001c0c11710528003113030f8070504224480c14460300003c04000c0d102058090850b0549134480c20350746944503050b441c01e192100d040100300e8a242c03600d0701c180c5040c10404a000c4541100600008140f460041d084205c043c00b000120f101419150b16040d0200d440401d901d03242e03441601070300054a0060b1901343c5103846510034030500364048184a031401c0400340703030350440380d848c0d000c0d900040151103207840c2254104000c02c400c40301e1130f40d90100c11890400003000140c40b8507003034a9000020711344440c03035a5a161810b041902c1640100c0600406500c0081a4150064040c50156a1130390341040843c203c001030004413500250b01030b10111503503000521481e451412410111003101d070040c02d01410600c5030742950000c0d00d0b402a10174446000c20b02c0707410400c514100501c202c00024 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 337894784 1250 337893534 337893539
    0x80318010c0c03081e0c0702091e1303050c1b0a080705010c0f03090f09020307030f0204080312070216080a02040c08061e150d020d061e0e1305010203010b0403120801 73
    0x182c84075102c114010240302001c00002c810041e05a984955821580b45940309840d046551004940c40400e08900c5070040c03202080300c01c01510050500c22600c03008030001c1d61144070108520103c00e410460800c0410440d24014030821303c100c3c100c40d840d002c0b030104203820714003c02c54000710b203400082d91540040c03804c100c0c03aa44580004001508502300c002d4540140c2000c540a80694008407400100302900080440c41a0700440c411400c1d640c081081321b900d1040041a4461842003401c42c3c1c0c014091070300c42c010104000d903004001401140d42901880b160350010003441d50020280340c00105c401c00542c1404e00441c0f1201c0c50703034500001a80b5081d0009551500c091841e0716283c102c40b0180503050f10b40c080c1172030b107034070f001c21703400d501c807169500d0030b2020703500120340c1c1d00485003490800106000300d40800401440000403494400e0305240b104005040c0c01000409809000240d075400b142e020320042d4043e1070205aa295140c0c250700f031400a024174a03540d00100807910004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 337896034 1250 337894784 337894787
    0x63b100809120702030a050307051501050d030c12030e010e01090b06102f030304080405180f1605040902070c030c0f0806181501080c03070506030c0a05090105040f03080318010c 78
    0x200a42d10003900d2582c4907419400480d203000100302000b00644000100001403100000d0462203000340103496000d160380710418000d034260402d4004000c47c0c0c1806103400016407404500039042c07000e140000381e5848204040e400d580d05034000001595558151200748100700d148250701810035580340140c2114034100414681e4070400401c22810b4200e007541004a8110102c1022030360322044a499003050b00b0031007101d50081c0320711031185e048c1c02400c48443c54141c44840c4120301c1c0404401455481c2d0050811860143e2815010007400b0072011a43c1d14451020702540b41c010700246444c1e600b0752030007035244130480c0c21000340005400f008002d030034030001c0d88543c0041142107104010b207245203100e00d130110800001074007100140000c6040c0d1400103400c500d43d4021000c0352107450344c903410300c0303401d00c001c0c0c0300c0110409040141c4219030f40240c00070f040034581803400503c0c180e0307111422904400990400c40316900c00209001c0c0e100359401c860600201c0b107000030060041e00762030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 337897284 1250 337896034 337896043
    0x130209090a0b030f1218031b0f01090b04080f2802040c030b130e1216020925120f06060219031e2105070801063b100809 53
    0x1500e40d00c140c42d2225507103251410301c4400c0703070340c0940000c58014200a00803e180c41c0c202c40e01040d0404803000c2c0d0308a403850f000035100041e0700c030b0410005101c51068103005e90180c1c110549414050601c800060b0b0062400050009105640c082e03d40003849081c07050400141c200107030100d0a50aaa01522402a00c0e86056031981114005a0342d1480c950960240980b43d62595000e1020429100c40301c10b40d410458603146e0340400c1c2c4203460b40b4031130708056034000c0c40358a1035140c0d040c0d1014401030400085960308401185a22180e0000b075040c00c1e03542800301050440005c0c032588442d9131040f03550051100118480c90144616414000000c0d50f5107a00b00008020342c207010100c106041c0501c07149003400d8061802c0c591201010031020740002e42c2800703001002c9540c03030390b10003d030302c0544902c5000f2119030b92844116460200300300d410041c10049030f40a07406104031000803604420030130240c0c41410b1521714111602d030080150802e00800794509205d2100c1c104010b6250224 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 337898534 1250 337897284 337897291
    0x602010b09010e04060f1806060b18213007120503150a0609030b01120803070f0201020d021602100311220302030f0a0b0a06050a0603020309010212010f0513020909 72
    0x2c403024407036880741081e8000c0d15011400140043c5000018072151f12164070a0040318041c480612003140e84040e090950310030141c1d10340c0e10001444187d034280ca040c10100440100f141080d01c403c880300400076052048030b000c08100c03441251800034649a8811440740d482820800756414460076481e01c0f025801d8a100b1a030802500000090f00d81460b0346044000c240c0c081e10391040c0365280c03031000d841020b10707010035101818050f000007120310640401f140041d911801090840e1104102901c014215207030560655409120b40f0160520034400b809080c60002340d00801104c2d1401842144400071710325904040c20b240380d03500092601e000701c581e880d80b003641c1c540c040007084000c1d10710b011260308002d526016080718140010400155030003100e0084140c24400c1e1154402002208c026101344c0d40c03c151004c1040040b640640c0c060341c0e10080c250009440c4c0b03584030840c00040c86090b001300e00d900c0300e4040140524203040002008401018808501c0c0c20000310006050300d0000703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 337899784 1250 337898534 337898549
    0x3020319030219030914031b010c15020f03010608010b130302011412010b0a080601020d0e0d0201050c15041e02181e090106031110080703050903040f1d010602010b0901 74
    0x840c4400c08240c0700300400910b10000c110900004450b03460028402002482062805c3e01c0c442c0303000100b440c0c085095003071144a20035004083c0c07031007030041da5000c0b40084281c0e810001503107401c0d40e16607607000420882700400a441d98070340c140b440180c20500103800c04910700c0130502021040c0c031130140184041c0c0ba024200300b8045440c141c030344d0340746100d096101c1e64039580000000400000c0341003d8400e44020303848102090b88c41e03000482c0d9844003a00c0000020388501c080981a0410b018500441030041c50150720b0103960545c01c525103a04800b000000422000820040c404a5842044003030849210340c0007110701d50700090350f422190803014851403680ca0118000c002001580250328001da0681c410b00d1130f080403403a00805891001380c440d1102e10503030003450f10304002c0e0220311416644a481c000e4596680440051038000c00440251200304008941d840b18020244003d040e04100007007030302150003800326641e00c185c4c400300a40e0704040301d80e50f1994032000d8490554201d07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 337901034 1250 337899784 337899823
    0x904020f060d0212010504060b09011e12110c0606010801050604060e06250b07030204060503010902090a180b13050f060d0f0f0803071d130b0f0306010f031a01030203 73
    0x8000003145031046100c603001d0030f8400200160a86444a4003604913035044404202440ea5041c0300c03d4203102e08908a03001841200d803500d000900d00006130040e48051070803124080c0528105400c0f41c0d400c503c80d0780d1030200440d07000d0b4004010040f06034841028a07001d0310039403603c40458103e020740d018240030301507841c0e0141d185403245d4003a030741d001b4240b920000f0085080004e030100d03140310a00564501c18014001000b45000c1d00803202224290380c3e900f45141c2c6003282510094124140a6620144004000070801c100c0c0d0480d000072a410900020043c0340c45041011140f0482492203110b07003030104020300d03080001c50300c40c0c4c8444203541890798001d1614050b81c000b072445400501c40310051031400c05010110340514810404c64446840201c1b84c070f0007850715441141c4440c0e500c0030104407004646d00380341d0003c00c00014060031031640190301d13600190404500360080015000f40d02d9007081800941012031007a455070703250a0541d0350441c0c0220740c40c2c505007903845105144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 337902284 1250 337901034 337901059
    0x210c15061a0711060d0509240a05060f090f01050a12080a0507031707020c010f050c1e01020f0c030c0c0d030c03050313050a0609030f0906080f09150405210702090402 73
    0x100c100c903c40c8080300401d000c0d0f039a81c2210072000200001c2c1c0346000c180c4100760803260301424640052080d840305010004540d980d0300d904c8409040001d0040303070042c0d07201f0f00d124010307103405c960503004440e140c0322140c41d581001c041c4070701440c40e9171041042030102003101c4080b4a02000320b6901c0040c0d0702e8050b40c1c511042c00c060b0381e070000c81074501900250f003004110f00386034041894403082c1d0091380d51411019440304126803d001c0c081c1c840d040c81d0003407842941b50f00d41314070500c00c9004007030001504220b40c0900c3d40007517400801c13840046420009001200350010b01c650145c031401203441ca4080e10003038800401d042900030b401070070301c540040400d0300f02d003140040c001103d40c4241183c0c44e0001c1d071316015014005c0f02c078044006c1642c01c174803440c0f414003510480e02611080da98285050351041480e02d007209029150341c46a02400100b10300310640380e2102c912541c0a90300400780c400031800301c00380098849008181015092140c0401a514a18030035040f5804a90354a01e80c807 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 337903534 1250 337902284 337902293
    0xc0c0201120b0a21021801030206030601030c020c1c0b1006140a051b0c120601120206090f0a0617091906090212062e0302060702010c210c15061a07 65
    0x8040340c011005403c01d12020310380302c1391409290b1002c14401d488001d0524240300840094403020f010084d8003c0c000e0000501a510030340c0104000302c0284100d40c0d4600505000c58841c0d899010302081007180d40c1c051105111300700040303e8205103400d410b0f1840c40d2806c10010600c010750440b1200c007420004401d10742c01d1050060754207841c80710f200c000d20a904481c901d640c41c11416010f40c0144450780c402c8110030b5006c51aa4100c0d070910141c400c0c80d60066080241d01e6001d4403100e5404a006000c445c400d883c4c0b641504054400382d15514801403d095003000301900c0140080120751040c401c1d04502d41d010300c040c102d00c82e846080803490ae0320902c006070080300a1400c40620b44035540c200701a90000203089030100d03440320401c0041c80c40910810079020f400d40400b0b034000d141045003100651040b06007400d803e008041c51040c203400c403c2c030500046150a46040007541c0c0c2080007060241c460000c96843e00c2c1c91500700040ca241030000201c0c00944900c6404000d80454101d0502 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 337904784 1250 337903534 337903549
    0x1206011511010c080105030105060f0a140406091503020102161d06040f0f0c11012702060d050106030510170a080f1605010f060f0f0302190506030a0b03010c0c0201120b 74
    0x100e10003c0c03000c0742031400000c3c590f0900348507545c0f00e9030a002c0803a010742401c1304a186042406040390185a081c1425504904a4480d540c0c1c0c1155503400300142211240c4101c060104070380c406054250b00d1800028600548101d09020321095100100540c0c0404a1695182c0c029203124a00ca552514009002081c42402d0245840d040c40c2c0e1180c1d40551369401035102011340d8850650300c603001e4444da0700700c3d48020701c50402c05520030305180804c07042c20700d25814980300030100d03840c210b6140100c1040d44c400380d114101090f02e92003070140d003e006816040c0640215880b0051094584018039600d00039050060000d06001a0315040c072080c40d4103c40d06401e5108038000c5041c81031900310700921111810303025203440d0400201d1504403c1d600c010440e84901940708000d8156020817606c542e060b0044100e003050701d840051103860b500042c5118031201c10b07000424003198000c2c1400d45079104012410045001e07015070050f80c01c14180c008040700d494000803080040000300340c11 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 337906034 1250 337904784 337904807
    0x3110307031b020d12020304051f090204110705150603030c070605040305010507050301081b0612011211060a0f1b05070320090103021c030306051306060e12060115 72
    0x411000410000c8468260308071207140450300380c0161851144003030890310340e044000648002102d42c11005040d1115401840e0010701442c107a81001c3c24001507140905508a410001240c0794950741b019171420303100348103041400700f9401c0c1c5007564603a030380c940713035489041c3e14155160300d0004620603480800545070351484280840710700c40c0e01c810000e0601c0d0072905c4202e6842d030a24000800c4184108103690488a106000b40703104c9000114440c02100c8101d02541c004005101d003003013603070510807018028560041c1d407260b00c01c0c16040407240b26581d03018179401000b0411038034040d01d81c07007400c2e074001d410145080e6241c00d800302010106000c2900380508103200e144404420300946240301d034124035005120082c0039030b28a013071025014003440040c0d40204021a400c10202040300e01816043c4207240020317915442d00c00084880d151107042c0c0e81c12a9840009021203078002c5070501c1019411100c5246000c0c8001040d40e42d6a0140a42c5240c03604200784041c0032402011152030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 337907284 1250 337906034 337906061
    0x70e010e18100b09090c2b050106061e0c030905191d070207090b0d060e0f060408090a080a020f0d230d03050c03191d15060102010b1504090c03 63
    0xb07403030149200c10780140010b05481e500c40e5140d02d0104481220001d4141031a05004c0c011080c16260102c55141070b4000c0340e4581e010003940d5640c900040c40070300c200b030080c007a580c48045a40124501d0340c0c0e800d2460804040074000c41c0841c1d0380100f070b000042e80c0100d90701115112042020310300300e040c58100603070000d103034126005040c41d024120f001d0304601c10503060b400c880d01c01d9624140b96003500e0f40b042d2107a07001160b980c202408038106400c8990411a100c041b1001c40380d0625002e40351040880302039070750708400318200d1581c2c0303418400b0f03500410110380100a000215000208490786180c425403103004e00715076810420440200d0040304090514820581d0042c0040031a00c3e003202402c4403000070f14010024100c80c031040c00707403401405010701c9409030b1403054281100078940800c550b0008440703401c20b5904000c1c10000240342c10310000e01b000762810100006803d5407840b80c8214030a4801901da2461541c400c0c007903404561100d034021030705042222040e0000d00d684990300c107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 337908534 1250 337907284 337907293
    0x130e0304081506090f0103021c020d1212150b070c0506040324020f0a030e16091d011b0c080f0f09030d0503070f0e150a021c02070e010e18 61
    0x1826181c04a01000c0c02c0c100100000865912a0704200340107100b203d48200304a00c0c0d00050000d400c004000b940e00c070329035460f03448029125400041d44036030814000c440e44800324103070750716243d803244e00c4600340040541e0a0080d0380c0350300501c401c40b0b07069025085481c84041541024803118204010041902400c1c1a694503141d0034503020004040c0b0086100740d010700502c00842c0040d1084445158444201509000380044105c02910544c100c416007441405240c1c1e01c000780e02032551f4010940b941000078114030141d00498612107646880321143d14142a41a40301000342d0944184070f0395243c65040d0006910f024681e600030780f85200c211890100300d22480070340030401020626400c6089804440754a0f008403240e10089424100080540d02d050f110715004112601c281d090041100140040f4801003091a81240c100c0b1001a0f018048100c0006414105da0030302604a2004d400c0c0303581440262840418103101d40c9090600d490700043c00c031104a861010888145010b0b41c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 337909784 1250 337908534 337908539
    0xa0b0a141807050102071d06030106030606080a0c080c061207180f1809031209050f06130308070e102a060203010602010c230c1903020610150806130e0304 68
    0xd018030a8241078000d514824800041419800000d00e0000c5540c074112081030502070504c0c01d00d0009000e84515019900c644c0044001555800390314040c0030301d2002803240c4191810b20b0001050558000c01d80d41d0007a41c007000d40ca0f11080220391040790550061030098492a108440342002c203401895901000c1102140c80034031100000c0895594146000080d042c1c038040e0012141401002004141d4007110801c4001040d000806140d0190045d2242801c1d000e04150800404590760800a801c0101a40c1003541090b00c1540000301441e0034510b81204002007003103940d050201d078040c4a03c4ca2441000e01d910146004808040400e00d00c0c178500081c5406c0f8042d40080c0500c0016500305401030314501d120f0b08803070091030301c83c00c56042000d03215416850980e10441d4580308600458404008060314003820b0002180b007903009048901c0c050703042c1400c004040d04403071500543c0e4042200c00310343c0300e00ca40b504441c0440704c801842c03082c5c03c450001070421100c00c00c880d010201e0300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 337911034 1250 337909784 337909801
    0x30c170c12090102090d031107050402030a05060a0b07050a020f0d12020106060207050d05030d0c05070b01030c0f050f06070b0c04170c0f0103060806010306020703050d060929030a0b0a14 82
    0x90444180807118591058803056401800d034000d000c0320a40044e0b11942c0c80002c80d206695900e4458660002d9510054680300814142ea00072910043c40a44500a02c80781d402c2c0008040010038100c0d003e80d09110566403030380c0c1ca800710003002911a01981400c10260390300e07107456145483d4002e4440c3c001a11111001c0c0c013030270452081002500890740c0c0040c040c1010000a503289521902640c45c0000d01e03042d0800072b110f20303600002004000c1c0408400240015043ca000c0c2d8090605404000d1070280444200740c0541c210030700403c003059603030040e526840c0580d0b06443d4407001e01c1030b140e07585840c051001c4c025503000c070001d010001c000d40200d0b207003c180d0b402c0c12142a01c503400303050f00380801035046d03420720b128086841e07000c0c80c01040810f00560280000900c40d10300b840c90081c00c14000020344005400516003165a102501140421803042680060112500a4000d519140000e40380d0903541c40150131000c0600000b6480c7d403045d8060444071103040320f03008044c2445900c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 337912284 1250 337911034 337911037
    0xd1a0405030d0e060708060307120602070c0b0f040801050903130b0306121e16031214041a040e130203030406051605160806010602011b05090103140f0a060b120601030c170c 76
    0x5111006c201d098003c5402400c4c041180700c10b841b5185900d40c0040c031036907207540003941301d51019114100b42c85408500707080309074010301011605484054655080900d10743c2142c0d0060140e1f803095004120821061446512140484035540005500c03680c8020114450003031820040c90705001c0e003000d0b001c03d20308801c0c070548000407400846081d0300914101c0155110030380000303000424400c500c400128441d2980400500d031180d552810030341c0d2181d0314036101c424600c02038040751021906224999044001e21b41c041c1110001c02000710051300883d13264403a5026400c104030001500022083c0c0c50321101002d541e024003120b411400440d00c40903100c007240110640d0b800390500000742503105005541c800541c3c900d80260a00800b40c00751a15409036149034145912284030000040c01008024032071f003c104201310700d6103080e01040c1d0032543c4a8204a081c2c0e40709102c0c0d58542030307242d400550721a4003824005000304e030b014805c0c0e969a1040d04c2484603002580304001d45154080e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 337913534 1250 337912284 337912291
    0xc060a0509120304110f030712030306030311030313020f01050f03010f0611060c12060a0b070b01050102070801021804090609021504060f0927060b0a050c0c0d1a0405030d0e06 77
    0x40503150141084111490248070a0700c0107481c0c001448134000c450711b04150f5519131201c004045a642d50740d0b658032941b1034001c0b441d00b030b00400d6176501c04105140c4c110b4035121141c0b040c603014515510b0880c08d41a44001e2001b000ba010340c040346800c0b40700364012021100da16002d6907200fa1250f94803036130310244032440d008440000703842a034880213000d00050321502414001e80721904000c6140b02c1203071010750050107075501c224a03610001d000c44003003005040d12401201c0c4410298104400680741003070315440414642e2040110038080d41c0c090481013409101220040303a941d19500701000a40000c0c200070f580801c41809a0741028100401441210490780f102e40f24000311a03429a54a4042c0c8601001400d071211103441c041000c5000ca169a5544200010280c2d00c0c0d560303544681e00005c3c02880480e100186800d608201000072010074034081701c0304203142c03007030303a6891a03425803407001c10b54442d035410003040c100203051080d10104003804104200820050300516511607090f03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 337914784 1250 337913534 337913551
    0x60a140904062c0606031f05060703030c0f020c0612090c0402040602250308030f18030301080f1504080919030605100504050609090c010f090302150304020a170a02150c060a05 77
    0x3000364143c10500650000e02c80c01009001504544d11a50111a4111101d2070309000307899204000c41c0d5a62550041c0803050302a980002d0b4140c50007402600c0f40c003204100d8410b55105000c82000c66488100f00da5045850a940410b25110b02d44000e1038004800089036010b400442e022400c10f500095190309c032030304801403129108242d00e44d050140100d02014011041c01c2000a403490f0a00315a150030485400c8200c800c0c40040d24400d045800a0b0070511007a04907035814402c0d08800c1158400380d8089a4bc3c01d141390409585503441d910440c501980074160004e0344100c945641c0280c80010340e0032880c24041845c21144004800c0c98038003506208610f004041041c49c20070300c0f0b0b01441818000018105002110019141050180748a408001365800040300588603002490031030f540c00284a9220b040c10b1040241c0c03159981c01145000014031142c0c1d4120304c00040e290754194050b1601f00158944a4121340184600500c5003c14410b00c800e1105880310360303225038480c0720352 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 337916034 1250 337914784 337914839
    0x40306150b04050a0911130e07230301090b03122107020d0903030e0f150a110312011a120f0603010b01020d0827101406040b060a14090406 61
    0xa0302018501401103000c0d242d00071300d2049081c403601c5201c0d4001c40c902040950f029080042c036001504046100790010b29841004405111000340c2104034810701c0e887c110313410845075881200e44103290105100d01d00711252622507a4186440503c41221a4040c00030469a1000c40341d90100d0940e64003c0d441000e442983c001a5005102207030b00303a10040d15a0f01d40520625684046905c45045503400307a0082c000142c509443c0d030b481540b29100341126104c41c1c2c59001c0a0006482a2f10440c6030311400d410412038075540f003034140b855505581031003540c420042c4072221128114044d032403000d0b004001c4030040c443d0900c40c0c401228031800040b0700900844091800490b116030503e1001e0000c14071180214400b05003030158a00549007801f9454000003c0201c1c031450b029920070304030b26059890900000b103045180040e540501c068500780260800c14000c90031610445846a080240d003096080b00088208126808a0401031082c40066203518607070031600d03040c0c504110002d15 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 337917284 1250 337916034 337916039
    0x30f1b0907020d120609020a091406030906040308150612100f0b0d020318010c0c06201902010e070810140609060d0f12030e010b01020625030b0604030615 68
    0x4000301114071035803180e07018118280c0b0301c00040c4e60714010320728100c2c04203803501380204442c09544040e02d242e02076950b41c48116480c1034443d0501d01d0313074098950b0050030300704104400c05200050303580d0403650528045050303075035107090b1124803009041415400080028082c4c1c52805c44d03004d9902805818240381081545ca40a9205480c0c151082404002041c40380340d440d5101503000d0b40c0e00104582e5804940c0d25850300306404c4a41c03a400407004202c0510b035010502a2134030030448040c0800403445007810121003420362038080c080c01d2a0f004000d0038005090740d8800c0d041102c04440540440e0200c44e102e07064261200b80000720001e0103850b10235000c400600051296010310806002e480c22500d843c1c3c2803004401565400307941180c01c01d1011030002e244c07c00584a158110341c0d002540780c280c0481c150a4420840c0e806045501100500444016800200e6030400300c1190024141045417016000350403c810340e88d5000e1000308002040c020b00d50486655800c000c001128000d8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 337918534 1250 337917284 337917289
    0xc0210050f151203040f24020604020d0317090c03150f0711070e09061e0f0c0306151602010e09010602060705031503010c090f060c020609040f0902030f1b 68
    0x20300480708501401e018401155010141840001c1c071600064000303030b4040200ca0990b49954080c0e4000b021106248804101008071280030300b00001988062081100200758000d41e9075402420180c85002c81242e84010580100c4241402c0c2c1c0305000020382d00c0c9020710500c2d498030030034550f590082c0070b091071071032a00032142180c900c00d0360070241043e000d444140e800c84d610512400704100714070440801050000c0003421151003036050500820f13061415811040d03648080450350f01b08004604244215804031300d03031159100c11b510003515169981c0c41c00240391212000d00e0300c80064400900c6895910143c3d180c25080d5000b0b80b036891402814a0910094a05c244a180010b81040d000708800520075001540c0100038805580e80103c1c1050000c0d0844040c0003a04010403940c40c0100094501451120002e014509128144c04040c0c2c002c90312074842c3c0340c8841c0c4a5640c6910355000c0d600c8583c4202d1065802800711042000355014460b5200081198044040c440950074905032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 337919784 1250 337918534 337918541
    0xd1a010b04030c03060209011808210a02060609071b030801030614010e130309030c170f03041404092612090a020607030c06060b21010915290304060c0210 68
    0x2c035402015030441900d0b5858020086d001200000e04105d00750500101a131101c0c016a4041e00d81c0c54050b1111254132020f5034034944031812035800800007403000a2480e0703008030b03007258010360940303161896944041c01100c00400c00210740d2103c01c03280011400303240c0e211000b64166445610100043c07500380001c01030740d83d000d10540103000e203404d0000c0e010b0321080d8181005c141c400d0901624098490384c0302240f29016400288070340e51228510000d0440030003001c0800076811015601d09410b10f000d0a01501c01e103540d49015036103501d070400410226003604075044070440b80554080c070700d0180604043e401a003280c400314000002095408078041880d2000c168010065071800343c02d03950940d0308043d140030640708940e0301d482c001209904040103016149225645c4038250240034590500d000c410f820441d1450f15041141d00385460440e403a00549018410702c0c1e0031006401e410740c076024a40e4100d088181d8020040c0702c100003c030f812040e4890070540941e802c00003008089001ca = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 337921034 1250 337919784 337919789
    0x60a0f030525050f040305010921090819020102070e07031e0203060303090103090f050a030203030a0e0a05150919050d0305011509150507081c0b060c06010918020d1a010b04 76
    0x7800b2425462110039024000502042122070802ea082030b40d60780300c00e8215840d814044d03414400001c5100b2011081403044c104402d0141426801c55041490540d034880c40c424a121844d41800c1302003046d68000c001600090125592040540c508820024007a01c01c0711404036090707900f0310042d407840070580256482450050029410702c2d100341d004601800341101c0070f4525407442481440840c00600020a209009400940e62414030700c160404840001b01907035933503000440c0510000e000403d45203043e48966020f6002c903103540d8000c0d0304142e040c8068540c10300040b15440104980424058405002520200480e0f82d80306100400420b2801c0da0000042480b80b00340031110240c031101400d0703c014a01035003011a680c3e510a12640800520080110781620b0750007415030502820010302402c0e9421341c04c000304640020755420060180804054035003914205032201115400591500144401c00041150519080c1b04480d05a064104030480d00041a1980340c402103a04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 337922284 1250 337921034 337921081
    0xd050915131502131e0509180304090b010201061d0a06091e0e011b08090105010b0c15040f0c061707081302061e04030c230603070c030905060a0f0305 66
    0x28802e50004161009600000680600c500c40719404101620081d0f072004004000c0e2100810302414113003044200e08004001d46c001c0e5842e0301014041300b5010055804a8887c0b0340d01207204403c100050b409020790707400c0180034142ca030800310300101030a081140501c0504034200b2105c1d488404120642c0c605940080031005000c10b034602040c204c1c1d01850110401c9000090003400f40d090041045400c9003910002800b00414001d098030300388202801005851255032601e006800c0d9107448004010350318042045400000d030900071851075481c645079110030391031221521600081d0124140001c1400c1c001d212800003100540140811806400741c0480b14640ca031040d070801400398082511a0145491540daa5001080a07400345c0059481481c070f40501c24100b1407048845601c8150800c00310f280f0440961940d04e80c8000c030303070f00802c60717290002c6a03a00394201518604070540c04a500001c000501c40d00b0f01d42d0003007410384502c081c2e5805100c1c60b240e508520410380411711407150b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 337923534 1250 337922284 337922303
    0xc1606030e0d1d0d1205040503010f051509151309050c0f0109150e0a090c020f060c0d0504080c160609061106010e090a0c0303020a0201121a010806060d05091513 71
    0x1c0f20742c07044042d15000014000d12a4200010b1980d0300880390644541d15404201c000c0303001e00841c5000e0007550b0316014210010001031802803c0c1030070160b624540341d4050380000002c60081c40c5544403a031102c50019000d405e510070030071540350050464101c261058050032044581501d00740c2d04035205241c050395100d0300181081e0b40d41700204900041c000c24410408070f1200280c0314040c4202c02000c05081c009501640c0c040d020381005010307600c800ca1608100200003040050200f42c0314402606400000c2a540703a00d00000144560350041d2480d00c5035000124900c40e00c03400ca00143c40065450b1082c40e0354400044d00e0140b0140503c00564004000600c109030040c00380e958000c200c1700c100c602407069900d400009025581040e0b0050300319010100035540c0004101c00f80b01c010901c10030003207451310060141420500030140c1082110800b01c0c000d65200405e503000b154000d5000c010906003902d8840d40ca52800c8c802c800c18211074000980000e00f181003016004d60081240d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 337924784 1250 337923534 337923557
    0x7030c080c03121309050405060402090f0106020d0c020a081504060c0c02030606040b04060518090d0507050d08060402041e050306070c053c0c010201151206020f0c1606030e0d 77
    0x2442640046010020f21500803400007600e2505006e4240036601420141c082402c0c00e0060058140c0010081840c415480300104001075000a54114601c06c9283c071601010301840005c01c0f50f80703151310600ca46c0c807921025841b8284400720041c05103100b00700800204400030815180c46070a060081c1d4190001400200b081c103094100300e03071740f410080000481c3c64076407001038040b1a0700440c00c038400e007182c2d0070803005201c2000748050403005803d1083c20b050351640c03000c1e91901101032020800c040d52000c100181c40c0c40d01510081e000c41d088903081401c003034551100c1d250300f5200d0244a40f003580c5c041a0214003c8007583c50894101014114816040074403142c000d403400043e050100700401e415101d2202d88801425100c0c084000d0001102484002030a407500d407a6100d0200103580e0080080b600035103440f6844a62240001da00c403981120b90352041e00a01291744564011098031002060310742c2c0302d9005030780580e2802c02c2280645851582da40d4190b4a6a00100b8002c0020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 337926034 1250 337924784 337924813
    0x7030c03180809030102091206090c180711010f0204080d0221030c0307050408121812100e07030501060806090d170103140f0a0b070905091504020304020d0f0507030c080c03 76
    0x3c0400001c060000b51500751400c01041d540010000035500c00d0304054107000c0d05071428015081075460407038110b41601c003503c150600703a40700030f850346003400342c120001c460820003900000c81001880c0c0046403034517565800c1d651101403034400a4014014031207400c0d000450410441f41010b51701c0f10480c11075440c100311005590003c0d2600080c080244000907541c142007156455080d0328102403910344401e0365075000806001d46826105051030b0030304100c0c0c8030000402c13460311081800081001c050740000d0b2400c0c9074807600050082e50800d000810105000298071b4058281d0f1000c0700c01242078410216488081400400600d501460040000c03440034100030344144440419225000ca000803d9860000d4074a000c903a600e2100e030401500703d8102000b10000c10003998104042d190000107208062602c0306042d00c10307a03001c8040340035504d8458000c1c1000f81d0084000003420390f1414110f60310040340c4001c0310028000134001c6804200030550b0022800d019000f00080318480c0391 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 337927284 1250 337926034 337926037
    0xc0a0807150c080408030403060b10031b180e0408070c05030d0e0405041a0a061401020a030e240309031201090605011205190606050712020127030c120807030c031808 73
    0x801c0d28207041c11300001c19400c42c14001000207601c10540004c06032981c00510081c14020f140b440d040c54138040b0b40b209075210142c14440e111145280c04511261404c8085000c07040707640041e00301c40705020800081009000c0100000340c007980b58040d546030b4400c10140d48041801c80c000006804850380d80c0c00c1d05040c1c0106801c00c0c4100508203200c841d02d407902d540da2100300ca801c01c061fa150202000705201400100003c01802e1025110441290714098056002c0d40c18250040386d030200414801014480d0000c202d032083d2680b40d0352414480b80c5070f0b0f500c0e00310100f4004440345401c000514121103100c1d60003141c60607141c241c01d203100714a44038000d0000600c0d18102100c80c441da0003201c400c51041e80040c28a40d00c0c1c158179418a8144041206d60800500040d603141008035040e070b06003030007444510403440071611100c58440c5000c9a00803d040c00090a212000107804a00e40c1c104030300d94410b1000344e40030860345080d00300840907a594007030380e4561140d84038005004210340c0e10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 337928534 1250 337927284 337927307
    0x1050a092112020c0a0c0902040b091e03120a020705030304031a06040e01230105040e03041502100c09060e03120921060403050403020114031909061407020c0a080715 73
    0x1410000c0c2d6080c150b81c04207992000d000c40d80f45400041d1540100092544040d001d400004e0003113007014188580200103110308007442d407286001d002129004030b201c10342c00c5224440942a00c0441400c22902c0905401c003481c00c030050700070003d01260a09001058504072600810302c1d0100d102201161001b50b40302804d4160071035203805042d582d28800f4016987d61160310708040d98859025480745e02400307010f81240e4030450400c20700c08518000041640c046d10040c501079803d9008501d41a868000340c1030314509070038100814002c545411000c1c840c00c0b2029902d4005480048104050300c8400b090010f0308081801e0002880c0c0b418801e1801210741c803480444441c40024000851410100710b90440018900050510455900040c0340f041071980e05010782c29401d22000e07032251400d6848846d850199905915070511400340c00180c10440840f0820782903017860440252151100141e42e805541c2c02c1c1c20020740b038280003e0460031a422400b2034803101c11034040c100e41300103584 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 337929784 1250 337928534 337928537
    0xb0106020105070c020906010c0f0c0915030809010509310e010b180618040c080f0d08010b0d02040e100e0c0909010510020a12050408070b0c0a03080615070303050901050a0921 77
    0x409c01071001500c0032440d9130506009030401003c6d00d180c0048041540c491452090000c0c2680d1010000104483c00355071003403074242002e1fa10740543c00c002c00c0c0607107404188800200c0307000002000403801000c1180000460080502000041020f840d00f1b999000d081280c101800f41d40d00e44082d2a110349003604080010488c00e8024000d008000d1140c4007514140d446e0b600081040103100420420304401c6803c2c1d002911244a1104004c0c12240d01403080300411100080c500f6a55035050741149c02600301807540e0300d0942045401c0c1d2010f88664001c1038148010306004c034038141c8030042039031800140100444c090740c0c00c2000344080300a20082480a40c815041e8403400500005081550019a980c1c0e241d02d0b189082c114510f001c265502003007002c0c004012481d80050080b0718002c145030141030140054807002c4c08610b01d030003011203600082c800494980c0070550301d82c00803030162825000902c11a2102d140003c00c9620b08940200b030365901c0c0c0140e02d01e00103d0102d00f620034406 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 337931034 1250 337929784 337929797
    0x41e051804050102161415010510050c03041d070801051c060f1b0c0506010905040818150a05090f030d080f07031517010e06010f060c150c05070b0106020105070c02090601 75
    0x880c03640d507950308641017044801001c0e150006490060810910382c00c1e05403809080040e514020100711007119500b013450400c200041c1c42c1d061144100700b210003c1203c0904507628282004100002c0e00f0182c4200001800f11800024249071007882c10101d0045200858064401d0b43d07101c2008002201d2580030642c1c8802038881d007a03804d031b060322030306003055216101a00d03010719090341480300507084500d6203443e12040c40007180080301070f40c40c1c00c86500c540707030044452200028041003584401d41e1b40c41c8400124900010f40c840003514480106072401000701d0f01042c100b58881501500710000142d0200003e084820525005500301c855402c000980303003161a00403060b2001e641020a0740000e1443c9141240c0003440f0342c0e82c800030194003400042d4141141405038100c507220389010040301003d4401070110385441603032a814a0700007048202c1d05014054000c2d0811031080d9490700650f000011040e0047c081e103441105140d4480144003181d42c00c21103102406030800c0d041051 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 337932284 1250 337931034 337931047
    0xf120b060f0d11040e1603090f0f02010e031606021e12130308191d090408090109080304090501030309050d030c080711090a050412030c08060d031b0602041e051804050102 75
    0x48440040000e856128003405e40341c80d124030395441d0340100b14108801c05250038040c40c0802d44014409e180542d00140d5100b80b8005400100c45042c0840c4002d03515001d845890703011603482c2010785044440680075500c002001e0035500c1500300640c0d4034035245800002035071107020400070080c1b91921024099a00458807038403050400c1d0400194084113845c0d5950b401042c035000721404c107041c0d0503100d245204816000c04a04e9100c806000100781010104001c58541e0280480b000504080c46c1103949540d65140d40c0307800b41c0820300c000c2e004501036800214031800c04400f03d294581d00b541f90200307405007507a29098543c0c001034007903840800d0070041d164a83d40300c203032082c0508480007002c94103003040d083c01c01d0403c0005151b82e05142c9804010b10060380c0020b0a554040c9088912a085c01007a080030b6650404004810075100240c4030004d0070030059038085d0054500b184a40d01d102c1c8105264140d0040403401000c0c0d012600e10050b01629051808569100d03100380005400c001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 337933534 1250 337932284 337932311
    0x80316080f160503030405060c0309030702040506010e0d03020615090919150204030506040c05030f070506220303021606140d151a041a0403030e060310030f030f120b060f0d 76
    0x28602c0b40102c5140c0c00020901c0180981000826044000480b156103181070002000345d903441940c400901650301c500c00103c0680c0548000301c0f60400243c81d484c004c1d40280f1f0000d403903041c1101c2c140041c1000c1c1d12942d2650a04014051250560780c000340902502c200003080c8010912030101c035400c1102030000f80c22074250000c0c000440c450001004181058503002c0c01c082203d030040d42c0280c0c808040c903030100100041100498600b0340b82a80d542c90b40103804071181304000640d8072902c0c00000008100350380040d4a144880803403100607a100d0301d8a50446000e462140c14070042002484030700081106a44078400321804007110f0000e0b00d40d10300c44032018547c088030000c0c000344041010030035880103030310010798a207031102080d10340703401d540e400741401d8096041140a04000310001c3d01c90350720422840301450f00942c011300400702c1c03407900901010003c8000400195043c0a220010686020f0150402c2d0b00400306414445101c441410607000300c0ba050728500d856031580a03289 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 337934784 1250 337933534 337933567
    0x4030b0c040518150114090f061b0d18050d1e0510150b090a0326030c13170c060d1104080c01020607020a030c020d15020d06030c080316080f 62
    0x1c01d030403c09000c0750310344681c0b8000007200d4200761505000c01e4642c2d07070003401d0200003121050b2408030707080c21410303a40901290481c06504000c642c0030600d040003410b0b200e00080e801e210081e55545e1400c078003500358002180100284a802d0300305901c00401e030f002a0b000608070140311041c800c03541d11580c0d2500da0700e10700f4003100c455042d182d944142818101040e1061070003e00a921000ca181550382808190007903401d100190003c50000c44000c0b00071103801a10b0b118003912041141c480c01d040700615010752000000583d41007452500090000e800340c00c0b0101c0740f8030170000e4080030185000340702a503800f4503400000b0366a5800d54401c0c0700d0050700900082d040701c1e40105440c0c2c099200180c901100031b00b8450941d44070014400000e070b0b10104022019605450500b017450fa03910b41083c0310f4174607e039605001030001c1030b246003068444e48000100c0b400b41310040c2105035100c0100c0e80b2031094950303104122810b000c1c0000822a15001010600d441c00c0c22603140941c00d100c20b0386007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 337936034 1250 337934784 337934809
    0xc0d050706030906112b060303170601021207060c0e10020615130c08090f01110a03150f0b030402090f0c0d02070c0503070b0a0f020d09060c05010f0f020d0e010b0604030b0c0405 78
    0x60519280704001b9082c00203103040c070350644000c0200300843c10364034041e100d0070440a44804540f47d1000180d07aa0748203010200000001284d896100d400514020000e0070001c0c02c124002150b1000700c0c0d03a01e180288603425070308040c0d006004076488200100c1036090007914002d0b00486011490b862080c2e00e8800d160329402c603503540ca880f80c05c00c58484c50820401503901c0340c4681c1040d100a82c02c0032090100ca28041351401c00290741c152940c0d0038040041c1942c4080d04071002d400c000034a40071036100841c4502e00c01c81e100e40d041d54800c540720710b0340e51007510300a0105105100d25800e8014560080861600903a40e4000c0c00b581c510010745080a590011842014042145449142c001800310700d8008a8000f4200c0480c6000000b800c0e02100c5c131440c0108506500c903042030110070340c4003584a4211440c02d00070000300c030354414040d5220014042120346000c1510007040010300c101d401c00503000b000507242c249151503400c4900c4002d0300405000c0010040060241d84018030082c9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 337937284 1250 337936034 337936057
    0x20d120e100e090c18060304061e0204060f0f05092e050901020d0f08040201052a0f0c0d0b040602090102102313020a150c08070809030c0d05070603090611 68
    0x121920200501250440203000500303032132410b10150841e008048500224030500b611940d4903903869050201c0074015000301d60300407400c2820390105400301d980060098980301c0d11076040070381c49074404480c000305c0c4280d5180010001d000344503480c60314450600701c04400480c0e801410402c650f02480d400008104240812000140210703196018401207000060909201041c082001c1c0060101c1800400090411000084042104258001c024070b20345500d82003400c0382104d24003044e540c1038444000091441101e50200041c03410701882e032040c036880f0413592040c1d01d40da680c0002a401c40c400c068150300810164a40c941c640d44a001112207001c02000307110240760700c12140741e080241c8080c1159505401810141e29151203400031201c80546282400028820440d80443c003160010b00f0f032103002a10000f4042040068021003004509032038440c44a90708104490300660801809500041c13010401a40681c0c002081c0038040c08000c2040f025802000e400350740800044107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 337938534 1250 337937284 337937297
    0x10603080d0f0506030609070302300a03080a2a030605030a08041401030608150a0b0a06030e010605040e120d020403060908031b0c0c0d020a0e0108060a0b01020a020d120e10 76
    0x540c0c0b00290040641000f029000703400d0034208407a1803a20f540c02804080d010344070318000c1c5194091421409415101207012081d030140300e0303902c1c460719059010130a40000d000000444c06641ea64490040905440b42e510500100d0b955019500c50081085c2e8405040d603800c80020552802e024184c10684600c00c821380d19410907030860054440341804d00e04051030410b090040080000b6100f1a0400072810444169101d00d401000b40c50180552600001c01c904002042500f541102c0341402c1200001c0c0702c00c1e6151020b0008842030f181c2d01c603030741c5d0b4040281041070080c0540244001030320b504004d40707801d860b5203940301914060102100c81c1c4c032001080045041c0c20701050740d0480ca584030140d1505c890850295076078680d000055200e4008002e45e03070110341e81d0040100c020403140303525484640c0e50300e05c045d0b119401107511a0b080ca0800389181001d40c80840c4400c049580244101c8000c0c00d15200c100c5a00c40c004050b000380003a410107481d10360b0701c1c03450003058074426a4415 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 337939784 1250 337938534 337938551
    0x40f0f090f0204030305090409140f03090103060e16050a0e040204030807060c03050601050d0b01050d050a020307091d070f02030720040c050f07030507050a0c140108060303030405060a020c010603080d 88
    0x1a411a40d403070100c00c0035144144070078000603600104417881171070105d40214410940f41001408550240d0900400b0300c91074880f01d4034010044023410400f082624200007150760b500110943c400201d6507c1901c5142c03014211800b80507401800e281c0b1201e140c00a00309101002080880c0e01641060b55600030104d100e03800c0060a020b01d00700f0380c01c0c40c0390605c0a0300300391002070070a024141994998940310844200141d10910503207103014070100050086043c42c15240000b54000e881d180001101110049031000040e403415500031206a240302150740e03160710032101c8101d400c2103107046000401814021a1100e60b000707222801c42e400100403980040104070445203c0503905003405424803040e286001c00200351941c01c1d0301405d00c603a850026241c900e040c5030000d480148481803a500200302242c403548800c0c00f1b0320080c0c039502c0b642d440d42020566a8082101c00801c0c81e400f40c00010b007100014cc010300b184100140c0007049003501e0765900c95030341d000904d82c51841591080790 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 337941034 1250 337939784 337939799
    0x8010924061404380a0804080901020a0209040f050c060f07030f0e0607050106090b0114070b0403170405030306010201050f060310090c090e010f060f0e040803060d0c03081810170408040f0f 83
    0xa03029441c100c1013285400182c50003d0010280104040c10301d200200e03020015034002c0c0440c09040340c1c020702c401120f01e45842c0c1120040030b9180113a0f258400c4003100007150a0001c2200c20b111003041c0683c1c10400255811078520700d01600c00c800f0081100c040400d135032182c10151540383e104000100321182014809400c0f5400e0030181030401070813080d40c0002c491001b08450b20035402040c05502c1d640d460409644001c1d0f9104580710701c03051041004103100001c0701642c085d21090307000f032010b501c40c0002e0240002c0c0a481941e030541100f01200c44039003241d80a407042a20944c42103596550f5844400115224000c0600d02e130b9456a8046000266030300c42c1c2009010400c000001e25420100c030440c561030b004000404c1d041c0000049107183e5100c411900740740d90b0111103038034072949a1802d600b8542181d07030a174100381100071121001d49483c2e1480350a841159880300d20402003c11144201400944152072403001040041940c03045001c0c0000641004a02c180710320b882c0140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 337942284 1250 337941034 337941119
    0x70b090a0b160504060c06061e06080c0f0301090c0c021002070e18150907030f03090602010f0608120706140405010501080609010903050d0507030b0d0308010924061404 74
    0x3214400d10b1240000705280e904003094400703503003035840d101c0c0c50541c2c0c6251120080249401600c0c0041e41e030006064407102d00700512050340c0f00d0359030340074441d00e0360400403100307015541c510700030f0340410300040c000140c03960b0025030030203528604103007100100d4020416201d04444144016080400c2c14492103a0400d11290001480c04940c059100c062610948804c2e005250000101c86407011444441041000700702179030700240715202d003c24a00d00a07120100d180f2441016502b0111400e500100074450002103800b52400742c54007084119004210780c0c07151f44103c1c1c1060f540e8454030340c802c608651041c400c034030403400080c055040c1f101031440c0c0000202850010782c10001c0203c0040e6100c0260b130400810888081a661a8030320245d02400c0075a116507084a400940d8206140d8000301c042c1c101d81d50640108000100d0303040c28103122132030050240e40c10790100c204102c01440303800c40c170560700305040010341000e84074030120070032000a510b4140701085515500050101d00700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 337943534 1250 337942284 337942291
    0x100603110a12050c090601171e0123040203131703010e0c070302070e270d09051804110f030a030201050103030e010e09130611040b0d0b1005120c070b090a0b 69
    0x482152907001550f9406950f80c001502d403502807140c18000c141180d008180004064408825500d410702e000607012124228502c0115000310300b400000482d4445002c0c0c200c860000d141d03120018454443c24000a540041c050002d004040030920380490b0850240c0080d4101e18013042d60f0741d514203c042040c0d5040500359001c3c1e914100074060000750002442811110400c00d6190b5554580220410040d251404007111950300303408980d21810215000da2040440d45503810040c1d110b5080c800c8410030340c815005046152804100410869101c0040e5044002c250110314003201000c0780c24001d0001d811400341c0e459500610825420200e1704030411001c1ca803010100c3d1155000404403100a000300400415410044c2d040c041c4913040200b0001e0400d010f80d64582d82c50700c50140300c0d4030009007025124909495404c41c2d03d024842090701500c0c42d0b440c582401004504583c80c1d120140c645003403800200007407400203e181c101c90388102d040d41c000d0b051545050400801000c0b009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 337944784 1250 337943534 337943549
    0x30d02030301050109120519030305040218090d120207140d02010f0b0a05060901120204081605040c0806060c100f060612050126150103300804030e03100603110a 71
    0x5000612081e617010300068211020384103401044403417403c2044c00d01102c20368070340d0060486080002815015045940074a100341d40d020045074611a08094600c0d00303844401958100f1a03a0b11030384d81c0700d1994120007814228005143c507080756114194010240041d401507081802d500c80741580a1240300b82c80501210280306141c071150009009202d28081c1d81e12031380000c0341c000700c01e91003440b409600009002c011540d0b19101e0485903a54003d0420740d0300e55038038002d000706180c20240516504450161a50580ca8072010200302c815045540f9512440c03040002001c04c440460088205880c1c030314400040070f44c10100000d104004072200e0006040c100001044018000c2000c1080200c100704cc0d58041d0300854209070404c0f0499081c000301501400c000f109201700c20f0790801c0c01400c1400e072004605130383c1c1c034444000401e5044620100b482c0d600040c01084c0a90b0034422040c0c2c0040c1613031072441c8500010003c0f01c0540d001030b101d01c0700003070110307200313042c0962900081c20b00d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 337946034 1250 337944784 337944787
    0x6101701020708091509091f08010b0306160c060f05071419081005090a060519080d050901270503010b15031306090b040b160c050303040f1e11030d0203 67
    0x43c0c80c1c10001e4403030180c070741d0b000300d1602d800e0241800c40c1d00f055581003000201032110a090003402e4071582c0e0000c074080140f208228400151342d40c014030400b000000c014025150a50350064501d44242103101c44405200c1042000d03000102c25200d8504020340012000802d400c21701c900400204005080c1404007034100440c00c81c0034540d2500b0805407000340b500d031080c1d50303c6250340b040030186a800f4580044603001400080e44003904a1010b5880903100e520106c200c041c07a111140580f8403540d1015004004950b902c0e610a0000303200ca424103041c05100190500c40d5640d408070b08c0c040000d541280c046090040b45400c2c0200d0094020031201c00a00d8440000e01240030300c0040c020b000f8040e500400c490800c0702c00c0d005000c020740c202440304054a0141440302c00c1c060200d0b000d44800301200484c00403503001d450142c0c49550010001d50543c0e5503903440f0328070000c11020544e000f0402c044d0312110340350500785421902d48150800c0c0302c450603d900341407500b101c00c000076056400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 337947284 1250 337946034 337946047
    0x3050a1a010206401203090c0902180d060e0d1805010c050a120203210411091509090c090f070219060e1b100f050901030905010e0610170102 62
    0x1d002840c660018000c110345214843e000c4504613a1803512801a030800300b004000501d10580c440c0c2c0e01c2200341c0100f9116500c1050104102c044400e4031340001c0c140705401405001103105940078011100000944407a4a45441c002550f1007840c031100700c81c1d9a842d092020340002c41030040c2c1c421007501e410115800c0103441103800e82e04d4441d01a85040080442e801c00612004010302c2c801c6039000500d418611540b900700a40780c2c0c0c01a02c86100c0040b10444000501482c01200c0b480303542c1169a0000c16071205003006038480028065036030302c9401515003607a607580c1e545503d0059098a00601840c00f46a050185c800c000420710102e03181c002c1d0070803030041d4011803400c031035072451140c43d08280000d26008008044085014101d07105040349030713441c58100d041c2c802007a41d08448920b854548003a0031100952501c4440d0000342007400101b2241d40641c00807840c5510810001c540141040b04052030708208940c000c110b00c0d4411810085800c510f081c2c00740085480c1c0083d0701c2c104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 337948534 1250 337947284 337947287
    0x403020601140102030d060e010f1a0415030e120a0e03030301030507050d170a0903020109350f010f33051504050909010e1b09040f0804031203050a1a01 67
    0x2441403103001c80c0040b48110328a4182e209000f10384000342c1c4c40504200103500c5807034480e4041001d001c2c11845441c0c0340c20103d0041c4104c2e00000401100346a09403415051800510305a125408148241a00c03120180a021024001c00b07040d4010f80c8500c0380c03542c04250000b08050740c0000c0d0307580070340c10400040c0b0101e5008540401030300c0e010349031a12501c0041c030700218598280610080a01030101e82d140f00660311003580011079000f40d032696180c83c2ca649a1500400003031a07030808440c126480f90f405820340040c500350184001d402d80c0e64817440000c5107820340d99581e6a2500031962070001c00d528000320824a540b2030b010f11264140084900e1494000c80014003455218a07119000001188921421134001d031601401480c0c09081402c0c1550185c0009900c00505000c0c0c0841e52202603040d94045440d00d900804080c5c00b51525100d403908046e5082c0160b41d952810040400071502d8402034031001340c101e540019180c903119440c181101c511018040652030003040343d90081c1e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 337949640 1106 337948534 337948543
    0x501020601090203011d0601030b030a06141005210703062307020c01020a0212190f110904111207030212010905070504050105151602060d06031109040302 68
    0x1a42c8401c80382c01680400d0140f140900001a0345000c00c0340c64400c6250803810604000902e0181d040100e4140740641c1c00640d011502c0300300021303000702e8041d40e850f40040da0100c0d1640007418800002c90400c402c0d4688000c001405200c480741d80303814000d00008651080d010071403c031081002469070940a507003040308005410006180d1345c0042464006d6481c142e0141c0713030030400d603400c03c03040402d54800c444c041c0c03180c000170364040c8500c1001c0c064118010a902c44202c205807814078148400640b80c0c43c0280403003c280000140d071030405410030003044808410541c0b02d080d541346407442c550301c041e5020010a000b69403500040d0b114800c0b090051055034102c6444006002c20b5407000e00ca0f6035000360060707404485030104c460161080d03402200003140d41c10100c1e0001082e41e084050030302c28690f5991820801c1108522000c46140c10545840c1a18075054030065101c = true := by decide +kernel

theorem cover : BRFrame.Cov 337769784 337949640 := by
  have h0 := BRFrame.cov_init 337769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 337769784 ≤ n) (h2 : n < 337949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
