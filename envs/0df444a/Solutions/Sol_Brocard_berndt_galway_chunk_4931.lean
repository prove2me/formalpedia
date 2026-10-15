-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4931
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:11:54.283164+00:00
-- url     : https://prove2.me/submissions/9ac120de-f97a-4842-959b-cbcc7de6c5a6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 886690647 ≤ n < 886870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 886691897 1250 886690647 886690667
    0x308030c040f030807050c0316061209051b03070510050306190305071517060919060e04060222180f09120305160903080406050a0908120307030501060e0906040b01 72
    0x300142c200307903590401c01900d4004501c182c0d903074010402e98801c20324000032400c2e4001c0d185402d0740a41490001e0969006003400d410480741c0d0740b280000400103005200d409960100921240350301420181458904000d82d004940920b00382a0300c031003000d40000503290310007422641d010000d6400c0c6c10101a0449a50000705580b065000120b076a03e40f0b4045c080050740d00d80d640c00b01d10310740d807030ad280c0c1e80703450565903641c0062410f40030070320b900c401c980030741414280301c01c01152141d40c0d00309003a403140d011601907810030360111310814a0f03001039140342c00748140c080c100e003412820a00c6922001241005a40350150781d50105c031803108042d08401c00050b000010703c8464001d0325405005000c04562182540383d1500d0201885805800140c054030707001800c080c1020306002c41514140d110640200c01d00040e002d00049402003040080c2142c0303d202e10726500c0382031400018094902c180c001c0702c00d110b04d14545603010b8031a180500d50140040301c01203109101400165546280 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 886693147 1250 886691897 886691909
    0x50609061e0c030f04150510030b060904150203270f0105101a180402072004091709011e120b06042103090504110408060a09050d0c0c15120c05040f0308030c04 70
    0x100300c104035851000b2235880007180d000d916108919601c20040004400007114002e009a154078611110700c40b150380510317407142c10745400c210207601800c07503816000c1c40442090320702d501807245400603030001c2c000c09400008101e40700d0076036418900200d00d45001c44490518102000c01e1101c01c0d0704250008541d0300c900a4821541c80f100c504040c0039031102d40719080387c00f440450360408035081c140f040c07100240d0802d003020300508910026008643c0b04603080c80c10054850302800100340c5042d161800700c203054692107454000194020156102c4984440c80344d0824042000302d13a2030030500610010103038140c1c004200040c6002e0350061010b4200d140c01610317002000c54030500038001403084d502d841c0210340c2166039401c528130a851480c40d00400c180c20001000109a008900792101c541c4201105482280c40740414070706860384100d0304c4000380940c0302132400180a1702c61640c00500a00d041840c1900b05400c0038a003c1c1184001418580008005004028002c040d9401742007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 886694397 1250 886693147 886693151
    0x216210c1a190201092409060e0c490b090a060c02060601090b211306140403090315060803030a0207140715050a03020903100b19050907030216050609061e0c030f0415 73
    0xd4511a6a00ea600c00c1d0054056680108903490b4800c09110040c2402c0156980c50369698074000c1e1401d018bc5240340010100f491015840c00040da40d524a51107075254000604c07032403000303061160035503800c1c007581015500038170309215250f40e20a81010940c1c01c458501681c40170700c618800d40300c0b40e00440241070a4401c2c0c050100c807042c0341061100841c090f0100b4854144000382c2c220504c10142c40007404074407100c60801c00210a8540120040910a0001282550340b501d1742d00315403003199031142c180d900044102c01c1003840d0b000c0780403090500d4010910b00c5d0800c10611002044800102e00380540400c500c190144aa01162074640014080d1070f61480d18082c0c4101a01f40a42603d21070624180c004107009900d4078000304032003004121840c0c85c0c4074401e05900a5101e0712500d00030180c44480240461030410106000d216500000c020f14a400050455403000302040352880f9801c040c04c0c000c17098040070949410003070265040840341c0b5540b8010a88147d9000a00200b0b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 886695647 1250 886694397 886694411
    0x30e06160b160f050414120a0f0308011d1905091f0e0601060c080706090218150a0614040e100509090606010216210c1a19020109240906 60
    0x821650b641005000592683c8140012400c0f0684032401036016a880300c080b4504104801c1c80d0900010310351904050035a10981d4040d200c4c421000b000c108140c020070048001040b00d202c07410303c00003a04454085c0d00303101d400c10b840c1c8a400c03a10b500c2c50244080d0384030008140c9046051011300179549464030580c4082008041406c09000041103650b071034000d400000600d103029400c2c04a220380e0111481c0d20b40340496444100800d070302e440c142d0704204101488039260741c25000d40c900480807804031005607004a01004030b0000c030350300400204002120074020950446040d01c0981d01500f52806d4241e54014601c034252400e503020a40c003c40000c14400590404100a030186d0420f909a54500c50001c91440340c6c00c2c11842001c441000909101d194250a9082da6207820310502071028a195111f6001c3c0c0180c5245902c1055400d001480a454003840012051030340014002400030418075180c00007a01000001008444886d000003040003050740d2280c04001c4e4011030400c640 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 886696897 1250 886695647 886695661
    0x705010b09060301050f070f0207050d11040c0e01050f030c0c010c050d140402010f0e010311041707090b0913150212040b0a15050d020a210201081003030e06160b 71
    0x1034440900481c1c010350715400071484074101802080c2c410400f040b1a0407540c0c9881e44206d6001901007540001c42c0945007000c600c50740c3d01090292032500440f40d25089905060400040303400d00c250300c500380070500e8440701c440c0e6088000c0e61104220b0000854480d07540703000c984080d00c42e4420401d841d51808003e9086517820002421003141440700400040103c5544ca04d01a8819500640400e02c130441a4030100d02c100c00304508c030b02061401007021510035600800b00e0300150401145003141e41d110440c41e8404005c40d500030050284180320030301d001004034880540140a0452050b00070410030300380222441c001c8182c80420108542e40c0801c0c50144001d0101030703178101c0d003a180c00713000f00d40281d600e17015080102409580016a107803a1a0800030403840d003900803600a10424000111b07100b0b4106980d5401c060603201800c50819440014200080101007146900c01301109101182d4410000c50781410160380d400da651130411141010f00340b0700d803001030540300381c0010480c2c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 886698147 1250 886696897 886696901
    0x501030c0e0405030d1d0a141605130902010c080301030614010b07030824040f020307260a051024020c0621040614010b07020f060319090206090303070501 68
    0x4990255002051068603100d40040320300c0706a4000e0065407052080101c148160b6018581030145a10580c42900703205840c0ca0620030040030070f030b80710451501c007140c01000c00c0c440800c00c4610000043d03406414100000c0e4020105d49000e51566a180d55820469004540780a011500104215265a540d203006000342c0401b071011031111240200004542c50500180c40240e98507880d50040e40c3c0d21040b42d0403007608864142c0350045030711031401c0c4140d107a6200b50071220550300ac1c0966a8580341c04040e05901190b11840c1041c402c3c11540b98071610070140c05500004060004203507521003010092090079107412070301040182412060042031034001d607028240321902900c001225540421805006116494000c188400c4000034005a083c0c5160b50080c49400c0025403015500b0b0000a41002600220000e45000038030320300f503261403018a44003801c111840d902c0d5103003030361000c540d0b0440091280c0f40117403a081400115601c0c4000e0310702034900a801c4a4643c040d40c00d080380 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 886699397 1250 886698147 886698149
    0xc05030a140c010c0f0b04110607080705010b06040609090f0f0c0806090105120a020d29010f050411040b0c0708060a0b120c0d2004090f060c11061311040504060501 72
    0x6030740c0300d4550001055405200051134158002295a10002594894040001008204459060710f850071244c8603610f80d070161840d20f002c0d0a05945400081c503200e82111444c001541c45032000b80410058150700440716820f0700c41d00350340818100d1340310740c0e114050549611100c041d103050440000c3d98076032041c02c451061004070782d80016a41c0e10000e1200035003a04d0418902078021005034000350511408000c40e01e8400c0d2707298000700c6580940300310311160301e114028811101c000104040c0c2a03050881d0f029007021281001460a1492620203e11943c464146441c40c041542c01e410034062088100501c1008142c4990307142045146004000898030644114be9845844040d0800080d00946101014040700c4500e4103903100d00b0020a11184d01400307041d032041c0c82c000e8988580c003a96400307611400c8014403a03802031a10009071980250720b07204018600750701d6140341400050498024040c40d0300e0298075081800c108a8a802070154681c2040c01d003003d110400c03e0350391020b4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 886700647 1250 886699397 886699433
    0x50a090f0b1210080d031a0d0c0f0b03150427110301061e09110c01020703020618030c0a08031b0f0915180625030e010f170406090c05030a 61
    0x182c02e9079649602240b41c50b06038002d512040c0e202090151000d07029501040c007044910170350b0302c07080d5200342c0021041000008211034100e42d001c0f0800607891882e400102500034a01c102d13055142c25056031144d15403800c101e44c4115101c3c003038008095550340c50b030a411210b80420700e544007a103007800c05110720703c1403c95010350310748000023892240390030710b0312090700e41600800306442c41d0165000241c164000c541807040008c02c0000d00c802001d100410005200703030054003a901e441201d800c4e00001c000507045064000704402c0b0200b4201243c441d140705d030300000b62070303e03078030303451001c5c048407811089900240c84001804066002c0d0100508040d680c100c401d0380c1d18401d0b4125054090003200784481e412104c00381d03590024545000035107200d030748d2204241c1c42404490807617103a8054812055011a06400c106101541c2c00007407440541c3c010f0505400000c1007103000044150011300103044070386d640c0d102c1c6080003061240b210042800070200c0d0191015400c18076000e180b180002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 886701897 1250 886700647 886700677
    0x10c0b092503050a110a0b0c0f07060908060a05091c0e030705010906080c030603010f050a0f1401050102030a110f061008070614031332010f0203130201050a090f0b 72
    0x4140200005200441034a0f400009070903444441d03902c240e074600880e010540d01c8210000c0100301e4000c1500508071520702c007002049031402c901300c0b082c1002c03c5500080c082091044040c8031110700000c2082e00440c0d4480e0009543c0c1d02d581c0d25506044010307103500a0141c1400b60303d2004c0340c0c80b843d000402081201983c40007035031440151090386580c45903d012522410005042540c60310195512940260010035102140c0240074110b40d42104c0010390581c3d6100014802581840b9110300c80c62030540b80543d9504010010755a8064410721104118840b42c0c03e18201c18240900d290809562048072101d08000b010081da1200b00c0c003030340e101c41c400d40100080080c03284079204040d104042d200341c81d6868510124441800c3d0a600382c81c1c454182d0740302ca00200c000c91207226005640c1d26403940701205600c25900351805490b1442905005105000b2001504100484400d50900700155a0300403501c1c240d4012507070340e120641d42c00c1ba2540c0002c40300500e00007405480140424 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 886703147 1250 886701897 886701943
    0x1209091003060f0b1305041109040813060801091503020102030f072f1302040f0e1e07030e0c0d0506061c0804121109070c1212060b040e09031611010c0b09 68
    0x504000c031001280c2c0030b086102c41d4402410541800038015420ac2c2c060341c066460598200a45200104c8592242000a4100004003c140305900c90301c0c46403907036040320b01c0481d403654000035924001e4503140c1c10108400108c1908110481040c100c4e52000c000b16002c4c1280c8400c00004105980b8107070354010382c1c50018540c1182c0c100e00c00c48040e03481c0f0001d902c20035400c10030303000c10319003000b4000e10031036484240c42402e40e070400408901c2500f0b1680c0c0410031a1100500030700340450300300490b004000104520001a0020500d1a03016400350b42980403502224484102524540c1015010401c002400b00b40a001c0300c2d04070000034000d10b0350001c9080b44106120007150200e03607120000340016141da0010300480000ca60444140c60401c0031004031101c0b040450b203a80e8030124043d03200003000c003d04100790000f5035100035081c0146d824000c2003c182d4000d0807402c0c0b03006020381001540d245150380940181103d080d00640c03060341c549404076450f44d0784c038000080f007180b10354460380d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 886704397 1250 886703147 886703179
    0x412051506090f070c140610031103120d02031312030c0306121a060103062112090b1803070f0b0d05060a12081b0604080301171209091003060f0b 64
    0x3024001c08003c60b8403521035440385403c96503800c2d50300040b152907010040015600a0800005005a10b420b1154881c581f940c0b50500503100091316050090b04004030320071602c23001c0320a0300c0706184a280056982c0d034880c084140801c17201c420040c4003080c00f450300c3e0045a4164800302200f18180c5003005019100c1807038450350816500e0040240644403110b182000c8400c0c202c80d00840181404079025440f69a40321000c82d42503120003001c40d00c5c0e40035809220310019403103486102e6080010705103003014409000c0b0300c030300c121450709141c0e620200c0b20359880801145000780809860042500d8441e04020a250300c00200d404a503030501001c2040b0303103002e41c4940c0c00c07158140d03616103076220385907a4918141c110071131210307451945506a01d98450280318003440b6510504130507581c4d6040500429524003d45a122000da02c20003a001c10700b804081204d814120885080580c4e035520300c021840d8120a400003081c9500f0b1240c800b04030b85264000c02070424044a0007601d10400030703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 886705647 1250 886704397 886704409
    0x5011b082202060d09050141130c030b0f04111002060a09050102280915121a150901110102091c03090b13030b06011718030412051506 59
    0x160711044849400071030380010310f007120051900454030b000c0400d8040c02c0d911814211441c0d0718440341e440921a01d40040c080c0d40040c45107407d840c00c1c4168103030729403d010140680d42c0042c144051403034035107052400c0c00021400c200040d40d20591094451900060720000554141e030100c9410341003481802091804119048400a482c0d00801103640c0701e652010191500075001e071070955027007003c10011487c108201e0800041c08072500c0e10301d090060000c00700d041d654003400c00d56004030020704400b030340654484680040c401010030520004640c0340d44451408402982c001040103c903008642500b015015584007600c1e951031a0305000303002401d074410802013550000095117980c480c01c0b1800a030300d85440c003070f18012040d030b41c0b242881c100ba980000030180c000e0700d011108108000d0f82d480c1e5180c0c496420318250701e02148410800c240030038040c00c130010080d40c88045a183e08020025103008144011542a210a4500303000d501c44021111040780540d011002582d5405d2031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 886706897 1250 886705647 886705681
    0x801080307151d07030503040509010f0b040b0f1b0a03030f060501020a060e1c0e03011803020307111c0c030b0a0615080c040302060408060f06010311071e05011b08 72
    0x624501c1d1110840b00c800b0005111580c080701a4803003085803070401c2e6404001c00f4000d0b41c42180156030725420041000782920059006142101c0804030901007086c0b200292011100302000300ca4031140c00c0300c800c8903580204000d24040041110381b251201078002030780001603011f502c040114011303c11070081528803a008444c05a840103803000001801640410b14060818054503400c041211170070400e0008108118001020512442418642031190b44039550422500c170440401a6801a451707005455001c0c01000d0014803070410390711281d007078209009505220034580070591170580d0000ca01ca000c00e441252a01d00080c0c035010f110300ca0602138031541d01c001407000400c0c1c9401c480300c4600520035841a0000d100020041e12110050b0015180391400340c1803900d417070034004031410310050626040605041c020b002d40c024481c100c0380a150020007202000343c1503001e000840c181c2c104028290361a001e8402000440c8580070a4012103a0342d90740c1c00382e11407031000d03004a2a1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 886708147 1250 886706897 886706903
    0xb070305090c0d0c0e0c0403151b0507060603080d0207031112032d07120506151b010902031204080d05040609090f0f0c030b0a060c1109060d210801080307 68
    0x3040c2d509809910308100286003081c442d40c00882156104c1c0108001c429040e80c400d01c686401150610800c181e0790801505101e10500810281c8010744485040d14203c82d400024013000007820300070300c812508180c01a40d00800b4050790340034528200002540004000d90000c2c074120114484c43c0000301e10040c0000c010b01401c2e085480d0081c800c690066401c01d0100c032035021501c2d00d0105e900181c003451003046152140e03400d030045580070005951000f03117050301c01e0040c1040015024201c4d41605e406071841c40e4011074605980c02080d00410040350042d43c90312480000c44041c181d09402441924900300941d50540c0c00c403007040d10140218000e41d004150b4424040c004c01d070701c0e03034403040c0c45412201c00030070001c100802440846000050f40000280c84001800f114104924050001c104074a80280300d4989502c910b0304814465103058498581000485c05a94901d410b04070780b1900f2032041e408007501da00001d2a001f5069070340f00c01103402c2c1d00c00000c107503102006440d80342d50 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 886709397 1250 886708147 886708153
    0x60b03090c040203130506091f0506030a080a03060e0c03100e0c0306190b0c06270c040203042f0906010e062a010f1401080a0507030f022403040b07030509 68
    0xd581d030400c40039400c001c0007500c0c100d805004400c0869003c206207400340c407419001d400212414086000c1c00c0503180000b2590504007401d0142ca524000b0319000000c0e0048500358a0310300740001140a4141030703202161080d0404107010045500c0001580903190701550480e01a594580f0f5004107202224010394080040c4006080c3d401e1a2081050f1081c14108000720702d074840400c60703c1030708282d11144c901d900a000700700b0300790140a0091090320b12881d02a0103462603412055031903c960000b580966000300104041024a200c0c0e40b030700c1d4000380d04401f41c441d11100483c09800a88448901c10042e000202d40790f94019100c1c3c1a41c1580900721a10788141d29018400394100010b80c0032001c02c200c8074001c82c200003880b682d2204816203402003500b031400721201001241c1078000100e107810404440f40020300c00a40c0c00d0480380c2c4490711000c0e90300d00303000144210101030310ba1200e102c0c801190b280c00c0118140218481c611810504007180c6a099044040301c20071110b00c1e4040d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 886710647 1250 886709397 886709413
    0x120a050d05031f06050901121b1202040506041d0703060b0306100c051209040b330f040f08010f140c1606060303030509060702060702030414030f06040b0604060b0309 73
    0x68441d400a6512218141c0010000103014440c0c4500c00c00d954403000010b10301040e000305a40c1d1203481c00320b6401903003000f840300c01d040203805c840042560342d41d40103100f41d02030034503045131007601605c0040a00502507501c403581c44a8045107520040e0034000194000c0c000a803140c1d0091040c40c0039a00c202c8110790844d81c80c181030042c0034034402d510f4001e221940c800f40c80020010040e005065440794071a40e00d0b5031603074082c0400d85068424035403041845109200304000300c0e0814020852080d440307000b404407185100c502074401c07034032440076a6400241c040751240f4a4002041103424403030082010100c0307042d400b011100c01c20b0007072449440c0b02011440301607002001c0c1c41760000091032500c5a10903550b5642c111042e0f58812008213842e00204100700d80103021181d80130b1200e001410f01c0b0b00c0d05250081d101d210f1400760761050000580424030075142001005124540d4004030b41035420981400001508119403480c4542d00340f8001207054100345040d80c0c00344e1101c400404a130703 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 886711897 1250 886710647 886710673
    0x100b070201050a0309020306190605030f06060925020a0b07020313090c030b130603022103041e0b0318010e241b13030314090f150f0d0506120a05 64
    0xf64071500c284002c26031a040214056070702480705900640f00c4103241d03400c3e055060030b51010346110b98041486034200c1c0110030110007001c03c0301544403d0840e00d026031590f80c910350f4501d0104040c0a20400000da803a6990364540008107141d00c40d004403070b0a261641c400e1000c99491081b5030148151761540300080101d2080ca400500225031241804a0840c1c28000070540703031944841d10a091b01e441c1c180400550a1914082200305180070b80c000e03000c6c0c12401c1e1aa070f00e226034880c000000311014402d0880d5946414410050490000015605d09140741558605880e5840a0319a9403802d100c900110000154410404c100c00f80403000150344201a01c501200040c05094040204030901400100520042012032403032054980d80f982542402000c24022407094004800208010303040f03030381c4841034020301940446880426142800422110f402005104a42c00300c001c1000f21015031160401842503030180d0b01d140c01041156602940c820031144050b100381c00c0403107040a5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 886713147 1250 886711897 886711907
    0x6080318091026120c030405090705030103230c0d03200304121e2109120804030f02011103270a0b1c0b190302090a0e06070302090a030c0f0509100b070201 68
    0xd140c100700142c902c409010f0f081c1007138982c807449041e07030541c02c00901880036180c008401500050faa1070214115810755031540d40c40003c8251000c00d41000c00c0b000702580400300480c81ca00780014054405800d110b140c003030072140c140700408080d080c0c1c21990210324000001520111003840c5114000c1700c18503154580140301d41044c0c10078011405420801003800c481243c0e168500e031000a0780a4003a0200090420450350400c0c50601c890500c1c00d0080341d60103082e1b8054139001140c070820245144010b076120044000d0b8807605020100780c0a034134a800c00c60b400e4030301c0b040c01324803034102c0c2e21101000524002405001205c82c0c087c0804102048400c035021040110b04000152200c0304a001420b1120f20019100d08038890b58404c0c0b086041a0034030582004184800b4032007142c030f60000c03d441d03090041880080660200e140c0526985048001c80115013004103c240c00340c8904000009443e035020b900c0c0101100408201501801c40c80402142c40d090a2581461401d40c011a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 886714397 1250 886713147 886713209
    0xa05070203011d07060809071508090a0b04110f040b060a030c0225090c11070509130c180b01051603081009020316030e030f0d050a060803180910 64
    0x60075650301c0044510010882d5807030720300100f0410062001070b1409100a01c41c0c10020903518403a001800200302a0440c9440c60704006035034101a01156038002e01c8030701e451007001c00601803411500900040c84140128514510740541c0c0c0a5040c481c0b460601042e81c0020403010b07080441082a00c40491095108050f0fa0388244140d032a042e4114860f0104a0441e0883c2d03136140380f00c800300300080d4100b4421021050701303c0c20b00c0341002d00e07502e0400740c84440e503102d0280100500700000d01d07075070381c0041070b42810307135229171200a40c54484d83d1513045d4440d0000c1000a041c60400480ca9640c010b0301070311005c10240c007042c0c80840c0f003540c0869201c1e80c05002c0901e44c641d03980e0081756080860018502c00e008141844440c0090440010181d0320021940c81a5030401c11004041044060441d561150301030b002007100d807a4114901c005042d0766100440d18003000c2aa10102181f01c028041d086800303d8007aa519141c1e06003132030001096100b4446010160901c2903074218021074030340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 886715647 1250 886714397 886714399
    0xb090105090f030f0a0624060804140c121b0a05030304060c02030c0409030e090a2702150f0a03060801180f11091e010806090c0d05010b040f050603060f0c0a050702 72
    0x4c0d00307020454010500d800340c12001252126291401107210320b40403003100d8401c10701410b040410070329101d405050004060005411f00c2c2c01e00d5400d01507480700f00b11208001401a007822404001c0d0102641c5484100c03039661000144403420010528064180102b0ba44004018600e02840c000081d2100d0324001000c03601030140c00d000520680d00da2040c154098001c0d120071410010174810880707484002002c1096403807410080c01040700c801006801151644004007070a10010300014403900c1e03072127520306a4100001901003c0841c018003800c013440d1980c60a108094480031914203941c445003000c5041101c1d90745510103e01c81d840100710b624000c0d0f040038140e01807031000c551000d50840b00da8003040c216016071010110b8401d034481c014181030f00940080d00304103401c1c1e81c66054065400d84980d501c502c1c860309004082d4003a801c7c0c480004d0040021020b403085400140904664141c40b0340101400500b8000c00d00b09000d02c206518071400c1c0c03602d5003d1200b500c0e581c206100903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 886716897 1250 886715647 886715653
    0x30906030916140117041e0510050a0e06070905090708070e150405031002070c03020d0219060201090c1d01180e250f030b0a23100f0b090105090f03 65
    0xa158414029050080604002c050140c3c901c5031520000d0442070b0f02065280254481c0300c200030104514003207440c0160302e1044210103491f1039080c400c2c5080e00c20307210042040d160000b03000c54106182d00403407810002c1d00542d01181d40d003860030341d0302036803e00c03541d40c02c1404007001800d06403044110507481b41e0f19042184036081001c021800140b210603800d180180001428400313481e00f0002c0c1c00072018110029494195240e8034032184005500c030080c0201c1c0301100074011540c0e0700404903c3c008060500308031050b0703605c03402070290151802c16100000191030114490501c0441108500700380d500410f43d036482d140c0c0080c00e00c0160755100300e83c0daa0741c2c072a803001c24106011089641c50000410700c0317801210072000200200d41c2c1d006440c2038400034020000103400f2016184d12800811001501c003000000a40300130744020743c001004900c031801c00c040d041030b2510042c2550004244285003a0312b4030600c00b0300d4451322400d50b02040f000c1c085581c1d01d140c036554100c0b000c5805015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 886718147 1250 886716897 886716913
    0x80604080730170604020c07140f1009060f0c03021504021306030309090b0f0a09090309050a060807300b031908030a1407080a0f06030b0702070602120702030309060309 74
    0x1200344502c225000e207500207103003481c03808100c03118182d445403c08012902185410040881c059644055100302a0300e2003000001c11103540e50284111000d00010345041204a0441402410a4030901900b00898442825041010311543ca03150741240d268006201e01d1000b46c03002c07a403100c001041241c4c00b020b60300354900100039030701410780154883d444611410703040044110a03070b001c2640e11070040c170b505a030034002c9694054100c0200c1d56400c10000f0303004910308045812400320740105405c2261140005000f540c00740115115070055540c20050514110019180d80d02d44201c00844880e10080c016080c012a409410080d41c02811180c09081c240d0103462126440030341914041e10100c1001f4540d10b00e401801205c030326101e102d010603d02413201400c092005400d509101e0f55801060495081c25441030000e9900102e40c055103240045c3d00960f1101103000303400c010f004031041114901100000d0b203980560040166090043c49424000503400088c241101032240441e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 886719397 1250 886718147 886718213
    0x12090708010c05040501080901111c0b0402040315050906070e01120e07120312050f040f0f150e0c0102011104052202040603020d0605012f0705090a0509070806040807 73
    0x4640b94691042d61a099229403034280054001c6000070b00c084041c0c0d041100210b50061017100305d8410160300c070080c290300880c0201c810018081c83d64104c0d00188006030100600030790402c09200e43c262800c051095030b940402c4039880d003005490714000304440d5109030300c143d800303414041d4050091038400544400e0340680c01d494403099901000d0740c2c00f2110240400d1651084040e9006d03250484280090b0074a000d8100d403100e4010300c003800420036482200104048141e0b81c620b03054120302c0c4210942c50028405004100500c0455110711031880008142d5006001d000400d243c044086420580707807609201075010082030b80c09642040c0c1c5114883d01a4131720140c4041d082d10350300141c5844a030b42041007201d80030380245051000c649819164840e2a45034201400c2c0d070b0141c940100c2a10484003450681c02d42c000b01d0b0301214800c03c02c04004220742c0040c3c8646170360421180030350303522000039032611425640641455010003003000403c850060088070021130f2541d003205d44013403003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 886720647 1250 886719397 886719401
    0x1170115030f140312070f140a02010617012903150906010306050c0f0304061a040606210509060f1b03160905010e0609090408070204110304050d141209070801 70
    0x18004507042d003000403030358040c03100641580b071145651000845c40d107000c000c01041c00d2030004080074104405824210303081c40c41041318201e680b030202c0b242516070140000180c080d1405004048501004191107642c5481c14011000300c0301403403010060f0030140c50802814401c080f100e16070140304620025600141051030a0300c9425024040c140e40d50442c40c003541550009412a00e00e140c2c1840000c0c0722051810840e030308103078072076000628103e1502c044207054cd110302c8020381c86440c04400185050704885509140c4c084154020a40c4030400c460800316881542c0d07001d80c03a8442000684e600f0104e504581d00320302852a092014242412008050350040b035804915200f001c04491045420111500140070242007660382d0000f100041145801032003070652150304888081020310001b9030407203500701c0d005001840306071420702014840741e00595085a0b948101c200742c0c0700c0244603480f032420702d00c0103103200d520b0720301c0b000d1801c040150083d1054045014110700082c2c045424 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 886721897 1250 886720647 886720649
    0xa0f05031003020d03170c0a09142806020c0306010b0412150524030f0d030207030e030a03020304060215040b040209090f160501090b040803250c090b090a090b01170115 74
    0xe583c030b03454540c4074154084086c07207001e042c800000c0307014800c180c18260007080e035200f61400d0040f05801c0b150200001102d51a0700440d0125140b00e00724021f02080f412103181c4280c03a899004c690201c4034410500d40e482d1024401d21214079801e01c0248001c0d105c1003040ca10650180202c1b00780d4034284114041220300985000403100c43c54685014560f0102603107001145048014158449044010340c0c4c50303c1c5031005090405a002941c1420180240c60034000881d000d000c88031688140d01c1d0107981c0b83c0c070034022a0007501c200b1400b182e800e0b104110f007030b100f66030007158007640e62566130900811080181000000e4000c5a8003041e00c240d0411688000344a01c940c01c0407258030303060024000c0711141c1c01041000744200310510030078a00004461040c950704009203446410414444604185407078000d12503604e14100040c03880f1140c00001c0004812a00001d4940340d80e000d05049a005d4040102a003501c1d0b0010811b00440b101214140090340380003040903988034540001d84001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 886723147 1250 886721897 886721903
    0x41a070c03050f0307020f10170a0f060311011107060c3903020f030109051c0e03060f1510020d080c090d06050a0e030c071a190e030f030a0f05031003020d 68
    0x2040d503d040d413511006032108060b0a455244007413003d50401421109d00100240c00d401e2103002140c2a40003a5104408055400d40100083c51300c0b45400340c21004c48400642c0050782c035007440b000054021a0440c02c031a255103c8c3c0303088800c1950f900c0d40c1c90300a8090030b000d0f11034020140741040101c074a02411000708000009001e4218410003020000c1544140d009a140000341400600000750499200582c140003100cae44010000484249000c00c05054250254609000d400f04581980d14015400c845001c9d05e010001c1d002d10001e0841c8c1880d040050f481110700100b0240a0001280c102240e00a16454000003101142c00007a40c640704465103640e81c4d0820050346000c0c441d10403a80182c002561030003e59100d002d540e503215014960311464440102441c0c20f44810442d031002e034039101c007010000364208000c1c09441da00c8240c1070190059804401c0c402d200030085413101641904c603080c07245804a81207c590700010012015144010750100150f81d07106071041800788 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 886724397 1250 886723147 886723153
    0x160c0c08030d0e030a020a1719080f01050d02010509090a0e070f060210150510020307150509010c0903051c0306050d0b1014090c070f020d03030e0d05041a070c03050f 73
    0xe1100e640c1802c0b41d410380d1083c1120f401c180543c03a2120b9012444034542c0d0b400508081c1e8040506030380b03e0315403140503090154200d001c4c480700481600041524810a06600f100f4410380c2e0707460a0044010380140000c0c0000c00801840c01c0270b01d0311945140c3c000c8900b80c0f000031a0741c0c1080480e4500002600b0070b0002c0101c04000708803169041040b040070b1f07400c110081c44020500c0921680f2b60006004891041c050000030a102a1003001070362084d0760003418003a40c00408405031402090305031106810355003011209000340b4010780083c42103a500c038004050500724440750304880400b00414100701502d81c0c500044070350f11030020400b16406029292060700345104150070b421000d1380f2280040c912411a04499134071101d2641d488648112035070390751003952a054a40700802c0c0c200a500a5500054800b4076a1691001201d074503030104580c07480001d5403080c2d0700d9004a115594100607a0003414503a1000e00f0041e0880610500c0d101c4210794899403200d0400e4601041246994 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 886725647 1250 886724397 886724407
    0x711240405031920030c1902060f04030b04020a061d0118051503160c0c0b03060a1e14011d101b0602090901050418030c110d060209040b03070e160c0c0803 68
    0x151544c10381c12001650035008615200035000c405484401c001e03810402c10311101c55440540d2101001c81d030010484c1001e55a0f10b0751240740002000d1002c0c0c400780d002d111845070114115009010a4402441d0940d030b01c0d44501c2d1000046818441d6840620300039583c000340050161203815641200120341a281901da107000e250910320029440c1308842006502550300010480ea02340302c0d425103e606425036502d64aa1021551091a0758800c0950554044410f282a42d07502002015264070300c24207510640d5950044540703000c800344070b904007030303041c2c030110110700c1c02d0042c0e5400441d45040c009580413001744c80780205e06a604d001d680980d0001840305440c079280451502511f000c4804200d090110a40240741c044560001000d1040700090203042c8180003203040900709004042c11b1034401a481c0140c007035042002094091400c00070b54840c94a000b09000059130724440000030742d5a036030881c0b8061801c00000b204280300c081d203056004204c86130500c0b000340400100540d542e0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 886726897 1250 886725647 886725677
    0x904050c0a0e0411010804080301090507031d0c1302030c25020405090601240c030f0e060c0a0605060904080702100309050114090d080106121e09050607112404050319 73
    0x841c1e2004124104031b441c404010000c1e8165069905513040ea00000880340c0d00c580017035000b8441500d940e12049554500e00c0f0000c04000b8469290300c00c10b6408800041b65544510709038081518030212140080c4114100780c00301c02c200c40d841d041c1000300058600036540104007155400c0c0c1e45144a500000018000405900c4109013503815100501131a0002c2c0400200110401140207007000700e02c02c0c08056003403081d0846062000c0051010303a807080fa881e00107a43d805e5609040340c1580c102000680245040100320784a140c120410524010061b0300704150f11b41c004800f40149641e40c5040d801241c1c00f442048203107032080c10202141e05090300e42c54074040c4000c100700d0401c40c5890040c8203140e408a4005643d116860012901200641c40070f0158804442c1e0840e01074941b005001c10b115000900710300451403038440c585190782002c040c030f0300d0308000704107600c10b00d03909142d0144503c1410400d5901c280190140c038240060301103506554400c25030024000307481c2c90407110300c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 886728147 1250 886726897 886726913
    0x6030605041e0b06040207030e0310060810020f040b030c04090e01020a0311130e10080f010203150a121506030203060a1e06062102040308191d030604020904050c0a0e04 74
    0x20021501410382410122a40c407034100a0001301a140a56004244030003018000c2c0e0054081c9803008044d00c8001d00c150228000411962092803264441c0c035484050082691007183e200840300c060325480c00e8248102c0d041150300107000c405940a081000280e007410034840c804030307038802d0000076a5500d010075008003580c8904170b001703401441c2000343e0705040321400da018044030103290781f0f41260340d54504142490302c2e041c1d11505060103420894094080190300440c80780706518801b19248a044003841880c445c02d000f8504c030741801d03612000100d00340100200c110130040070301080041d04c03a80841d091010503206404903a450380300e1406900d424841c4001001c0b0b0380c1804120300741c500900100001c0300700a00071102154420141e103994440d804403005107400100a0b51f4510840480144a03000d1301c3d0b0000020b8005c0652650031009011402c03516000200107100b25101d0781c00b04608200086d104640714415049098410740350050038034000c050802c4015220b1a0500304403075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 886729397 1250 886728147 886728173
    0x30c0d0302030c0d0e07090905030919050a03320f0705150906030604090f0317010801231e07030614060301050a060f02030d061202030f280c05040603060504 69
    0x500d801803007000843c460002c1a66003401007a403000c540c1c6104e8a0185d410100b154110001c0103080001a809029000005000200042c1c800d08100303800314040a0700e6907a48d0140643c0a41842d00c10004980710382c0d20103a2402e022282984051100b590400000d2641c04615026030400d803181d0a04038020700510000708400d541c4a400c5c0d85454402810b6441522445880303050044049a2140c4950b0b07c0140442c0e480400343c1d441c140d0078180a1b000040f15600828200180c0f030000ca8030380418041d43c855140c01004c441503141a01030201d44a038002402001d004d0204904110314800e641c11341d9008200e59240061005d0401254a40e0090415031301405510704100411480e241c2c20914801c035961840c0001c50400c0642e0128214410303d45802c88190414001141401d0b00605440d04544210220380480d0300e0799402e039481340302100c507881404075202540c543d0459175904000d02a4031907003040351815160b40c001800ca8505800584000d43d89404100401c45500f200c82 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 886730647 1250 886729397 886729423
    0x2011e14100308040501120906060905090708150f0c12010e01060f020f07060503190504210f0c03050a030e1902010e0303030f010b1b01020307030c03180503041a0c0a05030c 76
    0x103a820b0854840015910a500c10a81004145034441c039440c019a4032184e01690b001405001d060b51701c2c411040540026103c0d1051809042400501903000180c0011100d00a1071400110f0b5070b41120401c9001c401000405d90305410025103280c60148078065028181d11100b081c51035040100023004101c01c0c00e0030380d0a41d4814440d0300250310300002c1210440b031480ca4016034030b07562a106456104801d9100901640c10f0509103c10403410111504800722000c540d44a00301a10b03408031000852141c8036400325402d991000f001c0383c803590085c400041c0b01c0c1400f25031004034515192500f41080c2240090a04c41c0d1220b9007103681c010300c82030304108200c00660640c102030b4080542401c040c4103c5840401c00034110700252089100c08540502381d1008546034681200c01801a0401641c01400a8030700241690410310081c034030060160010b00550401e81010000c01e0b400c1c102402505902c00c05100d0300c420101c04101500202c3d10400140da101d404c068822860300b60052810 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 886731897 1250 886730647 886730671
    0xf0d0504052107110a080a05100c0c20013e01020406121802040f09030810080c040b1c0f03120c0815010c0206040b040e16021203040302011e14 63
    0x2040080b09400585801907008820f060080c9100400a1080d0030282c0c811455400350310000014043c01140045401d4403a000a001d44200480102c41102c4e10000007080300c10581e19042e04444410030070f00013918181800104200d294000038030350380e50791400c00f4945207000185020100103100007141502100029402c2504012024100c20f09080705644040d1f42d840c4000e200d290740300c20415001790003330420041112501d0301e070701c0503101084050b0081641034011404050803080130004407100031020307186803c0d405040001a12540a1569000080c84100c560000d04c030520345041d28854003a0400d1100030f07241c05030458881041119819103400380d0702075256004066070f0342c0214a8040d005039907000c980182c84281019134080e40041020801159001c0003000034010b54003075140c440344680d02e1040b4480c0200c03135821400c00581001c0b4000030004c88503000345821500c00e000100b00410300c12100303d0f208820042c0611010380718124150201c001c40c0c08960465609a01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 886733147 1250 886731897 886731943
    0x201141f05040c05071e081908150303031311060c011b0e01091716090509120304020a0303140408060f0406140402010915051b0a0605010510091503020f0d050405 71
    0x4041c000d409140d501500f00c2074210074000b5122004030300d410340c1c4c07071f40065480d0300c1d00300b41c5040701c10240d400107c42001c2038030760010840200181040c080455402002540b035540c41407150041d0300c05409045036203c103503c40e44e0020307586200203022010100c10000815100c1e407004504d000c008401038134144003800c0d00600e02079074072032292000da40e0f840c8012102e0034030440c1e030a40b43c0102c1c5140344a55002201011a02080c2500b180d0b004000810495521003070f47d405540700751005a500950091901104100080c01030001680411060b0340c220b042a0f07680410714201541116001207140882c4100010407606104071130410524450822092920340e0010303100d40802c3c0511650440d505007010480c602c074504a4111a4000103661078190130300e400a5625540410110b441908020000c14203052481074807006034161303074401e082c0074035000c400c01c049680400244101a0200300c8902d0225020005282411030f4880c001444c2c0380900303100707081c040f4482c1d03544060085800c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 886734397 1250 886733147 886733171
    0x303180f01090b09060906090612013209040f0b0406090213050606070b06040e0a0c1502060601050d0f06050d03050705010e0309030c040b04140c07060606080c0a030207030201141f0504 81
    0x3511811300055030303c1e0740d07540d16100010b01603010300c04100c2da00c1407000032151802c80100c11101d040700c490082d801e00d50385603900304a0510392002c00204c5180f4501d0180f03055450080c0245070818014080c811500810b611342c02194403045400b0344071703142c41c0c001110450614000c0101382ca50340850421542c00e000d00010403a1080040280c050200700c004075006550b194018410019000f040301ca4151852810740014491440b0b918030103414004114041030000c6012445820169a450b10b0050440300840040109000d448403a59560001190f1a02d0342850150410b000e074a850f03440c0c0b801d5103015402c3d2a01c01c007072810701360018412080280c600103034070000744100b200d000c94001401c1c80031030011f090140a540e9203900e10410300c108404010000c01c0241c0c007541d0b0502046403944c00585013102c00361003102c1840010084101214403d6015009151017440003107140480101e04034511801918030b0050810a0400155200000052308005040980c1c081c48071940d81c00c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 886735647 1250 886734397 886734419
    0x4081614011704031814030f010204120b09120f1803120d110c060103030e030f01090c050d051606020c240306091308130e09161a090303180f0109 64
    0x501080c010320240100d0f080600a40300d502c11803a25003143c0d000a981c404044200004200e03220b80240103003c000c00702d400c0d0600032141135850702e16641c09030389825928a84a11401003000c20390740070300e10030303400b500c00800c00070040440800f504035203c4000d01c5198255144070505a4401d034003204607000d003040000306a4107504161100028182c1c02d01408400b50312540c031862520f03009036030001c0100354101101034600101603040300d4110340c4034524503080b504015400b502c0c4031040340c1d0030407940c9050402c43c410f2600c9030003500c40075524520011231500d03081c0c022001580007866150500c3c2031070340180c00d1801c2560100c000c20614200b50010902c0060407060040c0880800103c0342ca02000c03010321071581c021059952141c1c40c201416011205020785180350b01c828020900d80240002c4000c0d640d4540792100080a1904400800441c07046149100c424400c3c002c80446550610290145804240c403020b80d5180310800c209420021007080e80c14454615402d1100031420 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 886736897 1250 886735647 886735667
    0x240504050c0f12010f020d050f0106121805060f4002010c08030703090204050c0901050d09110604170106080d0215040606050a14030708030a050702090c0f0408161401 73
    0xa9516245444090000c03600c20a14000143c00e1582400c2c2d1144541c45294028004003445400410503030711690b0840c08040002c0c8138800006407070002103031051609600c030b03d010135081030b40d5400e14002940c0e0f00c1e040400c105c031f41c200b82c01c1c540030030000c0b802011034010400d001030510350000a207500000161304101c408040101051400f062030459000780881c07040700d50003000d80790b202d00d00090000c01404071140201d004608207000700d128100118190b40c10144140c40c1c2509001d5034004140061441310819500d24a5000c01d00c40c40703885040092010b05a21300c68a10304160102045080d911150300005a542c8041854a21a136000c42e02e1402800403040c80c004a45407411303c40c018000c0b541003c0d038041320004001400740320726001140102020341c16039100d02d0b90381c1045500c0b80918410034020a504000003401440e00b55220b540c082034151200b0308229070740055003010703082900b0507001680810100040b4040d00103030740d001000403400c80c02001d52040c4c0000c10302d0f400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 886738147 1250 886736897 886736899
    0xe06220b0a0f020f130f0302130e0106170c0108090a05030304030c03020c0a090e0607082215020f030601201e0c19050f0603061008070219240504050c 66
    0x8003001041112100342c10001c50b48008441c159241c0181200141a90380000710301a00801e52900014500000703a0794002201e4004001c580c9954040c206100942074003003e81d03095541e20080411400311468000c0c0e00d0404000003012a00308000000d442c01c0d070060200d0b9402da00030b0842d0381c00074030004122070340145e061030580928106858141c0c03610300c1c4404150780c0440a65030114114166501519601c0c00c99411907070a03441e1002d094400c1d90041d50444c00342d40e06104031000203e802070070205042e100c6d02000001c1880b11000e107040743c108801a22050f4000002d100b400d686c050000c5106580400b40c0340a03120a100d03640e50f461508100c89003070406044d92010300d20781e05000f1501d010340c01421013102207204550381141941c0e01c2c05040d11840c0c0b40011036516040203020780703108a2001c0c008050721503070f050b0241c44c5a40014480070461080c07048010740c030144100103060161140460480c04c14007110100841500e80b060308039058604410080462400203401c85083c2c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 886739397 1250 886738147 886738163
    0xc040501030b030715020a1a0603071a070f1b0b04060503060108130f061b03020a140708223014030f0a020f01050604090302100203060d060c030e0622 66
    0x10031038010a00300ba4051380901489a01a24100c05c1d0716000300305101c54078810402c0da042d1301000d00d40784126013825500035401d40d0161a00744087d24414007840403030101d10080c1400d0480a5032403441c240c04110b000c60b185030b00d08001545046c07621046802401e8060804d0303042504002d0002c01c0381c000109290304110150001c1030b050400c54000c441c0c0990000010f683c4450941132401c05400380d00c000c49458031410f000408414440e1094940900a59036013900070100da12a08581c0e400400059403d0201040700c41045c4481c0840903054100c000344150420b03203000002e104000e510358080e004032140c00c0f1400c1a2410000d040604a980112202a802c4402600350310b1401501280c01c070500c000600416299000142c000000c101f0714001e000350f80d02c01003400180d402e070880040240c1d000c42450700340c04010b81c01542d84520090614800b6008039100c43d410350304100c0c041c401095448885c8085003100744040b6520041c01c807004040513034150300c130001c0801060b0300542110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 886740647 1250 886739397 886739411
    0x1e120a080411040b0d0812060418081309060f0e0a05040c03020d140d050d050c070f121b12030c18060f03091a01180c090603090602090301050712060e0c04050103 71
    0x42d40b182e202c9404c01c4c20190158001c06510314000030326030b1180f800c80e80a10750180008105103080c1c00b814440040020882c1800d024544c0e80129035000102426415468400b0101d031090303081c0718480003850426560f00034a803814032030300b050700c0010b080003007201c1c14031040101241c04800389104403075040d00c0b009000101814031071460b00d4138064003d10340c0034070040c494039964030034081c00c50355020010410070354445441040191081d070f00010b0a904c0d6441c00e804c003140100c144803542025600f480f40c41940c18014103400000d00c10b6044801a0580082001090f45482021318607030350b6080c0300e945201c1c4041c0c0403c600c0401c1c8911030400207410399000d0914480d820681c02d903030340320114900c460940039817485602001d015074015094640c149013541c41c1203020389249085542c982c02e200034180740c4202e000e08803c04099424070303020456840243c600344221071141c003181d81c0f020301c40c1070710100c1d642c01c0c0c49170383d440391880d91b018405000107429402c0840302144c1090800182c84 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 886741897 1250 886740647 886740649
    0xa020a150c031413090b18060d0b04050a14031206090712051b0c07082b0804020d080c010b030c10020c0f041d0d0212180d06020c1e120a080411 63
    0x144580148a4004c030205100090a55020780050482c19402c68000d0f02941c07410101d0038004030200d4015500c0820a4005004940b220391400d412502034000e40c0c0301c00026445510411420b0301d4038074500d5100090000303100c1000f4180039041102110b064880d41006d54008004682c0080001c544070794501c042a5000f4806001c1401d403108520601d0b04c2d21503001906403101454458070b29140a4041000d4654072008103035035020440144800d1650034050089a002100801c1284c207c070080c008100131a60550160034140410300001c140c030410707181890309109141d060240901041e12550341d26540210750a0b07140ca80c140d4503080040144000079004e071201e80c0395032103180c19054007103400e0300d00418142003200c00c540840d20500203081040d102880745808016500e00c181034117800c1450003652104078503003e03071400341c2010008001c403414a400300040c50100b406450004203048001c0c00006001c2d180080f00be400c080d45c0309405004010300400080c1018401c100708101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 886743147 1250 886741897 886741937
    0x609042f040c030b040c02010902010c06090203010f020d090c0b160605130c0b03040b010e010b0315030a05100e0c040603121b060c030204030201030f06030c051512090a020a150c03 79
    0x40340001841481840442200600180044402d5600035030a1a44000d1a1070050007203498060b8180c0d10700301c002c09280c0301d5000078001c060040313030b0554980c45c11680350300c1c090003d05404c1ca201c02000a00652a26221900c9031140d8441100d08505003c40e4001030350700109240140d41118001c0381e141c1c4d1f424030095001e01103050040840d5004900440c42c4241240038522880c429080d80c2d1071a62130311007000e0040006d10900c0c082400800020b00006070032035610103482005000c03270b200408903030b59081c14855203201e03e105440c0d1311500c040e0178140401580d84008801c0c1c6c0c0c04c10207141141c86410781c00380f01c044541c080c4a5080088042c0911701744284080030b40041003000314500d1004020003a62081c4004e90000341080d10140c11441d141c8100000c80c1c2d8004254a0305600d41400e2010041034a0400300d41c0740c8007842601e060004a1402030301c03d18200000d002d81c40418410030249072515007045942440c40c80191010380d8000400022260f09804c21207295039042d14913140c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 886744397 1250 886743147 886743233
    0x308180a0212070305120405060d0f14040510110304020d02040902060c1501091d0705090a0f1802090709030b07050306040204080f0109060c17130c05090112020108060904 75
    0x500442c10310750850070210302140300710940c0d1040003a2500b806151b60360014a001c0d50241d96407050302008904401c5100b03a10020b6100f02e460310115141d02c2c210261745444108503810750340c0c2c1d00125400d0341e0001c0180b14140c0340400300c0e40020306505150700803540400000d00c000380113641da010308100759991407054451054681080320201001421040c1c6100020b105043c41030b0b050845100e0040c001001000e130007012140100302c1b00b841c1400300000100050005a0b0855481010000949850042c21501c1c41c800c1003100700102140b040c401300c00380040c280020880034600c00c0c0001000b6112b800d42007035491a00b80d88946840d00028020712881d84510b0541c03149111041c0f5040e019005001d420303001c5c3c0810005121542404e9030089078006140101481140020f052074204400341d8543c28003e44034050059181d03004105c80003020b8004104040150030200b08660b484040c0f1a84a4410b940c202914103080c0c3d40d00082051400c150340208025220700703600c05440e640140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 886745647 1250 886744397 886744399
    0x30603030c0f081e220302090703110c0a05060126062d150a050108090d030207050f030c061b07020906060703231c060e0610120c050d0b0109030308180a02 68
    0x2000c404004c1801c4c078010b81c40b81e00078402c2e14802c80c135032401d405d0460980b80b04072500540300703041e01c1d66a95011801000e0281038408021000e10250241501c1080b282150b1880752000340724950510040c0c0145101c0300c2000e040c4880305001c0c2207480c03503010032010b80015a03d0301050980194641480141004200002e0f800d01c0d4403042010600e803480c40039080000641d004108030f1f80711001150700a104445c0940d0981c0605150843e0920a90040c22a5800381c02520140240389800c60706543c005000d6040c0303035100100340324011600310102010272178184245840d01c5810760224401c04402170010780316040114101d4149801028803610600111915203488039200b420100d05810a803030000c1c003030301400480d0603010864071650040d10380030302180b00d07030340d6918007040700c40590140d0380341c02c001300d10211a03881c075864004c256020000c1d85070251150719060f4007078110340c1130600180c1004400001000840e400809044c1c00044200104428100032503402d0b1815154040007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 886746897 1250 886745647 886745677
    0x40b07120e060d0902011b050705101e1e05161709030708030307020c0a08301201091803090e0c040f0b07020901050306090c09270a03030c030603030c0f08 68
    0x1070529030f52240d102c8402c56100b43c0b02c0190240f100340003d134201052400041507a409024140810703e0010b0140303921400c42d107400c40000e06900495140c00c4a54040d1300081141e422101546001d04105154aa00c4d2440c1c500d06044208042101150340c80c10060a900440700c0d0095258520204403200320f00e0180c00c954005a87d24449966075004850000060141d04083c103200c0c43c20700d0032441200c08072001050280b40705a44e100d0040c00140c0c0c40d90310542401c00c0c0100035081c000150681308020710a4055661500e0080b81c103844000369070b4082eaa40550350400066000440c903815038034010310382030341503840c40302c008000d10592300122a204207903030001912004681c01012454800d07151a072969036610189a40c50b80203603414000e41d00441c65000d2175007025980d039070f445810452a112600c060300529044840c0d198a01c10b0150001d1000909254040c00b03034404c00140c034070741000710b14510b03200200802d03170580c4001d04802c0c941607144203008803030042c0d07402e0032602400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 886748147 1250 886746897 886746907
    0xf09110306070c1106160b0105031b1503070302130303020a0c0b07080a08091006090506120a150c020304031e0c060216090e010b04181106040e1801110d020c06060402040b07120e06 79
    0x1d9120f8002403040512034854107000e42d10034100701905d46940440070b00001a4441e0880305a0510b403c010300340d60800d5400c4c060f491101c2c01c0c24500b00012d40c060b4002d00003491a504255020985c15080603a0801080020100061940044521442d21481c05069544070322440906201031401241091403c00300302050625841e0301060090b2022215070207088495013440c2d84454260802400341300c1090700030314014005821100c0d0002407441130317030b24040d04d03943d0310680611402a10600d003d6008645020448400456000340c0030700c1c00245402c0c00c89040c4000c05d505d541c003c6000c1180c071000c114031500d9094001c40300e081c1d4005c10030f01551070401791502500c021494180c030f54480c0221041c42c0360030114120780c180c0340c0081d5100195550441c014980c045600c40901e810741d07848134034410780c0c114403001d04106c000c4001c0140c1c5c2c07080c2040c4a40d15040018000030b200b0351041100b00188002d1000f11500c05502440c032440c40d0700f8110095408505070008241c0010000031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 886749397 1250 886748147 886748153
    0x51009050115031a09041b0b0a050306091509012706060e01270302060c03090a0b1c06120605071404060e040f05060915130f09110306070c110616 64
    0x301e1034040d0260b40801560304d00c0c0303002e110501d1010207221707004a01d81011030042040c07220300e408003203000401c011240750f903101081125440f50880000090002c4240711141c9040d40e201030f040301204d16400c8142407110001a09500706216445021202e21308004d03e00a84c44a003000c440d00f01202048a503a45800207403042e00c0c0005c2d45400034440030b8103002c0f0300a4404503400e10401c4407a60f5180541180c0c240080ba0740000000312441c8428408280380b541c60300000005001900700094550004440c016014810510f100030020300700074051055800b00a5141c0c4a1504880049100d46515105503058824400a5501d4002c0058049907190300034160803d54902901d08101c6080004140e00c00c5900589030207a0120140021554002d04101011541d8000810b640c20f101000c031040011501d51801020816840b4100c0c002400342e000e048210150054004e08054940180010000440700b540200840318881428015444500645604200140b01e0401d6100c0c0d5007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 886750647 1250 886749397 886749419
    0x8150f040507021617150912030c0c030d091509150209040207121716020c1002030c0102120a05070c1a09150f040b150a1206200703021515040510090501 67
    0x3e0802885104040303a000c6d03528040c10006210b000c0c800c0c00b512005c04000c20240e043d44c4003914001c20600244805850a401400100581c0365000c400045d42c60382403802d420482c03403649a18004034501004d039004643d580c0c0310507060007020440160759500c00340000700203000c1d440d4040c05040e0b2005036041c040380c02076603d4030110465880b00c1070030783d600a80c1041e82c43c0d015150310300680040c05030041a0810717180d81554035665005490410702c1050381642260002030030b04010041480600104007524885c454200041e0300d01449040b442d078441e01c0d05010300d0602c801c0315090610000b659a4020700010b60b1122464021441504202c000c269031148240c5042c1c03842c018450101d0007909a546c100d103d400b902504003e05549001c1c44074001c03c0402c03078243c3c2d51a4442c1c1c04851810414619040041920307100e154031050b1074100280380c01c0c000304444400e44890310511401a42d15105100c61400440c4c3c08203540d640c0c200c5803000882d03990301514640741004000700b2000004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 886751897 1250 886750647 886750679
    0xa050915191209020a140d0501020d060609080d0206130602040f122f120708070807030308100f090b0609040516020f030f030130050102070308150f0405070216 70
    0x140c0c0c0c1d400461040403500104031403d481000f0b6118000c03d00801125504400c2601c903204000c155003120802601d595003a89c0c40840c01034600c9550b2101807040e00c0c0c00201000180015030000c107041c50b411140656076003009000c84ca0b034940301e4452101002020340403a4040c082d00e03040340080590b00d03826203200900c421001c07074461504048014082c0b251014034501d501001d14022800744804082c802c095105000b01049030082081c08a1043d0741008808001e2801c0e0340142152842d41c00c00802c0700c14060006845150481d0b01000240c00d040b15482c2a17600c40800008c0401200f000034119110710403070140c2080c103081c00c000d80588100310813070300700701036400303841c0c1011002802e207071244503c2c0c03076640000c40d0600c010f0002040c04c16007000c507070561000d8040000c0c001316000b00003220b4204119000da4000800f102010750080051350005030f508802e542d0702c0c0d458800514020280c941c8240181d540d100010401842004000780c40c004110145080c1921481d20360703040303010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 886753147 1250 886751897 886751947
    0x20d1b0f0905040b2706040f03020d09080601050f0402042706050103060302010c081e1303050c010f0219020312120604110702010c060b130e0d110f030a050915 70
    0x864001811001d0707005252265a001d40c2003803060b079550342c600040d44034540c0404000c14460950700307081310701001441c0c02680135030440c203481d102e00d00c0c0080c54110310040030810081500000c2111510002c1c41505503081100d844116210240105c0c00901a550100329030310492000030f6004450107000604614040380140301d610b44400c01074040d200a44402400240c4840d03840000c81c0071040a0441e00340d0325208146904ca0001d5442e04541003114601080340d0000c1e020402c00404001c100d081e02021708004588404084001c0c0d150000d80d0220300c00311880000c110115982804030100322680d01244545610b07000140c071101000842d03895014600d803d08295050080e40d0542d05020360507900c000282c040d9586000140c01900041c1e5003000d0004800359007200e035070040d90a10081807000303002d448044c05c40140f141e10301c02c949201c640c001c905294071529010046400140391400e105948219000206004810001180c403030410003089162080d8a9200c005828160b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 886754397 1250 886753147 886753169
    0x12a020a080c0d020d1b0303110106090606050f070c051e040b040b241216081f330203041e0503070510030b0a0303020105100803041d04020d1b 63
    0x34440300c00c1503450003484081940103440302070a100600e45035030407101c50f43c4207a40942c04014013006005422441d90401c601140c03200c400271840075000d1059000030401298203024841c039010029040344203074a400150390400141081c18440d4003944040201405818481401584400303440c080c43c26001041c0b040d41005000c4649244c0360081c00f442d6036004000c800120991040724081d07418035004020f00d400c09209880010a40c000014840c0c0002d8100f40042c4200e00030007400140d005204000070284104440a02e44079001124183c0e108800005404d6100d030001d1045114645840c0500303000342c011681e0744607030110280040387d0030940c21418103e0403661010740400c00c0c0c000c1d05e41650090608010340e00c2e00280d560314408803418002458603940002c2501c9820701d800c1070340940e4445042c00303107046d03948aa80c801440c0c42c20285083c581413809618420100740301410b80c10310940c0c0402d00707664503249991480c1e6488001c800700c80d1802080c07010010044e01c40c02d40190 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 886755647 1250 886754397 886754399
    0x2030103030305061c0c05040c050c0f0f1b061b070801050703050f01120f08180607080c070501020604030e041e150503070b160f03110307061407030204063609020717070b01060806012a020a 83
    0x10070052440844048000c03e0036080201e190004070420b401924404013911c15004006480b842c02c0c8107850043d032496074040b545190101203102c804006030302c0200c050300091820030100303e5a403d051804c650192219035a1601c04c0c0302071154404141c0800d91005002946000300107411000700591150402643c2010f60760b0001640c544e00c2c200ca01901040904102d03101d80e1401e98008400c0c81c0c01140b212038281c400311030100c03c80366429221135120703000031000d20141c40d04101d404c0c000c00c01c1e5200f444c075040a00714240c02c4020350101c0140714560300000c00007010f010b112440911a400c4046a440302058144480a016005243c1c0100e8040801241240e4804e008540c1a91002e072161030300f50603007c400d40c0340210900420040c081c4148100050303038a440b00b20200504e049203015031556a02d00388642141003548100c0302071a003c000a000150704c0c10310040c112095801c00600325542c0c20b0041c0c82100c101c0c902c492549080200100d22a00010003061240d4000d54000140c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 886756897 1250 886755647 886755673
    0x21b06090f07030308040609150e0c03070506040f05060906090d0308070320121b0a05091504080a140f0d170f09030306040b01030204030602030103030305061c0c05040c050c0f0f 78
    0xb64031500002d4005241c5200140124415820140c0d07034502c100182e040c3d04414500040850340d03103000003115500a03d1582c00b4a1400704501e03000ba20044401030b1038503282c50003140d151a50f41c80303401d000d820301003140d44541c0c0c1c0e00300c262400280c000d810070594030003c1c500140710502c00c503565000700385004010042080c040542e402013100201e0781e585000c0c5007d440c2820040c00808144903142c0300401b00e000654681d01600c1100c010ba1600d9071a280741908000207201c3d440604104010107200801005c0e50001340c400903203030410000001c20a400905c00c0c28200507802c0340e007683c86012022030240e40d00510702e034400c840d410b1401450391100c01001da51a0410b0f5080040c42d07000b4008502e0310315140e0b0101d000c101050500626281e41c80d501c4038241d0700264000d034040f95540003086500c2c00c20610103007800c4800b45515240c0c0c041540c80768402c1d4018040c003400385944226552099014000f15920700d4458002c85000d5000107044655800c840c241c61702c200c2c01020314a03400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 886758147 1250 886756897 886756903
    0x30f060b0d0902031024171b030f2a01080606040303390210030b030d0e010504030c0806160c08031b07150606030b032826190c02031b04021b06090f 65
    0xd02d0805c7c0140428500c80807010b0500a66600320581c18000c000c00c1e44440303042003000c00e411040c8201e0540301d40710000780401070030740c52803061414071180074200089070740d82c041110281c95150400c0044017054109100082c08580d010b10808103044007805108604444210b14142c4200e91010840310000012025104041d185682680c042800e141495009140081d009003041c9001828245e9a40381c003640000ca0b41e21041098206c50184411011241d000100c0b01a403820403000849541c0d4074146184801080c3c800c08040000d0203c980050400c03c40e100b00750846803e0030152241104c013402000c1c20300c545c0c0042441c0c01003014581c1070101d1030050b1a40540e41c5001c47d04a11018000d0307040c0012421a0b0341c6006801c3d00043c00390101040c1c8100c03240d402c0c0d8607164440c42c00da17aa001041e21004005000507240d840005907800a86014410440610980040318003400300e0042d000e01004021280302d06c0400076082100010401d01c00c1d401e100464840382d0300c070740b080c1761 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 886759397 1250 886758147 886758179
    0x40510080703031101110427020f0f1207021203011e050409050d030b1e150d05040b04120309120507050a020a150e040b180907031a010303030f060b0d0902031024 71
    0x43c0c09081001c00d05d0600c3e5071080000c2c2320182e0039016182c403064181c2c0160035808000702c103d04240115400c1d40c05103400e0f88881d88500140024030310103d0085140c401d50105104d81d0516201181ca904041800401900c004080c043c000740501203403840c115845081002c19407002a00d8050041018035121000e00003141910340300c490415084400e001d00741c020790190b4145800d0421040b01c0140d02c0340f1505110f01d0040d01d83e442c0c0c03400c1c140b0700362205404412440c002c060402003100c002ca1000d8040001a945500f490344d60f407042860054240000d0740d4000c2d6200d08100c00000e0136003000740051009003107590b510300c2c400314800d0802045540602c00c0300d420016464600c4400e5402440c06500715504800700c0e51030607a640d54410640302903480f00354500e80d411303004008143d010f000703039214007260070310620281e03040a50840441c091961110b075042d485800140964505216906080c0300495042c00b141001c8c00354942c001d901e5000d426041d80c01c0000001d50f03500d210880708 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 886760647 1250 886759397 886759409
    0x1709010b03101b18121a0c0714011b08071206032604030c03061e090c05090a020c210708030108060601021c0e042c010c0e1008060405100807030311011104 68
    0x1d01800d00311440a5600d0b40303c03044804800702c11046e80e510400380c078200e200d1030945010554446103498443d000001d8007800d1780c4d140e81045d206c13480320603903c11540c20000652402c181e150361010303800c455030a01d4180c00681186444030101c1809198403000011220b00c07040c0848042c0220300b010043d12032444081c000000c004000c0c00004d189030400b550001c030010641081201e0340100d00304a40b0800d00443d4000590f0748108498100007000f1070340300451541c21814038450404140d2208030700d0f00c24401c104040c9400c60782a03074642d0b05031600c59801410054885d03841d0025160b0382e0505603012130151250083d1080c501e802e498241c50625590703500c40b1400c24496040c00080c01c020703100c09007944005040c084d203e00001e40103900c000d5000c8000305400c1800c5901400042040c050580070740c3d4240c85180600d1b07080009282c00280030b59000800e650f40c41402c1010030400c0d000500c2601030200c001007810b80c80071103c1c3c00d00d04094020008215140fa010300548210700c106 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 886761897 1250 886760647 886760687
    0xf06062c0105150f0f0c070f030510090506062101020d0e1905120304080702120a0c05040203090d0e121f0615211506050c070e04031709010b03101b 65
    0x11500e40c0e0201000f41c007000d001c03640c500d400d001c5000401c2c2d040850a4100c0401c0d01d1723002c14100f003404001c0001c2c18181b42c85000800c0181d002e07440d010b85640b0300a20550180f6201c102044e111030444c05075101c103501407002152211900c20515019100d4500b081c8603d1144081080c2c0071402c0220b64545d541d400802401c42341e850070a20b51150b000148140d8540c5d900340440d101686819900c10b40000e44c03a0040d200341145031810012041594010034061441030080004ca040c0005003101040d409051406040c020600091035840310b410741d6403414015403290038003442e074074550519101c5400300c1c1842a1511410341d04125007049081038000b520300351011000740d0302540c0d000e1a000003818041061070120f0201c4a95801d07691011002540009010710003d02c14402400a8a80020030000c3d5060545005084c2c0b00200c0c1070442c400841804245c3e080b00940c8440003e00014090304d4038a140c142c00d40000f000014000254808056006880c403440344642e82410070000d104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 886763147 1250 886761897 886761907
    0xf091a09070221041221030b030c01200a0c21020a03080c012013060207030206030a050c0c0607020610090b011709030909101401080708040f06062c010515 68
    0x10154a819003040d0071111960100400700e07408510440890940d8000ca0500d50700c090700018020f0031980460086d8100361500003410255580820408190705091800c00c244c1c0004118003940607007101080703400c0344a01003000c42001104003d001c1101c2c0c0c100282101100d0309503002c580781070f699000a5001c040100c051000a91401c0501408100030000092240b1074491450b50540c0401c0181c405400228440f001c11001c020380c04033400040c4042c2c179241d407540c1d01003420750101811010103140c035a0300040138607800300c007030310403041089049641c14200510081d440e5603040d261401061044c800125881001d400f80d00c0c40060103940300c0d511050083c1141071b007000f000c1e04046840c0020007003555159207004c0d0310741c01a2642d005144040c1d15001c0141d41c240c440380b08050610028200304201690403402260b8450b8011800448444440c548240101042c0e00840c00340241c1a81806000417403d01c0202c94991441c05004142d0700c4400700300290210ba03039480408801001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 886764397 1250 886763147 886763173
    0x70509042306090c071716050a0228050411090901060807080c0f0d050a0b0a030c080706020706080c0a090f090504060b01020f0d05070c050a0803030403031823070f091a090702 77
    0x24041e0780d407a03504003070402c00f40d091020403c603900441234407141d100302500c80c190702d0a0842c481c000c1a0108401c1c2407a4101c0a01c071020090307a00c00c0e54400ca0b46c0b40300b01030311400c0d04022500b9148004050140310340e1621030140240c0c0c0c0945100303000889040008a100c4917503801c8580740740044410b2410044243c80a0010b08002046040110b40b00c01c0d01c1d88039504c0d064501d01c041c62080c07190480550500c1105131521000d80c0c071040840d48180e0007044941d4212050940042040c40d4403669017044031420765011042d940241c03036440c0c1c42ca100041034110382c0c0c4046c0c0143d11a28050001400e284012640d4201240080c07180e03800601d0b504e419640130703100070001300d41705002400ba82c1c1d564100045249980354012070b103a810000400042660621401400110390360b011403440007241c0318440030f140345c405464941d810f03e00000101035810400040200784800382404850784074034255001c2c100e03070b01c0c4010071180c40c400c000d441c929092809a00c40d44007503000349070314501c4031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 886765647 1250 886764397 886764413
    0x100b040b0f040209012007030b060d0308061005042402160f09090f02090f06180915091e0c040c020c1c0f080703020601060816020a0308070509042306090c07 69
    0xc04c00b50305005440498219214802e64800940c01401e0064807041e45035080c581141000184060300c81c0306941e440400013038114804075000f050580d2500e40c20610004103860910442d0030035138100380e124402e6607030b4560180e000c6a20004550079511000111400500101040d014240707072031072607003070500103110281d11a00405001c3c0560041c648020340100d181c520003030300d1680e20391044004000742c83c14030504114047c003a5150640d43c0b4500000b9403a19001070b004420030401c2e11001240708030900f08003100a208089420184420052804965070904002031a02460500d06403824071130000c9444011041c0140c03069450b0b04400ca030300d4101c80d080c440100c0788410100203450101d03100c42c01030710903a0711a0b0020300c040c0d4140140035200402c0203089030b4101c40c66203a010402d90340880d0301d50700e50383e05003406a850307255120107aa15026844007142c01a04d048001c1c000080c4070080400d05019000d01e0b84159294034081c0003401d202210f25680c544d008000050016440c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 886766897 1250 886765647 886765657
    0x120c060e030114011409061c080d0902030d0215100b0910050705060705040e150d020927011a0429040603020402030f090d02030310090527100b040b0f0402 68
    0x700001100720005040750a80e0300e0a801c565600040207040354424140780406035000340c0100d8801c0484014042c0d90000103d04100c0103205102c0403688000c0801960083c403005980101610404c2e0b2828030000e556130014621583c0e24000500401e5171118011840d200baa00d000c030150303140c280c50b40140440d1140f02d00e001d4080080412008001c00c2052160318001d4442c0c0d0f035955512454111004d08040300903110f00b99901b1682c042d940942d40b010800303181c681e410395060300250341d43c1c94002d4141049881015030000c600c00b01e0781000c0010750220b108001c02c00703d44841400f9900501c4129074604086811660105c1800390800664030305c141819100100041400c0703440380d0125086e40c0041c0d0f00600e010380e0410a00c0040740703050203406040c5205100450851820041d030541c0b454162140300d10031541c9101003080e80b011000c1d6081c6809010044072400308034a0441ca41d038102d003001100c0003516080038000d59141c00d000d808500b110040c400030000002104020003903003c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 886768147 1250 886766897 886766899
    0xc031a1501093b090d05030c0a0305040c0906090b030f0c090c0d0e030711090618060607030306030f0b0402010f0203041d07021f022a03030406021c1a0a120c060e 71
    0x50350f2000182c00e4150001c2020803502d4407016541411301180b180d1401180748050000c0c0300c8144204042a4030481c00c0e5420074503546008a11a169400d01c1a006d40342504018891428910b011500031000d810064041c0b009030f00302c3e8100c085000303c1c55221010000c2c0c40e64003130040d601050301d628500d00a810642601000025480d81008c556403460348204c40c2114030b10042d00d000d491501d012050a42c1c17101040e210031205001c002500801c2960092100b8170580f0b02240c2c071000d140c404c1e84808c002d5a030001a09002c00781505040300f042e90111030890000d95100054010383d88044155030841c0c0d51145080340a80b06168652480351000304600b00b1031050890100100201c80002ca409401c520001645c82c004200002211802941403011050310480401086e107000021668000e0300100f0060f141c0980c1307003009240c20318003201c103541503003030514507514215510b038800d006000c1100c6980401741e0754100360141252030306c0302400740403180f1030801a00c1c1c042d9681942180c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 886769397 1250 886768147 886768199
    0x906090603041b0323031804020a03060e150a061727030a12051302011b231506120d080c040b0f130603020405100e06070c031a150109 59
    0x20b02400722504200041e030084d640c800b080e01410410840070960803400764640401b952410109911318031204001c60303038050186900169001c3c056109520610281c41c0303211044a0a06100395800d0208640e00d501520500003003200080203801079100b04401d0304071900c610080e50307651104840381540803181074034240d20003664064205003440100600e00346510b90300d000c40050340800e0b00715a0000d0441d40d50000c00740d80c1d040585c0c2c00c00700603079013100d054036081d4441880745000c5400b442c070700300300800940e4245270801440c40c0209070550401c0140d51003111680d204003c00819928014140718240c002c020030442c2140f040c01203d40c0408207500e0103142c80c6d40e4480300c043c01d0f0300003a41b00c0503410300481e60790404040e10307070f0520007840c0e01d140a50405052200080342820034040a005100500c9206201a190304007941e501c10707000000c4000165880c204141880940001122154410400140300c8a4511044160740740180d5a1401c25070404c000c10301e0a024115014112034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 886770647 1250 886769397 886769423
    0x3121f0b0712030c09050d14010e07170615220b1e0f090709063e0d03110405010f0c020306091c111506040b04060b0a0e06090609060304 60
    0x40460300a04280380305200800c882c90200c40024101c9441402c07400401603a00703801c0116540d81e0f4514041182c01c81da40d80c10f1401000080c5004001914401d0042c1c01611400121032000c1c07506040300346d4110b400d4030002c2c1e90300a80e00090000b0380d080c2c1075104a81c00080744e44010384500031812901210710000e180e400c140e000454600c03881e03003c90800c001d00c08800150782400700300c00c0200c039800d413603041460404900181180403903009a4042141d814014071181d0000440480f901500354060100801800c85100340190503500000c218410540c114400511030302c6420080d6105508003401c180c00c0000440f03107400200400d40821070050a2080580d45c103118050043d02c03103000509000c0000e8142c0808400c88220303450034840f1441003103104030f401081c4925420000c254089860b0ba4000028008110342c8503515000f6280000118101c1c200000070f1441d003201c0c0c2c4640a039012400b041044500c507849e0b6031504428107000b060b60500701440030f950090f102e142000915 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 886771897 1250 886770647 886770659
    0xf030207020d060b040c020f0c09092811120706140d050a02030901060617040f08070b1509090c0109030f232d0a14030c010f09060e03121f 61
    0x103010030b00c42529066502d5081116a152034410800000850b002604513440ca10074134a03240d451310040e40b8040c445150000e02014028408140e9545500d10940a600c5080d080719801144403102140c0300740c0385203a0a20103203403404840b10640f00203801003074000e051400880e070b2281c8140102c2c8a0b0300040c00a40059612400b40c10701c078406083c401a200e180c440a03541c2521282d0744101c0501c004c440c12131468840c0050007a900580010a49502c1402454841c14a101c3c420300601411540421320180344c520303112019010b50210707511500c6442310072015031108044404c1e540410b411402c104001540c002c481c4070340074003620b98000c441c03101c203482c00215135002850b00740e070f031f040750046c2c1c024000243d610f1040c0c0e01c00d20740307100c4164800d002e003141d48440205015000c8801c0f80b415440e2110200210b840c00c0a007a00244000b070b400132040400340c031110070b046880c02e0420b1003840c0c0c00d00c8000103850a010084400b01c03841d071110841c038141c5021001e00c0b000040302e000e2001c104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 886773147 1250 886771897 886771909
    0xc18060d150c0c0606062303190c05030403020c1005070b060f03030c0d03060902070b01060c05160f0815070207060c0c15050301090b03120a05180415230303030103030f03020702 78
    0x30410300b620b0341c0c0c405046900c0d0290817a002d0b60452001d2010101d8140394400a500030500a00030b44100701e0b0340c039281e21f90800049108089000280b906012514150300c1e031210166004621a030200c0d038280070b5140c1005010542c00c00e00c040060300c28030403200415107941c0305681000c0081c24268000354003802081c00c642c0540c601d4911503101c03407103000f4500e50500c101401852005030450512072240e8031500084010710071541000442500c01040c030006101d10f09807242d102c0c00014149640c0d03070a40020440394890442d290084100504240c0c0d8a26809841000281d0241038050706021007544d10108481007920b02a180ba00007003050301240681400403012912103940365850142040145c40088040707070300940046038506551185038050712030741c2030281070003a11410300c00d80008000c0c803d811007691160400d00c5881044d401c02c600c40b8181e03038180f90000410101e880304004440140c1990310b030581e100700010404a485240c0602202102e46405031030600d0603000105 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 886774397 1250 886773147 886773161
    0x50910090201170c030f0a05130b041e061a0312030402010f1b061d160b18060409060905251209150c09060207050918010e030304050a0201020c18060d15 67
    0x14000038000103100546c10b400d032000346c3c080c50410061007246001790240a81c80e01446c00186140b0103000402c0c100301c5400403944070506103034661250000316040800103017002140b940b030841170704600303110b00381800300d08894404810740702d2038a1915581c1c0115440e807199884182004565180c08101d040040b0b40d01c94a117010340c001003102c01580d07281d0f100d11840100614140e90022164950080d2800c10700e00440e40700413030907503c07681252200c4d180c4a020010080c0d00080000380400e41c03204c0d5034800c405032094071904100c6542c1d07051010340c400c11003034540c080761007d4080c0c00000d50700c505008002c084402502203400c032a180e5482030089000c0504465051302c07036098001c0342c0d80c020325290080038544010300d00c02d440c00c0042038015801500d010700c1140404100040400c094010b030206209100c1160798900d0142080d50b1104c1102031b04900600518085d4800761a0080420780641030401c20401583c94010402c048640f00c2001150008940140303160780750310321f100d804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 886775647 1250 886774397 886774411
    0x7032a2705070f0f03050601030b030708060405060c1c020c0c18040302063304060b040b0a08010b071509023f1504021207030203031303060b0405091009020117 70
    0xa503041241030201040d030714028142c60801c5150440829001d07403041110aa09a10b82000034260300c030000120b000e0503401c0150364252023200d50005c0c201900080c101c0c8a1401401a41c00303e07100d03080140c869101c2c0c1c0c9a02c140603044c1d0b007542ca00d10b03103140c0e0040c8040e00b401c0d0210b030f8594003d00c0100c1c0f4806c0fa4540c802082e441103000b04003d2540520901d0b070b101a95000320360300e90401960300c0b640102c0c495003490000300b003c0008a680e4450750300c841d01a000c13610a0a4845035500f58078001c9900005034600050303242d000000314031601314160340015601000714654506441d03404c02c000c0c00a82801ea078048805c040001c07540303440c80c900b24660200340102c0d1200c0c0c01040824410280b194003000a594400f08035203c10b110007001542e00554121842d003c00c1c034010600c20320700400c07500044d5160200041c40712140041d903035507001b2684200401e02c0f10000070410082210401c452200300c80d0001020042a0740c2039a10140d4224814100b5000707400821401c10b0046030121124 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 886776897 1250 886775647 886775699
    0x120c210f0909130b011205010c03050609130314040f05010210021201120602070b270c1c3003110306150f0f0318060f090a0b04140a03170907032a 64
    0x41b090050038020582380c44400d0130144860705140340860040280180000300e48804400d0321010180710b12030002400303030380701c40842d1502c2d12045a041c000742c0a02c5524050f01c2440141658100c050080d00d08c8044100c3e00c2c10401c1e80790078510011246001c400300d45003079081040200042c0d00000060060b010039040001d01128224007024074100c800310410180c1c4452180200c039901d0300f440c01e1029a280224601407211803074040850345d5400c040c00301107208607501e03a00301c103070349101d1441e05135696030b0a00c4030918010b070756880c1e84015185140c00c807881c4c02078041000c00060040c0340301e40c1d0f94245070b49052a80140210150003c0e1450b40c1c4500003220310f485810000c001d25500400d050700aa00f050601040c5140d60b060704441c02031002d1807041c006402e115640f81c55580103242c880c2950b01c0752506241c024440d0242c0c010000c4001d80c21804200140e100288100580e40c0c0304052000d034000c1e60586003c1000640b1150005440420300403030801806820b04640322111880 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 886778147 1250 886776897 886776929
    0x2030705071202160b040b033105010923030d0b0a0906080106090e0c01020607080a0207060c0807020d180b070516061d0609090402010302070203120c210f0909130b01 73
    0x3500741110007a0b001117000c641c2400140092404001186e80007155141c0ca16040b40324121301c4180717900c02103030f204454288075a03580f0034010190070600c0101d22861110403444e500d003010841621303000d40002c0890780705000342100c1a03100d0f4091040080028902e4040c25500c0409000ba100c0b0740d000269603945415003040380d40207600442d540c400c902c0c0043c0141c10f061a000079540c000040c083c0302080541c0300030510040c8540d0460b1020380e000700e810300c0320981800c000f4003007100940e40a0014891418040b41d614400e16040350340512441003040001d140180c14030305071b04400707400e542c1c60003a140048401c4061075904801071002d030300c410701c00350400c5400100001c3c2401d011400750004000c00d00d150f55030726001581c841c0d0309013001070f1100301e1400441d10b040300a1b0042c5201343c400040c0c809004800180c1c0800c00c114511100d404648844003085036805481c07040c051258003800036440710320306600c0c4113030302070080900429180c070340d41c0b580d00d41803600781e00010444418540c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 886779397 1250 886778147 886778173
    0x10030f0506030a08030705030a14040c0e0a20070204140a060315090f061d0106180b010e060904020304140712120e0904060b0103090b09070509010e010b0a0302030705071202 76
    0x80d0540c4250110080c080208036900d9a01d050322004000c0020400d00000140c0d00e0f010729071004649449411102d811440c192410042d441c21600400741d0342020000050280038141c01801c214003c001c07860703030021064034800412600090401ca030700c41d80340e10031490720211184455218420103240402c407203181d03040030b0840310983c4101c0032030345080c20002c0010542d00404003101c0e40d8032040c001808101914003c207003203580365640c44603500301440010b03030101c0c0300601c00c84c00030065020001c102c170460054800c1012480c01e66040f41c020b022003002441d0590146034014092040d800a003004c400c451810144550070000207041c000000409001104100300407d80c402d051513501d416058002070051080208002c100c142c0300c1d1400306181c2d2017a0010b8034a00c0c0c0c000411446420140005900e9412600485005a02d580000a900380f45410968102d404803403c0c1d92406100e500100d01960004040d24103102d400c2144100154031340001c40be203080d85e07901411440e14041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 886780647 1250 886779397 886779401
    0x102070f0b061825030902040906090b06030703030207032d0f26031f08032b11070b0a0b0901120308010e01080304050418060e1501050105340210030f 66
    0x4040300054020b8410000f480708525290000546413a4500c80d010301c40c140200c002d0700b01d10200039003050901126401700240d94001582061141e100f03220b00da034881080c10744e00c0805200c082d00503405a0b1042000c034100d24240044010505003e880700303a22a00a04247c5040f41011135120b4030001c0d0303c10034440341e04da811141d560f081c070400041c015680c080304141d010203050741e002608641080d441d503083c0c99030744000a0529405890321084030041104264035014840342d8032000b0301401c80581c205510540c12034407446104c09003003018a441e541114003000f050560300071703554012404d09640c3d601400e4000e06001a80c000031450500c0c0003005c0c2c0106138084142954800300601c14484080142d4054600c20344000038400d128203000c06c03020030441c030060002c41c81c22613103000282c1d0210f0060085540e01c429020b050360f984004440c01d10462030000001c036140c0f00c87d81e113280050020791603c8215884901c01d92034854002881c0f800d2040c1c002c00120343e441c10349a0014401d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 886781897 1250 886780647 886780669
    0x4060e010204050f1207150c0203100c14070809030a080a021902130917030a0e070f05090c09012c0a0609080d050309030c0129240a020102070f0b06 65
    0x14402581443c0c60725000c82c002125000c6001c1c4070f0b403100320b00004114020032010000340f0744c030501c03400301c4085150050940d0780b400109034041e005018881d2a5080340e4090101d510510741d030b030b5541c51140c4418030f40381e540203107500311680380c410405020303030b81e8041000d01c000ba80105411641d8101419001c0c0c42e001c441d0301d1407048421b8007409940541d649012049200d101400081560001890400400111095400e4a0308404800e000500002d0b5228007604610398084175200d5488115010044a45108a0b0340c00b41d03031000000e10000401c00908241001810808018401e28005184041d5242c04030220551400800c906a00d001a8075800402c29800c0401d1494100f034615a02d038100c0d82c8045041c440004003240e1400d0041040700d000810420080001c0301c0c503001039041e8503000d04882401c03071802400210391498a9828291500f0580c0c2d120428400a282003c0e03168101c400c48500b5958203000d06404a03c011b042080c000d8428400c40702c2614050041104840071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 886783147 1250 886781897 886781921
    0x70318060215160e010e24072901050d210e040531240c0306090b2409040f0608011b020a060e031309020903010b011d0f0402130e0406 59
    0xf102c0307090a01c25044640002e100d5000c0c6440d9400001e110085842400400d43d900030043e041d4010818a03840007010342181482038052003000c400280d4a450382d2020309420856a0407240010456880c000c00c1c00b21500e4031492505410316689a01c5d038802da014501c004011401207000da008601e0503105942e400456012400b00c843c0d0b2410002903181c05410400d001c10102c0701880081c89612074100c5040000d000c03241c000114586030a40c042d00e074522000c40800d090840200b030600603402440050207001c1d100c10889200d803881c01410307034440103050102800c10422500c10342c407503025142034180b120402082d81481c3c000314500b10b50b041d0121030100f85100303482c4525158003044004450f500300c5004100c4940c45c490b0b143c15440703a0511260b4404240c01d000a820286030060070303040e00210000c0002d90783d01001035071440c00f04d40da50b401d181030944800840c1d1400109544480304007500043c24038048076001060a529600303e51040c034244400c2100304100390040e40c0340450 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 886784397 1250 886783147 886783171
    0x90f0613050109050405120a0909020f0405030a080a1e0503040305180301181a040c030f14160602010e06061f03060302040603081210030222090b150f09100506070318060215 76
    0x388c2a00000c2400240340034056a060700081c0100d0300c00444000d440103000024242c84040040d4604000590701c1202c80b41e0106038111446e520407810f0400750000000b168680501c0d607a190b41d4101d402d6800f4208901e1204030661000c41b181e1401d20070240c112007020f60715100c02c0340d1403c212203800012052000c120a2940070400004d02c2c0204e40002c403a03110510314074a00d0185031030311092000d14010302c9148600408000207500f4840c60f5405c88640703030000c000e0000014441501e4050454446400c15051031010607200b000c11080542108246000280c40ba1a139000906036140380d8425202c411010070003442d410001e018480e00028400ca94540f241d103541c0c00300e40d00e0122040f110f40030500310440f036070b5400480d0b0403216206e035102e01180355910300340480560450002c0b0980d07009030818440714243d400c0c00b203040c5018144149419103100c1c907141c100401d95000030350440420440c031400c3c0003410f07021010000a0261034018062481e2610750900c04180c00a002402c289 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 886785647 1250 886784397 886784407
    0xd0e0f0c18090c040e100f2007030c0305031012050a120f0e0f012f212d0301030309140a1d06040e0f0c0f03010605090f061305010905040512 62
    0x2c400150b1103403840c40640300130844d907844850700e508040b118111136094a041c00d020400e91101544400b1b076070307032202c21202200d00025001458900030030740c0040200d801d2086490210f801400036590008800e0b07a00920561a4110140c9a40401c48111840e43c045c082035000c03c99040c480d050f0707265082ca800c0302c070442a258001c01c0e442040300624000d160080600105901c202c80342210444241c0617000c25032800e10740c100000264103501d0a8078090780310315280c140d0649a07440c500c00340b030001c2c2500f4441c100d0360304515005895500d8005c60441445001c07185503e40103140203501030345412072101c0c81e11418043da1030449581500c1000158024803d104070b421070903098060110104019a4403200400e00900c0d000307003034140c0c500c100440103050700d10000d2503c8650341c1c141c400031103034009401458242c03181d900925610102c0b49000a140400740c500103640404010038044001c0d0404180d04100c0f142030f0892102d075500d601c10842484410010040c446a6118055141c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 886786897 1250 886785647 886785661
    0xc050904030f1214070c030f0203040b0912031e0309120909010608060102010f11181f080901270201081e130611030a06030b01080a02010e01050d0e0f0c18 68
    0x20091588282e000e1203100d83c040ca802034469030040c403c41c001d080c111500c81c1400200600025582902100064000e16000c420a440070060f60100e40c01d0080c0340d810b00341844100480000050030000302d034070050003e140103d00d04481d459035104410f10b130b10340d41e06003400c85031300300035482126042c0c44400300407076405130300c413040c546044407030518107a60640c46420040303000d03140003910015410b05101903944801da01780020081180081d000b0034122007200140250311298504101005080101032075607a801400303460780c04482d46c00006482c0d80048081088a103d5008400c003442030304069500315600451100d400c00030507000b0025089400c0ca0f84030039140c0040040100b074120350440c0b17041208640100c0c4048080d80303640364407441d000e16510020a99440250b4005a5031000001d00c800c02090002420b41c0607035404411041700b10040d151036000390340240c0380c00d40c1d4031900c0c1e81e00b401c1440f9074400c03c0e014030042e00300d4040040820110585199000408003809410b201c10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 886788147 1250 886786897 886786907
    0x30f1c0c0c0809011701030305040f050f0d0209060a09020309030405040f0b030d181205030c01060b0711060a0905030f0c030c03031305091b040602030903070e0108150405030f0f070c05090403 84
    0x900c5900802c040e981d0500003004031900355a040858038900d40400000c001c05821101030410b40d0170402c0d00e0781c0356a0340c9000300000301c0c0c00c014209400020080c0b002e809806c0c442901341e07004401034184e10806a0f079840a1041381d01c00c840800b41500040b6050282d440e0a000300301704000400400d110100341040002d880c0c000200515051040108a0212442c25011150000c5ca0682c602c50701c1011641407840e101d0b03009003842e0005519211011464800e000103031035400f81c0050601c24124031000600a542d880084c441051000d00400000c0d650b40400582c0420410b11010b0554090100c2c00d151030300e0503441c0110b00c01d4000b401203941000c0d100101800300d0b0001c8070b046031151641c424100303114200541d56142850b0015022409640000090240000c140c0403550700603a160080c10384840203000308039003a00101c6003040010003d8413800c1d00140a2015640342c03900c0317043d80d1065503100010680901c0008a2b40500b4480400d1071a0010704040e0740b00714140c5415074001b44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 886789397 1250 886788147 886788167
    0x70f03030509120c03010c0503041202030c150a18050d020705040b0f010302030c310501022113090c021015050904031227061a030d051b030f1c0c 64
    0x80501c1d00c50314241c1a910f01000002941c1102074000c00c45900c08a40c0104140e0080790b09030b659004058121040c2403000080b04d18a50709107029004000d44030b0450b051400c2c2c060040c0d0314a44d103d0a411100205050f524401e0b40d00c01e00040045007904480a0b0170494207521141c0f040d0700c0c1030351402e555141e40010020384002441c0042c0e480d603412105080601a5007150300b28070411403040759003121120400100000c500c900b48d42c1441c0da45004aa6652140c3c12612080501c0e80d21100c6404421019089014440b0300b40016a81c0b20381c2000100c841d407031304600047c0d0185488194181d40d80c0304005801c040040e102c1852400d01c0040360a600010f4402820020044c0e160455100c2d5507015010091002c90744611849064500c02d100150086081d200c880c42c103403c0c2c140c103808102c2a00390884c80500942402449a401550a50404081c0440c6607008204034140840c00380010200c03038003a44074041c0c42e006240d010b90304200e444034416046600e4042910822500104054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 886790647 1250 886789397 886789399
    0xa0809011b0c0602160c0509010e161d041103011401030911360a0f0e0a0201050c0708010612060c051323060705010504060b01030902090408030702030c0607090602070f03030509 78
    0xe542012180f501000900c43d01180c01c0d009504400030741c0070403c042120208450086425480c5a600d58a051000d031b442994220215500783e030070b243c0014056000c0c200500504071a10500c0c00303a42e0041010351303031100c0309401c0002000006015141e804021300b505400d003131070304001644540d65071a83c00030911402d82e00c550020442e030a03540d080445411000d42801c1c040d03c0f100061135044000748001500e0200003542040c0c05850f0310011480f4038030141d90180002c1440d0207540d00155815132102c0381107103030f50080c81c0001c61000c0b0240541001411142402800f04601342449401c4034075480340001003120400c014031801d800e4061600c00d440e00001e0008502c507181c1ca10025100e0342c5070a0680100d4040349640c00d009044d8000c07445580181d009001c0c03000c50200440c00c40e052030400079807040c0703404040f40220b503034a8040c5601040b10300480e490082e420079400d150038421150b5000280444409015095051201500402c601d00c1307581080d50460784e028210340071b82c030109 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 886791897 1250 886790647 886790657
    0x201090b070e010929360306040609020f0303160209060a06090e070507120513150518121c0f03020301050d080d090210030b03070e01030305091201150b0a0809011b 72
    0x25824801c01c03010710701311101d450045c17165100980c081c0350f124000c200c24858049007100321842d000300030010f600c9000c85002000707400d481d910f954450b4001c010703102d000e0780c02075100c2c108910f081d00c04000402005103081040414901c903841005280c460040c00d40d401400c00355010040541c008a0040c00d032800b401080a0642c2c0345da0003100c0501505502401648407808072100c1c0a801800a000034503074991001e40d05912407014406001c90100d01c500016410440302c401e5140c0c01c0d0320804803181c010f1101d102c144005074414a0704007020b50b09000c4011282c450301c051034214540400a1801c4e00741581198036240010349003103010507025080c5a00000d81c0444420b187e80301e0207050f40d0040c00b90721a0550110010000d00340400207601174802c8070004030710b070340150322668100e80d40341e034400c1e107031041c21010301983c2942d0801c914043d640341d00603808250f000701c041b10090802c05502c1c58968103104401009801c0203004080d082e494103401c02c1e02131981c0c10307007450f02880c80d0903d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 886793147 1250 886791897 886791929
    0x21501080a111c1421031909080a03020d06080106030309061b030c080c0a0501110306030c090f0105010c02030a060f021309091203020a09090504060605030f030f03061e0904030201090b070e0109 85
    0x580c10305c0302c00c0c526012402c80d0006010f20100600d00039502443c9040982d290b500d07842414a0100c179003200c4050403462042c8009000d061090300101100221950041120341d65404001c2c01c0d03030240c2d0403c8000c202521024014076a00840b0000d44504042d204c20881c860754401800c91084084042d001c20740c0020500005401040405100c5600c00001c00c20f0650142e640006070704217a82c04c9110380900c9109211a00c1c0c1a91490300942603107070804280d9203001e005540d05002e24904036014095100058041202c2c0c4c42040c010324001000540c1d11034401c0742c03214905515070810000c040c600414240401c1d14805003210240a504005030354080348101a101c0d1412540319180c50b80c1450b08000c10410b00350060f01c2150b02c03e030119603101d82e0718803c041c0c8034000d01490846110003440043d03407620f084081d04c0d074400301d9080e018010b54048800309400c00300840d400d501603910b40e40c00e01704200440300e210350f21005130315140e80b000c051100004c01041c017500c2003440383c10103404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 886794397 1250 886793147 886793183
    0x180115080114040507050c0f0703020306090a11040e0a02060f0901090b190e0406090612050d020106081b0a0b1b060c1c2310030b0601051c0903021501080a111c 70
    0x212120305e1040422120311a1340346900360358449d42400f0890103409000d0108030380041c0011010260f40d40b001c002d003001c040f0841448004c0c941181100c96030310a9030070000247e00d40b00014602c4141c40d4041555501d2054000b40426500d0b50000d89998010020104d00e1003080d10780e50f01c8101580792840d1031400300c000107005425907401003099180b0381000007801d15528524840001d100700161486040c401400740c0c00c9400c20302c540150341d00500c502640046810180800c0e00d00002c1404100588036090051309400c038000b0341c001e080214401d0a0200803c1184680c400494a00f0030f1038180906680021440309003611038290b07484111200001c00381e4250440e2111200740081d601c0e191030a20110b0b141c446200a6401104010105074154414012506000740c0120b40002020f800e074101c02c014410701000350704600680d450100c08141c0300a11701d0092095000800e40d0440e80d042481c0c000e80e406d50b0242c800e110202c0010310b002195240a419681c00030311801c0c00c00380f401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 886795647 1250 886794397 886794407
    0x1201050904171c050c0c12130306112701050d020d1e051905070504060809100908130e040b01050d050a05010c080403110d021011040302180115080114040507 69
    0x44942c0e900800f09019030384001d0312003041c0c80500810002d004585820b0240207007071003101d942241030707008100c0090b001420b080041030341900814100c10810360300c1e150341d02140c80e1000101c10026001501ea01900b44501003108103008016118504812603400a032681c407078441010082034012441e00b1640f101070344444081c1c580c0418002c810442100005c008001c00c0355116241202807054a40303014480c0b203810320550446c1c554924180c02c0c007200f80c0300804010201c80c0144101c649042000c02ca070300810b00c4040c458401680c0fa0220392203244e2500203190031031144036448004200115000c0b44003141150002d482c040888415070038034500b007d580d220041c00c103600305070f00341c0a155800500540f04900070f03a03a24050801c01000c1d00d8032001070300302d00c3c0016803000d4169092420789501908000e05402d00c42d51400303950ba408035800305582d402641c608813820004100149020b041c049010001c1c2c504203000d1740c1031401340642401c075404000e001d0b030740c1c0d032002174280c074010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 886796897 1250 886795647 886795673
    0x280b010504120b0402120d08150a03061a130209030703060c1115101508070806030f151b09012106090e010903020d02010e03390304090c02031201050904 67
    0x80b00500120401e41001521528180ca04900840003d0580300e8041d001048400c41d20944e5683c540c050303200c03020712940344103207040503a074440c40c02c503030000018449200e0813040314135655610681b0500103081110181c400c00d411001e85004220300041a6000304159050f640d00c0000001d601c4403852007106d030070302c100000d01c01501c101c401c62107445091182040c03040e0400000d14241586034480c40e541d03c001300b520f01010990030780120b030b182d41c000e02001d0341c011400390480c1d90a0a4075130700d040c81c240305007000702e040d05c1740c103018030001e031150108240003108088186481c1c0000c510000303080c14030911542040c940c201a2100c205809a003202000307241900041c085109280000d80c001c20300308404801500c20003008081840c018000c52003114003082c0a141440c0e8406858002c6901440200c44400f00b05001006062080c1d100500c0c180c0c140700040d500c2c0c0e402c1c5140c6004846c46003072080f09650007032000c09000ea200c5105181981c0c02030316083c02c1c0fa101d51822500130000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 886798147 1250 886796897 886796909
    0xc1e0c013606080103051c090501390b061e01081e040c230105030a0216080a090e010f030803042010030b040605010504120b18030706090308280b010504 67
    0x400100080c0c0b9030707480403141e03051328003410070340b000440503421081103800416594004542c140310100944c1d802020085081e000d040141040c00140401c0c42c440040faa00707468003070511800942d0203024031000c0c4158804001e0300e00445004035100c0e54262225010080c0741001142c0002542030443c03000710303014043d035803d034444007405c0c070f031034081d00c400304a0046507901020f080340001c07148510352203101e0340078041c2c485510390b803a4504d00c0c02c0a584945150100d8400401590000910341e2009200d035212a41d55000d0b01c9040161342401c0a0060b448805140945401800450b221074100c3e504550b2010b80540e504a01e150340401d403085402001ea0310040c0c5032142900701d0703096000030141c020112400c1082035140da006454500940c01446c0d60041c0d000305840c001440154503a030000a0265101c011400c1059050718690040070304861441d141c414080070181c210b00407c0d00202600d40121640c080720300380e0140e404045000514007500c8103240b00035a40500101d0b405095 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 886799397 1250 886798147 886798247
    0x20c061b040807080d030f0c0807120915270503091c05250f1206050a11041d07050708090d170a02060108280b1b0c1e0c01 54
    0x144d00c03800543c171103044503240401b01e03080c040440c9011410b44194401c1e82096200e400441c0c41e503200031101c0c8900405103c0c0000d568945100c040341804913032601080c001e201c003080403007c802401000c0d034003094161a00d00c440e480800e00055001c015140039000903251261490304c035864104004504401c003805500034492140b0711b03921310b00780342e004a07030910320303903100035503847d018262071501c9071190020007140e01d506500003540582020340c00028074100429482c000c040804c005a00c03c0d40a208d852000403040d48001c0102100341e94050000c1c2091400d01001c1c1c4c403030022511078280e08920a40c040241d20042140420320f404100b800d40b00d800b61518030704440695614028014561244114041501e4400b020307140102200c0326180411301141080d82c5404007a000a0030641c0b00300f40050f80e04100010000107000001182e0004008841003041c2d000e520104841c540100c2c1d030065032a2410320f903000410010303200d075019201788580914100c2983e07c803003541a4809050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 886800647 1250 886799397 886799399
    0x81303080c01020c0f0d021f0608070f060206011d01030809030a05100f05060d020d032a0f020f010c17220305010b120a0c120f0f060f0b04020c061b040807 68
    0x70a05501600030746081004503618143c0b00400159070b611400003802c0188e00204c8040036075440d04011054401c80440007141c0c2544409031142443c06c1c0e90002e6081040c42c8608100c0300e90304101490040c00914a001c2d140011000c2505034080140005451207400242d404c1d5180c8041001c484203c0d00041551000510303046104084c0c100010000390190900010078000d01c0d000c40c03504881c41e80180f141c41c9040c407503a4141c0b2003000400d00c00c40d48140d01f15040d144103445480180c4260311030113082d0007465051042161000c40c1c401058104041e800d444000241025203004d5181c0090078295100c143e01c244030090205910f250b040c2006401038000700300001501708501d20201150040900d8900c001b03020350792110301801a05124116004111003070002401c0c0c503030240070f441c007250644803a441c0c5a5240844542c1101c00c01d507213080e42500d4240758880d440302104110360039442d0168200765180d950740c4c094091901c0c2d141034404501c1c3d50919900f25402001300c0019102e140f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 886801897 1250 886800647 886800667
    0x30f1a040308060f01020c06071e05100912050c120c010207081204030912030210050606040302060c2506022a0910061805011d0111030c0c0a060311040308130308 71
    0x40da02c141ea034503010b25110b00511800358000b00c3d2000c6000301c0030340090305201c02622400116401010022003913803900b50300b20082002031028152040008401181c0e407106490000006110403000c2d4003040b03405d00070680311640100e41c012010300b40524a544410080d04524024454848010141d0a00040004442c0d0b4141c541078480e900944488020b07640c2c4541c005d200581c200c1000740103070015861240400e00702c1d841160040e201070141e900300340d180ea0200d100c0740e12070080c40c0039550001c41d10351f0210810054840350614142c07000c400d801c2c508080603560300104460b00005440410341801c01c805042150080018010400001c41c2026105035121541e903008400008003c5030f01c602c118a00b00ca0750b1800c994040c0d55106d091142d44420410b10a200f5010a0400003540f0141c0b0074180c0400141c00500d9211000d0101000c2e05400c1098100c101d03070050007418181010500345604032000d580441c0c1d00404483d5944492851003444030783c00d038000400135030002c41d4031160707 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 886803147 1250 886801897 886801907
    0x30207050307050108041e080405090a0e160f090f1107030c0b010f030f0803090109080a17090a0803160e04330e13020103021603110d0503010f030f1a0403 68
    0x489005a040d240540d40740c400440b1150011500a040025080c2c00740700301525100ca81c6e100c0b9030289423041d06158840000840b00032055403050781c403585501108690190030710038420152510720451584c0307460300180580c2ea0045201c0c0c0d000e065500d00160300c400d48a600000800101c5c0c00c40140e6403803d92502a004903110f00058a92945c040c1c000f26004100c03491240c140c940109418080024946d240042a8002000d11015540b00c5040c41c000a5806000c1c000c01006601c0b2080e0f9000b82210220702d45400611403d11940070104c0040480c1945040b203800442c0b249440002010001007907a165821800c900e4100b483d2140e82455288003801070f41012410742600c2013220108400300200c024140240b43c0e5050b01c0d9000308541c500a0403004140c1d52045c18003604040341110420f00d0191448030a80c0451203102403180c032070340d0501006070360541c581800340c150350510010b4049244c42d804000c0407500307000030280501403400304106200303143d094a040c00d132509144c0140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 886804397 1250 886803147 886803149
    0x6030a06080d02070503191109040c0503010b090c0a030b01180e06011b03021b01030b04050412080c0a1b020111030313020301060807030302100504020f100e011214240d030207 77
    0x4074074020803206601d210701c04075a40d0221480240100302c1603403044404c50084c0c080c0c01089403111111050710700340391a0038042c24402c1d03005a0151fa5014a004245825510480c400501c13031481c641c20030000f00c9419007034034000c9086150001c7d807410322030016910b2541c07044007500343c110101000074550070407108007840b44d242aa01d0354005060080c810710010203800c00180917800416404c4150240306401341046401407401080358042d21000c40c00301d40065030103840b0f42d01c0c004a82e9035541c0d00255000c2d0441a00844c0034030f8110403d5000300804452a458207002d0260301c0004190780c4180301c10301c02d180300e0714141c903928100502803d420350700400c0124040d5081030400114603002207030031801c6a8068018240e02c072624090140100700007407040b41e01081d0881c14004070384460103510355040ca19225607141808000024044010000b07084600c5400d100c1e01c0501215441c4203190016000c0c1d03825002080034140310b080e10420801ca2580200225154005266000402d00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 886805647 1250 886804397 886804409
    0xf0307060c17012d0f0803030f010e01030206071101050906040602011b021f1e020a0c030306090b180a0e16030209011e031b15051801020c01080711070506030a06 71
    0x4038207224401c0ba103100e42400d20510812160300d607404180d410020300600c0341c142600921081880d10b6418a4101d001942c10800d071542c4080304100e640701070f8501250240218045410843d8956400100700303100720003000b01034100c580e854a0103130740900241c445072800180400d4850740c071118002e0007071803074024a20780095640b4450b0f103820f0000c02c0807090b60307040700340c0c1ca44800390040342a0050540080318640c0340c00440c0340c0640021103840500303840c010a80c0d950f0028951b41c100101034070310342d03000041814a003078001403582c1c4d40e004600e100c501111022403d0380da103500002c0f005090001d40c01e4102c3c02140d8111114560740d07c03048055910860321911a0f98131f13004400c5030400c03082c003001c4062014005c2480440c840c1030503184204120140a074144d41c0300d010410402c0c41c01c0200c82c020071400300e00924481712609a90620300b2007840104502c1880e03000083c44450050b0210382400461204404a40010301c2584080c1801500b095070301c0c00c000c5a510001c1410344221 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 886806897 1250 886805647 886805657
    0x51513022805041806060608011a0f07200a03050c130e0615031e03040510030e0d0509030a140607170c0a050d0b10020c030d1b140f0307060c 62
    0x940303407a5040100007040d05a01c001522103803420103080c0402030019441c414040f501d40c160350400559280034040261038240e5030040c480d4034203c1c44507c0314050307070408222500c060103001f03210043d26003540c01c650707040480040071107400460810851104412a500560011000300602000040e03114079210180e0b0030084024102c004074003140c0100495052540182000c1024000301d4460701031100c40081c244c59442c2e41c009038480c0141d002880790307600f94202040412461600c0441d4030349a800605060029030211040340744c0320006040e030365090150104001c07c1944042160302d42c09503000010300c8080d408200b13804d50309c5a04641c81030000311085102401c0b840c2a440550091205090003824a1150141a9415001440341f843e2840c0e43d807500c15880d503500002c072954100703260041c041c00d504603410f05060090110301d03a01480f42da1140000411408203d0b0800f003a0000c0e00c40f000344a010040320f0a0008500c44010075210102d680d1040c420b2aa122a1060702d05880e9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 886808147 1250 886806897 886806919
    0x2b05070905040e070311210105100b28120204080109170a0203070b0703091a421206040305120a09030e010c020102120d09142805151302 60
    0x100700590b841d0071490303d02c60304001c00c1040090030003010343c00d0411009200407014030041c55030030b945e206908104400743c5c2d102d500740840400003107036250181542220b80c6180c140d0320700c12404075240e01c00d0721100d880140c078003440b241ca214000c0030803c480583d5095540d960340350301d540d020305141d5105403403040e860404902c89119140482c1d032403080540285080c0001da03100d003140c00c40020026000d040e107800101c0002030304890400300b454210912580765040c00c034050682021201607482c03502c0301d01002101004503c0099940300081c2101c4408102800c0000c140038108428060443e4802c0100340001c00d90407001420903020380d4610020035550b840400000d0f592032190103070100b2084001034095500c05c400c0c03245d190340107004491b94003801c42c4a50286034010614415429076895aa808108001c04441d9482d40c2050043c140020b50003418540390321a0015050303036845402c2c694007080411f101a0710040200001d2448030319041d4542d64400e00756840c102e11030300b07040714 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 886809397 1250 886808147 886808149
    0x10b0409051503070b0d0e060103080408010e0105010f14011e0c170403020f0d0f0f0506150901050a0e07140a0f0801060c0f06020307030f1514060703142b05070905 72
    0x2403610089100400400113a4030742040d4249a6020b24a1681d9458a8005440004004128050003103100c1e130b140703558441c90420780f10b00f19000d40b1001c5a480c2d04120040110140580c01a010388201450040e10740f102c500c01270341c004c0001c205c2088420504c00100800503000f00018050f40c0c0515030455050100305d9a8101d00c2c452030100940c0820f03a20209503803070601d20030401400384101c14100384c0d2007454841d050320202147c0200c440d90320a4007000074a00400c0382180c076401d01600da51420b54104030005c0c0b00345426015109451075802d000440940c480c10002802c401d01c1b020603659004a18001810a10000c04403008114060000180d142c0b09502105140b500401b81403001e00b80d0390f480c0000703948060615010191518414040f171031142c0f00c0e1485482e030070321028110910b00340f07034112201e00b90380409218203018002e05011a400104c20a403d441c0601c00c240c2d00c002c8250100c280b640d8241c0c1001450f124110f540072280741c2d0340d102c80d000740455100e106046980790 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 886810647 1250 886809397 886809421
    0x141b160f06083720040e06060a05130f0603061a030402120c0a090605030d090806040b041e080d0e03090a29030f15030114070c030e09010b040905 64
    0x4840da20004611100040e81c07410781d441c242c0c0030b03159194442100c043c140d00000003100280c644a050203552400f100141c08400090246a2031101d50344500300f07440c0c95505040303e6001081c0d98018140000c2000c41544546d01b15400c001f483c1c42d00784021501d0300c1c110051400d180c00384001180c0f90041c0441c11003036a000c50f0750481501d08000c1c3c5955650760034400c0102d0701d00b24094203031080300210b00345070382e030a00c1400242200d00000036855142104043c5072044540e2104280b11070524103021010010030380ca40d11035003102d24083c050b01c4603d07103905c0200c03c2026264803103603510110020046003600424283d10004070a1201d60b00c43c560306501c0c1c2c0305030049168000360b0325004210032400c5420000100d42d00d003402c44c2c00c7c0a0101541c614070b500445009607080c0c2c402080027503161000c0e10031040b28505030000c1242021140c90362a06c1da60103000b40040c0b140911100040503c05c900c0ca411842c0060540140355a4030403074108a43c002d0f00800d0b40301420034001910a4441c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 886811897 1250 886810647 886810649
    0x4120b01090b041401030816050105070201021c09110904171204030f031b030c02102a0e0603191b08090f030f0a083102090601110a03141b160f 63
    0xa0340c84482c4d503440c40d0307214504d582c46004500c0240c10a0546640899020b104191103081160005aa1a02e07071208409204815006400182e86400d000101182c2440381811018000b0381e024480d6840b07a003405d0500640d0120300141131980000c1d0407404c81da400e440140214406d8540200c410300c01c12042e02036648600da480c540340510600800302324405e8004802058550040c2d0310b040e10907178480000c0d02d54204003a882580715601c0000c81c202c19003404842c641c4c0741c0c1b900003002d01c20b80c00020607600c0041c1c40ca0741440300c082030809005409074801c00410710b01c0d8400707400c0c101c2c02f1000900081c4003200c84515900030038012030301444012084030301180d130341ca004c58684a51007005441440000d02800a070404565142141103685001c00600007480f078240f64100c800e91040040440d80109058104410301906100f081000103030018000d9050811804070090007840c00210f001301c1346142c00055602015004d1003c011842e40d6042100342041110346841d00a150706107260703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 886813147 1250 886811897 886811921
    0xe01090b1e03100b27061011060403120e032802070305030702060c01111b101a09041e080304140a03020304170a1202031201052d0604120b01090b04 65
    0x10210b68500814425032002115401c01410580c0e02008001710190f180c034041e000501c4607019400380700452503c1d1698141c01c00380c1e483d0008882400d12000f6469103c0504020300303110520341c1003030302031075913400a040c0542044220780c0c407001c00c03614148880d00600c01d00c96280c1d0721400480b080d1480031400406403504040118500909030f400e003c0d0b180d1081161070043d541c0e50000b458030300680c03801811440c0241c100701c0706c81c402e44d1041d18140308440302c00b600034a01d003c020a21103406412401d401c9041125038082e960380381e04042c500d8652072840244151508840d040410644901843c040c0380180c06200f00303074001d82c100650300d55001c100500582e20602c02003101901d8188804081d401d00e40589801244595a0324408000000e03030708056040401e5041d071030890111018010501210000d5100091f2440e907625699480c180b2010020b00350810003d6031a100201e4000344005540034042e1525418030f885001000c1c064842c84c1ca080002103901c0746018001c16049c114 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 886814397 1250 886813147 886813153
    0x3030c040515040518070815181e090d170c0403080a020c0d062a050d0b010e030d030c0f0914120c090103031112120609060a0e01090b1e03 61
    0x10030142001000c41e001140ca1a144008003c04501c5458a001444550690003080d401505000c1400b800b400401001441100300721202003115a407500348010301218044c545036081c0d113030030701021710280034003841d01082d00d00d00f010b0002c1540001010340d000701490340c1d00490005012010000640140c92081201c0d005003c01d00100d10803500a201c1d0910300d004032050020b0580118a00f0540524155a21950341d80c03500c4e5094180a002c181804209026102c02e0700c00034400b80c514043c070801042c004d03503982e0b070790200b0740d001d0319688241c10001411254208080c00c0c004020b8207890120b10000303070704200c0e01c0801c18014000c80e4166045801a817022001716020301034040014170b40d001961080702e81c6c0d91403e80b1084030442c0614000d0343ca0300040c07d05d841c5840c4ca81000910442504d0b6010421464a20002d042039600683c04031111005900c4000000e441e480391034000b202c0c034500ca03000029440b00158082460010113962440d440d02400043c034811052407108150550 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 886815647 1250 886814397 886814399
    0x3090307230105091305010f050a14030d050a031d030d0c0c080a030c0c061503030801230f06040b1902010614060a0c03180e011a030403021f060e0a0c090803030c04 72
    0x50300610150081350005001c0c241c1800140c0d030144141c881c03c2c2d01c50399060422030418072540c00d240030440040c0041c3e07842d02d80020501000700e5696803c03022007a04004011078107001291080d00628110700c40c0051400380c01d4441c1041d2904d99001c0174000083d1858900316010b074900400c60410216001140542010b01e4898140d003d001caa13a2501c0030071004205040004540b40b107603c1c1d5056240200b00b403414250306c5c1c082c1c8000c0060b080707030303170702100c00c0603110302100c1039400c1803042420540d40700440e0801d08000c9000790007582c000003050b200108500e030382a4045902c02884100aa0092040d295200b40b000c030310180410f0300d51b41020042102da1003040c0106001010507210745000407024103000c401001d06009900600304842c1d402c8010403480a090303a04d0f501c5095100c030914034500700b942e4081e50f1000e0210981c0c007551595600346000c101c6540c0400c2c001c0c080c4081186452910a4001c00148040611280400d0159502050014001041c1d03031154100360081c510341 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 886816897 1250 886815647 886815649
    0x60909020d1502190509130b0a05061608070b160503040c1511070b0c16050d0f0f150c1101142707080102090117090316030512090309030723 62
    0x140240c2c50001990b030b03000c020081c8040e0000c0c1c2070708921030450741c0f11500c2d0405981007200400034401500040c0b414440e6008050b03450b903441c802210310841c1d2517940c498940c4040c10310106400e00c003515919000c14036005202800426511602d83c1460006600c0160501500e450000f907a003e040d00010720310900440b0807800c900c490f09486414610300b008100380c4410300d040344a400184ea40007001c1002a0f003850b0402c410384840e104440c182d0700c500d080030b000c02c1c21018858400b9004e20380191401d82840b8800141c4081d058100d15001c90303007059401c02d5009000140510800a1020924804000010311409005850009494945484206420140283d040d11109019814541e03003060a00d0070045c0c04010075840c0000350320380c0305090024210710817032a00d01c0ba40303943c0c01e0200109510b0100848455401800404100b000c1c54102210180101c2d600b43d0402c4040d64140852400e001015022402d0304804554020751143d04246040c03c0d03402ca440d1098410600e1408a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 886818147 1250 886816897 886816913
    0xa030608071d073609061a160305270f09150f06090a030b01050301051b030a05040305040b07030306261b010507051f0f1a0906032e060909020d 63
    0x190080f90000c10500c0481c583c0050011103004544c8082c04000780401041d022030213104010074216441006200c005070f40340180344102010781440740b02a00000003014083d0301920018100410041141c011000203d40c41100c0c00c50054401c1a443c0c2c0084400d00c2d10000c0c0c42d100f400c41c0034101c030404100805100e4201d100114140e07002c0010b010883d035030344410305004011070142d80760740000d51402050500b181d0000d00010318110110f2030fa1b5010080345400c40746c0010301200009001e503900d08040352980200d812905414030001000828154103800010a0340c4a40c030f150f01c440d640c1210300039559440a00e10400c940c0054207500d0400c40c0110500c1102d11b01810821700d0031810340d54a03414401350305c1c0c0a09260b04042d004006500d81c41c0f01c0c038400c006280500b0818144a1000d8242111001010520910010f00010007549062020b20300f890381805400c1c00a140e00d50400540c2407184804500c0d41e40341500c001070004a50040b10162038014000c2040b11090341c4400342 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 886819397 1250 886818147 886818167
    0x30c040b0f10090504091110020d1d0102030d0e0c09010501180603110f04060f080a090c0e06040912020309090a09020901030206030a14011202010f030b0a0b0706110a030608071d07 79
    0x280f100080b00001d032500c0c0e5000d40c2c10003910603003000080203414030401240c000783e0413000085520480c0c600c00c2c0650851501c0d1104803400e442805400807220040f803840c1308540b03040c01101e09010790103009100c00614824140c0301120000c50300d81e02d5400448230100001e00380400c00741403000c00c0000e18040c0c0e1090f13100000d8907401c949010011007116019a00c203601c440b00007100140302445455000b641250002d00007481031101660303546030711b0810300e424001d042014842c0e00126040e5078841c3d20840540c2e80c8080b62016181c010303400030b03480340c02c8400524000c40fa450002185100c06100700340016030700504000b256401d6409008036500024002c019060b5925030740b1080828100b090390082203848204404800c50b0b1000400d0700c0380b82d4400206050030900407240300e540e04a80b030000c0e280c401c01e042e44c0b168258203000c80a040d008600c0d140d403070f00019a0f01c000c164190005070039582440211411940d03980c540c0080d030304000d82c0d640340d00e50600001c10889841802095 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 886820647 1250 886819397 886819429
    0x10e06150f090d170a1209030806040e030c01050a0501050307090e151f0e01051c11121501080d030c1409011d0306070e190e0105040522050a02030c040b0f 68
    0x1020314166501c1240244421400a144c01c2001c101d21020302d50014020007114a00c110600c10700c05203a901070700380710011b40120311468075100c1711f880806041080d6003000000d0b00023400725040c1080d486005140c207004060090054200100d1341b104a4000c2000b00c640001c01842c003010310100c1184899005001c4208244880100080e0484000003580140100d00b02110300341d4505070400414800a02481482507000c40c0051b000c0b810b00340c0e13103411460b0700342d175018900c640883e550340c10719100a55035280b5074182000840c0e50391000805810f8592903460030003d44a2112003a6800c032072001c0304d4141e003c010030500840d54844d03000c0c3c110b06d010380745000e60028000800a42400001c50f45000000c030005502d241a02d42001c0c1050038403110040341202c9418031001c00c1c442481406200c4c0103689440100722032030940220010000109641144020014584680c440711304071001c0e8402d1160640d41940e91805100d2543c1c1600e00904d0010402d5840d4144850404824200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 886821897 1250 886820647 886820659
    0xa0501110325020604060e1c150c180608010e0f09030a0c0303021315080c0301060c140a020918010e0102031302040903090801110c01050a05042d1a010e06150f09 71
    0x204016101c044c082c002402564554102d101c01a8061100861400b0b10010140d000e00c560320b40170840035191036942074824080442c0001040e04152280c0500020100035401008400242d6541c0b0644450581d0040041502d02e41c03180c041500748140c042d1402c40f1590002c025a8150302c0c022642d20345420300c6800e015051220002440e00800426440382210b522000b0381c040025503c24406130f03000c503403010581d00f554100a0000c203c52102d81006024550200f010200c418003000310300c00032a8014036018035031404211034401c0388940c130b04a400560070044003040104040c000c2e030703200f0a03a061a1100103d000e408001c0036150710700c000d42c140441c0e0040860070030020300030350b0761084184000a40e100303d13500d001c5003103c000510740c08185150405010000700d00c0c2043c0900b03c218030150110184084075400c0401d80010b50003400d4020600740c1310500c1030a03140943c120b0703541c130451740d825513145802e101c10414803110a402000d01002009072840b450303000b42030031305406884 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 886823147 1250 886821897 886821967
    0x1101020909163b040c050301060309081605150f01210f0b0a0518010204180e1501081506011b0210230c0705010921151a0a05011103 58
    0x10180d03400300c4008108040d0308400f0101c0c0807200c81201d0810b5a803c00d0341c00b04032108200200501d10b01060144c07104050311100384a060007020019285c41c1c503290300d0b0710b29410401d8035006584034060307003200f60030010000005181400391003806040b0368012150101c0214400c100c00c42400144400700c4501c0701509801c2c2c04120040281c80c8603444850300021582010318080000580c22003224104d07170700410082c88892020351001040389014580810300302c103030200b03003410904094903503c50340c40c080c40006110720000034818901408041c582d180c6d80c94102c011030f801006a032103044140100b43c48000141005030990941c000e0740e24002c14012102c480d1800d40324580700d8404142c150105003256041c0040c44003200400b400d003003e040d00c0b03181c0702c0c00c604507120752107520340c054080b242500240584060f40c0d0802058046041098401500c040082d00f091350b00d1a50040280c100040b441d035000e5001d00c1c64400080c0021070900141d1040300740f5425103403681031035003006210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 886824397 1250 886823147 886823177
    0x14011d040f05010c03050f0a060605180d020d03020c0a1d04030f1101060303090f1e0303050711060a1211040b0d0203150612090f010c0e06130e0a0c110102090916 71
    0x403840c165070356136550100e590308003250002100d07100034103400344151800100b04a500e8006040b44c92010007541c0300052010301e040014400c04000c0c0340030f0340140ba0500e80200701940881c18400d0740344100c42d0a84042e4942c44a130b0740b0001c2d1400041c0d640140c2c10081030219018622078a1440349601d080064802c1819206080d01c0b81e5a000300d0209141100610900340310310415405451103c507140803034401186944895006440040c0a01400040117418050141251410740401a08680c4d4603049400300401028501c80d401c000c09241c000c00d000d440311804103c3d01180c000d080000d0800307030741c54070704802540094040d060482c2d84502e00c0201d501c455000d03046242c1d00c0c1e0068075441c80d12040880c05c201c29118460826450142440002c5400040d0065040c3c41620813903210142c1040180915000d6001446c07003020140821000e840d10b6041800100340c99903039140e02081c50207402c0c0c280d0083c502e0041d4401580c0c03000441058844100c810105c4440c83c00510b001c0d81e4807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 886825647 1250 886824397 886824401
    0x902040f06140306071b0302030c03041523030a020d0f060e1e060102030f03041a0a020903010b0607020a0b07021c0f0b1f0306111b010b0414011d040f0501 68
    0x30304003800c0c46841d11810020712000b042c2d100550342059001c0c1c0240c0ca044280103003108410140d100c0340c8600036020509041c400c10a6413a0982000e0860ba41e031500c541380f0b5109118120054400200e00520f4080e1440c0074165440c980d400b07038140d0324210b4850b48a828080d400107200c6a0509503107540010f0001d00758029140100303940c04400b00b640c1800ca00604101707042c02209401ca0b081e860500000da640041101c040c0201c10f5000c507120340365494000e4003441020100c0000403208020300050308041d40c002c1100a4045008000d40c0c0490014840540070f861030281d801400c0c0001007001141c1030004024451006101c084034003060060071204201c1c2d002c05135100344d0002075003010062403c44a9400c59004480780d5090002458500c004400c4c41c00000c10658481540c4808907568401b903804c02c26400c0440d030b000c03403408810540240300501080380b16070b08084003620700c90201900709040e50203801034544003682d0b55415410000c801382040762940c2e603480c40388021070003c8c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 886826897 1250 886825647 886825661
    0x1403130821060d0c03060903030e1c0336031b110414010806041209052206050405090a170708040b12060907020304030f020a03060c02030c0105090106050a05040f090204 74
    0x41c804615411003242200d40d072001004000303600852003505800d011901006843c01165800000031600d0b030740b1454214003038800314176a10801d205030030f0404004641e02510b9140f07800203a0741008005e146101603011899003c0800c210700341c05140c2000840540c0c0c0a40000600a00b0002a480c081c0684000510000c002c10358501e014a090111685094010034040000c01d00440701c01d54101001c03d5203814016000034418011000e40160660044041e0802084000c10f130081c4ad080c415014500e480e44491070108180c680940490305103894800c242c015507030503009040780d1980c1d51f10040074140c0540f0000c0d020b80c0900c03520000411003030080c405001200340683c0c03603a880080301c0e0304050019140718456018203042089084c0d00201327580c100c0303402c12040003c40005002094049010ba080940400e04000c0b10003240f80d00000100840c00c3c400c0300030409035640da004242200c48038055180c0c0045101c0040003e0b02c0c0603007004c005c0140384100081d035446035900003001c464074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 886828147 1250 886826897 886826917
    0x20f0c2b1b0801150e27011e05091603080d15060504150309021e0d06020f0c1b0120100606031a0607021003020313060501090b1203070314031308 64
    0x1049414400b1072400e0080c0d0038480486071424400c5030518070003010751000240030300b0440c45c0c00303000740d20001007580c81c203007a580d4054000c10015140c450041d000c800150103505000d800d05020858071800002c003601d480f40303803183d050f81450650b9684181ca44c8104401050300d6200c001d241c42da2001e108403034004013565210141d69518000c0b103604901c551344040c505051604020700301507160180c022400390316909454040d4001200014500c150f0351402524140c03004c40d01d200e400031b01c0c00040c07000c1030b021012941c0c84440c5001c01c52840a5880e110790000d4222440c40d00c040318206403a00c2540700050603589851480191039007107030707000d5200b0300000c1d4031400034090042d80d140f0f2401500705c0640c1e42914110954022640c2124111485002c0580c0040014403021458110b1780341c0301c0d8032120030311581d6903d004500c0900040b10140e84182c040c1080300300009000012114040d0f4545c81c0c1c1c489242800c408940f8030781008002803c1c2c001c0340f0700e0758030000d203640d0014611189 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 886829397 1250 886828147 886828193
    0x503122d011a2b06030f060b0406080f0307030305040614090610060f0507350705120306031506061603090e1012060506041b030c020f0c2b 61
    0x71501c0350540440e614450082c2224808204803600c03180c0441031990090403100303940e07040c0846080000001e0103c0d90000d840b40311192240b02c20414903402207031855004a50a01a55031078200f52078a5594040f2400041d510400890b000240170f40c000c680c1c00380c06900c00107412032905480184285048a01000ca90080c2082003050070049403948090501ca00e00320782a240c800c0c030b01501c0f91240040251a021403210321101619036a48d00f040807102c10f0a50f10780681031503074102c195400c900b0040f11a40503145004c0c034408c0c10001035038801c1800034010480c074603410001d1209840c01800c055006a420405041a6455540d210922502c240c3d900007229141140c1c072985010060090340c240b08143c0c00810106958414046010f500a0400a100d4642c038001a0040c41401d0301080210420195030341c6481e01940310708440c810390303001d84000842029209032682c0c0c000d05d0013540103511036450700300d030140380b410918000035407400031408154544943c00700b18440214404112 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 886830647 1250 886829397 886829399
    0x909091c020706051b010e030403140708210a232512050a0903060c110105070c330e070302131b0f0c0c0e01170a0503122d01 55
    0x208105020102108452002e04201c1d410084002d000707124402c20400152104000030414034070070343c800306121400c60f080f255125500e251094501d0700c00c80a0120a004105c00014420400305001078245010703055030006140201c11001150802000d03081001340c0224110040202001c01c0500500c140c00c4454590070540b6400d184001701c00a100301651403580d4100001e070403249040005113003400e000381c0381c0ba4032104c11104400507078800b9011604140c80300c07440d0f582201066001070b003250000c0c0016035a00e0703415038070504920340003010762086043c071400c00c280c0d10200c440002405951101e540621980440a9807000403013155260442c080400840c0b030115942c058000369200f0501554203052400b50305007044034176a105005041d040341240d130744100703095104264081021110951a080c010314148400d004001c14107045030460f1042d00b030f0000d01c501095500034002e515140040961610b0010040e261740d2082c01c01090301054010f0b20000c000000080c101860515 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 886831897 1250 886830647 886830673
    0x6050714070e10210303090222060f09020a020705150d050c0405010206090a03021504020a091a030d020c0a090b060c1504050d030b010e0d0c0f0f03061508060403030b0402090909 78
    0xc00056000040010f43d15844425031400d00a410004d10f801d030600158004d01d6002103100e00d0700c0c08480340d0100300058400e040554282c0c2c0400161a5001e1003080b44a494059020491042020a0015a0012804000c0352504840ca04a8031140c94107460420214802c8281900d0081c2d4070040c009401240074046035904000e466800140c010041c445412035440282d21180718000707030041c1c50601c40c0090700795142e0901820003005e080c0303401c210083d05070300b0b449041100c01c1c0302a0f119028640340394a86520004000e02c0120f00140039040181c03804407103e00401300c000809802c0300c01480f5010b0542021300626a04044880f50400705103058544242010707002c6200c01c06241c90240c10909599001a541808003025215800d541c1a18208801c543c1129030010808091040001c20164850358001c1d0841e4030502e41130000d80203d94451400c410a400b031418030303500283c0043c01280c400c0d0401c0042c10400b8200601d8602c1001c0170030703901d82c8221200c500d40e074401da080f0b01c0c107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 886833147 1250 886831897 886831921
    0x309050f061e0901060308031f1413050a0e031314151815130e06030a0b0606030403090902180108060a03260904090308040203060f010f06050714070e 66
    0x10035049401070182440d10650301140126455409440c600c0042c1c0054582c0c0b500758041e402950308840d0040e1030385001c04089880c00e800035407c100c410300700d440004000900a840c0c89840710010100d4115107287d0241c2c20040100a1180514903101d21389064400030500003000408424216888001d0920030700034154444542d0a0b4000d480ea010a0998a40c800050f9003c560b11000641414080480062041444c2080c01082900006110010000d0a00c40c05d4111101e0003081045580c4500400d0340301d255038840580600c0c6e24200241d47c52422100855201d44642045800b103500c0b200054201c1e0040b0900000703058100e40365001030f41e0000b02141d8001004c44411201c40e041d50b6072242e0b8003c2040d01d0b45689025042c50b010f01c8541e903815500001e101030800c0110501c3e60a00800c58403056800b45d000340240c801140c464581c50b2011410b07180d200003c008020f1410100f00c400d94842c00f800d5991210204001211140a111000080c815114201c015041c90341030822 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 886834397 1250 886833147 886833163
    0x60f07032a050c150103050a02010503040302010f05090601260c09040f0b010605090a0801020a020a0b07050c010e0307060b10020706080a110a020c01020c011706040e0a0215070606060c02011e030f0606030905 91
    0x2560f002c1020040000510001d0308d040304650a180041d1207844501c0c090f0b000d407500652400350303541800c00f00b003624400010003504a5035955285101c01601e01c0c0d21011400e050035000400d6004880e41a8840c14118055078005121b04841e0b0024401a1125428240d0a030402c000041c000a050045032400c1c080403005045000002c602c0d22968550180d5200070081c03004126070408000120454010004d880c1e00c0b0310404000c3c0314042d009400c05441c4d6129660441301581340c20414452420402c91241980b503468005240c45418944190b5202d10000c005460303041c2c4031142490031000e688081c02100000390020b28a80a40c2c50000e03050204426405040115440400d81e58a00c102030300740c0c000700b09a0b000a0312420903400c05062800c2900041e4010000e014030403880d00a4400030021680142810848140c4881c01200c0401d201c007406800561056549035444284042566800c1643c0c28002158502c411074002035501592141010075650007150341403040c288980700e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 886835647 1250 886834397 886834423
    0x305070201140708040311030d0e030913021e0702031603060c08091c080c1603020a0b1308040302130603020411071b06081614040308040314060f07032a050c 69
    0x15200307140a901c004c20882004202404104111440d01090402071046a401c0e16800c20180601c0c9404420310307599600c1003140500070b82c500e01030304554001510a9070101b44a494000410f01c4c103161400c2d1441c0c10034602a83d05001d00780b0786c42c0030b440c14100c45000542c800c0e04040348000b03844101030700c10b1100038603c842a070001c0785aa0300807900c00c07192074660741c11030078a0052911460080700040c001c01c034468440d448030402d4682819000500d00b03603454880e80c0440065075130304444800d076049001d00200101c50a00040c1b00500e0000120800d02140704000518942e807900060243c2d103440e00f10a240680010304842070211b4024200f100d000b0a104107041c1034540000200303176500c000c000045c0c81200a56601e0114420f440d81843c1d00000180942c8036a01c81c207003510f0540c4244002c40d4050081d800f22035001c04045651380c820012142080e1142d03640201c280c01800d0300b0884a401c02c10000d81e680a081e10700082828040c20340da4032151903610b42c68140d481c16081c0400300d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 886836897 1250 886835647 886835681
    0x71101030c0c032a05030307080f09010204050d02040b060705010c03020903010c0504030c0e04051f0204090c080615090a0308030109150e1306020a050405062d07020114030709050904030305070201 86
    0x109030007007000000d02c550794104e590203801a900c49809940d0709a0014403502001040c042d101d64065401c40c0203981404405800f0380702e5426035400c0388900d10441307400c9101146500c0241c9010b9000c11750050010b45a0b525080381560342501310351402e0303540c00120380d000c60080080d040911803910f034040603042c480c3c9842d046442d0700c88102c0d41880360300c960071340540009003000801c0c0502c61460318070f00581030030300400d0369241019400030f000b0040e00320310b400b00d40a6030a01c03940b005409a040603000000c0307070307840355648d2000741e1003070f80401c0c0c011892103c00000149028002e600805240100280040d040d55864035140ca0541c050041700c4030600900c200031080c20741e10800c0a41c000c0005035110700c1030405841d18004c40d4803c2d81e02c080c000c0f440316603801741d86020418220b00403002d2242541410140e0b011030040301e0020703002a10901d298230480c0590b1005641041e02403c00c031f00030035560b00000d00042e808880440010b0b445505201ca0789409000300b90b404040385060f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 886838147 1250 886836897 886836917
    0x507060c0506040b0403021518060c07120e04060f09021c09050d05031e010608040311010608100f1b05070521120a090c06020307050c04050606120912071101030c 71
    0x60076599032070142c809440c408010010404141c000c0080031445111107a1004443c81c5c281d180f203440342c0346800818000e010381000669440d2103c4202c2d4035860740550884041d62555804480e04800702c41100e0b0819034664000c5a40b07032200340315000418011001507078801e007030f011448180b1003038118a0116810b00d195000001d4020480300c180401c0c600c0d22984079034480c4409242e01d80240f070321082c8000d03c08008030b04140d004a00e144100d000343c030740c0c0482c006a0740015080341d0301c40c0700d001e9140e00601c95081061825401c81e89038110320b910041040040620b003242d00001e210844000710b000003035a101001400e000310043d1200f00402c041e00140d08000c0c80f14144a8105101844141d03100050b0b00d244156000c180c2d002c2c0c00c41c2c04051740700e8440001a40e681d00200c2d080e5290304c81e08080c0701181c40d2901070184140c4001e0a110f08107208011034044015014200b10f009004804c070001c1a1240741002d083d010340160300c44400c40d44014009422512000300c1c607010050b01280b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 886839397 1250 886838147 886838153
    0xb0402180a38011d0a1203031b2001020d0c020309011209020a0501030b040f0906020d1805030d0c020f06090a0b090a0b0402060c1e060405070b0c1f0207060e0a0507060c 74
    0x40260b00c1c4030080c04c04140c06608052400d164080125440d98004c01d0940041408219490340d00e24075071298400700f184e01101000c00440362401091100020302c04400380715104080c0d100d045114030341b2400582071103420302ca01d800342c41d03801c4904030050340046800f48003036a20036505000500742c840e0400c46c0e00741603004074581025a001d654181511281086515116640449101000758104116112a518292029501c44c6d903910340d020703082801001228044000b02c60400703a0040040d40780803c4d01c40c0d41c00103001602045401e5001c0c6104845d42c030394050010602c0740c10381d140034091120407032900e000e0b58000548049078a80c4007001c00c50001d0405014644c000340c0403a4110385810780340007914600885000c83e0810145000f1600a0710341d030024800c3d004a200c0d5059034030349a1240c42900c843e0050a544859a5000150601107810720300a0a451840602009880c02c8515103442050740c1d8414181d103507960090801c1c41c180803040c0050030182c500c0345400030003140952 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 886840647 1250 886839397 886839491
    0x2090726011509120803160c06020c10050c120105040c03060503060117010c0906020a030e06040b0d0608060f1b070c05100f1d06040b160f050703030212070b040b0402180a 75
    0x704800e86407154991680d02050041d8048c000c01c50b4009010355a41c40400700450329650504a110310050420003c10424001d684c1960100912010500498be02c0d1804104c0078001c4001400207241c0c1d50a00440d80741c60030301619018181c00101002c401c100380d4034075421240c082155104000f1000f0381448259800304129207103e805280030544062198001400340c4240d5004182c07900002606000e03182140c1c0010040b11280400d64500780c1e00c00c80982403420f0200d81040100c0140d9040609440082d80074041c0319005004080c1c01c0c1351950023054481c030802c01b60401151150000110040e480703216214140d050004100449031440080b550b54000c41c02211401d90300424840b85082100d03c48143d16500b01d85824070156003800c0c00c984400c030f107020640c01401408001000e00900404076102c86900c404410f005a68640322030009080c00b400807a441240b11648100c5907440040b524001c2c1c03918a0005041c1200c01c58002102d1203804079901d4140050225088c141c1c0c0c0c3e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 886841897 1250 886840647 886840651
    0x22e1b0e060a0c0308071106070c110d0203150c0903061905160f050a1206260c180601020123100e06093d0303140702090726011509120803 61
    0x250a0000803511b400e00141d40d040b80d22031080c031442c8140010030401b1036204000d80811805040500c010058001c20b20114449080740a90943d100c4d081440d219640500d240b580004080913140c20310070154002070608905941141c9000d050000a4241d02d031203105981d0051158a40e078440e454035580046c0804440010800900030701042042101d409a0420382d0794031088081000f08a8032a00c0380f1091a51580d208203985c10204107031841d030400043d80518102d17004045c0f0746034403450303115405501d1004000904654844105506c9031030072000030f221507c0c02500f80e081a14040c40c0b801803c4000b54065010305280d00148446038581203c215004010041d80b02000b07050340700d404c0308130b1176034000020500e40b1240d40e02e50809000d03456442035034420390300e500103008803100720316403401000d40113544a80c0078400b20b18180d024a580301104a0307451244d41581070395400e104500c1500740e00903251450010b41030321409900c8043d8501500292003085590354843e00c070b10140c0d000c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 886843147 1250 886841897 886841903
    0x30f0c0903060b03070801090804471606061e050d1118010617010f030201120f1e020c060f04050303040f150614010e01090501022e1b0e060a0c 63
    0x141d6a514000ca131818840380c030240c01003600902080c00c82e840c1500d070356800380c070a602071080f00c2514090364021070015114000044a02c500c1c04400d070309040d1b906000c0c42d200400984104012841c0301c8200285d190f040c980c095400001c0d498980310400f85458150b81004850f0300003441c0c244072580d0341402403810346400014240005548601060300410a042e9042000d460f580000490540c40481401c0310f00340040b41d0892030342d035520b07075003070480c07807800003d012070b005400850b1607400b0350b801b00214804444001c0b50a014090084040d4003000807140340c4103800042c2400203107010801150801000d200c213075054609510785944900015200178294a4a10410800c5c400c40584030011454001010814103a03103131f090000011b10241e4180c0440c5038140884469030203071114008070b07030040e00034140346001f450505180d043d82c20004054403100c40054000020303a031060070120117011541c2203402160380303805401c22001260307180c4248030400ca440c0c15140c0c8512028000e640c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 886844397 1250 886843147 886843151
    0xb03370f1e11090301020412030906020105041223042d05010c141c0804050c0108040203100b0145080703020d0807051b0a06030e12031e0f07030f0c090306 68
    0x35403001405101c1c403e05481075030640c008100403d404940e103140c100070611a480d02c080c120f5851205900365103049501800100e4818000c0071003a018401d0508004244c1c9150b030010f104006124801d40c005405c241d940580b400301e0b80103c28185102c1a80030b400881000079451303d8613000810180c6181c6c80245011080c0c1030700920312504024039038159010325005460420800001465540100c8094816203c0c010102c0c10550044654a003d207030098050440c102c0b0074104003024003000c0b8100c60400480d42c01d00304d90361010f030244000390074405110340104025049100ca401208951140315544c03544400c0096100015084044a6040d6a0b4034103d00050501904a0041e000d001c0d009000da8524207403050040201c202d902d04003280c0002120f51500703070480450304070343c65000e250361281d04004031044088003e56445003051b0041006c0b401d1495128464100070f8a0902280c2e08a80a20000729014041c0c0030010650520420804102031001031100140e440040c3c0403136 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 886845647 1250 886844397 886844411
    0x24061003151508061f080619030512070b06090c04030f0303142a0f04050415120b061309051506120706021b0108010e010b03370f1e 58
    0x15207200d06000181200844181d2080141402521031001224994401c074008103203080c85488104240c6401d841680c0c2d0100d40f036899005000c4a403549600b11102e0340f03401000080050403c10005070424640702e04240c85040900c0c1841d94804041e112501c180c1c0f01c0f0007000307811280c400c185e138100ca400c1565540d91102ca401c00742c00030182d150304000c0d100482000c0200c03182907648904001c1801d49110b504508245010741c10760302428514000220080104000c02d1400b5080800101c60320400440f10301d6035544402c000301c1480d5421240708018070100401840c01c0c20507800900e00440060004010a42c0c403551038030032010820f000509142d001c12035171740b02d440d074184001c0c810404a034141a26250b000e9540d6403003900c140301c24a04696059030344d500c01c01c500f50482d40d000e46900d850740d080059102c40d9820051484201685c280e2035204501030603c188040c2c0c0107413264066501e81454100002c0d514902c003c002058105996104184e07506510000002040580000e4107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 886846897 1250 886845647 886845671
    0x902210f0c070c0e01080a03090e1e0402040b0429060703050d021b0d0302040f050a0509060d051f06140306010b0919051203040f150203030103031407060c0224061003 73
    0xf038590413403203242c0309020022a844100080800006020361228030900e40e81d0080003910301c4044a205000c0c100a0042c0f5410f400f40302c1e84141c22510060020a00d00c1c1014040380c1100c8600144a444203111066004d4007840d500c08040c01039015100c403454548640c8020348144a0855070804095000525a1155000403070505039460003c098401e07045c0e4050340107001e9000f070f008401d0591100040007030140f401d009614203e450240403050383c1e54034441004038045008505407080d00a6000880c00040d48801d00040e060610070009074250601b440042e00403123240c81c0c18001e42c030071001070103404501400d8409043c1d0481e37452174103c44040301071804c0001d65008980140c02100c07c002e103a40044040c00075034042c60140004941c4da1521892003140002040015820420040c00468860b0312046c1d1601035a80c0c003a40b410340c83e559118202c590444907600140c12400340004400d01c80901c0b4510020580250a01c9041180c00540e141c0071001c1188107041d550079100d0b5131 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 886848147 1250 886846897 886846913
    0x6220e130b06010e0a0605031005040207120f26010f0501050a081b04050909070608130f03050708040305060a14070e011b03110d020a0201020c011e0c060e070902210f0c07 75
    0x1404d2000303000401c4542e55000040d00c0742c0c109a441041b41c00d2008800f19a40c01d0a109886007150042c0703400e400d003d0803250030748005c40d1001ca0002000100c2d00c1c00e958140c1e044160110018007017280d1001c80d850f18070095080394403a086241001002c0000d415200d83c0103444580142506032800b01e84800c030945407041e0720460340429004004d440c00c00c14511004a51072044840b6600c4401e101d07170750307105d60020320310003414010f041d04555035a05000c24400d50161905900c42c0041901d0641c603a12014030b03110b012510b040b40240c603285001c42100b0040c482a4100045051a856003089180081c0c5a00c1c0d0a81c11846001100c144c0841814440c184d0070b804d51602c5c40070388500c04e40700100291103842590060b0302611564080c480036511501c1d600100c5d00fa40c00c144644000c40000856942440440587d070440d00c8440e04814081c0a210760b030b00801080200582e2103400c0c40c011480c41900c8014007189501e01c008200407000d0b402090fa602c19030240703200d503864105140c0118 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 886849397 1250 886848147 886848167
    0x10c05160b0606091002030301090b0303040b07060b030a150b01030606030605060909092415151c0608060910052d07020109062d05161b0206220e130b0601 68
    0x98820072170201003480d00c1d000700045040c0c44000100340b14800d01041030503039030b00c02c5120f18080483c082007954085201d0b9402400c01100c0201940e100c030150f40c4521310068080505241460358a400344441903070507126850007007506e414140b10a901d00000500103008600302c241c02022a0390009403520014031511a448004083c0c1808401e80c40d91002d40c04135045582108480080c248240b0601e8003402203403010340d4442c0c40360310740400c2d072950082d030382910000090341646914002c03816060910560f4450400b00f00240110521142c0030000e4640141005034242a00060403280480c1c0b0080b120120301c0e1202c01c22441d0302d8803d0102d004100c20040505418176108110448600c4600910119a01241e4061784001c44005140448000b074400804075030b41c07242207400940c0507003501b642807070f000260740050780002e40103d5081e0380f01e4071035400d4405c4110000b0401c00034000e0f04002030600a100c6c00070710300d400ca0045030500450b040150404424400240d1070340e1041060036 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 886850647 1250 886849397 886849399
    0x60f1e04030f11281b0f0608151c0305130305010b040b0d080304030804030c050d050a03050a0b0d02150d0f050417030403140f0d0903110106080a0201050418060b0c0a0203010c05160b060609 83
    0x42d0031035035030ba61b50005c003515400f58000165901c00491041d00c1c10704200006420000c0445000c039880b0070349020b41c03c1d010042181400003d001c0d0459001c10f6031707500c10085002d44008105001540304100880700c044c405684030703c0c2c0b080300d080049920030041d02d0740994581402001c030f803640e040c1500d6041c504c1318014028840c44c0212604240c0c00350140a440e200c5072414410794407402e201c10196500f4551080d000325401441001628204c450b40c070300000b46002051910301503101810540319000c0b81d8012181d210340a01c41003007003035544841c00031040c01c1424207509180d540109680c02c0b180d031003007a820000c90a00c0c4603201002c2228400c004a102c104030300145031030064287d0344c0343c08a0301c030b180d481d20400007010341c0042203481c00aa4141d45981c41c00c2c1c1080070800150189000c0d030842541d90b6400401c00c4581c1c0002480c10044510007011500c41d107104250035201c0700401082000070600081d540c00d04624541180310350b10941c01b00050b0f4440011404900444083c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 886851897 1250 886850647 886850693
    0x2070b0a141c060504020903100902061606050610020a0302062409040b06090108011b05070507030605040506100f0b07030e120d0320040602060f1e04030f1128 70
    0x6034040c0009001c541124038507404180700084e80e903c1048200d000304071125801d90440c0013038220750345041c0d00080b0401e100900090410704204040c215004031aa0103c400c15a64000e100a40c03822400301107041761184010300400c0d1032640c0003503c46402418504480500c1e248071000e10943c04e16400307500c9009842038000340303010706080040c10350903203119028450180010842c400c0600900c420820f48110040c03c0781891042143e01d0740c40514180c0d480d000d0141c0200000310356014503070040303000300c0041c07840d410011f5104400d80015408003040c4e5060200410902c92088281c0c5c000a406003000f00740311440d500070464401c0300400000349409001c4400d0340654065101d813145404c441c0841c0d004000300c00c00c5075500d1003030340100c1000d80c2c020000981512070f4042200c0d03015140500c00100900108202e2055200941d400c50220b40e03405005d0528030f52102c11854180362180040c4003a080a0182c4c1044484001074041341c3d080b4154034a0501c90910102030005d420304007a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 886853147 1250 886851897 886851907
    0x12020c06191806050f071a0903071b05100e03010f0c0810080a0803040204150312020303061813060c090b0735120712020307030608061602070b0a14 65
    0x801d040001408180d6002c501580d1958a01d07007154003541c1d040d524151146807070030f04e40c001c001c60280c0060000300e0310b800e0608036003800c014480d4040d60040301c6a030001c54803115a4900145208040d030440300c26000d00c41003c120941d107600d04000d00f0130582c20300041d4039100801090142c14400c0c80c0001c000d06180d4107582f03c5910040441c400c5410180c00b10425460b00c0325291a6818000301424250301400813074054a040e911454000c1101c918554413151b5035610120342100d40c0d1180300158001001300540360034400c052034100d4044200260b1a4075040161102c85620254040d0640760b40340f480700d51143c09202c1500243c011414200e031941e07880d1803d41c1040e1481c148448100401a10030081144000050800341d01d10400150400d4200c4d59458001c050041420f4100140b090a03e01221840c4c802540075070b1455a02080060400f29400d192150240910f13081107580300480070440d80c0032a920007036641e54112541d40390b4182c0c0c422036086842407840d000b0a000010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 886854397 1250 886853147 886853167
    0x2a0303030c030209030312040506010902040e0a050a0e0d050406031409030703030504020402041e0812030f180c0d080915030606072a1d070207050d0b090a080c03130e04020d12020c06 80
    0xd11301e03110794815270454410703030b0702c446105085e03000f1403082403404040070700458480c2c2c18a4000381da000305c0138600054200040342c015840c1c51682c020310302c04180300150a01c005036044c06003020450030030808035028105003051582e240714180c3c0240405070303544013040071540c943e011034000300b842080c2440110710f00d80c00100003100d1486404210b04c81c58003034403040421101902d12503000c202d4202140e55483c48180414030301c03000f80c11140d01a80b088030a140d52104c9081403042d00480b6002d8494007000c0c144604079855400c03600902c2401c3c410045940d03034050880e204aa80000c18840f07a1004013160100118081505503648000750f1011030784903c040b0480d078010503ca01125415121450142e848030200c1c080c80307810610f800900340109500c0000c0a030000420300c01c503103614660380c44105ca60303080f820504035241c00000e0141c02e607410708100900a04406005410702d81019030000d052070b1642900104228003880d003501c0f08900920407800c032180e02400061703444810b00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 886855647 1250 886854397 886854427
    0x5120618181005010503060711010f1b0f0e060f13050907050307020d0905130207050f07080c0f01140706110c19020a150f0318140a2a0303030c0302090303 68
    0x401c504145200300c1d2060b00400145010380c41c102c0d0301c090b01074041500e840c0001c0320026140c00740a682c9640342d22003505401310300c0c4a0300310300d07141c4408411701d0b407100c41c08010881b12244914404108420030003400340d82c0c6000c100c0d00250100b20449645505401c0c40b80d1602d0781c01c2d409035500484180810006130b0b0004011481040c01da401daa0620324020402d40d0b101082e070198640000d98410801100d810303d50041842c14003c40890b249007900c07100603071400760203401c0340a00381c00180b102261410b1000080e41c0d80082400c020013a500481659641805203a40c09820389880c0d4031071091140220007112403520414041c0c0700340ca0118401d0380040303001c2d044100d001d1460800002010f84500041d00b080501d0369883e0290aa00800308038041c000c0c14800e500003030580389000d000030740e604c100600c042c0f5034140601150b04d1306003040ba5070022814400514100701d4020000b000e038078021910107680d8107050000e42e40040b850308400034002c00c4051074040c4000140501e04032015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 886856897 1250 886855647 886855681
    0x2511070905060d0b0f0604060e01060534030c03030e12093c101b03120b0a030f050d03090507030305031b0c030715180212160608220305120618 63
    0x1d51f418441283c1c0c6603030280e007009091144c0c400041051202903080e00700303c800c0306803132000c05000782044445410844042000c4600880100b581e1130303100310806405000d00b40c00da40408010b000b0445800020000d60310a1289c414031030754040b4008072400101d104090950982c5141d50310440c0e0703071448196407409a5040b518414020880c00300c140d04c2c49070502075450600e60780808203150196409407081c1d200d10340e5100701c4076201c400710340340b03910348240f290010340c05901c0b103400d05e6806081c202e04010390256000304250810101ca00070034000911103040701d81c9458040c0e925582d42c400c2c00d400140c142a40302c10000001a0100d001a00201a02701a8040c00b0080d40c62802c01e804442110810301d051600004c2d0140d01801501e0000480c55800c40010284c0b0700c20030a0051141450f40c5a8004a0109410105000703c01c00ca80d4411a420030400303504400104c56510060294041c81c43c008441c4400c0300002189511541c00000500000780e2000303500b814003078805141c541c12 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 886858147 1250 886856897 886856899
    0x2a160f050111120a0e010c0f0e130203130b060d1112010b0a0f03201e06040b0a02061b030f0f0a18080a0318020d02040902011103032511070905060d0b0f06 68
    0x1c0044d990b04060b01842481c20487c10340c0c40c2c100300e800e01c8160684060710100c802d603070701c580b802c815026500013500045120b2642d10316247c8161095290884181c038000c2c1121380074281e42025600042d1504040c210308200031a824000e110f07980642c1d5002d0700d079070300365145c02504140e0001500803400324484c0603644900850321a620044604407400326060350b07215880101c1e6401040e4100c050303210017000b5400503020a140c252101903200302580700445000040e0b1116041010300c0b003110003000c4540c203880c90410b1450801c611340551181000c0d21140e1120041404a031000480750b001846540c108452580f441441d410401c1654101460510100f8105070400740804800c00d2080c410a0b0300501c030042c11030441d0248402403a8210040781031007040c00c05004000c2040010358428514042d040c0d06906d0900c3c81100d041b0800d2011030f00f4000c81100042d400000402c000081e68407810b00066141d803a100014000303c524403000d021003e07a201130084841419900da1310800c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 886859397 1250 886858147 886858151
    0x21c1e050307150c1211090d11030106080304060e0112141602071401090b1303020a0b071502070201050316020c04020703050301150f080a0507030902092a160f050111120a 75
    0x1180c0c03c2e4450079030b030070700c1ca0003000904066400d01e90641e031580032550707030840384000c2030400c919000440e41880810f00c09945520780040240d006203801d00440024002410180d4242807800c200901a240344000c4981841014041e8581594040c0d1004865414460078880d040c01c09d900807001c4081c19400c0000107016218010400004a20380c600d1103140607543c039500e00e894900350b070440b50494521002d034640c4810340000582d9481180754094411050707410383e0750340305240600c00f41405000c40c1a8841c01841403401503a001801e603540003020410040d54020007201c100e0030881d101c0d803107070b03800344c80881c0000600d0761050156069501580301110000b070003a0007520f5003116807041e400002c0035400045c103801103c0c0c00a0360000c6140c103002c5240c0c2055400100e0281d03088ad5003241c415090700510240808541e0110360048426080c40d140c6081c003503c484414140800240c58003c0d020030300c40070031109501c1041c40e20041c2c2d9081c0d407211014140101010429501109014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 886860647 1250 886859397 886859423
    0x5060306090a0f060b031f0e06011206180210050c16030b07050f0702040f0e010b3319080103020307091b20011521021c1e050307 57
    0x41000a945030041c0da40a00900b0744489982d00c44991095441c0c046a00b19240c0010041c05e4800b000345501ca01c0c10941880050802e002c907480c01c4888040e9000318640c171032801001060210201c0103150742c0c01c40004036420480f41502c40b038010640030002d4014520a2502a007240e01c14090700342c00c0800f0040d40c401201511020350a000030b40400b800b404105000b0034002c41c00790008103a4070f40341c8141d450800316141c0004048440088802c050982c0711000076071160310a103d80c00c00100e04441d440d2045441c07c1507402c104880f094600c01070f0400003481003000c6c0c1782c5403c0e02c04180c040d01c54000301e0300d48114003c148500a1000302d010744a2603c0110b403101c524006c40c0d40f80840d01c288a001101402400c44030302111a2250101081040f40b07409045000c0c0252040d00030340c1141d02105502d00b1012006800c840d400c7c84960300041d10001c3e0041e076550a410440d000c440b2500d1000500034140110b0000f1042b0801d07580000c505034007010070030f020005c1c101480c003a0882c03604030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 886861897 1250 886860647 886860649
    0x20a021815090f060f0d1a1b0316120605120a0314160201260405010c0f0906080c0a030e0604050106090c050c0619060b0a0914040b01410d0506 63
    0x2ca00769a0301c0c2c0e100200c50000742290600000b82c00c0d0044000302955501c2c0f00c0b546400d4039000d41e01070060003c400320000c1155900c00e10307004402a00507445c04a1031403030940210f019840f9546100000c009100e1000705001801d900020040c04008006121900000480590b45c1c6050720301100410f103014464902d060400017603400206580c0301c20020340025600445100c4110168062a000b4950080d269408003800240c07095200d000005802c100c0414080c0000d014591039030204400c1180c01c0c00f040340e100c03038003c3d0030810145007035071200e00400c8103401a2403110004107681c03140300208000c0c0513054000500f21081000b04109850010760203e5039441a036090785216071040300881d02004003410750708800c50307030341d036001a050b5112600c40740f0542c0070f41d0801e000602100028084058016801c003c41c0e0b000f11010800d41c501c0e6800607060b0001c00030310021083c1c070380005a009001d1003030341100c00b010301c210f43c51000c00c0f003001203542c1d9000f000381c0700c0c4060315010003e20303a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 886863147 1250 886861897 886861909
    0x1801210f1d160f0506040e0c0f030f0603071e0b09030111130603050c0403080324030304140a0b040602070b1305030703060504031206080601120c0905010f0302091506070204020a020a021815 83
    0x1a202d001e0840e40c1b5050928200c105654009440c031042800100315280e41840703da000342d8040c03070305d040c0c00c0c00f50340c1000300401d803030f0413a1034200340a203038000382c2d01d06d403a001d030b400d4524102c076050241107444414034400a40100090040303a0f400c4a400991740f50600e403100da00b001583c00c141c80420190304c07a2b4000c180c140c003035408004c215010401c0402d00d00030018946c001c0058403982d80380d41800801c00030a0841d00719502c0184482032a07a14514103251035540c81d00602181101503007418034108000703580b14128460700005503c0040e010314110120380006000d030402904549402e07070381e403030001c008000c1110140e0000d82d4200d80c20050460701d00070b440c2100c00100c02480185d080000e00f0100080201c421608100002c200150051980c040e407402802c80306207040c00c0ea4914010700000c0c41000340303d08020703803e00f48281a40d603586c5d0259400c541d0143c40068443e07202f000c040c6d24060b00c2145c041e41c04005c903c001706142c40c21006ca00c0c85040b28195600c4d034010004c09002c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 886864397 1250 886863147 886863149
    0x3010303021209030c0411090f1818031e090a0909020904082b0603110d1a040305220816030308040803060301020f030109021801210f1d160f 62
    0x100580189000c0078404180b040a80780011004050f15182152000050100c2d5031409031a4502e04007c5820200c070310300081208032121058800e03c115000401c500303902000003e102240703010302191a240440702c100f05848081c00560306405000f40407850402c425008503040520854071090085054030090007080c00c815809445220a52220340d211940e07074100740c103401510100b000f05d11030402c105100140302c0c0d030600702001030a2801d45c103100d000340c1e100882c11405150445c1c170400004088030040b1540f00400c48c103003407060700ca40c035088440b480380003404483d510418a0004064086158040071036002c0001c88020410112183c1c2c5200700510024001c21503103000a004a610b4000031075100c200200010324121012071100c4240c0c01c2a08174004251b030104150002000039500752110104c2400c02001c2c0038401e210f8080002c64400f4030040b40ca403034215038030311000b643d00804803103042c00450191502621a103d5a0780200d0050300320104109880000c64031400c1c0c403114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 886865647 1250 886864397 886864403
    0x2060708130512031e0d0f200405150a03090204020301082b050a031509111b01140114030c120c031b090c0a141204061d100b01110d05041505030103 65
    0x500b040c9200b01d4880d82c00030b803052400c0e00b0300010005609198010321880030003102c1550000794005c2c40d0b081c00b282c100c940c1d1300d59400040e4100018082b6070b032201500e00c2082d602d6045180e8880341204114081c0c401480000c0d0414004000894082e5003c00c0300c6038206003003002c040710400f070740300740c070140312007000040c80841d904014030200035104c2e0300086400e100c01ca61401794680d54044040443e0f00d040f00070754502e2004910340c040d41d9019400c1c1a06000c1e01c07c02801440c1e48800fa01c090600306105110340710440303220b410f00d20340b818000c00d90080c0780201686111b000d408151511141c004403414400c0c02886644065074020203001054a0005440c8524550b51044607a030658041e034241c205001d1080314000d14140d04030000c00d07400d0980f020180490030a4584141030703901015a620f0840201c01403544d6400d0b00242e8240c0281065101043d40003400d0010f9030400880c0c11030b610709004241c02c40c1c000c4ed0f000401401210010054000c14010380881180d180c0020b000007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 886866897 1250 886865647 886865653
    0x10020d090504110c06010602010c09080c0603012d030620030108070302090c071212060e041a1b030f090f071406130e0910060920070f02060708130512 66
    0xa01203400e09a0220310f107809581c09051811302101c60680c40e01000740d00c1100180c0d10388014101c000d5000328200020100c5800070305414540d0800103800d4041405846200120078030412081c4550059825106031074043d80d403d51500e0b4104000a041c81c50321994424026014210055011700c08490488480c0400381407150704550030001d003c4805080300030400c00c24440000401e200c0c1000b001080c00603110030f078a401110316618282c0b11240d003d030800301400c208200120b81310429801880c5213221003420b032550b0307081c1d074000c0162105426460251010080144140d4880c0070a806041d505084820792208580300c40d0369038080b070050396103c8a0034a025461414400058184d000466101c000c0c200d4403803141c401c07809030031902c550b590380c80808424038481c0f5502c100009031080716420b0100180c0489003078082c0c11642d5000d68440d000050103c14072488680c440022070340108016681c0c0003500701095550070201035403000c0d00201c54001050b180c04c07402004054644405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 886868147 1250 886866897 886866899
    0x1d0103080304050f061003051603031d03160e15030606100305070516030206190c0504060e03030405060f07141b191703180406030f2a030b0610020d09 66
    0x103400c0468001820032520752143c0380ba18140b04c0020f00c0b00a01c942c08095504622a01d941019494480042c15011201104804c2031010a5008240116498481c0c0003888440f003600c000c6407800c0307c440440d912502d1910000b107400404108204d00032480015080030100c204000c250315503c0654085501400d00303501d00c4c0000d4040d070841580403d090420500b801c1014400e650800400e0790200c0041e00040100150002c00c000b040030072002c1650100003083d0040c401403c244103500030030301444800b0215020a070303010003c03180a0309000d080c0c9500e030000c140d070418813030304180001c1f1220300c17948410390010600000e070300a42820004012448000b440f040c0324000d92140340a05400b41000c201194407030245651810f070310b00c0100110b541c0c0364006c078203961008110140e070b48200d0410404001180713002811200041e0404007003a61003a282540320107030388036250110949043c196000003440482c0007610312666040e685090705148254003242c441c15020403807004144a150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 886869397 1250 886868147 886868153
    0x10e0d0f0c060e010203160f020c030607050c070305030438091e12030a0e0f0d0b0702070e09070e090102031905060402040902310807140402041206050f011d0103 71
    0x2101107035000703110001c3c169802e051003509907402101c80500040c001540c60b019a80e000f5114a5100d45500c050803a20050400003900c500c0003400c00003c0001c00f180b500000c4109000b080010340d444000c40ea900c03642d4103410318401040408600000d8155a21004041d16102881400c1622503035030600d032080c0d55041280e110b881c600041110101c61170064082d444000c0c82c102c140845900964951311000300042a040005081a000d1070b883c49000c01d146d114000a002c11310340c001100d07801a07580399800c03890003000d035000400703943c0e6800c1030000003440424043e00743e901b003124500741d69070307008850b500b80c3c44196003640c0c4400c002504101c0f00862503128a4010781c004001525040d9a0080e08e070036601f140000c10040d500c86485201030134032141c604180c124020301d005040707038640442d0782d4030b0f41454402c2c0342891100e0019000e07665119030403903000e02006041414011a01e081c0207009260407900320005580303040005c1020058406030002940d8000c0c41b01e2003aa0940d6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 886870503 1106 886869397 886869407
    0x10020a0b18150a151403150f1b0c010f0b0f0420030709120302011e0213060507020a0f120c0e040c0e0613050702070602010e0d0f 57
    0x140da207801c500003192401c2c45181028040100d5503c0b1105507000c0c22801a00c1c290710007082d02c0101766000070005405d80080140d044900c24590b075080d108064006a48030144030040c00005020000003804c040c00c1d09108001050030b08134860071035401d40380c1c08c00200d003000d516003124074120b0078114078403a401001241c040c01070508204440b4520200c0e200402c5c1d4042c000800a0001c60040c04500c0042c800404c003482d0145190500034001d14080b007500081001400d50310140103580d00030386a0070040143c00400e910301d03007403080d84c20390300217030089030054600341000410600032201c0b2401007812442242d6204424507100381c05244a80124090203144414003011511104007401070311509071007200c0725120080011000c0700000004030b2458207040c20082410b5001c41c03043c0881750250024403103254002c04e02a1104070b200c0c2c043c0e0020720011010b03860741c0d03c55 = true := by decide +kernel

theorem cover : BRFrame.Cov 886690647 886870503 := by
  have h0 := BRFrame.cov_init 886690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 886690647 ≤ n) (h2 : n < 886870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
