-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3759
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:35:52.546991+00:00
-- url     : https://prove2.me/submissions/7ee3408c-6ae5-4952-b283-3f1d57ba316c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 675899280 ≤ n < 676079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 675900530 1250 675899280 675899303
    0x7020f010506042306040e031c1125080c070e040606060c1a04020a0302090f041407050109120809090115021902060301050f0406081b01021213170a0204090f 69
    0x43d203094003559031030140c0f100b107030500d0120710340c08100061401003140781c0160311064400a00070040009003000e0000c1303414084c00f11030817005c0c2020344100d00b502d11551b84050010440d005003d25000c10411102c005010615025103801c085a0003200c1e085041d600501400083d204a49105144074030701c00d1404010040e1500000d136440e4038908406060407401c0c44080f490100d01c00d00704c41d000760000f0314101d003203592580081c07502c1c20101e452911122400c3d05001c03c102840c21040d5a000300c40001e08541810507000800800e238920075400140c1c3c0c2e4500304404e115500e030884000c0e00c1c3c05012034200b0740c6c407002c0008100d0611030741d035801031049625400e01d0002140c00180580d500510301d40c5180d00c0d10f81082030344844d1038025071f40556900700010785494104103625031507009440c250418606003001a041800c0003c03031002c12842005201410a408a42d0708161003603410104540d500030311805103042000800250030500e02440702003400385800c1c81224442c4280143d101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 675901780 1250 675900530 675900541
    0x40b0a091e051501051309051905150102030315040f150303080703020406140903031c0e330403020f06430320030a060503010e0d08040f0c090507020f0105 68
    0xb1141d0803901030a0741401c005000250703601c40c0004210f80260140c00346101602c9400241c00c551090310030070380d01e007084219100c45d04402d010303082c0d01c00c0090b03594250344184000084d440e8800100112160601205803e030350b50380e40d0348078028070b003211082004111210441000003640c80d00042e03001c0759605d000194900e21900131201aa0402c5c0d440200d040309426404d10503410594000354140018017170110b4001b80115260380c1c1c3c043c85a00481c0c9106581c480e18240b0780301c0c2e0107800c80c80440a441c5000c0c403d20440c41070940302c4601d112402a030342c038101207050881c8200c000459005100070b0019a0020841408084100c0f5070030030000e0b40751118061140c3c952038400402444182c1d46a0744040c002d030320200050002000b03100b00d4181d00092500303690700c102c92000c00c0b15580d550a00032820240308050444081c1030007440c80004258000d80200c400810040021040d40d80d81d104000f03409900e04000c010f0003a0511040c201342c03c0c0613440342d45071038a504880d842d0400258 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 675903030 1250 675901780 675901841
    0x302011103271f180609080a170910020a030207210b09010e160f060219110303040e090a2d060b0f060f0406090e160e040b0a09 56
    0xd5008051240b158103140e81455100200d248440e18503602c10000ca440186040d8003c0155000c0c0016960385882c40c1030030050390b00002d001d42c101104010058000b4482100c0000d400c40700345400c104144201d00204881c1d1369580300e82c7c4000b54000c10300d104445469a0001110b00c040c41c446e40a0701d900649481c41344220811091043d41010b0010401c2008070302c00d583d8482e0001c50000012803103d202500d003902e0210900c41040c50f44030306820800c401510031495030058102d070720103800e0001c0d840e42d505104190002014000009040e0307200c140355400c001b280c0041080a0500c000b503d0094003840d25080400010759503503400010f119109640900e40400072100044030030002d8403252103440003090501d401030782043e03041048000311354800010300303c604140580c0e50703078075424918000d200aaa80d401600000c541d82d080c403950241c0303c0c451005d011140e01c1d103014191240d50004003c0c051085900c3c0d000500342001107451866134010151007100f520200c02081041003006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 675904280 1250 675903030 675903037
    0x609040c050d14150d141f050c0405221503030c060b0a0308190e090103080309070603050405030a110c120102130e060303030109111b030d0608030a091505040e0c040302011103 77
    0x71101300c42c10743c0081481c3c0c070b80ba20f0700e5622940540e0701a0f4000d462180301c0c0e4070b4907079140344a012000e43e04124980840d220b008a40e8007000300b01000c0d04061500e000710382c40081040f0000c51041c20341c40d00595002c0e00b035010f042c103e810700c901464030603602d00b4007411441080c001a9011410444c00c40c00600f4880000701c110303540301e14024a0410f034141c02000000d510400f010410881d0032242405a490301c0626001e98002c08540d07699044c00c040d130368505942075100314140350414003044080381000c0165501440a81032846a1030b0395481070a040c20301c42202598440c00c2e1034103540521405501801c00d030181540c80101e03854071540b203a4004201110483d40c50b0740200010f0001c903440b038101c0342c87c05e140c00c440c1c9070a10941d4459400c40e00082d000481e40b5501c0462004090ba10740e0050200418149024504d489096540140b0101490040c0d410b010340500703450b22018862001c540c020300710250000300034207191410301e896a016120503800075030280901120608080b007203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 675905530 1250 675904280 675904291
    0x6090b01080402010302090d1a06010e03070305071520100c030618020f0f0f1e0a05031605040f060c050c0a0503060103060c1e03050412051e090609040c050d14 70
    0xd0100d03070b968907401140a5404884c400e60015144070101d0b0004207403c22080c190107010200080c2c0703241c900300061240c5407030f100d11032081c0e000c15410000b08001280c120180e0b03d802e1480075a4010107002900d182810000040c3e1200012603414034000c400710b881a100580780e03000f8801c2d604c0541c4110103031140f500449202484a0094a174140d101d5801007810300c403c1c0015608242d184c2a401c00c03260405a140c404083c400140c0054040c8116180740e810f003402c25440c0e04009490400421901000b48989821110718901543c014015001d8030700400c40d5541104a00b84c680c60001e103803a414010450700d41c4200c03894809140b90001804068401c0070b002031065070b2954958901a00c40f10300e01c441400000d0300c0a6845440f510000c11f0741c102180c80c04541818249400e9002807094403c0c0340421400340314107296078000c003810b090200c0c54000303015152605040012518410100070b00c1d8002d02c0e25185030403080d0000041c0440307600d242410080d104a4041c24441074508866 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 675906780 1250 675905530 675905537
    0xa0224040c151b060b0402030c0d05010509040b070e030c0a0602012c030708030c2526030106030b061309050106080c09030703081c050a0204091a0f010f020a0501021c06090b01 77
    0x240f0303400050036041154072090107094013192442c2d030070300410300304c1e8000d441000560000142d92445181c0781d0107068018441591004800c2c03034140c031a10150300c400381110040090880e155602e9039020401c02d851404000d1039440c1240d40d400b00a07008084078400501070f080011040040b2801e440c004001d00003c003000b540c90b01c0c84030b564004843c0d000030a1044080702c180100d00c004518084501c1c1c003030102809181c03007200681040900c543c0520102c010b54030200201603c1d0b02038400569044400d40c0c200451400c44020010700b8a0051003041038210b184610009100300c215088a41207545035115401207848800a40000740310700200711740c050744481c0c42000050101c20003009540031101000f202d042c4160380304004d0710405e80381ca88126030042014004010036100d12030070b6202c00760105400300310f81c01c0498401c403418400f4505010b5950801c442c00ca00038080c0340c107400d03032080c021540e503200c24081d10122200090b180300010318100c00441e000002d8030030348800020584 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 675908030 1250 675906780 675906797
    0x315011d040504032c0108090a0c290c0607080f01030b04150b0409050703111e040525021b040207030206190b060409020405090c070b0c0a0224040c15 66
    0x30107000c05404041e201310304000c0c00212200e00344040842c0076071009901c114041c0004086000107180d000042c0298075240c00c060380007000079521f02c10240841e0008070414190006205031030813030f09419135181090034000030b00c8961404020a02c548158450344601e519038540242520a07004240030061007441100c011802240240c4c84c2146015402400800c08402c1c100108040d903500110848899002c00000e00802440341c1c880710b081103068400f8002084104480d1001142c41d2022600650303680021a0003400c6c04004000c94004c0e400e2210810300d40614025622040c4241c000b000710000c90031142c0340d141c14000c42e5191509170707000f4030880d21410782e2030f8000d038000840d82c401ca036510f14890200f92120f802800040c05130040c01a21203280c4024411001c10003401014108001c002c0d1000280700c1414041e001001c0c2c4500310b8a0310a0000103034a0702040c0c3d248401129460010318800a81d0740f0849032159220b800307444141e03070351908151720510320112010082401c16 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 675909280 1250 675908030 675908087
    0x30703081e0615160f050f152e030204060b07030e041e0b01090306051008011803090b07110607060614030c0a140a0902040807170f0c04020f1c02031501 67
    0x200141c2000440c244202141c2586a5685005860b01000c106e41c1d0360404980401508010b000c40c001400e10070703c100c05c0524080740e20300c54889064501e1040c01d04000c403a04040c0c040f0715030140c0036541c00f602c00c1010030b480b6448500d180e0494102100001d2125100e00c00509050240c030f0954004031846101c2500c407024110301400d48840503070704015050030b00001080b80da00882d40224842e40c0046807150402003510300351111802d440318208042021000001d0340b06c000c860443d402d0350030058480c2f0a0b40392603800d0f841004541548110041080014000c40b580054112604205003140311940602071607214051a1041d80d403085c100c40c4108103088021454403010040184080400d54459103c54120b070403036041070540d0760100c40c080c001d40c000c2085502c5192000002007864810700450540e950f850900c0860140390080b44c85440c030541c6009841c24400b000d502803428142e442502402502b00300e400901c4e000c112540c0c0c1445502036040e50440880309003140c4c8061811 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 675910530 1250 675909280 675909319
    0xc01021b030f1602030c090c03090f030304021806310506120d0305060102010b06161202031c090204090515070e15030c071406041b0603050105010c02011808030703081e06 75
    0x1510f030b081e60103004080110300703282d8418825521900c04c192455403a400d03d00080c0b864514128540100c1d54010024000907030795161074081000c10625100b4215501e107800300384c0341c0502000700030b0001e1030304043d42e24072802c91605407503840078000100195503904082028081240035034600c1c80c2c11124058481c0c1e8800d4010a50214041c00041050782088010640300d40c230081c4c0c8041132852604241c420415042c2c103c20300004244000c508015072050300218910b05040e40e04682030341c0f00e41180464489801c1000615003040603180e2142080362080c015510485001d40000d80c3d000b04048149014590320817800b84100002d0700f5992007150041041e03200070010ba0391032540c400c107911140c004101b65813080780700d00d1001c607048904007202a0041642c1d00010145824600140b0090740c2c0242002a001c0c2c0928001005c0d140388418180c982c0a5070700403180900001819405054100317810350f0007280c9a0154107070403420076106e07002411065640d254050300300c01c0c04510405a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 675911780 1250 675910530 675910567
    0x607030e0406050d0804051e210712140708030406051c090b010b071104090b1611070b0403020a0b0702104b02010c120903050f0c01021b030f 62
    0xc025200041680e2a00006441c07424071000449021100090078012400d100840700c0e00301c2c144911650040f8600d074001751440d00d80c0c800203250a1080c0b40d400401c490100310040080c00c1d0103203c0050100c0300d041000c401d02c80d046909036284074002c000540000d000045404442003541c0e0542001c000641000501d440b01c0d003074410f240e0702c40c0300000200d030504000500900ba0004003594821203071814480007801d224049120300c0c50000c420000c0f0301c450882d00d9100034504201e01ca81440b20390700f40da040441003500708042c4107001010075282c500600030004c2da402201c8180c4140c0d9981000c0e0264031810000a400c606c02010310402a8040e42039034258001d00040090341d102d0010040780780c25000c80e41d82106000341c415211035a45002240031b0b4020b081d20080c012000704910151038804080d440d082d116540c1c2000809051213002590000c0d10200700d4a0b0381c0b40c041ca217005000c1e4200e035400d00030040d2000152051320400104684004028884160800040d42d1840c07107100f9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 675913030 1250 675911780 675911807
    0x7211e030b010315060507020922030c240605010909061401030209060c19060e010507080402060319050103051c020d02060a110906030a1406060703021b010c0f03031a01030902060703 80
    0x585a5066402c030b502131948100c090016940c40a4540e24180100209848060406101048440b038890303100616015107850f00d5805007082c8201095600c0d00c1e403000f40b1aa1828803150003403074102603004210350820802c03100e0990b11340103541c3d01c411130300049039218824404034a508400010485d40660007402a4840c014486414130490b84074050602401361080700200f401c2c1181c8404202c079070f1081c42d510708061002005640382054024207080001307800030f0301c64a80400040c00016038420008446010b841052245503540d10300569140041e0034120362200100709280415480083e03502d10400c2568020f1000d619401c600d040240f83d0b0401213f01c02c0c0c0200903072103c0d606e4050045000e0303540503200040240141c09444400c100140201d4401c0c80100400b4002c654001103180c219200115020010001c0d140140c0b00d00115100c000d00103030010344030100340354050f4008071709882e541c20f02c1d09401b4142c000440440d881c0440083d403182061041c400800c0c46410001242c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 675914280 1250 675913030 675913037
    0x1b0c010201330b0304061e0207030503070c08091306080606060a081305010609051906140d0201030e280506010e010b0d0e01151404060e06010e101407211e030b01 71
    0x1280c89103c2041d03164000c440c04e4900e00e881d5500404600200c1e40005000ca040c41400c609003200c0341da0003805132101820f030382c08000c0032262200034007000314101d8486034401881d2100035124080d03c08080c0c20300b44500302d0729025140c00621b4604010040300c003000750503034400d00560f840810b40d140403840d580c0c00341c07019903980101003212304c030603c2850b005a044000b800200c849440042e400d4420b2f036004100d44580844c9000c4543d1284821681c101e582401c02207641c001111403e0320b4103165a00d003103089a07001da81d0500f40c00400410480c0da6014109440e41c41ea02d0300c00e04031a506086c483c010500404014a14401d030440d0300403845481c0c80d0002040204080050720140403180d08050b44050b04140601034510303180c40f880004000c0d410304040c440c50140c002801800c06a00b50a015090300e4030b405220394800e00c1c540007c00f00034085580c0f581c0f03007420302506080e44203404410800d228802311700381d01c1c040c40205400740704101c07034540040640401140a00031030403001d81031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 675915530 1250 675914280 675914381
    0xa050d0f02040306090b070f0806010c031101090303151208030601050a18031209210f020d0602031e01120b0a0f18080c16080c010807141b0c010201 65
    0x61400d680010700045029240108032220681440c00600b0806030086042c0511a4880048250069a11a4019003d007040e5200700520b040c10f4807014103e070403040b05540703414004401c15030507a12040800c080c103000901ea10741c41c1d48190940110003034002d00601020310005010b588248000d064200c0f0519005210402150705c2c18260100d41e00101c9140090f120b80320040d95101407007100400300c0c01e0340300d0403944203030000100d241100ca10181400840d0201d000039506c41c24140c2c190a5884001103560b45000a40a26421410100345401158140000854034503140801c1c000170f80000b0b54607540d840c3c5480380c5c1c00420144a6100c21507403034540940c110545e00c0500d0a000d4002c6250542c0d8803403103040d943c1001c0761500c04142040f1800f8082c402010300040401803907100b0300f0b000c0d159450780c00d070070344010149010f2042d2501c0001400303010071100070410604140702104880050136014010390903140784000048009034101041030b11404600780861031690039803c030859 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 675916780 1250 675915530 675915551
    0xd020a1b0306050a0507120603020a0314210a0306060503060f0f040f060e25080406020a050d020d0902040509030f0906180907020303071e0f05090301062420030a050d 73
    0x7034070004c0390509800b56030b4008001c81075030041d079400841070a1010402290781580c0c0083c40c10001808064080c5480000f1900380041c04c20081d400c20002158101c00c8a600544036041b0354046c2c9858800207080c140d0028082e40a10284d80c02010010021a5124140d400380483d51308500507042d40581c850038a1a2020721a2240c00e01403d18403000b506ca5242980c030503c0403080050303a01c0c40114050780c98000d00c80d030100b01d058002d42e01440240e640c0079014001c5845002c3c04940c400304610001d044d04221500b54400c41155200346c5c1c040c00550780b4482816183e01845c640080144010840344856180c40c0c401050010542901c8240c43d070343d82030200e2030501c02142e4403000350740300006000e11a43c01089a00d940c220300b07601c044e405038100c08020b180500d0907083d01309014010a1409483c3c1c0d0030340110000e00b01c5d460385011040450050300349480d62207007643c0f01260f40f0240030305404102101c01104600034100031031038040066011034940c0c1c04980030310b554550340d054484 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 675918030 1250 675916780 675916793
    0x709050108030a090503070608130507030203060c03180106060801170109080a0801080601140315070c1a070e01020705060405060c0a141f0e070306050603031309050a0605030d020a1b03 81
    0x902030140c000c01962210f01c1d00f0005007000400303401107446540808400c22056501440702c65001c040002c004410418619100303144c0009900002e5241c007483d42000b4541c0340d004d02440c8a1807603040d000510b22041d990030380c2218490701803100058255801885030544c0f034481d07a074012000000024030148980c4692282d90490105000082c00c10801004000350400160740507001415032886003144807400a56540d802442c0c80300f00252010000780300c41d014100c030844140d0070064070f15100d100451010b0040404a0b607060110303c540040b02115440090458203441d00600102d26203401d0800304207140d04114186061441a070752168002034a0803600c07000004140c00401c510304a000e4403022081d0400c543d402d80d1032801907c000d03020000191201103c1e00050002812f46444010a040d0b10481455031075241144a0000d01c0265a0344001d2040c1300e03d4400700411500c070000c140d12030b003504140d807006a0020b06218003050b640d5102e043d004102c4d4643c00451960307a680d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 675919280 1250 675918030 675918041
    0xc02090910140a0e030406050306130207080a030915090b060405090c1909050f0f060f060d0c020c12060106050a1119051f0b030a0b0a0207020306100602190c060f020709 74
    0x202c00a02400780011214640a0380c203006038184003540c00d05040490003040c44c04001c1c02e142c4546050a040c0c560184554101e901441e08150480e64409010b0b50180181c422200c04462480c50300020895220091003005081944a900d03d54282c0f030b0941004042d000140c50991680a1441c2001d92907503405003007003558400400b81701a244c50800400e0803180014000265540c00204000a2020350a1010340c040c0b8103c0b02143c800030590302017550781c045c111214030391920f050b00111103203400080428038620b089980100800d84541d9140d11203100384101000b24105000280109010307080080c00c07880c01200b11b804610054140d0250b43c1c400c84d100340c40c43e07084100784d80c625007030034038219000c400d00080a1020995a8020a50707801d600440a44024940b01c08518108015011542e845400808072110b9082c00b03039212100b400310b442200e0241c0f083c2500e103400d05002402e04000d03260088027940382d031482d0146c180d03281413079001c41c4400c6001d02003000c0385005c0c50b03102d007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 675920530 1250 675919280 675919301
    0x10c15022203050f0d0804030c1b06050d0501090e2a1305010816060e040f09150e06090c0603040b270705100201020c030919090603120e0607030c02090910 68
    0x100c1541c00e00c1e40c00c140b03082c90140740c06000c882c0c210031100000603030040040c54001c0da15241851014105051581400001558510015003c0d07200001c2055104d0050800803001400c20807559a036aa00c4000b01ca40703400400e5142c0d003111480040403d02d000c240268240c240b505103002141c0240083c41340c41c07081d040c04030981d6403040140540b040c2003024082206895816410450400501a1203070070030840b410311481c0c64510f0480c0d5840c654000d40012a030014003010107000c0501800c4c003030f051920065115100352400180d00b0400098188544003016000600e5525940c44240e01010020300500012000c1c082d030540c40c0b155aa0f590b0000b041c0c40e006020038508000401440c800040801411a030050000c8901032401004a4901d6042150394040e11003868511010b454a10380c000e000d10b5180c1311000041c0000540c9410701c3c0402030781c600c854400303d50100111409480e00c050000390307410000c1c00c01424400502038202405074100c4103410b05400d00da070150703403d0640 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 675921780 1250 675920530 675920587
    0x90d0207301a07020607121e1a04110403031404140d060e24090a020915041e150504020c06060d0201020c04090c0f05060c300a0203120a0506010c1502 66
    0xf04400d4945c030500300e008240d41901d040c40400b08030b000412014802c03004001c12030350342e0850000c6400c18810b0140d80710102400c140074bd21034041e602c2c3c0203508103206c1607001c43c0f43c0c22000c1e00140601000c55068541040c28814040451020b201c03031018040401c80b220ba69079928402200c604225034400c17409a106c58043c0d0041074071000042c2c020140064443d603200d10500001a982d01201c654003051a010000d00e02c1d04000c0003c1c0030b0039003080e03020b10608280a001070404e0141d0001508001e20455502040c4c2ea1001400124855041e040810740c00c2070002c140103292408862200b640140304071000d000b0708030002811078854810841c2c14003003155040042c0c007015081000200001c640d100d0501114864103a220f03500510030511441414600c80d04590301304406062003000d1548440d03c91200050182d034030352251411216220903407001a00c2841c4a0003050f101d020b06944100c00a4400d81e1b81001e6604500b4160300b2441d028498501840a80107506007240800f00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 675923030 1250 675921780 675921793
    0xf09032f0a050d0609050106050a23010f050f16060f0c23040509100b04090203091e0706050d0b040c1e0507050d08041a090d0207301a0702 61
    0x8604040340044146224040c10540004221960b41c1208a0f249a0f81200d07010800c003220b40b80140c01440f450304400e600103800100454000d64165820161081d9403060643ca41031030001036804406081e0700b24009001000101c0c540640c0e10047d20801c010041c0755690000e031580c0b13040550b800001d2000b0340c2030f0f031513030282c1c16550320940150600c00f410304100c00d458803440005402d8450f0307002300f0740141043c1c004206032034040300d04240100a8800180d4586171103180040182d401611107031014442e03956001c422216400070304411101034070040903110302e400016500d60304540c82a030307a5581e480942190b50b8981d0b004194040c00c8580c0d0f083c0c3c410883d0400322108001d5562002c040241c2401100005000052008440e0b001c2e410415031079912450f080f628001400c4051000b50107913418072500700c02c00904041e90a500c0d40941c0c1040d6120100070164880d07461584509407108200c0d041ea0b031040020413207030a8080c0b1a0251002d0401c403002e141140b0a846400040e07000340d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 675924280 1250 675923030 675923093
    0xf03210b0103060e102108070c0f0b0c0d0e0616060f060f0b040b0d0f09231b0904050a020d0305070c050d0809150d0903080a0509030a050a0f0903 64
    0x180f01d43c1001c0c0401455800550034403681c5407844400c14003e04401405078038144142c049a003014035a450750150071107a0310007603460422492140703485181e101075080d540101d140d014880542d50303282000801840040b4481c1421168030310720f4251190444410440804428800038070700740700d14081c0c0c00c04644440c50f0a908412210b0903440821600d901c00d906001c10b80e0b400d400c480840d1111084551288001c0c199440106500917030020542e00c0d04202e40104089180c1b02c000810708020141045e47d80c1c5495540c40d918485031102c20030300c1c0003d10308498602001d4850300180114211940c0000c550702081d5180c484490a07404038102280d503200b0082000842000381505840c000ba21320012303034031a007a074000c01450520030344c0c44140f803400c00200352054034028980e080044c0300264244c100605140302c02c1c1d4150413502e0400f00091181c2e48004100c0e030701510581d0724546014490042200c11003684c1c6035640403c100802c000000c1000d02d030040b001140d40080b003021510300c0c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 675925530 1250 675924280 675924287
    0x20105091006050105070b07142d030c04051c1202060a0608030a1d0f0301020f1b0d020a080a050c060a020a0e0a030c0519050405090105041511070f03210b01 69
    0x4070381440440c0c0c2400d0080c055668450b090310a10390f800140a00300e030700d848406441072203145a10a1401c40041010664042c4c2102d141901d01c03440c4102c00840f0390750035610911752004846122803003104001c10011030418003002102c401c001c0c42055529a203a541c0c12a003404018003000059004c0c0d01400581c2d50548664001002134100940c0343c4182541c000d0000c0c3c8d918040c140900343c441e9840803894860300222104010018008c544d5542081c410407802e402200311a00124401c60300042032003000107419540694940007800d080c800765540006075409080c000c4100481404400c0d0000020021207001d120b5010340540c440c01014001090184030300030f070500c40c0c0d10301001000030941160a1200b0344009545103441c42401d58400048404980c0c800b83d0482c0c030f00420004d100e01d065025034021480b4804d264403100b0003010010544a40700841800040d04000740360006107806004601d05110303003032090441c0d1840c042e11010000410141c518961103121425856a1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 675926780 1250 675925530 675925543
    0x8120f101214100c110d080705030c09040905031c02120c071b121106131412030c0c0906030d05090418051e010c092102030102090a030606050a060302040803070209060a080d02010509 80
    0x100000806444800c0300c170040001f44090204014880b000010510010388801100c41e40c2d02e0250040c4040750640c544156240d104105403032440c440034140c01d481c12014000c076801300314441800c00c510303262041c0c400c00030780c89400111840810788410f0040040f4200c040c0b40107200c989a1080d000380075080030280031102c6004a441904c040280a503020350040ca910207032120316440c3e800030b00c541404034280b20307a204585809488042208201e078070300014900d00142c805e86914030503407984c1c400d156449000b185a0760221b00148041155401c060f0300c80c5148070303000f4203a128400303010b4031424100000d407405543c0c410400801c0c0ca100708024028441740540d40d260076940c880c034140c070703000880d640c000301c603140809920711401c2599400d405645800038010049060f6903928a0008020811803080c5c031f000c7d054401000460398040d100340c4081758030031000340d4a0601e0742d6007044503042000b0451075000144620200d84440100311036003003c8000e1b00000303a103082002e603e500d00304 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 675928030 1250 675926780 675926807
    0x70501030e1005041b08100605031c0302250b150603091f0e060c071101020d0f0e1306080c1f09121106030408120f101214100c 56
    0x609089098501d00310008415200028101c40080c0f40c0d241c40c03400c40c41200c81202c19803942000361101150707000e008181e808402c0d4909070104400c3d036032178041c981c490485425040708100c941c24691895030198006042d40a50400c12000d40d0815540c0b40003184410030048e290f1041050410182050345149500f141c40c040350b070541940340c29207100c4d9448071880c214a5418010303080700e000ea8881c540082540d081c604084d500741d85082d81c8500c405400580040c0e4100e015103070091590f5001046009010030b03982e42d64400c6250120007a030b6907201c440070960700540403200301348140b622441100301070200200689904010001040741165074404081d0032501c10680401c7c0c0a508041c40ac0308072035440e0b800041103c1141030074400c8a0441444503044000041000100010b0304014600490b03281d1042403240c80f00700321038540d010101c07000020006181000d022840d088409206100e22540612211401000c000b47c100411103074002840d9440e82100d200703007900410070f0041e62 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 675929280 1250 675928030 675928037
    0x409020f1903110313031b030305190903081302120d030b010e040605060307080403120c0504060915080402041e060b040312020607021b0a0323061617060301230702070501 75
    0x16140c0340c49041c400d2101070031549803244a1700c5d1210405004e4126a0320a41c100d8a0040e040c24007814060007901044440d880c100b4103d0105120000f007a1090020040c1c15a40d5503c2c5591542d448550442d003107401664800e040601c1112849010000210400c0256602152601d024800034014034402d035002d07407155003000c1c01802207446080640e680003002c0c2c901341c1c0071501d841c2029035550296070320f00907050381480082e40041350448010412206580c0cac5000c40281e4a03003020700844d038001c2e5030704002450440030030090300d0070b504a020944203016a01500507100c0d010340c400c030b544981c07010301d802602007070130070a1285442d805500100d40b400601101d181010b0300a464942c0e00c5111942495044a580c1468540c4002708c9e010f1036020f030683e0380e5a1030410a104403142c0040b10500a84a04400034842488804000c00c10151507100c0400c0703451688040c0c4036a0303000810458066586141450700c1c0801d4000500e8030036407100090a850420b03040080c1041308507000b46050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 675930530 1250 675929280 675929291
    0xf050c010e031b061e04030302030301140d031d010504090f20041a07053a020705030703151b0c030e0307050603010b0901030906020309010f060e010506040b0a050409020f1903 77
    0x71100303c0c1d05440080012144155600028140d03041188080c0d0520041044082404020590000010f60583d10303094400501d512030f84003000000128088005c5c006407074044225100e10880c11140740d40801410500d042c5911443c004044034410b83c003030800603485900c810b01403401c50a51005010100600d07a1600341440c000d04810b480307607149540a12800a0b8040078001c0a201401c91084800100007510020860040c82c45441c980004c000100e40071034201c0303580c00041c805045a030042c001e00100740c0780d9120030b0818003401c3e00c0340103010349500c540344290200840407040c40f03003d625507100401d01c5080090000200a51407400399202034424010345d0307294410303241114442c40c850b82d03851500000407001340003a540002c01c001d00200501901e64019000b03134100d00d042038010003440d580d0758141c43c080c0d0340a02c41c0e13503000042080280990041003000b02652580c5040c040c0ca007035625041441240d01c2076402d6800c03900081b85200070194207402d100c801e207250340303000e200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 675931780 1250 675930530 675930553
    0x23040f1811150a0f0306030f060b010809070302090a0e0c030106120317010f03120507020a030309171506060703020a17041401030b030d0f020c06030123010813020114070f050c010e03 80
    0x7103c0c03042c0c1081406001007250345a2516120350406005103500c00b03401d5140031070300e06d440c0000e80303401401140807a10540c00190080000076800e4102c9800078159050350b101c841503000203010101080020340154000407486403024098640285028804204020a5402c00810700500c0c0300410040d2040d9400410502c1e040d90044030a84e504003041010300456800b0a80c0c0c2c910074030310300940105030307818000141034008030018120b4103446540600c015a00340103503151484024a88110344181010034520304080021f802000e10a004444001030240c607848413501c207404585490010000c2d06100008040420080303031582804c040c0300c01084200006c0d2170703000c203450381d808004080152144640c401c004c4104034000c0901055a01d50b110b0801070145802d280700000031b960311048902c40c55100e000010301c12540c0d8244481450002da00441d003503c0b00300d528581c00c0b4010701810f80800d4a83c0801a4a64411001050000d500200140c1a07000090085102c2d0300840e19480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 675933030 1250 675931780 675931819
    0x302060103080f07061418030406080f060a0f030f0c0e01030206090d0602360904081e0d0c0503090d080610052a071a0423040f1811 58
    0x505403540072881544030001040384840f0f601400c0005003005080400302c40c035580d90a079641d0b0180d9030380074031742e064400102074171643d030b100e9882800005a101000120312220490314241c1112000700b0303494001c0c0d520850300d0300342002c0d9002581d0302c100c0c241e00c4408001c010400e20000380102100c601040d031440d00040d0913805101c0515000c0c46e220714410040007201d074115001c03c4410b409060040740241418285610380c4900d030441e40c1900240c0700c1c00c0786400310784640f046501071a0b0915122a2010840d01d0242c5404403074a004e0003480814140d44040c0100e02c41c041c82640c5085d202c0c9040354019184c1042e440c052018070a451080c0b10182c0c5803501c000d0b803071104a00b012035803001c00c440c0d08840c04041d801100110124401e26840e0035402150324004c58100000d0a00c8440f00b10040c003030244101e200300301c0b6103440e00d07602038400d22402c00403080c000c0004000041031440d4000040555510351b604600c203060241d00d04007006440042071000303a40698100050b03180340041039 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 675934280 1250 675933030 675933043
    0x601140d021e0d060507091d060a151e030911100225030b0a1e0203061c0501090609050303072703020103110d060f0e010501020a0c0b0a0309020d0b010503011104030302 74
    0x207007090710841c1020440f91661040c0310b6149504c04800c103c640b5140340b00a104800c240920140c0360301520315240e051401e15110b50007507a0080100100350710f81565000e2003c3e00e0f108190606c1461204510f510002003007000b00d0341103a0b02e01089480261518050075aa42880c45100380e100504030f4039420f07800140200b0300c8030380c03c0035001100141400b0f0011402c00c2c0c1c1c0000e0021040d0410880c000920750041c410309040b14028003109003d203141081a0701040392804d0308140610034900508141620400f01c1a00580000884d26046d0300d0b032005549040f0001d035150b81c030002c00c2c0b00e030b1154429100c00307282c000207081400504a1380500c040314101e80c44041e0400d03803194030103640c0e100408201c546c074010600c010407c444e40c070244104910350030301c1940ca00650702c03c0000740c00c1d400803482e090159400000c0d2111b06003081c207001c5450308140b005008040d942c4080000584a52612070346481c010101480d40d07614101c100f600396078140c8106042444144010030000360001483c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 675935530 1250 675934280 675934309
    0x10e0303120714040f17010c02070602100504150e010b0f0f151b0a0c0303021506031005070e100908061e0f06030102070f03030c0908060106170a060504020403050601140d02 76
    0x11403102d111014407010f0f500643c0c0024075030300400d207400a48450003440c444a680b0f401402445481540c240036602c811301e9204a00258004c0074600c502d0046941c0a02e600901c240c0c1030941e41e034040c01e0040100c82d030f03a07512060a6952000030607030310710340080154601901218500781c54004000032442d68022600012150300012411009414200386098880e4900c0001c0300d140110038106501914650301c0258058000c411080b900404400e900301e1090502030000c1c42900807007090803006002c0188520204079400d800d95265948203071442c0030350109641e03000d00003401d0000d864180140a4003a083d0305c02c0035007c440c200c1c0030304d41c40389610090700740b0340582540c1d82d02d0100b406071041c100002e09a00040344050304154042c0d010b001c8044095850381f180940f42c0b951255545003c0c050f410115180e0720840308114000003080d50b200c002c1030f5000c03802e80e545001180c1030380c00640044403550003400c0103200c07000b01c483c1035810b01841250309141c0c407003580d00495500120b0480c0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 675936780 1250 675935530 675935537
    0x1703130c0308073c02240d0b0603010b0a0e010e0303030c0c060f070f0f170408030f0f0919020d0203010f0c3f0207021e010e012a020307180902010e03031207 69
    0x78070096540d40c98001068050302d42c4826068810b6a0031494a17500ca20780107c075080c034004d043c5581c0e0a01d001941d0696107034840442c0b8060809500b594800c400c00c41043c1000b44080056145880c14030196025010a0703842980703415003a444e00e130030f20900522140b070070a580d40170040010b030700510207a0311003041d0805d124490078160302100c094402d2011001c8005035a401d100070800315500443c8920922000c4402d1615000c3c401d002c001400d544642c400e45c4074000d0b081007440601e0340483c0b018030007486283c5409499000c01c4c251540c03000c0d50201550707104c010001c0301e600020365030f180212020310380d034080c0300c0f4811542e4004007030b0300d410907098010000320481d013050b42d04449801703400a2800990b14003118054011281072a560390001d4584101030702c13107501640c11840b02c02c0c901600300c108460a030b40c0d120391403001c000050740c3c140700c1c0c03c100242450019007401c1746810a0103001c2040003890001401102484004074000d6000700640d04884c24082c1106800000514 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 675938030 1250 675936780 675936893
    0x2d0807020d14030a0c140307030c060209040b0409080a02010e120d021812010e0d14091c1407080d0807120e01021e04090e0106031703130c030807 64
    0x40c40222107440c0310780030540d4407000400c0648135812461019030140300343c42c08190750f0b11943e40e071034403030041e0301c8000c001c141841040c0c030001d00c4a401400d04400080c000184001c040300003d01511900d030420341d4080e000041c5c0304aa02d40c28026094480003200092000c1d012040d100903080c81075021180c0f4180d4017083c0c103403009407051303500440840007c20b4010300da809544041d00800031100081c28510920110f884450f0148c144c200802c2600c00103141418495001c2c40020101140050701d5101d090780d0303410000c0c1d005240c0c08000040e41d0020002c1c01d0501d5a0140352030702c01040301c0705100419040140c01c0398080b0b02815600c07401030b8046400740d03c0200c1d0034003a0040c100d15a00200d103c0301500d100c500f511001d4000c440c0c3d42e01e814030100314842c14003801c90b0b859001c09040c04d100c007180c040d00f0300440b030021038004e00d0034401c04194040f04e40f00c0c00e0101c2a50740084800140c0002c0502c1071041d41d00c40d04000c1603030403240d0b81e4416a02d49141c52148010005080ca54602c40c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 675939280 1250 675938030 675938033
    0x50301180f06150b0324010504061422140d02100f021507050d0b0a0506070b0709150c03081e15040219031b1d040513020d2d0807020d 59
    0x80e0400614801144040341d09251113140002c2c05410071111803141a10b800a010702c0510311088440450314182c50b068503040c2000402c813403010540d50b180c3c50ba440b0801c50591605881d05108031940041e200b41d056107800d0111000d05081c015884910941c142c400c86805603a03204c070240c0c095051800c00000351038094009078104034071103c41600a000716003c1040d6650048000d05140b8244d0104000c003442c0642081501041402a5a0015010b100e00c81c000355001c402580c00046c0d41c14072054555a9194009030250701ca0601c0d00010802100301c810550400d040f00d4006450045640030b054400c00b80c0710652703100030041c8505440c1100820070790f03250b5a0403608220b00129800c5460b546c59140580130744544c1c0484004155000400d001462246200b2010b00c16102c00582d4400030035410440541000703410642a546092010001607481c415a10f00203840b440d5821400c0c401100e180c081010762907501500d004110300002e00051280c0126120303e6811a003205117101039 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 675940530 1250 675939280 675939293
    0x1f05040b01030e0f07080d0206130b1305100b130b031216020d260f030606180d060c08160e04020d020c120720060a0309050115030c050406050301180f 66
    0x144400030f01030340980e204404d5281d1001c140a010344000600329406504600801c0ba5100c2e421607006071031242c0540101c2c005224100340541100c80003a10001162407621064204020001c2202420380d65201c0c11041b801c0281500014100c0c00d801040581c0307204010980703a0554141d5031a50340750001d40c0135029040d0f0400000c1c940d80240000404041c640341c482c0d00b1403100070801345418030480d07091030b982070460103c1d2000149600005d08584038101481a80d40011440104042d52041e6003100c42d20750f4258403913614058440030400031641540503001c008050601b1103d150142c0c0701040782d64000140703c2203010250303001030340e42007011400c50007401350042c403038240d0080751103894043c1c4040c00900701d554000d0010724000107090410742d440b688410103154100b01c051110580c1940668000c41c1ca041c01b9100108622502c0030004c2c5070502c09400444070b100381004188010b0800b03115a00103004c00f50002c0184102d80c0c01e216a0321403005030f004240340c1c040e6000000700a034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 675941780 1250 675940530 675940541
    0xa1706060d121134050f0d1b0b0703030203070305160212031f0602150604022a0703060e1b09010f050607051606050a0206070819091e03030c081f05040b0103 69
    0x40060b0840100081c81c0061355400545811081d0801d070038400206043c03070520411070340c0241c000c020716116442c1d6640c1c180100c01d02046c102140d07411410006101501000401009201e03640041c0e5078641440080e0840384084c0451a40b07200640006102030740003d98115034411405049031a0303622803c02d5868a0382003500300b03400c0007980030000342d9150002030400b000d007540700c0021840c0d034400d82030000328000e0004d8040704004d0300310185543c401e81c0c1090b072907141d888030550f44000c0d100d40319070096039860b40030788086501400110701c001041c02d00414010f0800c860036505545030025181c0038940078090503100c0c810000388142040020450014611a00c40c04c109519a0702c0a001e411a04050702c0c42e4050b02420f00042c000c01d2050714a00d114000d074007101c0c40c0b040202648080103012840088030255130b1180b01c5083c03420140c2244010600c41d84e0082079640c00e850b401000048082d010b048021402c40300c603006c848601c0401c02c2a030b2401c2e5070015100c030506004030041d01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 675943030 1250 675941780 675941803
    0x90c1605030f07021c0506060d0201050c06012303070e1b0d1b09090509060103171b030c1501081f06090203151203040605031f03020a1706060d1211 65
    0x800000c0080341560008040c20f0f040f0700880708915400c2500b4a81981c070145084000c1894116a0025155117049040105040d006140c0309050402c0710003041e20305034080e0420640170909094a21031041e40200800305070b02e050f0060510b00e807900b11035851112003e005079041075035110560304072600c101e0680e20030310241d19052100101c0c1040e400b011442c3c0910303080016002d0000420640b406005c0c19014000003001400141e2039500c5080704c81c11000d41c0c000c1004e4041104021035804210100401640840556607500101c0c80c51464042034078002d003865107052004000c56440807800081d04440c4000c00f40c800e10a8a0151000300030a81118034868804018001c0e034160441540081c034900381d035070202000f880c0c03221650303a01862007a000004c004000080351806440e404a507104920241600410740341d50004240789100c0d044400180300c0d40a0311881140108089900884107071002c4039070001070345a003900c5582e611178080500035038200e0325400c00405c009a46901 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 675944280 1250 675943030 675943033
    0x150f0a0b0301051309081914070b190605030d08060427021302090f01030e0106050406080d02061605070f110604140301050c1810030209040f06090c080105090c1605 72
    0x250300c5180c0ca000c190800c0c099140100b40c140320702c400f982594403884c10526089041d1508100318070300540d501a051301038000030410300f070b100500504228400341484506c105645907451a05400e130020100c2c1000320510440d0400f88100300d181c9010a01008001152078244900c1d40c1c2d82d4041400380500e144502513031603801914030364a880c100c06929103180b080322103144c2910842242c01c2607000311074850b5440b010342c1001c0c1c049507010342d21010f5049410000403403925030303035000101143e1159209500c290800405188015814040769a01070f43d034060702000c3c010740860081450141c2c0030000c2003503480709405000c0c131000000c450742030640146816512500c0303408803088000c0034003031203001c0e60070304001c80c6100000406445405000000c0249102100c804100074907800611100070705a00300040501501ca900558840c50310582c400300301c0600e02141181103400400f903007010080e458005001603992030081c03542000d115000103444604146080c041d03031255a174010000d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 675945530 1250 675944280 675944299
    0x9360213180e06070305070f0f09090c110703030f090b0403050a06020901020309030d02070801060f081c14071a09010b010c06020a0908031617030405101e0e15160503150f 75
    0x881c0d40751b00071078071410455541311403040e4061820380e4020052403103240881c2c4940d0b0203001100c0305902545070502c031846c00c030301000200082103080c840107400640c00500380d084501213041d0008030400090801610310b916241c03464403496201c00c401e070700060240342c000070440c030b803603108100341c0b0030100c401815a1015421107074042d56540c6a0f10400300c0c154241400000c0c08600c248000b012034801c0005401380c000c90b200540d10b68090f007222441446a0b0408412402000e90081c1240070711689503000c040398691000821010003c000d42d4103030381014811070181e41c5c04488407950903130180d40945c0b01c100000d000d5540f01ea40e5000102c00c0e20000c01e003608072919092010031030038003034028481d11080c004400019031108450240c4140e1080d4020803090300a0340c0418003501c21005d60320070000b8402d4414081d50720707000e03510722241d0143c29200201c01030396128941003040300030650054210f040020302203010003043c0c1042e40071080c03509079050700c0c1c0003218445280000c0c00d6843c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 675946780 1250 675945530 675945541
    0x408030a0e0f0a150608060f07020a17040302010e1005072d1506090506010f14280f0203161401020408010510030b06060f180109360213180e06 63
    0x70345182ca00804d40344046083d8000c0b15440083c881c0703400381c50418000c0c0a090f5a140345443c4a1940a0302c0381c41103202c5c5110001c042820010012402c03004000f1907903840d851400010201025007201600c03910001c503401d210036030010102e44000c0ea103e508078200d900f16419024251940c031000d4012580192401e50800454841c0341304c841a1200082140706c3d01c030f2030807004030350040f607181340841d90b50006450020b020702401805082d00401c44c034a4808011501090b5504000781d0020880f892b032040440315402c82c480354002e07200c0e4401541800c0b214503441c0d140749000500941407101e000b1003090001401c0d012580680070340f8009116606100040d40a05d0409100661742c0800c00400304000f49041c2003194261810059100d0800c04180850410490f03020300c4036041c01344a0f07000240407550b072011441104207002102c00321800c181c1c1c081b07040308030380740013882882c0c8100034150010000c085d0000035115041d10749610510303000d0741c01d0018981c83d41c68422500c41e030810000d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 675948030 1250 675946780 675946783
    0x40f060e011e140708150414040203012a03020d110301030305030402031506010c02120a0b0109021c090f14100203150a0b160311240709080a0b0408030a0e0f 69
    0x300902d40300c01000b409403581d0940340e0100d6104103006882c0151181c0802e28071846405500d41101c21200c1c000031550802001408444e0310182009010702d0410400c419854203100c0d09903414080040c2a100c0004840f503018080001e00380402899408070b04042851100c0d40091040540c840c5101d56a503100d0401400980045500700c0c401d118088080c8040c6400581c00ca0242d03606859517000c00f06154200040c40d911480303450b800d4441c18440501047c00560098020141d041340141c1c2c580040350780702a520f0300201c401d200d150515038000002100eaa4540700d0236500815881b920b44408050b20781019032060310481490b00100622803111070707441001c18001c0b01114040c0ca065901e1000c8451400380d4a0b25030f03003e0800c130b4010350205e07000354981203c2c5440b04003510f40400201d035800344a40000c029100b007120310001000669500103030b452018020000041004a03180c1e0740720b042600c40184000c185003004400300e41d541025800c204440f405540560f04010411100709 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 675949280 1250 675948030 675948041
    0x30b19060803072d08030a0b10030b040614011b03020f0619050f0c120414011104030c0e010510030b01050904230a15030803041104150305071a12040f060e01 69
    0x143c42000c401344025800140c0c1500d4803044041404441c0300c0800581c80740b244940004081c0241982c035130000395655610203900c3e0144c807100c0d4038000740304003500d8140003c0341c0d100d07000030344040030304404490030f40c1e005400140d0741250200481d080c210709280c200d09103002c08040151b580325940a1100403144440c20740b25502090342300f040f090340c80d000852403200302900d950521030010801114400c1e401e40a9a0b480f50040c14507000141c2c3c942c4c50786084409a0039901880030002c181801001417034a80300e801070100c42000040344d410940020a8113912520400030b041c0c0e9120003044e9a40030f041522200d4078020004c000c0e207500103c0040022410414100d0801c2984000454044241c4110340a1186092030340c1400d40c1517558851450384050029039030381840e21010300d0156118000c0c00c40800f9540e004000c0c3c10701d1450458a0075203503800c103001d1110719461b140f020407052410b513031410a61004500c0d4540750b0741403203001e00300d00c010041c050509102880410101c1500300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 675950530 1250 675949280 675949283
    0x91c1e050d0201050112021e060f09040f0903020d120b0907080403020d020f0d051312050d1704021e0d060507030203070207140603010e07122919030b1906080307 71
    0x7503401c07401c851203049080304d02c00d004903c01410100359841c05420800041c446899040c1d1000c00e10200110014405403c0921201c000400c006515020382c18507000300032001070320300804d000400103554080c0d1240342140c405000c0202c010b8a444202a01c1c1d0800105181c019010080700c0c10540c0e0000c10603541220240c1c054840c080c0d00c0d850051001a0800740034214070f0103071158444031b00c01100c0a9110014103080426200ba010a12007848042004a140f0500040401c0c1d00c200c0c1001d88201c0c2951018800040c146040201584800c410b03d4034080b08482000800c1148200144807040c070000050100340c075110411220030f4043d8001c60040006070229038850740ea69510014460448540542000080c00104807982403c00d00c90340140a9060049140c4203154000d4100c48041407041c2d020700c2000e0240a041003c240122854102036500340114500e1000201e210a090701c8010600889580060f112000c2c07a0b00c4054050140c200030300415039207101007507598111800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 675951780 1250 675950530 675950533
    0xd020306030a140a2d170c070b0403031b030c02060327070f0f0b0d110f070b01140901050d330e12030415020a140a0201020d0e060c091c1e05 62
    0x818840003801c0d008045e94111842c102940701151980e10312a20329075402d41e40181000520602041c0307942400701602420020f9040703500d561650400900748402d000f040d0114004811031640865444603071720f0050354041d140e080e40d0f5150703141e400030301c0e10320001416200320494010402e81500840d103007041319041c000c01100252615074072207140ea55880341300441c8c0340402142400c010160010495048031f1540c0f03505001320445007404562000c0c108035002440500107011003030445000e0301c6030350000e41d45904290304100103c2c2c2e010003040c030054481a40041d810405011000d4101e0301020402c9078148642881e200c0d80000c0c2005280c05072590103080082c1705001c1242c41501d2085821030880109150040000ca00942c002040c0b0b008000810900a50b20f51a00001700403000701d543c00141d4030740a80ea444000c84e400b0945194090b080541441558003c010070303151942d1044134a54000980d100203681580340b0300750010301c0c540488103a00255081c0da101070741c0d254003400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 675953030 1250 675951780 675951803
    0x302131d010b0d062003190606050f0403030e0f1201060503060a0b01050405210706080a0507031e0b1c0b1b03100e0402040f06080102040810110d020306030a140a 71
    0x10409400d9414005415030000300d600c60f032102003011504518541400055002e0607000c00c660380100035441114480c009401a0100185000d168480c1c10010b00003864031a090201542c5000200e01c1944406400c00001a078010b180760340d4200c02d510074001c000e024680718040807804a000c0c100f907214035071290144400003507048495000300b0f007160605950300c500d131a0a0034208200034a946032000880c1030b07101c8440034101d1082101c0000791065450f03d000b07a280215090007a0343d4001c00d22401c15003841d4000407290392500401180d060400404079014003082d0101e4007600c000d505c103170803c500c00c200c40400e208803800d0540c043e00068110041003043c80243c42c40070310045d610034041c0b05a641e810042505548819a04948001d00c007080d9450541002c00954001350040d001701d0f54001400c22008908028151034103100e00d000784044000564195902d00441003121411500000007681c16079090104002d17441c3d008402e01e0509000c030380340aa481b507802d5012a0724600702c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 675954280 1250 675953030 675953081
    0x1111c020c03011413080c100e28020a0b030a090609141204080706120f0903021e01060806150f03150a060b0c100e011d0604050d08010602071a04030213 67
    0x445103900c50300402c503817403014910703e5581c007900740d0280d640344a0342d009154036220120168020b4800c500705e000024408022120320b031070016540701031b41201d070103002c2443d503005840b2010054101c4071440e5107582c403a50b806410b800601a01c440040107246005601400c1002140342d582c4a00c9049046030000f01101d1a00c4c0c1991160303019804055000b540104003551003410020303814100e0141c003154007800e512080e010b4030403541c802c0780580c0015948000070104890741442d501c00090090129074901500d4035120080548030103d003180031058898540c448901c4240207010103401c407201040c082c5035402001c44283c512005142c02c020300001e25844080980728890540e01c041c1000541c001050001410b90170665000d5548401364400c04440341c4070078090111140c40a0b0005241518009061402e4030f001042404103141c01400041c3d4005881c40584812003e454070040c0107100100c0f0501070341d80300a40c8003540b8150752200403034a40044154041d139001e13410f21200d45 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 675955530 1250 675954280 675954311
    0x70303050c0c090714090301020f040803090f030d0504060e030c0907050a0f03090201121503020a060e03010b190302130e01020301090c180b03071404050405010b0306090106090602060601111c020c0301 88
    0x1c4d44c42c0c0000070010740071401c000c0076460007442d04500090005103040240d034482451034226610128880d040030540e051241407074100320485810450151480c0f54028202800340d00660040c503041001b4582a100c0c1520100051000d03054020402d1a4a03c1d07c0c090091590b88162030000000f0100002c60031094028022241481e43c16124548420f8821200c00b00801c4614584010300c101c83c2c0000002d6200c491001c1c0140c40d00b030743c0e101040c0355030b5007d050030744414801c0a4054002070020540b804041c0c050070301920380c120780c80300d0501019403501c8050100c0d03203da00240d51000000003507440565000350390f8404140c46008000c641d051554507002d100344500740801d0410000620180e205114002c2c0d1544c100700a542440e859a01280864030300341c00000c52080c00005019051070150300243c014441840d00d84c40103410990025103510010745a5414001c0080311050075100612280041080b4186604038900070003030025600c209840419001317510308065440d40d50907 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 675956780 1250 675955530 675955549
    0x150a0503031911070609060f0c060f0501081204230102030c010203090705090c0325090b0301030f03080c030c070803040c0306091515210302010621020405070507020108040b0a0e070303050c0c 84
    0x305c903107408204c0792408405a60440d4065211810400e4070003102001501d64416a03603246642c1100040641c10130082d986826103025801c000d8201c00e100c104140341440003c030f00c2c281c1e8011802c070b001c5518400181d1841c0200d20f903080840d40041308000392080001003030803c5070070468064903541c80740030b4008902d20040e2800d0100507075a00454031450700c50310704d02031300448038540b00400c156100d504186580007a0400c4841004e1581200c0a06a2100c2c40f1074210003003001c41850760070a120102400e114a540c024000400440003e00b03100910b4010b000442c2c00900a11030342185203080300081f03502d07251140d0305030307d0860004221140700c60300c181903c0003c100c09229944802c829004415820812801c540d03c07194007007112688121526420f411b40d0380c0344410304421780704100903154000c00e1001004003e20107075000d81c0e4480503098005401840d1103525443d0403131082c01801038041c1d0102d041c41203407000400c160703008006101c141d5200080e13852252055040007520314 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 675958030 1250 675956780 675956789
    0x902010e0910050d0c2306030712090606180c020f151003080c0a030f0503071b050a0b1e01090e030f220b1804090b150a050303191107 59
    0x480d00e1010500900344001920b41104140c2d09201d20750b540c61000994858103c01e048800100003481040b074078440024801c00c1d5048568007018070001c00c004038106010003041d580c10007840401c0c1444000340340c0c0c41307115141c1c0c2004090000d50b4603400c1d040a186115102c010520340b0380681c40d0201440440e1040110045e040a041902c94040b290158808050884d082c00c4c482d4070700000c0003c5000004207411581080034120403411382c14060540030011508006004081040083e6268011074541344c2c400300b044000220b254504040c4d1400820840080185035a08117100d42d0a168440383e6070b00a0580c080c403803440e80c03202c0540090303500221101d80c04c0d50040c030625031905030b288003600c01d103074012507e06a280442ea80d44e400f140030681c44a042d8010020311252201041410410a184282c40074070102e03045a54240c580103004050300600e0074040a050040d030740d080183d20007010b0040c01c8131b45034004104a4a07a0140d01a401c2c070205841d0132012000890202d1040100e5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 675959280 1250 675958030 675958037
    0x40b07080a02191e0318060e13090c05040509030c100506040b041103010311010c05070f0303080a0e1b13050a0b09010f0b0a0e0d120305040c050406030f021c080403060e010c03090201 80
    0x800712413084c98080300070284202e090211840c001c0360704482006c4904014141540e50124001401c01480544880a109454107500b1301103414082604514044120742040e5400200c45e0307140e60740c1606600482000d0241c03030094020244041d02d07280c00036030003580c00319400c0081a15440401c011107041f10102440c01c0741c10b200420101320342c00b109503401c43c01814040701d5041c841d900d5500f40141038000310140c164411741801403503440859a940241c01c43c2c01003050502c0c4001c219542d1106204c1c5500380e0301074401c0e180164840d001148401144040c080c41141071604040001e082c54400007402801e90300c000207003450b9a8080003085440812046203061301d540011554001d040445c2c641111000041500107044d2400c5013584441076a030009450802d0b14090f89c107a040c82e408588906d052186c2403002c50101803585030b03116811110080c240c4500300500c5421100f000c005130800f0004036002013440341c5600243c40075101e0f50001c00c1880f480c000190704950602001a000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 675960530 1250 675959280 675959303
    0x1051207120303060b0309030d0f090506040f0303021b1e070b18150408030a020f1c08090f0604050d090501030203040f120909050a020a020625080c040b07080a0219 72
    0x94031220303408240c030603000c1c2c83c0c0407581e56145c10303001060360320036a403110b5190310000d64911400b80780d10914000110b900401c0c4000d654540b1980c1d62420050170103404d900122003100209802581201c0244000c0242c086031403248030702494813030091000ca2104d0b1079411112209070700b000725988050340d600b00c81903414100070301001450381c81c0d0514180d821003010200860300c8481c8502420040800b00b004503511501580002d050100207203801226030f02070401e255085502058091344090036180801d815914401103900e0940000300707001d041c0c00b81c0c47c00d0001388440450081c0540f0744944658841541d0340b4011403c0748011030b005800810550847d03000500e01c210854902d4009180200415440d030b128503048420607101042501c0c0c1c0002e8a0032465010b000b155407102320303400800103140b84010150309100712182d62000704851240020f2404070300006139005040c00001403610b85000385480183d541c0094060005480f5072508001031881401210078410741c4030b03018810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 675961780 1250 675960530 675960539
    0x7200a0c0f080d050307020a05030f03150a0b0a030e0709050702030a0f0815210d11070605180f19230f01170a18080301051507080a0c0821060901051207 67
    0x104c07a040600350130114000c284028001c184200090103a0707550f00c0d42c1a958030b013030044240741c0b0302042c000c00700e0003500284010000900c2000954040110509020039079a00b80280c41d4100316164101e54941c41c5410140320a846d400809040e8258280e102e13405040e82c0014250345410301114121510b0340007204400d031a00309502c00210344c41d00c3c64a44004028120109828030408045003c00100c551100c44006507007042920000c1007503091840c68a0306804000d840c2d0a03810803114024030f001c0b142d02e00191100c140d00c10b1646840e4104801c5c1c00e841d8410200451426030082880c080426600303040c5142a43c25102040d005071107140000e83d2000d06846810401800c03000b01c02c1e542c40c10071410b242500b40c02c000035445507110075965030600b41040980d07200702e244c1400640c014007140000500501c00c0350035400240c18054001c030150300d400041882041e6100c03c40444080840a11100e000409405100212000c000a07a2950248400728010300302d00e04090781319650410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 675963030 1250 675961780 675961787
    0x70e0111070e0a0506031b060a0923010f1706040b030c03030301060f0206100b070318051c0501050f131b05130f0c051306030e0a080705060a1a0607080307200a0c0f080d 74
    0xa0850a0406d1504195102f49000c1c03140c1461031341c1c826505a21a2001031580c4c00560162418600d042001440c00300d2107501400140003800b41c0d01955481c00780944039501000791140c182801003c407a41c030360310b41c14001c041c00000b900c68400b6202d590b020a0000b0f4000c01c09a054514500900b428002180c40858500700c2d440d12210f4154542032000c14903485038542c00000034920303087d8201002c460302c0c0940c00c54030300505210084943d0000e114001e90513130001003129402c4910414000c0790100754010569031035012903400707501c05620b00c0080301180c028030001007400314204800315030391009540b1740c440e10680142d115030350760060103082d00070340c0300c0072082c1c40d020100c8503aa080c960740c07200564040791003668254000c008200444030240940380940505407075070751400d40604080384481c01f030308000902401002c0001031103a480303180d503105002140e825020301d40203400d07801078840151210a640e43d00754580c0205000074144101030840d94004000c143c50b200210048 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 675964280 1250 675963030 675963037
    0x150b0f09040c170a0201170702030405061e040e16020a020f042c25050d030507031b1410020f03040f140f0d030c0215070e0111070e0a0506031b06 64
    0x302d5114806103004140362070350f100e02201400500000745040c0d411400094a030b0401c000a40d20034405480410a210344e0100c1900c04030b9100343d9030340751143c03000a0325407100c441c641000c0621483c04034001580e0340201c69140d0068202d0b0040c003410301070343d11040f07884594030f01003e50802c00200316224030b4101980103140004243e00a901d680d80314034600f9900c1e4011401412007940100350302e868523124000c6401080000d2442c1000c424a09004250700c1020707084003a0030700c240030a450043c180a81d502041c00d41ca13406810703584004900c4d00c0c0150f503403250401c0341d56120369800650713800068030031220000081d00c0c6880c00c41c2e5841c0e83c0c0d802c038488030311004c40304101b91501112600703404100c2d40320b881000340c0140c01003100720079000b0100c4001720024411580080c4d001c0018070040d80c2002e0300101d452615640710034a00e0010786100541201300900344c0314122000810701c5a40e005c8074000d0800000500c0305403140800c05a88a11181e440000c4561141182c0490b29180009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 675965530 1250 675964280 675964283
    0x21602040f0c0801030305090411030c070209180c0409140607090906140d060504060207051b09070e22230405010b0103200a0c060608010b130e0c0d05030f0a0c150b0f0904 75
    0x2c40cac10709486000c45055082514032010000002c102c1008601d00003003116400200b2413000075a9030b86240c4d81c180d48495082801c0e001e580e458065005120264403041c070301103000002c07071304c00d4104800c000340386054910600c0030302450404007040d0403510b444120751004005080d01d40c0240b050700c4e440000c1c100030748125451036080200c400040c00070700000c140e0303c09824683c0103079810541406911039008040388108203000380a460241c1d155000b0300c2441c15150501b8800d20f14a210901c0140101d15900710098030901103007d51aa110030143e2007948201c009200c0004a2001501580c1001c03808102c0004808220001b15407010003500920700d0038907110041d09455201c000c2150083d4018165a9458480100711418a800405861402c11100301b0121070250703c15525005445042d5200c0e500707000d8240f06104007001529119181030420a03550148400080c15141c240c0303500719441c0508005030240b030030451045500020000d0101611007001004109103040000c10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 675966780 1250 675965530 675965539
    0xa030b0a031b0f08120a051e030a09060b091e040501020708030a050a050f06061b0a0c080717011404020907121506110a12080613021602040f0c080103030509 69
    0x2400004182c1c41d2840c500e07070302030720021807807090300b48100c0034160403007904518045e03801005154213101e592402c0310300d428014a4142d0b150400c41440e540c071030500340450401e114012040c000c4204076a8040c1da111071107410300304610100002405200901220301801d81046078141c102035a50400403294843c0c030460005103041c2684d81e9030401904195440c1404c2d664a408009192050303218094000c416204c07062003a1500000040f0180700c4c0000c05a1201c0140d2070006e0a04000c0007406801e076841461401c806403501503103aa16a41c610554901d4a002e586004134814180710b40101002a03000c03c03002c2d07540355000e00c101c10b81c1c050f0441082061610030100d0100c0544180e013000c0c05610360380c20f1014a00381d0020b00111340351082c440141c008072088000118500c0c0800c40324209070400300f03174580d18030002540b19501a141400d2680c0005072071041c2da1996007148594a108490804c0220407007040342044403050f40000021441000050011034010000340260440081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 675968030 1250 675966780 675966799
    0x150f0b0a090e09030a030b010c1106160501092901121e05010c080106121116050c060304030201060806100e151f02010b0a05030105070206010b03040c030b07110f01050603030a030b 79
    0x4210040b11811a0012a00c2d0070115202030083d41c58054020486400d00c2c005807a501a512500e911a0f0358100703075882200001841e001c103c2802a0402c10240c00200811a00d101d0b42019044034159400b8031900745010b01641d031031803040804560595801880c1c0440081060ba5820704d81040460710480703610062800c0400207070240201c6c01c610030240e071f4514103545050343c0a4860400340b903a40441074184540c610103c0c601c0010b50781e02001e98040142c0c21207541c1000750400000d272100e542c100000104200034150150003036400c4403180b0085a042c0d0340c80d10a40c102c0d40f2140c0c0142050300c0349540101d901c00e0a00e440d4010f1030800207052082c2c280240d103116003034001031190200940d4499030604210b04e084450b800050200b035009120610308048000d417a007905005d1054410804004541481401d41c091006075500030300594040c1400900176140382da45180b104103502c2140d468045000c018000c00c1c0c0070750006002181480520b080175400340000c00c59180c0c200381503c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 675969280 1250 675968030 675968039
    0x302062d07050c060109061202040f060b070b0708091504060903020c0306100e0c0403080a0503040c03080d0522050615120312220503070f020d02040618150f0b0a09 72
    0x100ca0398001e99150b16126030b80c090803486070b810144140d1080250070700c1c10000b0040d8200c401c2c4e04881e240da04a41c00207031070070b00025110003003645d600f04943e503100118181080050520000d400341400b922640713090f07070ba403542d607568451320070388000d0254013510b01150000f001c0b60000e40c2e0b4944640151100d42c819040417a15040c1e04039200d00d054014003500700025545c0c0d1082c0c940000354910a0751810781035480c0e000350351040556500401200000040070700204d108401c02650b4000c05890382d80038011000000391000f03480b4044044848207034100035104101102c60b030305034000d01a188950302e032940ca60400e680406039075080756103002041c01c188001d000822403c3c1084403580e109081860071030f8031b80000070004a0348603000c1c0e4030b0f000c00b1480010583e0032065104084030541d91a40c80401c0c10351034804002500503061a4000c9403040c2000703240c5d40c3c03910a42408000c11101150009010415440792076490500c207941402982111801002000400e003400c0e1030581d81c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 675970530 1250 675969280 675969361
    0x20d060b0f0102030705030f1b010906020d050106112a0d05010507020f0a0b0105060706091b0e13030e09150d05060412050406120e0708010f0203040b060409030206 72
    0x110104440050351285286018542041203840110083c4019400c254040e070798079540e480345000d04003062002007465551845810032130000c4141f404024001001c5502d4000302a400030400c0400c041c1c2840004146103100e545070000c0c040c03100004043c01c4001d11282052954500d400b00754625440c19840d0041c1c6804206040036849000001440e1514210083c2440d16034426202960003803000c2c000030a03902d100c070a040d01c83c11a1040d0f603d060030725200d0300070700d40311400415039690380244041d41305c48280608104d44030103005500c91b82e00d529030816811000f00f001804034082800203011401e041c444a940f00710f14040480c0007038820340004007a050282001c8481c1d40c805001c00c030421410f6607841e0740a1030325040c1a4100390420350301400c0038100300d050400c8a60f4809115a80b2030080200c1d400400a18000300900642404000081d40c0200c40070b0351001d031020f002c01c125052038403540010b56015805494140c480d0320342c0d881d800340d520040c85040da100c00c1035403450855 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 675971780 1250 675970530 675970549
    0x50607021c11040e03091003090804170709061706010b0f0a1436010201090f1e0b070c0c17030702130209271803090103020f0d180201020f0d0507080a020a02 69
    0x209113000703544810460040080000d4118098000c1509014140c400218003005860a5907030000d4221190407400001e00d00e05800ca6012910381810710000140340210308070b0140340e80d90010309540c91603880711200c6042c3c1c4101650000407020400201405911a0000368220b240314956145803000d41c05950545440c15050340d100132040c5040c1d0310300850041c16940d0710800c207000900583c1041e032100e403405c40704444003500c00e00b602d83c1c0540020840320700c6100300507403007a2010401d00b41084000c14a2944000880e2041d95038040426400107284003415040310031001545030031210f900740607100f00c8500104001c1502841219455a519a151000c032400118940720981c80380354281568000035015841d101041141c0b0030702c111012044030301d8440282000740e55000120b261891601c603280b101c1d64051f1401840700084c03041d04020b8000d45000368200c5603800e0f900003425885601e40d079000c0d4041041040b0100015200c00d014142c0c042d002d006840b09245641c01045e8080c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 675973030 1250 675971780 675971801
    0x1501090503010e010c260103060f0b041b0906091a0a02121602010e100207091a040501290a050301180609020d0509010e010e060c03040c030f0f0c050607021c1104 71
    0x25118114540b00359071009006c08003804588004404190600710151000340c103000150103140c0303e0039a40010600c60f0020003000b03002038070030499001225044006442031107608000107d070f01c1000900f0910800f0b942d0700756400c840c54614a0003445d2100715080d444051a18250701031008140490146070000c0c2407440e49204200100084a00c0010042424500300e1403203000402d800b0340025900083d2441512413490002030b00401c042d80d0110390342c00e50008158401e081c0b200214801e03e19804141c0e0940102c0c01790701c2641000002496540940c4100e0b10026400380010002030f071440001034460050311400007580f503211545581a680303c01d0034001c0d034544410900030703c4c407400d10910a02c81c0341d0400800021082e5011030344c4819003d01b240e40305400200c082018410303030044440045501c040381c810b0545452070402c40c20340f00442c080e40c2071510294005040e052207011145500d60042200c021184041015204004c1c00e08040c2c03150040400c49010135241c9205110340003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 675974280 1250 675973030 675973033
    0x60a020f0d050a050d15210209220b04170f03041713090509010b06030f04140606010906080a0b090a1a10201908090f09040b1501090503010e 62
    0x40c20a00480307240000d0a9855001c1280401c16a41419840810b64014816000000c0fa101c841c01c505a481c2c007500c1c1d000340707a054905180800009202d07c110040c0c0358070946185000b80e840d8070030342d10f04441c0d50110b0000500420032000014900c800c00d60f51041c4200c104003030b11200c8160061943d00010b050325101032000092000b0700c8221012100311450012180d860002c8240280715800d066110310400e16031100d02045540c542900070b1080000c0140c4050303105e2400c0d201c00841c1c10f9007910180c030102d5444070a1017103108080344442c03080106850b003100881c80c0a10440d101113004000c0e905059603440e034882c0ca903840c2ca402038000d02e802c18003c60016042500c02c80e0340407914491031301c510400c41144c131080c0e030445d0300700c1c0c0c2a207802c1d44155a02290450034a050a03210fa08120840c41048620000c009a0300081c14031400b05403206482143c01d030050010042040d1005464440d12000046502084041c6085420310614195060796510404682910924000410b55 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 675975530 1250 675974280 675974293
    0x203040303050f060909030d02160b04032001090221032107121404121103040f1703070f060c0908030415030c08160c08040e04060b090105041103010e070e060a02 71
    0x1080308440f2243d0450000c0390388407264144900b14654921419003412003250300800c402c00c001d00c03200c1d0620141504100d036030401d4a424035000301019131305403008803d8000c1503280084803405200c0c62a000d5400b0740750b55000c41055021908001c00000c42031900d120400c0304d0780d0156082041c500c840d01a9504044c003a062101c005000e13170440c01c204c05c01c400d10f04103000c0501c4c060901c81541143e04007845003007101e06200100d491022800c1c199425210009000034030300c0403440c40070215035001602c0550145080e008513201d100c0c140d00540801d604644042c080307006c40d4170010300160b403801e042c8a46603540000070b040d500103900869110071901082c000050b09409095008500751401e50b06030b20745201f4000c64242c600c8135aa04200e01d01e0040020002410201c40c0038249040c5803141c1450b0502d0900e0281c03010b440000d0240c1055000050749041c2400b880e40000d001030705290840e07007000320302e080d000d00003001c02c03040040d85a044803e5441e2500240200380d0a82e010b80300c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 675976780 1250 675975530 675975541
    0x110c011d0105070309050a080a02030c0f07050f0f0f01030e0106180209040605192c0c1902010b0a05150909090f0106120b0115020f010e10050a020301140108040302010f020304030305 80
    0xc44600802e50f1040c141000c1c140320010b100468610780e1580d20511480d2a01c0100c2e000321b107540070344507000049106000400d070700383c6c00000c1e64400b262411a0000c1c80b440c03189090100524008400d00d82052120a40450542c0a60401407125003108000554a17580c1c010403407040b01c50b118202241c41e4002950007044c107080c020035029000a8414241c8040c0c1200e60580700c2405100300d203208800542d8425418403520900403005424018074105410041c1c0d8038003440d8001482c1a01c0c1200c0009807040990060251400c0410010700003410b4130303d0002485020205510408a01d08040104800035503483ea40e181c01200410001c00010b00c01e03404550865143c0d030056a00c610020000e07000140040b5085d41c15210485520000e1050f0700790164036200100300f4030743c80395003044040c0845490018100c882044000d8040c4121f480d40c50074841248428004c00d82c0040c48a90400240d5004500071038219220781300001d95174080820b150102c1c1c2041e01c00300c00094a5006128 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 675978030 1250 675976780 675976783
    0xd09060b030106030521090405010b1b0d08070e0604050306070c0210020f030f210c031e01120b040503040b040e070305070f0801051c0206040b0c19030909110c011d 72
    0x2000200181c00030401181141c54055444040034006810021003a99603a401e82100701074904010340a0002d200c90351f1540903081a40e04081665502c5540401c403a00114100041c07107101c2c400591102c0219403200035088039190586442d039a00400b04010001d055101041841e2294036650740c1c1100c400c07414810411503880081c1280115403051031044003070700c0040704490341e5003115240c6a0340c4002c0d00d076284c03000c042454000c40f111204401000000060003000714400e01c800c000074890441c44000d408130b8040d080c000c0c0c412040c81000f080d000649035400840d0032900650072203043c02d1341d0b500000036503401504146140d03030f0103106102c5900c0d094064103410040c2814038804110001d000100080d405129413480f84400d03c0042400d40856140008001d13005042141e03103548804804130b060348042c6c1114107610444d009003008031510141c582d0480d0b455650304080354502821a4080c04035403001d000c00600402c04d010344c05001344903006460501c2d0a803e4180440719a10742d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 675979280 1250 675978030 675978041
    0xc0b0d060605030405031602040e010c03090303050a0e06010b0304060b12010c0f08060f0904060605060a0207030210090308070305030a230402180c040b0d020906030709080709091203051302060d0906 87
    0x2200b400024000e000000b00d01000396030301401c080d90100b034825040d00002d000b600c0703410401112546400e4030301040c580e040d00301c26805400f1b61805e10068861010600846064482d0715440c2d810100050185554840045030410b000c6c040200b90900c89000007401c0e21004004460300da0740d41ca4480da141608245001e84d0701c040c5040a403807525009003c10504c0c20a034004611404104000408108050740301601800c0c02801d510f44076209600c0c06940c032142d5020aa101d0b408810b10403140512426209054079402038440f410022a42c1c0d05480542010340201c140c1620f40722007450490196805106212208a14844030305160060001306100808580f10268100c4100440880300600b00c4040f075148040c280e6654006003000740090140e2020a82d001d10b001040c0241135030700410104c1601d0703003141962950796840c0001001c56950700310003001c9100c400314690700c0c14020361045911051048039154400a5540000c13240d0b40044400c22304241c2c1c48040c078050222901c41d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 675980530 1250 675979280 675979289
    0x318060c07140d0c020f030f010c0c11041b0503150d06141803041403010b0603090304051002010e0705120307140d0e270c0d090303200a090506030604090c0b0d06 71
    0x143c0b4030b84004840040c401041e41202034002d40700005410381c241c0b0100700c03a541c00c14010000700458200010010003d102602c0141c5c0c03503018244449069260912803402c11000c2c031843e088031107150090940b086d030401852000e14405250f0085000c2c1c40300d910030310482e442900c0000384003a081b580d940e1140005018504810720004c0c41400100d030010484064609220640340301c0d1200600180c050644640142d81140d004802d20070504000406031080d01e40c1120041c0e144c03100d8100807401ca4601154040940d880134900304090b0800c00c0b000001d03200380606903442e105290b240d000c4100308141c550b010a81c41000b4910482d9407220b040540c01c501290903051404810b45110101c0c002000203132407244048000c00d0300c203000e0b801111084034007134400740086240e6080c050000d0200b4085903110354004d07500030243c10000c0c0c3c11030384107005584070300b2059820300e810321400d6000141307d04e03000350391803092034049083c640b05040105a00a2210f80e00e10341540c5000c2a0307103c1e42e02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 675981780 1250 675980530 675980533
    0x20a3b040b040201081017010c110303100504020a0e100c030f0504060c060b01030e150109051513110c010f0e1006030c09020f0906040b070611041a0318060c0714 71
    0xd1000141e03800340042d401a0b024038154089031503140220060400660040100380518201d03030f0b408a60641081540c02d200ba04d51681d001d4000c0c107195180d101c00c03100305240d10b95088081c0030030701c3e05038085c118240b0f4a00e88200c00e41e2500000c22000c102184d00700000c50f00c100a904105580044000c03500c4400303141a80c10246010405480a584000014882d68642c080000300e44d1099120340d050241b8142100c3d0781222000484400359401c0c002c0444e50780c1800c0000d051641b1120904110311005801c9841d20000c50742071000034440725072620790a40040003c6000342009019007111030030b640800140c11500301200d149403041c0c200914411500b03003501000864030301c400b40301c11602c22000241ea03e079165200240c8a02c207150b80316611600110f404208680f0180c0500f003040d1061400704000c90f4001d84150080c000d83c41412003c0700001641217108003020051504004091900000152078800c080c0c2000341c1190648013078540462140c09002c0382988141c4000280310 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 675983030 1250 675981780 675981899
    0x406021905191211030c04060305090615010c020a23010801080c03060f0c1603050306030c030f03090d080705010504050a051506150a18150e030c0a12020a 68
    0x441c1d20340b520100900c00e001e0200c1078441c5090348241c0d4101e8561a03150043c0d05542c0c0c5000c1803e001c1c10f821900560b40040c3c645000a035003500c0001d0840e01620b541e4400c0c041c441d4151f001100d1011103140700701d8000c01c0d6408005a0b814a282c101b0a880380c080998401c150090000141741c42d80582c0000c2c00c540c0403204545075034a0114815802a51070301126030302d03a54100304171001e071141226542201c880c0c0e0a0b00c0003810351000195004020072030590b5800383c00d007020165280742150407040e03070380c00401800881740b801824507403c10303100c2d590705402c0640580b00c031421121704480944158200da0030040811000340710341c00040300708071a9000f0310708110f00882c64140c3c105203a007094800c0020201c00300350040403004590a00b507820018400d0315408007603640660142001c020400c8003d0401c054607010450050b1004050005141c5500c4c003803c0606040300c500c030980c1c108021040129582182010030b0006460440d201504201d541000180d540d400070308000b03210042d40c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 675984280 1250 675983030 675983047
    0xc03130f061b020f060a050708130914040c090510030f08090103180507091e1a12241b0d06030209100b070b06030f0a03091d0906180a08030406021905 66
    0x2e0340703440c092420a99071700b51159040042a210f034420f02c00c000c1d001c008042180c5c09141030051101d0181c1d5002d00e4103201206c41040500b40084050b60000c0c00c4030000c0c2d005000e0280e0f240c2c80580e00101da61401700c0065500d40b02c07984010001c40090742e55030300001e131a0249581501504030002c80b41c2090b6070b14008a40c03038080d01d0f84258061101d40644901d0096041a11450139100b201c0010740b0401a05410110800424004900e03141c061050503101904030300001c601c0e0381d44d41e020080d00100518230100145080d440082130311980d00e00c41103060b4061880900549900230060700c00146003820f600401c145400000e0902c040300700102018805541d501d001d4030b400e103070b000140314103e880d294002401c3c140803070308040c014403480181d0410305510169080031a944a4903d061107101810b042c1c0100900300c40342c0580368450b002007001c030544001c1c100148001c0805131000c00c1c41c1c40d6608080781e841510246c0d0200c1e00408c00282a01101034000b040808a08042d8a4613402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 675985530 1250 675984280 675984289
    0x20c06042d0609090209030a0b0c130608100e06180f01061409302e060503060103031419080402040b09070207140a0902030a09140601050a0302060c03130f061b02 71
    0x180c004c0f00140d980225800c0c625031010825441802da010502d00764a2811a100d0189070300102004540e5401c2c00c840001d4043c082c02415005600540040910b03a05094000b50001805085141c1000c58603500c540e480c00040d0b2203a0082100b095030703842e25450400014045c0e0750801e0382440d031100800411800340d441842912130715210404aa5425060842c804510685094200c550340100c0c1e40061030520040a99041a000080c40c1c4001140d00305280086854500039290568000e0006001007030141c0d1003440a100310141e890301d0a4001860320030039a00b42001c140114038294240411854503026005038020195000c204916141c80d00070364039000717485251081840c205c02c4101035100c5140f02d80207886000b000703560703e05046010800811030b042d03042d1100000c61210358401e80010074224101d403001080d18044900350b400300110f55010101c20101488100b01c0041020035109915009000203803100041925196014110300346450941880701c0141c42d129005030b8a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 675986780 1250 675985530 675985547
    0x504021b060c040602061e0a0b06090a0e190b060304060527010b01081608010b130504021c0e210307090e090705030111040810110c15040507050d0809090403020c06042d06 75
    0x6850308c04214905200b010401501c03910700c80540185c21514042404c1240819080c003510200d0954040c0401c8032840c50100c810300048150302c5601000403401090160700a190000300ca500803c06d140c548086044031514000224510342c0d44495540d080341d81c100b10007a510a25580e0b44201c0490300081c0140700b503a0500a01c0480a00403a901c42d00322648102540948000707402190b0300d0348038601440000b9054003034014400e0810503444288400491904c0c01074140c802103121040000c050780041b90001480c01c4208120f09800095a000007403225014203102c00150074514102014182541d502c2c00c160bc2000004102c20821000001550a080000f1100c006203400d5055800d61480c41940150515403003030342e040141c1403c103000303114000d40c402c40441d0307105940d580901217465091803024100540a00500b0308070700700707001c000c2d601510910588203810421400194581c00c01c1e0484200f0562540c0080940c50b40038500d0800b0000f64404803001ca40b4140005000d0315 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 675988030 1250 675986780 675986791
    0x317130308041103011a090c07120f170106030c121506200102040b1306030612020415030203010f0e0f01060b0703141306050909100509010504021b060c040602061e 72
    0x72080005814001c806010449440e0000d000780542c61352181d0f891458480403c210344903000c0300c030100702035040030402c03a0079079948001169103000032910240c80382081c200007002807281000c1010046080c12107014041e09540d10700040700300850300010700d400c088401c4101c171a441d1804031400c4481c0591321038102d038018500103250901ca1052142d841148010107411913002040c04070307100e100380d4054a02d1000c40300324800510368514044058031014442c0321001c41d914184903015007040d800000c5211100342c445a100d42d0340f540401c0c02c540c910f03140c0c15203140e510002d0340313501e000510a0000000c55900207111050034808440080c4c030414100070140a03190004800782071008042d01c6004400380d00b07401010341e650300c0c040c1a581c4500e012610440020001420005141112005440010740b0202c00741c0c1c07c1406001c02980100548a0340507600d000c4404a244100301440c82110440300680d00d4601c0e249000e0702e02540a410380c2e002040b883e43c0c40340340000740d055195100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 675989280 1250 675988030 675988037
    0x311161208091f09081602010f020d0509060a1e050a09120506061215070f030501080f210904090c050909070b16060b1002060f0901110d020702010509091303171303 72
    0x11a183e11000c070080c041c01000429800c004552202044208041400064001c0c0c03588240308240c0181240c07101a94011540401e005200f601180d0030000c2c094641031185043c50401e8007804c0301004212651360183ca40010340006050240507404090400142a40c962500c6c0c014150340c1c2d0a41c450347c1c018050346c062500410114000788007006040443d444405c0f07070480c6400e01c02001004010f40b4450303900401d013008000508003030001940342101403000041e00c031400c5240041e003483c03010f03403070480040351043c0600140c90780c0d10320a07045da0764400c100c2c5610070341c50031051000d143c2d40209403002503000b0030803c0080052070000c42e001d0240305c07114500b000803e860080b00802d10f680c0c480e038110b60b0850040461030740009103039001d40c80300c40c074400f02c687c2e9510700c4a083c2c481c025102907041c80c05014012250101c0c0c0c0261144a10506081b0f041c00101404204c80300f904440d18481e4502c0f101401040c150030080e036600034010102403144914018111100e5002041070040c00c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 675990530 1250 675989280 675989323
    0xb2e0501080f0601090f030b0403080609012114030c1c0f02070b1e0a02101d0a0807060e030f12010608040b010b0304030c3509030616031116120809 65
    0x55030700c00c0c2d40f024040c0c0040006c000695882e0b003000c08882030222001c0300400d0b80d55004c1111072030300d005124100d0307500040b44031000c001d614001501c0b203416403003100c1145507100f07000040f04040c40549900700641005164004001100c050301010620ba044107001001b0001940704d42e022500406543c00c130380b03025545062800c0b043c1c0d55400b1071810300c0c4d035079030001c264a40495400f0400e0040a281114248002d14007401c0304500c0c02141341c05c0203141d078031004540c1c4c0040d114001925502d80200c1001070000c1d03d10382402e05503070241c10f0b10400e10000044d131000300d1301c11000030b40c090500752074000d405103001c2e0b4034104441b4042c083c00048140200003d0704040c4142034100a0f00e0b4861268101d201c2d600811044940d150b428810050b020100d503003031646500f4050701c0d82c11100a004058540702e40c0d0a9a00f100c407040140720415840e10510050320032504003e2045101c0c0348510050740c085030078074440d0b80c0c0c0c0d044c103400d04201c1c10105104d01100c00103810708400d0042c1706182072 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 675991780 1250 675990530 675990541
    0x30203040509090c1f0e0406060912050f0109112b0201120209040c051803010b10110a05160911160204020f070f05010603050f030304050a031b0b2e0501080f 69
    0x10f815480c1002d180e0204017802040800407446441101100064440010582000c41000300b992480d026003000105034880c20006080701e80801c40c84103010f00c044e500350303100f41203848d400c0d1052120b0940301c080c68080b020259007400306000f80055034000202c905c0b82640038003e080c201c40d00308042d041041e1080c000b000c04040380c1c111050400700030401c0140b48000800500250841c4100c402c0e80094007082003018103041c02210000c25008100c1a001000303501d098885000c0492034810b5482008180c50002c1d004014a14811205a968040702d0b45400c2148003aa00c40241300f00c08010248031080e044241d0701d503204020350303048070301507224072100c0700c044d10328007600310042c1c00202180010401d0000641c02002a04c3c09030080d41e0300001100625036491009480040c883e030711400e84040803c4c410602544182d82481902d03115914030b0329803240740c0d20b09a40f50343d01005c40b40b282d1220078054503007100c40c020240400782c110502c5c2c040082c0c0307050707401005810741c0c2d10403000040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 675993030 1250 675991780 675991783
    0x708120711132901030c09060210021308060a020d050a06030203060414030d0609020d050907231302030a050709140a06080606040f080a061401120303020901020f100e0c0d03020304050909 82
    0x3c528220414007103640c400c0840925403003180b02c2c1156002c030346460000d55403580700d010000d059800c590014110113510500038002940540b200c01702d03046420b5000324070300c0c000744261400b90780407480c05a118240607a03108111440074280d100b1083c5001c404000584010805a6000382c01c44c01c1c54419040c94510a821071040c0c011000c0c4240c40c107000402e1028072035014000c0700004201c2048180e0340c0e80c1c6282d548440314020801411490280c0110960701c500d036a00242001514020134141c4184940046c1d8000740c40d01d105142d04d86041160480d031040340c07034005211a4082100e80885100402c00d0041103018140070845458002203c03074491790202c40c02040c0501c0e0320080166580ca503613890b10105d03002194203d01340008400b034190a028043e0688071206c2002c812195035940c10f500170352201030030764154010709044041c081d909000c85001c554440300b020500d107501182040c00e1175001609a48101c4074000e21b080071a6000040e2010785d54261240c101035250b00404a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 675994280 1250 675993030 675993041
    0x6060a080411031e0a212f01020301031406060108070e01110c1302210903190e18100b0f160201170403020c01080c09011d06120405070812071113 64
    0x102d081031a990041810a000004e10546a90103800403c030882e40d10b500e4070000c4c450414502d000079008201d84000400c280c0600c402c075840c070004054000507048801f41c2642c009900c00c1c3d0b450b151410303c0c0e0124420502078a6400102445c1507035007031501b01c0c0041c00d4000401d50240c1000244400c00203441410458446200c800070001140c0c00c0d05031289e4406035005015000809002925008016007224a0302e405040003801035800c000041c011103074940c01c640112030800040c04041282510340a11014403180d503541c1c003942074942002c840005d0402940b10340741c1100300b0001c80c424a1000c80a5030f0745004402c040702c22250480c00100d406081180d070043d140110390b810300c000c154000517003800b2080e0a0701c2310112640c802c54903042c2d6000d941d541502080c031070303c404c140701d507050ba03200e040e160001013070070741400115840515090401c031002c031881d03803002500f441044010400450a840c41c50b0801d407074506555250504c604480401a00031070414201c10215005908503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 675995530 1250 675994280 675994303
    0x151d04111503010e06011e0906030908040905190e0a080706050402040e0d080a0c1106071101020c07031109010906030c1205011b0816020d021b030a06050f01030b06060a08041103 78
    0x12642c8a586403541590282c409940c00790205030956400c0e103032500001503c0108280b030b600c9505d01a4a020b1050700130b0300310a0401c40c0c000b24101700105100c1c102d84a514040c80c010301c0207550050070f1104220440340c00303821032205a40072a03885800540c621048401c0241c0c011804607440e00d41d403000c540500740e1841c00c00703040c3c055103c3d4043c0081d40700d0410b601c1103c00c00c1082c810010501c1e0b007601c50724000d090070046900400001009a8050304401c040075800307400040c03401d12941c802c0c500b4003406800888902c01084904616031400203003481c0505841e0740d0030803030b0071f02c0c2d80ea0f2065540e80d948202c0015180b520014414041d0a43c080e003007150300c9284c0c2082a44440000074003a050403554220a04c40e4407010043c210320010321000c5600c134580080903200e2800003121840404007154642c540705000450b400110030f0702511380201c0740c1d03614140391075056103820b0007000c2c0300901c05800b4000510070b06110b19071100c0d2250300290400800341820060300003080c01c0007080c0c00c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 675996780 1250 675995530 675995569
    0xf020405071d090c030c28020f0c04020f09100905060d0b04050a0b0609221410090216020d020607020312040812040e0c03060604030b0109151d0411 65
    0x4010750180c02149062801c03a00b90190b90441520030100110054207842101074610180001822401a9001001d641c082011100300e50100c038150040c6d0003180c1900e05005800200c8202c81e01c00b0304000440b01080d00320b60550901c8504030746103c490003806116407092a0b043d4074084440d0051600700090f041c042c20703803552019070702542d0002d8081076401a00030303490080000c0d5111078501c580c0c11079000043c1075500d00311101007003214031601384c103055135444640154842074414900c07903c5d2840ca44c0700d40807041403408051040203c42c0560001c140746004010030121500710304002c00025a040700da034802c030a000c0c004039280e405070340e000a4140c1305107803042d2184003540014000300d4505000b2103180300d85501599050780128801c50300303030060103000308a40c0d00d60940615031290300a8070305130800b641c98446450710102a80540b24036030303992003411108441002088050460545c2070480c0204212264240d210001d1020f06074009100c11403460341c4e0784264020310040d0004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 675998030 1250 675996780 675996791
    0x903020f0c15070602131e0e070e0108010e06040b0904050a0c17031c064b030204020904142805042001140c1f0e060f061c050606120f0c06070f0204 65
    0x1a0547d00401a030082c00b804003413980010710031034030500705000070160607542d46405928040c1c035030001c514090030303155100341c030307051480c00b9501c1d4480f2540c4642d00032001000020000d00704400029015000390300c85507d22190204010000002c9440000c20003604440c00b81400080e000184800e8114074410320441c0150714007440c20314008842a91800e240d4070038015281149007088017074107000e48100c0700c4060204050311b425806015104009000400c1c0d41c0d048510702e0100141c03c03540411050140f01542c4042195003000b0000050004020003039402c15498a50010043c9200d121082e6050345030304507203074442c4d0440b6801c6061090050340302d95444c504183c40e50f030501e842100407070010010702c84803209401a8000203260742d01505e8192124400c0c00140b1074010002d40e04880e01000308641101e41d00e83e0715003070a000e007024000c3c0e81420b45c00c106220300340c0070510303181d984028404136401c1070200c0d0b81c0701c40340e0341100e0305640c48401e46818509030424001c0658000d2409 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 675999280 1250 675998030 675998069
    0x6090213020705070902042714010315050c0708041707080d0906031118061b070905010302010e030604121b080d060602120304030e060705010905010903020f0c1507060213 75
    0x350090301c141071242058070010f40d125400d1500b280100d00c290a8503104030140030b00c3c05026001c0c0e0f03101c2c1d6030230002c0109411000380101c0503000ca013070b40200c0b0801e80c056090544880e0501c82c2a810040d04504030b8941269500c07601c416000700c0c01045c040000030071b94140385240400c0200c004101032000e0301c00c10034581d440584800c085106030360109042500c0407200c5681c1e4400c44814009650b03510f600c0403241c0080c02010382010500e040703030101d801c03100d4862100802000000300382120740460a981940300040289400702501c0d4042e070322034028040002d4000da4241c90000e0b20340f411846c203102c64042900300c40042c05016191640000b003520342c0903010340011081d00c600b9022038403504122112034045100c00c0320007a000400c000c0142c840351624000524200d4004e9001040704c1d80c080d1150b070700312001250102d000d64002040c125001c9014800052010812520a040c01141c55a03041c2c20384a1481c0040c001e0361300103101504030002920300c074041e1411381203691202154 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 676000530 1250 675999280 675999319
    0x1b010f0b040b0f060414060d060306051603051504180b040f022e1409030f0115080c010504050f031e031c0605060d0f06050d0308060f0a03020616060902 67
    0xa044a18040c0e81441d010ba005420034107545015580701601c0342c2c1c90700b841c1910312070205001000d09544110108996682480f890154101950007150002114140300d0f002401c00f0300c8041905003410709001c10444030260044143d1a51902a20b002c2003071050011070340c1080141d054010007450f00d480600052104551018281c6071080d148000c0e41ca10b0004191241040441c140314802070172001c09407000d01c0f500390400624500c290050520345d200c00000d041c50046518481d5980d592000c244040d05c28400303240042892030081c00380034851000023001c2d8400da0240c1d5010342081820500185c17420402e070860b0983c040300e114005003042d0f0740c25480e03074025131940039408040500a60701c1c281c940300d00c6048a01c01402c0a2a0014850204001d05041d80c1c50030409582c41c135002a45031104900c244146200b90303900865880c2a40412604820401d2014011401c10f032040c0016103403841100d03141c0051078042030061170f0364604038018280c07880000750809026203202859030304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 676001780 1250 676000530 676000541
    0x9060306020c0d050c19052b030b0f0a0b1c090b09010f0606091412011a0a0801050606090904080903030a050909060904120c050f010c05091807090b1b010f 68
    0x1291015101c4034000400c08603014080e00b00b600345c03280c024401c450044540c641d592030790740d44a5001d07180714a80e58501007001004403407031059408605908040750580c988a80903100b07008940e85982031002c034000c51105d0701760740503407074403c0000a141e090f0000f800010941840c0c07075140c184518001441e15514601c0b05884600c201d41c00c203207050000d40c000c3c0c051348098450b03560710362003440e103405281c59030010009105a00031242401d8000b52000038080d0b20404400c2c202403101f07041c3d041091190003207103940156140d03450282031103003e03a250000c581c9550400c890300c1d03205841e94242940c2510502031440d60600c4005001d80920740c010300a412410012102620706684600500540c840304480050040c00c048012100860252030706282d1507020f04203e841d07031910664028215244c0034083c601241006c1080545807414161216180c1d42062000500e4202046e02400c158450301924903c1d02012800845074000d0450180502020000030700074401c41e805e85100524 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 676003030 1250 676001780 676001797
    0x3322230117031b280206070b0a1d010e242d01180e0c0904060507090e19060602030406020c131415120f0a0b0603010e06010303020f0c09040206090f06040906030602 72
    0x43c1c189000da00b20300d0600380d01c162040e07006040c3d14540200c90b96640088e020060206c00c95654030080010401810701e03801d0901034004000083c54600032001761b142c84600c0301c2c881e42c0c041e070603007005801150302c02c91540c00114048084081c001200002c079040800400343e500c2005418000141c1e26038500781d030910038007216000f00000745441001c6030711141c140c11016003155501000c100003a41982c001d5500510502d0040c24007600c413031a040c84110b00b070f6111020081c0c00041e100d4020907511542c401401503000651600d454001d01946900711554010310a0803070002050300c4044030317008002690740540041d21189002000b5842601d010801a400f5043c071500d2600780c018000340c095a10024000101404122503a82c11942180204030f1350300b55413181c2489034140020800340d4080c500c250080c1114540d55400e152030071800002c0380348546c400c01c0902c0b0150700c0381000c840380d210b001e40f03000c014000c3c4c40c4085040c510440d884555014039110001003880301e2640a440480b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 676004280 1250 676003030 676003063
    0x609030904050a0c05030f100b0408010902030f01021e03061503011203140c1509010204080d020a060e070513050a06050306090102070309050402033322230117031b 72
    0xf5203071a94401e0440d550403c003440420410404209116a80801035074000c2010140844403901c4c4d0a15052a400c03941c00f40310f850791150041000c5140c24480d03404034415850003182042000400c01072404285512124140030020100d030303094a03041040a03201e0010740c4055902d583d9402e480412030024003043e4005004400c08021803003024040f110580b00071380042855400400b0319047d0b4120140c2410307d95075013040000f4540f9003e03c60614407804d59000340c040101d003410403c080c0c0c3d480f8800b5040c260450581803080b0b5480d0101242c08003201d0f440001c00b95901c8440f0b4004080c039410040c2d140c4107060401c880200d05400a22400d0711990f03075451110755550911045c1d0009aa2000d0344644469040e4110082c181c4284a60700108902c2d520020710070001c140c83d1040d00c443c0380b40e940e8a60003020701d11840b41c094040740c0480d03102a030f81c0c08000518880c0d000d050600901c0840301d040d25a100013042d0410940b0f0181c252040d107110301c3d280a000e580da8a00781c200c10020741 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 676005530 1250 676004280 676004291
    0xa031d060c0f0c011b1107261e21040303091a130803030a0f050603061f0f06030218010e15131e030c0f0315091a1302031c0c170c0609030904 62
    0xc8550204156088801040c015010031683c0300001d42c0d03844400c0380c00c8c442c81c07090040c0c107000181c01880000f0340d50868005080d81801c18028056a142400c5031002c0e0000300700003c0002076442151001190001101c1180d60592810b40f14a54490103044407219480840046040701000c0000d6020b000d54500030800940b410b01c5403003c0d11811518141e0540055000840c0b10300406803040701e041c180454003028944800d00d5a2111086411001c00a90301240710403803080418001e8071444000d0802c400c00368202000604049015503024426244c081101c000f01d18030512400e015043c1c1015481c1080f0a14000c1000c0d241203220941329110784070000101d4142d0541074005076904099284040302c0030307051440c043c080d5584d007141d40d00c0304500c0c1c00940d00c524680144c01500091510308120059004051400413080b11099800608804c8607000e19001000503041c01da0018003802c09502c1565800994000c5a440161a000d070004110303c084020004007201d8104803010002d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 676006780 1250 676005530 676005557
    0x7260c0601142704020d05030310050f010318030c0c0504020d0207021809060c0c03132301140702220c0903050616050426030a050a031d060c0f0c011b 66
    0x1801c8048801c110425280980402e22440c4900b107a94040d00182c651001002d80380c0d40e02d4131310360045542b625540e020039011302581c9824061844503a0017440c0034031400440b00c241050052825070014203000d03078504100200711a000c13140d8000e0000920840d10780c1c845050407000380d0f104c01c1080744a03440040c0080320343c90009000501a00d103400042c000eaa5461380045110f034070848103200144414801c8101c4852641c900002401e00741840030707250071007442d80d0b81d02910001c071914113015016140400301800d01040d1003400750100c0d9500c040c20440320344000d00c03c5158600081c000d0802d130400e042103030807030210b4085070311034400c440c00795030f4421149411882001c01000080c1e0f0401042000c80305424554240c1103d103a11040203c00494182d85917901c4014410040b17000460705580e05a054030030189860107461601200311441080c44d92506d00040800d56110004100c1311320b20b0f0620010758060b000200003c001c50401c0000400b54200c04440e4000040e1204034601c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 676008030 1250 676006780 676006789
    0x1302090a0b0a0b12040f0507050d110111010b0906060d062319060503060f042a0e030c03070603052e05120d20030702062a0703030507260c060114 64
    0x411315500744200e80840d448540e07946500c0701d003a00050300c5034030410386c011401d642c40d4034007102031a201b1002d02032922090310015058200b10050a170031039261080c1102c2c1c81d21481845039100302c0485a2980c3d414540f4480380041103650440e0703030018001401c2e0800d50a4900c2d0303903d0501d0307085560405203400705204200301c240c640605400920240b0124130bd03418405400b80f08440b0080000c43c1d01d1140344410082c40a88881030860482403044c41006587c20034200c000b1490260040c2000c6460240401d40d02c3c50240b0548040540d21030005152004440080440c04415900c24817000400c285130f22100d4440c0c0600e40c482c4103540c3c0d104c032400d180000e074940701e80415203d015500780310400e51185009150700003d943d00040199400603039075480100751004007040402a03104a5001801da46241e002c1a07145507400004c00b0710200e41c0150948106580c0a000d80070691600c0a150341d4458121514500f0318801207160382d440300e4085071060513210908680301e43c8040580070407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 676009280 1250 676008030 676008037
    0xd0b0a030f02090a0f140a06080d05070212010605030318040b01030212060d030203160f0b130f14030d0f1a0a050f01200d080f071701050105031302090a0b0a0b 70
    0x5103540010904100141442d24411342c1c072a00e030290008654824083c4482a81c4920b40801c02500c0b1201c200502c01300c0e0303440360201800601c1c0007041300020824001d401481103d502038030034841621044129602508800080d25000d41525105c0c2d500f00c85400d240801c81e1582c0c3d1242e82000c03070f0703441554848e02c02e50b95801c1400c440c410301501d4050900010a112030415001c6020412814441c80d114088400a4600c00d05000000704801c0c2482d07105508042c003082e44140900c41c0c40c2c030110348003a1007803500741d40200c1d1100546661520041ca144512a00c1c880454100300c00100f00c40e18030350002c5d6640205900071040302c0b40b16420011004401e00407540e02a80c29580381c45194803a0403902d100005483c1440e50920307003440090b03c1c000c1034180140004100204101c00c03502c0c0815165040415401e043d901e1030030002c00307580c541c81d050041504004010000400403c1a004150301d8603801400441d41e0341031480d00103000d0403207212503034062140010300040f010500c000301c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 676010530 1250 676009280 676009283
    0x60b07060c021902010c03180609090f0606020307031803051f05090c060f0f070b09070513050903030112030c02190f05030f030a03050606070c06030504150b0a0605090102011d030d0b0a03 82
    0x800801d03d0039801580d0309140191b060301000b080c440244c81c0700800110100c0500407179168003145514140b040000d4541d20300c4d1001041e41044420402c181d0004140d0340b0a41e4035040101c400a1614403114070344400c1e40c4090110300c114400b5240000481707400401d540e54440c02403045640c1d0b000b070180d8603c0c003074950310b8000b6005c100035040ca0740440090941c001c03508691600d00b088139118000b45a50640d03010100303800140040006280103c88000350468242d0b06000900d0881a0243c42e130105104034401d003aa040e03038103c100f51282c1850b15800d0345c014031500c1d040301100c505d03180c801d88902030001101910007010030640f41c0000c440c6440d4000c3d2000f507251918403681100074040261049400131030a10070800002c0f014000710b07001e46080d0b42c001a040ca800d04180300d06046d074003000c01089c0e10f0100c0c000035a44800064000707480c1a801c144d551102c9110040f40103150f0950400c0f40702c0c044802184e05500040018a00ba41310503005000c5042c01004000c03511065100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 676011780 1250 676010530 676010563
    0x60d1502281e1101050405150105010903030e040504110607030f021b0a1404110c0a0203150618040201050c0d1808070602030d110f0a0f0306080c1008100504060b07060c02 75
    0x70107005140c0a28041402c0024900d0070300c0e40e4244840b141d07401d40b03034195011245a08003c90302802c028610088a004080900c0c00a515920b1518060882c0d050011014081c03500c4800040501500402c803140c0c3c040050305050383c92a0900b8020822240c040004005000781c0c1d05015003c400120b40390004140104500381c1c162600440c40d824200030652a50030544070f0907141400c7c202c0501038844c5a0344030b0040c02c00300300310b03104050426004000c0700a0480500003441006e0700ca02030608200d020848840c4201e807228001650305000790482e02c00c0da8414075850b60346440d030000d0052480090240a0015151100c00480e00c810280c025600164424460010f0101440e048000c001140c20007252800c030034032a030a00e1644c0030b10705d42c03c003041456800e030307070226410320032100288028000341c01801c0314500001c0c500400340700010104110302010400c8800244a40f100420005000b0844640ea4031404102d0b508101c81c06d030b80f654506044001143e001007503101111441b040d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 676013030 1250 676011780 676011797
    0xb01020606061c0b0a030b0717041106160819021002090105190e0a06090503100e0706030c1710050102060708060901270f05090d030e1203060d150228 66
    0x144060b00700110103080c0d0f405a5159040e180d110b0b1500c98030700c009580a01442080c40c9022407028003a60040000030160603803002c100310104d8903111800703140580440703d0981d9400007048219203501c003140301401d0440d000501c0420000040242051058241c00707641844074450410000c90140079103ca0100b00100410381b401521030048000d43d600e02d0400480003040c40d40403800068107500503401203451008244920700d4200000c220343c102c9040305200041100803a140c88078505d00c500400d141d00d43c040502e04900404a0230300700700c04c9258008075403400c080740109400d0f40388902409030246001088c1f12910032a0707007610840010781460004c3e441c0401102040c94540140982c641c1c481c3c4101c200101c003406000e89644c80705201042500344050710505003012003610f0341c203140ca842d403103070083c140101d107400b070020030841000d4480d80d803038012907d0b80300d1400c4007e1040650b07d40500120046902030840030f451100284400410305000d090701c80c41440c515800301e041c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 676014280 1250 676013030 676013047
    0x2010b0a140f031e03070b0108031e0f071b0e1321141b071d06091e131506051807020f1915050c0f070602040b04030b0a0b0102060606 59
    0xc01d281e02404002034104d4560f9041906051203800c03290b0003250ba96080042c21009106840d200e05000d410608040e61600c2d05c0b030000d403091b60382101410303141e40c1000b081c02ea904000c800b0070b990f0901e800007410b031002d0a03800c14a02000d10307075010f045412645040451207603c1ca0404055807142d100560384000000041c1214240000103400c0c02040300c17012242d503540003014003030024403e07408000c0004544502460382445010b0700240040240c4c0025100ca030341ea500303130442e048041906c0d01580c0391180105031241c90528003203182030050240c01e120000804150f2014118002c13001a01140450748100c015030380140309165001c0c1d01d5581d4441030f404244803158201c052030040340c10711521482e41605009001040e42c030f0a5600b103081c017041c000174800d80c01d9500e00d20641000710f850250310040c440d02403509801340703240c0c0c00316840382041840d90407100640480031310241c81d1943c07490a503074000300441c0c011040d10f05100c0c80c4000c0d5400001e4550048000412950402c50f01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 676015530 1250 676014280 676014289
    0x140112111e12060102010b0a12050f030a021b043b01050910050a0b1c0302071a03041208090c061e190f0906050318010b04110a02010b0a14 61
    0x68031255104680070440310301100ca46000c95800e001c00000e00c03a803102c10b1a8420600e000d4010a03080c103590404041d1413030355540042e00020380e07039a113104d4600342d440b40c20100d1802c010200c210384544400203032000281e0300000d41c2d05a00301c0c1d01010495010f030820621082c4e505e2942d10710b9000801045d180740d80c84142240400e080186283d003403025501c2a0110309407107095a4240c100c2c0c01000d03440070040d503503001d03140e80071b201030100348080e505100110f0703505006143c200c0400807080d04010105482441980700418512000b801e02c0c41d41e05180580580c0251001c0318001c0814480795840ba01500c0d0807407049954a02400c000610381040c4601c5a0020710b8950b00c0713401c3c80c8200054100004050144450203040c100355100c107041000d45103051201000781032015903401001541c1d0f00a040325840288036156100d00e05152903518050072074a03249039030190030849042005807407100074151120f19540240f107940c1c02003040c0005403200c1c0c002c01e15002852040101c59040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 676016780 1250 676015530 676015541
    0x1608010b09040905011a010201140103330203090c0f100806011d091608060613050d0f060e1020040308090a08060c0d0b04020c030d050a06050d0f0606140112 69
    0x60140020910803866503901c0e084400c50307245040c1281c2154144122548e091056580405025207005015419500c80940103001310f000c0041c80784041c285030a6504801c81110741e02d40f40f081d07080d91030f41410620b0640307911421481074040c024201120000d031401204401c0c026515464910081d182c1400469804182c6409290a6174203000340792002d80b2000d445a10802c0c01c16144507034014800001401004054181c600c283c0040c00041d40540c4001d03c030200f00d6030112007010035601c9902c0c01d4202180315000107881145032032a6500340c05004500071024140c0b4500400010700e400d0a4031032900d8100c030b01402101003c0c002800007482a200415500c08018081d91200c1c0e47d038943c8600d050400c4400411000c0d0101b130b08441030f1510b0064003100c450845043d400c080200c04000c1d0781f80110300c4588552500c03140840d448800301d6000344080d01001d030400030400c0007400d04482d03281000108950840c036040b40020410300c9a17244031807580c01603403040326021940011802800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 676018030 1250 676016780 676016797
    0x30510091214040f081b1503070c03200303151e011101020c16080f060105011d04090204180b0a0504050c101205070e1201200a030e030a0201050f1608010b 68
    0x1c40410010600402103500700008080503401040c0030703000d4901140c4442c0203100c0c46c80c090030480000296541d43c40301034907440340d10340c075102005040ca410101d40000b400315150310b90749500010400c0384200440110301c120055403445440141c2031017840b803101e404020340194606228043c070401c1d849140b0607542801c1e400d002500b006110040c1500b88100c0700c0c06204800c88120040007840f00c180700503e10100a44050076480d80f4000000e46802c4581084910666801403242581e6440d907001419031900a002040328100c0c0314158180c41c510500c081c1d409600c0702c00024181009402203900c20ba83c848054041d8241080500000041503960003050084510b0420a50691481071911a000c0c5950340c4480d48200014440000720000300b454890341800901d00381c3c45403002d00701c0441c1403c8045203075103500c0000c049008001c281041c07845c034000000c215090650540000d03004402d54420300c2c4180e22540200bd2046004c2461301d00443e09440042016841e58405420400c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 676019280 1250 676018030 676018067
    0x80408161802070609080307030c120207120e03150a020301050a050901030c12290103150b030a080c010b061b0d0f0e01182403180c0b031b0309070305100912 69
    0x40302071b0f6072044203a41080f550307a80000e036115041036644e580800036011081c00b4000440c601105a145d0300c2451100f0700c0c642052145080e001c50440e102000a8076845030901c00550490415201140c080e50083c402e09204040000010500c0d1503c8402c0034107e0740d020110074055490002418500414000b094078071280c40000f600100070507140e0f1114495603441d90652560541c90403144143d4400540308040c2c2c0743c26100c40c19a24006418480715802400c01c5403624011089070340540103408070304c1c1c0c102502242c280140c001f16035046041084500540e071000e4500b000890300d00e070524600c4000074080c000c004d140755000b0596813000325040c2d005101c10382e440b0521518809095005ea00c840341c2154901e480c1c140d45445040001c40ba1240b1644080c1c0e915191803c003074265000b0043c800d01c0c00030201d840d60b0620380b652509803824070502c0303440e441e190080d651925003030700c4140d81c540500b5101a61165040c4108880726911040103004140c409200311155028451101a203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 676020530 1250 676019280 676019291
    0x150c070b07020a03031140060503191503060b0f060f0d05100501020705060d0e07150e040605011704050f010f090302160b071416030804081618020706 66
    0x104210004091007030300d070794008101404452500900700e6502d910b40d066020760034840311007483e01160b02d1400340c0b40b4507800c00c0d1442072541a85621580903050b41808004500c100003078054005019510408003600303900610314100300c005081d10390300c0b40341d071100400040302400011107aa1001c0825100501004d42e5540d5950201d001a845924944074109002c100300c2462036050041950108123001c200c01d41925040c0040d46d10035207400340ca4880c0318041504401c00d41e1560010032556100d10459004d565194000008000306402d45000994140c5c142080360910b400303901e0803104180e541e100861701400d84c0c4a119035001d0012902409210100380d0011024051000b400c40c1e002da001403880403074a00031b0302e400310500000ca42214800403c10041700f18034295005a60000e400c100d0b91004440f225003444000f03802a8461220b0540100038006820b01034070030b49011604840d211001e003c00c000840000e07204420004140301d01d028100c0d0502d40182401c80c2c81103001052 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 676021780 1250 676020530 676020533
    0x30c06070b06091306090303050a18020604091a030a0c06020709020c061303020c0d0606090609060b0d152c0c090a03022b0b0f07170402040515090411010f0908150c07 73
    0x42d46d2404070181c00180e159000e100c6a90030501c01d003035480d15080307504092002664045070b0719001d00c1c4101215203070368a031080070040070400c05038010f18009054a00c2070701c2900c0e10341d42d071213a40c2c0542e100504c1003410105007840380703208550040280d2001001c003030ba1040169004003040540440031805824031900030307500c8030b404401c800c52007a1000314a01d030421110b40c0172500300f0ba0008040e1414030408001101200c000c84940c0805c07410003055003041038650501001c0325601c070201a0f100dc0c0360b000f0011014608160386c3d0100641d0041d4141c90745940e0411074010f6581440c0d00001054003003005251030082061010040c01560361020350b240451819445c580e6800c0c1da4050f002000c0040355256520b2080c2c0c49045801c2031840244014082d819902c00280000d010380d540314003140400034403520b1a00c0320440140507140c10b1500e40f078004800751a00460a0202c0c11006c680d60a00c2c1c05181010705403400800180035400b01c405a0782084030014042d40481c640400c203040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 676023030 1250 676021780 676021793
    0x20c120309190305190207051005091809010603140f01180819140f090f010206010e16051b010e07060f020a080d0b030a0503040e010b0f1803010b031b030c06070b060913 74
    0x5c08030b02c0c50300503010720741c44d1405009000b01d09840340d1082041c2013020b03100310b42c0da101c034101c00c2d5071b40d0042e0038120340d4410f44c1c502e0040c08941c0000d0803403034020648071150480043c104c0d03090344440000b40001c1a010142451140b00c0c4100100102c00900000601d040282800c9030124840c4c03805c504a40151040505990301c0001c805882e1800084d490000c0c1c20b00030800031440c20300303100802c0258905034019400f8a40a40140b1003070f501c200460010724450000d03202d0005140301100180c26202c19401d00070540400d5200c803d0003000b400161450054a03034001e212010f80281014848075034031103403581e00841b113929000d6551054020795403410440204d42ca13205000547d075039410891741c4684800160b00c04290040c0030440119960130f210280c0b24102d60050380c0000071442400000e001d00018140705405125524a03054040c2d0205083c00a0b103105906035a0036529003414081a40b0482c0b002030311040320032010a8060912146c0280e002103038017550503042c0003542c0c442 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 676024280 1250 676023030 676023067
    0xa14010e09090a06050c0306061e0f04090504051506011409040905060c041a0f0a08060f090421021b0d0f140c0a0819060203100504020d020c120309190305 68
    0x54003a0b6208007400f60030001c4a124458100d05100754090462804900140c040e10030081c045084802c104422254030216006840145000840d0562034948031510200100411501660070b480b17100414240c0e65800c0310781a005400c182c2d01c820300706a40c040741d0601580815580e070307085070340e407104600440d41c03d010903805404e0883d10607956a141c094501c01c200001901c9943e210000c00581c3d1900d4420030460749480c1030390500100d140c1c0c88400240421a07101c0c0c540f5088031101c02040202700424055807000918403245412a02000608a9548a01000469440036411306035000d07890103661419400c0d120302c04802d5410f0340b40e514002c200c8901740c100d0304103601c012141c00135440e100041001420b507030002080c801c40c0e001c0000980c040030b80d1000d000b156000003c20001c003110204038029000c00f510542d910b0046528400c020f5015448000060107034148054031513105104903400741003581e0003800d104002d41c0000042020854044042c01000c212042481c0029403c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 676025530 1250 676024280 676024291
    0xb0f031b0a0906211802031c050301290a030606031a060f0d0608030a08070311121801150b040e0601050903120901050904050106080411060301062c0402031003061a0a14010e09 77
    0x403105d025620b48181484c01032200510200403889030481d03500154010103036411910b14030851800136140024141100f501442c0e07428020300c00140001c0c0d8140c154000c0011244e890f90100140301202c1e41d00021002500c1c841540490301304a0320009102c100c02400c0368000c09400010050f96550800346103a01905400021842c040c0401c482e060701442030011490001d4a2180740100e1103800051150f40200355610394210079090203a282d009612545050041030707800034140c0e03141e002a0010750401d2042c1082204100c0014445512800c152001c040000d0001c040030700c0041170050041e004a03108904101c028451984035039a940030300f500a24441e181c210b240c0c14642032900d0000c0242040034040d14003000104a41a8400203004d4056103004072101c0300320700840e11302030a4540d0480954040d002006010003011038150200449110703010801c981103551030340c100c500180c800c42c40d511007400b0a00f00089903191761084e021a5052405810205d102400644110800d581 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 676026780 1250 676025530 676025561
    0x151509082134060e010216030c050c090a020c0105060f2b0813030302010c020a11210a03030e0f0f030702040b0d0c0f081501050a050f0a0b0f031b0a090621 68
    0x520512195200e091083d0381e001300203501d007090442d15004401b140000040800a0840002003840010711004030284002030102d412814500900c1029400400700e11549510b8140440c800e8505840703100101800903051620030707a485414104000001000d49250729500a40302c800140098003d0084548180c8054501811800d00034211b55154150000390350000c2180030110301e04520045061008036035545a0a4102c0c1d503115074000b10000005141c400e4021040c101505604601d6010b900102240c203640514100280e0713940c1d00701405005504104094400360400d90007800c00490042c1c5400c0c125151541d4200c04000d25070b0114020740c0c0d0140c0c0510400780140001c0d4030300c00b1050b0fa15540303541402c00142c0c1100aa109081c456000603050890b81d403100e00c1840004c2450464064540c00a014140d6484e401103d070000090003040c6c003030742500c40140954200003a140d5601c1c02c102e040c06801d59107499030f01da02c1080341024100c3c10802c0da071940078402c0081904030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 676028030 1250 676026780 676026877
    0x70302191206140f040218060a0806090f0609070b03010e0a0207050d0f03050c0f030606310315110a08060609130f0506030d170601031515090821 64
    0x2044034400c3d40c0c01804450f880d6400d04144009a918501100500c1e00305120011041c4c80320b10000d10b0710040c070b42c8a00315070701440d01041070406000c01c0ca644811215400e03640180d41e038101441d02d40c0068050017184c3c95090006105114040c5035040d44803c05540061500c5e00b2626000c2c030b01540c8807900b00000d44284270040c100b42e858052950015411013405050241d02c4180b2483d03800001c2055015400c0421000b581b03003c1494850810403200040c0360500d01e00003000003c0e43c0306d81c0026107040801091800e0401c1080c8100704040e596444264204220079008580c000b00150401d50b222000b0300040446983e20070030007200070080400000d009072089240419900010440707442600309880380f41d105a0005081d0500c042240c008808555590b00103034000d002e01048102501307900c000c0410b0b0310071102d00412040300c49072140390170503644115495136612100042000d10004001c0c440708102d0603409032202002804101c06040b9214070107805401d5580c460a1a00e031050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 676029280 1250 676028030 676028051
    0x3030504061d2d0703021201090606030b09060f070c0221010615090b040602070e040f050109080d0b1f0c02010203040b16031b030c030c110a06050a091205070302191206 74
    0x3c14480002c00d054000c8255420b40c0c0101d0360f0311450310f484080d000b0890f14118061020007944404a0706602810400415460f802c100d091032078200ca03085030f14800e41f00451a0001d4100d40030b40f01d0090b650f20350a03410115800c0c49032246100320400444a03445e0189445841c1c01c0c041c0402030180248500c0d01c56164120040100402d43e010801402d02040700b0700140e5400300b1040117980b50030450003902e0325240f402001c100744000e00078026502e000d1000f010050f03c000146000820700c0c1c0107000b008a40c07000c0100901c0750180703640c1849118508000b10f140504908080c00f40140150b03070605036100c2c41c0442e00d9200030014810900d50039090410585c000b03584e000c030304003c11048014030809a8011308680b88a01001c6d041c002c0100d620300c200800c0ba80c03450304000c0701034a4941490740d81c88015105410619099000c40c851000100c0c03030506900d48540250f40050080910078595028480c030320015940d0a003643c50184008a0181daa0050104038a031003080b001078a9603a2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 676030530 1250 676029280 676029313
    0x10914030d18020d030311041d0f061e0108070c0c030b010e13050309011b0609060605090915010302040c0306030c0602030307170105093702070215030106050703030504061d 76
    0x5003102c00742d05031942c2c030000c05611030042c040a82685802c0004040c0404244001b85000302c0d4841880514403001c510b06484041d580c503800b42d140400700e41e40c1c1d5181c2000301700403410641384500c101c400001101c22150300c10b409854000354903040c029907110446d1504100750f18103400940b000c20784100100080b0318070005480e80442400d44410400c42240c1d19940c5038400d1981c294108894180c040d0a042c441110301342240360300040801c041040c2c0d03d4207201603c0c1500c69103118981100020341404000f05118410111504900440307a0840d8204030003440e21000c071000b0182c0d18040071001075600c0828401174295900115124031b13200a00800c014064482900c2c641044c000421a07600c8800d481500465451070861a0a401d16903404085a111a44041c1c001e90201d031400043c1080e8000c0c5482d42c000c1d074400041000e403002d00c101c82c0c4401c2c490350000680c20041d01001c24400d03070200b40c00c18442c0740041041190b07000b01107540c080004015440d0b4000742c07034030070000310b0707 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 676031780 1250 676030530 676030541
    0xf0e0102070b070c0206040603090c05090901241206050a02090a24090e0103030833040f05070e09180615040507030e03091908030708190207050a0512010914030d 71
    0x1804c1c540071941c0f00e503d0740460f004d800303507100b202c0a15850740c804004204400c0c03600b0b00903041c044d200202e0b0f8500f1240907800303030142020301080740700e00f048002d242120071007010083c0c0d00107098440c2000c40e1907817450000e10380180700e15901a0300b400a030301c90784d4030a03031020300428813100c41c0040c0580030700702c07a07030f040901c900030f18180b1030014020003600e1003010a603411079405d800c0413419640c402e0341061180d0700111000d40a0601003c18040c401d034210383d0703d0309918040e0380c10004044d0030a81d10781110f0050f2a140045070582c4980d044da440c1c4120040c0e400b820b1030055a2850760800c4040303183c4042a80c80d02c0d240c030902c0d03a03000001d0505101d41907000601c3e181c1485203140c00c201c0540c40c2e01c85c1002007405080c401c001c1d00d0144ca01d1081b03100040800e4000c5a43e15642070821580c00c1d00200b04600c16201c4010160722220700c009400815150010204000075140c070381009422110510020155502c1e03550b828042040b08a00400301184a0040d558405110800c6402c0302e2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 676033030 1250 676031780 676031791
    0x3010503150112021203090a0f080f0f0c0d0c081009151820030a05030309010e0304080601060c0c09051503100c0e0907180f0905070905030307150f0e0102070b 70
    0x40781c0041214481c1c1c9400154181d0b01541c130744605c0b03089059024114412400b0064104034040e0000a49003ca4800d12003103074090f80c19109a03011400302103860b80040315041d2001d600c451040025860300102e950511481ba5200102c0710396625000c42c1080f0304041c0ca500c00c0b65807644400240000ca9820080710010110204416424011480303d026145031000d0b0100514070407404c10200306044003041c10500a0480784604d101d49481ca80d03903442124100b07030319400c03343e00a107811000401c0e0350698900c1c1c40940b03842c1e801c000045990340040501668200310031400040d40344907a108003800b030510901c54403818000002414948030030415140b194510302465050550b07441440b40302d4407a800c07108421162a0194211003807030f0641c114000150020703200203480398420360f00303000301c0707a903154144941d5603007840545680519120f000d8041d001001206d001074081c400c0c01e120140004000200c4001b600c0303005d801c40e03274070282d8028640c0d80024104140b10809170300c280d10a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 676034280 1250 676033030 676033063
    0x907030c030507090806070e010509190306140403090b0d06170c01200703031103040306060b0d05070801060f03091a07090503011a1f0c060504030314070c081b0304170303010503 78
    0x681c50031a121b640c0340e038010001000c1100c4501008a10b030700c948110759814800401c410011740308801b50f0345000d0601d100032900c0c90310300180744002507140102241700e80e401d500c400340762602e400060074455110520340002d041c0e6892020940818440c04036072107140000061401303084000001d0140220148101e1076174207031003201c007100600001c44606803541407074805080011900480d1541c002c6420041c03666080200200e0b40d07010500207400d0f4420f041c034080c08681c0b01d07039400340c425810a028030790002c2d50480c00c07140203900030380146c03d503144110440113181901c40c512065074101602c41c40005096400d00704204c1c0b5007402610305001800c003003000500140000074610740018820101d005250b20740a40b0141d0007155411025604208180002d00e441e03e030040c001c000ba008203e0001c84900081900389204180603c5e14690040b1a2031418201c4410301480d008500c19809103071204200110b1181c030038080350000014010021f40c0c803541803104040c200f4120b80f00d1101d14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 676035530 1250 676034280 676034297
    0x90b060a0c08160b0640020c01050a05070909020c030904330807080313050103090215070f02040e0c030d080a0b06070609060b06070c06030207080702090f04110f03030d05090c0907030c030507 84
    0x24210000591b1184140301480029400b80741000402070300400d14404d60f15485c0c4820040350709410f0b00194803401041d650b050015440351109c070100c0c000c03070340ca207621036009104603070590800c5d42c003a01100c03a20f0310380204200008107038921a044102458a42c1c0f03c0a51010425480c040019201605801000d103082207040c000724801c001c4640302c0c09040544500b04502552600d40301c0040411401c81981d6540c0e900341400700c000105500308034000e034905120103491510200e40c6d1605200010042d05805105103800c0707601d4000541009900b50b0764191039449992401c00030001031344240c001040e44412402c03e202150417202000303005580801101c00080c00190045c41601d1203400c2c0140c8a0507617061684182c06400390003904484039905220a40601c254001d215910410036030400114203014009901680049150180d1080c0266100c0144030f03007203540d020080c07008445002030b10f4400514000c2c0161141c1e8086580c0d01c4840b09550341c1406140d03840511411b107803c0303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 676036780 1250 676035530 676035589
    0x7080d0306050f0f010c080a0801030c0506190c020f040c180e0c030115090905070302070b010902092b02031204030311070f09150803180307090b060a0c08160b06 71
    0x301c0800e0070f5814820000004001e0b4140e00505036008000c0e0030210f801e48808401c0000760a07164280001e61300540c1748a000202494610708940300d05130741c0203c410b40581c040e20181d51880c60a08202d0307000f414040150a16180c1e889142e4888001c1c2d0b0300c120440c0050811000100040d40111200d0030b841c10412030407a078188102c2e811107140b8103030050944800071080300d507070032181c020001060400040c00509076064000c0e1440f94002c0c65480180d99a5000354800ca1141c0c240d52038010003807243c0e0704402080d400101c043e180448a550b00380e00c00c16800a41072540e20020b03000301845c04102070060650099000380b0901d000c000a1404600b0720185981c40d5889104142969440c2c0c6082480301d64070180ca540284412012680c03540c42d0311038024000f8100e000b00342c2c0281b150403070004009104c0e0266001c5003101520043c50001010700448000356101e50949078070760100003030884044003a010032192030180d0701e03000341c03402c050701004031840010651221201d0b4178101c609 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 676038030 1250 676036780 676036789
    0x60812040518150910081603050d080108071211040f060e01080604021302090f1003061d13020f0d0b0a09060f0213050405060d081218030c0601030816050a030207080d030605 76
    0xc140e114220b444041c40c5c1c0e1445a00314103c41590003410041c0107004000c810714507209905410f0700c4c450f1040e1001201802012030b61060b0900c900ca00a5000700e41c00c0010047e0f401c20011007e008600b001a00d106070004501070391000803a20004950b02e0208100d02c80d4000303002405008414060000d506060700007400003080f01000c0b1640c0c603400251b5804542e102c400c12aa821400751074001c0705466260003a005141c02d1046a032041000c0c4848042c1d030103200c4803248554180300d03038694119029004d105807a0f401c007814a0f04400030440007008901a041006d00c00c0d80715110101d400b0303240345819804c1c0c0748006c800700300280c01400781d140003e44c404441015610305480026681e07403814001003803a8104200a410320000041940b20040100481c9220381c12410f84000444901215217a580c4600365207480130750445001800041d07a84001080f09911030029540320009544409080c4009130b041240540d1003507808124082060224041c14103450070104130180c941000314 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 676039280 1250 676038030 676038061
    0x3070608061c1416050114040909051f091e020d020405071e03090210090302031c091505071505130f080f03040309030b1303051c060812040518 63
    0xa901c10500800b80d003642540c00e0b400c148255801ca05a0008183c200b04a192150068000d01980c6600b0804c0421554043c4400703101080c84460014035091420f0700e68801400411401c0f039070380c000e0f01380c1040e003214803078034402580040803000544948240b90018001c499001d541102014008034100565604050060102c0c2c042d01c0100c0c4643d911441180c01041d0f2542042c00c185411550310030b0240c0c941d020b9030825200761800003186c01d0001040d1070100342444002d50690021a001140122000540d009101541050407070305807076541c802410034160415000065002c03c800d82840003101d280c5603c200301040410180c203000c80007051001420b540034041d8600e0511510411420300115030ba241c00440e83e00d5228281494014900030741c80c40107807490722118005c9030000d40e1081e0390084255058403401e103015a105e040081c1c0c1c41a462001511955807000010392800901020222010006034240e459040004024040650780d11030302405100b00d003040700d100e5511098 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 676040530 1250 676039280 676039291
    0x90d0f1d030a05010501060306030b01050d0203060601050a1b08030a0f0504051c0e06040e0708010902030c180d1a09070602160506070c08010905030702040f050f0105061308070e01080c03070608 85
    0x11250610310360001c6450402c100d8401443c0e586080c00000e11242d244d4003540507280b1480040010340da03a201000750075580c210010b903040c0c1012010412941c0901e00401c1700741210700300001d05600c4103071a01c001103045c541c180c4400600000700003000d202c9206c3d401000c0080c50b010412800d00e6120300d0303901e8118211003086840940c201030b0200307005240c01c46d40000010041940c0320748030006920070403800e45104022491050012880b018240296440b40c6c000010043c1841641012190740e041c030000c119401c405840014800b0a4404080c0c2081c6a440c0414a01d542011b2604628046150b80031004540064070184491148000c0ca2400c0b94000c4404075203c0303001c0e0410001c40382907544240b180358a040f14001c00c01c00040080c10602e402120100104074004221405440e0b080704c200341c040030100d005000c24500503000e441d0300a00d10311102141c0740c40d480c0251511841d50401d20b1340c00480001004100410840c44c0c1c045081a405025a44e1400344d0103010510007820 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 676041780 1250 676040530 676040567
    0x10503070e030303011523070f02120604050f1b0a0b09150c010504020f0d0f0b040302012909010501020f060c0304240f0e1902060c100501060503090d0f 67
    0x104108900c00d800c0c0e40c220300c50042c282d07681c0b540d4408001190000c150388120206200720a10311128a00c0d894100e01c5501c5507034002d140411640d00c0c0280d14107000e000700ea100f4050340030800f088004008851080d4071070381c01080092b05400645142001d20000c51465101c455111403c0d034071110442e104481d1803822507602c590404000540c030000c83e5003600d04203100070800c0030040c0380c1504414010390007580c034000140142000d0201e800f200280c0a030045130780a0030b8070005180c03c0407403a03100740244000100716038480362400820305054648405e035542c11410003098541078044500521090006020303420401c890740340c27901001820050990000300002d01400364000504100b0f4039000f03811607454010b41d150070001c1c0070b650904020301340341000e0407045000002d41120005000d00240720400400e6081111561108201b007a650003410343e10801400fa0780100340c007a02c03141d142c00791203280034a501e5141150759201c007820064104900d5110319040103030301042091040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 676043030 1250 676041780 676041787
    0x240b0d0614010e120a0812040c0602070312230f21060a051009080111180a0b03190b0603103b09010920040c02010203161107330f0c020105 61
    0xc0528103200c00ca40000e81219030001d101587d00490580c1c103442a41716607110401540c071500201e03640c00f51030200a084a9180c07109000d214010180c242034000d03640c0800d05219075000c4840c00d15001440c01c041d9880011401c1d560342c2c0403c0700004c3c0d02ca0f0000c41c01031160301d000c5000505081c51403080301c0c0103260030718030502c0d10b40c441c44036607001d0440300d4001d02400c40b0104070880b49031301480681c900035203000300700e204601e040c2d000b480491341151640c50968880400e84010408101c2421001554642e02c07481c0c0c2c0c0e100c9001071132007080d940250b144050b141603648403000b46801d13030520369400304103d40031840031801c0102e08100c0c08420a0032240d1741c0c465840b401891171507400780c4904c02041c1c1e207507807110b04d000450220000507101480000c00d0400700780c0c00e0340015100c1c20b40000e401107160755490b116602d001009000b02c000c0b98030307450740c903100c4000344080d1500c41c0004400243c011210605403441c11508084035161a40c0042c094540080580c0c0550500904004000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 676044280 1250 676043030 676043059
    0x1a060f0d0213090b0f031506120f2815091104022701030e150c160602030a18080304110a090c0806131e240b0d0614010e 53
    0x81055603040d612511085680d039400c038216041d2840e19100d40c40e450380c1032891450fa141400702540000d0f45002d0010320074241b00484a01d05140c0c0200040e402440c60a10540041820060a0b4038810204081c100040c41d000340009291000c504a030303030601001c1074840c0015507458010310181c440d59000101c0d0045490710402c1ea2a1104c1025881400403410088001076491030302030702d420301c1e2500a140c0c9080b10054058030003135800801035402c11200400038512141c020351b40078486c168001d192540d40304aa141505082006844044d408401c104040b01e5611400313104100084400300e907902169220301e280d21001f84002c040d24042c104460041d290841a01c01612203494244640b1070185402854603008840f418400d03682d02041c0100e418241c82030b004010800042c0c01840d44209c207045014104900101950458241d9186c070002d081c03002c1c0402810308860402e44d5941c2d401d414030290b58050300240c0170b0100840d00b1903010385c2c04c03a03210810284183c500707210403100c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 676045530 1250 676044280 676044307
    0x807050d060504020a0e09100b0913110a09111e1335031809090a080a02100c050309010b0f010e041a040603080a08011a030403110c100908101a06 64
    0x175600c0001d1500b83c0000713014140c5804603020007250702c0c0000401156000f9010420345d210144c4d141040801c40b66407604c041501c070b800803400c54001602c003a40c03141c3d54042074412513171034034160b10b1112804988803403007811040007002e030201d02c8540d141c00c000020204417002d031968400c0841c42d4007400a0001208508004505020348a5100d079a894005104a1340c5903402000c03150300c0440c0420b03650000b032034044d140174000c0c0c1e000001415a000c10399504901903200a00000030340c03052010000402c002c0703025820710101c042e91410341f03906000718103e00b900e00d075101c52481610103910301c00704d50340d00070401404001d003114040303020303c400060030455000300588ca941140c1414000700c2403080c10303001082440100c0d564600385030790315041d8221000100a054072000c400f000410b0110340304014048008011005030303204550303500001b07003480c0007901c0c003c40810707035903e000c10040c902880f50800c1908056403d214041c030780302c0d40d0b03400f2141e42c080143c813540c00450b003452005203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 676046780 1250 676045530 676045549
    0x31a0a0b150904060f080c040507140c151810050a090b0103080703140a141b150406050a0b1f0207080604061a04060803090d03110a0f0c0807050d06050402 68
    0xa06840400701d0381100344002944076410040c001c07030400b54000366803030340850f120080742c440c0805000c000000604001c06480c010b041c40f42084603200d15001103074100001005d9401e048801004900070309404035042003c01003d00b03002020103c0c0e0f2079080324011034088040ba2234501d0015080e41e070300304131070024aa00b20002e041310040000200030011040003c14990b40243c81d030001403580841c03900034510a00d03004a0005100381c09034040388001d28080d0000480c074410741c44800c4410000c41d1b140010b0141848220505141400184109882020342041c0002d0060040ea810070700424140e0460701e540380110701b901446041b2640c403d02c01d500c040c2c28002c007075820900305800c11101401351040b02e014803104940c1a101903103003078403590044642c1040614241a0182d080007600d004014040d802e204521480070703900003060001c025010320440c0c0c2d039400740b03030207092000006109810201ca04e0f0b201c004c0c18002c41e641d4070002d15030b0716880a00880c141c1c2e5a40f0105400c0e40c1d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 676048030 1250 676046780 676046801
    0xb10080d030509100b01090902070804030213050402120106060215090f0715320705011d010e070f080a02090a0f06030c05010216060e1314041a09030301031a0a 70
    0xa40303503200e1620368035802950059040320101d400d410881003807002100c40c3d000c42c41d03011a000030300c20046801e2507005803648a0003a12030a04059490b00810110b040c0070101080256682003080210314011030910081e4040e00000c0203000d04001000e9525442d5444c0b81b283c200c0540005040350070100548508500c071074060700c590329035402405406001c00060000400d010130452200c0740385042070300140c000c4d28503840d01c8407500c2c2880400030b98011501900e065480360004904045a64000300d00d80b002c0000002e040314940c40c5090034804160408015107401c418204a440340000e041103581e0f404654020305900c4001c5204000d14010342440512414081c0000c00c0c49007100d40c6c001151000c3c0c080d0703408440c41009002c0c5590040c041d42001c1a40410804450b0400c0180810150460302c0e0018269040b6a00e1140385141118100c074080044081e00c0e00c100d040d1000e15422040c00d0004600355415035445505940c116018032244449803000922102d980f508203a5031403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 676049280 1250 676048030 676048033
    0x121415030a0510060e0a050708010b0901030e06010311040b0306250c050715140a09090c0905061614061b03062809050606090609040e25090b0d08070b1008 68
    0x40e0341c5003c0e21009001d044c0f084007840d1079900000b81540e40c5601455100d05240c1d91680520783c02c1140c4100b02da000010711904042c3d4500060020003804c02100740a140504400c01600c8903003420030095684411201e8040d030884814002c10380800300c1c25903110071103040c10810140c00000115140c001c500e0000d005440350510004420800c09960746413005a690741c2c850b400c9460390b0844046c86001e82e00000100d180c04100030444040d0300c003a19048040c40e0200241740e98400003102c640010281882403043c810000c0108243c0e0348961248600c1030028080ea45840d11040d200c0340144038410481e9032000000501c907aa031420007803003040320034644070502000d9139140d540f0540b240c040c02001a1411000c6607143c0b07000020355a11003001481189400407641c04d103c06071140901d01c011070300c42d40c1c01d81072131a0888948030034000d000c003500380c9034149000328110941d08071581d41c40c002c4601700c00c0c0d00040369047c3e003250001c03908445c2c400c100b5103078070461b02c0315070340e240c0d1000342207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 676050530 1250 676049280 676049293
    0xe0307240804020f220c110114010803031308210a0c0201060503210c010608150a2703020a080a09030611030907330f121415030a05 58
    0x103800c408a6aa490345080c04a4003505490441a80c0714041603a0181d0310100300e050611082c604a080c5401642c42c419118040841d221000343c19590800450804103c11250080d40010309125010180440484c0058154540b0351103588a01c000b5000711030080800050313500f4881c8500032580c81c814100102c00c1a03040100000700c503468240d0305100c8840c00d0005035107001c0d205016440030f0720341c001c02601404036450f5806600d803444201200c480401800446043d131001e22800000b800903c02900c03c5c0180402d000590820040450807501d2408001183c01c01c0c056240380d0b1941d03c107408506101c80326003410780c0307441d00c143d00040882c0c03400a581300303416500c1010300c001c89124003410f004941c05001e0680307890004495164203517009110402130f9000d440074011a22003044d03448001403016000280e41c021001d190307800480c810b0100c0c0c01e05990300c400c00044002090604212065007007900e80c1404030050034808426a41c200d861005030341c10312000c900d00313504c4002c4901 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 676051780 1250 676050530 676050539
    0x10050112060b0f2d030117070320010e0a0e09100c09050d0807021e031905030a200303010801091208090a0b0c09060d0f050c180114040b030f160e090411010e0307 71
    0x1d403648240034101321119180400700c11f06100041c00002c0d0b82e4086c41140441c50b6950405811143e204030700c50411100f411078800300e03120a46804060104503d1030115890201119452320102c1c0ba42568103514000d040712420b54002c45a00a0310b00031981c90000030b0150908040074001d4000185d80042c080e800307440716011409104231525020341c00c1d600e11514000141070724071205a4054220f410420100000038415032001c01400c0041c00e41284da03400000c9440d2654000f41c120000d44d0703550300102c00910003074211000300c07040285004c030000c0c607262000315110080048000c0000c604100488d505c1c00c00300301035510158020b0501d48e140c1210340b07a25006400c02c1f04c5500d00d42490f040206d82d003920000110f40080304042c0e0096581c900040c01121a061040c40c070710300c810030611001c00c01040200045000b12095007800426041c0499004e6050419a172481c0500c81030b018582c48070348920810311b50154014441001c212440c00060b603012082c1020680d060040f1000400c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 676053030 1250 676051780 676051867
    0x108060402120f040210090b12060607150c02010b090112060504080f130509090a0b130812040311010b030d0c03030f1826120c1803010510050112060b0f 67
    0x501c11381c0215440b220500c4003020030f56051040b03000d40b20134050100030110344a122003c12582026000c4c1c0803a1038688680c8511140740e81556481c4a40ca46440740c41da1035036424010914540002c0f01d02403050751501541744a03085120b2401031046480d80e00103014003140c00180e40200c1801941c1c240d07110903003845c803400343c45203006440c0300da0031030300205102040001c0c00a88480e4085103421716903d07800030016400307003882d2084444500400880c118403660704603050240d032184c0c44600600501c1c00305182515408220207003e9481000703404504c0d40d210707008000c607076018100090300f4121801804003500c51811040c8407141d001c80d0b01000c002c0203500c2c60055052010390318010385103a603158081407256108540c140a00d00c00854000803251000302400c000703842c120050581124046400c0d41c800b141c0d0701440704030980c4200038a503001040c0c1a4089607010003048024245000002c0343d0041c4545d040c2c040b48045400440280003001d6003000c0c0780c0ca0b1092841c86000160b011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 676054280 1250 676053030 676053061
    0x91618170c3f0a05030f12061e04020a030e03031303020d030501050a06030e160e0106030b0603060616030c0501090c0609060f02060c13051f0e01050711010806040212 73
    0x20740201d99800441d007504030101e0034142240c25035405400008902c4020b115044141c40c1e03502c0e180c1c06101000c5000070703000c00013450605050300482c0d440d59000c441c40200c500008001c5401b90b040d00354140d000c18015050301014a07011580161113403101c100c00c800070012031f8200d0b03006201c004103212a0724202702401c04c0d074a1180c1d003150190100c080c4110b040d10030a10440c0d030800103100092041d140203400c00f00c20130045d4012900011311462041100f00050784c0080c0c0005c1c1024018003000783d25000764410b64000f40c8a8520b503081600c0424414402c0000c0c20128921201c150001c05203e04256034103281c01a00a002d800240d0030030001e03184551083d02c01080d001440000c03032600071001c05030b480d0080d8003d00300c3e903900d4103550355050b44042550f5120404070701c2c000c505a038481240e00c80003d00f0032a0184004509007000c1e003120101009641440350500078540020422110458000340c02c3c42d002c5160788404000c103003c3d00075414000340419a100c1002441c01034100c60 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 676055530 1250 676054280 676054303
    0x3070203101a0a030c05040f0f2301060311090d020a05030a0303060905060a03050a0b060f0a06170106030207050a29180c19050105090604050a0f0f0509161817 70
    0x40c6040c800ca0300b08011803020b052100600380108100d003000f03585425172018000c8050a00d001c14075a07103001034402101c0c0c8030484510f4034000d10034418508507004120714007408460400f045400000d030030f0042a4003071003105a20911800444508546034842d000b4000c20000d07048a80004951030301030f028284a01580f10014540360020703605103800c2400008887d003000140c8a488120703107035003000d114000c00c105d401418660502e51079484e01da550200904082d13070b40e080d100d100701602c0c00e40c021041e4404820140140b240c0e2010880100380341290541c0904c0c0c44480550350840a00e00042d0809010302d00d000d540200040c044003541c10440c440e0700b4406a80c2c0c0e04507030104001e080d0440403810b00c070b4204903101c00d01895000720000c0c02c0d640f400518180c142a580c900095501085030014403500580f07040c1044010b44082200c4007500e000c036243c10140c80c3c5107040c02e8401c41d0180c1101c0c104403007000c0e2800080750008a0310080c00200503510005950340400503500c8241c040d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 676056780 1250 676055530 676055561
    0x1c06110a080a0c020a1505040c08060a021209160b0a2c0f0316260303010311030d11030702041d060a022203050a030e060f04090c0f0513170307020310 66
    0x5103402d0140301041c5c212074241d008980d01040e03000e4030b80700001048000d100304c03081e4901c0040802ca18004020b80c03445408400c1000d41d58404100c503004642102502d00380866200d1050310380315600040906060b034803a800400d860302d108101c1190703007914014004401c10070000b000032965000303941902840c641580c01a82d0341d6000f40074036640c5e2140136120151446020000e0013220081e6480044e4103251540038140e0360240100a411540b0a03402212010b8035046002103604040c01052801f0860b0305080c2c1404d41c1281190f82c80e03104400b8002c2c0303e107940d12110158100b070001141000340d04c00c01180d0452070702c2400d18001f940310300481c81d0625580000540348134801005401901e41c048040c102e1403d40741c0c0c00342c80080c03003a407902d0f911640070b100c0020001f20720009403000f00744507840402e24250b107050240580794210504410013004000000a007401c83e81402d044130411070b110b0021200c0c9181680c214018110000e40c10300841011010034465a0040b0311001d0720f149 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 676058030 1250 676056780 676056791
    0x406020d060b09130e0a0221120301030309180f0c020f010b06161502160b0411060421060f1112010905010e07080702010906091b0803091c06110a080a 66
    0x8009520b140a0002c81d00e42c045030800c0700f0107034100107410082040300c000c02110862200c950008250303024030f20b8840c01149002d1000f0100f9501023010702c1c80010341e050a00e18550441d140240000c0c4e190040341d11601050801d00794030707002ca90080c00031402c40350040251044201c4000d44811444512017415800c02064010620304041152800301c0200109054100d8076500d0741c038541e090b8800e000309680d080c411040d14801003071000c624140301d10102000d0b45403a24049140c41c929003559406004140001c0c0611511460342d410345020090002150503518941080a4141200701d040124286003084140003004000b0f8a10030000610b5545e10741c0e01d440c2d0302401c41ea0240301d8003030b0780e444120100c0c0d90180540d0025400903603502c004542c00c83c0740e4030390070103440c0407210071600b100a0703051200c040d410106101015082c65009189040d1721440050650380703400c0715014403070404081c2401089519400122a24540c910a5842d00310740100640412005c5406800d81803c21 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 676059280 1250 676058030 676058039
    0x6040305010509150105180c0d1508100c08040308250504050f1509010f0e190501030e010b09071b0c080604020a0f03020904080d15090c0210230417030406020d06 71
    0x691541c141c50001c7c100c801d0305c482100010001f540050060003009004200450101c1300038011140c402496010f0324a410f4500040b00d803400314000e0b90188024500550300c082d20f42c0c014049900150186000c5909449000c1414a98814200180341c207081d601581c1410b00d8002028008940044920101040b1a0717000d000511901200d080134441080184042c15805406070040102148c0f030400a103200140116031283c1c4080e03611001440c40b090304116540c0c0c54011044d4255010009100d200003160204d449040050902b401344801d445648000ca411101d0b9001d04e0741c0c000b00403402c00707541c803040113807543e50940c2c040c2c0c02015409804200e403101c000c11801100d41c0542401c00e0b0360350755119051160000c0d44116607080e29000c1c034031051030680300d043c009000c401c0c2000409011180c3c000c4d01e00700041200c0020300d81064042240211700860b104001014190711404540c0c0720314107030000040c0300d010664030f1080807080c0000c3c800a40c1c042c0c4180d5104ca0810060580ca6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 676060530 1250 676059280 676059313
    0x120f0f2a090806070f020f25140d11060906030a060303020601081c05030a060302042c0106080a0803060307080601171e030904090302160627030210030b0f06040305010509 75
    0x640100b58150340580c010541003445420407001d113440324070682d015200744110140c207000242c0314a0301200300b0001c80e10340d401010b006d40d6008028004500e40440c5d141400320342c00c1e03580d0001c00381c50f4000040101045407074400417031307201d0341d00103040c1c44e9a807824504000c01040140000c0d8018850000007041c510030024408130740c0c40e5200120804110a0b00c4c0c119813540c001011340403407a840f04400001070f22140101da0301c004108000002d545840307500d801300c00c500d00700c00e801c00303070f0400404111110000c50f80c0710005030858100f507501e940c1d20000c6841c228007030317119071035502c294800056601100358018911035081001d903081041e81400d415881c01c401400185c0a400c10815036405160070707401441b516200740107031020000501001d049140072580700360003242080740a0341a40c1d172543d200d04650001c11030220442d030305640104000e0008140103c05069030303500041c400b551012140781030a00f008000320307071301c9803246401c6000e00b100352070707251a82c401e01101c0018000f4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 676061780 1250 676060530 676060547
    0x16080403080123040e01020309010b0f010f030b040b030304170d08063f0307020406090204060207030b10030b0c2208120a050c01090c080715120f0f2a 66
    0xc05035151600c9909000012030808012000e01c8807802005420070b00c41d032258003030300610131803100c00143c491512204417030944407034030081c0c0d106810780030400c1210781e00070864690702c1c0518034000a00181d0900803030000e1646c500c0c1c0692502c4045000954083caa42001e03000354589820b48914290004050f200d11005581c1e081e401060000c42640c0104c0c5112903881e43e501700d11040d208052a02e50240c0e00031a421283d81558200042400544c00c25025440042c03c420800310715040c40c20600a480703e0072400024240321028011401c45541d0001d80400345d40c0102c1e000c905410020255252a07000140502041c5445150040700e52905111141190b99220142014245044410300d044e40160800b4091010034001096203031001d00c80c1d110081c0c442e490000c0050b00703042143e40b80c1513607a031000d084401c40722021082550312000813400c00711a18004140c4c14804072544000c1d280d4032441a500d24500a0404120a50200840610700491400c0030355484807900c12140c035007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 676063030 1250 676061780 676061783
    0x12071b05030d08041505010e1605040f06140c070609050406080a1709040f060e010801140c0a030b01170406200c120c010b0603190c090312080903130905160804 70
    0x800c0558902c140a02030803d003035200f440348900a5140818101010481d8170a801800200c030043c41000001003880c040b102c1c45003090305009040518062151002070a01d000b1038013008030040c2c0008400321500140ea500380c080c2001d036042107813904002032001c94644901807082c1d060540004040c40003103691005e85030007419800079110401140011a0b01c11228180c00035922864000e443c4113511801c80901703184003040c1c04551500700340740e00359281c500344a41005000e00501c03d5000c9908101d81c44144030b410041080ca10a03001070f10409203214081b0110040c0b00100030422890798071110380901c0c0d40e0000c1940c00c0d1499404045409425008080c0741d10400c442c60040b090303d005050400364410000c6001c900004c0860603580041d20394281d5201d140704618a440d0f514040c0d03002a901502c1c001c844503140d40c442113100703030010480205004407d07000c100701042c140215a00c41c055001c002000541d81e0140200902c0200c41880d5a072011251300c41045109040c001d0145 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 676064280 1250 676063030 676063033
    0x20c0619030908041208092b030c150f0c140906090f060d02190305060411041e05040e0307030221032d10140d0803070315030512071b0503 61
    0x10303600003003900140550302c401d441002d404d00c000602e2840e0301584400c418810364505440748282c405201e180e24581030394420b0a46400c4034684000c00c8201401c24054151424102c604414142502821050030000340c10301c0c01c0944210615003e43c101040d1800c09680e111407020140d07100326040d0082600079548560100300c0340c215883e0036a00a0700c40b8100a1509103004005103000d8103d81c00002d5281422040b03d110740c1c442d0390584600c50f8040c1080e20140841180c8126140061096004180020405844413007041401d58903020291402600070413140711890400e42e42c07a0043c0d6011001481103402d011400020045a4a20a81e84642c09170441e1100c50a84088c04120000100902030b0708620b2550026042c03544c1d4060300b6410b000c4045141018407490051030207003c081e004901c841c004c04000f448400440c0c0d8000101d1500080482c089503001c8000002a4405881445008050040045400d00500101d8403d02c40401103d101e015a02c1c0007403400c1c402c440e0305 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 676065530 1250 676064280 676064317
    0x50726010620030d050103140d17040515040b060a0603060806011511030406052502010c1119091d0d020c0402030604180b04030f031e0911100e01020c06 67
    0x110b0049078404416031040540494076441c404480b8556040324101009440d00e5070010010701012411a6846888a030040e2880c2c094260340644540c41e60394071500c2c0f800001c0002018040107002200000a4615400e070103400d00741450031a43c14140c1300c962103036056140001c0d0040c0640300b8201203400b04005807401d0781c82d10000c600000c5009810000f8018201e02d510f540050910003000901318940b50b850b00c840b2101320301c0307543c4801c000f030001e0f0200c000d5036100d01503a00702d501c4134035059000b48010080b01b031038400710b07423480107041c40420410f014480101d2000d419411803000c8415450352841c080098103959270356030329140d081002580003044988118106a0011603100c84080e1001c00d6101d40740e14070707401540c1d000c4400e840180081c406c0c0010140d001e40d100400703050500c0d0511200210307203a288818044070f102c0c050800d81d07522610040198118400030205401450709000c1c2d10803c80203401030271004061303401070184170001001443c00704241c9010301640004c0041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 676066780 1250 676065530 676065539
    0x6031e05150c04031502070303181104050903090a060e040509070302130c021c030b031c05091c06020c0f0706020d050a08070207051c1104090807081c0f05072601 71
    0x3020050180008242d00300008800700d46a42000c89030380c0100200141d030780e503603804c000302201d200110750340c0c04a034401c1103031000c26803881300b52602e400d00311000030b07580c0c96400d22580746101d0070f01541e8001d08103080011300d164000d0400b9400f03480941e000c1c003241e0f844152231900d61205010080d8803103d4141506508005640700c0000780307001d40100d54190100034042d400804000403a500000e444289132800390805121400103402c48520007165001801c101401c140140500d50b4002c0060105410b000c2d800c1c8a0101d90b881d4010341c04550b034841c000c0c4116100c1e040711080110038440c00c6c6002507400c0c800140e02419034155a2003606060344e40000b00c404120103850b2008510842c1004036507a5280745200e01004007601d00821900300c20302e030003411100c40410b02845685403a5500000c540700b0b004540c283e43d03000001c503035503200b05111030351182d807208014642c0c285002100d95100c0003561100d03014040544407500c216550025804a858032002d2003903013002c64100402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 676068030 1250 676066780 676066813
    0xa030b040c1b0816120f0306060806060c190606050a0b040b030c2209050a0c0e0a120213020c0703020108220b1806042006131802090607050106031e05 66
    0x1907aa84948041480c1c950414008aa65050520240c444601700c2c5000424150001d002d008a518241414017200f0701e0f11001800e428401000320f801410005401107050009124040040c1f000d4252401070003014100803000700b800703008041c0900a40300c030100ba40c228660a40b42124400641e030303031031a80c80b20403890f015040101c5584102000206900198540f40c0e4141f000c0c18a41303400103284e01c0c00300c00340d00c00d40b03402c6040e0001303000079881801042d4507259040c4042d02d031f919000c0c1000c10880c4c404658480784d400d00da06000c0c7d1020401541510000c150b00044078000d0361000c8003601d50100398050302c88010460b2940e9a4400141e2001410384c0000381e40c8416101c1d401400c060001c030145003011030489080b01c4081034014140745036849400c421220890950303956040184c103840b603564111060080c090342c95690108480c0f1032900703404480000310081c02ea0341e102c2030b540c5025030180c843c500040304e02048040250017800700b440c10301c10409070010002d202d81c0114045d000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 676069280 1250 676068030 676068077
    0x51801030f0b130f1b0519140705030705150114040c210605030106120302120c010f020d14070302090d0b04020f0a1511060c04050402180301110a030b040c 68
    0x1074241c1d80c0314400d00720a50307551001080c403c14070140100e40024448856400c8820001080d05004000d081040c4060b61100650308910342080c5c0304a6500460101900d003914001d00c42015004001303a40b500b04680030004d8825140b240c403c039140e140c2030782c5402c10340c0c07102401100407100d0501c214021310704d429004420170319064140720b40c085000d200341058445c2c3c2000f0038100c4644a200421207800d00340b055000800b1003162100101c038441ea0025103d6490b401c1c0c2240c0300e40042030005001d14294001043d02c001001c00710350312010740c6480800b411104406481c0002c1c02c000140301c0c030b8003d000f03c07007070810000c081c400e12640c03655803460500800b510503a00203001c3c03080030750f03076441e020b0381c0c3c50180001d142c0044441032000b8000b04015506649100d1325000b4070140a450b42100d8140c601740c0354111005a2101450000080b080f009072001a82c55820040440c034040745d100c000f041c000ac05a40d09101d11203494003808103603205920044006114600841c002044000c0e12 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 676070530 1250 676069280 676069301
    0xc240403030b0f060409060e180a08031b130806070309121404091505100c020f10050c0109060b03211206150d1422080f0c16051005180103 61
    0x1203e0305410140089120b58005410045445595100c24403855004200075507100300f94503401e0b0600c04803d850305464020610005119a4020000c00c1c0300441ba0101011410800030307031f05442c0c4441c0b0f01d580d52000203520648a81d40034200c089100244030340030780d41001d80c0045602e07e02000441c030403112a0944200d5400840307060201040c40ca20a000b6114500c190050141000d8100000c114440418800c40c200b8083e02d00c0d42900141c9580c9004030804008540d0600d00e00076411050b038442c8252290f980c125482c16030750f041004050307401100a10010340403540440c1400c00301d030708501100d00c50540101d405201d4002c10072141108140d01000250040d001d0700c0395941011800d40201c13655002e0b084e241c074660540c07080b44601d03040d4040120f98121031004030340c800e8070004054507803001c0d146010004074290450581004c1b20611107003041120640210440101c1c0151000d01405216207810002502414411402d4821100c0801401c40040001c5c40040d80180a640c50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 676071780 1250 676070530 676070539
    0xc17030703060f09060603230115033e27060906040b071b15120e0f070e09010e0607030e0109080c030703080f161101021902030c240403030b 62
    0x5000c507000258501c5440188240400455100d0803c5400750594610321503240d060101c01101250510320800300b6411501603100072001104514020bc002e8407001ea543e80b1130340c203c0d06007a0840025481c0c00d0080194101c1000e60740c84400e140c1f0f00c420b22802e100101031751120046130b001c680303001d0541030003218014091072500702c40e8008204190400c0c1d200d210440d0022603400c06128541400b41c800c100030104400b2017038103096011507102c0819130614100325038210030503031140ca41d42c001740c00d0008080c102d94865012540c140d9449040b8040c00041d0802c3c1c002041340c181d01400f440043e2070b02c076809884282e40e9264114010030065200c403200d9034075000160045041800100540006030020b19500c10700c90070003504a040c0a4940c1e02a0038403981000f8401103a14060112105a460310244006102c146240603004000b8801010001036a001114a0300007004106014400d0240d40002c2c100070004601c09138850504071a16610500203000244254400e40031580000d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 676073030 1250 676071780 676071791
    0xf090a080a05031209070b0403060515130f320c0409021215030f062d070201091703010e04080703180b0901022802010810150201020310060c17030703 66
    0x26466140107100d41050711107030000510040480400d1025591050920005010451618442841601c030302d210140c00d0703940e41c7c80440da403600c0a0322090130b10b160007802e8400c0342040025120040c80c20100390300800b803811358142c140012804e101d172218865070100000ca505d8100e814200c4407001000003084e24420807000c00c0e07071a6980301a00a210b01c103a02c0804501e04080c00c81c50321100d5442180c4a80c0c4a4603c210101c02c0010b0580e90100382d8ac0682c0c0312103204c0303c00820325440c40200f1207410031001d03c01c005074554154442e0b01031500464400405000c0c6c003088100710b03c000c3c02a401c0c00b400c0ca100141c00b05810000a241c00303403182c030300860480d0500243d01019101c5070442d0740407490028842001c0e6038100328545152404500c070031030391812100201b52451000400905014080d000211180700b00d8404c5d00081a045840c004540d1041c0d00080c003c3d48225128200e01111040100c0e6051280304050540b9030b000103140c00200c0d221315011060b81000b1300d503804064454 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 676074280 1250 676073030 676073039
    0x60c040512061e07090e1e01050102150c0a090b16121b060515100f080603070605040e0403090803040608040c0e0601120b030c03010c0903060f02121603270203150106050f090a 77
    0x1c040c15403040d07d8503015007002c52030b690890b440790300c2c0c10b910060440d40004800c04000060f00c9480307402c040c100458598523241881c064075810350380d5101c00d03401100818001d0303e0354100c640c0d668029201d0b481c0030503206030128080c0d501c400da4204d0488244029483c031400148254801e6412030004118100011007900002c0c00703d440207281000000c2003000354038001a00000d1640e0003c2088002d814a1070814000404502032071141aa034208030364042414140921200300290120301c0581ea6035988818015140160035a41290445008440014000e5407054020f00400050390303454044500e410705035014000d03a041079540740c09510034200c255a82445480c100b000d06441e050903052950034a038003102c0b6400004007810b40100844140034040c04c40490788041d01d50484180c00d07081000c111b000740319000b801c1186500000c1d0203480c0e0003c03844583c80c180e10850403501262050b08008410107001c4c862000410ba0034070504d14070b103685030050241d610340075100c21082c5559 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 676075530 1250 676074280 676074299
    0x1a0313020a090c030605010201021c110702090f10060309031209060e19030806060702030c21030d1a0409030509041107050d030e0609060105030c01030905010e060c040512061e0709 79
    0x1651110001642c0d50f40c1c10424150580a0500180300900086080003000e07555940c080c01184c1e0010300e015640c0090b83c05110155050759109138001d459001e152410b012400302e5680151050722030301004440c005034040c828085c5002c00c0d68035a03110029a103240702c81c0d00c06031400d914111340154a440c0894486034040091100c14071080403414050079135070034081c00341000030b0071460042008000c0500541c500068800c51010280d4140aa4074034006c500002c11014aa5440c410300000a92088000140d00105149481c0c403020071440e0039100208030480b24482401404202d0500c041c83c028a429440104554031300002d00d4a07001d00e0b41c0d2500d00b440188510000400d42e039455034070f6901020000d165104540c00c008084550500d400250354074108207000b0304054071202d980d020800203400c0381c42030240c1d40d000c54a40c5c3c10446201161900580036190058000d82c0c041c000040b000151103001d030040502015080002e410041d245d0500289024184030020ba00010010726 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 676076780 1250 676075530 676075549
    0x10050d1e060e100b090f0c09181e0a0c081f0905091605030a0302071404061508061201110d0b010c23061003030215061c0b01150203041a031302 63
    0x507001400350380140300c0f40001200c51400744a4002d034000d2040111090041000e580c02945a5040c640c03260941000901001c49405459005203540424030801d0a4844280e1500200080b000b5503250b85081c1580b0440700e0341d45048000881d4000032070302e001006091190002c0e092070346501c103140c07511514416070344c1c26545039286a02030300c0e04080d4400c4020031200039040443c06401c040100c2c1d1002035441086011b00b40b150700f000c60b00f03100b066403181e10500c020300340341916810a1610700c9000d4411a0119003483c040d00d6106801a4075510610585070a1040c0064060400d551a143d107002400750010181c10b2040c000514408141200010090240e804940310310081d9010000c50904401800507042c54081e00c10910020742c010851201c0c2644d80c10f4001443d0b92104001207056654a69852001102080322002d01c100409105e041c1e0b107071256800d03c07a400c0030804aa880c402c61180d09880b18060203c4005408110015500000c030031611200c0f81c609a00014507505 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 676078030 1250 676076780 676076801
    0x106050a020613051015090605061306050f13121b0f060e040e062a0901081305010b060f0903070f060906050d0605030105100e06010918020c01020c061e10050d1e06 72
    0x1240ca030007c0002d44140d0140c04013030842620b05038200a001b1560350326102d114041c100600001246a22002c40c220080d201940075100b04180001d9664900440300504184181c4610840c029103c181003240400d400885544e0801d038403d04d442c0100888513000148080c0f64010380740d0b070040307030600410000580500d00155900142c8c0c850002000013074545507081202c1d80d50b007070110002d603a03089403d0640c09041443c0d40b00360b80d5040c1c603105005290800e0003c6e448030000c9411561210410007800c0005000d4080340c84490b1034900c0140002440d1140000144031404d043c07214601c5180913180100200c600400c040d601d4000203406d40c0c3c0b0840e440104104480300401c805a074045120781c00020a003425002641044d031007981001b681c01007440442e80001c6d24000b00002581214000009402681c60300c0c02c007250080030000001d03103d07241034544440860310b454011000c520071941c0003041401400c1c0302d83c0d00c2c80021003d500c03050300034101e1084c2160115407503010703424012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 676079136 1106 676078030 676078061
    0x120115080a15210212010c030e0106081b0105070b0f0a060e2505070b0415140135370807080906071505040b0106050a0206130510 57
    0x10b000f08600a40102c103403000c0b15008003041d800201c40f007106035004e10815485411030303401c0c2c545070b0181005541110058141c49141307a0000c03240440181000d03414140e86071503400205074200c40303904025170142c00b00000910240b00348005414141060f0845041c0307800072400301c44c5d8080e44909064004032290003094003402c15074912950150340b0301c0c0305162520b8140d586000b94000c0348281c900780101c4100001d206500caa05a40da506600b03010120800001c0c03030b4210b20703841b110400b0018842c01191001c0f090101042c602c3c006542c0d880300400d80a10a25410385118080030b50030001400000040c413148101c442a41d040907840751100f56500015880d8490054010008030398000701002c007174555040184240d0113982410010707070365000705450780e1080c01440c9005801150004200c8502c0030041c5204a000304100c9402c0300c86803981b94107ca1000d503c004c500c = true := by decide +kernel

theorem cover : BRFrame.Cov 675899280 676079136 := by
  have h0 := BRFrame.cov_init 675899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 675899280 ≤ n) (h2 : n < 676079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
