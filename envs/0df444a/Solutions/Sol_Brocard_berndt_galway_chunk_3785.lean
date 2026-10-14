-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3785
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:39:46.963776+00:00
-- url     : https://prove2.me/submissions/e841155a-bb95-4fb0-8169-19c0689f1bcc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 680575539 ≤ n < 680755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 680576789 1250 680575539 680575547
    0xb030115170f0601200105070f020601080a06021e03011d0108010b09181908070512040b04090c030b190f0f06050d02090402071e020405130203030a030c030f2a 70
    0x21a100030030710300d98590300e440d50002c48035032000d00424188020417940e400013220203900228071200e01000441d06060580d400382502c02421140302c115008400144801c0f400003503a400b255520260050340c6902c540141c1401c4584c40c460f018098100200000c0d8078044025003414108600c2c80003404c44c4d0b0b81e140040d00722a20a0340d60764200081d50300180310007855507050046000c40c00e054a0402c2d0710794180011150104004444004000c01c4603000e01c00100a00309401c4041444c4500d0541461060100d43c0210301c0f46004c055150300c000c451491182c4c1206c41e10f0003002d03051a03200f0903005c2c0c444c4040325690003402c1d1581d00d8040002080e030101d150020484d94070303845062a014900880c000a580b001c032010f60810340800001000521511950684100c3e07280c070300d010941c491042200f030301c1000d80205010705400210320003507a004422145042d030b06090004614031008021760107059080c010b8140f0502d41030655229240c40c440e40b00d800d80c20b1088501d100000381a00752 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 680578039 1250 680576789 680576807
    0x3020a05120a02090702010e01091406070807050d02071505070521190b04090503040b0c1c140702010e090109020a0207120b040b07141801110a030807030207060f05010b030115 77
    0x4032190b84518004409828820360603504030050b4400850020b1014683c242514040401121016a66075900e07043c403805004190700940286090181c5090103e0028000c0c050525107100c4544c0c00500c1d07004100040340c41070704210020009000d83c0c90712000142c0141c01075181c0d040d551203c00c2104094034100070350320b03110f1700660f0000e540344510505070900500d40403c02540040e41c07002d21784042a41000a0700042c050101910350b075100d041c1c0301500f031848041641241c0e100c1c043c04a000c1702e411805500d44d41d5120016962038100900040b111110200c071125080b0071600d00101e060200c0c0d0300208000d0949070211030607a5aa5080c3c04440c2d2131110014240640c0c52000c40c0014184400603900308929141c100701c0fa12800401c0300b95030380030740d940d2404143e20003003032501941c003c4030810525484202400044441c0d890181050310020580410190700041072801c010ba15031100010100101c0104220740c0c541c00042d41d183d0007800741e9141c3d1304035501041445845801e140e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 680579289 1250 680578039 680578069
    0x40e12391005160309060b1e130902010f122a260411180f0f09032d04080106080c01180305030409020a1116150c0b0c0d15030c03020a05 60
    0x400c50440400f411001030078030007402c4031106d4072000c0103240c3d55a03d4101c11a24105065400c01c0000302c41c040000842c5101c503d2450320b03040c1005132001d42c3e0454400c00050200e410040d203e070607000301e80d500515005540e000d03c881c0c410001c8400e121b454010102d03140142e2211000c4070802402070b00d101e9183d82c0c28101d0a200c81c40003400090000305c20766039151001e072514503904c100d0500494240303c02c0b607204030384110001c20008403c1800d00495001300c3c0e0400503500e802c034a400c020327100114038005207078454000700d0006201c0100c08201d40040269030700812000c2d444018890725640020701c0207002482e031030519944000f01041440c204e0364000c0045142500e0403103641c0213900511030f644244058016000300340c4000340840b80d201701307002e6994251181021003401c44080045021020440d68003011400204a0708081c4c2e04898902c4040c1c1d2203040c601c0319807000e4110300890010a070041c460000401c10701c20714000a40e4800c840103d82582c8070f105008040c0c4010283c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 680580539 1250 680579289 680579311
    0x21c120c021005180d0516140a0501030b0117090705030f0a0c14010903140109060501080d0f08060f0d050304150908060601410c030d0b040e12391005 66
    0x43c2a28035211803480307030052041b000c1d40c81244500381000070904c0c55070720000380c20184418080342450302c104401d0281200342801c1021a080000003440c44000d0b0038449030928481002c11b20f4802c003040400020100201100c1402c034401440b15203c8050510840340c070814240045428042c09101c9405407006a546441091940e242c100740c0c129500d000c42259503841958101143c5030b8040c480c042c25403003005000b00e9100200003000000d808001200300590042805041c2c3c1d62000500c5807000d04a40c2d50044241c3d0341400b6046110f558410440704001089104802d074000d1161011560500300f510a10703658040151181003495007640510341c012403010101c0d04500205480c0a00e815003152000c000c0711200e101c81d944171a840c00d04a03880400d400301c1c100801d02948041c1e84041d030b802c0c000c0402445840e55148a0300d80100440038010816059551030451040c40017000c221041c0643c40301030342c40b00008800703101d01c0d0a0501401c076020400701485e0059500901c414a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 680581789 1250 680580539 680580577
    0x13240506040608060f041e0c0e280c020f03071101091202010804080307051303111003060815090f240a0c09060e040b0411090906100c021c120c021005 66
    0x101c903003400c40c4020012515111380a100e1903804440c46e507c0c000d6940f1444a800703c9034206103041c1c848075001003850307442ea15156a41100310000c100d401702210405500810032900e05802030341085000203090260344808140c240520540482641d0640400e0300e50801190701c0d210a51f600480c0f800d0042d020410340300c00311b000552014011540401c00c0d1034030b50b0500c621158040b01440599000741c0700c00d110380001c0035003480c1c050310b40704030f80c290303030800b000355a00e06583c05440b040c840300303031050030003510001410410041c072142c1e0030108800c0c02e940c11039a07514540c5500c44200e0001c0d59050000c8000214070719494401c0b80c0c0100c0c1551500541c403446c00c0c80c1110380c804141c118581040c0c440600107140c0e1258041c813906c0305142e006003a12003901e101400410b0f180100081d02c42d281c4020511520b87d000303041c0001682c2c0544002203244249500d0998031980c240000b422050081c100303a040300d13440721140503e1442120341061081d000c0174100c8003030103130320152181040e0040e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 680583039 1250 680581789 680581801
    0x21e120f0604110409020904060614190b0c030906030a020301300b060f0307090531120c021c0302011401050a050105070615180605091603051324050604060806 70
    0xb009030520310f00300800c089403010031540800d0344c0c1042a0740403100c0715181c030302c1401b1030003201243c4013200784d0507100b89210011075039001c104003140d84a800f4aa8100292781c418041040c030885900c43c0c00584001d5507402c01c25110802580700744140344003a1040c140d404451ba100072411403040f002440c804000f050561101d10b20f4403005030016134400d110454041e1a604c0c240551070040406420020300d40c506140d000d0000905c07203d840c401c1001c44004c01440004903001510000c2e0072000058040340464000e0b111030b41c3c03510300650b0100c10906210182000c03400081c1c4110b1213030b8000d0011440c15036050045102c00e0107401e40c090b51486042c002c40d44100054146c40d401002c0c041481900c0e0326107958501050b4016050907109030b01000c500b0851402810020801540c0d150070070f280006c23041b04452100414001015281c40109510950090341c000515411400034095000a041c0c150048c1c0014080402d1980c00c1c8000101c0514051140400701d44500000d0011940d6030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 680584289 1250 680583039 680583053
    0x207200103140703020a0e19060f0905030312150a2318100608090a0305040501030e030904111b120301030210091518091a1c021e120f0604 61
    0x901945410150b44401c0c0e80b00201110101500400203503e0046e940c0700c41003001000b41f81c8480c1040c1c00740c5015881400c4000080c2000c0c002ca130114a440080110441c8040310035000641c04158141b001040c0b130b4200c144104019805800c0c6080c59051801410040c00030703d01b054030450041400b0381c8440300c50006903056030300885800420291403620110800254081c058441c4041403034808818041160080001c540001850300101000320319594000d1852080f4080d0604041d00c400043c050080100251491030400a00c280203207410f2401503011074105580c4e000800300440216400c940c401301d41d514000d042160003d14681c02c1d03409000d209540009120100518a50009a007100301910100da40100342c3d5600140e444050f005811900e5540210046a1410643c24400345070741408243c142c03400e44501c105051080700d040039013000c03014003942001c400380004640e0001c802401269a03011200c900c0c12284000303031103a44464501e5042d00d542d0024020902191207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 680585539 1250 680584289 680584343
    0xb18010c0507050603090a020d0c06020d0206042f0409060e07060c0302060f0c040e01151701150f1107080f0706030b03070e04020f130b09160509060c0f010603080703030c030207 78
    0x314002c41c0e01c07803116230b070200e002044100020f0700c1000c40c25106004103517051098890869480c03004090340e04060311055000110800c204807a5102076000342410310003400000c0310004000c0042044120034100140a0880000e20320900e004d04180442d8280c000c40c400102c91380c01d87c2c000c06040d6150702e101c1c2a034481c041c0c9542c40240c000d100015200c07407134070300c40343c044c0c240d1614048a0181c0382c1d10241034594035410204880c0760910040c8160341d81c2c03d0540c122183c1c40d103440f1400b14510b81c000d450500140182c3c45071401001008101480005074038908414030004507400c499803000f0880495440d13a81e920740c16040f4520412581d991349a607590018001041402069414000510030581c90b2180510740c83e19404034100529101d4130141d4000f60001c0c80b0520380d03d002c68001c280f485440451480b522000c11481c101040c1086080309000c031100003013060382d48a0030b15210303c0e006250214002810100e60310700140c42402031b82e0407181e0101d00308007400400e030204c04035511 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 680586789 1250 680585539 680585551
    0x41d073606030507080a0b014a010f030b1e130314030f0a1a0a0b0705030c07031103120c0712030e030619060e040b0408070c0b040b18010c0507050603 66
    0x1898810102c0071401c24000c0f1001040c84138000c00d44000507107010f82c85964160b11002c0b20092810002080400c252111440c0e204010106000c40060400f41080b40c5034454800110306030303200000ca8030040d10f251900c251b9005651044844e41c984502d2084500407903800c203c0d0f0f44100300449c810304000c04500152510900b0222642e40601040c0d40c041c0e001295038881c644511018048210350501c508030442c416078016040489404001c584014810300c03451102c560006080300070301a0034025500c070718041c01c1c166101103a40c0d041001c00f600e0100c121512038050004048100304007402200c03c5210200003400015103003a1481120110f001419024030501c08070030720650f40c05002c042e1064000111110001055801d0340d0211501604460100c6569109020103e82e9180c802039205610582d80366503a0740360315020030498020340c80806403142c04107004c500e48000002078101e21841c0d00d42d8510a0300e007100111200e00c4604c1000d0482e40042105001a0408000459001c6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 680588039 1250 680586789 680586791
    0x110307020d032303070e0f0301090302070b1309020c01060302040c2a08070501141f0302010206060607080c030304082215032c0f01050604090201051215041d0736 71
    0x90010303244014140c3c01100c0c0400082c000907881d11b402e18043c4081042c510054000b0044040c1c5982c0180d41c81070a8062031032191400304072401c81c40c1d1000c060402400480783c003591034a800c0c0c01024060407050004a1040b400c1885800c804c521030380310446020810808641c0e04032054102c0c03440800101c0c000d4035400760400041012610034002da0000700003d50052599280400328000794041072032a044200110304010000b40c0c1c2c0c005082c07904050116803075071b074400007481c05090b1885000c0d102600c1d40800f1041006102c1c0e0400900300318150724030214800346604481c02aa4000760140d04c60241032024413036441880f03584440840b82c0d008a802d5861142403e0700c118412031080350424070790200b8a00c0003202400c0c060310390000c030240d03070034030a11a1550000c0d00500804401580f20751400700040c1540b040c80464802000d00038008109c05014a042041d14a400c5c402c0c4000c070b40320300d100001c0c420044545c00580c40b01050f060403e1210922042e0301524040c1e0b40d4940c501d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 680589289 1250 680588039 680588087
    0x270504060213030b04140607052b2d18060209030705121f0b090624120402100f020309060705071701091707020f1002100e010507110307020d03 63
    0x8201c42080000d54090039840b0301034030b428a007150010001c030311000883d0b00300347c09010040d0707000070540f840135100b4031708203c07480c00b0311203150710540c4000c2007010301038200012070902003c407014510304030b081d10344002d0703c0b0250f400801d42980c00e00204522a20044d20107440030904a42c09003141000040588822a03500c1c4001344117000b412199400c0c0f03802c5481c143d841164480c12800044005090a0103011048400a070031910010596030240c14083c0501d8082c0c074090817185058250003070a29100c041120034008207078003c580c124003d01514000c10b003113030300a113048000708449074021460620403005000c101d42062000b00c0d014032403030001040202800c0507090103a003021000284156650410802c14186c4130b0140304840010030040d0056184c8040d00205404c0a4800e46564081030108914000305001a42055071400d03c64812602040d0010342c00390b481d40e0b40c1c01c114011050344081c0c480c450540003d42c4600361015880000340a40300144140c5801d000d00c13508 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 680590539 1250 680589289 680589307
    0xa0903060c0309151a18041b03080a2006060a06050c0705120609070509070203030c0a0e041a130209010c0221060c0d110c1e01180303050109062705040602 68
    0x410745292000c6260fa9407180c2245e0010801096581d14910089482c0c100e4480104000c814105001e4400740900240c400d000d010010340210340070065a1020842daa90900701000910324151150218580649001000502c01000902602880b402044034000713528182c402d40c0c01d54800b01c050403043c05003c00c0007039981d0f64441c20115120031355019095074030740581d0b841d040c894a030b00020b2091151600740034000d507000040c0ca41c46100c1b40060380d51003401e50001d807503640e04050113552050510504104251100c200e000c0e5080098541501c2011170906407000d90240118850000d40d400c20b030300c40035140c10840002c08814002d400d09400c000192010705202e411540d03503400b07990001300781508094034841c828031081140400c41c1441c010800c006d455200040d601103990a40d0313080050b07414000e5001180c901c2c2d20940211b4200410300d0094040c1009103c1d224019140c10703000a05868803c01040e05610341d03100305443c90142c1d0120700c1c02004003800c03d031944c0740d00f440800340c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 680591789 1250 680590539 680590553
    0x411030d02152d090c0913020a080714131410030c0902030c0904051b1902061b120403021609270b060f061c14070201020a0903060c0309 60
    0x1400403215800350558490b0042e0100204034041d2200d40401d0240c00041c80a0f440e003032001c000300400b0442c07821182c40305000107281510303c078000ea038030001d80c02c00d00c54429200719a001803140300b5a00042e8007607480d92400e444504034810a803403c000c10408181c245080d40c5195440b12101000045400d00c0b50b00c5549525022260201901c0820b5424402d00c0602c011450046c01c10010540c6189400c00b80a00c041c00740303023034050140d03485078041000c80c100d101b5a03007400100b4824086d15810400000d64a40700034401c048090300602d000701c0d61203210104400c400d000c0e0030780800d19002c400c0702c2036611117000510a030f0450284030507003c2d00c82d6004111000038010f10201003015030a4174680351822031071810001548144050f22000a0010956682e120604498150407180d802002c82c45a1141030703d40d4145400c0703a03554000542c65607100b141d514482e402080034550300c04805a080784510900a00406c0c0342043c1040003d200f42c00c890240c1a8501c2d01080100c1c80342d450403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 680593039 1250 680591789 680591803
    0xf0c060801051c08090d020303090d03082e0303050708130f030213090c0b0309010908031801110f1e0d09050f060a1a04090204140106080105090f070e09041103 70
    0x4000911954010001ea18103008110203400d0084250401d2120f40e0760391407014440d107001e160081031900008030079540c00b401a40e0018102400300c03142102646002001c20b4412502c0d200c404144030030400c40c6048800f421480c80040b0415100d08a045231400d07034130f07504101c100f290940e40c2049484102078000e141c100c01014082c0c0304110702815841000264245400001034541ca002c000b40041602e1142e40c50440750a50f0645580c2d486010245002d880c0c00d0300c0241100c3d0000081c00f00d01c0000c0d00195911204a6000b0440200c10350403070030300703840b410300e06900d00881800805071440c095502d542003078040e5800302d89000e6490341c1c03450507036011030b100741d460b6004481a00074460041c04a15400240681c040000c400f0103001441c224400c5101c96024964407105801103403916485036609910701c21a0522790340e5102c000500101c0309004150180709001c01080c0d0070800c0354512405484103071070b044601d001c01010310a61410081055800402e545052401901c0c180320385 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 680594289 1250 680593039 680593049
    0x20c0c0a0b0a0816020303151c0b0a0b0f13050a061a190f0512130813030c060c020609040e160902040602011b020a0305031504180302010c020c15070f0c 67
    0xb51aa007003400050442072000b450f5810301007440d10440600e5501004070382d030081210303410400305860000441e51a903071440301101c9001040c400d07401880ba80220407441036007801000c0c050300c42d0300c900f8001c982201c92015500001114030040040200382c101c16480200c1c51800152550fa501142c90100c0c4110425050f40000054400b0440803074152003800b03184608081003942a9114014151320510b001940c20184660100369148001150302c22143c2c1c11520561b115107904068a540140130311088a1403603032031500160450041100100300d540050015007426840f1003440094060300c041c1010324000c1ca500410b101420000038809003645250050310340e03041c050302070b003140d203040c0c0385400f4130155544c2500e1302c590010b65684459131500d0019266251025040c40b030b03503420940c9a51160a101040c40c402c84012801d902d69402903009108088803502c080e030319049660b203040d8100c0030804144026040000090601d64400d507484c4d42d0400272610b5202426402da001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 680595539 1250 680594289 680594309
    0x31005040b10150f030b030d0504050a291b01240501021f0b0a03171903021e0c0c0406030b090f1212070c14070303080c0702060d020c0c0a 61
    0x500040c40700d03500c0841e601000d400c1c42e00c61100d0030000226501c5181050707080800034003800d42e003e036901c20f0300079040c4500c01030103c60880d607503240050f00b260058014240540f0483ca00041c290f480c0071138103000449109032010141034400c500c40003075031207803290030f080c21801d40440c20709200900c42d0890495128000300340c0e14085d0300400380544102e43c041da0465100c1c8101d83c541c89610265100d000060240c0007074044600ca0210b424400b00303510250407416241c5081c1c414801c030800410004081030450038110020700300035402c0f40260300b007103003d0043d412518211501d01000401c1222201c90031a003c00345544001400e950300c60300202d40c104181414002c0c01c140c100000c403454107100004e03046030401100c0500d850b006448440d100085914040b500c5a030040201d40c010300e03000f90f918401c6407142d4009a94546841c4000c6000425000028544038401d6054032001c07507005003594504204080702c100650002c45000816000b143d010341d01c650b541d9101c4800a00820b29 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 680596789 1250 680595539 680595541
    0x112081e070c031428140706030f0f0515040c021f020d06080a1e02010905090405030306090a18080304060f0203090a0b0c07031719050a060311030705010801030f0f02031005 76
    0x42c1040c490300034501c481c040d0358041a0000e111181388544000e9000d141c480b01c1300e94285504000c1b1141540c090a010140102e04020407500e51542000c1848104108240080c0c600503641c0812503001700da143c40702c03600d010004402e501d0035421040443c0760310310480741120100200ca0694015520900e0103250b800600f0035001a814000d0b40000d0400c50060034400307a20340c440700209039400d54200b040c10340045030541168002d0ae05039001e0003000c0c29008680c40d0901c0c0030340d682d50042e11740e14850b040c102c0000306001c00c68000c80740d00b40c03021100c140c0032003400d54881c40c141d0005401210703055120b40c1d141070080b001e88095072140c1d402e0001421074190a0609902c01c90010303040445404003040b141c8046500040800181140407075410801e030b9425032803100104610110310a02410402031160340c81c502c0d040360065a00075520042c0010365582055a109080d00c206800308142e038004001181c2c0c504101d060391170103049000b400c10710750381c0028203020707400c6030451065607104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 680598039 1250 680596789 680596793
    0xf0102130f050a061b030c060216110d12110f010c08040c21080c010b04090c050307060203120a090c0806040f0314030f0a02160203070e090f060112081e070c03 70
    0x401128010001952001515400c0c10002480511956a0008005d020a81000c10984129280031000c5d4103e4001c5444644a07088504800c03031021041c0c40c1d11340039881541e128a043c08452907070643c0026461801242e104055441040382440c80f045801150704940400320203000740c9003c0a50395859286500d850301d440341c1c05003880d4100520a09424046401c101d00c2012042041d0703810507800ca880c1c0041c034035400d002d80004105541c1041c24110000704016800c03040380b00f40c41045041c1c3d40030688802049036240200a0a40410010361001c1140b400b000d03842403e0060190701d41310085902c803192180351100542d001c1716840003004080c420305030701c08541d05902040c20407580c80c605090403032a10340034020f4130111146a0000361320360000b041074003088030558040d05403105d89a90b4043c4040c44001150002d01501803003240b000051004561517060b80d00e40d5002811403a00b41e140c003003258001c0107401c4002124071101da50f103081044040c05c02a4801c2020a801030700718 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 680599289 1250 680598039 680598059
    0x6031406040e430b0901030f091505090c0f010e040c09120503030615072a050a03051e010501030302120a1419110606010905040f020f0301170c0d1a090f010213 70
    0x200104028808009010b11184c1c030303250125200c485c0c007440c012074080c000751010070040c400341800500001030341c10841d10010060304078030301c191030b01c0080da1040d6444c02d01380b18040380e003801c000307000883c0c0065001191501d81c0c0b00c00e03030a100078500002001c6d11000c0d41024454001c4052300e0350303031011080010030310708001000040c50315034883da0306003051980e42c050b403100d21250150171840b1502e0194400034070000000300801d0000c1003100c0c0140c5d80c0c2491600c941800503102d00144074070340d820180c2e800500a05048070392590080400000c2c0103500c0c54141c0001c0c0ca640c082000014020301c6075841c2c0000b92203070030b0404120244c220000000503000c10b104681e1054942c105a00300b1080340e0700002d28904842007514040354010410800d88000d101d055030000002c80080008650180505000c0380082250001ca407441c030450010024000b601c40001041c40c103100f10b80110800181c6100c1d504605044111880c502d4030100da00d0980e0440b010415440404210030402e401c10303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 680600539 1250 680599289 680599393
    0xc040e01120c06030f0b0618032406011101020705010504061d1b04020a02010f060b07020a17060c0c0c090c0a030f4803050402040606031406040e 64
    0x9000c03000c1c60821907035400c0c8652880307114078401e1543d12440c100381030015422084d51500c00400c000da0f5410344900b034048030740c3c0c1174001c01d01901c03901d9980d82a000344c40b1040c0c80c003500524245103140d036541c0d00440706059070a4001d1400e54080c026500014801d00400e40207500c512404901c201d0700c1c041c06480034482c000e6940ea942e00809035030740462070881c0741519031201601c01517601c1b0700c65101a8094015030410160891800d14002004020742018149092085440c02e8400d6554942c007403004043d40d1310054550000d0000c10303141182da600400fa1450b030001640e5001d0141400140c0c10340f0200d540c2240b02034002000005c00e80e051080c103070980e042e2441080300b00041c4564038594001c005245c6800d030041a402451030300407103c2850400442c402d05001d00814450007406054141d404900032030130b00c040440d00c2800303070044040500340d03208408655664a400c200103004170b000d0b42c1d142030040c41075140040a9034501002001d0f00d50b02004914030b130f159005540102 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 680601789 1250 680600539 680600549
    0x40c090c05090f0f0622060f0c050619062c060402040e041202030c100c03270f0c180b0307090b060a0f020c120109030201050109020a090b210c040e01 66
    0x180400480300c407540c40d003150400d450340980380c030314101c5003032408143ea5100d82d1005a044000410a18112520a9803140c06647c103503a2005080d001403841550440401440100284c11400014800d84802c25100000a09252010840650360306c07032810108001082c01d02800c0076078105107184290030b0f603159001a025101103180c1407400544042a40c0040c0008103425a61a0961700c99403080050302d84245034107054030092001011800b00034441c0c0540c50001c00e040060705481c6803007040381c9120f00b5161030125822110f1903500e0107002001507401300c038220410070300440c440c88003514402c0c85a110300c90000d0003038601c00402d840c04e0800d80c0101c2404c0d043c024080000c0d203452081c3d03500c0c980d06003030020340e0a180c44410382c00c0c00f0760303550740b0303074001088071600802503005400c240c030024041e030020455030340c032800080140e1040100710004182e403282c04005c0c10942c0b0b0300404065811081500c683c0c0d02e925800900000181c4207000c42c0040800d05100b85865400c100b40148 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 680603039 1250 680601789 680601797
    0x303110706110304300302091306060c0c08120a050a140a051206040b0303040e0a061e24020303070e0a0e180d08072a05070602100c1416051005040c090c 67
    0x4941d280560001700d0720001c410f000c054000c18050000c1d00c40414900c0740c20104502403142640341d15004245512500d02034503403221610001540c00c2000c14901e1414054652075454030014410580d800c2d40902c02007410820402e0740071103501101c20150420030282d940d01507956031550b02d01080b403000507101911651401d810741003150740000490381190802c005043c6a9591451420020400c90380700b00c0d40500130102179000003504400e1501560884000500807070390015241e215408805001405640100040742856003d070207046494040140300311440c9071280343d03020450009031007800c030341c41203102846031112050022000401052400c44058a021748000781215500400240c607207001c508002d07810304000d401c01c0200c941100c11140c03001e9864800944d20140c41c0610034000e403401448040c054400d5003030340f00c1c41e8800644c45040c444081c03d00300c0782058401089401d482142e805c043c0209203070003410311583c0550503100d1210300d80401c036001d617840110070800708 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 680604289 1250 680603039 680603093
    0x106060306083c010501030f0218070c1103160b070512070309060e0d05010911241207021c030b0a0603020a0c06050403051611030d05160303110706110304 68
    0x7480d4000406207000c5107280c01110810070726640703d072982400c08440d42c219401e11300040140018003030455003052080d11010290303407009881442c1103c003a606100003403d50b54000010450f58040c01c0100e54005007030340c05032400100d48030f019001d181d12450b900c59010074050b06112080c0051083c407124100c2040c0b4102184d0340091044400c2e0080b4001d00c9010381c07011039161036582c0a01c4810f68441d0081190040300c0c00d1040c0071000580c0164481c40381c000707624480712100c0381d001101741d0303281c2d40c69030030410100e500e1407400030014021002c5201301481d84a11500520341048110300036100000d900b03486d6002e014044801da0002403d0500412140c0811580504020b00c000e0b0818000241e940300c03031070116442d00c034a074185d40340400c449820390140805c2243c2103001c400d04400304c0b07407400f004040980d001d0041840a1948900c0d9440600100e40240c004002c038920080c2d40e04d181c580c09640c1c4170101c2e8080b50b8454039070385001c8208400c100c84075452000500b4080071031028 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 680605539 1250 680604289 680604313
    0x110402040e0a02030a02070c030515061e04050a0f090b0a0c02060106050706020a090b0d020d0f060303020604023304410117180714012c090405010606030608 69
    0x15094003902c1c00305507903400400140d0314081c99041d600c0d42644070807900d01d41030340c03814103603505c0d20b054200590f10061400460050301e0036842c000504400c010311990380312421020040285001000174448070348803401d0104040700e500c6a00003452041504005a00b440c002c00002c039201c049503d0190740c042c00c014030415400a055501199100328050781e075604200c411181e02441d03500110f191040801c07080540c0c64590054840d00386100302c100951481e1050100654205210241c003580002c8042005030502e803003000c1d0351002044000045081015400320712482d4070788084400310010800707001c800e00c0003424805a00888a800750360082e212001e4803043c00b88180c030380210080810100c416405003044800c1c0d8514800021154500a102c0d52490695400302060f20701408402040071f19640040e00b40c002e06c1030b0340707190907802d0b19482000485095030b103210108071441104011640e443d01018403a501c214004600c1c5460600007406580050b017140041d50003140030409 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 680606789 1250 680605539 680605559
    0x504050a0b09032b15140f0103021c2301231207090c030b120a0b07050711090703110a09150905060f090a03120e0108060f0306040f0303180f11040204 66
    0x30f640c070001c0303100c3c1e0004c42c094480326005000440601c0c99441000000090001c01e091813408441d8054421424822a080c01101244208107006c85034003a142d0303095901c00b50690084030920003510325002080f1300054041d800d82001d9104920901000c8a02c40c0c0c081300391900c1d10f8181074261540d0600482808440b82c850700c4030301070600c00503a141490700741d81d8031036000a030001c440038005800500d00605256256003e0f00c405564150120000c02d039194801e408032000c1c6a04022560f6000c108881007014491000d001401056240e440d00045042444005e11207442103841d807044040c0342c40b00c00d0340c650802d0000744081c4050424104110384440b0216401c0311407695406588141c541c0000300c0e0b014081d0800741040703011500e0754006c0d07600310100c410b03100f900f6265405180d68543c20844904c901c010300783d42541180000c1000118144002c0200c58800c0c28049035060303041301101c003c40c40340702c0f00703a0310001d00c03201032028806803106021081c14180c0d4250b103410705044580c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 680608039 1250 680606789 680606827
    0x30408100f0615170405010b10020c1503070206011703070b0703021c06061b170703170108030a0c0303090f170a03051b07030804030c0501020d05150a0806070f0903060504050a0b0903 80
    0x41c0100143e400178041150a511818404000400d015850441e0540080d91243d02050950003102591444c0c03102c01c5040d0252403280d0f18036801004640c0c28120344030a401ca01c1460000c55100600601c0001600c0045841c4911200d03900140c481c10140d482070310f6404ea05154008403031034041c05104052740310000e03000354041105640101c07641c1d840c05903214050002d074401c1458010800100305680244111080d500c40c030381801c0d02e6600c3e038442a49034440c2003108804509a0401b40c00068000d030022082280240c1c20712001d0855500c41842e8008c1e11041c544544800051612485405200c1c00d0340219015500381031800ca00c0383c5100304d074800d200024084c80614400501058401d010504011707601c20001d5499036000c5254401628003920050300e48868000036044034180700b1182011034419000409854942d00c1c2c095540d482030b082c54204101c0b0002c408800301d181d5019640c007a5100d0700c01400f02030070900301070328001809024803850f17410811190000041c100010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 680609289 1250 680608039 680608067
    0x40608070e180a180203010f020903071703040e1f080d02010e01050123150f030f07020c03100b0409080c030301060314040809130b0301091a010605040f0b070203030408100f0615 78
    0x41070051401135140e0843c25020080d815801c0100c08100d007641600503041700c0e80150b0803980541d403a1001c030214065058040d83d01c03075000344800c00160714503055154100404003883c9084c010000700c2065000c81d40d811680a60344604500764156509110700c0f99203188060082066504050408101d40c05204424541d201294134002d00c50b65400708062000309017403031455507640c944509074120f40040303036045400b40d20000013a840383c0c0085200c204503a8001d01078504000c503440e220004041e035401c1d02d50019a41d030401c00002d0041c90003042041c82d2400156129850035000405480d03954148409140400044c4800213115405950f41d03114104c64400c4800110704100d40241078440409500d98249039580c001d120100c5807405c4240a450b00a802583c0c07540300940d0180304a128907401510401ca080007000544800340c21891f2008090780c0c41d05230707180c26942c42c000c0845880c0d845c0990f55445989105c00510488008010007400543d112020301d802402d40c200045003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 680610539 1250 680609289 680609291
    0x1e2107050f01180603050f060402030f0a200f070506070c05030d051b040b0714060702070303030e0c040c02100c0e06070807140601140316052b0503040608070e180a 72
    0x401d2280e801044540304a525140c1002c81c0150380d100b00401510741074406918400c9a103010500034105402164403601e90222840102c3e11040000c1005152110b04800c0e0008212a0404030a8a140051030440038170701e01180c890000b410b140f410020701034200d80c103101400c1044000a14040152010682071040c00a170654600e51000796072046061000040c0da80000c0100e9100b181c0340c00b811041c1e015071003011014030310141140e91a941612004d0150b4481c0f00f08000103072003070f00400c031141b5901c0c041e07a0b440d1307212001240c141e8403203c0e03459000d80c10004050f810784020744904c0c0281420740ca00007580040150106d481440b580b41c0141c0607a400058000a2104036488809000840710407940250f80d81c01120440404a000c5103100380540c2c0c508856075100c5424181c10b540e07005010503019006410403403012011808034101400304034203003402107041813000c0d00c000c5c41c03240c0321b4628034035107908000e055506901c46184103031440440e0310611104d60010303a5100d1840d100c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 680611789 1250 680610539 680610559
    0x120c030209041b03080d0507090e01090c02010227100203030610081815060f0103060f0611120a0e0108072c2206030b060603040b1302040b1e210705 65
    0x610080d6910400016001d00c90340c0354000080090305c400401121110301400c22a940b9408003c5504114900c00c42c05111201c000502c90071100340c0c00020403a5081c00010302e0f0104c4008900e02c0c50111540032030000317002d01030084240c10002500300c00940540301a51661034000c0010b07038500c04080c100001c001900000404070001c155110705004507440c01c88800c43c41204100500b0780049031000e02504440f40e04405075402401140b088c0c80b0354801c00c07428681421800c607500fa01d4484120303d6481100c500341c2c480c0441c00001d1078400c11940e1082001610030300054403109002d0490010000c14000348090b540030000d1500058044022940d00c0036171000000300b80416495401484085000e030506d03201d450340e80b00108413803052180041d55038a080c20000300340000c031800f42c151540ca074009981c800303178400076030309040c4010b100007000302000307000c06d00303441d0310a1000d0400c0751100b001d01c105180c00b2020a00b4002195002800c80c0c1c0481c403034585a6600d4410300303005102c020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 680613039 1250 680611789 680611793
    0x2150403140d051b0c1b060f03010e0402150304020f0405041b0e0105150901021b0406090504060c030e0c1509120111030a0b0906062205041b0801120c03020904 70
    0x64034040d000c0000018644520070912800001e060035a8002c0d4088854030013044441c1d208020381c0d608900d88405840703800301d2540700b1030758050000285035000c9401c000d1500c2d447d6060000d0750280101c0c0103101d0880c60a4414000c0c260000ba440480c001020b10070400146e8030000e040e0000c0780c050740c000c2066116480e0071140740c500c50300440b40803c3c4141010031008203510b485412640202c44804001003041c2c0100c01d140f103103d030b0050060f041700700c8003c035601c82182d05085841e005000010f00d5550342d0302d120b0071202c0036203084922a48500314004910f07170501035010a0040701002d0180c24103254001103025a8400f00341c0c02c440c5000c101c14895950740c0f041c0c0301c1090038840003400040d265004010550348111040300c03035286011035440c07a60401c11503041c0308900103403015103001a03407124006160084143e140d1070022140d80401c143d2500e0240132250014803040701250385400102511090058120200220400c51028003107400054114200c94040c0d0713400e901501c80e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 680614289 1250 680613039 680613047
    0x7021905030f01020a03050f0405120f09130911011107050d1a040c0501180807050f061308031308120d0b011b11040c030209090a1112181c02150403 65
    0x168403141d45030052080b4141d04210640081024281c0341c0d408020316034403c415040c06d00b205550150007a0301000036000075840707040040c134222189450090034102030400041c014503031305a01444450311954103c081192400350a950b0326400d00f010350705141005000d95980005120f56072003001c0703100380307030042c4081c69080904203250f91056142500e003505101209415511030b460004000100c5480c9802c4806200c400303032146c00307003e0310046141c142042504c001542805500140802074031401078041042d01000b8031000d0003568a43e552000580002ca8655100780000e4018085050444001804807a508014840300090300244200100c0703012011095241c000c0d0401e80100c42030110800100c2c2034443c08403001c4c040c2d9004914202c0680c01809081500007880001044100000b82c00600002d81d00c50b0407241041682c0380043d00000c001e54207409082c00f032140c152100b9600f40b1095115103d49a0701c410b00c040341c2c002c02952001c1820b030b64407a500c0c9500104081601c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 680615539 1250 680614289 680614339
    0x5040311100f080604020d1503110d0f0609240b10020118060504060b030f01060503100b0916030f021606060906060504060e030c120625020a0201050d0b03160305060c0f0702 76
    0xd10f003c00042380390001242c004201800251030800d00d50030303034171624a07014542c0f040e1707150320801d1314082e401e295441130003034413842c60b00312400300c0d114111603803081045441c0c05501805030404982404440c00307108880c401c100810085904044a240c040c9010b80499078520b90301520010359944c450070a800102081800a50b040c001ea40341203c034504150410300070b032201102503450392011541c19000310348401c0c42050b0005030b007100180090101c0c9094028142060a0114206080704c0c0060126401143c0c80c0803d0b1818001d0503052107110320036031002e000c1e201010000340d42000c002524900407881800100a80300c07658504c039031002d001c081e82201e000341c05c2c0e180689032113580540f241c00407a0300070303402c415186403540c550310460310841c091181600503190b1a0155001120355a02c000d841d8818541c552405a045440c10400c01e64000251000c285403107046241150809101600808540b90706000034080d6180400c11503d039981e044a51540000d041780640020b400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 680616789 1250 680615539 680615557
    0x101806050a08031c1b050a0c0b01090c08090304031e06020d02160219031e080c060c0307170105060a050904090203010501030c18272105040311100f08060402 69
    0x4040400058004000405420003206213900a20030241c50050b5200311012032840103d107002840080d600c0b43d0007003000705144c416518002c0303940195074070b5801d613004d001c1c0e116109560b07807801c100410541c090b10894002c50000095460301c1c0c5191141411102180743c2036491081030700c5884108540c80e8100d46801c1c01c5c00d0780070f54940f58480754006d03680d620450141d024002d80c4400030201428a0803072030551f94400d03282c1400784248201060000c3d00c4800c2291554030401c0540e0340001d003080341d288101d047c1c0101035504d107000c0000400a00d01c2c16100710b0400f81c14001440196680016909010381c546032040c2c0303820080c4d00007400390000c0e44010350954a4107001001b407041c0084580241d518480070500c1110004545c2411140f410112201c4404a0205480703110b10b824081c1d0107042c0a00090407882e01c03480007000d1071151081007800032480000e0108100541540d494950801c12a064803080c000401c024040c1c03c4804141820444000d0006050355901d9041d240e60031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 680618039 1250 680616789 680616799
    0xe06090703180f08130504180602090109080102070803070e10020c09070c140a030e0f011b0503040f080d0e0a080606010f02071e0302090609040c090209060d05040f020a0b0310180605 80
    0xf43d541d0500403e0790384603c0d03c0b80e400305a00c14001c9aa410640660355065030050085822940c003a201d001c0250040c40580341040a45039000500c1c92090018182c0c840c0038030320180e0340303007000e00c805062a4552401540070f10104550050200e4000c50107580c0d0340d200790b03151503aa1751b50800403164215010001480410084805108800f000030b1440109100340c480c05407034060701c4100840c4c5042007660074002040c2580341c950716080d460110074460720a0084a007403548802c54100694089c1c0c0001e526a0f0043c44c522814a50101c0c401c10043c0302924100e0000b82000c25142d101c14000384080d0500507445d5821108520802c04c0800600d00c0c0f5042da00e002c03100c05800648000588000e030f201d091120081071851902c854018003840d40404d10700d90141c6060643e6000e5044020350036030005050000540d03840c514004d052007207106910014000000748100f10060703e090f0810703442d0420910801176070803d01032000050322a40b118000003070f41c0303c1070001d001d0141a00b204e5086 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 680619289 1250 680618039 680618063
    0x6020a030902100804031701140f0301020d0219031a06120601021515130501081903110d0305090105070305060f130902030307032109030909052d07090e0609070318 72
    0x3c0c3d5440034645000714402e0f40c42c2c01280b4080700c41c244e0070080078080c580108c220603c00320b00c1880d219411140144010b0005410295045d081ca4100e030000c80c0f07000401841d002c0300d1075030140d06100b110045556000c891070b10340400c0c400309286014007070204560303484a1000c00d1040e0b00030440304903084983d980e40b00c0c00f0f11b080d030314600780d01c560103440700c3c052030401180071507640c05402064103035035915000340310031410302c0b1680f446111aa4001e40074051040c000703420203070003400b00169142d41c40d01c000c1254200800454210b52000741902d041602e008240110b076645c000c05111440340855020005405c44128031004103001030000350b05103c00a240300030140c00c9280c6452802101a9461403400e14144910a0b550969070013800204142ea0511003c3e616501164101410341403012170070180d43c1c800c004c10b0303213414805250410460100000594040e20b1000548200d1484802a0404a02154000601a000e101496104c1e410481482c101d45544410942c020345a4a00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 680620539 1250 680619289 680619319
    0x80f030601051909090c03020c060403050f0c01050a05013213140103050f010516080f071e020c0f030a080426030a0f18081b0303130305010618051306020a030902 71
    0x13001c41d845411213403800c04a90480c001c0c02842038079000700c040c001410003a603d513a011100c40d40600c00c0d804d20b0160030b020141c4a66400d210b62445540d030200009000c1d41032100300312580080200b0341760b21007250881c40280802140400c51000320903a00c074035520320b01c20822000362040304a06100f00c0f0362000001b052050001e00444022019030007000a44c445402c3d0550181e1044080408120090b001c601c0c0d030480907004a40c00380451504641c281401600e010f451600c951410300160f1201c0c00a549504d01600541b1075400118003d10342c0d52201d550311a0309005502c602990301e100815000d03407000304500320030b82c201e0180007900c0e9510740001c0d003e4101d5014150500000d42c0703114045644e110341c0342801040c1c6280600038080c000728820502d54900a03e00314a4060101f8400f0802c010b5400700d0f144055442403001241c00f038109070103400d40d8090100041002401c00041c400c02c0c41d41e90729514001e5800030030159403244002400d0300a8464100025003001c41c009200e55 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 680621789 1250 680620539 680620547
    0x360f0c05030f0f041a2203020a33020913140108011803080f07020f0601090905010e060c07080c12361e0111030d0b1c080f0306010519 59
    0x1c428141d40c0004001901d40421a2000c0f2004550080030301041000702580360038100d81c640d40c01038400520500d2a8080c015105001c0250f44c0103c0150b4048400740081102d00c45500f811039504d540c01c24030344e44203028510042c8460304401c0349030070340c0080d6140c02d80e120740c0140810402c0d910000c0c421842c9014580b0941d5a00340700c1c4002a51078203603041103901d01d01c42c62004407901a9aa02400e4580d00080c0304250000b919940941c410301141d50328107107050007120300070030110100080c030842038203199007551001c1d43d0b80c1806030482810080c16044441c285c40c02c103134004100c503032540d09007083c10340340002548611003604030220f21400801d1844c80d04808103698401060700d5000303107084500c00c0054000d583c0344e11528820240c200f412040051079200d4205142c40400c1e2840301100c0b40c11944031740350300c403400e03611a40b413440c4600b0095283c805a8000540014002c401c58441c0401c034042c0700e0514040100003c0841c1c240c1c1e11a03170584201300448441100406400403000d8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 680623039 1250 680621789 680621791
    0x80f03091c020f031b150a0e012003011710180606060c020a05100903060911030c100f080c0c19050c01180b0c1203010905010609360f0c0503 62
    0x242445000001c61000d9201061100e845078100c801141802c2a004030050050300301501040b880c820303403404111149003a01c11a0144401e142c00007030402e6403117026070a48060b40000a0f0b00803460807228580c5c1245011a41150f0f41c61016850006590203441d040414800168601c40d040080290642560f20004007000340702d0401003101594070442a038500c40c4e00500070f5800301400000b040f06007460100d504100e400c81c0307005544a51030380da0303a2044944510041c0c1c1c20320303083c1c1511080b42c18200405040100125a149605d0140000007001021583c401e14108204200032644000d800025504044079a00591b10b6030450520584032420300010305841e07501c1140b540211350750081810000018070300650034280d40c02c081051006900081d141d88913445002220007800496001440c0038020501c0d01042c99403403d03600074120006904100320003522010608800b070300d40117520584040d089810321150103012102401400b54078000803003d401c1407011210705030300800035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 680624289 1250 680623039 680623063
    0x1090b090f0601090e030904090c0f14150f180a0e040b1603050c070f02030c1f02010e120403020915030105010618081203011a07050d0e040f09110d080f0309 69
    0x1070b14030340ea84060300d03c103651351604100c2e240e410402140710309040075017140780c0703250042603030130000b030384d11000002061159803003920200340c400c0783c007540d0b450190410050030fa095400b160501c4040202503a80d841009101800351403143c040340c0035070f01c0303040004004101e031130300038905440c0c00e050049441d201150205020b44502c0c03040300016019108250107002100d10090611400350303100f01c000603081c001a6814403d140458003180e6a400040c1e104e402040001240b1102020001c0d081d180c5260014a25810800500c82542c7c00d480c1520200d0790101c0c0c480c00e55854220403189401c0340441c0240d019404e00c4000300352603401c040304064940d192000c5075081551803182e540ca5049088001d5a00c3c6c00810040065030042e0780300812031b80c01003d43d18500320640d55040e03c1c10300c00c01082c1e00480c111140c0c031162890a440b620030a500b9004d400e00030003103107640e900c03076000604a20341d00ca406943c0c0c0c088207203c165403d0726012281e1041056890808181450303031071030300c0902 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 680625539 1250 680624289 680624293
    0x31504050f01060203190201061e0503120403020d0206070f05011a0f0f100806011b1a010905040c0302010f050c0609150615040e0c120f0403140711100201090b090f 72
    0x403801401a81c441a412a01a5400340d803c280c000d0303146440c1d107600000340e031045648441d40440c01d0704c54206186120a003400c18810901e20309001d05040040b01150620602c100303000400258803404120809113034100d03149079907903d2524040c05c10030002d94019040f50320700008061802071007019103151200445070449000c807900100300c4401d040c21980d51304a079403260b01800d424043c0490301c0d041001418101e682d42140f002800b80b5041807207041d0b61060814407000580e840c42001a0701501c100301042c0518500350311560002d183c0c0340302c001c1c1001515200400b90601c1502964690f881034025030b062420103d001903030300d001c206418241c401c800404140d042c509005120300040354000c103541002d1078040400000a002000f0962900d020064541010a0441c0c0c652040211980140950070b240c2401800b80052034440c42c2c020104200e2140072581d442d1070401d1207070b82120700402c51020701d5000c0380900120301008248984031014040084004100740352504030402c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 680626789 1250 680625539 680625541
    0x6161a090601080304060c0b130512030a0501090207052e0618050a0b011b020f060a17010602300d110a1e1d01270906120c0e18010203150405 62
    0x83c2c1c183c481c4120711940001c1150400083c0004041840c00703540300c0d9131441c01e00100221501c07000d09140c4100300e03078405c0304000000c101d55140c042c8034142c0076010051045007001d00680c1c070035640b088015545060f0085510b2508441d43c000134036010880c8040d030050107130569445a0b0b0600144d015180c90030741d030406c8005001c2c51483d00c2200c1003500f0585d941402200b120148000001d0b04480030303a000000e542d40011552286002840b070f000780d558a00150741040000300c4c0e18290107810440c115044582e24040c4021103a4a201c0a241c080c1400d007800340e00603542113502e10414001d5000355080a1041030328200c0075000c1c01c4002c1d600d441e4005041c1202c0700503142e45071801c4410f4003240001c9800b50800c2011454800041010304120084004040c0035010340d81840c103029400c08200c010030b2003006400c0c028a402444200501c81c100580c6945903540c003d854021140803000043c001402e0a5010150844401c1110021956402c0070014071000001c0c0045040c0168207280c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 680628039 1250 680626789 680626799
    0x90606050903071406030435030609090c01200304080708280c06120b090103060506150304081204030207150c0326060f0d021c02120f0c06161a090601 66
    0x110304a140b6001403191b8915655541d07682d010543c440444400c00e00d09412455024800c200c5044840d200c2180700d0380c81745400720030440050001082c1d00780c150009034000d103640c1d8211a00c5280120b0020068140410380e221030307465801254891000740c410460001140710020400c0c101c91003804c0c5200002d100410034203407001094602c014080100340000f00981881005040d00c550b0740301c000810b260303803205c00017201c01000303800a480711541c80c403d00c030641c074040b4000403403c0030111000d03080d071800d81c80e82100c0340138200c04914600071510008003014401d000210251508138410108400490401044003020074400c50104d09a01000c0449180034006100e0104055a41090701d03a50701050203000007250415a030004103006a4030300680d15000d110b024541c000a00c00c40c007034854010400f18040102c5528000e42052140170807500c0c010481e110503c5040d40c5455661315441d1030408015560309024045000c1d90162408003480c030302082d40100b041e44100c03460381e40c8078 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 680629289 1250 680628039 680628059
    0x708090a0c1e030221060604111e0408070305030c070b070f060c0e06040602060a1b080f1306020c0604150203010609120c030f230a030e061309060605090307 69
    0x140c2000c0d020600090301003025404070258501041403600b07a25000326a20b60115040512080b80341007040d4111510442d8000100002c5510250456041c80010140c0b10214018481e000c03902c2424080c01003029192506a000c80c2d00070710540f812102d43c1e03035590074101e03180e0b000b0500040c07a40c069910001406030429080d642140e070407180300000c0d0f8070980d58900c003e2803e05242414002407020020381039a418015000030161500034042c545000258001150202c00003030503462403080f862041d0550041c40d0b190320104a003842e09132500c98040c118404440118010314490000034090801d10010804600503413017049079919000b02d00d40000280d0009005201c0020f00c4000104002000313065840c00c0c89004004007a080345d1a07403140340424600201c20b0351074048605040d541410412895131a0401440240c041103100355030081204c100c81d859140728040c0451480e4800307400100c03140040921b1b250400c000c0ba90340c500540540c201855692083c02440c00008038598a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 680630539 1250 680629289 680629303
    0x1006060e13050a0e013312031d0303130e0601020a05030919080d030c182111030d02060910110406140c16030b0a360804030b070809 58
    0x7072444000025003040031000708001428003e440d601c0b0046081d884001703105440d0a95076110901d203000703810030304e10b03010084d81d41c422540030290b2500400c52034800c030640400c055458604a121b14006880000c074810311060003943c035020000703000d204a00c8540810085075901d06100c80150f40d540d0059031183c08000c0064034a41041003280c0c0685410040e03d201c14050300c0c0404600c64a44450502e840d41e5161000042661000380b0819144c00c044a006284800700c81040c282c1e05001c01c141c070303ca10385141d8049c50b03d425500d910400960030310750b00180e1009402c8403000c03845c4403002551590265501e548902a0b1040462048194016121000e440b91901c0749820f107446009c6808106200845c41c020006211400030084280600d4100000c00447e080041e801c40c14402100b402c00741c40748a035545000030243c1080c0300d005210010341110050180c00c000302100140f403090080400801800001401004114240002500900b00c07a52280c607a962117a03002aa10f0131 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 680631789 1250 680630539 680630567
    0xa0e0a140f06010818030409110d0b0d05030a1407060e0601060e031b0607170c01050103060c0306150e040b0a09050f0109140c030702011401030f0201020d05041d040807080705100606 80
    0x10440d000a01040c0055402a442401179040342d1915a807400ca2000f00c400d00c0f04082940080010b00703542d411054000c450001c0c01c1141e404608500a82c3c5055880c41006440c00c2401180d007441518a00c0e207006a030007541d0054802e1000a02440480351140c03402d00501700440d01100ca802c405060006412003025001e19100c41c01e8142503041010f01e8200002c01c60f1403108003c1e881c0a4400303a88080d115228114002040c1541540b4080e002d40752411010000c240ca0f00744c00b08664102c40a065240080f1418003414803440030300400c01811010016640001e000f100015901d00203900491291354041d01c4001542d880f500008207503642c0c10349486851404201051132000088010751308880c1343d0000054070030700c0c4a03c040340300e41e09a00030744942c65440c1000055503014012009101014940245042c0c246101544042c00e03980d0704080c00c00303401000070100207520307003100e01554100f01000d803210032078039115550703102c40c4041c0e21300b581c1003c03400150940030707480701041c0c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 680633039 1250 680631789 680631797
    0x218090307060207020d050f0d110312060d06200711120c0603190501060909051e01060509010e04090c08070906031104050601021c081b04140f0a0e0a140f0601 70
    0xc1c040c1c0d100d080294000e48401d0303074021681001c100002c0e50402c1820304103200c01c8080c0180311501c4501504101c03407810411191f40041040c001400e541091245c3d101c030301113500e00e5101090303061000080c2700c00c443d862507110088000e0b1040d249150302901c5c2140c0702e1070b4185002002c0c1070520030b600c66203201f00d041c0d40d40a41e81c2040340c0d2400c003000c1e50380040d8440403040c8607010b11110380140c074000c1c0e01c0b20000c1810180103014010b014019554081d40d1403281007507560740c0c245140d140c00414880c01041040c00300c1c1d0b03a0802e0380320320f07580000030798020018400c2034007174200f420070140e043c4140d09851003090300c0010704582e140204401c80c0d800005401031161000244030141800420007030442c0124403020304c030001110000c5a400e581940d640250386132500801030240380b034440c0480d07007200600c410080f15801c04401d0305000c5040c1c0d091480b04006202051100d030451b0001c103004502c0d40100301d5141456400104603074044202c0d00070680311200c0340c03c2110790503580c01d0b0000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 680634289 1250 680633039 680633047
    0x150f0e0c040c051c0515120607080c07050105090d020d080906060108040f051b091026151807090b06070b06031903091403070f15020a0f03050702180903 67
    0x51405911141d03402c10b50741442450314044200c906413a41140c450940e02c0b80d500c009110290000d188250004601941c041d11644920b02409a5400b402080e00301080000c0c40051006100c42043e10031144e0b00000a11081c1800c3c00c0d495200e00b60b08070078000600c19600c0c8454902c0c4036001e10360158010401030603458032868011103403210018026101405840c207043d000600c104018030080c2c2d40d004811b5008100102000100c50000cac100700c120028225080c410500e40b0000c400e0400c01601d90ba11a0030b0141d0811400d1a42040d209880c0841074010030202104c4404200034002d050300030354000940301d058620455581c5000aa0490010300c1542d0008018070f8086410407002001c07640000c005d01c100200780e20241c982200060b807110b13001c001c0040c3c404032010030905d044001d458141d060940301081000c0750b10130695140160603490050134003d11030b010185800c10402c8444d89024103001e00150f020310004ca004905141480b9400548107027003c4c0500c2c14000030710b141c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 680635539 1250 680634289 680634313
    0x90603050f0d09090504110d320309010513050d0803010303080903120703021e0d0603020a090c0804020607170307270602120a020c040501030c0f09110a1d0d150f0e 72
    0x2030100410880f07d04a41b00002c40059990508542107540705411280d60580300507400d0b4655042903030480b0702c0c242a0700f841c1e0503003e000700c151341c0e80c02401e29081d07440d500e00500340d0090b0a900e40c003d41d004440d24032100d00b8084101c0041d41a070b402074880105580700d50007201e60302d20400c1e1248448201e20400304103010f22030740050500c034640c0c801c0c42e8010440034150030046c3d4440d01c201c0242c10f0340e0f04810000c60900e10107200c010044c040f0300300b040000816000e04200d0b8003c1009208070400074001d010001c1050001743c25840c40840aa1249030644000c0c203900c4980440f070940106040c1e284154120400b104000c0d01c0040d03005d00119005140e021055421401d083d5042d4041e41c0d054024a40381c0c3c1c031a250003140100740b0220924641f01c1d0101d03900700742c0c0d0040b901c6035041a8018240e091044103c0d1401d40507840d015529000c0e44902d00e001c0005080c259a002e2108592102402920101ca1843d10480c80b030400503201024049003c81d5840a601d1801c1e410008240b04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 680636789 1250 680635539 680635541
    0x3090306070507080d052415030a18050604030210050f1003172704060b041409041a090c010e0a0e16140406020123060f0f0316090603050f0d0909 64
    0x189403013002018180390003d2a007005803401107500f022643d0415a45283c0b00460718450b819842095400d20044010680a0b410520004103459111038403002c0c02c0424800800e011842076401c031050714003a040500d002500e840c00c10618400b040c1c00d101c003240030445040391403400f808401251b400181e2944c0d6424681507800c20700000701c164141721040704491041c012100d000d0501004140707502c2c56200300000c456480e0400c1074445020f01092100303840c00702c5542001b100c100c403034006940c0c4a1403d18525890341e6800100000e420060085503480020080d0329040241c0f620b410b414502070602131400014480d907903400c1c40318000b054009086150140d0f6107421032400002d014402c5d20400c1d4942c1c03159004c040144e40d204410030181202d880d00c015040e00702860704a0f90305200d000a280d0510b0a40501d1288a991188510310781e000c1000080d4044045854038a2954a03080f1000038469840180d031207000310746d14604034941c00315200c094440c145d10703011142800d14031410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 680638039 1250 680636789 680636797
    0xd0f2a0f03090812090301060b0307080103150603080f0d060501050a02030a0305040524010614041206050703290a09020a021e15010f140f1003111b06090f030903060705 74
    0x9802d200d101040403034003030760520400e40c1c035410035002d0641d100d80d120281421941d80da44200b60702d481c18024081030781d07030041040e411203400c645c500c4d0209001040f00001082c0952005150440002e07036800c5822980014002080c006802040555551001900c40d8880c0450002c01a00100f1024501d03500a0744100d4200b400752044445802c00c800c90300100345035140c80041d1540001004108003548000b40702c12a030403d50b00707241841d18001c2d4909401d00007020040031281c0b40c900081d06180709a0203548207524501c80255101d0b1040c40da61040b50a105890340213403002c00020a09245078021200c0e0510366500400d112840e0700ca90b00400441c031162119107000d4011094146194540c642e80070385400c400040c420b6103000d0700031090a41074502580a000303845854203481c1c0e81d07445941b40912142c02c002c99240d000380c3c0c0317400d50b070b11807503200c007640080080d9100780240b07000444030712030b102800403243c4104080e0300d040d0f96401402482035051748004c00140c15144984050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 680639289 1250 680638039 680638043
    0xa0f031a0a1a040f030503070b07110703081803060703021801080f1b04030605070816020a0c0308030604020417010506101103071e0b0a24030b010e06010504080d0f2a0f 74
    0x42803c19458004100003007015034416900c581c00401c05c1c4040c007010b1400c0a030803d072942400700e0924010210705072101c3c6684005050a0300114007080e00b140030452404000b1001000e503080c030f03d0700100280013900000503042421640018408865008030f00840c0915030043c00f1182541e41c1c2600003030800101e1410b9000040b0038040003000601d9809007d010f81101d0b00c5015252401d204d0340c82004030000901421540020110fa01007030400782414152034001420300d80d255103403408070300a0710460348248241240b10115041e40801940040d0041600b1245400f1880740041c007101d0030b5104904180c46d580080218100103012040d101e081c600c03404072580520140b60f21640c201030000c0787c003c0102c81d15500c48241d07621540403264010041c100d034940e001410b5840b0803d103820140200100440703a1b00100d402607000310251402080c00000300d461042102d0f0000348140d0082002a0129418492a4800409106c840c02e00d04440181c04c0000140c1f036190801c40745e54140c81 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 680640539 1250 680639289 680639339
    0x1902040209060a090317270103110f07050111250302070e04050a050d050a090909080708030408041a040605090402030612010204090603020312030103050a0201140f0a0f031a0a 77
    0x400142501da542c080c0055400d0707900c998107100e00d1801c1402c500510890314030b010200c00c00c480556101c4141c155150482180c0060001440141c01a8001c0040b0202000d19000209243d011203080c41d00500c1c40d41d1180d4000e009a00e903440b08101903000702c0140d00360903c007000c4003e04401440c4680441c1c3d60007841103902082d945d0401003154601541c0544203038200f4641101840403c0164240310a4030386007240c80c04034880401420752030076000304c0511381d480380065010b0050a40c00d803100c07070350041d8000740d890030240fa001007280d015109240903d5020209000940d010ba41038404907626601d40500e04941c45040000a40c40146240c3e4060460340300110482802d03c042c102401c4184e030000b416a081d80101480c02d100a07a4060080408000501c000b480101c0e1044803a942030031301c044101c0c1e031004051800d0140203400580000003180b80915a907000b00398003015183e07502c00304031003020007824040702c2d089401c0c1d054000e00031090800c02c0d94600941d1140b0700000c108 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 680641789 1250 680640539 680640547
    0x211b03070e040207080c15060618240a0908060408030a180f050606030c09090706050c0a080a0c020907030c200f0f1005010e0121081909240219020402 66
    0x400201240c000c13401c01d0754048004500b0050b00c00c410403d1070702c058180003104c3c002d40781c900c00007240e80c49071400c0361022104010115603d0707203a401c0d4603618400d49281204078003081004043c0d05070004641580010a82000020312030408186140180c3d0844035141c40c69079680e0601c030240416103c070703401070a46010781c403001c030300404501d07254644104040c040c1c604021041615203607012030313410f01c200b02c524180b00303000c400000c590088950b0b5040042d02e88448444507410410f000c60301401d40c01b0f0008050389860b41c48035880b48402c1c821204500c268a1b0f98000b00c0444071395048200206541c3c01c2c014411081c010140480000c9500865041c03602c0301d0706250a100d01c0d850381307896580c03103e441145104864081e180c05040c496006d140740351b03d044040c2c40100d0a140d2071442e950000400001032004c5201128000f810814812030451f14106008110510521990043c50030940a20f190021003144142c0042950383c01070440c4542518507500100c3c50201c103c2e07120790300300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 680643039 1250 680641789 680641817
    0x51e0423100603030207050319060e0c0d050c01030606031b080c0c070602031c0b0a270903080601030b062a15090a030e220e070306020d02211b0307 65
    0x7020200c844155000300c1c0311851450f01074541500b039041203201e504558032800d4000050b1078a5900c1940085001c184803994110550070b0900388c2c8a0181c04c404013030a0001400310010710019010f5082c2e03002c0180640d82c150840c12511000d0300580c01d480c10740c1e49441041c0c4030b080001d0f003040707480660619000c440090750b0700e4415503510600244e0400714a40210750710f00c01c2e00118110380f5031020b1024103110f03000241d09039001c1c05110b0100703a000701c1c020010300b01d080d10b102c00f04110b0074003007000591904028020000c1110700302e000031f040c641a280903050800503101a150f6001d00c0d0241400c00140c1680003414070b41500c0e0b00c0d03200c0c1032008010746d4045803100b0f00400c819801303004018205e04000f85100050b40ca00c90040c001c86502045595401001c400c0403087c91300c1c0090048503600d81070b0306000030340e40094a401d002203500b4070b200115900500d40c20241c202d00049458010410000c00f41007110404c1b6942842d0005070002c10300074000359808585458400e070007082c06 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 680644289 1250 680643039 680643043
    0x20415051c05011508071a07170d051f12051603030915020d02030d090519060b040f050c1603020f060f0406050903033c01030f06051e0423 61
    0x401e404054440d032203040424010b00707118a1030f440d0405281400501d0502c2155695400c2500c9221401c054610041c5030304101d6900b9101e02c998401030340c60f10060700004011007500b00031201124a441e140102d4042c6155a0078020f140c5002401d5040702c614003c0281414198848140d4150090070500c1140d07541e40d0b0ba044c0e02030351080d105d1021650411940312503070640d002c0c00c14195480501e20901d4580c00105071403682c000e80201081100581c601030382880701c040c00c0c003411100d040e9070420070071a45401222909006480c10002001d19400d400d050383d41c1520b1b0b034a1301e50000c11604282031114402c801c0110300900440d5294420200e0542c64940d00700d51120104090105200030010341b40074060b04201d5800085046041c4203840c0301d10302d407205041a000d40061003022003c060b1151003091b50444001c203419941da0b482c240203100c030b00400c4046030411314110000b0044c561104010010310b10b620101c0c0c0c000d540d25a00c8405a00070b14007088030021030301100c82170041d03003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 680645539 1250 680644289 680644309
    0xe040c180305060103061b050922020703080a2301120201030e070902030402010f080105180712020d05040203010e0a030f03020f0f0c030d050a0b060a140d052a040605040302041505 79
    0x3041000f00881d600d5810300e80c040b2090790b0700c007907031540d2032015608041ba40034095030310b170103421548015044080380413083d0088241e4a410240e03800410032074203254101e0b1250b8800c0004040c03e1040407130042c1c6078840754984000d0b403240030100b50014000840c085501c0a074051060400080c505801c00d42c9518083d4613600110380c1075000400c22085507801782200d690220f043c1052050781d418400040c0d20302000a00c800e1840b10014009071120340b050070301140801000e201196107101c1c0400074409403908a4080e4020f6080c99483c0350710440010714080c071035805a030b610500c0c000030901180030b980320b05c80000076400c06100c1488440e42d140c004156018a100095669900d20740141081d90300c003e1141d201203240103505526900c5001c200d4070601118601a080a00c2201c0300c4545401144449002c05151034200a1a003060403029100d0010b46884540315007413050781e4411034422405840c00142d4180400c20050400d5048810300c031a0351365002c0e2215072104085110302d15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 680646789 1250 680645539 680645543
    0xd020412050703110105070b1503120c0717030a0e0907030f0c0c140a030806040c05040e090717060601020c010309210e101718071a070b0f070e040c1803 67
    0x49900b042080101100415807011030a081542c04c11a0700d455040107100000d20211b41104003c112200b16502440309009100700e180c55540c5480c03004050f203956030310034052503041c040008500211094004242c0d10444042d60740c0514408030355084c08460780000d40b64405054071410710325800c5e412409000c4060b00d4035a50f68844d203105080c40408482880303201c8080c1d41081d1030440110743d001002e281d11181c1554081418140c5841c102c40502c036650003110718602c02020f10143d800040b03000801c849034104002803820b20300310011b8403140e054890310f01592050300c45030361070350081d0800314082e4028422814003110340d04001c01c00007030b440ba2042c002081c5a080d9140c500d000591038000320094940401003a031418002075084102401800822440c413440c506960303400c0040d00040c0c02a20b00350010104130544110b0280c00c030102c1280c40003064000a0603a02010010500c1100e09030781d041c20706a15001800300a26411000780100040d04040d0600d22009402d450001d40c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 680648039 1250 680646789 680646793
    0x904091e0809011b02130c050d1401030b0f07020a02210d1812020901090f09020310090c090c0f0815100c02031009261c0c0201060f0510050d02041205 66
    0x240e000c00140b8000f25102d0341c1403503100c0b8021030f00141c6c94840030354050249003000041c0788102c1e10001c1c0c8590242c41201d2184a0408800c01c04e0400010b07030311f90482e0300c40c0307e512469888840714101810001c550704401030380042c0d80040940341c2541240c8002e2032a03031070003681c0b0360408412130600c8000007070100400c05055200560010510401c002001c110503c189d00102c150700161042106201c0c8a1000340c03900c83c010f00140003540701035002a40141202d01c03e420904140d0301800180001762416500180001448800c9000c0d03000c001d100303565060031318540c0072415100000043c15441100203840003242103525044a8000004a1500d4207200304202d841058a8941110003240c6203a04080150000034000c0c3d50740c40100d8104100c010703000f008840910980d0180010741c0c450310186400108881502d079218010407401e43d80240841d680701d54685110080078454035410044028644070301c02d214201038001d0003400320025141c0b079030356202005644140e00f030540d41c0d6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 680649289 1250 680648039 680648047
    0x7060c0e090703150501031a091e060906090408130305010c230a092601060306090224031f030b010e0106021501081005070203120f090f030f0904091e08 67
    0x14a030030003801d6408212072905124072a640807081e6183c0c5030901c00d40f4180340c1c844400d010080308400401c040402d02a004c0d082a00d40910311145007086803240c4507101c5030341c802150850401003207107031003101c002d4140d12150315507644460746e560100c42810540e03480c450000c0700141d030070300403090202c0b903556441d0019100145103440072501100320b0740000104000d0107036440d400405203021544000080398554140a1540c8007500991036458119403034a4400b03c1044420380c0175082883c001d5844400120480d00b002c00240c812000407025060240001a00441000410220f00100c0000300c600070340e80c1d80e07a200810b9402e801c00c80414100000600c025a810403143d81c111028074110001075241130241c40d2540f540e40407401d1402d46600001e0062402002215289030f01c000f0f90b10321900e04200d41e940f40c1041650000003034010340743c810804150000c160340c00d4500400c040d03490010b5000802000b4590703070104941922a403101038210280a5810468a038050b040040e59 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 680650539 1250 680649289 680649317
    0x1e0306140301020301050f0f031606020105011403030903070504050c2104062d0f1b02010e0d050f1206121204031209030803152b05010c030b090f07030207060c 70
    0xe2400040c08500a0b8414030040180c0d0740c0305815010749407019100049807084010120f8105001010008003610620b08001507155055001c20304807901c0141140d120080f05081640340c0c894030407421380c0f581c0180400e02143c90550710243e00401032100d854502200c02044407943c80305011a481d25840220070032050050328002c035117045205011007030740001411050060000c10000c0c1124060341e034100703820b50346499404840c2c1a1081c900722210b01780a458001d010700907509280d8044d000c1c9802141209000310142c41942c07890100c402d0520209000d00845a80010b000550290300010001407040d024440c10ba010110030501326a5141941026a0600d0400e1044802c00801c000c0800100d02c0d50825240c00101c0e95824642c9002e800c4001003051800d601c02c0c0c014401d068040c140300a005d8041017603203500c80c100034050b60503a40d2042e8103c1729018440e039001a0514005a40100c01c1800143c3c425130908005040c00c03059190ba500311004400f80501040f403943ca134000d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 680651789 1250 680650539 680650559
    0x806120c03161e08030304110a0e01032103020c0a110f060a120c171603091506030506100503030a0c0f0605010b0d0506090c0a1d13270503040608071e0306 68
    0x1038140051402c03c04507900d0282e42503a00e1000800c041c1040d4011000102650760700245100140203004210841c1d507160708000040c00c000c400c40040d1082151400d000240c0170703009a8424803680b101400350809562030707810003038a1503081e40b640041c030383ca403402c415600e9602800000910341d0711800a2919201380c0400c4628a440340803d01c200192350400b5000820141d581c400e0600c0c204450801010100350060481c3c414028820310f080b40410b501c000305548110100c034080e03411074280d80c075082d00990f1640401d01821f0f805400401020a44074040d0080c1c040b91445103a40651001c12a00c0f500201d410031381200e4140480091020b01c1c20cc290700545801c07540846150b03003d4244160040914400c580c070040c14050300b0724070b900361a544100381448131071010b002d007548001c04650000050100d00560140024640c80310011880000c8a0314076460742300005500c0c10f424540107888220004100800308281411070760002a000340e41100384c1106520b0120710f10703040480c000c1d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 680653039 1250 680651789 680651819
    0x10515031e01090b3c0a1e06030305130504060806010911190507170a090e07050702060712030e06010303050a0e0d05030c06040b15130b010302070b0106110d08070806120c0316 77
    0x1a000c4000200c4e00350030017112001150b00024440310008003400440300b100c95241e54a0800d5243c00c1c5428000014150044014510480c030744200008490315072040008642081c0201d859540c0300764018440001c1583c0021100c0010032101810f00ea40c01040003100440c6060714000500081000010010038030001000f080300100f40f54144180f004009000300d84c030317114040c400200d12003c41c0c43d690140080700c2c0c94a0b000b400e2541e84600d02c1c20400e410a00d11054480000d1030008006a8010302084040c141c030f91540e1514a420942601100c13010203019100d030340b02c13140b400440009007041006010650114002d040549000d0820300d181030b200600580701100c04940064560752070121072034200780180ba00141158960740100c0080c002d0307041c0101050038140010946981152080b54034848550071030302031000f01328044072031150503242d036404100c5140102d03600303140a965104107061071030201d4203032400e1040040c0c9807072261342d6501c5002035621024000440015856 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 680654289 1250 680653039 680653111
    0x40c030b0a271e1a250e0411031f06110d0530010e160e0d0f050304230a06172208030603010515031e01090b 48
    0x412440c1c18480a5540000c6180e48410114007400034080800188a081c6001860f8004140414010501d0144110708482806020250b020340008403d0300d60701120202041150152055034888a0402c0d40c107841d14960240c0d1154441d049101e2017005000610f1013101c1c8407081c07a1101340a90f000c2031400c5003580005c0c003003003d803109a04c901e0400180300820714589140499070b5405100516441d0f400d44007602d10311426010809081c1d10000719481d044c1ca81391140301a05880c3c8100a0044647c00c03000b40000c1220175071404143d180c150740295410b40a8004601c2e4081e040e69403070700f16407090308030002c0031804181c0307004040386407829008850300945141c520301d41090310140c071000f5004c613211140c030400301c0012a40d082000400854264954501e0110315903442d0403074098004440d858042c3d880d107000202a10f02602c0780a00ea504040e0151020f003854106415040610241d100c40350340d203801c40f02000400b16040507100704e6006110004031071001305a00b03140d890b26814 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 680655539 1250 680654289 680654291
    0x3f0b16110c030303072706020309010f051806030705091206160903170c120f18041803121d060403080714030106080615070f020f04150e0601020a0b040c030b0a 70
    0x1200d01d07540c80c000b00304c0b900104241020701014070450b40c0a44003070f14184e4848811105000006040c0b50008050f09024900b41c0311300302540944142190240290380404030060749090311b5003101c0c20058001d54005049250040c40d0124000c081000c6c03841c6820b1082d0154040b004000341e03281240c0b884240364070300c1d24200050b68510b859400708083c0114070301c000b80030b0020310300c1c018090411101ca1140c1c446412a070312008008601c0109401000d0b480032140c9607140d04501e00d20b40340c81020280c0c0001e8010302c1602905440444960003400c102c0204c03d655903d10500b510f9400488048061851000701250b01c0c01c0d00e001400c03454094941024841d200c800349481d55955801d590542d041c0341303480d10781a078034040001c10442c103e00c040313810800c001402405000150f80c5462505d40259051010341e0030000c00c0c40308503025031000c090507540103c0180400070780c4c0c100fa330382c00c45414030445883c000d0326140d502110000343d03011105508408800c10410051500b42940314502c60301c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 680656789 1250 680655539 680655553
    0x5090304050f040e1504080a090605091810120803012c040f02181807050604180f0f061701050a09020109060c15020c0109020a3f0b1611 60
    0x30205000c407081082a0f441103449080301d14118600704100f44407403441103543c80050920b81060903559001480c0c8070f00141e03004a022440324000ea08489005070040c022201c000078042008120b160081e0201c4010420070380d000404101002c014a0304a0285907140e50725450300c440e602e41e10303084c00341c81820505507070250706103d2804901198031075080013422900414503c001000b17016480354144c001020350043c0f0800828403c007102a5008400840d410680c40d501004100c1c01544211030441900b10304401842d1801d4214142d800d611100204407000507800755804d584d095000060240b00d20f018602c0055002d00800c0d80008080000b000000940d400080c0700502c507000f95000d02803441820b00401a19020b0802c400000e50011500d500c035a10025001c0c2c400003d0a900c9410f80060201301c000d07001d656090458900441c2c032003030012114528a29101a0204580e414144112480421309014801c0c0c412420f40351844520101c84202030b0510045c1000b804007588100c0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 680658039 1250 680656789 680656799
    0x50411030708010c23070b0a02040e1003120e03120c0c03031612090f03060902060d0c081605121614040815010b07020a061b022106010b13030305090a08011401080105090304 76
    0xf01100c04140c2c0100001a148d515a0300010191042e60300080d00e50f00d45800304255203207602055400c0d00c5c40381e580c7c680c070070182900807285100520f00c9142d03d1f403c40c036404012928880003d280c00e541e49000c0c3c0b40c07000c14050010342103402c00d003800b03507a80ba00d801d260000c0001d4502002001429030403c29142401e007581d156485450b03020060000b56079290400655503480251180b1040c141800d0051412007200144000350030f46080c00412540c451010040303001e83c00303665a901040013070140719902d03056581c031041e044280010502640100c01c0031520100b40080001e050560000c09214164110388001004c05900c074007a210001e11021005a1310105c2c000300b16416442c18560010120700881940c82e68884001d51089110f0010b6508861202c0c264519698103810f85030fa580e81c8609080562287c088051142020100c0078030001e4081c40280c24800005040540d0b40e80d08d07403061600710f401c2580715100368010305004109105c42400740680c0006a000071b103040904d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 680659289 1250 680658039 680658107
    0x306150507060c03141503010c050c1504111e0a170a32071403060103030f050a02160b0c07090614040e1c0c0b1302090604050411030708010c 62
    0x32600200784645942a4203005132003900030300c640359402d070070030000341c200800681d095014064050b4065404c2c2299080800d01800550303280407080300103800e80342c840c000c820440b00c00c0180304603208101c1084540403501d2b6050b0910f002090314130a03c030500410800c00c000c50000743d02c030f14080456424403200c032142c00303e01d00d0407895200078600400d0b00858901540350715403011403040c02c0380715041d5982c00300000030401d04403070403118071400c05425035040c5612020b00b4003014011641100c8a001001d20600040924078040d20544084062072001c26074007080c59401201c0500000c103043c041503000303004842c003d110002080010a103003854008243c1c0a43c1d40061140d540d45013000b50240b028040044401e214005420b03074030408140180001c090054180c4020211000060400c00c06aa0301e10b64250000c00222056a5031020000a2f040041088038000341c094150001a10100000f5010300404000030907201e00c45070000705a143d040c600001030303041c0350b21501d160081c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 680660539 1250 680659289 680659297
    0xb0a0809250b16140a031413061d0607060501030b06040614040b03070e01030827060909060118061e030b0604051203070b0403030b0405010803070b06091b0c0d03061505 74
    0xe500034541c0300c0c119940f403903041d0030324000090205007140090041c000c60100362086514440e03100d402c00d0714044c200c42c254034000c1e001540400226007005020709809000300700c2e5101542e4808071580c0080101140b2036410a50044410644403030060080040449150380c1c010000d0f1410031440e032500c07142c94041e00a0500341402203950f41d440c40000c1c0c90604c94500a4100800760040c1035075a4070f0560400d07840614612030035940461284080380c0d044200c060920700080c0703910b042171140710400600a4014002078144180c59034180d40151a00101500038031a0f6141c1c0d02464515049040c45440102d60000805140c0081007203281d807404161410f0350016220401000703c00c0c0c03000b0f881e600c20040007800074034a0b1420441015415000258110015501071001e640e0b1002555600e0103a000010403810070394000891900301540d80b60782c402039000004411102d80d1f51446201c0e40300c0c4001c03003441e4100320781d4149000e0b0076026400041c845440c1041d074201640c8001003850203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 680661789 1250 680660539 680660549
    0x3410c1203031e070e1e0109060f02150c040e070f0327080c0703170903100501080c090c2a010501170a0303020304170c010213090203071d03070b0a080925 68
    0x10100400e6203144100144002a1700c09000001d03803c56008481c410320a0000085000400b80030000c00ea0600c00c22503980000e207150001c2c54170500c00419a071700060001e201c201c1c034840610001600a800118180c000c030041c1c0c8410300114059038008003900d9425551780c0c1e018001a9440d0b4000d06d336000d1142d1030b6030b003260300c031620380e15101c60702800d103180380d48081d0144540e809600d0341e488180004001d044012000c0710441ca000d101c4103000d0711024400c2420340e03003000704a07080b85c0c1401e286565200380030308041b92528142c001c8181c200a962070703208014500030066121925001d205840c00b400c0c04410003a000808060340079074a41c0c01e00b030006c1c00c02d074010000c1010803291500b82c40e4400100410503441e003125002c280d000390415104000d01409982d40020310001e10300c2160300501a60b07403a540c6200e50180e50480c1d0b081fa2510194051142820000e100c00e00c001c050140b4072120b54600d0710074100003140f140740106841c00040303150740c820810710300f202000601d14100c507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 680663039 1250 680661789 680661841
    0x1a060310150e04060e0304230a0e0c0d0912030218060315120f06011403100b0f01030b06070203070323010608030706090204200a09080703410c120303 66
    0x56540c4c9000d401402c50301c140b45800d8807010030081284400c1d90040883e00c14034100c6040d80d08403050812403140300c0c52044001c001140303404102400c81031700091040e84400304010480c0c12081d51580100402410b0403400a03074040f40d1030315454603100d0000c0c294801210400e080d41810300840c5182d900010515124410111030801d04000500010b0344012500050b125690303035466404003811440040c8030311a0048411502da41c605c40d129103141c80101034072240d00c0800e442c005500401c0c00201c107591001003403007801d0060340e00b0440c0c40081d510610b0480c900f48031031008003d04004a440c054100c0c1d0404501f03000c1c184001081e144071a40002020524005078000b0400411031884c015001200d030f0641340c100c041415009008080c1140d90b0308607104e5940010b42c1e05c0c0d0b01031340402460100c2d40c04c0101005a200446020024098aa1803188561402c09904a00c1e00d11545850541150009841c00e2402c090b400c250343c920440035524500e0145410b4030122509181000c3c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 680664289 1250 680663039 680663041
    0x1021002090907030c0c0f0507060807020d080f130606080d03140415150e0f090607020d0c15110a09030312050f190b06130f0f05090703020c03071a060310150e 70
    0x100f41b103012500c54a0b038104000381b41c000114180301307440703020b00d00030140070035502e030702056070740d840001c200451904d140c0e24a4490340b0340d50b00000000030050506022a8081c040032808954144120001400001c1c010522044c6441d4040c0c281c070261100461415280c1e03041002081070650740c0c514a0000c1c03400014050410300c11112490003c1e04100382400c00c0000704607090b0426020a03011710308810031a40140e40c7c80b4812039507070444c180d0384000204a10b511600040d95000400a12005e0103004100c010191503d48415000301074048000307035800004109060f000f0071034820103940d0210600c40340c40c10400210803d40042d01c14032000d1003009903070130305071560b911107080c40d800209456510860148000c4a04a8a008102e0b8441e0724031400a03448a10904407c22501c01410992099640c40c400750001d4105e20590390850104005c81c000061084000f59030f0051605125010781c24000141450100040c0301c0ca121940303080070b49544440940c03103074030803606d900342a0701a07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 680665539 1250 680664289 680664311
    0x30406080406021b0c0411180f0a05040c2303070c031d0616020306130201080c0a0e090a0914060709090209040209060301080a170304121b150b0102100209090703 71
    0x284680380000400450f05544500c4508000c50382c17004030403048906000c180420800f00c01c4e14452401c3c07401824542806145141c108090304440c4100300500304056165100045070a58210442200006800e10b00810380d4001d511310034102400420710103401d6144c81000500205800c2102406002203860710b0010700325015240300c904e10380030386a00e03190182c02c61032141d000321000003207100b40103035800243c0798603c01c90f002000c01d030141c5d0341c003505131143c2c0d030b40c4080c40c5d1203070380003101304003041c00342040b540c07034104c0014050b186240f80084c205429003440c1d07140b801c0024040b5002d4010780c090000c01e541c06200181a58800c06005035101405800540203100381d880c040e4000030084000992060041104e1440714019010b10220500c082c104140521007140d008060035501e1440084013071280c0701d500c1c4150305801c0040b1190250741c540c0710050782c240e40e580740203513140c203030b00700715940d051001e0600c50000940950511010000042c5c40030001402030040658031034107411 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 680666789 1250 680665539 680665541
    0x31b1d0c190e0411031003020603040c0e190c030c09031209080115080f03130e0720100b01020c01080c0d0b060d0204052b03123911030406080406 64
    0x180d404201c6610070081e095000020742041c4076900316a102d280340140306607110403a0340c2124414609004925503e070b01315800c0089682018000340c131001180e22b004100800b215076a40c2c014081c0e120007411480031a02141d00383c03a122128034080500702504810940d42110403003055a500c8080c031902c411155404403442d0b1072503031041c4502c2d0f00301031003102030520701d28641058843c030340140d40110210259040d601d00c21181000c50b02c0050003000c2080d0741e40410005c1d041403c9184c514105c0902c0103002c00b1403070003000741d0091034000e480307102d40f100d01c2c40c801d00d050403100f0300203004002c1403400040c2007400f00078019141144000344030612400542c0c000c01e003500d0028a91521004041c061030000c0d04a400749600403540c0d582c200c0104000021340b0303000001542500e2199070443d55048513014103515000e49000c1e15644540c1c800742010a0200c8000205103d90800c19044a10761094000d0b03420307800240043d00d60428880d8030003100b00c40590b841c0f42001c143c162a0740c50301c50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 680668039 1250 680666789 680666797
    0x2a0f020c0301140a0e0c0d0602070507090f05090606011d06070f020a0303120e030f0703110c12010b0109050402181c08120f0907080309010c0c0816031b1d0c 69
    0x15030301d9441c01000e8410303205aa0052400389000d0b20040100d200e000f03902d01e0b03458008610b000d41c01b00a00344010f0000d09a80c000f001d0f424424019603c881d1b64900591301980d4440100001050b1540200300d10305004219180c0c0c005001d2034001c1c6121030060070386084802001c5d1140c040d110010f211010310440094000c03209a016000e8004140d580c24002c01000e4104209000c003410003c0740d550b140c0d130020981320300800c450806450300d095030380d054070203100c101400c01150103020f0144103950740d90b98291000b03a12110000c203034140c417417000501080164000714482c0d0300c140425007250080d820170220882054030b2060f107842000c840c0d0302c5100c558181c010115040054003482600880c00d440d030242050741d1400080761250030301903860790f00301c0c0140400b40c7d0041c06103105a45c41400c2417620607008000003d4003a440380070050609100200310744840110401c10402c010001341044070001a51124182042c20034080f07821080a1240d0708000304480d201041112001100b26 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 680669289 1250 680668039 680668063
    0x24151d060c01060b0a05120709061209261804060e130f080712030608030c1c180e011a0f030c0702040f050a091401020a12021e03010801050a2a0f02 65
    0x80f07074854000c6000109a580481e021f484003404203400324220720b01036500f01d4190f981946400c81c1e45000ca00c00d400003000e001c0d106039588075032000318543c04180c04110390b00e04042c03840c3d001e41d601d0500c05040070400c405182c10b40510301c1d2060811188085e2800749030011011404508000a10f04004591000e0240e001e400304000117485400c001260f081c514121030030f42c4007071003035981c4d0341020b64983c01000090616500007509041801c000e50700b4013a21000c050400e0a00b0903c0031001503107030ba60030342000d070260003440c006020846803412080001e903520110640741144454041c00a404007070050070b000000071034800115034464014003a0380c1d110403020003403443c0c1a25002c0c0a850b200b00e0540e4044401050082814010300854120101030348400e105103c0304240900203511508030030840c0d20805400e041d0042c2c2c8040150b000301001f0001251a0504003200d0088404070140d2002403407101c0c00300400004901c108a282145604021130001c41410060b41081d00c1c588030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 680670539 1250 680669289 680669309
    0xe03031008011401050d030f09180e0610060525080d140106110c0d1103060f1b0405010f032f0418050618090124151d060c0106 56
    0x100900c6584038a51201124101c0d4000c0c0301d20f0000150f450100c010a01032250490f0030582000080f0b40104d035082100d0b00a41350030500c26944100c213405560070310b080b10030310fa07031920405203000f00c0c10003545400c1880c040080003140e103880c101901b136106007074645e035183c51030801c402640907841141071801c5400030009a52486071030030080042003c85550321207100007400100300284225100b00026030071000130116029000c0c10029220203071b04003101c65001d0000e14195544080c0021801080c4900b5500f015050005c010054100b01210340340b0722840c10b010800151b82e00c8240c0000d0081e080c1030000c4c40d4411000c900c030910240000075201c89221001c00211542407000500480301d001a010310026030295410b801d80720241d4401d41e0011704594181c000000f1002059004400d0310f00005562203003842400382c60380f14454107800c1c11480c410421034145200c0d1018290080348c50034070801081000280304100c1c240d4202d5000d21008528100700c0603096001c08054804110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 680671789 1250 680670539 680670541
    0x10204050a12030f020604030e13200903070b280c1403040504230406180506040c030b0601080405120c15160315060203030708071b0308181b130e0303 66
    0xb044a8402121038040f00000c0042c46606101440851214021945a078500d024070061804100340507807512030705440c0e255180b44d204202c0661990130320303050460031182501c6140320001c15040450381d52100f0003e620030411021003e0300c141c0555940308800c10044e5494144200440750580e0501c00101101005140d4800580000025000303d5000f107a042c0b181c032500d610000240c91010301038119140300400464000f501d20b8102c80b055042041c11440c3c10000f03602c0b4113260050076502035078403544038101030051000032055240d1060007030078581010300349030742c41a640d0f044841e46191042408159035006130414440c141d119010841e4081e005d040507142240300c0428007408002192030701a02c07501d0b2030548240c2804a4803150051030a5580d056402c0e19440c04c014a50000c11080b00e5442c03084282008d988402c03030780a0750300c1c0c40c42450611741c0d120071000b601e0441070b030b40d51140c8000d040311103500c0c02c0522100000c0d03440f0050b008600c40350001415009007a162940000300c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 680673039 1250 680671789 680671799
    0x1c0b0f040f0206030a05040b010506280e091003030e0906010507121101020f09040b040b0a0e07120606030902030607020102030603071e0f17011b170618151305010f050909010204050a 80
    0x600100e0095008d2003040c041640e0b200100b01040c80f82c0c01002e030a0030980d1140326040b0440c0030741610400034600f0501c0c0140481c2c40012030080c01140e0400a400c0140e00c18801d069120380003c185c1101500d01030700908082c0000382c601d02900c40000c04089080118100036845895038040c0b440030b40c4000e54032902400100b403c01d0700100c005900881c0b4150341d8565602e401c0c09403500e00d580140c410446281048403468000030010026814003880d401c0303a42251580d03214920040c030076650002002241c07441050306115005c0c00c1081160b0040c818030805540c0841c8071011964101d844041da171002e094158094140e5038040c4880300b007100785c0003a00006800320800c030312031010003c101e410054071103e2044844002102c0c0003070550700007004204105802c45410a0000344114051040701403c2c903400d1000300e1307079104e8226050340981c0e60340c2060211858124902c040620444d03040c03191011500321240f08592040141e440412888a0291704450140c54003520041030641c80e5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 680674289 1250 680673039 680673041
    0x70905010810060915090b0a08041b08030a050903102c0102131202040902040f0209041103040206160c031e03090b0c1e0102040f03111c0b0f040f0206030a 68
    0x14820580071903400000203205142d18403508042d10225219003100300c0c28500c51018850082403103c007800343c10040030a90b0b05c1404090110035600340e40341c800c00d2400e403504d8240381600516041054185035410711a80350302105030b803041002c40c60302c3c54031007000400103440c0188084214149514080102c541d1199212b0307006010105926620441c4188107402802c038420380b14004520141c103581170100212500208101c207000500100390107900303400182c122540c42240c1540c440d80065503288504043c0104840c5000c8190602c0c110310301030300401c01d07030312a11054100c0480b0b0442544200200302e0080409142c225076882d8602096048040070545a00ca0a134081403070900002010001107080700c10070300b00500a03185500040340d0b94800c005503102e03c42040e54084c88003107031010401c0f000340c000b0342c0901e510408043d02902841a01000984034010344200361b01c00801007000305803074542007001c00c0171110f40c1c1d903510b0620061100203000b0003580a0000820f2100d00225 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 680675539 1250 680674289 680674307
    0x4030302070b0715050601050f0a020c31090f08031602010506040603020d0f02011101020c16080105010b120c040f08060603010b010206100e0411120a05120403230a0b07 74
    0x440d8084a03503058a904041410740203403180101125100c82500030b008205400c9190000700c103040050808001c0082c040058003d1621440141c4c091080125645403038100340c6100d01481c00e1980043d403156040160790100c20805400d0261078140c038504000c4118a0441d0181d042002c85840c1c0c148210b80c140c03084c00549170040198240004206646010300c2910212507005140c648106c0050352440000b07083c0040603418000705246200d5019428001800303103c0c5060042e11609181c8885100c1d8101c4641140c180b131f0380340500601031881d010741126000074902c500322086517034982c80c100304c80c442d940000c0689024598001032040e000150140030341001c9000307100078a1920012a41c9200449175042d0342150303540c1c1000581c2000090350f80181c001c03c06003040354003120201d5090305100c1c190132170542c40400e0340024850207101602e559a502000d8618107407440e214924400504600140c1c27441c00e11017500d5600c031040100c021000d41c0507902d0001480c004802401c0408 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 680676789 1250 680675539 680675543
    0x102120f010f0b090d2406061e300f060612090c121e1218050901050f011206180c05190c0512040332070b0306030c04050c0403 56
    0x3001a0001c07078031441c204500340076035404000e0141020034060422000252103034090702c030000c0c480240c116800518103c000c44106804d404101e1b1441c10000a0240d28160030130300d8008840300a15036440c0e4011031400031280c040a142c04200700e1038405d09140f8444100408900d4582020716041c600d00741c010804813585034031002d0602d6920fa894005441010000510035031001c2020300402110908040d00c035405912203c0400080d100c460b9009060f12006450b42a5480b900262569211032582400c041010025502a24090100700c08010602a45e032007400c42c2d0404801d1030b4856811210015803040302800b90715501e428600f04440504d10b24210346080c5501d07002214050800c030f07000c0080002d0114840101c40b40c0413900d101e011b0f8001ca0701070160072050351142c0d81941c045d201075030241c0345000c0014070700d03107848400722200520f0070307002002e2284d030303122154011494500f240c0342850003039a03a40d5003e0000e8184540104940d0740302e071411003402006101c81020f0f000380d074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 680678039 1250 680676789 680676811
    0x1204060515011b060f06030602040e04021207080c061b01020d1509021602060906283c0912051b0604030c0311010e09040b0a110408030f160203010212 66
    0x285072200115046059003108000c0b0504184640c0c00048850b0702190b5000f8000b00d000034601c1d261364420060b43d12071b80c04108802c0400007480158548902288605103440d80141800e078a00b104842d11044001038207480341001107500800303900c0c0380c4240c00c43c19601c1d8000715501c241c003800c131600500180d110110440550710300460130044501c215082c2e4120100c50a030300e9140741d42082902c1d03100c422503e8110300c0a02100001c019052500da5000658204207402ca58400e1402080100445c00120924125000304001d4407240203044120b408900c0c4280b048260901d002d9605400b00e074030525250700f41c1407522050180c00310b211041d1000c060b140541c080c205408000050045d40030241070400d00e240e0400002d09400002c0c2d60201301030501c0305502c1620b50001c3c0521030210350544000d560b500c00c011035928184039848007444002041800c02d030400d00915568090400c28401740100041c0d01d4140e140000302000010381e0040c0295902c1d42d21002d800e4a05d1015a41c15040f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 680679289 1250 680678039 680678071
    0x70c06030c0e04022b0207050a03051c0225051501150206010e0105150715020403031110050f0613090210170a02030103120e011b0c150e10030b0612040605 68
    0x80d1401e4000c942450b2075188030000f0390988016640050b048000c5160505c035030800180c00019000d018400c48a03010b40c5401d501d401d50365000425008001070029070892040000000250800c0306000070b00c8510b5641c07800b0812035250103450b001074130b03d03c6a284d840b804000901c0380d001f81d5903c201a2041d40c02d484030303a41da50f104034200050038003482e503106400c4c110100c60081550003130000130b40922550318181ba00d101c00f0508a9106400540006e403040160119100d410440070102100749102040a494480f9200d001c1d0b400c080c203800d200315a001d044580c4101c50340c006c40e04058008104208000380d10030058203500f036804401519181400000317100c6580d40c42a203040b280c00655010100903030040445180000401040c180544840000d007075142c2d0030120040325104015442c3e056040511903414080010782442c10800d100400860588900785032003440e40a40c2400b1408801210010f0807d00034003c448260b009050100000d001e41504a6402040030700401018 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 680680539 1250 680679289 680679317
    0x903010f0e070e0705040b040e100803031308130902030901151e120804171b0d0206090d1a0703020a140c06040b0a0219020a0506011403071a070c06030c 67
    0x9846141d004038440e03420a07001000703419000100c03254062528034042d0302c0c0a4403000760f0100742e00640c008041c200e13054402c00a16400444551014062810080d03080d4548a01020150200c00a00600e000e070045000145445000d0f80c00e4050048010b055403a0701d400c481d000d0080c224407054401110981e00006012000c40004502c0205034100d9403103598105102a00c00c990389160450300c5640030000028441c1030482c0c00060040000042e100c1400134848040c0c4401012120611402c4480c01e81001030b40d9140c2101c0d401042941c060904400c10300b80001440005406403801d460b900c4c0c20401c1c540c0e495402000168a01c0d2100c02643c06c4441801a5500030902640b00d198081400f04000c29801d0003940ea0140c08a6405844e20890b150304100e408030513811600940e0003c5881740c204801408414054003140c40c072110140a40000a47c1c0d49507c0d105600d008290f124890740c08a140000f01d42c802900514a81012039640310f0060080122448404c0060708050b4036402c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 680681789 1250 680680539 680680541
    0xd08040213020906070b1314150c04061d0423010f060306030f231002121326070609080405010215040302062e1d0c040f030f1b0b0903010f 61
    0x5008098650360401c0b28581d906d04603010050500c601295003829100b0000d00c01c0b80043c41c000382031a0103010340100d079182c1b28682450150a400d44518180020701c4400d038030583e10303500d4841c0072070750035101c00c1c01c140424003c01043c0111a150514030003c0d9031406c00300b10205040302d40310309540000598504084046980a000091041c5800c0038090085200b071120403005140228518541d036084580807403408d01c09a030000315042d0040742c5046040b144d888581c0c0e0081c0941c8184402120310380d50000f040c0010000040080c0480c4500c458000b40203054500141d40b0450400156000d03041c00d007031503001442070741d00610034980c8c650302141c44840210b00482d8541c00600c0292074001c0b20040c4903500c2c2c0b4540102070600110b040400000c08203060080c12280c0100d45003c007500c0f001512401c009010541d0500704010404c406140c04400c10101c80e004075410210109904c1e00044070615500d0003141560111401300316580000c005000d42c00b4200c00800c42e003020300796000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 680683039 1250 680681789 680681797
    0xd2001020c0604030302090303371b03050f0f03070903060b03011a090612030d06034407050a1109100506030604050402030c120604050601050a0305030a030c02030c0d0804021302 78
    0x11500002c0c0403c0000c1d0083c0c021b02400700008054074240303d10044941407070903211154552681d07a00c542910540c002c2140b18000b140d403842c1c20030025501201011107079403104002000c0060001d81d08690780f1910065440304807002c810140d49080010005000409600083c0d8415140400c001c4981c038052040c203401c5044040200300c0000e182007040721f8034100500b000d40150350013901c02013040c0e0900041c01c80b62101c030000a4190b040d410524864003034080742810710a591034002d114803011001c100100c2da1003540c035604120030815600e4981c01080c500401d00c0c4500c0c01640208000a60b03901c4608405070b42d00307000c0d6555410f80801c070740003c0c42119009001040071840906168100b95031050000c0c040740c51085405002c10301c4801a07000d0712410342c11000a2004100f001c1c01154010700b02121894105070940c5c40309522031040400b40300134195942001a180c84c001d1055410040d2004152001150f0030701000d416a002194200d03c1250002100b150b03031901442a1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 680684289 1250 680683039 680683057
    0x40c0305070e10030b030a0c170106030b0a1a100c11012105090304031a011701270c0302030d02030409050121030f0c02030316030e0a0311210d200102 66
    0x150340503031a20803d1150100b01c07500c2c00e20415460b4428020551002c100404050303101c1c85014100720310340307458419030540345c0030180b000740d041c040c08201182043c0b1046401031405100000c0b2565900c0e40074150300d0352043d003070fa040803440a801c4071480e04110404201401403c0001c441154803004494004030074000c41462007158038100800c88599110960007482601128941501c0b0b07141d095240315803140040007848464014030006003482000382d0126003107402031080d074404d40d1501d801043d402d100000c03402800c1026009010035011040021900036003a2212003500324070094503070303110780200800c0318144000010392000c1c0002030450310a0140c0d29600e502e5881c0d504071f4280100c40c254104210b02812020f000d65400d1004101c1c2c0b0354054802e1102041c0c0340b4014210041c88800c051068040800410226041a050102d0301c80111103800c000721500c19040004500382001d866140318070b0100707541c95074200e4001400c6000c0d0412500d40b012804002a090707104ae1011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 680685539 1250 680684289 680684297
    0x100c02070b07050f121903180f02061b01021306020c03060c03102c280b12010212010302030705060301080304050d060b031501210f080d140c09040c030507 68
    0x820003488910040d01005119070155501c213010904018a00300740c00c00c000c00c803090300003091880e0412901000001d45080d0405000d9036641c64480080d480404501815500c210881c4c08215a9450200d414421904241e0000704901a0510307000303402901c00301e04408032180012400c41c0c00043e010402440c014002c1000d0ba43c1c00f40c0480b04d036040a0326079049002d240c1c40100d03901c2d00e016843c880e20b0700051200503201500040001000001404261a00d6215444018a400d240c21910b5842c500002e01040380c41c0c80c9008984899000c44100c0b16951000c19170722144214005090f040306d00031001c8400c0251035a08210300c5110a1086158540c410402000f0034105224640390b0340e0300450300040d406021401081c00c0122041004802c1c0d0402001844012a151101c205070b621116011410224940c3c0d000441a400b94024200501c0441c05107048011a0005c103c1e980029644488a007800c040640f030f01c0e0407480c0014401c50400983c903000342e1091080d54030902132691 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 680686789 1250 680685539 680685553
    0x11090415170118020d0614040303020a12020f0a0c02030316050609010b1017060f090a0e0f0d0203070f0809120a0314070b04020105070303270302070f0506030c0c0c1011100c02 77
    0x401c01203c1744a48400b140c001c4e486600b8551000c049a03007a07031040340641c40242e070380d014561006114400c001071201c8414418001c48407044012070542d002c41006040c20300070381410f400000d1460096a903042d0b4010000010f0340c4c01c00901250890048001034024802c0105101c1080340030000002280001ba0028519140008528425a42151024000d580b25049142c0030440c082f10885000d91031940b210480b1230302c1a000c00c403110940316803502502c0140e401400c000e403203109101d000b810544042050b00c092103200b1048400622005001410024844a0702902d4600c0c6140580107c1c0d02c1c18015a5400004821980042c1d40000d8402069403143c0c0103440c181c002d040283c040594915014409041c8c00840200990002140c595821080c0c070300203107000386981050131409005c040170030491701d825041d03d8100a0070850f450726000820709992401400030340480e4490354464440e90599009030161600b912600705903542c00d561440400152ba440d10380340d00050744045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 680688039 1250 680686789 680686793
    0x6150415031e0309081203041a010614090a0f0f03021008150d0f2a0b040e060d050a0b010e061512061215010f0602011d03090411090415170118 63
    0x542e00c062403003410080e081c1034403504554589010310520000d01c1000206000901100e80c1031142078401018200d02158107012000349501510450090220b6000c44e11882640d907440004000c0c00c242c0d0007511600740c2c1c0d100f050105080c40d11050740540c444445a0354100e22a0741003910614654032290145809201481030f9506615000e403503d200e2070230b54800140030f2a014142e410f40010480504104000300c140d401d070940d50040b01d101e1402c001c10004040d07501c1346140c1c041811a80e548200910341007486c1001030800b801092080078000100c0d11400c28601ca500980701501c80c11008040302e980d410051050080d1001e0800e001d0000410601c6d0117000c1403038240581c0b00340c40c64054a4000c0101e003040a030071001d8981004001406925824403a150071660440c1281e09418048500a5202d2040c15035081c09261500c800c40134030030410307044440900e40070b0f00803c5040302d540d001101903000b502030804940d0807d40c0c171000300f01050040c0400b240b0a0300e00c0700c152035425 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 680689289 1250 680688039 680688083
    0xf030305040e0c16060f050c1812070503070303030f0507030209090a05150d06090b13120e04150602060610020d0e0103181a09061f050d030306080615041503 69
    0xd00d9043c0e0400c00b00000308221040c141c00c0e118035441048040780146419041c0416500002c045440a1209105200d9841d81108001200d24020349034102400c034400c40741403c1c4105c5800c20350300f611660f00d0010406034540c0c0041d005e802e500398100034503103d140e8101c06030707c5a0302002e64440d2178140412040e504560095400c1b0900c4c1ca442c40b00141060049108501081000e8504a940e0b20001c0c040c410590012039000a00c1e201c282038421032a43d0340c1c101028408100b0040141d80e07c03014000b0b88aa90003a05c1e03103400032030200b000f240d40300c1009560b00400c4542074060300188c0c810551842c000280e0080c2d49469448a814202820b401140200300f02c0c6145840480c41c016540003140c541030650320083c0c103c403003481c120324001c150585051400b0b404400510b00c2580501004062a54808151007003110500c41c1c088050404402400080c7c128411500991042c030100003030142c036166418000ba20144000781e40250048010100e07844040c0950403140a000d035a0b40407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 680690539 1250 680689289 680689291
    0x18060c11030a1b0906120203150c07050a060b12071a071b030b010617040b0a0c0e031b0310200a0212030c1213050c040203070c05120406090f030305040e 67
    0x40541142c41610090b103404488045120b0400314000084105001082c035600900002d4840140303c100f50170010350110b40c2d00c101030841810baa10940c0081480d40d0b40c0c96040728441a0490216a00e0100d1800c0840040400b031042c01d101d418031408034612540f0204507101265510300d040c0410040c0c0c1c3e08140203c2c1c1c84800100d0303202e50003c90000041032845001c4000c2e46c003691589420398140a8082c1c0702c58195880406c900a000080200041d00304d4006075010000000220302001c070030805a480c0c0c5900300c1059454010250004038454210307401c1c10450f40704808407180c0004209145003110507400780c41194145036181c03000174401000003440524514412030b4000c4016119001c2d130b41d04151044000132000147c00c401101c1880038035508041c448941c0e090080302c0b5920310340e56011005000e8051500800090314407030003050414803041d002010b80d0b40304821840710103050343c000d015480100d0032060021132140220000f003025241c6c15155549050b040420f02d1000002c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 680691789 1250 680690539 680690573
    0x1a100f0504120501060806011a0a1803060c020a0b060402040503060610050c030a03050403030f0c0e010804110d0b0610020c030a080d021b0a0308090c1507020607060c0503010618060c 80
    0x80108800548414100c02910b415400380d8000a6020b081098282c202001a07212021581c0c0300c0c54106030010001c4221044000d69050224640360414241000c80c50700350b00141145140050001c08a500450480240c078802d040c0046140e9814040004a0007213015884d0568054000110310b800e19081c04010185682003180c02c0c030042c50304492541e0700c8000502c002980320001c1c0020190503018070003583c1c010751400d0280004141d002007603200346251030341c1002030100104040c800c0c180701410804401600c10900001d0a0070720200200c2c0585426000300d0f2800c0b00c4c642540c0c40030500da80d114100030090a480700032070312000d034207402030f8105c0b40c0860750802041001903090500f000c01080100090441c4202c1400c01900c52240102070301802c1d08280b4210043ea6540c036205510392402c0790324942c540d5883e0011400c0c2d40075104005101c64a8858111103550300a00a141254410f40d1042c40b1000002c4040310350b0901d41c4900b4012807001c0010034002100100074005140c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 680693039 1250 680691789 680691797
    0x3190b03120403121419030b120105072105040b0f0709050a09060f12050d0518030d1e1404180917040503100e0604060c1823010e0303041401020a14030d1a100f 70
    0x2808000200d0031039006a49440c08540d40030560701c04c840140c0b81c044070de110140700400c0380345416128010401d070024501c62034007010400082c516400348040201402d4090401140c0c1511241040d0081c10036024103c114283e02070009403040a08030301d04482e680c0880500443c0e9040041a2400e8100342114201050980c20300401c41d00e040040e50380c0c0f0b131131039559004804200300f41c0380d01c2c2c107051500503020001840454540c1810740000c4808640d401003070361581024501d0240f004003000a0010300040c0e0f141c6000007046606009030044c5c44007141522204030700040c00404898156920080a8200c0300c00500821500d501c4808802140e09080a041c0d0910002404141c01313900b22803002c003202070114510000e0140c44100390102802e1601045501c0800030381e80b0700891045a43c03d800d43d1041500303691091050300c006035070100c00b400c8841140b0114585035006a90a00c080600d071140303802400341e4102c00108045005480300c800d00c00c81200442d0034500890100c0280 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 680694289 1250 680693039 680693059
    0x50a051b09100e121f0e0c0307150c1b060e01050304110105090a050303031906051005040e07110f0c2b0b062407021503190b03120403121419030b 64
    0x70344814003540b450340c5d071501300000b00d000941400c4d00403a802c03841c2a40c02070f40300349159003c90f1400070750502640d8014061802e42d4661400499070201114002000082c041d2100d2108210900f2802c0c155122511008120342e07058004541d940000c07980035046100c0b661041e1079a5010743c0040113205ca004c1c10b01d403081500c070300c00300e071942d40152010035001e8800c0b100f80c0003c158920410020300011541030310140036601004005005c0d6000355100b4901d05404550003a0060480b13400c04100301058420000c0c520003499104d03c01d4800c2e00d4016004d902402c0c1c0910f450055a1207080700d003030100c0c04058031a0700c0e5003c1c0d05100402c0c05400044d048407024004041c0154070261800c02c600c10b40eaa003038507105008980d0842150b80040d01d40900500845030441280ca541c1143e640b6000a103d40003440040d1a01031001008000450002804810b100d106802401c241d14552101071760354600000c0f00e0f10340e03c0340f0b07240400c07140e1051003440390036032081c0c02144403c10014811120 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 680695539 1250 680694289 680694319
    0x20d0501080c030a0b0f37050a02030c04090b0d020315100b1603050c0a20030c0904050a120306050603010b03160815010c030e041802030601060219030c030c06050a051b09100e 77
    0x2260807c54150900c11490700d0500651080c0c034007641d0b90014200009604500307180040b01d02c503010b6802040c20240e1120040350090300c8a203801078849400808845050302c03030b5410440302803000d413146a035400444101140c3e5424890846101740b080d080c24040301800c544049500d42c01ca80e0b04190035004e21114100401c1d643c8482201c14260106604c0003a60b400040525110110140a014455400c104008200c01203400d1514071303040700480981c2401034900304c2c000c00540c1c1007544d0024011001090203042c00d4091442110000780c20f19042607001c00540380c2c654115880d170300d481c4005080c548030f5440340c000310344120300ca42000c41d400030407000000c0550750443c200d6003030b90040c1401802585400c00c407460041003280090300348048032030320700c01c1d0001501e4030241c00d01044080302e604061007107118618994100c9030803c100d003002007200000c1d0400303607480c0d4810f40c01546004030002052003103d040090060200c008401515015108804080342e169400f00180c0b50941d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 680696789 1250 680695539 680695591
    0xe0c0c07061214090a06090510020c010507030e061003031215120314070c120c03050f0601081204051315050a03030c201e060d020d0501080c030a0b0f 66
    0x20242040b41c445030440e020801d00c030030481c1c1d00a5100340c00c1c010110140061400081468500075401020100ea0b040142c03c3c414905155580d54003103040c400114804208810b52040380a8100740e038081c444030100c0d0414a80d02d0400380d50304084148000c2741000080c0c09103080800c00c010006012800c90540100c0040642c4268411000c542115116104050f440031000d05100ca50444660a040c3e164460707103c8441c1600404564140325040c9401b071050614075800250f520004030344a003000309125039264031081c440c01c08144907640c1c0050f0b071101020103403402e0b41d402030541500100f071000c40c1c1c006445480c020b61162141c4941c04506500c54032960000746000e6122000601310380c0c5030503104c2060204284008480311035005038580d441c00c00c1e0146503580c1084001e00b1001c100005101446504408501244000b620048251654011710304039803441094840c0840120305040c1c84040140d0010460002c0b9400240c000c0c1140c02c415402c0010014440005c04000c01c0c071603 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 680698039 1250 680696789 680696803
    0x90f0a09090516060206010b07260d0e1005010510120e0a0506160c17090102010f0216060509010b09130507080a111002011a150708040306060302090703020406090e0c0c 74
    0x10712103401c1003403020143c058401d840707001001c0500c0104565807501c030381002070f40900e4400905214030681070b9a4009085000d030b41d4a0b0000e900200e0755901c224101030700500b05940d416030f0900410451544c01c51103441820b04075000030f480c1d500c001c4441c040445a2125850b1564041540c0c0c1a010426120401c40090704511031401001141800c56032455450b1800c407111381001900381c20440007803400e42150322586001602f4507200c01c2030030010703800b500d010180242e03114404240340c0350b07460000d00b100d150ba600170b2204100c141c554102079400e8a0400851360303085101c0101203000780043c4240610181d00600070f440049848019407070811030140025074812201c2e101109580c078005040043c81c0b00b0500080180c5000401c010340094070a03589184103040c5c03050600c5c2c007a007a4408407a4860782c0700d89041d130344d80e40f0b03440c02c10001c10710f9010a03030150810340e0000300c51134085c3c0300300c0e41942c101d48c6403000414a0000d44411010000340400c420560078000c20310032040410180e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 680699289 1250 680698039 680698043
    0xd02030109020702120703030210050406021b0304050a090902300313050901080613080a02010605130e0705091e0a020f0a020f0f030406200f030301030302060a050f060303090f0a0909 80
    0x5a503c0c40a0300400010041080000e0b265802003441040003e80000d0601055135421201144943e00c50800340c0090164880103800f955411101c031086450200041c402d880003100c000301c00c01d40321200c20003107445034a8000d4100d8002010201080b50702c0400d19844c20140d03040c40e540f0f4807003020030381c11a000700c5603600210300c075032106000c41c0c60031003099800340c40c800008084600d8000103035645503002000207010407038005400a460340c07007900440043d2078050030409040191310040001010121841455401142400308092400d403003500d01449a0640d11140c40564128040758000007500313a03044a682005401014108540501100d0003a50040c06025041c21103007400c04032402c8881d0441c2d0001c2200380310300c0d900303d0850700d040f401c1031621640c80d4001107005460105600403035141480084000000c15600061b0580304500f9800d042c040780c1c82d02d0194501b00c84003500c0c0341f0f50540040c00741134990f0a01641160116500904c07031810596a04000700888003d2541 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 680700539 1250 680699289 680699291
    0x5030a080301210201020307060507030e0307080301090e0601060f0311070f0b0f06030c0109060305090c120f070524090f0a3506010303050c030d02031302030d090305061b0d02030109 80
    0x403c54040e00b024501c980c2500400c0398508a180d50f0b00003510b900c20001d00610056903100480e1010340b003170b80300e040c0a000000440b0343d030301c4082c100000e0341d4009200c1c2d00394050410100c0da00042010910034100c43c610340f252100c92813142002e80180040d425501c2c0107940c140100000320380104c00c6c1030103942c040c01d142c6240d41094100c40250040050405000354001d8000c0c00b0b860345d001c40c2d00011202c1610b0002985e456a000803401c1007941076800340e01443d1044904450980454a03061518108045604050b61881440004c920311000104e01080d0360740e01c290f03010b00440003000c5150303006007224065032041c00080e0350346500c0e411000d200000122040c54a5840c11940c2020820300100d03103000302103482e0a940e0701e40c01408010b08000d0082104401d10f2810010ba48603012008410741d128680401d101403d0305100300168401c0c0301e540400260075000c1c1c0c0341d40050702d40040103000c07142d640048086d003108043e62030f9800c4442c10080504e0302c0b403251014601030452924 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 680701789 1250 680700539 680700541
    0xa050c011803120e06060f0f040e0a12201c0c1703090c15090f031f1e0e10020a1202030a0b011404060801120c050d0b060a08280c05030a0803 62
    0x8000c4045908401d07202502d80e00102c14000740d5544c40c11400002d080071200001460312404c080f4016040140112109103d200425420040700c10080c0002402c566500c0020f4202102103050053704160000c6950f0000348a0380003010201443c00c3c40d41c503640c1499600103202d0340d20500c0a6030f450561442601000c0b0510500c000184903116114800b00c8050042c40c422000941305481100c14462040c04000f130f01e20a21b840c140701c40c0361700c52040501400c0c0703102905202000b4024100040c5d1107200a1402e40d10100c2e00d900c2070303001c0030740c40c4402482640030000340d50000b5400880c1a0050000030409500c001c0c00c07500040d80b14030000000860305910348c4001401103c4045000c0b008030200703000503c01d06600018580c1156207003842c3c1c4059046130300306000811101c0d00310f160042d008811010034001c004070380c02c0c010070080e40c440310465920340c502611142c5800d910720075180e05907864000b0b0501c0501900d45140030740d503401c6820340e603003001914041030b40070122903400d0080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 680703039 1250 680701789 680701817
    0xf10140c250f0f0c06080a06050303040e09070b0d14071b02040902010e19050a060c03020d12090b0a02091e0f0609040e0304060f020111040515031b040801020714120a050c011803 78
    0xc140c560001c0070001f0a0040d0ba00303050000780c60b4001c0303018246581d00303401c0004810003420004403006019091050741d82c2c1202d152100040c10000080c01020721104010800c0d00744143d51104001102c981e0f0320011202503800c000c05010b80d8502a4100080c401640003c1c2d40c0d1f120042032807084411000800600d00f005000c00b00380c043e0302c8a4284a407104100300800c0c0c000c130310721034100744510704104c036901e41e116200c000b1310b448140685083d03030300c0b01000020740d0b0720750090848180403200342c00ca542c07090700040300880791000c000313800940c01041c01209090000160055010050000c40c01c0c0011303000c0140740d42c10590011000500c4c10340260030321502032243c0b03155001d484202901c0c01d03042802250140c0d4040183c8525a900003000441415410241c3c84111804020581d515523890200b580030b50410407041e03425164040300d01d07810f00c6c000030f00c02e10b03080c0201f1401c500f4002201002c0d16540c002c51403031103055480700203031000030101d080c00c07600c60b078401c1c2c58034054081c0d10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 680704289 1250 680703039 680703047
    0xf010501080604020d120507170301060206131101050c011b08100b180918010903020607090b07110103020319060303020709060914011401020f10140c250f0f0c06 71
    0x1030780140900e40000c4140805611400550700c0d07031a4203c0d030740801c10f1100c081c007124036204600010381240c82c90b2034510402001300c0011030480da02c6608503103068032541490407035400c28075002404005c1c003c00740f120a501810150240c2c0e544807000241069030401c0c030760b44000500b109100000c071210100100e0b003101101810140c190b88070020300b04140d80b40301821010780844400e1140d081c030b50000740c807910002004482e00508a009004110091402954072300007520720394085a40b4180c0441c425034003505442401e600614118564901d0400650080d1720140c02002c2020440782000301424440c014000250301c03d600400c1d445140502074801ca607050b4000000b07250502e402070000d03030024403a041c10b40f0711501e000700004000e600140c0c034040c0b0b14204604240980c560702c4049192a40c0990b403500d130050031408965489440743c80245c0300c0c0440b50706080c12a80401d40011070320240104045202c0d0940301540c1905880b003401c401c0003c0300413900301c07082d601c0600c030690b40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 680705539 1250 680704289 680704291
    0xa09030306060c05030301290703200a020112020906040807080d1e1d0a080106090207061a1011120f0c100b0d0f2a08070503060601080a050403031d0f0105 68
    0xc0d85007010f454055555007a490b8070061181000901910390a11040c8604000d92031010b4140d02409585140c140f4002c0c01d0752081c100d40e00e0694000460b9100d00c003401007848a06190b05a460f00c01010401e05480d00942200c540746030000c406210110300e01c6000c1145002500d4100000e00801141000080c018184900d02c07030760580592010600c0240c03c4103007181400b4003400e1031801c00d041000400e80d8401540d00400007503081c00c5001544c03d103139500a019590242d841801038050607001e00c000f0b00043d0040d15004200d03803040a0956100c3c130001c2009061000513107002c0d8a40c03000b20103950300134a000045107000064030003101d8404008041541a2020082c406244050700049d80c031000c004000d40400d6804240d1003c1160b03004603501907404000242ea1009620452000c4000060007012120704c11140081202c0c1380c0041d0052150070160b440c030701280e4500320307407401500f0040d01c200c0c145511100243e00d45403142e00d0f242d2601101d04014210142c8001c501800c1d150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 680706789 1250 680705539 680705549
    0x10516140307061851150608090f030f0a0203120106031e0b010203040b0d0f15080d0e0906040b011704081312050c0d0c0f0b070c05030d020a02090a0b04050a09030306 73
    0xc041140070411076180200210b1141c81400116000c22410200c1e0040000c401e400c003a0407403030306d2450201d40503401410010b403800d0740d65100a0b41e642180e2260746a688884154290388140001302401454200130421011180305480c103100018540030b403245000c0c0c2088001c2920303030002d000e9928810b0085500c5603580380c41400740f01a01c60020352640304038002c0301e8a41100007070300c18090384140c010f40405e0182c02c10400021008030310001c02c415540c0070300c03622800b43c20407145405118606141344043d0091880742c85465007003c210003008641c9101d41032205188298821041980e00d2500c40c3e801002e030310b641d0303107072400103001c9000b015000020700c031402e180c055003c1140018241e40550301900e06400c842d0f5682030200101400ba0300150120700c041c54046a000070813005490301354070136000107110a448104040d1144c0f18003211500607401401c280c3c000d0f10382000c01d16081035101d04001960f042090200d030555804841c2e01000d0b03611404c40d002010741c98030414000382 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 680708039 1250 680706789 680706833
    0x51002150a0f0b0105130b0d0b0d2303030f1317031501020709090804030b15030d02010218090112020922050102040315090b04080c030f07030309060b0105161403070618 74
    0x3904500d204200c0711221700035089000c1000c500d000c03048da1180d00804500c0e000070403020807007071140b400c0e120700010780c405000414a618180c41d032420000044d24025120240e00520703640c1c40318004151280c40c54004c1d100c0d41da02510802010300e4180041d4003800c03600c1003009400065170006890082684c5c4449511480d143c0d1b0007002c80c100c07500b0f90b001d0ba5070020a00300c01e620740c02d030881c69000743c42440503414021030705628403480d0154000c1c441d82d150160402516102c503010462886824072501450b10b140c10318000040c1360501e00164814001102c05400200381421207504241401007140c407613600103014000d2000038a11159106a071081c2401404d40d26942d140040788042c10003400b86202064220801070140180c40340c1005840b1407517110081da0800502030480c0b200107403140e42c034100c1080804d510074001c903810095640c080d007001110944d10001e035030421140c041c9050105108110015610380241031009027441542e0326104198102401d82e401100c20200e02a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 680709289 1250 680708039 680708047
    0x5370e06100f0509090c040305070f0f080d0f12200408010e010e030712050d02030a0f0b0a03110d0203010b06030a060f0b090d030309020f130e012301051002150a0f0b0105 75
    0x9a22030101c1d011a441178421a8490301d4202054103e40100c0d040101180188000820b60054541d040800c0302e50400600750303100d64685955441c1c104922040002500e80c284051146010b0181240100586040016180042204d50080390400c41803540301c944001000c000c900300c24003c050000140b50002c202c510b400c00c0d9155542c2c420404010151000103020860039809103058038a01006002e0955481c500240440020800c0080c4401c061740307840920b100764180030620406a980c01107845d04541101d204110040400310812607040d92190b00700701c400c1d1248000303980110510310011400074108040301e00c4a103210b401031140d1900921080700c259075103c0b0304645440d003508001413000b2250010811070044100503076003051b10502c1041d40c80300c46070700c50500e00f4044002001038103508500c0c142c80c10005000d0414600c0300400601440c0f80041812921402d58012142e03228500c062054500c0021101d030700c0d23040d64405510541400902602e60901024640742e498 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 680710539 1250 680709289 680709317
    0x7290a0e0f0c0906030304031209090c0302160212191a0916050112111b0601050d0807060203070309170304061a03030307120b150904060603020405370e0610 69
    0x3a9401c0810414814200c243c003003102610140202c070091038005000181900901001402c3c402281c49580c1c4118a40703000103c110340f0910a0b00d10025034070a080d40c40080369000c0205500c05140f514105000b4149522001000802542215882a401d540c02103440181000546800521803400ca8001c0400c0d4184150140c215800741d0b002400d05206100300b03031a440000781580c04c40c40c906100c002501030a03050b581d940400101d0407820454a840c2e0706d502c28461000001131004207410020701c00c0f030002400316009103074002d84e5450700050f001860b45030041d00204a50711601000400001d1000303021141c000d010303080c001d000c03055100e11900c0c0c011943d41d01c0000c10000412414548007403160002da0040c7d50000c00060048800f000102d10708880c99110f629a50300c61464400006405402070003900c040b90402440102a03840000c032402001032004460107100c0c50f41d4003100000b8107040400c00252408155641301c0c0e14211b020701c2000100d100c2c03400d05100003d054034036 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 680711789 1250 680710539 680710543
    0x51506040b030a2a18080f0a0314091c0501060503011109040b010221131e0302101407080304060e060609131a01080303090714130207290a0e0f 63
    0x2412801d0154002041000c28026203042180c0c50404034001c0c400e01a2001803035400301d01072026840c89428001c0d100d0740c0321800ba076241140107c11440d9000307000c0300b4000c2070003045c1420366500103038941c130701d400444400038240340d51500d440d500f007107610340801050103030034840e000191000790020031444d4070700c401c1c4140c54090980114071444c0c6035625048140d209005540d01001c030a01d1218030110401c004040a412042035024448030340c030030000760194140540d85456101c0c1c41c99841983c00d503005c0c13042c0e00e9904484d01f020b000003500c01c895008401301c014504076006000702501c0c0d00b00303458100e090300c0c000075440840d680701364140400303940c03601c07100c80e004540c5424082091419150002415020760401000e082e00c15000250315500800198030821000040c1d13502251501c244661070700128060b03941120340c2417000261048030358020480180148036466008003808503034440303500703088a00c01c01c2107915010300101d00b58034041d580d104244a400360803083c032040d60f440d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 680713039 1250 680711789 680711791
    0x1080103020f040b0406030308070f0206040b0a02130806101809020f10140712092106020a2c042304060216080d141b03061e040c03051506040b03 64
    0x20388941c0c510700b00c02c80959201d41c01401001c1024005100407962402c019199540c05c440c070402103060b20403800c50711480030507041e210b168400c2400540c0d41b520300300100203403c8440201b1143d00080d1010401d00c40412415201e404c200700341111160500500b06400e15141d07d425043c18208124600140c0e515000b07042203d50640c0c5281004040034812030b1500f0100c2d9030110b0221300058840c00b8010f1210b5000509101034460f90134080c0c1c0c0c0c0c1010704440528007602c64100303969909000010325030f48c00405c1442c11030304e01022403001044007110804806e500d1a10000420396400c5242d041a0080e80904241e0019900e0482400481000c890700010b0000b4486a400174000c0400c0090f410074883c80c40d0441300c50358503216080d00c104001e0840c2200704044149003030015507102180072038000401201c0200d282580c03a4113080c0b1000301941070701000d03c0440c04410341030a403a64810800e003208650b42c0860141050b03180c0c01c120402c81d68030140180000c100a018940c1500116 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 680714289 1250 680713039 680713043
    0xf0b0a11070b1b0606030303070518010905090903190f0c06020309030d0618200703210f06060e0d0201021c0c08030f0a1a010206130c090c18080c01080103 68
    0x8448211245003200d03090540d660401c100582001c1258507003101440c008401d43d00701601290307050340755001095640d0008032080c20000300304000480c040c0c1484d01c0784d4a0b86a2060501205164032140003402d2020111401000c9600125503c0003040320b48080d540746038110300f44440c0001080100406160ba0034002a013203d80010104080e55030030000c450b114400c0c0303441000b00c00c0d222029000401f014a0002120900300205030001e402c49003600c1501200c418449032031b00c00242e5007604c00c0c924003021030303140c0c5c0744002e0001c582d44414054a142505840400110340d420000050560b00340c940c02180034030501c94550700141d03000100b000e54001700300314000e45600c8400d01261000e88a11000702202000f00c140141c09c0300884a1501032101100203004030f1540d5121b00c1e000a84040c031050050f8400700208680090110b01d041da110300036184c1d6102c0301d8440c039640040d50004695800041c040c5692250450310782c5d840344015280000c060001444000c000800388403041c040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 680715539 1250 680714289 680714297
    0x90b1b0708033c060d140102030703091502040b070f060f0e0d090b0f04090e07030503040905151207030803090111040f03030e034c060e010f0806010b0d15030803060a0f0b0a 76
    0x580c040c00880050703010350031b034100000c2d556032600ca000180070341110700e42162542544200711516110074000d030340944107640c1c00142082c08a864012500040074004c2d1540703943d40b1042491460980203880b00000610010241603589100081110034141c1c45042c82c00c00510284e10440e82c503004580480d1001c0340e000c00c002c170000c443c0e181810300c95440100248170000c0d00144245060300114429814242d07501107418215050250303c02072403540306503a42019006100055605000d5508224010000107410741d800004051660107074010a80c200007c4078208201076016400290700c1905801614074113a1185440c802400600907105510f0391880c0411011070403940b11282c0300141105503180f00030132086400041c01c241c045c85c000e18290380d001040c3c40c1c80d00880c2008540c03c620003480751360710b40b02210309203800c01c110301c42070130b925203400e1201660381c82042c80145010314801543c03402e1140c10480695582e0b4840d9031002c2411a040120199480035200c84c49502d042c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 680716789 1250 680715539 680715559
    0x810060507030c062d05010f09060b1b1006030b160c0302070e0403050d0c0302031623030a060302030f07211e033609090b1b0708033c06 60
    0x40001148801c1c217020544002554a05582c06140f0340189040348d56031000e4550254a40048509a940300d004108280e901040084007112024414a001d007a041003600c054900f0300242c00150b4495501c240d41d611100b9092002401800084461458003400c02c061210402da602940701d000c248034000c003200f0701200060a15010307400710b821000003100c0401c8a45010100680290429505c0c1d40751a0340c11030880c1c0400307015104201100300b2141d4103542500d4070794402c070455440200124440c0c0e40f12500000140c604005240b145190a000703000c0641c00c144107084c45006681c81c00e2685880e48041c071012440d0360540640300e4000140d8405d91449a04055070200740d40300c06540380f82000c41100042c0010b03403018490045420421031041c56440040e001900c81c44078000d0018004c900118031014800b241c481d610801c24001d00d41480f070180ca4801440d00120344100425610300400001c4401d618004600c440c9200f07001c8401c0010400011350400c1d00601c014041c1c1a408 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 680718039 1250 680716789 680716811
    0x70302010902060f0403350f0408032805030c04030206160b0709080d1e0e0d0605040302060106030b030d02150601050705070f261015080303070810060507030c06 71
    0x1d0040c805003074020f00308640e5400c10030b40310b41c820f60040c4800d4451821583c000c4150300080381003031204000c000c103e82c05101200c2804501e80d80213105948400700b0420001900490a00161000200c041c118107485980d103400351507140152150501040710400030030080b00094015102139a40507a00729490b480005061045e0100485c0301901140d5454100001145e02c41161000d4501400c255103605581c008190765112522880d0704030190421a14241d141c030070030244128160050050100d0905611038100301c82058405500581100700188070041d0035009a441d21007098000700301c001c80c00c00e0000c0d15103420003181840240b003880802d00a83c803803802c0c0d8034465041415901c046036900150800086d0600c10450005004030104091401040400f0550707000c00380504100110394090b10000c0496004495450078400c0e4080b03035400b8204040c42c895401606e0b02c05441c00c100026154000c055400441000760802034500001d604c40c164842e850792103400410081c4000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 680719289 1250 680718039 680718041
    0x30e041103090604060f11031609170609060c070210120f0609020408010e0f0d0806041517101a0d050c0d08030a0513080a050c1c09050f0d03090b07030201 68
    0x600444840309201005210000030b000c40e480b030203113205840400816500e0910082620401c80c142503c209040c400101011034060f2104414226450300510b19a182c1c1d903501c092200401c0710b40007660100040041e0844200724080e005031121242904203801a800034400c90000b030015403c008004000071043d12554011b049201540fa1091044c1a1604070b01c070000d4100b481307900c105609040703540481080100d001c020000a10b0050222504a0312090b1100d10f0090300305908540d54541300c894140400d500b40c0c0c00340071403151410105c40c15000303040c40e00d080c4140c0301442c10715104c4004880f540701041c00c101c210050300c00d406149818240790b818030081021680c1c00072140050705040000210080d4401c64100f881044a500c0d1406815906900024002d080003010401d041e1110b010b4009413510303a041c00110381c6110b41e844850341060890f0340000b808201c11060600c03580c60704e112080750032642030350501480c16003510000d1101d0524480ca050021b400210711041c1807003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 680720539 1250 680719289 680719301
    0x4020a140f0a0b12060409020a061b050a06060806090d020c01121d010917090112020306040209180613022a030c0105070504031104050402010f1b14031213030c030e04 73
    0x900c0d0220559a0701c0e94043d03240e200804c009040b02d05100064107502d420711410070403d802611139a4041d040050540c0c807040b103240c1c1c000c901d00c05550b2050024008000c4007030428070030b04000c6481d0386000c0c003071032400b90041d210a03072940001a60703060b1141d001842c2d406082e424a8050355881c980c41070307000146244079880156602c0380d2040d90096105400c8111890310444941e9040105600096003070b00982c1031460000c0c406648007040700714140c01858202e60001c1c401464104400c0005202980000c07a40300040702800c20401c4501d803140300c4940800c80e81c07c0c29480c01c81f41030141203141600da1610b10100d1041845103040000800c2581ea000c110b110003040242010344010700103803c0751000b2100c1010003010300c0d401c0d04050040c03901495040c3c641081607504042c0503200d0341e2070f40c402c0510aa640a00240105a140a03008000c0b28464040c65403640344a02224101e1801880c01303542258030100b0340c0010303a0150140d4241501840c0c60042169020002005061 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 680721789 1250 680720539 680720569
    0xe13050601120207080a020f03040e060409030e0907170a061d04050f031605010b2b02060d11031e0712050a022a161a0c0717031b0604020a14 62
    0x12002c150342d801c00c0205c100618113084541c00b1a8800c0c1000511a41d41740310340e004224061490314003082481c00e01ea00306440c440e00c80c3c24565000c0101c80c001c10200c1604407007030000030b80d00007458895200c5e4501490b4200029010902074107041001c880403441c10b070404588109030090000301444824032003641407006007800d41703980d0541c120828404070707210f01094850754079201e03002c0c22a25128001ca00c58811004408881c0c00701c807a011141c000ea01101070740c0180c1304101c1c03102000c203a4854a0310902e60002205e03100c2c01c1c1881e110014540c20b01400740e042a04409010440740c00503585111804268404640c944d62031180d44043c0c00340b4001c0a82c00407010300e2044101c1050307040800d04801043c212201c035000150380c010040328034401c2c0480840420012410f2080000003442c0c590141411255000e566120704403d60f081f040102400e0f0700081000d0800c06144204241c41100c0d11000381202d04041e000504001e06501c07034074100000d0103070700c2101611107100c0820841 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 680723039 1250 680721789 680721791
    0x61109090c031605072a1401020303150609030a0213020a23070209040602070b151201060f05060a0201110706090b01080705060a0807110a0302100c1805040509070f240e1305060112 79
    0x213145401c00c000d000307034034040e0014003118031f5052103c9501c0081501d00c200184407204002e281a10f00344000741c0e00a040070b80e00350150b510400c007d40c544143d00000e55002c5032005076524400103000b00b600310220f04094041900c4c245a403190500e074415100710540480d1840e090340ca5504d8140002c0c41440720003042e4001210802c00d5504690140d46c1d034803039081c0d5080400f5441c500c2814201c030050702800012500211051246007003843c054548030b03840d070000040e400140a406400c5411140c4116941c0f500d4034502420031448190f00d500425142c0000c0114034101400141a4003a201012041040703480006660758070440c501d524403218002a5044842d032410001c5d00d80c201c800005140c9030801c9500701c3d03590b200d020602e40c0c0003000c100e611100e0303041c40108005464060700d081d01c0c520989401164854100d80f0b01d030f000f892203070100803c4800c0c50762046203030074401d031061040c0822000b61460701d4450514a1300070101c07030300700055141d84400c0142c2e49801c0080580f451a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 680724289 1250 680723039 680723093
    0x31b08010f1b020c3102040b030405010c0507030503070e040204031a0601031803140325020a0b070e010c150e010f021e09012a061109090c03160507 65
    0x8030466000c010741e00c089070360341082c00008030000d80e61544140c0c1c0e050b0300320030401820121480c40e4a07601880300d000e02e00c04445018005400c400f41d0b0069040045156000424171003001401d00c41d4240d060f405062241c00c04505031405001800b0050006061040c41c141c01031042c0c0d99903046501455200b00d18020400e4404800b08940750100c80d01c074003091426071a0900701141e21800520164166207544100f1004138603140f031a00b000c1c000d1540c0860a105104441500d03410030a1046840e6000b800780c100b45040401341244060a10024082440c0c0d11000a0f40c0c041d074800d0925810011910400203051414001409004610032f8554078028000a40701c0180e0020840e240c9040c400078190345241a00d01c4103442288450360203d1150121518420110181520a9480700760990700c0270341c0503100e800a50302d41e0b03414001c01440024213800f05103010007403150401615200d160442c40c00c40d41d41054002d02c004a44140280402c0b040704009801c00c818105120b280000c0b40340d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 680725539 1250 680724289 680724311
    0x10221070c0b090f0d0c211b0f090905100c090503160608040b0405010e100c03050f04151e060b12090309010e012d090503010605060c0304031b0801 65
    0x41900500421512003104440000310280d0a400b6144500c20050107440160b508600300300c2d00084005e001c440401866030b00081c01006241e030890000264a82050011100d1900358405840c41c0300800311b0496030340003440403c62400d01031058039030700c4070001400b00141c14454500207c03d001d4010090800c0700e80b240f901d43c4500c0840440b4010390445804103900b83c00b000c0c02c6041c60180b0000100a180020081060b00070341c1c0fa0454002d03800010112114950641800000d141c00080603403600346604810754144141036001000d4a2040d90505050750b54401700450600d0070008141c0301c00708203c5001c00c14410001d8030f84e680b0000c00009a40d1002000c05400424041c218802c10b503000484020000c0100e44540c0740582d95104a202c1c0e402c0103403864a2401c0e002c043d51810300780758000fa180201042c46c041d00e90b5481d44042245000b04240c02e40f1040e4016034007403034040c0304181c4489400000d46081da0b500c0017500f0180d0001460001c03050b0001d91107101e2039820f0849002c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 680726789 1250 680725539 680725603
    0x311060a172403070b0702040b180a020310060c111009080106080708060702060c07020420030a0501051905090417190f020c0105031909050f0f070f060314150102 71
    0x1000c03100310b5040802e02d007000c8080644882c0103104003150303420200b0601c0f0051405500c89020b100e0014043d80c4c1c2c041e0b600444403180e100455680001c141d000041c4100281c2440c14280202150b107072284003440c4503500c0001446c600710a140c0500d50541d280f000e418010b08a600c09042181300030422542d135041d60503a036011502c42e141040c094507012420251000c200b4511900c04201c01502d04191607007804020030707440442c039a1009101c246004101c41800c02140658480f440210b16941043c0400c42c2420130038410022136101c1c1181040541c8079004102e40c41b035041402010381d107074900c0c1d60318550311036995903880030440c01296a251640100400740c901480d80d003144c0010f00d0f2000150361070f220940f04c80c0180140f01405d112070f844a600101311081c031a60544c0c1c118002848032515100702c0c1510b0010a4000071410b200314200c400c509001445545001d111040380500c5403554135201606025106403d603a118895900801c00400d40394000d4071010344035001602000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 680728039 1250 680726789 680726821
    0x20d09051e031e0c0a0f1b050f011407020f030a0308090d0905010e04050402041104080d02061e01030f2f0910030309090c110609030306030f070311060a17 68
    0x125580406581d10340e001c00001003a258110080511030145080e0755605080c1504503c41c2401c1c1c510600706004002030b90b070540c3d540072134400c141120542061095400050780340d90002d40c0102c00e00c40700e002d0703160b901c41804009140c1080c500d6544a045002049c052000c603601c1540501c5050344010802d07500004030741c8201500c00689242813100c2da42207529105510845000512044041c000c03403a007a07102d15005480108002035170307821011583c06036002179000351031300c0c1c0051088290703958050140d958010320704070030300e0f400f6905002c0810328800107001c0070f803541a291a503681004140e1004032188109030031a10070004411703448281ca100c545051500030756240000c40c01c10a02c14800e213082e254540c8619084900f01140ca0004285400c01c02040051583d081e80f1141814020140240b01000c040c1d41c1d81d103030040c1850f19007030815203200f42642c04684200040b6904088083c544d080482d00580e440401450461f03983c8011903e1298450b10001030000180c002100741d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 680729289 1250 680728039 680728063
    0x10060302070611300421030b03010c0504150206040f0b0711030f0304120c0c170c0604030605010e010518060f010e100801050f0411030f0c0412050d080a050105130b04020d0905 77
    0xc0c80d502000c610005088029200181b412048601e451a8007180700c0900081560701d03e8001071182d500700c0040c0c01e403020b001712070b40400c0001409000100710410200d401c0305441c00180300900302640d81c5403101a012001400405544001c102518862070382039600c4540042140d880c3e002da0b8240c1c1d0380c0ea6000355002c031400040c1c0c000d0010304901685c0c480000176000503a0036401450980b40102184451244215038042d460000744c03d541c8400284c4040c0d80035280001d110342c1442580b802d5007806030070451081082c42d0300c103070f03e444200c4142d40d4004802d80d0b1502e00c4c44425001a02d40c14108035495a2204000707818140c0254048180e40c12981c080713480c100d0404004007448216002e042e240100780000700005482260500d034240c0e0002035420500c1e04d42640c1d80020800d4035001e540403a02038000c00e950342c510f6a44000c1d0700b604403249500c01c0002e5454440012a1a01400044088107488990b1050f0542c0e403641035400300b800041090112201700c0c034000d40c41d80992039003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 680730539 1250 680729289 680729347
    0x50426070e01150c0303150b070501050f010503030711030129040b1203040320060c06160921020d05030a0e041406030a152d0c030510060302070611 65
    0x2a80c910441c901504a0700781c00d1901c0c0802c2840030003224443c41e0340d2025028181c5415820495180d45c50040002300b28040750661030b08090310b011801d603000075080d1890148003100601a51b90044101c4105603401515000c180303e505010901510125004d0345100702401c1c00940299603000001d5540507045804120140c050030800601020300c04d10841658400d02c0305200240c95124005842c0082c800300c0000002e03020001080c80d0f01c003440843c8a50015403d021035200f4150359000c07945010f0900f210340750300342030441c9801c41810f40181990740e00e640c10442551203030b030b00d13079018103402800790f03640ca038101c800c050407940603a084980110b1800c16079482c0c00644030b1070325010748801030141090112a40310903407641042501040b205176521048200040301084030b285031323091a10300030907680c0c02c0c0d080c0c10101d60842d03a24105250130076007000004460311804400381d8415041c01600e4904038201080100302000047d501c0120001d828809034440826109410200c0d1407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 680731789 1250 680730539 680730553
    0x16050c180105061309230f040c140321040501021207080307050d0207050d030c0f0c02100e060c0610030b0f1902160206040b121003080f0a030e0d120c020d080a0c050426 74
    0xb1000c91164004c0700c01400045901000b804503541002e0b8018082c08018100c598133134400031030404803014103821032581d04c2c00090820503542c05200c034803518004c807038126081001d1a01c0d00b203000e20000f1b043d407003080740009030741d4020242036060712841e640010480c0c40403546054082c000303040da15020008a4682225220710078802c1810010f015800761078044030604000d0192419014002802d900510074812210400303020400b161003409603001e03082c0100c1c550b041c144000407016043c4c1082c100c50804002c40000b14400100112a00f1000141d6444400000d2400c0c2c0781004002507208500290024054001001402c0710704500075001880c0d4582d4074004448600034800104040c0003072041c8079001444101a281d030710a40d0801140078020310082d6030910b40000c100c100442ca50a1640021400504c280245880309000410061203c135002030006000209041d1403076482c0d11307080044904c103500341c1c0c0c000c25400c43e568500008084035180d00d0318840d80240c009114040c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 680733039 1250 680731789 680731801
    0x3110d11100c200307020603041a07030e06040b04050f0d0504080c06070201120207061103090d0e03190f0614090d031401120212010605030316050c18010506130923 72
    0x44500488904a030301c8280c940c07208400c00c03e002c0e20350250041c03403d000600180015848410042d0302c1607200d0711a12200030100d4603007403600b200c05030030709080602d001014001d42c000007035501d40080c0c200001c2c07a10769545141092911100c0e25002c680740c0240c45000c8030307143d0403002410540e1180d4060307030489040344045c41014002c281000e400140d07441540340343d02840e03500800c400c0e03005040c08154030341058542c0d0407951041e00c40200c40d83c0442002e4a0302c503801603072001e099a04038068040e10941803410016034030316010117060000d101200d64100001540304205070300f43c0740c00020083c5000314030079848805105062020070f003441c040c00c01034214652000c1c1130744c8000c0005100307a0760980034081250806283d40409658490010840d0783e4100040d080011908070102c1480b2240d140c440e003006480711104c0d0103495583c040750310040301000740c10305560b010b0390626281c0303840c241803420b0700701c29034480d1103020302d01030048c0407551078000c1501040f6103161640c1025140c503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 680734289 1250 680733039 680733041
    0xc03120309113705100c0303150b09060d0e011d0d020a0308180c03160f09270c1a0a08010e0f04030e060f030c04090510080a0f03110d1110 61
    0x3100d00703c0fa44480c1d0b2801500c0400314040c0e000043c065070a0b51903010f4840c804241c240d4001e030304800108500034010000c0580c90b001da1300e00c4408036940c0054140ca0407032240040c1c021007800d18031524010071303808094551a401421051180e20081c80000c0400340002012841d00c0f0000340c280c021103004211007400044c03050000703503140d580c02e0015514109449900c83c500502e82034103004100d880c1256540400400301d4015000e00038010302440d0140142050506c0e81c00721981600f041350500303038100d002c40300d1078485c00412800780c0c0c800700d24500f052010881e82c100c48151040d0310412412102c168010b046140c1182c5c90f52255070362600320010a0340300460303a00c2c18103010a800600001d11070b031101c02e0040301c0030f40740d0350030200100026015a0400c4400c44074203a404201048a6445809100c1e04410340c410003503807080c1069804c0e03880d200484000750100000554101c10503201c0c503458a542080001541c1300c3e031000100080c440070320300321a08001e11030000e072500c00e20700c9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 680735539 1250 680734289 680734309
    0x602030f0706110405030f070602061503070e1302090903030a0f0614010f140a0c2003060106030221090609011407020c12010213180c0206010308070f0c0312030911 72
    0x10452a56040195642d51800030380100340d44403507103001c203000c00134640d02c040014100900003800a4095039060000080c901407005006d000360100e04d182d81c1c01a5200411503000f50b403031a0001140036940c950500c807507080da844009410041030303000c00c0328142d40800a1805141c0c806401d0106111180002c419a0b5445c040c03580c504210511400c1c544d07005401c03904454000c0e0914070000072490342b0a602c1d98110f0041e44010421000e030744c06c104400c0f41e18181040740700300c0034070b440948010042659440305008040c14036500007000d440d0030f0b8070455000700940c05407075514506d00e0710a04494172424159400145582040c5084000c00e1b0f8403a00c4034801c18071a07008190a43c4130000700082d10040c6595803039655030800c0454107980c2e2564800c0080c0c03007901c912024419041d085403040f14030b00000403045400000062000950040440c0c080c03941105010000b1806400c02c01044410745e1300003801b0030101d11114440a4041d0420651503004d00300700c2480aea2141c0c2032080f0b0400c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 680736789 1250 680735539 680735557
    0x118030815090408040b09030c1e0118060f050c07050a45020906190804020a0609180c0203270f0105070b0609130c090f0e0313030204050c091e0109060203 68
    0x6130502c014050702c0a0200604901d200003000c40c0c0003003669502207841070340c10b0000d135070702d40e02032001940341542c101e010103d0604e007550300807100d64a890340041440010b00880d40c10460000350104480c0d40c100882000f0300340003018100d006903070340100c40b004130415140c01c0048400079088000c001e8200e82c64200221030b4040348480b07420004244000794800070809a02000030b00c298401c81c208282c0c103104d01c0d06240c40c0d012403428117004001b600c1425034020010816012800d001e0b0007200f04c00300710107118465010503400a0514241d0850080e10b1008803040303480b0313078117480d8520415500103400405880400460f00030301e00444c3d00b03120780791018042c1007055001c20b40328180301c80700650041040d444c0e504100c2540d038800c2c0301c10540b030340301412154a604c644000300740c1610801c8407260104000318506018548200c160000324070011b4810383c0c0d0341380090785180c84901240c910f000010801c49000304414800540d041c11107e5031030004112007004281039000100f04c6100903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 680738039 1250 680736789 680736803
    0x150e1507020a031e080c010207051203090a020f0a03060c09090b0102010e12070501060815040209252003040f030c090c08041205040504021c14011d060301180308150904 74
    0x5046031561400c107011501541a21400014140041a4100007400911b86810000340e6106d00c14100b851801a0080940359000400c00500108480000c1d000c0c00855041d6004003d0500c0c000001e44960781c540c0c00500384900b84480c010f429984078985070280e8444000811884103110012401c0f1030090b0405e8165611042d8820015070502c0040c09041c0e209030004505681c40c1c9401c94184524014550722250341c0100303010862034450034696101513050f280d220a4031480b01540a0000001d4070203050202d039004001c400c1d045c0c10b000f001c81e13000709011a50764a55074030003003090403c06d2205407100d41c480e4502144050300c0d4002c5540c095055520b0480585035600ca0006800500c040d0000b4020f040100007a0340d201c0f800501180c004101d820070b2565100d1249800341e6108030040e202c0504000e0050000318003c1c4580f04680c458455000030f00d60711100070a00425024510100c42071100c11007204150340882c0d510f1041c503e01f00d101c10030000301c0301400752940d0140c0d0010505 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 680739289 1250 680738039 680738059
    0x10824070e040f0e0a05070608090d1b441813150b0c1e0d0e0102070e090106080f1b010e0f040504051c050310030615150e150702 57
    0x780b500c2d400c00d158000f044500019400e0316106611301d0401108002c4071150040341040220a401510380c551001c5500c015041c441c00c01c0b0002065280035016600300c41207008860340602c08940104104100c425014040c9030100f080c00e01b50303100103240b00794a040c14044030039400300700080598030f0420034540191007219902041101995041034841c11280d52454036940203958180d0358001410b001840c0b50391000e03a4035201c0c1c105000101c40c2d103000d0015910130125091300007441c1300700d85018a08805e112400d100100d05000325580103410b40e040107428400350820640c090300403200c0190841300007003810b007a4103445800300d9542d19074807008200020b205501440c00d40d0b5001034000c08006a1008000c00101190800c0d00e042e00c550340b0024440e4560b59040c40041803846c0f0b1400d18504501c0d00e00d8109510040a0000a02080d100e403c082c1540c00d031000d600b40900060282c2ca140c2d8003070b01000a0508070603d0036648945110310b10540381190880441e000d4580180011101c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 680740539 1250 680739289 680739317
    0x90f0b040e0a0f14010218041103040b010b1605010f0b030105090d020303040312020913060e06040228051c0e07060c0323040807030303090203070e0f0a051e01082407 73
    0x1d2843d02d80c0949190541c5401620f41000a00c010501d02c41c2039544440301942e400103120484042c091001c07146070040040c08007003020810018119151174440075500c3d006034a20048181c41890000c00b00d43c01c0080c03116044071160003140e00303100f09030003c00c15581d805400700d903100c18034803a00000da0020804a80800e120f000b8000072144100070240c03034000008045000c07a824058020000c0d41ea4000500000501b000c070707250400f008440550800788035462041d07001270910030710052070350055090743e030150003201919180c085c440303130450031041064124405028400c11010709409805808604107014039107484030130340c15a40c0e45102e94080081800b50024030400358800c903900303000004524004010820103184690f601140e1104140705140c07401c4030541001804004140c10098498106841194000ea00c050080307a00e445081c41800040407107004101c6001c100000441c000c04001020707121020031001e4070b001c00b00d51003000c0c0104071055035944001000840400c103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 680741789 1250 680740539 680740553
    0xa1d100b031303020102041703031b0c0714120102030c0705060c0a0507080a11121309060b12070309020d0819171602100f0b0108070c030906140d0501090f0b040e0a 72
    0x4803d00c01d00005140980b1456803441c0c40490b0000c1120340d03400041002405020140c00415403a4808540750420300c00b1070410b0f80380c2c2024001d030003401c5d40070741500c0c0342682c401c86501821050301c03008556904140b161405e05902026080da42441280301003000f480000741160346040059881c1810b08055554642c1c42c0e912001c804420400744500b5880010030a208081e030400c09a42072a0b51080300388400c001c0640a540070314000c0d80780c403600708103084604003210600f111040f42801240c0e140c40c1c00b600101150350002c0d4000542d000303445c0030084450000d000c03950b141e51404070580300c084400ca80c08015034040403843d4040902085d5051209803903502c48006a0058621600e41080c21200711649a1003803000ba9441d4040700091303503000000590000c8603450043c1c10714009850280101c002032040008011401c64246c1c0e4003460f00c015100100c0a2a42c01e12580d65160700410141401d50318070340d00189001e603036071a80d240c1846100d020160f14405020703408000d4403141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 680743039 1250 680741789 680741821
    0x2130c30150f080c09040201031113060807020f0601030b040b071202040b041403010504170a12140a0b060304030507031b0212010605130603260c0706021b01030911090408090a1d100b03 81
    0x89406041c0301d81051034100b0bd4080d4054443c682c0c0314952840d126500034a8011040120070a9400c4030380144049141813949a603c244c0250240036141c5907022704070340c1c240b84103010789203841c804500819400c104500400440e50b01128080c0c40b00d019204040c221071050724002c1c49101240400811707072076080045c000d4080e09041c481e03176041c441e01256046d1013038000c5440d40318200c20204030b030070310b250700c25a00c0d440b41c280c414070308528090b54043d26600c00c6d0200542070155a0401c80e0120724100c0607260800e41c0541201c80600815800a0207403415000b490300c1050081205a01000c483c4106421660030041d15080b8080044180680b289243c40f4603500640820500720344620030003c0400821385a8010305940c100786c00300ea1414500075100c00e04150808035078402264014801d0007100404844008058444d8a0260010701c00d0b40c0d003081d005a00c41c80d0008000c014004003440440104482d404669905004045481350324045c540c14044140007007100c4c03102c0e0380042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 680744289 1250 680743039 680743061
    0x30c060509030604120320040f0e0403020a15060b0f0a0f03110f0f0409052401080618131b0509061c0b04060207020402030a0902130c30150f080c0904020103 69
    0x1040010300c000c035055090700e40811003c100f1f001904010b804680340c0b01d040200107042d040041400c103a40c1c000d40324040c0e90303009803040ea4411525541e05c56140e1101d03004002500e10390381c0d104103002529146401c155084004210803541d8900194028000d480310840c0c0040c9051400030030164480885d040722014645240b020301010502c07511300e106a50280c0700401c21194118103a8505200d1a20000304050400003075009119082d1034440500490300300c00c1088911668800e070381001459144400a40058100e80809043d241c5802281c02610019500c4080301e6540030203000c0719104410481041e58812284c0902054180030659007091103030f48054034280d01a0005800d9030400e0307901c582460343c2c65125004601c5d1806400f240d00580d8042407050404103c4054940c01d80e26074100d0710071001c40e0710540e5880c00b40810f4041040c01c0c0308200000306d281c071032064881d0480d00038410300344900c00c400301d010080001c3d01420700e50010070401140e600c035070045000e40248140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 680745539 1250 680744289 680744291
    0xe090f0c0c100507090e0a0c0e1210090309091401050307031e080f0307091205070302130e0a0f030e03120f0f0f12060a0504020f09060a05040f030c030c0605090306041203 75
    0x145806040c40d43c02414014996580d45841550601d217441075581c00240106402e81e250101c8000e00d00d0f0404d4845245540c101d0303428040320011b01c001814286450a4144c0c42443d00c1e000104141d0407091010a84000c2c584c03c10802d42254801c1030801000c1c041e00d40c0c594400351f002c00000d600500c00200c100b251403404402803101c1c2e91844042e80052005244405012003040000743e408801d0700000c103e100e4600d40e41d00c010391102500c540c4203005c041d010f4410380100940e21100c90704981c694210f007204868214003542070040014860300d2085001a81e0f030025400c040c07500090b54521001d0410b174543c40e0401d41250005107600c40c91409410040c14498080108041e0019000304826814801c0c007600d0180f040280380700940d00100d10540c0b0503c003031091112024244c4061060546005958403074280c001c0e140c501680e409662a808485030110401c1295104032088921441c4032003115a110348050310b103802a101e54540580c06000090081a41c0707010101c1c02d16030300c0c20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 680746789 1250 680745539 680745553
    0x910090f080c01060f090c020127120201020f0d0e060604090c060e0a05060a11010c02160b13050907020a20013c0903050c06040609031506081902010e090f0c0c 70
    0x2400100705c0c0202d90050324000d6852814400a03502809407842e00000300d02020002c001e002c81111104200307503005000030202d81c80c2c00600c18003d60440318840100e0702c10986400841100310090b0040c0c000c0c0d0308180c0212008502c6500b040e0058205855000038040300362800c0c40c0003145c00800c10a6165800b1000d40c1c0005030540b60400240b2501c603036951071035000109024060300b540e1884a95a04560000e4072102e0640302040c040429a4012100c2c3c640d20030500c801d00041240540000e0360018030350050155850700080c0760034119102c4d8469240216805030f940c580c0790305031010140400c0140c0c44400c001c410f4503400c081800384444000c110344112500c0505040111140c0001054000d17205000740030382006645019102141d03490300c2d190400600514821301c902c00200f181c9465050700a20488582106001d81130460445010784132149000109503100c4200368041001c04082a802e070801450451007a02a0b01c4421150740307c0354611620303907201c4e040203809400b0f061 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 680748039 1250 680746789 680746799
    0x120209010c0b130204090f0308180d030b06091008100605040b040501030f0e0109030305011a130e0622140610080103030e0105070209090a061b0804030c0611120910090f080c0106 78
    0x885000181c5020708087c0c06500d03960b01d8003518400d005002d005c0c60f079110660612010304001441780c000080d41c40c0200c2e0003545040440c21718003484100c5a4070006000402c1d10641c1d101003181c0c030035451810940f0130140d5840c0207845c203219901070509500802c220600c059402900145080b031100840040c00c1c100084c0c105086074202901103000a84610042007110300c5e562017125501e120240312454088103404015903400d0510840e00314a000e100041c07030503a603000030b0f00c0c40600743d1101000e40c0d4a42400c0c26000f40b8045004500c1000101e01244c1030b82041800000d8076403c5458010841c0d0031510f041d502d010306111102d04100003000064011303158000c805000b00040002040340200d2890320798256210b4110035500b201d62500d4441d0403030750144a0a4000d074250030250102034007814104042c0c8174160816203a1100012110701800c00b20a000d84260303030b580d05450715016181c2d5103a040d41c0780590080c282040d43d002e12000b0036804070091508100840c00081c9050f40c0d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 680749289 1250 680748039 680748041
    0x5060f210412020c010e0d0201090f03060608240f060406081204170c100503040c03140d140405301f0f050c121005120a0201120209010c0b130204 64
    0x303850080e050503a8051104202030781e50b1161458901e070000d001d042e10204002080d682143d00240d00c01c0d5101d03680e1f4030a59016043e030708003070045d07210004002501c0e41040400780c03900e8400e1210368490725100302d102c1ca120304010580a0041203070b28504c0e0703e0b10b0a00c10b900070310180a83c1c2d80b10395912400285030804000d010f4200f400040c2082d1940d16143e1401f00003207808565084c1c580228071220101e079903c22020850480e2400c00c035441340c5450801d02903401d1150402048001d92505590004100150405031482103a54900100b1003c201003100c500542c42907540200c403100003e00c001c0c01401d442d20101d41000b4841d202c002007100342514094004241c103003422200702e1889803601841c020000c40d510003c105020900b0030b0f5050303103c0c92158284081030841c03181c0c042212106800c1c03844000740002444030302e20340d420700c0807181c5810644034202e01003a06031041d05821040e5000390f500c40c1c40161203d0b405c581c4942c454000f003030170050902c0340e0340c00c0090724a401a078503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 680750539 1250 680749289 680749327
    0x20c0108191b0e0102100516052101140f0a080d1d09072a02090117030d090305030a14010b0a030b1309081c050925030b0a020c0706050406050405060f 66
    0x202c0d9440703020500504002a08000b8440c50034042182440200125038211204000410102d4501580d0382c003500306005807500002d4031494034a08034903000091803c1664281d45111004680c1034202e80011000c112000150b441000c0c0c064101980781044c1c240a9180460003e4225071050f41182c12400000c0200d1403c0b0b07088004a80300761494916080f070390541001503881104440300c41d2506030001840214140702d1111030075002210810301050600550300c480c4260041406400000d2038090442c0c0c00403a14100031600d8180303142a07200f411444181200d4904100914001d03818100314003130f003510310086410041c800c0300790003003c0700c600c504200ea40c0254500fa4454001000201e424010304400c0305d000c0e0300740800d002c500400480c4030f0929180d40e102041c0c0542c0ca00c1034103100e4402e00d5001038a2007803280100404110250000c180782034820041d154540d80342c0d04150340c2c40c0245d014600001c1d006120078401418241d0050007050060303620103042403403100d81106940d030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 680751789 1250 680750539 680750591
    0x2030709150e0c030f01050604060c080708040e0a060302120304030f081b030301060f09050d050c040506030120130905010b1c0209100c0312060b16020f0603090a0b0601020c010819 79
    0x5800005c0080100d054002c0c0c81c00b42c00d04856042c03500389008170050001c034101700040d00031400068034400300103c80e402c4400070040030f15442d40a15091200300001d10540c4016030260100c88014400c280c408411241603c0e400740d9541e0740a112a115a002c60300800105114584591440980040c01300003850091a007030351060f40407244000002c04400070380e8010360040d0707000c5480c2c100180d03003c00e0700100300d00166000112562107a00007030240c405c2203c0403680401c0c40c80542c1340c0c03c403014001d20041c25928800035005940f9284d01c4c0440b00b0912801c0c006802c180900881202180a00c3c04098601400135082011100021381c11651172130030342001c604a8003400003016048600410103698800341005a286000e80003842031180c4050100c0c4041041d240b4001c56031000707076440d000800079056070f07103e1804d990300031380d501c00c852002d0721954007540028107e9840040c04120300001a59107210300e0b01d984400307009480c40190751682e21612040505580081c080c0a035032411703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 680753039 1250 680751789 680751811
    0x1b1809190c06020c030106060f0807022a090105030f0d0c1b12061a09070e0102100903030b120309030a0209150d1511090d1212020f0301150c02030709150e 68
    0x520b00341e4003a1030144403a41c40d078080e0b41040c1e010491641c0200c401000326409060092207596134510403030501031007414030039800b0200010500c900701d41c2401860a01003d0310303110820b0f622102010340e00c41240030246010340c841504441946d11451003038080c00d1140314020f01801d10107010405112094106601c2c0c11912802201440f1017405007441400021101414165501000ca403900100804001c103024003060440d12503482008051000640302030704004c05861071074024090910002030310300c2030105001c051b000d40c0d00801101c00c2d0f80e8004000f0801c5456550034041c121500a002c10385000f06030a2000301c80d102c1c424100c117811b11903400d000c0c084007003040c40d10856586464421040c3e10034000d0078000d0b01c5401545400d5031b04460141480c0c184280b0445020a104031003940950010400d1003601c080140510305882c00840b4502c0f03010201c5034129240142490042e6043d44502e81c10031244190754010301d400c01172090399482d141d0300c0b0141c80e4080d08060b01c0c018158 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 680754289 1250 680753039 680753063
    0x170a08070f080d09060507050915033402010b011404120606090906050702070807030312022b06050103110306060d050a0605060a0e04060b040e010b03070c1e051b180919 74
    0x1c0940b180d250b1007c014100725050040b0000402c011085248520384410800030100b1030300c080900e10000c090340754071b0034182c02841800c0c0812402c8030440384c15026600344803400c141513000341c007060300d00c41090101504152500c03203110f500d402c0c4e01c101074032880c1d6210300100d4910300e81d0007805c0440e8003a1001040606006d0b000900d0080107034045041904504414000a5480031b07003d1900f005031a80540c688085444090001080807030351541e00c604599102c0c0845041d421240895100345c80c02c000c602c02d80e60001015100890700203600c10010011054040c0984d404560068160417001078000d840b03101044031580803031028404034442d15101d4202d403809001e01300150402d401881d04152400c0c8011035041418001d940c680240800068422132043d28080d0070b00f03401548008802d074004035828040c03182180150703064041c121100149150380301c1620001200600b001020100818500c0f406104c060820542070140030503411102e920100c844071f0b1f041c0146851584 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 680755395 1106 680754289 680754293
    0x6090603020d2a031b120c03110418230c07171c050603010e070510020c060f04050a170a020d02061e040f170a08070f080d09 55
    0x144a202c810f00b1503d00e40710160900c0c4070703206460070000e000300c11050745100d180071441c1c0c00c082856051a042e0101c126031083c000b0045503c2d000070a102d81703000c40f070490343c055440700d5042c00d001d9042e52000030092107821102172200c00c2d4a45090030080051100040042c442244030801140c024140180d10b900021032080f01d032600c4c4d540e0804440351013031004110b4400c00000e460100046c005007014072038451902c003c08000c04501d46031904204c40600b000707040d1030440c0100c0d003545901e174440344040e04040034100899604ca40c10102400b032520300d107a010583d409070611410220751030209068400580503030300c0c008030742503c1c000b0030001c2c403840d058684140c038102034941d0301311395940c09402910745041050726001d46ea80720310299104e001e02c4d44007454002c4030020b800144540000e100032031140f2450742001684da11030301d00580126494a400948450541d01 = true := by decide +kernel

theorem cover : BRFrame.Cov 680575539 680755395 := by
  have h0 := BRFrame.cov_init 680575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 680575539 ≤ n) (h2 : n < 680755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
