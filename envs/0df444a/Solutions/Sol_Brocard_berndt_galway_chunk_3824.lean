-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3824
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:46:58.096176+00:00
-- url     : https://prove2.me/submissions/75661274-0a85-4477-8742-5385dbe1a0ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 687589928 ≤ n < 687769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 687591178 1250 687589928 687589957
    0x171003150522020a080a060f0608210703200a0303111c0e0102121603110310050405071202030a0e070503070303140d1503080414040605240c0106060309020114 70
    0x140501505469481c1c0d40b258005032103000b5254449852615200f10110100c65a9a8a6503920846086841050301406d00f402c00352103100e000485d000d41c01c084901c00c68a00c0d1800091400405005aa1034040c2415084c917030ac03500e00003007200d80d450386103005054000c6810b1201a034941021001100c000707548030400f103030001220301c0a40c1c000f44100c0c0c0407444959800c1103000c6040105800c1c051040010a005654204400d000202900c00c0700480001d07c030014018880e80c801c0300840001507030410340b00040c00703540d19401200c540312814402030740d203417000050125802d00d80e0403010391b001c0014101ea1b0050358407024195034902910024001031102440481e4078584d80009000d2000012070100303030400c0317984000008021650084600c1400080d040041115885418501e948121020050580360002054081000b809031003100e9494000b068800f80b520000c1e01e6815904c032000704110b40d210ba101900420760504140d000c078844408140940d01b00008803081a1f45c201c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 687592428 1250 687591178 687591211
    0x31e1b0604270906021309090201090b0702271501050f03160c080a05030109060918060513080403060c1e1d0d080c0127211710031505 59
    0x600b480b501080d5181d240105481c1030315901454000d40181c90f000c0c01006a03103a410080003442800346503c140c8140e403c005030500581e03040001c510489000d0401a42e442220f0300c00200010300d490041031001400301d075484941d10a82810511a9018841150810542d07000560307440c007070801d0101205000f04006040701ea1503003020101d2070348604103100210203942e2008001d40015405800152020004114108c02402498010107100e40108802005104e850308640c4200c000600060b44a03c003203000301400c400030110040d0040700c000d4440f030712803900201400002d103071040000e8041c0c000c000d80307218140301110451816200c40c035010210b00c0500300710203442010145c1c0b100302000703c80040b0b04014014241000030030000503460b1b414908044d03040c2c2c13a000301244007030510642c1c0000107100c040204c91036183c102049030102e5103d038048071600c64000151984640030700902041c114880503000581e4444c0c1d448001010408130320324211001120101d2840c2107481 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 687593678 1250 687592428 687592439
    0x903070206090f030a02060c010e010c09031a041b0803040305120a020304060e030312040503090a0f0b040311060c0106060f080a090b0f0403124101061b02031e1b0604 73
    0x5000341c550f00090180d64a0442c036400051503500800429200c594507420700c041100420311640320780905038242a514282544c503481c250301030b412011021002c83d03401140912014000d0180b080d4800807214413000c1e1034440403a201e40003403104035114443c20740ca00b02c007910070340305450600b086075008500302450080c0450700520584800d0f609400704101d0f040070a468004628402d5010354002c40d942c824040038400c8454031030703000700e00518a060741030007440e03c100100c03011a600094038040006085000030031900c1240c80e070401540c41d100d00083c2c82030300f041590b00c03d06216202d1084650b0b400403140156401024028082a0013074001071200640414084c1c000e400b0303240140c90201c201c0090001c880303034118010321000c1c034401d042a500d610440b1440007030200f041401c1031041140c194112401042c0966410301c6a140300f400020581000005600c61700103048640701e0468022500320610b490103242c03158002e5030400d00305801500005598400054681441c143c07924 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 687594928 1250 687593678 687593689
    0xe0f0706110127170d0b030d02070806070f0207150f020d081306020315091f06050c071202130915050f04020a06030e0118080a0801061d0607062304050105090307020609 74
    0x10841e04c00391100d50b0601c0c04000700010304188025030f180000c61584440425140c5103078580680304661003010184001c03040410465040180c40c00e044040e02d8103030006030b0400345180c01c8807014200c1010340348071007035107c1c203c0000e00300d0a800360340f031515403003c0851764400c1c1200d036550f0030905140f034100010b4443d40110340c86224001c145498401110000c0c904100c01d43d445104d00038240e50121030544401c1e0a0130050201e41803c600d003005501c0c1c00d60304d03244148a00700310103c000c030400040d0f40350748002c0b00250070400000c110760045458281400007454404901003480c100c0001c0e030780d100b80c40c099806540c00800c001c04140c501001240641285004081035540350301030300c1e941099546003204030a202c0c80d007140c3c075100d0401e401001300b41c05902080c00c0100700d40703402100c07501d03603805032014903170a45c0c2d50307565802c1901b042d0010f0f180c000e85c0c0e06985109070601c408852000200a070207648920024030454503440d0290350f5901542070060b600c10010003c140085c0b03000f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 687596178 1250 687594928 687595001
    0x150c07060c050304350310090c020c1c05070b0415091401082413051821030705040312020a02240901030e15090a0c050d0807060c030e0f07061101 64
    0x1440c05c0800c0c10000000c2c10143e420585411400d6011424280504030607401808900f03612880101007041000000601c00f07090041203d21408081c0e03081c1c020f002d0180501c1c000f401c40c1314040c3d41c0d2660707110f1a420a03003107d181c00b00c0018031002000314041c1c0c00350321406240d4130140e548a9050302d5451a07560202e0222780350000308140d4006400180e240d202e1a51244038443d940040d05142c8080d00542066050540d0203041d042908004440309900b184c20f400c9030202c0400301d80303a54501c003041d6041c1c4501e0b0005490750240280300840190b00081081c101c0d40300756225040c55141580c05070104d403820384070300400801444188829442a8070040d580d064020440d01a40c80d10049800e0800050742c400c4400d4210410300d1050004810840c8004c04d000c0d1921a10001d140c2c030380500c0d03802081c40091686440d0310409403014825000300449221000588030151008442959104507500c60080480c62050041c83c1900c0d040c401c03405640d14038030722600d2440d10b1826503044400c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 687597428 1250 687596178 687596243
    0x219110d020c0d031b14010e0606270c1c230103081e1c0b01080f01050105040504020d1524020f100c091203080103021318080a02150c07060c050304 65
    0x140702417000400e46911044000c0303d04503000088407a15015454101400200f5650040d5614a2140106081104101201d680d440400d54494441c4003200001d4400c000e108a0394550241040c44013260035400382521205d2000a003146560b5a03000c88c450500910000e014100d09200100f031707200c200625401000c901a03c3c0b40e2402101030b0314200c0a5100c149a401c1003582e0300130b282081d580000003a80c00c241c2c280310a901035031400740002d145205070f000b08e0307018a0300840c89120030b00f01da400022045a038480c0081d070aa4841c8030304031000d40420405c10b40a618410a10184e0b0700105420400d500c000010b042e9000110460001500c9528880700c20001090400600000ca1003402c4103c24801d5484070300c154590300402040e50001c815001c801841c0403509111005072954922003154400181602c405098006130f0810b1a000746481d00b51000c0d1007003002c042082c100400da5148103c3c000c00030300b059080119035500003120b00a202501401401107c5003002444070741107403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 687598678 1250 687597428 687597467
    0x20904051f151709060a0608120a0309020a08010513050c010504120b06061314030c0603010b120a1803180603090b040b090111070303020a030605010e0a0e09010219110d020c0d03 78
    0xf070016500806050742100c00c4107603604100c0911420610a009031401400c5040c002c0c43c1c0343d60740f0302807081d10344aa13100070800c0c903503199140c41c00c41d203c111506005080c2d0000811a03440c0500500c035040c80200710480d181d011fa006c03007403074a600810595058980c4070f03010820740805640c0d500d01c5260042c2c81541c1c0013100340321a01c0303200c034500300d200080d1000c10560b1040c560f0b1142494500003400540920030b0000b403005014a080900c25034800392041024070b00d05441d200d40d00b90040240e0b5240004411954140006064100300303241003031042c00142c0c4695903a5480c044003110520803000703207111407160214000c5413070300010300e8009503000c3c0000303964541005400c03146c2d84141c0d012408240c002c41d00c014080d40520907100144000e08107550800c00031000200b1820490240c40101c007407441c04210350003000d505807681b40c1200488075040220340c080c00f50115081c01190030942c8a0340c4c0482584c02d03c0460101081c1d01c014181c83c050302c0780c1d43e030140c42c440c48044d554942d05 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 687599928 1250 687598678 687598697
    0xc040b0d1104030c0e06090415020d0f05011d0f01120305300603060a0c0203030c0f090d0c15020a03050322170309011a030a0f080d060801020904051f15 67
    0x20004000b4401144264882080c4038645500419800e41c000c0c074a0b4828242c42c003c00c0003081061030700044000140c8001aa00c9a40401020040220200360806c3e1403a140001c10001c1e030144101c00103000c010040020741e51a908441503913a024059600594024129000082e000c2d0b800707040d0703d814130b078214400ca1413030b00f444600e01602c54981c00c103480131031424440c0038141800b1598101c000e842040c000c003030081502a55a101c0a03003081c544500002d168130000c0c0a00d03003070390b42000004003180401107450800b006096828003c19640d120701000c26500280009103804240b5450384940e410f41d03941103003800e2800381610028010b9029142068006402c3c3c0c905110403130f000110003516401c10386089402c640e14400c0740e02c02607111030707403010007942c00048004400390700c03140f000c48035040d80c58190028090640c88000d294244103010030341d15410b4000e0040f401c0150b804201c5a51480d011076461161207506051001940b40e0600c9603110031581c045100469040c5071402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 687601178 1250 687599928 687599951
    0x9091008010f05160c030e3f0c03030a0801090908040305010c03092901090c05090909030712080f0f060f10081006050a0807050913020a0509090a050c040b0d 69
    0x356035074642440881980c40007082041001502d00f4264083d036880c10010070016550042c003100b0301c202040d4414400300844c600307010055440940c50b690b4038100f4558282350a00c0c9526984103100b807146007801516106142818000b064070780314081c0359074000d4164a084c10141c0240a038100131b07548844104004800300354240601a41c1c0c202039038000078040301a04040b900c8410701843c400d000ca1007840398082e644440c40842c0e0542c0c902501c0010035106407a01903600e44108400f060b00420081e04010300342d013010018205141c0205034141e8000b4030781200300c907403680803179040c0102900d6402050810707030500c4003580e2004020708903000d8581c84074009141041480220000550103030100401d41c2c03c80d6030284000c0c03603d810300d2410320280603000340101074002c01c1c0c0000c1003404189985603507181600305100750000b010440d40c2c0c00202c0300003000b80d4499036005001e60440702c0401c50111007449028441c41549140a081c02c0c101140341500b0b0b030000f1441d01049443e1200f5092 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 687602428 1250 687601178 687601181
    0x20106030c1d1602120c0106050a0f0f09051012050a0b1320090601300f050741040806062407140a0c0b180a0b0909100801 54
    0x50890601c4901146600c408207100541c0020040c0303d0340c0b081d0740902000b41d40c00103151984d190107200c0c5c1c0c0b074548180040703a44c0100880d0380304a5000c1101c1c1d07400a031f0090b4650141c010b0345c604500200e6010f0700d500503801a01c9080c1c2d00a80c00c02e2406c01c0800c040b0100040c2004417500c81c900740c0f11408019196041d02002c25a1104410204180103100304100c1c40c1e2020346030328405180c10300b285800382c0010445200142258140320141003140e500b00384d0b0700075503519800c02c0b14113100300c035071480792182c0100000360703080d0b000034038040108225501a00510305180c60004e46030103c00c42c8100c0b500c41414154501d00b895030107000100d40c100d1290300c05030010308610750090200c1c1c900401040b614452035139103c150310800d40003110402d4002021680307a1074000708985981082005000d24003808944050201b100c00c10012070b225a00900800f1402d13000114821502d50400030032039141820300c10115101d00070090b05000e420181c4540d98454070440c110680300c0d5443c1314090 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 687603678 1250 687602428 687602453
    0xe04020705010c0e1207030c030b040c09020409050a0501090515040e070b180a06050720010c05010c020a06061a0d05060109030213060305010c03020711040e010b03150411010c120f02010603 83
    0xc02080c4110b2004c41c1e58240f810403002c806840d00000c0009034699110003d00d03e460740006010b0720b005d080000c040c480e407801c85000420646c0c3c03045541c0e42d07440140030001c00d0143c9400c003880b0308110001560003024011540034003004030708840144100410000145030000c1d184201c0e000380784001501001d0354021744100132a41c10b08004607101d080822000070304503040354040c01800e009004c00f00702c803c05110120600d690b030708002c1c50710a40043c5c607080d801a100a040e582098100c4c0809540814160460b0b4894402484015298030a128400901141c00414180240500b9844026540105402420604002e042e0320740f40d4000c192801c00ca24a40d0310b80d5515010100200442446208004145031508509142c100d54038503501002c41010548929204c40505035070440c20350044c240c9881c028100ca42c0f401e80c0c400c032010102d404440648580070010024041940030b01d25411038280c1c0300300000700000e6111402c1c0c0e4280664250035045658601002c4001001ca10411 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 687604928 1250 687603678 687603701
    0x10315030308040203120a02030403081c09260a0c3207030318060507060f1116020112020a020712210905092809060b0406090606020f07080d0e0402070501 68
    0x48600f45818010f051804150301440d02c1300400810080102c1c1d0390110666083c1c0340d0128a841d44c940c0c1424880329951941442d007140107141801480c03c0040c0c0c4240042e0480b1003a0f02c165641a1011500e056809401c1c118008101001c0c028000079110310583c0180313000070751840c0c003815015400805200c010690186950740124030910038035801003a80100c60303034054402202c2504001000780b0501503c0c0000303212940306c1e401d9810144480d000b4940d440e0303100188c141c50781c030030400840b0008000402a1b000c40da0308550302c800d002c194000c841d0141c10640007442d510b894000d000d11032216151080e1861140000080c080c454907c030701d441012a15a582030301a4200420070000520182207402100c00710881c2d05262008442c110462100c1000009100c00076400c154002c0d1014401c01039129103020002b046036180ba5201c40c060f10815422600c0c0c0010301c0e00300c0ca64414950144401545c00801c2200c01e691050f0700b08204210007070000360914a182c1e5415007590f9120207003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 687606178 1250 687604928 687604937
    0x31209061b0e1e0607150f0f0b040e120313210207090c020a05060f0a06081c030b0a0e0c03040201120203070c1502041d0a0207200a1406180103150303 66
    0x2040403070326051103040c111070780085601c3c4022441c42c00250300c030311601c04003c0c03020017225125841e0701810f51020b0302c25801c800003405051f100d642d4040003032241c210946d00c00e502e0602032070200200007608000e000c18006820746140c88a03a0200803c0c5581801150102259200300c000c0402c0030006442810f5140c0081021034100700040c1d0540300c001c0200d8046501c1444940e0215500090058000c5040c0319000000e40702e1994800c05456075400ca801c0364400e15014000f8905010890003c2082c00e039000c00410481404014809800b845002c600e5502400840e403c105400000d64000703105050032403241d207200881a081e600112403200214410000110070f011150724211400c4034803540861a00d802d03d00740002c1050081c00e08901c90b1100390000f10b4074621541110000c540040d2004420200c0744001c840c0002c51a4005025013004000003c4135500e0b807120320030040300107000d80d0900303403080342140c0d44a00d03028900d8100358455404980000345034031044042d5001e0f684 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 687607428 1250 687606178 687606197
    0x9100605012a12170a0b130c030e03040803040e090c011d060904090b060306070e100305040512120106020d030b0603071b170a320318030d020c0c010c031209061b 71
    0x440080c0c1d4000400b417160b054207210848001b40c1c0c401c1a14030850380c600000090302d01c0c040400700c00500c000d89070505144070001d03011401c040c0c000094001c860010029610641c1c4154840f9110580c915a5a01007040c4880c45101c5040210a03041200d40250000d424031001e040000c0559980640507030340340d0314038024000e0500f000e1060940c0300700642800551031100c100440d416400d40034030441095a6034000c1000c00106101801e0160502c40303059840310140800c2690a000c01e01ca0310b4050710991507034428160281c0194164003800078100303800c40d665510240c450050005450382030380c401d01d0134800015500495020451075036609182c450302e040f10060050751402d101004a1070003a8510320600d01c400151550504204030080c0c0c80742c440740c0080d0061400401041d146000210307020001c16101c0d40542512480f600c121404c080040c1c00540390302e64400c40150000b21b49807000708102203260401c5284501c201d20029220440d200702580c038168802440b40011141d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 687608678 1250 687607428 687607457
    0xa02160303142406090103140a1d0c1003020306041d06070e0108010f15020a120c0b0c07031418040e011521030f0e0d0b09100605012a12 60
    0x30121540280050b00310f681c2d5104160001e00180f10040d1000e200d040001130000c032a911a800030400c04400b60404081f42c141a0220340107000600c60048c0d040891460010320450001b40e24000c803200901001802c0c00c44803011401307944020000e98000e40c172840b04843c042d0342084504a0341d070000c3c3c054801801e0100b0b00604180504013458100505040103104641d10803641c40c08503038407203020400103c0881d80903030400034200c2010f4086140c4010388980300e6000450301c5001c5100381c031904c0450b643e69902510501440304080c000822500c180e040040d8850000c2040845105d0124010003405001405075801720442c42c0580c0d444003511368840c85281c02c0800a00820700001e00b07404071003098500f440e42d6800380034003000030401c00c100205006000d5407142d0800503110b00c1c9140d0032420802c5500b107041d40c210410344a50300d480f2080c1c00d124412a82903500c160f4503050050f041c4104105d40442c022151100207000c2201d140002e0900e0040d10b440707031210707100d0400b20400017 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 687609928 1250 687608678 687608711
    0x30c0709061712030406090b041a060409050c090603031b1c03060b03130807020402030c03040312060f14040e030a11070501050412151103011706060a0501090303080a02160303 77
    0x2c0d071250100b9000c450060400260100385949030301890106161680e656040c03101c06801c0e80900a449002008140001e20174060039164071580c07181203440d819224001800215101e9140c042e0468204038890032040ca003201c1140d80220000782100e0924240340c041c45980c0e0130781d28155501d41e01507842065079081e68192a02141c10a00b820001580340054601075844001e01a40b850703940d91740c1490030005400140e86003650003400454480ca030035208011983d10a55055001c41d103640c0710001560824000c0605070b54000d8240300f41d46241850400b1100340310310b2074950003611129070318030100d4100081c04840d03005030b94100707240c4c3d00c00030001d092941e160006410040c2c01c000078415071020102c505416035000072501c0301403044400e614000c0c5081070100441e2035000000181c03400b1500050508968030307509840c403648942040110385c40d200e106d158041441c3c41010400301e0300602c0c0c000c0d070111400002510700841c640800b01c90200c4a84100d000c00d990350701800c4000c200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 687611178 1250 687609928 687609941
    0x1602060609040203151009020403060b03160f09020c0f010f1401080a080405060a051c05100e0609070f02190b0115050a090b0c0705041109030c0d1a1503030c0709 71
    0x1501d044030307581002c0d0042601d418031420b40040044074500844c400301c0852941c03400500c504841152143d03124508a00508a082c26843c400c0c455a1072010741d01e1003211800c002c54404c18900c41c10149041700d540081d40150b11010445d00a410081e10000c4080c0038802c1ca00ca003003540091300d00d004d910140c94524041e0000ea90a0784021002c00c00280002c00704c405440b01181c40350345074908102c0c115407900c182e00074210040c1060764000e40900c1386070051800b138003400164603503154a4884882d081c038804c49200394441a02d402054807117008004c9009528418816206001055007000514100c0550112940b50842004006101d00e910110007110358a05d409032401030760340c0d0010106520340c060142d00310310000707078aa50001e080141600500c4090001e03c541440c5114414480d001906a80d0082c0030b607411031b080b540b07041681030551a0740840740c091494141901c02084040c01031188a04180d50042c210480c2e03030404c0035004940c00040104480c0c0e0030440400e0a4419 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 687612428 1250 687611178 687611191
    0xc09100303020d02190308130f110a0b0a020c1c0506040b010801050705030105010c11040f06081c090f0e0a0b0406150e0312040603091110050c010605061c0b1305160206 74
    0x5800000481041030208201d825011311f404401c170348402c8100d280001c0c4150300100781084401900d820800e50078042411024102c1d210000507540c0c00b003c4010744244540180103030840d21582c81f8518052402c0c0c1200b14075a035205044441c01d80d2014a0f014054509035040003900700100402b40c02401074a5109030180b80890840d454080081d210300c0c0c4401d0001e040010141c0b10014075211a80718440c2e113000c3c207109002513030340c50021740c0d02c901800d031050407000d405105466203503004401d0241191440141c0607074040c6800b090110745000540440c01070380d104d622110030360ba01d500900c00035016243d0f8041c40b42c2c000c608050484188110200d00035001400c02883d11085038003942c080301c0b0103040c0030550500c0ba242002d14500300e140b0965201025140c0c0110b299445005441120300c400700030000e2039100c400f004150b01414059205060841c1201c43e03040314036800016111501a124031007d80300c8515070301c142c4004890503240b0380d81451401601c17980c10030400e5081071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 687613678 1250 687612428 687612433
    0x50f060a0f0908030a0902010e131a030105010b0316093f21050405030a0c05120601050a060f0201020c010501090e0d0306030b040605100e09010531140c09100303020d02 74
    0x35950310a50300f1301000340000880d550362413844040d64010403182c41c00c04401401e031880c10700001e951400900369000480d040c0e035143c034070703142080c00c051003244c2c1620039248845041d50303100350450300c00c2c1229442c3c000800c2408034000880001c2000c0703090058000e89601d8420150842c280600e600e606050f5401440400c10310710003140d1840e96060440307104c181c1c070300d907170b88a03090080e0360718400c5500594143c810720f0385101c140f00c1003182400540303d044a004007040b0b84800c04907035540c028000c03260310424604040190a0041c64125404141400007600b003518030040a400c60702c0980c0b20111258440c20000c0444105002c822030034001c50408100660442d2110020800001c10051049039942c01240c40801c203510550010900030042a00d680b91900101d40030707100035a41c1980316041041511f4209196001c08031807080001101c1b220840c46442e5015000181000c8180314000e8a0031a00d99884540308030780300d548070000307039100b0501d9460000e1810640d0f5080c4000c54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 687614928 1250 687613678 687613691
    0x807030e0a030e06031305060c0702090603160608061f0e040f1404080309070f0306020a02150601080f04150c020102091003050403050d0b01050f030403021515010c140a050f060a0f 79
    0x94000b41a05100f40c0181d41c1d10781ca0741e80384401c000d18860200e10281c44c2c3d126440420844180900040580314401d48091800f41c5900003416517845024203100d455000300e007814894a841040c00030740c8080010500b45001e44625080c0481c40041460303c8000b1710703400a0b00aa60070580200c0100c258501d00420546034640d03d030007040f482c081c000801140000005c0741c0c610104000300005488003000c11038202e5074a140400c000e6100e1400302d40540078002c00040e1a01080d0a0144500b9040e1940005541c8401034540c042c1e01c0200102d40c2060030001e032074035800b42449104440029a0001607440805004020a00a0060082040604010070040000d5001d805c0d59000100c050700070a0440b518001610a8041d2401c6c10a03c101e010041009045d0f00080700340791400c481e4030701d500035154003196010041c003440255001c102104031080008464902c00c03403120700b0a0061b00ca030b411081d03071080d050050103000c0f0281580a081444039160a91082407004921034400b0841c2c0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 687616178 1250 687614928 687614933
    0x60903080f101710020f120a020a091e151107080c010e01050d0902130501090b0409120f021f02040305070b030103021c030315030c0f050f09060409020d0f030807030e0a 74
    0x40051401070554143c682202080311000070881084500d4000c00e05546400c030f0030b9030030401c0b41c100c1c103200c10448000e0130106407803140f00e108940b8401c250381d42e8644a05e00304200380e4062120850100010b800107080010b200c0c010b000e4070100c0d200a42c1c0c0e046a2030004440440c41c003280f80d000b1070b10b640c01c4443e0080e056030b04101480ea04200a0824a84031440400301000800c040c0401940002204d100c141f05000740b41d0085050702c88800041229142c00414081290b007600c0008001d082e200d14404621400740c030220242800c10300c100c900d00c280c5107012100303190401038a807030010740214040c01001418848074024001d4031000038215851600042c450691001810802d14000701072001414801e81000204490200d14000119039030301d081d866900d003e1052092141d940e036000b013882e203059110b450342d44030000c014002c2d90711003204000c010000c43c003040740d000780b0340c1000d1000180c2103c4018030860080e01d90501034039219038058142d0780b44e00142c004c00e81003403107190700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 687617428 1250 687616178 687616201
    0x20d08011419090501060804020406080f06010b0f0c013209120d0f022106100e1003020c0f0105010609060903050d11071d1605040b0301030f060b0607060903080f 71
    0x36401d404880b45001c074076542219114540c00e03074124a1416040100210b24a900242ca250142c1c2c408d4804010440c5d40f54901503d600c01040c000c0c03c04d4000800411090a210f0040d001003819010090b1800001c080305130300b111000e0202405007400d0304e200b42c2d246041124203011005000c50b07801101e260405c91562104140103c43e04140300102e09a2603003862513100601440a406045655680303007034658901420040c4480d40800b071650005280d400d11008200e2027070f00ca6100c120708007100c5000c00c12000f501004420402d82d081c8107040c100d610411010307018540d01c1000180c5035042020080c8500c00031b410040a202c04d100341000011000a4000f2030f003a968500494010b0f03546c0316250a03e009944080c1d0000c03500c4a018a020b94810b14650148910000400c4e0070b4010702c005643c0c1e8000e521581102020510040010480c1200d401940510810000031100c1c040340008000c0d070480c0c8030503030f0fa4581d50600c8008140e0040501c50300045150041112031408400c1100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 687618678 1250 687617428 687617459
    0x102070803130302031e09121603030c0203160303051b010204120b060a05100f0e03070501020a120c08070b331e120c0306010f03050601091a030607020d020d0801 71
    0x4041016520801c24076100784107460160600c0002c611b02032003281c443c609203400c102c481030312851a04001c8260039100056010082d0036404400040f11301d10344003038802c011000c2003660503010758001c10059101807503441000d18880c0d162661600d011680340501d1904052004407141e10401c018480554030310050082c940e401010031180e0740c3c0c1d900210300c0c40c1410f68002c030b0300203140c01400700040350444920a0030b400280c0d541c58090001d0001c01d503a0f03440d28414140035170031514a500100d104058945246002410100c403803d850344e841c41403d6100c0c6034143d801e601c241080c0040d001d0742e108030020b0100140e00c0461008102d80049403840211000039104a803009014024404c0031007619040c040028441e80e29100d403008001d032100e1a6a80191081c01800c2c000305d8044265111041980d80007001054a83e0038003c03000002c19480c0045480c464500310550003c8d6410001244564000e501601c1c08054194000e46422030701030300c640900070086c00600c02c4c0c1030001e1000c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 687619928 1250 687618678 687618691
    0x90f0605060d0210020c040b0109050901150504080d0c0b0c121518100e06031f0b120a11010207060309080712180602010509070609142223090102070803 67
    0x11103072078000024500303019102009400039506165140201d8000c01d50703010440099406000c41d8070808011162000321340149507000180720018070a40d0300140c5628250006406c003945000c0e101e0251500c2d0480c0c204000000600c0c00702c9900811000068590304011031804007402c018020160404815000f400302c804444610307074560840c0e86d12072414441241ea002018007a0501c11544d01030a1002d00980310300d04468004146070707080c00661828480340c52010040c22003404284000580610300080e948812107130450316079511f0030b00105400c580700d2900030303480544102c006402c102142c0d2020007410f00c0c008050000c90640400c54040c10f5100c1c07102404505610000e680b50104c07600660b10300ea00088000c03030401d80550005005480c071408483c1001ea454100f110362184c5400340381911107014410115900b0711034290004028140d1091000441c04202c076022600010840035119003e2003142c280c0700c079071454442d008036048000391f24004c40f03511404058407025007007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 687621178 1250 687619928 687619931
    0x40c08220804090c030b030f0d170702070e0a0f0e01110906070812010e071d10030e070905090c0a0504020f09060310050915010e040504030e0f0102030f030f041401090f06 75
    0x103401000302050482e00074045905080010301c2161030020001c0c01072540341ca01130f10424603401c103280c9001030780003e007032050350706d070b85a0f11030280700010360410180210003544190003010505d8241030030f000f032180e039846200050b2500034020010503210100780d08145039140010100340300002d234045880b009410744055566031002d00c0c080f5201d00c100c0111401c0010a40000300f5142000c0041c40c0c0508101da940d28007003450b10354103206d03010b940d840c2c40b40d00c200200081c4180d0340c000d401400b5004040d00503035402c240d40315100380a03240220751114640d0402082c801592414515581c05484251401c5041c5041d180200005105611045124180c00300026144a0324401c07440c0103040098404445030612006c6840c14106201426020880201040e40682030920031544143c1d015550f04000e03012a500f440b2801c805a03003118110b00080004900a124000c001c60040400b941c201110349042d043c9040318500c005104007560341001c0d401404101074007a000c510507000f600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 687622428 1250 687621178 687621241
    0x6010e090601051e0a0c03110c180a0f0f0c020f03120f060d050703060b1e1008130c0807050f0303040e0708070c1217010f03030507171314040c08 64
    0x38030140341da200180b10f602004001120207216900201b4a05100d00c6611002c40503954050f0aa4503001c04d0681c00307030440840115006078410071205281c10040b081d1000a504a0b04c487c12826640112400580c01c2e03120003030340f40041d60402c4580b212521400155003400303000c2e80c00d550407041c0035014404c2e0826240c042191651824110a51240c0c403004075a41c0556a26008018100c130a0031144200c0e00a138541007460418013180250840c0202403064804148406880c500806803401d050100b11000780c0b4000f4850400c00400b03060940001c0a80328a01800c000e400035100b58000d0098105000400a21801c007000c3e40e0410146d0070b02c3c0741e01c1d0745c810500b1640042c0e10038018051100c1c54449c46030740740d0411241c84030421f5140c40d41c40d6507a2a065006940340240c0700040008a00b04850004584440c1c1d140c2d01404c042c00381c00346003510111812070f9020158100d03d9564040c581605c20900d0248100c0f08108203505118540d0304c0c0c54651810b08540c130701c10091185c1000794 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 687623678 1250 687622428 687622447
    0xb0a05120a0f0212190308151003050709091112090109080a030c231e09060403060f06080610080d0c030804031209051002090a08010b0307050618040f0e0606010e09060105 75
    0x4074803413044819801180c80d00700409550701201007130a601038000c6410080402c1020200042a40e440da00140c202c4850ba402d40204400404004100c0300070080100d0012442c06054018840d040d8400454540c0b50310401c0344510000b000a00a03008980c949048403002901c1c07402683c5041c3c050b8100028050008001541c80100456042c1c6102c9001c4000400c0149000d012340051b4506c4900c14501d192000500801c5100d603494030781c1c0c021014001000001c00c2c6030806040d03048190400305a0680c0da00403a07280c900150b4880c44481c00c03404007441090820084441e11f43c100707142c042c00843d04c5482c003400308407010380050100480000c1100031010603400c140a9194400202c0d21400b80c0d6145d2000250415119282f00d1005d1480000741d5000502078070010000040250194601d064208400c1c1d40c0b042c07040520001001c0441081030b5910b12920b0940140500302049001800c9242c0c3d00f0f200e40141554180300d484200342a668841d0360103164090401e00b0960307030307818802 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 687624928 1250 687623678 687623689
    0xf090903041e0e0f04051f0b04060303020601080610150c0f05150718140f0d060207110f0907080a050907090e0f06010b0a0816210b0a05120a0f02 64
    0x54200307810805015048207807035100114610121072548401d0300340ca8480302c03004c0903a824150750150042c1d00074210b0700d43d90303858078000d54000019448001442c07100a004102601e220390710541c050b82050300100310303080090004139803215042c2000500c541c200b40c06210b03403002c00246082000940c003540010483c100340040302441e040400c98041d0112008030b0b003607080d0125518000030300d000210b665000305074060003060b030303420415208001c3c103403406000c4806400b104166100888030ba85030041201072005142c21401410340381501c1c0416024025104c40d1807652a000f090000204580140d005140607000920504040b8003502d84003502481c15866130024840139103004110945140e001540041020b80b60060b2862031f07980ea80814039500070660071301c004c41c0c2e0100000c1c480340d0b220343e02d90144d03012500302030080d039404464500c000c64904284200d1140d0707a48240320280b07403000d00c4100411040b83d400558800c90041aa01c681203441d0040492001114980446d03a81 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 687626178 1250 687624928 687624937
    0xc030c141210020724090201030b0d0302070e2a0a0306120f03120e0706030504050d0c0c0e0c0d0c030e100509030a080a0207080703170105150318070e010807030c050406050f090903 79
    0x1140705c61580485000400030041940d07090490109280c40081440307401e281c00482601501500030b443e08601e04102c0385440d41c40100700f03610b0015646441441040c1a00c17000070541e01504c842c42d01d50300c1540c0c020381140e4464014480303109840c00e25034001100340040b07030500e691620346124802e400640c448003901c1038480c0a0098010810085007050b41907111521550050048a040d420942d80c2511000b468503400f0b804410503040a0049107000700c52550800f81d000c2100c2d1400c40300984410440320075892860009445140c400c0c40c0520400c00440080c1e0015002c005606040702006d50b00d204a40c2c448007400450310001c1d80b90800c99054880503a000032842c1e07500c180f14a1b005103050061142c00304421005000407545041c440c4e803001c03041100385601807540d00c03401001807807001d500041e0b585600c14003c0c08074040c1600d6446600034401c1c072008000090551901184440c05904814000c501d4944100b00307030b90b0b40a6110002100035070b164580c42d12141e0301c15086215 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 687627428 1250 687626178 687626213
    0x3150d06061512110a2102040909050d0f1b0204110304030e0109090b09010905060d32030c060c070503071e11030d08060f0d0c030c1412100207 63
    0x1030810000b55444040503003086440300c540d60004018070b00750390801141c0b00c07000681e10440082c000882500e005138610f1881011768a61541c03032a5803841c4660590f030041d0003a020a9444000000412000304000c801c040aa1b041808503100e01a20003419600400d00ca1000803041c8400d6109540b100e5000d002041007810400355240380c6820040c14001086101c80e00068009400046060391449142c1e4107500041001429910701001ca202400028016980c403681c004061070005220607203584003218840b222060401c030f0480c100031401d941030741448098108020111110310b001c0389541e406840c0230191070f120070080c00d2145ca10300444100a242100340c0c150200516400060f0080035449440209500c1c5000b074145500c960254034400041052803021464615061040d2155444003901c00921410300381c961903e01030300b9910a44001e1442001407003140c000781c000e042d030306105440d284100410003907410340d98114229101c0348291f01003052020850a100519210718 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 687628678 1250 687627428 687627431
    0x103090b150604170f06090a080403020907030b100903050c0a080c30070503010606030207122003070803090607090608040f1b0602010e071401200f0102030c03010303020c060f03150d06 81
    0x1020b810303542d45c0c1c600541100024a12968001558441c0c0004505401c0b41e4000c51282c00c1514690070310810001c013034070b48401d16880d03420154003a102c00000200000181d550032207003a2460070100d0804814100a0307000704491401401603880021328210042010398018086220f07401400c030891018050b2549a00d4050f02c00c0010ba08001440c4415164102d00030020a40d0b250415000c9114840c4000e00b10703844902c041000078010551003007081100d4041018600d0042ca82d0b50131544248803c45421101005100e0700340420803803554000c085040826840b41440720160408100810050004a8414006040154080040c0da800390224600d040385521401302a01800001101041d5407299440c00158086090442600100180c40340100040f0346003d0031030003480910130a51038482e01ea200b05511074240300551244811180c5c241d20795056250081c2068007890f01184100018051214aa0301305001c4035040722281503c1c0d040650f204e0049144090300800250806 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 687629928 1250 687628678 687628709
    0x101802070501060609180603110d110a0602011d0724030b041505011706060904090f0f08040305060901090308160c0c03052805030d020c0703080c0c0f0103090b150604 73
    0x1a000b80b018020b80713506c800b10040060160804008413601d510003c0c22100150b0055109418078107280c85400f0301826181c00480c4d05000400c04404040c2e02c03100c0140c0d034450510480170a41180c8103007003000c940181c0012071034a600d01e00c0703200030065881d00700100003a860381403a020740d1003001c8070000940300340315190140d40c0c0c0c54aa04094401d9901013080c1e1540982c1006603110818802c000040240b401c0c081c124040c4002402807600454500001d68a800701203410360b000e2040084c4102502942c840c150310f0102d0400030080d01004540e0b040c8109280043d030000c0c191079100c3c008052aa0140d1881c4404543d41d40e0b44e4100a465104044804020b0180c0840d110400084140d070781300b007440801c0d01400035125a03150190407500180070f03070381c0302d0304050f0000e01060110900303d0344600e0b140d8840c48110380c0101843d80c0c00d036000200c4a0010300b8101140c40107411f0900f010491841030f41c0342c4d07c441d075400600c0040c10750100f0642254903907402c0c0c103840c040d003235410078003212 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 687631178 1250 687629928 687629939
    0x406031e051e091c0f12060806070908030304050a0f081b0a0302010608071d0a0b12010209040606210b0103110d0b1203130b16140a0b060910180207050106 68
    0x800700b1441c15620030342c00900061841c0000141c0f0507107407980d034046a25003101210048400d150342c44008000c0100c5070200d2030745c2e8001e5001d070701c3c05407660101800c0076003003121018000c01c803e644400d406400c00e0040001080d40400c10000454000d031603100c4075005450514224440d0407590101c00c0404010007c904100141618041c2d10030f030000c2200d0340c0c1782c20b0031580d07490320361055401c01e241d42222034401807400340501e41c03c80d039400001b041da2000100025902c000b9a90b42100580d030100d05480540b91038040c20004160b60f051011400b1065041c4811608900810750300617034888058510607403196001c203414030060b0310b403162102525801c00001e0f000c01c4950a100301d008200b1880034448c00300c12a03408003000c1c2e5010b00300b1460101d01e803805400020f0015250f06d529550240880c613007a046010604000020b0000e00b09185005142413402820060088011400304038817806e900710f054007271700c80070340800d55130110424450020344103480006205500b0440d00140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 687632428 1250 687631178 687631201
    0x90504080a090530010e01050c120a06050a061107030507120209010b160f0c0f06110f01050402010225050402070803060907050f070f1b06110c03070503030406031e05 73
    0x50320202c1d990742c0b051580e82c000300000c0101900d50500f107004c10059514003100300a02105107034400000204030103280c09405800c564040f1000c03000407200155000c1015450f00f4210341c0600e00c17090070810181404003141e4000c11a004610501c100e00c8045124900e08004500c01158007001301c8100b607882c0c20704d1183c640c0403000200c2c0141014000456829030344001d4860210350001c08035a510425103031082000f802d030b00107564020312118041180c90460f12800c0192609454110b181d2051003a500c0c0380c0303c0e2080100d04036900d000140310040c0c2c0e010410250032102402072204d2450040c2a69640003a0369200540c46440000d066080202403000707548990740440f00700c411607959820540705449625410320b0420410410300c0c0004542c3c24450104c40d000310074040f0095144404ca48c000c0c201a008a0041481c1017040322110004000c1c100e42424260040c0c00c6c45850301001c65940d0040f4081c2e901450b486510118202c04c592240541e4410040c0c01840320b814551300d01c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 687633678 1250 687632428 687632437
    0x108070b160b240609181008010c0507140606010c140106090905011d0318130b120105012301090314010b0303120415020c0d0c080c0a0b01140108010b180a09050408 72
    0x50f5032045107116010785820b03c10b8804045016040051900f03800505019030000103000001c0c15a050306c0100f40e89201b481003c80e16a01ca403986942d40c0c440d41041c8250860402401010f50710190800c261641d21503001072103554004038a005100020702014090314098008022051801d081c0800380301054100d04035000361504000151a0b084c4c1c44140c9070310072403410075038885845100112500f851881d45910f09940200002c1c01c401040c0052285450040c590515079154801072104070081d10030010280019510140d10000d40d10020b802c000c0c85120181040c00040c03585410481d003034105420300b000081c1540d50303070002c0f00307030100c06000b00b43ca0035199080b12048421842d1038a01c04c480e2042a200e004018110f5030308070072035280c00c0307454040700d0350007081c4981c42e20038500704142501144116141203442d810400c0d42a0310121900d03142d410440c244004020b00d00e4031808440b403100060300160f00c0354425401080e50801c16611103010700d890b00c003c01c0240300140303004c0c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 687634928 1250 687633678 687633721
    0x19030905180412182714040b010506041a1602300303190903030b2d0415030b04050a050607050c0606030109021c020f03070807150201050108070b160b 66
    0x55940000b442c41115840135001d070440400303002c60024041422041c082c05203250460803580e074030140c500a204282c0e940c42040e00c034108114001e00c410010704050755405041d0640d0800e040c1898051a041038407082c1404988011001419070140c002c0354054004041d0058103001495900c0d400300000c0000c5004146104c26906a480100b00c101000f160302910300d000350a003c1d0b80140708804d00400c1e4400c000c905160360382202070040e460b0214114407a0400a040341c8000761889070102c1c010301d4200f401032249180201020b8114060a620006d42c0d401000402c440c2c0c0e910b19000b1b1908240c80005011446501d0401112a60080003494624950000c0d2941a112070003031600361250043c000b948200042c42c030401c0984440d001e828903e0008258568400213003002c40d0400c0b000c0d0700004261340013000e0900205100c40031074480b80d940c42c070080245d03601d000c1c3c40350b0f2100c2c40d6004200c0741c04400901e80401e240c0312041d00040c560403a409010b10305120350072805990404603203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 687636178 1250 687634928 687634943
    0x708060306070c08070201030e030d060f050f0411071103031e0931020901030b130e0d111203041401020307110f0106060503010b0705150702030d140603190309051804 73
    0x155840e1082d15010000f035448400c26040807020782c01507001c3c00c902c90340c010b4103101c1408040c4881e015800ba04c80204102c3c0303a100320007401c2000303020101195202e4180200c7c10401140d80030289041110849038120b0b14014170503201d0000a419403044048400f00c000e4110789102c0b07003480c580010200e651045900016031560303404108155000d001c1c145425024411301c004001002c2e4006041d0160b051500080c00c14910f00040d0108924040340003007903590301604443c3c0801042070400000b41802d141c2c2c000b52800c4410350f40c031280c5040c1480703101800300104040165424400c807035aa9000e009540300c0c940250f0007032442250302e10800d40d80c800c9408100002d44103204180a031030030340c1c1d10a4591f030300b01498500d00c0c4d440480304a5907445a40a0354091404070000b0f00d00800340d5501560b40d42d400480da030001d5540030000811240200c609005096a0014030240d2060f00e080104103440300605007902e05614980c040c64102e41e5560f00121021454501140324520890700b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 687637428 1250 687636178 687636181
    0x9011d060f01020d030b011e020f0d0513030321020313050709023603010219030e0c0907030b040e0706030c2601050d051606030b042301090209030705090708060306 72
    0x8100c1c10160800015025070070802c1d0080c20b55102e078004008a10341030400501c142e44d5004c00005580940c6400030040e003040411540280d400c6c040c04040030614580103041001500b8010760075a000c0c48000d09100781200c1c07000c46240c2810310800c2e1900801001c54583c64070b40901d0500e0300507100d0813220380c05103500104031081944251103400c0361804a40400108078401e448000b180201850364182d0643d0801890760303024001413440c076442120360304480011082c003605940108400380520303088001820055100d8441c3c031a0301020b00c1c90003145a07000d01000c0780050903003d80c62001406109070210310b0340c0e0103420450a07003400d59100640d924600700b506002072402c118500e001030308000108203500d851042c0504246c0640c090f55801407071030401c18000701c8a036000d0008070342c50307c405030003d1034107104006ea0090b44060446001d982074040245c9403105001d0a000240e001c0b41a9180e41c50412403c00904009462002541000b00300074100b01f10440e11603229105050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 687638678 1250 687637428 687637441
    0xd05060a060503010b0f1207030c020f0a080f0a0c060608070f090e0a11061b07060f05070b16141314120307060c27030b0a06080604061a09011d 63
    0x2030340d400885880d56070341c07030540c4d0070030006881990290040581c80b210610115031203150358091503002e0000d5803400214070500810207410050200c54114041d044080c00101060102c0b04441c071002040c01c805564240c0208141c0d000e41c4869005050079240030004100414000b6400003903880a80c0070a101c40e555038060801c0d02e4200c1c50a0049802074208000020b65000901a2401c0c0c02003603942019002c281c002d01180300c0b0004a03045d54000d07507040003030036080a0041d80392065450010300d41407498540300190a406090000b020216130b07c210070035840760159080000900e40c0496460000300319510b0b03002854018282c41c2100002002c0c000d00d0986d141000c00000380003d98180412511000c006285008413403003444101e4188407a0309160140304000302e0b201c07a061405041c103500300004001001400c5d01c6106141503000d100e007207000286180d2040d440003020800d404070310901c0e200660610142c0b031304400341ea000816a5420740488507240080e03052580019034491 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 687639928 1250 687638678 687638689
    0x1201030507170c09060d0f0b07140a170c0f0403060e06010b041d22062405030705060702040e0f100b0f01050426060901021210060207060507110a0b0d0506 68
    0x2d440003101540b203061a101a03040c54480258410401080d0f1050001c003034603020f1540545400845403080e2034010060400d420210b69031405400002c828185200407001801d4011040c1c9001515404000020f4518005400721400001da26001c59101d9540340f0b000d0002c4c00600d038441c5c441380548400402e034259000c003a04d04443e400600160294255002d2007a407201c050140d40d0400d00745c042c91340b80c89480303089609000340701d207000203021500121012610b20300d44020348401c8070765000c2040709950000d62076049d204225802a40c0f62161320006008120b40d0320101d00d680128a51190224804281c0c1184090034000c02c0c04428007001c100f00c4503031410040540840d03804e0105000d0500c0c00c031a08038626198080754102c0e6121190b40c24a841c10450785a49580e4001a40340e0071241c0d0255050740100f0a81c1c000900107045c50006900ca04a502035a4104400032420030240001403031241d0021074050101ca40c0705e5103450807141141c0c0b10030302ca441e800d41844041400341c10320 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 687641178 1250 687639928 687639959
    0x60201060b0c0a03110102040b07140c220b03030714011d01020a05030f0606070b0c0307030b0d08090402031e070203070c0e0709031202150f0a0b0a0e070f090b1201030507 75
    0x720000c2d15000d00342d44e4040d90f0b4000742c0340c0704000543d4240008035100715030300028103909018a450f0300c160819500240e240c440c2440002e8051203210308204408100a10500d5941a207140041401545103001c289103003e0820003404003204003144442904d07041d84044201d514031104001c07001680300180d8241c0c0305aa0385480081d404100003200c3d40d1800c0e2000741c10040080c80317035282600750740710308508520640321202007400000c20b01c04095014410302ca84443c086c0c0c1c8000780c00c103882d128901c1c1c50048041144c0500d4002001460f00c071940c01841e029684185d01c031058030304046100179500d40103030400b201c13070b20302208001c1a44000c028206102c0d4141e6915074a045007940c1c2c40924021508130504194424501c07a0700c10900001400c0d40300340c41d502c140341e5180c5030ac00d9840b0103440340001d41c0c9005030f6080505103c01c000e4160260b9001c002030030510842c40c0415001c4814500541c810300d00050040307002c0440d004040d0b42941224010b00449440a40395405140030081 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 687642428 1250 687641178 687641197
    0xa06110a080c030403051911061e180c040b1503090c0f010c11150c030a18050405070522050904050d1116122a03060e070303050706050a06150306060201060b 69
    0xc248040740d41031046c1f1962003a8a441407409061017594100c0f0149030010644402c10000002d5141d11410310820301415806001c1c04144205a0101c00c0c0440d101d8081c550344c01c4c0a66250110030141d9103c1c400d002c1158450078103c907139249440f0054035201e2040070360b911b203e080e84d011082103542c81080c1c2002201e0f084084c5070000e1070003070708102d440d00f42c101c400b440700c0105100f14100c42d00f007403010307180954480c0c1719201c0c030441524420b000355000381c01c403070710445c41d003070500007a203a1040c10f481602c000390030401303400d00101c0702400400e4001d0b0b100b158040300c03500c2007200b044030100d5501070300c00643e1034103150810122141a01c40e0750301200038010650346002000385010303213640c1c03101c000c0c05081220300660360903a0307071040c00008069050550034040402c1003003101da0b1090606010040002e030600500b55034000b0050310480c038001d480651900c1c04940000101c3d480140101450852106003019541010340504400d1241f130307015510304900041e1070b8041c041125030307004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 687643678 1250 687642428 687642437
    0x3070c15081e0a0203090f0106140108010b03011d1509130201080f1603020d0204050406030c06090801020903071802160b011d0f1f03141606030207030e060c0a06110a080c030403 78
    0x3a203001185001750002420070007144654210b810042d0401c1c03084201030705072005803400c0e0004c0c44002428401041e8086842c0300c10400c01080882c80361801c0009401c0100030145e0944c03194420102c80c003d4184109a0048280c0c1c1800511803040355aa80400d1017a280c2020b15034841c200764080d018115007800e5860ba003a000100710900c00da005041c403503d0800018101512180898206c1d00c44c0d4004542e043d40d407403818008a508003038840014a44500258a01203116003c29203070143e5100b503040490b800140c203005c03000250180c880301040180085007002a90401120303144c000e118841810928200c015a054010130360640700b029081034030800d0751641382400d0303004100070255203c05018100f0200005400101507108000f4940040400ea403030358402c504854010340c0050245441000594002600000031000c018001c407030703107926a0290240c5900b05008218028003051414400b104524845070141c0a0f2426658410405a80356940d00c0303a030f4403040c0d4020f00440d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 687644928 1250 687643678 687643681
    0xc050f0d03060f32220603060b030313050d0201030e0303070306033c050a0c0806061e010206040b04171605061b040e060303041a07030807020d2003070c15081e 70
    0x34030740c49440c6590b18007801c50341222810f00b41302070950000003102c0746407545401003003048c00003c3c043c4903000601140514030704042241c0c070900041c41c3e0b00c145401119138540f90001c0d603001c0d030702900003585010252a03072442c015400500621184c002201d0548880080000111401c0d00e01a203541041040214104003032101030354914224008072028420b1122030400a2860750040d002042208020142800c000b41004a110760400031851900f24a021900140c0e900051180d0016000011030519403910700749444440048c4803002904000000e00c6008425120403481100e0b00800c05e03180e03ea04c40c486800403403a1501102c6614010902c02031002040441d03109402c610000d0440f407420b80c0c0c60003c0001e00320080c03407003400500045105010325030001c10301940441e00f440034241c1040c108001504651003410341220007030140c2e040e0001800304000315185980c0180394040300075511000c1c4034580d5481846440050740e90750120313086464421580102401a07811400d05 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 687646178 1250 687644928 687644999
    0xb0112230c01030207020d0f08040e130309050906030c031b0a0b03060f10031e0e010c030e030a050a030b030f0a050f0d050703050d0212040b07090501140403030c050f0d03060f 77
    0xe90450a003c0c7c3e80091008200000502200000c40d003103031080c01040d4480340750185501140000030a02c99118094100c0003001a5000e0107440c1920801c503140c142c66213500d80400d1801400c014031641501c19081d83c1c000707003030941d502241c04140443c2c0981d203044c1c40c2c41a2403030794013041ea84540c01c42039002d1403001da450704025025980c03140740741c00601010ba02c15022100700641180582d134542c1d4600c44040c111342800f4540f0090a00d003001c0c00035440c0d510515550303108140540d400c001d4007140075411070344280c00c03007500c480c402002c4650000d8007101298607040000c108448521132510b11840400c0c0210720058010b000303071205401c200c00342e1010b072032540c01400000e001076420040710248001540e0070901480c01210050283c0c03601308400340c1a0f02d0319802c101d052101041e80074919400c2c03982101c0950350301d441c01034000c10aa01d404c6203010003542c0104010702a110494070000d40c95071080c0212043c06001c0c104a6580d000701c5270701b80800050052060707190140d4000c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 687647428 1250 687646178 687646181
    0x1309201e030903130b0405040605040b2808010e0f1c0e01030203220609030f1704080904060b07051c0e1018090e0c1008010b0703110a0b0112230c0103 66
    0x2c1c001400c1080e40e140c80c40804040c4003214440d0810034a4210100d0180b019003050300c03030b240203014280c500300008104074001441405114035070860590009460f104035018418002c0d0042c40030300028000b02c1e1218040a49130200000443d040303100705000c1da07600c41304a40d405403540b04640c840703046903011030b03004401a5000806030b0542110744502600710080c032281d03070440c4500900000694400d5464010190f9265040b1001000746a541c1600506035000003683c105621500321617541c4022800310b40981815801000f10142c003103800800e010740494141c0e11605022210901041c0881c0180e5505e2030402c256a001482904036140142c0511643c0c02e6000100300e001d10030700d541e428443c094070b10b0f0014604903504810110f01c06410112182e00b91f0840504000d06158184001c0b0f0619015004010b4100903821101040000b41440b959451640200a03904150b85502c01040c0a100c0105c0071541d0041e480c06411419142c14020138649000700064030480184034011070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 687648678 1250 687647428 687647431
    0xd15020a020a0b010803030405010516052b020318070b03150907110f07140a1203080c281b0305031314010f0501062706030f021309201e03 61
    0x40c00e502c02c8000c8007020070100f640e400c3c0240b00c203100035a502e141c1890424295000078160ac040e0b0860201d808200d40e0300714044e1041d00329008200501a6a65094440300c20080045448054400070a1000417072003440c206206d031020000324cc030020b58540f41c2c05050300c001c84184c1062480015200190318008a0340b0350072000e10718048440c031220180c07107030803d41c0c001e40f6000c003503104400400140b03d9046030880c01820860308218154945401400c41501099000381000004400507403c204c1c02c40c1501c4091411505001100c062103003004403925100700c01001103203840304070000941d00120510001a45655540c1c1192100800b4442d00806040122920300403d0301100343c88030300b40318510108508003c0031645514012002d483d15081945450304020340b2100d1010304d01207041480304403080d62900248005012003054001d0091a0b40d907440e00544e101c0c0000c1189050b00002425003006418420140181c0261103d5208800d00c00790200740070894120203064140203103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 687649928 1250 687648678 687648697
    0xa0e0d1d0418200a060c080a050307090e070e040e0109110f030f120307170103030804080f0714060106020d050c06010b03041e2402031e1b04230d1502 66
    0x3804010b00c80d0b81c3d41052090035034a212140181a240c1c01003840e000c074000008058a040508250704151189105842803031958400c0c4680000403a008920817001d04004190040300c2246a08000340014280c0d40d021000520070b500748a0a011800e006205038802036030b03c1200515246045c1d01400520303c1340098003640340c02500e2803441d0584017845084480014408000e5592400c1140605214580f46a112280152400520010740c01c44480d58000b500a6800b58840c142201040e0322842080c0b80100352503015071004d0060500011000d058403902d03002d4410820964100312281d005020003a106a4071a1004028600d0386000a40d04103001e504000d6410b00c0d001c0e40824518140321017100d0030304125040100d1100380240303980040d42545415899410000d03e064070000090321a85910640b0401240031401008501c0e030f494001c8001c1242c072590f942400144441d007000c41010361050114920b5400c2c43e042c0a40400030360301045079903080d4882d60244000790400f01c2c61 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 687651178 1250 687649928 687649961
    0x2180c18060903070303120509060402100503040204110c010914010c171009150303020c150930031c06300204020304200f0f06090a0b030a0e0d1d04 65
    0x1c2c01c001d450a016510145000b0303112070000101ca0041b1100b2280c004114482d10f4000800748001a5505000d20340c240030300d85030076905d0b615540000b83c024081c0c009415410100003e049442c4503040d0401080940165140001640c0d1881d03410b098408900c0041d000840080102d0741e8017142c5003909402c08039604145941640741ca11003c101c9910300c0405003619004c00c000c108051b41084191282d08080e500701561a0048840201c14016528083e1080f0404a0400e0b0206800140c4164015602d40fa078041c01703114050380794403075124003003642c42c44204100e000c283e021140034107002c4545074055146078440d150800070078a01c07a81d850507250f510040180c00981e40d24005140241c0c014401100c040407140f0348007104110302010140075103c80812203000e5620030045107a41e50b0240d90060356400c08500044151350150070000b00500b0110500a035a41550f019000302010001100e5010401c1d407415180a0010380c02869201c0003902d07224200c0c24250815201700045001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 687652428 1250 687651178 687651187
    0x80901050c16033c06020901020c10050309010c050c060109200a080a0f050415020d020d060320010809060c0a03020702130506130e12030603160b0702180c1806 70
    0x31480c101c0e002640c42640d000032520b0203019901c00c1310402d0780c200c070550706011900c2c00c078024528140c0c0c0c5548201800c0b5503404100050903034028848003085640090980ca45206503210252540e0000e5480c407119603c0d00446c0c2241d54003d03402c0300e581c84100b0300103026a078a4a141e0001174401b229220700c14251802038042340b41025009006080216119922540386c0b150441044078000c1a490060908180034040030030b0b420501030595100b0584050f035200b03258200c44c4080d1048016048029140200020510080500702042850302c4a180c62060b0543e40046404550580354600982c20071404903404008120080580c0400c500b400341c107002c0d09400160f041c400703400100901c5515101005200e2620554101c4441030716101000320700760395041c1c1d507910081c01b000d40b20040c0340040032034920780d010440e10303280d90710a01c1c0350044c0903103a0400208a41103580100d0240d40c3d0800c01d007500e030101068061040c400c0f26440c13802e20000c07182c07801d0354004540400e90400d20401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 687653678 1250 687652428 687652453
    0xc031002031003080a03140a060312080705040f080f010c0c08030a09151d100204150e040905030318010b040204060c0b1906080d140f0405090916030f0b090703080901050c 75
    0x4c003d0f21441c0915240000c01480304a0640b802d404005c00d1000700310700d841424000142d032244031080c4a01c0500d00802c660b51040b070103031210300c07480d00f190004440840b000501c0480001d0340390071404010000340145a0f00c03010684008503001001425038078148001a008141c40e44021186030041303c4040c1d903441c01c0402c55048680c031140310481880c00c803188ac1400070003006040280f9508120461400340342842460641d503140c0490020810013210303400051340c070b980143c0035032908001901da581c184405c07403601941c2840007440f07695080540c1c4804600d420300c2070768216140c5449065030040259a8022152030050034150a1245c0f4161500390410512827080038042000040c4a1040c91440242c00c1e0382d05000821040d80042121800c801d00c1d15069034110f60003039035018040e440da8400c04e820100c4480d440114082000c2e000018020845206020640190841c810f251030f8000481c0c0c5607107090102800c035003003c00045640d544914010b04807a1136140582e990303c036881 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 687654928 1250 687653678 687653693
    0x2010806091b0f03040303141b0a030605060c06040c0b13060f020a050a03082e09020a0207090e06011d0702060105150702221b0903061a131406030c031002031003 71
    0x24103e400800380c040100401c154145c854506101c51264201001707240009e4a40d810450000b141d0047e08400714488001ea03000740c0000010f0302004107003e84400c01440c403607580d90000c42d421b841d56824178200003503a14040003152500c4a0a02000042d0381c1806010342e45000f0700760490045110340310703000004c89c00030f000300c1c0041c6110380e4441400b4145054280e04205001c40090042ea140d440c102c1583c414045a4008440500001680b44d181e40d0030203a09140940d4000b0b5035443c00c0009644000c40d001c503a2a0594100901030709450659081162051104484c1c42e03026a2004005008600d40a46189040214588c6280c83e00171113601003a000c254000480c0c0d0900900055058000c0e01c0d4014104035422580c5018044c0e9201100201505c281c0e10015082ca40c1d0b038508004210006011a40328032006807003400754031001b80b8cc03c0c0080c5a006600c4400d2400c4e180898114607000c1818a421000140100b60b03501040d42a5402584054001e82d000c07982001c1c00400640348 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 687656178 1250 687654928 687654937
    0xf0d0c140c061611100c02030c1f1506020613080c010204240c03080f101a0703090f051008090a3f0906031a031b0a05040902010806091b 60
    0x80000e01880d0800c0fa50305070a18400d824180140281c0400301185400b0010760700300c841a001101007003a004020050b8114400c581741c903040740c00340c40601219100003240c4515005507a41041001c0f2000c3c1c07284404a940500400700180c0003400071500a031010040c2c03000d0b05000b20160b52030011204102d9007207a1299019036900100185420101b05000002e07013006009070a00051035807259034028400d00d4000c1c2000080e00180c00402c03010b00c2d01120501c0500482c0d103507a02501c0c0510705840705604481d00c02c4002401d40080890350100c4515a03904030752016100804e000718102c41a518030380f0041140c081c600c039280e035150116802d5451403201c64403080512058241c28400c000c41c0d490700320354032811215041d2030a04480c1e88603d00d0307004c4468916000408000544000040d0254210006c0d450300c954442c00b80342031007811000001039022031700d50140b55603420602003551030301030018bc01b080c40300300024038500300844000ea02001c41c0d680f6065048a810b00400f02c2d400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 687657428 1250 687656178 687656197
    0x301050604030b09100c0309060b0a0518071e08060f010c030504120602070605011e14060901080903090406030c0501030c110606060c12030a0207060c020c0f10030605060c0d030c050f0d0c14 83
    0x40362234600c0b040c00a0303480b500381c19220507100300086a0400e00801d9000010008480707140c41c038000007651b0184108100380054100c458401d0444111583c010a211429214a071013160307140d07070882a560040ea04524110f41c11344949003080c0c5020001e50007061224001e542071602044100c1c0001c140b80700b2580a01422400441e40c80960740c00c080c4154010381004c05140c0b545034800c00140c0c0d51005540d8040c0342481e0018030b55aa0850b070508500078003c2850f002401d0030707404010000b0340111841641c900ba03070104000c00400380111129883d078490f0a085400190104030b131414050f006015030440d6004481c070349500300290000c0e5078411203500c901c0d15404542e000411825006a100070b444074401480e126607800001000700e00300c20185881170745500c203045e21041c003c1c0c02050060900500c01502c800c00f0050b15500c5246003003400000a00e0000c020f06550b021b0300c141c80f810351010b001141400c404800c0c00e0010060031600c68140042c0c5034400b18240900801001d00c00da = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 687658678 1250 687657428 687657431
    0x3071505011502030d020304020103060815040b10120f0203030c1002030912030618041104060b0c07080601030f0b1f090f270b10080d020609060702030301050604030b09100c03 77
    0x15101001400300d81041c0c210304105200c0ca840045125800015241000401440141e0766103403840141c001b080c1950003882c040c00f8012004403940e0b81440d0b050f01c00c174059121500320707a59015a0541c00082409003060b00c215070001180821840c40103545210320190890b80f501080640580c0f500d001c542e10092a1030b000410011000c1060040c58400f8480040c09070450a0070700002d15005031041c2400448158180040c0a02104102898070030f00c0c060801c002c0c003034840000c0c0c29154410700c407511041c070031180c0020713041c84006402070481e40c1012172010601e08541c0d0304012481c000d171191210410f40e101c010104512060400014054000c0000f07005440201c3c040a458030f01600341007805d003a46c0d00401c010b2021503c216200d9200680401c6940c480c1c88070500b0f1041900081d21900c20005184103103500001d4150040322580121415941e402c0c3d0126500d200034041c43d034200c00144800c00000b000c00303c199403c1071420f41541c0b441000c501ca9a800c48910240700703c0003a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 687659928 1250 687658678 687658703
    0xc070e01080c041a13110a0f090b030108060403050c010f1b0f0906050a0f090e0703240b191e030c0f1404270501030c0609090516110a050307 62
    0x1107500300a25074407241c06403001e0101581d02c0b074030b591480b07100c0d0070483d0140d01c0d8070703d1400003448a80d01000d030743c030b4241c030320355403141c0e03d0031801060104c4c4c0085c400007003a8003071008a011905401904d04a504040c01000150f0700c0c1c1d0380450340c9402410b40300009640340e841365000c08186010300400400107921b107511580c075032400100307551007400c20034041c401d0140041c41110780c04021607207047c04030700b0080d1052840c4102201c007889180c0c040022100144280000303c1d40c1034101116482c1a40314080c0895865018519241000e02c101d602d125010411108954100000c00c036402c0124203004418240102c183c80400f80e4440d01c00300042d6440d10140d0720030781c00001240c88281c0c2480e1009800b400101e5511141c8214025215020036140c2a007180e030b02d0503028a64446180300c03040c800b55075a0310380420702d4030580c0200b002080348400085480311891003607500c40c1c010100d03c811900b10401042c0c85803680c003e1510308501640460101003401040108041c0c0c0c410014002070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 687661178 1250 687659928 687659939
    0xe3702070605060402270d1e060e030a05093d021c020307080c12071407380d0c0207051005030106080115020a120c02041a0d11060c070e01 61
    0x4036500100f0341840380344144488942c41c007800e0804e140c02c0b4010f480c00e941a450301000900d10090181c0700904810251448050700c2800b25000400c092160605025016094400070b031280902441c0c500065000c0c0080005072801030240e0020f68034800f0010103e901c986044003043c0404908507409000d1100e0a803810b660401c4181d108400e0b07070a10261250850304007d440703100d0620094840207020890140241040c49040340b8401ca40500540c0d840d424541551961040d02d1091210b00480c0c02c001401c80a00910302c00031500d140705201260141c90b48540002d101d5210140c100d0000d001d03a001720302c6140708040d2340c034100d40c001701245444c1c0300c10400000080004102085402d000401c00c09400c502214103440540c1307011042c101d01064101d2800c004803801401c0b2010703c2c042840e01c0740e00085040070150003610300340184c2c510a0003403510404400a040d41202d00108207501145246103644461080203003150b02c1d01c14503942c41e40ca060000c3c0c0007000c001e4041c400400c003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 687662428 1250 687661178 687661181
    0x3060a030f2f060d020309240108070e0c030721061d06042705010b030304180b010206040309051c0b010b03010810140402100509040e0708160e37020706 67
    0x20340c1c250701d0402c06084070060080750890241030841d0040540110210700f60600600100a0003040305500f030403c1e0200c05190b81e80c0840c2845694068000e40001264581e50080450301c02d00104601038555224428100c0d420303041c051b250001c810210300d02106c040124040c58000b40888071348080040c40d01120a03803256405480a8800c0349085460180050140100d45442407869071882101c0d40900b03007a03014008c48500140e16003c001004500000d0790030f0543c10035415688100402c6444400580c0c2d50030040d01e0103008100000740800c0940b40c030600d003110340759483c210305400c5009036480c2c40800d04c080c0c10070895408007000500001a040000c0e06002c0f109d0103090240078009200d9804c2000c000d403010380500d2100010007400c80c09001241e41a41d00908200035847c6182d81c0c054031002c5074000c0580c00c1c05282c042800c0c00061820200648030503061100840d191800c006401d9100d070080c01c03d80c2c640c0315808a0039030318451180c00f40901c3e1071a0160f03a4640350b150074030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 687663678 1250 687662428 687662483
    0x1f1809060c05091c0228091407030b0d0c0e07050f030408040302120d0c1b08030d0504020114070302120d0b1003140a022d0c0318032e0203060a030f 65
    0x1030780b0342d6880882000350741c903d80c14500404100d506c0704100e801d82c8991204011503604800d04450030810070301d15078100031a031284030303040a5a042011010aa00300101400580d80150060740001400e01418281507445a04010f03141041c0c0d242c4800341c1d804a03000d400c00c4606458038103011400f00194242000066802c41c1c081d030280000c03070101c0b180500282201d40010304850006d121110400007224006c4019103045d02c1229120116620807801130041158200d00103410b0013a59003002d4404026280310030f07419000ba081d0f00d0070b411408200d0350010b00500650944540d2001030b16114120302e40c0000c990303560081581c008100f106964040080c1c99940c54034810022002c107060308011072001400304003a11412241048010b14080c040c03812844101c1c00300056040d50000320aa844210301026005da443c0d5083c43c0080088070710324403c0303942c00d0846052941a8029030b80c2c0c015075002c41d00924030160261640c0310504d040c40d6010040741c0b00e612070440225080e81081069 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 687664928 1250 687663678 687663709
    0x203010e030408031b0a0c1212050a0c082101150e010509060d0506040f0e030c07050405060f09040309030b0a021c0c09090f0603050111121f1809060c0509 68
    0x45103014900345465070b1342e114100341113500112800078454140b2050103529481504501031a910301c5d21104900b11004042800300c402c961002451402c00d0701035400c1c1c6042103119101c0c0c04201009843d12031343c5501c00d007550505002c002580c56000201708001134060424a00c4007030860317980d854054074210282010b513051010a0045070b445540d074904590b80e85913542000f180d07a40341c40d004200a0200c40040d03034103540c14032903120071325030001000e8840c10310124100d54035070b5600d070148400c44400307844580c0c104804203032841c200e040101015030824860721342100c846550b621506403a4034207481ca40902c0b600060800c00d000c90481c4906544a10110b0030032013007a03114405840c0c00081e21855100c5601c442a503456401a42d000000550f0800c0090145441d1810040207a078891940620340049000224030490082c002c20350424100450f04000c1c00c0c10108101c440080528110b00d070340340c54640d03900000e4050b00420360525401d889254440b590001007050200c100c01c0301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 687666178 1250 687664928 687664933
    0x30201020910090e04020103090809130c020706090506030a230f151f081f1502070e0c18040b032a101b05030f0a0e130207030c0b0c09120a0203010e 65
    0x80c130181e4840400141c225909090000701c0100c00d25140d403050040c3c51246038400c0040c1c0000f14039130304c00d03003040580520700d5003540d003065141c200941e8814040e002e030581003032080c40024603550a560001311080740e11342080041d020f100c62444400c000c03c480d403050140701030f400e110030400c4080e810440d20104403900000a4001842212036010080c407140800c050300d00401c1624410705c0c41d08501203030700500145c642e500c030f4280b02e5406002c8204038005100b00d26001030140d408940342d0b802500e10450303045c9000b6000107101214002d002d40c503503200e0358130f000d0000f040d43c0411020564248414040460110080c051899403149207841401a5258142810803513408000740f51000c27440307944a00b6802250404c03d02c1c0d801381d00700070a404075001a40381800307030f0000300742d002240b4122080c0c03000044a00c0044180d020b0140001d000c60302c28001080050380d8650001c1c1e0102001545031704103a450300004031002071014180343e05801841e8404290300f800e008181c3c408041800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 687667428 1250 687666178 687666197
    0x10e04030503040308100f030501090506100b0f0f0d06080c030106080c031005040f02060a080f1b0a0509040f02030c0904050a0c0906210f05090d0306030201050a0e030a0f030201020910 81
    0x300940a0311005100404209031a0700049001142018402c0540503022a0021250702c80c60304070b008004409098520f803103004005800d2071140001d8809854284ca801410916010440307001c642003422aa14034100510984074410454407a1500800c9050300600f2191400000d01d82181c280750400181d50b005004c0242090718001003070030b0717444492100055a0791307c0e07080c0300640e000441c8001b0340c40400080c00c1c0c2c030519070082c1441d000e14110801007400e501c401a44121421240300c0554000b18240a020703049801040134046040f0040c2010518820000380ea400f2a407003140d800c41c00080200301d0030501c1c105841115408442a8010002c031142034501404c1d1107882c1c0700f0b840c1001f0124050a0320800003002920400c5007524061103c40e81c0307a41010080d0a0854100714940b08514035015940d2203402030804403a010b8481d40e02c0c081d0b1490040f41c4046111201d15010720440c2c05d440c001820700400c601215001e54001a1202c0010041003c40080d40e40b2020400460300f5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 687668678 1250 687667428 687667433
    0x1302090d1203150f18022503021204080a030518130e1501080c040e0a0609030309030e01170f0c071b03020910030302031611030109031809180210110304030602040e010e04 75
    0x500300b4140c80300514002d0100714906645c80203031054403654007254168100074181c02c1c5d400d1851503401e034440e0302507480380f8100955403503182c0100c2c03051302c20076400b06100c1c10104e40607c0c005c040300c4401c0c00c1100310201651001c9418407510000440586a854942031002c4c0c0c03081c40507a002001c040310044440d4945046c076540c1d075003803d4425101e9035503100c1610b000740080000c8690207901410510000c91641000350080c862800103802250461403991015841241c02e9106100501030100c0c041d100d40030b01e1906147c000b442104a11350400981c0c002c201c82c800b54000c14103590318280409800c520502c000c0c09405021409001d04684040c0002074002c020781d0504910041c01008032405800c001ca4454024010160076500e040f0180050652119044004840c0642e00345c4543e5510b6121200300d403016001e0319448040740c400d5200519002800c030025000394036000b6160005520791b18107680c820751080360f005500040400000446801039030042414411100300b624064 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 687669928 1250 687668678 687668699
    0x1b03030a02031c0212091c050304050307030f09170102220b070b1e0703050717070e06090a03060606110c190b03041b080a02030f0c030703021302090d120315 69
    0xf0403c01c0d002d00199100b4201480031641070310320303401c421082031600f42000c172641c60f03d03201d444101100003c68a100c1c54603e50144084a02030365125005500d000011740b030848000780c80c029840c1c20807110000005001002d4640d5500c5d80003401d00051780e0f04202455007203401c10509040c201800300800400c0601403400940d04540e40002001130396641d1a80c40c1c101140d29400390050004c14002485185039040c2e001c603109942c180c0314900b201d00306400c4e640b92107004030380e045c0c0003c0310240380f03c8050600c003019040c8000d02800300440c007501d903070304e0340d064610716008000003880c034011003500d282e01000307045a004400d03104210148003005c5411000344050085801c0c40000201023001c01c0646007548500034651800b00b0030064544c0382842c5c854030f035001c081c1e20034450040f0040e0344410109502c00030700c0c0d005004100c41441e6034240701e251486002d0001c026039003400641c1035a01d86641056403030780301e101c0700742810540d81d602604640301030718401400d00c48880c1c2030001c100003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 687671178 1250 687669928 687669937
    0x80d0908240106050c0106050a0f060f0c02060306060d090506160206011a041413050a05060a140a0e04030909050403080412020d0e0f0604050a0e16021b0f1f021b03030a0203 76
    0x6458800d6031817101074481070240c00503501c81c0d5088800c0c0c220003d8010034200601007990b182c0d5540c528550400c0400310b0b42005249800b951151007000408c0c400d03d4081c0060215900308100400d000c00b1030389816043c00320072074200c80b01030544800b1908a0398184101409031150305480c0c4444c04d24040d8488040c040c5000789030740c013460311507201600c1d592281880140f0411704000d0005c0d00d003c00341c25000e8941a941c207405141c00c100c01050b00700300313600c02c0c500201019054004092900412800ca0440982309405100c46200c0225104005002e0103105038040c1d11156034909062030b01c0300781030701003400007000c54100d0b03885a504a0b5010b00c003031580d200704071004083d000982002502d98400d07179001d50b1344209441c40018a09a1007101c00f03100d10407140301d40710102d50014050b601c0b01e04040703514400c62504403207800079141c0000c544000d003030301a00780300c264944008a00840c0d01c2400801016900c034901481c02620f6841d030b140c0070070000741d0155007840d0b2482d4011f0741e24001e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 687672428 1250 687671178 687671189
    0x90d0c020d141b040b030d050708070c031707050c061204240c11010e010b0102030301091a18060f03010b1008090f0a03090810150e060a080d09082401 66
    0x7403503600d4418005040000d8001c07a8401056541820a40200009240f0303c0b048007401141852450003a514000c2a0340c16452015100c9903e03004441d502e03100168440c03002110707400070040b000700109501a001d041e201403010b49480e0b4900744c0c5c4c20320a24100703112400341d125500070016000d8158040c4100ca41040e030002e19152664070300340700c08903500c0a2241c840903031460f2280345c014455203c1c2c111001c1240f500d000308040c000f540700e1a802d89540c2c518040c056842000100803410036a80640f558500e110b05144c40e19502c4400180080c00001c1508480000e4106001052500c40721034101920210000c10189115501040000b0b61982d246d4080c1b0801a0000b0850503080c01038407040c0c005d65042c0c80301c01101e443c002c0c12850071401206118450000d14080114540c803a421030102c031600214209864a01241c0d000e9000900880d0420200070300000d0b0300b14100721001c05480c050b140c1c1300805007800d00c0980380c40200b515660158101d2085140080e00d50040d681c191032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 687673678 1250 687672428 687672439
    0xf0c1e1b03041e320306090d08090303010b1e0d020d05070e0405012403060f06260c030103121e030b101b031b050a0c090b100e010e01180914090d0c02 66
    0x24000c0c40c1300345140b011810940d4150180a0400c08204400324941c52191203c0d1682d841645642c404681ea900090050602c0002d040007030307140344007080c2030f0b030f4524410300e80c0c0c1e551038005001e000306c0c1070341c10680b0195030480e2900f0a1140181d0046804890b08500f51000c1016600d042400d4040d022080c0070001711116003030070701c01c940d44240c001d0806851800036150145070b03149001058400a04059404004074070b600c0d00c009015a0001da01440c0550700701c1e81180d0951303c40c04154504c2e4010f0606015240211441c610a41d24032145c01000d90788000890380860300c00d2003880030904c4078881c10880c803081c0d10f801c220307a80210b09401c82d400d85006440700407110310b01e4080e01c00c10700c0050254803800b00c0c410b081142d00c0f5001b0082d07900d40c0703006012400c042d405011042940c03040e01d8010402c540010340055102ea10b005c0754008051410180f40500486e000403101055003201000980720381e525190201806c0c110b6400000100040031014092800203054000e2000c0c024441e9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 687674928 1250 687673678 687673739
    0x31505100306030804030b0103050610080a0201050f0417100c050f030f04060e0f0a1a060609041509020a0518010e130906062c0f0c1e1b03041e 63
    0x40e00c00d0340480043c6511000345030b0354540f6424218904802444100c03810b10603007000450000c81c2c040c6400460b80104000e04081c1043c0c0d00540b200d401c51044070301c10803001d00000079215199400794100d640884040c101c1d0885c10484541592600301c0b454043c01020040b8160000131002100c1d0300008002401300c3c6c0e500c13030386085009004000c014210f03078491642801c0d85850040350079074506104010440c90b900c6200040080d0316002c440e250342c80b84090042694504294108215101000c510494216104e0100c034040703800c10445800010f202181c041140b528200c500083d9080c242042c0410030300b50340002c0c0100b021013401d401c000d41c44400040811000c0c0c4c11840c06071003642144c410020340c5454402c03c4010542c641e00c4004005c0000c00c01612801c02100c0c002d80f0a402228505900c10318805c800e14000910341003200c4041114850844c010a05014031500d041c01071982d40d03150034031894690559012003070402c42c221508200b80841b00e041d0700181d1941c3d81c424802c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 687676178 1250 687674928 687674959
    0x1031113051b0306130c1214100e0618090a03030e0c06040510050c010f0f050a090308070c030207051008070f020303010b18030a020a0f050301060b0c030307032c0715031505 76
    0x100452800c0c17020000d03042841042c4210b41145a03d4080075402808010b0740c80070f00c0000d01000000c0d1802007080281c1c0006115240000b40c8655000c08003411000c51440d5103400c601c80350004441100040d000540c034034080551502440c04d00c140240d0080591054941c0000d10520540c40317003a105011700000e41c2982401002541e80c900090002080603540004421025202d02d05440b21420301d8240069400c000c603100f0401c68541668852040343d0380d1140542d61510360f001c055083d803003211000500b903a00d49086d15a441110359131880c9038101150081c0c4550140905042903400c2031005110000e40788085c0c880e401070344031401c070b03151140d24042824500c08020294210f2070b85d00e4045404022038641e030088070000d8000b000070f1540c076000c582c498000d04145801540080000c55038080c402e40128448600e4070000102120713141c461104030403000c04a42803140c0002d41c04001c404580080e804261001e428117004501d1151902614018a80985807040340e012080618 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 687677428 1250 687676178 687676189
    0x10311010c0c0b04090c110105041101110106090518010b0a0308030601083102151305060307050906070510110a0f030e0721110d0c0902070201051201031113051b0306 73
    0x43c00f1600c416595281c448683c000034050700382e0500041129035102804c581c00520500707100300e4001200f03003481c02d41d5400448002e020a41410300300c0d0b4951102041880e03c602c00d0a002e0820b00b030174038a214072060001c9003901c11000440d8800c003103020b42000464005402c80f94400bc003441e10702c04550700e030114420501d5092400040e8640003807030000c01031000310b40000e6024002c445280b03c1003c6224003c0881c85524107180040e0b8032000e0806c070380d06004001d1900b1071086d08042d41804203002c00b24600790001072040d01d10358803581d01d88000c1ca01d2071251070b040a1300f40c0349962400c4031218000d0584544401018100769843e841d580034080f00f40840c20282c0345940c03000c2040202002404ea0720400b090742610b07030100701001010285403a000c3e81003400d502800c040b42181c0381c86d0384400203420910069041c090100440781c00311404080031406148243e41c1840000c4e4480148014680840b0950741841d14101c14003c00d66500f8880401c5407403221500c541d2683d0b540d000c2036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 687678678 1250 687677428 687677453
    0x20a05040303050f130b1b070f09020904090f0807060501051e0609030705030d02010617070302010e0915130e060a0e030d0902210c100903020f060706020c120c011103010311010c 78
    0x111300c3c1e1200c2e07401140a003161b00007010441a1051036115084108403160703100e245511919141080d10b0401f002448070a4010340201d9100400000301181e0603214034000358420141169546d10025800007005000d02c1407902612055440a00e0760b01140316000c9415421070180c4d108250102c2d41c14060740e010403448000e000090240c40603c0304020010780a0b10b00743c058803881a9200f0300b0700350003030b00008405084a4050f034800c083c07018504203101c00c0c80b10190000020207200b40441c006038551402c207072910a500b03040042c00c0c80480700c485050803c003604000d085828201e03900c003088400001d4914004041c240040c1c0b91f00e0070320000740342c4d02a144d8503d22044e41c01112640c0b01d0b41c04124070b000b03017000381c0340c01a42c451145001c80d40320f211808000d502c42000c0d02508000d04041c4041d00741d092048000500c0c0c030602035a1940740106441240c0b030f24800020324102605400c0c000c440028000b0200d150171541103544150b04012001c80090400c030038818841c0610819030141c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 687679928 1250 687678678 687678697
    0xf0302070c140321090a06080c0403080f130b041d040b010902032e050103060f030b07030506060c0102130501021002070b06121c020105071e170411060c160801020a05040303050f 78
    0x24100d40c904c00310050000c3e000404550303c5158114000501d45002d941d000303220b4003c82d50407501e480c0c10b50355504e01c04d42000341103c1109a0074095890403691020355200900312200c110394840d840d00070b4905041103500f60041104140006020002d05502022410340701405005078032980c51801281100d0640c848213030820721440c198442030f504014240c4159007083c2e13004e02002c2d0312003c92160091080c40020311501d4440d000542c264820340c012608030030300a06492620340c1e04c10000d402d80c0c00641e4044940034098100f0405981c042000303401c80d640c03490042d4101440d54035680000c210041080340942264180a00700620a015110415030f202c0c030050310708001120000c0c001c01085891102140c4c0006802d00c07854882e44240848071507955035118588040450b000d0201e01c0a00116084007007903c0c03d195503a034080c040d1801e040440001c095002043c10214400c482d160b0080c107290344100280c001e0207501400f00c5043d0f80d00350900b507541300b4007003070645000c1c850030401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 687681178 1250 687679928 687679963
    0x210f140d090f02040c0215040809030a0b011d06030c01090b0c2e0b04092307030b0a020a02061e16050d0c030603030e030f1902121005070f0302070c1403 67
    0x140d00c20405a0b0140058490003900c0400204c8019070090303a903020300114100d407041c1007900060000e14181d0041c6240701019054074880d11740d99456050071074082c2c1050024001c8280040210400340c4142c2398803001c214000e100201c0202d0019040c0252405203c2c0f5120300011100f10f0300c5000c00c15040c4543d980402c24681c1da41040c900c2a0f09030070545101e80050800c07021103c54a051b01601040c07d400006440e48140310301c6003018600e54101c6000001d0291400c004041340d209880e0074400e0008500141e42e540d500ca00083c102800140040b022403103c1c500c0c1c125460922016540c03001d520800900e400801c418280d9540c0503c10f02102801c0c284401ea01c0b4039035150f0080c03c00c40e07204c1c2e142c107007940001e4000c040d00c1d9030014003207038950f600180c10600881100c01d01146074034000b07404080744040300b2504038106a91104410303043c0c3e490b0b1060103100c81c0d0044950070001802e28046061440540c0c80300c3c00c0d0078151098002000500b21105c00940c1c0502031200f599070b1a850 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 687682428 1250 687681178 687681191
    0x1101030f060315391805060405100c050105040501051501140f0306031c02010b090601051c110906030f070f0807020309010818061e090a0f060f0b100c210f140d 70
    0x36070030419003000b000030000d08124000c883c0c28440380d10f403178107443c2d004222078146401c15060280d00390340c00089004100e01918044042042031245500507401071001044600d0b1038164503002a2403480c0072030410420b10791031060403441600356264507088100b1142d0f60f446c1d41000902c4c1460b4845240d45a55805400d05901d603015441412210015211030603140d50b5800103540d0b038081c0c2091201840101002400700c03100e6948045056144a0201418180828045103040c0c1003103d2844441c0194018400c1943c2c0101d0315500480407480d000d1030601d44030b4070094980c010039034401c3c148000800400e13580302e800d8031546010325143d000c59040d80b62070300901c04002c0102000c0d00840610402049404601145c451560307500445030b240b6100e49940e039580107003c5e0001400702c2c9603030f400000c40d03907036101b05404151070803550b1100e000c61404d041402c850900001040041350030409048034441d0450400c40000e051414a10302c1c5d109141c2c09290503200d00380d00103d54514044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 687683678 1250 687682428 687682511
    0x20f1305070219050c010806041118090109020c0a0b041110050a2712150c020a03140a09030206031b04121b0b030609130501091101030f060315 63
    0xa001520901450b82103405800c081d42803c02c1c0184021400380c12034118800511855014010312600100701500c00100c1c82c0e4424040c0b2078a40010406141051906a580406141841c0e5180c0500415201145068201e250321699604150f00c002c28000103800045d0611440d107040c5940c034280034001c14514052003100038001d0b400b201a05020440280d0154482000e41c0281511400880d081c070344940e0030005002400e21400700b0407150344102d0160000039040c00d00903210740401a230018406407009141c0a040f0300780c0246903c0800106002c0c2c013607040c0c2d00c403822a0440c0e0b0140c1b03c0300e0f40c0351215040118203000c80a40068011000500060910020748106051500441481c03079580d2021221040364245c61180b100d400c941400403480c02d01e00303949241e410004050030240c060045903151400d688a6042c01d82e05112084041225540c2502528400d03000803c0c04000150031035480550460980e01c4074070b5001c0d90780c0c0c41c1c00461600d0006c0c0d803c0034070444444100c0100c900 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 687684928 1250 687683678 687683681
    0x2090c0301150207030314130504020a0c02210309040c030f052511120c1c080709051206072604080304030201060e0121020d080315150a0c0f020f13 65
    0x30b108004451030b060508007401c61001c038100050343d9159440540714078070543d4040035034201c100d010b03104100b0058002829512071000302228003413512000300000b0140104041d405181c1d0108140035610000c0407084030000c02143c0c98400c04403800543c1c00042e400840080500121a2026074601700134400707480d036620031038400c050040340074417230009460804554820013429aa80541d100c5511503240003802000303820541d07103031b804031003100440d8480070450104603440d01d030200305050305015103a07604c10201c00141405a6070340d400d00c00c400c216240c4d01c600040001c020004070348510461550145400440c9071800300d09200d4034140f40c14110340e294400c0e0340c02c40c00b541c43c000000604807071701c601c43c80c100c0d209004998440c541648007020f402c01c0314801283e01030311000b000e90004400c0c002841c015010700c80001191417003281440701001c90060100c42c202000d0013907141c4d05070300030f140702c41d15a40700001d03aa000d5014030208640040c1002e015a111074160942e5031068842d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 687686178 1250 687684928 687684931
    0x1612030c0305040315062d171f06050a050a03020d03122318070302150a030617030306030c0105041a090a17060f2a0721030903091d01030f0f02090c03 66
    0x40c064100005450568200860812000ca41c5000041047c208803052041c440c0d040c82d18100c3c030540e90007110018500800030020070714481c1896540c142400a824002a00c8020f04001d1b18081107031821030300004c107240d440100060030000c0d01100e000c8880c900d50424180700e00028441141d0746600006039000742030880342039040281201c4401c60a50340002d0880440360090701e80040c3c241d1961600442e64403030340a64041c192612800280c9401d8020314180981e40c00000d1520f03400c2c00c02c00c150511031021107280c1000414002440310101c0364040c5526400c0101241d82d03502403000118100385013036440400c4110300c4a060601260740414907905c502140c3c0403818940d520b803224641660f2820103100b00900c6100032683c09085100010300c00113000c1c61710058000d2600b81c0d21000d0314216500034001a1f00e8060680c109030300f10700c150f4003528030b0100364100001c101c41e500c13014040512024101419050034070040c060806101303071084e90040c04141487c9086050484141d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 687687428 1250 687686178 687686189
    0x606030618060e01120515010e04230709090302010b0319031e020d0807170115200a020409080c0a0f0c050d0b06010e040b030715021612030c030504031506 68
    0x341403a2081010500d1007088160b88622141680603400c0c81207112a12075507070ba00300c815205991f054520f0000f402c2041c2d00806002942c101e041c5014580b9040e440000322043c14900d8150820909200000ca2058151228040c0000b505202418202d01504000599640500404186110500c00034510088450107611420b03424903856038138020308004038464400580000403040f00c1707039124610640c0c0101d00e91030b05980440c0c1100d04400c0c13801c020303446400c0c00c02044400e102c407030381c000c0704901401c0924a0070800300c1c1050810030761980d00c1024024840c580e5600b6000c2004521340a498000240c4000c803440726485140034140345411314000d50721441000780000d0107191030030300216916401040154107880b01c0c0010745000b100280300b41d0340140c91700210117450b01c04201d61001800c04c19101d03550180c0103000641000000d80760071601030007105040c0100e0812201c0c84c1036003070349890940c40c03070041410f045441d4000d03508001c04490300c0c103a42e94054220b5802070801c2d02c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 687688678 1250 687687428 687687449
    0x6260a0e0105090304080c06070c090f2a0806090c070512031504020c0c0103050a2d1407050703050a02030f03010605120a1a04090203070312171528050406060306 71
    0x3c0740d03096016070324092031003400360a600111444906080100c05840f0345442003512411003921503601d01c2c280c401e82055484101d40d2810406c08280f2190055080141d1803000280066482d84004107414801841d0038000c2501710040b0300a030201900300c2e081550460240c65981074184151001a070043c0e030740a2610b0703a446c11861480c60107100725210b040030100140803801c400001580580001030842221300d036507502d07c00404809996910701c800700382c5050b0285100140f5404111460303520b07074191040045003001580758200742121240e68160401548a4110102c100c0c6140301c0d15440c0e130382e52900400005807958005c006030000e00610704640b5003c1e6290f03200e41040300c900303401004001d481c0400c41c1c0c0d07031810540d21468001e8009016106004d440380c4801d4000c1e418201e4035030006d450b000003c666a4280e24080350041c030002591440e42e078031200090740480112108900041030701038000440d8109012440c001d1101800a10217103903209000f400624651240c1c101c201e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 687689928 1250 687688678 687688681
    0x80d090c080c030715030b120f1e070302061c02071e060509010b0f12101d0607080906041202010b1503011a030103051504021c0503091c03020706260a0e0105 69
    0x28540840c41c6820f8450300c1005c00501d07080304408502420154840326003000340425181120042803141d0748080790716078001d25440f6280555a000c0e00c80303540000500f80c001000a01c0182e17208812605035640c0601d0203101c0040e01c1c02880000c2c455950020000450032800000c13480c00800c1b20603e050141e031080196581740402203083e10203075503400e80e0210941140306903502c1d155160a0303140481c60b00301e41000107041141411120740707032003c801095900c098544003480400181d40d0180a42c03400c0051402d02d0901c41e070391140050001040ba0012580704101a4801d501246c80c0c07010003004481640d0544c1d800240c5640203004002e5000001c901e4800010784803001c5a0407603034490003c101000074103080410207034000e8030403a071200c8031400c080b00c2981c08200076070341e0358001d402455861550070100f02800c4c5030b40303989c0e9002d0b204400c090000b280d00401c0c058100d5038582090210055140b820b130b0345001c5d0702c50340300420002060501ca843d0b4196882501c0046001c070003000705 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 687691178 1250 687689928 687689953
    0x190b03030c0a03110f0102030c0d0c02030f03040605130b0a0b0103050114090609072106050a060309230f2406010e0d08090105070c06020a0b0606040b0f07080d090c08 73
    0x101c1c4105100c0700299400382c811000068801c103d642209403188003070f54250a0310818035800e9900076180c04155074000b09415074102c10610665006510300d0000b140313410b41900350310f515404003d002808841d540c2000480e13003030080c0a1414050380c4100c8074409454002c2140c0c0c01000da41e0b81560002c2c4c13a00c400442c0908503d56070100005005042000e641c2d549000c2004c18080244000c041201c500c03030303038078407246002c407a924800e8217034000cc10710f5410320082c485901619400141054105055140400d07032141400301100207201421030408100e150482c681a0940402c0009200301d01e0b142c5030100107010811051052060761403000d444010045800341011044ca9511806019041000035800b0703000340b20000d41811b20505011146e01c4024003e40d090b030044015030040c8540d20704100702c182c805070b40071404886a0307040c00e04040d101c00090091a80c15039100100280c48401c0c49805403d595004103900d034148080445031600e0310300708006100b071200a200d44144440c0703 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 687692428 1250 687691178 687691183
    0x6030103050d11060606120a09060e100c14090d0c1809150221090f060c0c061003080d020c010605040906060f06030c0c0f1b060915030204081902011403190b03 70
    0x2445d0040801d814040c0b400820540460003400d540c0c1310741e50b6030702000009801805100c036401d90110140c40702a54441d8050b0603980364420403001c000e029420380a0018103c810f0301c1d000b003400c4c0c032283c0c042d02880c908503810038165001420303011815890324010500342c0d04a1500c003441101e107810344003010155401a40a10300ca040310001c1031000c0600c0c4400414176040e400103005085805c01c0801441d1320b42840707004c1c0c90b140502d44001500c3c1011010400480360040c104040d01c41c052440d60b05c03842110701810710842100391b000101c1d1780c0d02d05425080b002c0030700b000800401802405250420041030b00c1d11500c60095030311a40080d01c02d000f403041202c0750240351240281010142c4d40c800d02a61110021600c000e2801d081c3d4048140701c840d544c0203441d02c3d40700e8848460400e18003070807076006c1d00595800c0600400c03090004070301c0410920034184143c11811000d8500e440165400545000f41008a003008800c110391500380e40741a041e03101013510b04101c4541d51805054 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 687693678 1250 687692428 687692431
    0x6080106030803010b13030c030b1816170309041e051e0406021e0c010c09050a061e05451806040f020a170601090e0106030b01020c06030103050d1106 66
    0x40540000340010810440d082000b030843c506d030003004446981c2c9990fa4450740000381c5e0000c0d03604080000800464603540c849000e0b4030000742c0004c2140f41120017100643d8501405001000300b010507011f85050f0b02002543c100010043c024450b070100c44181d60303030b910041483c007500b0504140c04145d1800080881e901ba081d11001c080b2040d076160340f18040030354011400300d40400100403070388031105c010340d015000e814203c90002c2a40030040800406900e40e54100d10b1069903068170030850381c0c2d080300a0b02400610786140741c420b60229801030710a0b01a141030310419031140d030080c1e4444154036000c540050705008012800fa4194903c001c0e8042224048540110360003d00c404124003407524141e0003080204049400701e200100481030f604405a0f160200e02c0c0303c4c81c25070b452641d4900c2c15511920a00e007490480f481c19500c005415418444e40b801c0c1592a20b96601d180d1003800000c0c256400a0811603803546d50349070081e43ca90789550203400042240001608011010402e103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 687694928 1250 687693678 687693683
    0x50c1b010207120317041a09030f070f0c030215070b0106140d15030c120209011d04020108180607080105100c0c1e0e040809011803020a17011d0607030608010603 71
    0x1400828180007031400f141c08103072010780a01581242c1048075906564055104611030b1041256082402c0905080c6440240000100350001d21a4003204842c1000303440c036490300800c10b00300b101e0050400f0405403555400180d0010460302c2c0d0b0840000c2010020200705128984601503a0f170f80d12412940c00b80710000c01c0305441c60800c60b03140240002c0d00442070314113880c211071420310b607242c3d181805078603d0390042c4040d200d252003000540c42c3c216040d6004040109800d00c43e00303a11201d100361008020002418000c04501251001d60003004403103074010750b1402c44100c0c0c14191000f5100c20024480c003480b401c0c0d4800c1d000e082500c100380100c105940100307a1050507040079007041044281120303030144849100000030f440884c01d20818041d50203140696900d0103c00001006141040844000c25600b0b01003040180c584d81d550320115221403a181c41105161058107000d0005001e4032401c514540b45e0015003401c0c007299aa01460b41038800b084595596003030b040c01e031038052001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 687696178 1250 687694928 687694933
    0x210303010909050f01051503101a100c080f030a11090102120a2c1018150c06020310060e0301060b030a05070e030f010603110405012105011b050c1b0102 67
    0x4000040d181e8102c04030aa01c03d9095401581c1c0d410b640380c1c216102241d4002824010300c480d0f8503542030502801514003080501032042c903403d0032801a1400d10b50005600481400c0c4400b00098441c492810040f40d01c112001c0e66031240084816070b68209841414101d85081035141200080c0340c00c8403d00c10068001d806160403140340300c03070941c00c001d50200510044c0880c0c640c951814803500c40c1110381c070b00024a01599036105010900f00301e0000a0140714a9501924030080d0003440b0000303e660f003506040d46103101170001c990491400800074640350000c810320080858620f985001c0e101c156039002d503002070307000405007038844d50710801450000c200081124200c0c160451a4443d40d18188a030341c0321807040c04130f480c00241008500e2070780d41d1064103104003c00f2040700400000300301e4051101e075060250b000c070801c0035246003143c3c42010045803400c11000b900280001c040c0080800300100c10300102810590191b0700c0c1001900444030049031301040c1c0d40d4044080207043e0b00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 687697428 1250 687696178 687696181
    0xc07120806040b0310020d060e061c1b090e0c04050c0702120a020a0f080d0c02010f050306041b020c04150806011703040911041e030b0c0702060f0c0c210303 69
    0x40d1000d1202070501e41d04552a4026852661410020203401d40c26840d0016514080b050080d0f0031110a5081441e2400f084c9042c4007041d03031501000c4070381c00341140c40042030350950300d00040f0080c4810780046104480920000b1118066841008030315012070548600100321810007040310340403610008040c000b88650005400d0405200c92040b8204e0220342134015641c00140e0112003d0384503c03980c4a40e00e030700f0702007150306000c42c040d000e0042c113000384002d03456800031b003048510941c000200301d00840020a15900d981141038030907030011004128005903480203494002c0406802d0040d82815400310445010200d0241241c0c1200040c2002c0c0c0d080c003000e100d0400305850000550b1000340408140340265100d5120800c03400241640c0d41e902c0d0070070301c3c5070424201a60401c4070000c1e007010008070720800701e803c2e48148021581035541205200049a0b030207205c1040108a0020030f41d038443c40070002e8440b0f0303000421183c1c2440240d04040f282a03d03200503820b902e03680c00620 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 687698678 1250 687697428 687697463
    0x10303120b0d060e03041502121e160303020c01180807120203070c06030b13140a020c0a0b13021503100909080d0510030303061406040b0c0f030409060504050c07 71
    0x14020700120700010840446503001d40c441c0f8058a045880c3c0020581002608010007445420f00448280c25400a480059103c3c20f0318040360042a0040f2046018621040c1c005501e41003180d0195a80a00205140f070584c20010f00035008044103103074035840c04c059149e8010040400509042e0300680c428908511540e8034403019403840707006815840103001a0001844414004010f404a6a00024004900800c0007601c030803180c2d0742c506007494804541c0c0c00c14010b01803540d010508e02350159445d009081c02c149000015400900f4260b40601070001c403040005010380e80714000c488488040d09a4091078032988002e50700100c0310240004200000d902c540c01c004d02060059800506009103041c07424140c5108862041155824100074420140c1521958000e800e402150703045644180700800d14900c500d0081901200d00030403001e5120f0403c0001c0240d0f03000100c00e8035119961800e502000d0909030007010f200724282000134200c0500d62054507401c94118413401411500007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 687699928 1250 687698678 687698681
    0x402070302160e1e06030307140309040207080306030706020d0f0f0306091a0301050c0c07141f050406020c040902090a15052d0907020c01080a020c0109150e0601030312 74
    0x6160803400c1d401440b0081101c0502075100c1c10091583e4800d101e80341c50041070340c2d040c15001990398518030900708240f00f11506c000055907500b03a4001800d00c0e0000c80301d10024030b14021040320b20b50050001441c0004c1103d8200510300031282038007203910301911341000307036240e4038401c0c0d000c00081d20400256138001c2c8503841c2c0c050303004101e08000815075103075817515083c1c501807101a2103039200403602e1009810244100b03544040211401403c050503144039035242c001b544250b0011a140a0043d5a00e944080060301c10b40485500707510502200140500a81c001e0f21801c009800781050302081d5007014095024132030350089c4045000e68031710700420010803000c2d5140c0c840c1c03540c44c20041965100c03141d51040241c4403d40460301d402c030040c040700d0041c002040107801406048103000e415600042d043d0801070090070101590f965200d00b1800078010031004150941c200841e09043c4015441d12025071104900144415014002825a148020700c0002c00080c14030103004100c1d4120b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 687701178 1250 687699928 687699937
    0xe032b0f03020d0f090b070c0c1208090a0909020a230405090316060b12030c07052106070f080c0c100f02040302060409020c0c120c09060409080304030801140f030703020402 76
    0x1581001810300e83e100485004880141c15080f0305107070342e10120000c1c40442100030754070610b10314000800c0b140683e20440110302e0340c45218030040c81030821100300000203050700c07220b4401400c0c1384c01e840c2d03458900c940500503503001a800381c80380440208500005c2200703101803980080404c080d0b1145001400020300004120f00f144c3e000a01503030320b0352907281c0c0b401c001850103418045940310a103000c11842506501e2076550b10762042110303455104004c606e82040310012181c2d51311190340d40504004030101950300c144035000719020400300540050f9540c1c2c0c911040d560314100740d40d80c3e041c541201d12031103801c071105900105881600a40c2604000c080503074500000d4240382e0380b43d0105046401c81d4008040d025000300307410660728020000a2100c0d00d085030f900d1140c03501968002e4480c44140f60060140c03280c20001043e81d02c4517044012055801001242e803032805040007401000280154615903400c01c14101040c549841080b100d10001005020b030a86145c0c00c000c0207510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 687702428 1250 687701178 687701207
    0xa0804020111060915100614090604030503040b03011503020a0e0d210306031103011b03090204091202010b0f040c09172e0b04150306090609120e032b 66
    0x1203221451548120511095009010480007002000e030442c1d02a201008010140e801c10304019004205245d404038005440b823000c1998159030f0350707407040420280c0c880c1e0341010b803d81c800040c0000380585000b000318100c562900308040124200c0c6001c80c1640b04a4a90200081800d0007410007840c0460004500d02d00c0760b410205008183d0007040b000356401420807010036a141820001e000c204800d07401e000208078020031001d20075800c070030f444000d0602c003401050b603100e041d44110b4485921003400250000e20350980d2040c0340300024040c14401c820180520070040c001c00c2d0300c0c01c140c010340388030403282d0720b41d05006030400c50304a00c0c5910300c5401106a00c00c01c1e10321141c140700780e0b030500c001002c20701140d107981180399209400e554080c4a41d50140740707061706400e804c0c40703680f40c03050a40b81d0088020031100c00b1802c092020305504880901401c4a0311001c60780b082c0c103c0c000b08800d240550556200c030b042a951010001c507402540214600c503046d04204a510880d6403818006 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 687703678 1250 687702428 687702437
    0x603060f120d02150105030601060801060c061401031124030705090102100e030919080d0f031b200a0f12110319140c070501080a200307080702030f0a08040201 70
    0x503a180c03052441e00721040b840c2c1000d030708041010003018500d80307200750241400b0b070000e085651400400030400801441903102b00101c505078041004003542144000d01c14061048645c0d5841e410072224121a1004c0d8520980c0c14505000c00b550502d072560081003981141c49056559024041d2a16406000214110b009000c1019400c0c40c640c0300d140341d8049404019504e406810b000d2084241684170b42c004000c0383c01808001c0c45000003010b41c003424081c600105100c2c40b0303103400d40c043c3c181090520045842504401541540140403000742d80080300481c40d01162400304545810300b46c6005407801d0345c520400d101050069000c4641c103881e501d0038005203060105c0325420f40d00907540d4903805400f14028066283d91003010584119400480c65140c615402e010075584c0344c862181c00d050141d0800041d4a0303524603402100c941d100f6101c903960f0f040031180b41c12007641c41107607031001003000070001c10111440001501e00001d10340c034509181215920081e1100f940c0100100d0400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 687704928 1250 687703678 687703699
    0xf05330f0601090b047b2d111804050a0309140f0409081905091003061a03101d04061b0c060b1309050d030b010c020603060f 55
    0xb01301c0d581c0200002c0c916002c422a1180030b002d580342c10400451060007021819041c8111220010034155103000c0180c1303440ca40c0440042c030b0302284400c6580032a4002c15a0f081c84110f240d14000b02d202c0750307030b11480314a01c92854180341d0100c201900341940909050104003000018540c020300c41d4004c2c0000c00204040303105d9a6503918101045808480c0c031703041146140b0030150410b03040c10140454804c21201c071504040807070035003011170260921a940703500e603140c00e1000c0e0030226000b00300b011104d4003c0c80302c0c01c00302626941c80b503d40d507409010740392a6002541d01c41e00c22041605c0c0901c181d1350400004c0c40100c1c015030000341c4402800303026880002607810800b8000d6071240c912010f2241145454140781d02192107422070308800d5070701111010304544c2d0101080f8041c07070b80550b002501010f4100480d10900d4450f20381544a40340c00040c034144580020940c07605d40700d03540d00740920715916004407401442c5e0340340250000407d00c00700da0305240c150920122088050040d0401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 687706178 1250 687704928 687704939
    0x50a1b14012601030f14010c050d021b07081e0303070801061d04020406090e090105010b0a110a050609030316111c17360a0b070c0f05330f060109 64
    0x1141002c4e4012202d007684040c43d81c0800c005c40d6001c1400e02c81c0007000b00120520200013400502c81c0c900012200d42e8001000b02c1040c005040c100c43c8002100300f100e100a44480e074265544201c4d400c24080e4500d01001d121000b400001168403482865880000c42d9181c6002aa141000300503011145043e0280e000259140c501c090030051843d6035074400c1003407034400495071380740000d01050200d905080051201e540113504880c01d081e500d20b40b440180f020742e0103041c185140d01800401341d0049500740704d02804000050b43c060b0200880151100c03609400c02e1318014100034405040750081c0a0300c030701081c441d240408484226090000c4a0081001e407003540c0300003216440000341405e0307008440300e00c0510f1103003803109401c524041c04036035180000c0d54441c1c0b907110040c003400361440040c10300c9100e4005200d01c158060034605a0b91902d181c0991140303e20180e0388c2044414410100340e8501b0038964110a148601c0744c05100d40341e0002d1103800c005c0041c0700702d040c001d61140c00a003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 687707428 1250 687706178 687706247
    0x12030c0c03150207030e0d0b0f27060603061602070302060f0903030703020a0b010902070206040e07050405060f2d031602120711040b010504080304120f0204050103050a1b1401 77
    0x40b110307004000140c2e6424503141c00703000d002c01013010300e01030740c0d014800100045c80c2c043ca15030008112030015000d40d07103920100c51401c3c91512250851101d6026500300108001baa10b03015640c220191002c541d10310300c2d5074000034032040e04080103901112082025081c400014410b0303c04040090780790007882c0740420b1661340182d00450060703004007007020034000781e904105e0242403000815850440c50b60001842401079000701e500c03011034000480d10450007a8115001840054003c64031808100102c000342d801c402e00f88d9981c0085c42c082d180009041c0901900d4103030080281d0703070030b40e1a2000405000c111284c2c1c010258070400d500e000c601c1d280034004e4440c55200c0c1d24031442070119002448191224480541c0c103014040c0300511088102006907000e680310300b0f404041c110201d0030203030b00e250003604019401900d001e0020051000c0411035507001401008035003100c3c4402100b03150304090300c0c07203400769514206404810640c8a0b40603488012a00c1c1000e4014403222054a207 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 687708678 1250 687707428 687707453
    0x90903071704050a080d02010507111f020903011e05060607120e0102012c011401080d05070611070f050c100806010f051b0705090a060305061b0d29090112030c0c03 72
    0x1792941c070414890002c01c1d42401b4423a407020b4645060301c840e0801c058459594150442c40001c3c0d105980c006074401a5198161501c2e054001c00a000c10300f66401d13a01a600408050780c0e0020b800c100003d003c40c03c1c4101240c4e441640045071001100300803c0448000e0640084a8119502d8152504282c0fa250290684010f07600d01c44820700007440704480d003100c400c0e643c820820b4100700010415040046035007082d000181c204503540f0501c0c0d161034001060081c4100b184584041a50800d00c60381c41c010035041071090080703d40c28103481d01000180d401c00d403054800a02038200151442d44031b0b2111103242c0445080c0a41015103400d44101080c0750300040b90b117030b1707400f1000800003445c1042c0b03065045512141d04201ca00e0075919440e803035003400ac1409880300350b8880c60581c000b440c001145c1140045410422010074030780c407080c400d528640080c0362004915505c02c01a480c10030b42e20340c100c1d915100c0814404600307503810340b8124090300040d56401189a00000421450203140307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 687709928 1250 687708678 687708689
    0x501060f020708010b03030a141312330f0608030c06040b01050d05060103120504090c0c05010f11030f040201050f0309010b090f15010c170705011a090903071704050a 73
    0x22440440c40040245820265440103819078100840c205141d00d0220440c5d07403021080c80c2041014442c50701c41c1c4030600c9104038243d110801c0100002d22440c0c00320146203121711a2101d1000f0310050428003980b900c0d502158940c80c590922078a150755065803060640220300040030408590340e1181600f141c00c8441c1030055900b01c00200010080003080740c501400c0d040700c20180c40040381c0c03521545c80d101404001d1070091340b14102c103115401482075074010030b06984240032a5803d264014907c06a46500b10703070640c205220400c8002150144900c90325192010b075065a40c1d52550300408e400161040e414014108600414426000c0c02940700d10b200b40300219204031110248883c5a40c000c1510190728030480500c2114242c09030000082c00091814402c5041d007420b0030f000c1020030844403203640e40d002808200b00308064104c801749820010b403500c452100c41c5c0a00c2802c1108030b580600341d0b0010042d010004100c550300740b038071181c130f01e0700c40b0706080e203030404102c20b1f0509412070b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 687711178 1250 687709928 687709937
    0x31611070911042105060c34230307023607081b1b0708010f140109060311011409040504030806130c090506160503041203020d030c02060c0d020d050106 67
    0x14030110f039504c000010810340c0c0b1407204903c00d0075a02c80a4407584050310389261000b00041035400c00c20f240c002040d0280030076810501c07071071801c00382a80540742c40c038045070009680e415421240c65003040303428000c9201c501551804095908200c00001d10089a120fa249100b0840075003d481400c24401c1d200d05d01140700d02e60a18480c083d0003d18014000b40962059040c80081c1e01120020303550401c0f0440100d0341c0503042280714509100d45038014090380c0d031a143da18003840c200c2d0703048800c40d204103c0500c0b0b0203036240c0f4400000d0b515680800740001c00d0000755540700e03503c00d800301648112601c07503150424441074001400d882060741c05800040490b03081c000586407040303544000ca401060200896001c00a0150460a252050300d20810001c1001d5500e8640112518140d6901900b500c1d5115100d68070080c0050603402c050700181708010b00b007041c2da07029214501d00703103446400030411540c0721407050550344d2010640c01251a020310001080240b6030181c1030181009485 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 687712428 1250 687711178 687711187
    0x60a110106060f0216060c11010e0904064106010c050a110f010c0210030e1006170706020f1009030e030f060f160914040204030f030909050c031611070911 68
    0x3c0c02481d014000455015416030341038100300a9130050701c41e4940582c010b80310608a640c2400590b04802c10004c3c40b50080c215408000402006070710201d108160882d0408076840701580ca80e2055415003402190061500c0c000307a1400742c02e815542c1d10400515184a420345e5950b5000d0810702e40082c211505180400805c0f9240f030320704403030b010590082c41c1043c010421500040c01c0e0f24011980602415900d82012030304042c10b00002580f1181400305220f915900d00066100300203000b446071080c040c000c07000ca905440071803c000310500610081c04118061455003000301000c001c2103041c018441b0b09410251800d10070240c4150000000d04a18907101c0e103206060140209411081c0c01c0740c186030b001b1507412815100945e140d1071001100801c40501140091096030000351008040c801d4500c10035a1146810055628020091210b03468200c2403506038002628404660030400303105100709845080e20555100d02c1c0c10454400c10f5480942c402102c80ca440555000e050006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 687713678 1250 687712428 687712457
    0x20d172805070e0d0f120e150705010b040b0a0e0c120108060a2016020a03060501030f140703030801030807150f0905070803040303020a0b130501021612140405060a11010606 76
    0x150340f0303c68600c0548400c50910415540c1c0742d841074030903c005284900300c4040210042c0b04035218002c0c02000340584002d6031102504120035001000100d0384c96080243e100704500785409081c040c80381c06031026020f50b0601c1c0888815030002800000c1e07205060110008940c1c070588400d0080118101400b0b06061a418840c29692054000f07a211b11805840c10030b5200720b007040721803c5c0301c0074000c03c100c0074440c03002940c132424960014156900f800300100901000240075601180b1a1100305001c1654040e040c2e21144030f031102a0220700800300410100d10088000c00c02148126140e00c1296070b118442e40483d904d4580800000f070752101a00200b240400c24803004d0500f6200840c1050301e1030343c000307640741c00c6040014074044032003012514641300f08401307050369075028000350348030560f05003010130010b107409080c5c40e60341c0e4841c400e48805005500500c00c004080000501d040d080c81e05011081c0d001e009288100000380c8403020013500284181c1c2e010303291660701c1d1200043c118 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 687714928 1250 687713678 687713687
    0xc02240d1a030f030f0a0504120b060108070c0807080306281802070b0a0c09080d0f1d0d06020c0307020301141f0e1b090d030e0a06020d17280507 64
    0x3a0703481030283e4031035084464890000019203c1008207a01010b60f11129103c0440300b074005c0f0390105190220480505c030400400024061241c2001c1c1d96070091685c42e120100d910a030001806000c611081240e03e001c10b8002c001140e100c2400b5014502c41d03c21030503415540303a40c0c95500ca1042000040500c03191030421040004400d9852040d424138034a070b11081d80e0785d40090403220f4215580e608500a81d8000c0c440c3c4d000501110003660318100017044041c0000359980c1c1c0c007800143c0640c140491908402c1c00e40e403145c213070207403a1070341600155031908002d50101154141e207200074080344005a40c00d014122440d1075080d4000e24900b06824041c40742c4d00d40b0a0b40c501d030104450705c140458101000900d03840341d8441240411a50000031201051044550132a0000380080307c1c036042c140c001c5000a0240f10a071040d0103165680d170022a01c805c3e403460680001103050700806d04181107208266003103100018115114149050a4443c45080550803844d598440040001c0c0f540c11 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 687716178 1250 687714928 687714971
    0xf0828060315062606151804030306050a1a030a09031e0c1e02031506220b032802010c02030f0304060c060b1009030303021b06010b25030c02240d 64
    0x184c43c43c070348402d4030f0300400c50300c54400821800c48240d141412025550303030644041e00b80d0107440d0030001e072801d0906000b00030b000c26001d00c0c1c0c00780c4804000060782c4210b12030080d4220104d8594181540c032100135060107800450305c02d0f000c10101e103900c07959129030103002d40440300150300c034502c8c800c02d10319001070f03050074030360b041d000c0c0d82c0c032a200100140c0c8000c10f103005e030304005004008041e82e0b6400058040b00c240c83d441025514001540d0005900c0d96114840781701045003140e64001c0c10340b24094050400c05110000f46821078205030042d401404800760441c801010344039014019208207185030407540c000710004030303c500e0641c140519440b8016500c142641c200075004075061000d0300549180c80001d04055000500a414001075541c030004184140706941040d40d581c0014071440e0094844c0c4868060302d135122070200030b1071640c508882035064803404480213507030b000c0014459a02c4844030843c0c051a05444c80c111441000300318641c1002c1c0009148140c103840c0c60309001c1d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 687717428 1250 687716178 687716219
    0x70f140c060c010c032a0c0f080a080618070e040f0f020a020a170f0406050f0909100503070e06030a12090e040c090506010305061f090305030408010c0f082806031506 73
    0x2881046d0404000c0b1080040c0c0080e100b508001e51072229914107001e42244031403001d131498a02080742d6040e03541c00408030340118000c90349146100c1070081c1c032800429098030344001081d0008009181401c1c1600a010403444103440041c60f5005040700000b61b9120009034401608103d01120402050300d05540700707044c0e00b5a145042c00c140d12040c0c0701c1c0784924004c40051040220f9491103040e0401c04a600944020703001c842c3d6410403001981d800c50003801094428007413440003188419581074200d2082600900900000700c054072000c0c11880c512003108100302c0f65840100b148404e0881546c015031080c0c001c080c6d528a4100703004120360700075082604143c00c00341400070b159590f81c1e4580780720010041c000f03414010010305441c40000340c0d0008140307000100b8002850841035010498004294496080c0250800c0080b202c00408880c12081041c106035000c00b40100c02040760800c42a240303000654070740380c0e1600f02c1c040d801c8111101c0c6403038032500140304401c07003094540f29800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 687718678 1250 687717428 687717461
    0xf0209030f030f04090218272d0402120f060402030d03111b0c100c020a0602011401180f0e0a050c0a0b04050904050c060c21070f140c060c010c03 64
    0x101201030f5070302648600d21403042010340114901030ba211684003021001e01004010114910410450700001a1082c600501d0f280c2c65000084a4190403080c405058000e01003149054180c516011404c1c0d5000e80242d80040e140401d40220700380c01c018a041d0000800002c20036032a040c410540780c11000c4d5a41c0007014140300b003e085a51901c400e0301e84a101c840c00340f0104024101074580b07401602c240060b80140620429012149c0ac0307a1480055030090322144681a100d510a03420307200c0d002003446040d00d01800421a805103400510201406442d0110751400e0900b180c009440000d00300700c859410004c0030a0800400f04110074860700103844a0007413502e020740716050b5000d148a000d0290075403000080c1000410310011210f080001d12140c0c4500a00a0b09070b525403045c031450011103080c1239003242400d16036043d03850309070b80000100700419156950100011803213401000c4c0744504580d00802d5075421000e0a00d9010440001508081c445030003003c0c0d4200340315081211 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 687719928 1250 687718678 687718687
    0xb0a0c0801060c03020a060213030b010503030304020604050603094305130903020f15060907020c030d030c1e03051b03060a050409020112020d0203040b010602030a021c0c060f0209030f03 82
    0x125000660141103810328140182010f55506003a810a0000e200041116100040540049940c8406c40040d2401403034100d500e40e0b214030a0590300e1109940107580301c00244403c1045207001d00085510110060603034119400d843c20941016061041c0c480c050150100186c41e01a107456040d030034030f54403001c2e40320028a090085001c014040090101081e00e4902030700601d4020480c0380580c1600d101210234116400282429494090300d010f8803070000c09011402c40c9100290100302c050001b00502070101c01803c0550090034050380301d07000c1c40300000307018101515840500d080c0314038a8a01280d03030b1800c1d03c076903122a20241c00320a002002403040c032900d916501b4000c1c4c00d48200b500d002034440b41500040c0d0b483e0041118049200f400050703d02e0f00c0d040950040c43c02144140721a4080366201d210598490165200003001030b0700440e0440703082e002100901000b9215410803503031100464846a05440e09004840402c80d00090554850b0404114105100c2124070207181003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 687721178 1250 687719928 687719951
    0xf0e1504050411061e0415020d050403120c06060e0702010b09070201180b15060c0c01021203010506270312180d0b040b1024030c090f0b0711120a0b0a 66
    0x2a502610b041d68010b2101082003580c0d00320032003882078170401c2000e1180e100d9603105820546400004d6181d001400b8451401c2c54a900030016102a2940141d0009046040d60000c41c0d2000348000242ca5143d2904000a021008000520301403281580017082c5004401c01703001c5070120207004002103a14000d00c20305442c0e02d0b80791401a071079000d031644600d900c0792408a1030a90482940310392040000420140ea580001000c00a0820a80940b118915001d562000c01e00003440f0f9203411010802c0010308165144040100402d20012140607042900e40401d02c0d0445080d800101d08a0003e00404842d03d44200c1e81c9148404641007a003201c0190b450013488080903200621a0b809a00429011207000101d0006480d160000c41c45034101d55100760526807519545c0c101191610b610642d1140c1b08107541e806030740304042d0b010b00051810046c401d10717501000094940c01403007910312156940e1807541085062480c0c004115882503801d000c411910041d24140072117145c0301e103807801d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 687722428 1250 687721178 687721193
    0xa08070f060c02040905070b0d050f0c03042406141804050307140a050a0c090e01060b1b010f02042619060c18061d011d090705040f0e15040504 63
    0x65400e40e00c0c2c610071088141c4041006088145e500801c14042c418000c2546042e100240c5917121600205104030748400c0c4c92f1001c0c0001c1074038010805902000010007054404280c8902920320134804c480000c08070101030222001a0054031032440c480009414600e032001055003813607540004000c007810290398150381c900c50260300400030000c05189540341a001d112010a05401c1019201404070340e103404000003e1070b0180010041c503125030f1100c3c2107414031980341980c820744941440d0040100314000d5480300317400f00c04140d41d04d0300707185a0401401d0010704024581c44142642072400d8072052002c425003000401c440d80c0c0004501519540c0d040b04000d440c81e0071103000a83d1504440c0b00f02c0b01c00380d2035140724400c10385411f40000d04662000c0760080a05015031079103107090040300110703007031500c106291666091030390095609142c424040b43d004041400e29a24183c1d5511881159150030383c0500e800061100400c107041c00030380941c000e5081d045608000902e41680e6209 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 687723678 1250 687722428 687722459
    0x17010216060902271006110a02041104120807062016110607050d080c0a021b03010e1c0207050103140a0f020f04090510060203190c02012c0a0807 64
    0x1d0865496a00c000d05645070003400c06007040301528103840d03046008640b200032060503501080d4807040b000c2c000500f580f00d00390150a503a40d842c05801c5000d026000c000180844040c0c240d8001800c01c000034001501500d80c60889105101c001c0d1541075900b4030360200c3d1084070904901e07401000e001e5407085201c0d821189001c800d0120590b114465040403001e40508960003a0094000505071050003000a2010642c0020742d5603810641c3c0c80c4a4912014052605160056440407203044141d540d141666200800090700028464042c00d09252411740700103070140f4004031170702d02c0e40601581401041e019200030f007000e1140003018411543e501200414201e40b0310b42d1600c00441c0240b06030100ca14845062040d0360712a03845104040c001c001c180d44e06242c43d451200300040c064004001c0e9480707600791b00000b0424000d15542507513a020540380407810003a02043d5000700d0b10403140e0500c1901e460308003086901c0c840c54244a055149504003120a81c00400100881e800f00709400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 687724928 1250 687723678 687723683
    0x31c0207120302070b03040b040606090b030307060b040e03070b1603051e04030c060e0d0905030d02061b04050901090b1002150a0f09020607030203120709150c02031e0717010216 78
    0x101c19015203003412410010250000592a0b20001c1440b0501404407000350103a4080e000030050300f42d40707c50090460721050b40c03041d016007040c0a401d0100300e4076404400c40003c09000030070b0741640341e08220b044d0f07803040e002228003840c19400d000f80168076220001ca40c1c042030a00b0801030410509016540060a1042d441c1d000300d000010101442a52078041407948a14180035082c41d0180168403018110020000584031400004191070b00203014680706003141c000d0300c016201d115403c1141220b1041d08200198100b0000441d41c690f840c40a000f801e5034940040c446e205601000100305690544030110740c05a500600c1043c00c80d464190400003900e400a01d00c074424038000c002d41043c44000e9440070b40824618245a004001480f1421502d81c80033b4403599840400c0d0b4100b16903004455910140340004410140110b040001541c0010708941000041c0e2100c40030321110400016256000400e0400251070311a41004902056400070b6040c04200b1a00800071094080e01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 687726178 1250 687724928 687724949
    0x150a021501180c031803030b03120301050a0b0f1204031841060c061e040c050402030c12240411030c070c0b1206090109090807021002030d0c090302031c0207 69
    0x108070014004d6200780b040460b0307100c5c00540c0140c241406030061000406040c001e0003080900000c0c003080c00c0c210780c140d80703004004400b0139081c800304038426004022660700040042100031140c880480234a480f903803081d51030a09044e544030305a00020411f610240e2025146041244112503400c0b51000240f9250340c145698030140c104018000c082220107074012800240101e01442c002c035060b032046010180c01070000d1000c0c16107012031601118003401204000d00c0c14170491600e50010360b00000785480440c20400d00764502c40000d00d0590b1100031240307000c00b10a07500d54509801845d90a000c480801015815070344040346444010406030708900700040380e00410a0345160007018158a18000b41c450135034614034180542d041c0c2e4000d11442d8200c0000500342c24a01511035050b522132030322400c000c510760900c0103900c0503140340b10543c00203204c1c584051070107200715504080c40755541c0080b140f640c018503042001403001e400f000d0341003241500485400180c142d080314501c611 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 687727428 1250 687726178 687726191
    0x2d070c06110d02040e070809030a03090510180c240e030319050307020105130c0b130b191e021906020c1e0d030e12090301060302150a02150118 63
    0x4010005140d0300188101103100401c81c160b49004a501030701c20307100400300d0b000403910381c0d4000303845603e402c13109100a94030400041c4c8516200341c0090211900c035008441920304583d06001c142c0310940c1040c002000c111030510144083c8044c1c050046c4646100d580f007a0382600c405841039001d9825900c00c1c845010081800b44d18208215204000c01c5101e903500724002400003000b80d801030301d45100541c208400300e40380c0312722052506c20155000d103c08280d5481e124120140d500010881020900141800264544d00c840145151010320100210a013030401000d44003800220142c40007904040503c0b502540001714441001e000c410b0000b071369041441c000e0040d1144054080041c0150707070300c20000600140c01c0c0c0410915803415240c4154640b1401c5040b1501e00b8402c00c45a0700c1074003554074040c0d03048003c0200150180000c68507a0300c903004210003d094000f0914a0380c3c002407419060f0754140541ca0b1107580c0061030480b03e515180b411800d040360803942c441c2c035603a61070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 687728678 1250 687727428 687727433
    0x31e020a06050906061008070c0611070c08030d0c0503060307030b090319031b11070e1305010e10050f0c090402210405101b090b070c030c0e2d070c 65
    0x301041656074851400c1c0002d19280707101d503495800c00e450f814056044002c0d02c04105e402a25218424030590f51208070040d61516440301803c8100d81880400000f0400b01011600043c2c2400c0900180c00c0103680d201081c862540c11525100c0c82030080040074010300030944c6c0e010441e00c048070742205c070900c40c41c1c46400070030342144125210583c0b040840c4495049480d0107400221203040341c0c03191441c0c0070510340400d541d614840610750341185c01c8084180b0100c43c2c9a020250003022215940201d140950f41c1c16003116110320224a184d44152961140b0b103100340074545c1e0201078004205080e09180e40c540d02c080c0128940700388181d8010032660064050b0400f40710303040c4a510802d82d214101800c0c515114400a0040348483e0b040c01c00ba00007483c000411095485550b07581c07500a00e1510350580703020340000d0012580c40c101c1010002c00b095004a142020b060101501070050800c3d0403290080c01245092805800c4074080e9030340080107000d8540e61080725030401810089040c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 687729928 1250 687728678 687728683
    0x114010531051c03030b0402180d080d020c010b0a0f030323091e1e0d030e03070305072417150307180e010b0301090803061e0406030809040b010903031e02 68
    0x90300041c2c1c02c08040d1206540507400104101c2c3c03414000e0702c041011015032014881a48120020300600c0040c2080010b0b0314184a42481c0d0024054845141040800c442d4030007640c0c480c902525030390303450700d541080919000360224001d004050f20b080c1410700e90b99002d000c04c03c0250000c250000f0615040f420307030800f4804c40c3c404100092a860712241e50481c3c00e03081400c2450028012441211381240315a404621210340c640001c3c0704c5400081c01c0d030f41c1211040038005006400d801180000130010b4010030010380904800c0c420041c000540420004600a07581010001c000c2260888604d41c500368007081c0e00043c0c061000c1c800b8060300b2003c6881c002d00755002c00b00b44403a010742c40c0d240810950115454101200091005950400405013071f0354200401804100040004c00e04078134240134000c134001c0c0c0d10040d041c0200903645c005412112190300940e07440b40300203040190b514249c800c03c0a20102401c149030400e0442c1c41c001c1c181c7c40300e255498481c502c41c0c0381966006008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 687731178 1250 687729928 687730027
    0x190e0c0c1204060807180b0f0702010311070c061202030f0a09020f130507110f030406030b0a09090c151d130e060c1809130803041109040b01140105 65
    0x7100495507466554501c000c0c4018001c4814800094128401c00a2040f2070300c12481103402c028400381c200121300c06005c20380d51049000b00d0516986e144500310301e840c030344046e103d01800340c113600384420b1901d000644402d02512006040034810420042c450090301e41454100c03003202c400084210813840414115140b5815841e80b00446203074410b54458680c200d03510601c0d80c0d60314644211416020613030b4485001c0c08003c2550001d000c18008c142c8260322aa001c070703d0050401c1003090b45c40001c601100c6125801b5101300a08503030901c00506031031040141480c0b2881c00b291002140d40c1c494104080f80880d00b481007101712160b598000140d00b08122215090301500d00c9401d00c140d4480e100d5002c0c07071000000380451304142d8050f24050603075501c10f10820400054911403a038a407542a800200304944002d0200c880300000c0d203e1415440c07040e0301c103075441d5015504004041894400d040302d011704101e004c01ca048030b0100c07003e100180d0201012500540111898110032101c1074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 687732428 1250 687731178 687731203
    0x60b0a0314070f050d0302030f0d1404050c1e0904021002010f020f030105040624050309013308070515030919050d08060315010e04060605090a0902190e0c0c 69
    0x401c0100e1818030010a41400300c0e109040e00050b01580e8074203000101e0781902000d4096002400340400f280300d482c004103091b40c21030800185408074100f003070001030015281980c8550001030062564200240e100b18035182c1c4446203020000c00e0b0300080c0441c500140000d005c1c99481c002004c6142c002d401410381510900340541d05c40e128203509402981003445510f1266060400c000b5030342a03840880d096140078150001c4d030a020f40034045d2038650015110641030341d83c0340306d07541c2036050402c0d402c26a03102a243c8a04500140c2c24421100445604901240c1e0403041c41009103070f9076005c8481030407103650426601c0713582e06800507007840c02601c5c001c0070801c56130081d00c0810001062802010000c0d4171500070540350394003496030700c080c50030103480400e43c41401030040500403404154030074850240410025141d40c0030800107402a15218007083c0c9500c40b4030114a0440c006101d2418048580e005007445e01080040710700c2c001d0901b605880000808085641c002e000d480e1500d00b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 687733678 1250 687732428 687732443
    0xc0d1e2624060712050703020708120703032d0c110f030406110f0a02062503090503010b180705090a0312210207200a0e010f0501031d0604060b0a03 65
    0x2800c8450344500421003580351a20304011103004a81d442c0403400d445120740c0004e06202108050300f03050f41c041e4030a070070070fa00b0740c42004030000359020200005030020071201c070000d032038124900e00a402d44141030305880b00000c1c0410307061944815014030b410089000070303020545118484058681000307415403005940075010400480c0e103c0000104100d0b030807540c0b420401c030540511551038901142c03c0d800113411a00910026107042006007200300d6601180c205001c0d03040d52000000300d07410030220301240d0a400c04104902d8288240740e4032240682d15400300c80714840840d203050b88000c1000f002c0c080080b500c6202078a40603424405194440d00c01c40740d0030840310010701100402c02d60104d0a03c0c00f010704c034400014900955105a9020102d0560300e4000c90120400c05001e841040d0840c6503001c1c002401521101040d000307001d45032100d1021400e0100040580e494101d981400828000c0341081181000503660351064101c4000200f2074400d100081141401d688003600c5207 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 687734928 1250 687733678 687733681
    0x1a04020d140103061b08040b06010f03020d0c0804031805010c0206070c0302090408030f0a090b0a0903050d2a03092102010609020703030c110c0a0621110c0d1e26 71
    0x25038001700c010341c01c50001c0b99204540c008200c078100401c440040c03104821074041030a65000d0100301c2101801c5042c00350502c104140b001d021200d0760441000001c280e1828407041c0f68028000090352092042290642030410001800c0f08144010090103514000b500206014158070003c0103160300a01ca040542400c1c1440710094200fa00c441800746181c9004c2800c0541c14456403121582c00135280c01d20399580e000340d10083c01c84501c04d41c2409403c01c101d40303500100b40314005081c0c0c4130206c40201c841d0111041203008074a025081c00345841d01805001142c0060781980300c0e2082201254000300007943c00703c0c090007541e400b103401c0c0ba0004ca0108105509a08092001c07240d40c5d45070100e004140074110350360391000e00183d0b0003102c0007105010841c490784401030844141c0700c4066200300440c203101c040b140c1c0e040d031048000e00007041000c0c2d021001d100703822001421b480c0c0b200c0c401301203148020140c014213614000340812100500c0f100d64140307048000208090780c040740903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 687736178 1250 687734928 687734933
    0xc0b0c042d0801181709010f030f1b0c05060c0a021f02070c0b09100906120b040e030a170109020310061d0a180e0f06042909011406041a04020d140103 66
    0x51300070852007121490080398442c8042100b2000f0fa41150714169200d0081074000030080d001881e2188420345519291843e00b4039204d200c600209554110b6580c00032241c40b40e050160400c1e0014040b51004441004110f12403680042d03443e43d4020701c08488a0701310810f92581c0e00038890100000c0c814a4021000103069807244040d00380342e241510381e18080d1b40401c0d011184002180901008154143d107204680007280d440350400c403601520000d00d020020b1035091460700500701100000c0c075101d003000b40403021410241c0c0104a1410190b0850030650f1200329144103500520080000070303c0324540480f0701c0c956440700e030307200501012111500d4408060b403420003d800140e500d4280801807101c01d100190702d22060b810f640c0505032503102ca95030312803902140050600340f80e04040341600d0096100d280c0710700414000d400041c40e440310700000c8043c0321008018600c114941840042c840701068022012210100c40c0140da4a21400f54a8010314040c509000f0b0f00c0000303c004401c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 687737428 1250 687736178 687736211
    0x62a031808210705041d1317040e01090b030d0f02031222110406150c14070b130305010c0804030f0e0102011b020c18131502190c0b0c042d0801 63
    0x6e40b101010b40140f5011984101d9081c24416100380054410340c0c0e4030000440c00d450003200401801103003803440c0c45c0c1d89029403e1044400c1e000849803c0e030720008080c0c149800c200f80241040c117800c02641c5000031000294481c041d8059600c5540300e904002003020f405088400d0060355041340e6030b40d801c0d015042c2031300500812000c1c0c90281349040008a901d584604a80a01c00300c03d40c0e500c81007204540d0b84054180182c40c8100c203a100e42800450300004400190050386518440b1014030313441d50825a007550600c180c0d24007400280c000340000b1a80c04900d4214550446c14850011428000100e0040582c0b118040c0360340c0301001212112a13001c142c6010417801110140e004030f0460146102d001c2e0107039071100142c800e40742040c0026264032076040b2441020320340141400c1399803480e100321038400708081d800990302e8900c920070000340180643e0841c15028001e0306050408805400b2443d103007541c0c8026280880d414041c0c24064000c1501504414000340841800050b01701c6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 687738678 1250 687737428 687737437
    0x9040603021002030309011406031207020a03061103090d0903033507021f050105011b030512010e04031b150e0715021e1209010c0f062a031808210705 66
    0x5c041d4201040c4040742316100c04864015480100a01001000404151280d034000c020498221400e810000b010540c1881001080d00c25400c00303a41d2850042c2030103042c031140103100018400800003c0c030210b640010015422007080c51180c50001c0860b007528072815801118582c1c40164038200509036601140202c0d01800801d001900513024208e45030540311b0034010180022a025084100c0c00200c1d2482c2c500301e0701a040961400101000c0b56480c040e098120f07612040c0b803a0103110400da03214a12600c4c5403181c0120f420054603681d140186c018078020b056a0301c80d1030380d007407684200c0d0034040c81000388041c01c0c00c0b20404041c43c402075142c1e0743e80c110340383c180b0720207541b5a030810a0115100d101c4800d880c034010314082034500195030402400744c0664006101030a140c0018950b031103640c80801140410070320304409202c50b0320040380012041c004140c10320102c0d41c070404112001410f5180c2c8280103a440d194941c0c00c034001042c1030039031404c030f0100860034881c84503008002807 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 687739928 1250 687738678 687738691
    0x203010e0a080c0d09080a020103020a11060103050703020909031c02390d020d0f20011d0c0a03051b06160b09061b0a210903080a050a050912090406030210020303 71
    0xa40048a0113034054075468518420000560000c80c12078005601c41d50040c111006182088a05020402da10a2509109801c01c86040d80000402e1003945498150301d5072208108004514201c503291082030781e85516507210b412035401244640544c0743c0c0c01180000c0d0740c44a103111000c1e940f240011800c41c1100050605640110782c8040002d030b101040156104074191500c40103944480d0f0100ca2501180c0c2465110262406221032152002c1c001c0d100f0f0460340001181000f2107028100741005010008203100c0e0414010810001d00081658507110201e50441c40c0d000300d074800451094801e1400a0f10140581c034181c1041000d4101298000e0915004540c036540c2e807500020402c09141d10000042a024420f144c44107105030980c2006084400240e903d01d004c40c00ea06080e00c140803c00ca002c50038500130445000c8442c400d043e440090010240400e051000c90b07140c9410820400c04400e81000400341060b485079007025006542c0174040203801380c1c0e0200000e441e500159010f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 687741178 1250 687739928 687739933
    0x12091a0c0d20030d090c0e06210a0b0118050a0c090e060a030812040b0105010804110f03100f0e0f0a020a031b0f0605030a180308010b0d09050f0a0c0902040b070605040203010e0a080c 80
    0x100d80b0300c2c0d0781c1680c43d100e45409409d0f85c20300d00e0348952089034101d00240590301c07441540c09240025611401a83c000e05140c10b0b08481c0c900810040019035070300910b0789041c01e180800c2c5034203855001401e61304403660145010581d8581c2c2012604040d569007000c0c0c602080014075240740710000301c030f061080d40900305518403640c071030004451004040d580035080c824282c4c4400e6062900e610300d02200607008045401c40280c5070011403e4440c0103603804c00c5ca694800c0c0030741e071408040c40851a850072000c050540e050555001910704000b502014040450b00b242d07212491084854420190203d000c0b92175269a445a00a04076403044400c400018249140300800c03140d50a040b03140d9580c1a200d40e40644e0818810f075100750484601042c143e0f4907504682c02151085c80140ea580c4003140291541d40000e00b0800101d400d0741c2d001060703281c8104010011b2904000c00c4c1c80515500c04030100b015152400000c0c0508402c41e610340860040d4007000c410400e6070760060010306c161005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 687742428 1250 687741178 687741203
    0x8040504020a02070e1501091e0509090109020d080a0f0203072a030804030507051309240b0d050706020c0a080c09060607020414061c030e060d0912091a0c0d20030d09 73
    0x1658000c0e090904100110803102da034040c0485e140c140c40d02f6611404090000035200065000240244240c0609451100300002e80e182c1e0701d94040321115140b00c01d03000075803602c440c1ea03130b509541c50a4000710b0500003110a0280442007003025401000359004400c541d01c035622403e01a4540240e407050a04c541054042042200214040d81c0b007215001005101841c00d40004640c1c90441d80400c1d4030b4095641110140503034440300907443c110b0052004140042c01c04502915186040d1001031007121310020410461400142c0c0b21006801951315042d0760301c4450114890b8010100000e510a041210055030000c00d001c555200b20800c4600414101035030020804c8100c0005000d000600c0a145090396406d210008003458400130000040358030007503c0e03031800c0c07a404070340482c0000c946001c01c01c50f907403200c400501c2061585100034500300b103903d00c1d29950000000307500140034040450003003081e140040c000c01c0c072a0001c103903070350b413050008050000e0000c0d0600b150305a48819 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 687743678 1250 687742428 687742439
    0x2150c180f010e0909070b0c06011406030907121110030b0907030e0a11060f030405211201032a0f0518090309090a0f0f0207060f050408040504020a02070e150109 71
    0x112501d40d07440040e120b002d803d500b03600a01000c101c00504000c4144034026000a40300641801030404010340301c0500507550606201d01941094015070520812045c400c0c4425500302086010803201301180a00701e0800303a04e0481d1400c0082010355500c00c02d482003d8800300e1301a00042c030721490032502110750b5a2000b00a0f41290012400e54480740c2c00025024001107581da04d4104808005182a007049030501107038034039038001c990440e8540c010a80d0b0749202004040c6036809081c03009491420400f0082c1d116078240c105110260210019040080d82d0700100c426901241c0b07054111261441e44551402c3c6a146091080500801091043d10881041c1400880c010343c0c10b84003552030310007003d00300000c090010f0110100156501c5020581c605140b042c244080c895100141c0c841940e418038030212144250990b1400d070400c42080009004502224143c440494005232542c0c0e074000101d1810701250000c14408001b0024000c1c101840310000460480980e180301045813140e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 687744928 1250 687743678 687743689
    0x6020c090f160210020703020708210a0e061210050f0123070311070905011a03040f0312180c0f0b040b0f0a030f02120108060c072102150c18 62
    0xc440308001c40c4454004140142002011150b40044903c100e816800e80ca07400d20080740d101c5142240980d1104901700101c1c3c2e0144940ca2012202400c0c0141a80c0702404240e4148680320002c82006131040f180c09040d6600000ea40c0005010b685070448c038689525042d0644c0824016144101542d59140103558401e00e0407c800344030002c1c42040000c200500e0202e00c0c1c02c40e000440a21a100380e50541b0403d013040040c00801e6450000300300d552410200a4448840b80d0f4883c1c0307444c408208000224820441401d40319516203020710810050782510001000604070718081c140381c0300e2040090040141d000c4003a5036581e01001c0c041544ea1308980f07038034400c9202c0e0340b803241002e00c05001c02c07003c104050100c00711142804100483c09401610032684400301043e0452a583c0062059a404005159025008002103460194541c0b144e4403004654001580080c00c00040c2c03014251007405441d03e2988070100c0b900080c10034501c0e051840d001891500e94103020507803000300f640b421 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 687746178 1250 687744928 687744931
    0x1f0c1b140c1c0209040f0b070806010801060e060a0e040e0708010e0607080108190f06110a03060b03010515070f0f081801020705060904020714100b0103060e04030e0d0303091a0106020c09 82
    0xa1241251241d0740c25424130030007040c0284240e90701040420b615021a44581c0700740c1c407403041135941240a1134850000b421001c01070b001102002500f4401c030215447d044c040321901815400c080b84074141c0140068042d00e10032540e030381d2a0040c1d0310001072403201504004070004228094900d0f50750380d0002102d034002c01340b0842e0003c0c2e01c0b41c00000b440045445000c04400e01490159602a055803a004261202000d040700388040005001d0440b550600c54a0050807490020500d1549002c0008258802c5101600030403007002940d0000c109a25501c040c40e030398041004400040282019138450f0410740c0c040840030051507036040d6940c400300d410415a01d005040750b00b40016801400700940250004403a246103580400340a05400c01a06a01c18070200c400700c0d6054503c4001070075511280e0009104448110500000035008003030240d0fa0300301134500000000c4203040403009048190405042400d00248401030300318500100c1c0d05803801a02202c074064020700c00d02400050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 687747428 1250 687746178 687746209
    0x721050601210503030f0103050609120f1303120503180703031b080c1c2709020f27090c0c12130f08031b1f0c1b140c 52
    0x800502401103150a00d245101030345081000b440880c0d91910b00e541e205031141c030740c515641001001003000410500368030000060240401007198110300c00c142c0a2a5083c807010f01c00070a0a1f44905940740781c40000f10340200c02650301007060b0001420651064038000c513039200e03491020010325400901a4210707503141d0741c0c1002a0f01c8a010039540704488a8003155841001c01000c0c1801e6410401071407540000c0c4da0f14040760000c1c8030060501c1b4041d4140d030b0207103011a11800d21034140c54004004a4041d600003590b6940030700f90708a4140700e14407001094800c5001a0810325070807100b100003081094801e07050584581c61901c019029030143c034103203a0710040020070403122040241205114240030508200e859040300500e0480070742000360309500c0031a12400030065560f25442c030101c1034024220107072071302a51410110114400b10041d03921559007000c1c0710300c00d41da1804909800d030142c00d5007068914191100c0c134181c00d443c6a1a104521103c049440d045072110090b00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 687748678 1250 687747428 687747433
    0x901060c0f020126240316030b0a0e1501090623040b1203070516142d060c010b040507030b0a05040f2703020715050403150e010608072105 61
    0x411a8011600c1650000090321440400c21385100b070b00d40a003840c0381c05000400e183c640d49600c0741c0451010024030049103031080c1c0c000021420b01600d101d0400041d2a088240486aa03440c0d0101c0000b404030312008240c01e20802e05483c0118591084a0341650a52003080c400d640d502e01d04e002818000c1074032800c2c0c503104181401c0481c41c041c3d104a82080014040764403482c164540d0341e04642066400f03a415411803c461094900e00c00c0d1140c02a101c42c03d020a0341480d50b0b07001c1105944040071012000b500a921a140c0e09140420100b00d410000c0c40700360b0342da405840c02406080035a140074041e40c01c1c000426510360003030080c6000350202a00304d0442500d80420000a014031a0300d00c071740c5940c1d400c8403000c0c02e80703502c0c9002c00003400c0c2256010300030110318000b0314108403a0f001d44469441400b01c40a4283e10400f143c08898000410f492240f0507071410000038091649400320361361808100003040d40000c6a8001120052202c030800d1070108402c161800fa15010000d1154 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 687749928 1250 687748678 687748703
    0x5010305040c06050c01090b0c0702091b04030210031401060f03153f030302031b040b03151206070315090b0609010507030c0b090c092410120207110901060c 69
    0xa120313101a1102d12003600003c2280b0759503485400741880c0a60300201e04490003e030200541c204141ea480d0410118000601d04c54031b03402c0748a1045c0940c0c000203224a698100142d4024829000401c0c207000300440c41120796941d840280c09002c080141e5400300c0d090040780c00491500c1c181150449103448a255446002203001c100c54100030000c800700d28100f0141d030b03e00500d05c1c42c00000300780c0c4030380c9005030f803410101e5442141408921b100700d200c1d02d04000600c00c00c09120146c03600503402781c0728848076038690000900030401010918409200c0d800800664030380c1600480e40301c5020052509005860710310b0b240685002d54035180d0080c0040203000c1e8654499070040092900078605100d200850b070340d414148070340c02d680e2406a684641f10907012032400c02921307a04146100085a03003d80310400c5200301085880c0018800c14004103003e01c0c55014980146c40b521206d14119a112454904020110040005240602c4010001055a90281c0b0803000d0298000c2e03004502e4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 687751178 1250 687749928 687749939
    0x50a0f18030b18100b01020c090403020a080f0d020703031505042d06080a15060b120f1518150d0b0f061c03031a0a0f0501200316030905010305040c 65
    0x110401a2985051484a800096030020140211984041030500100e0303e172074840d000a00c1c2c24500340a641c070500b4038000307000c0020340020380d0504095000400c2c42c3c540c0402c1580e5011400b0300540f02242e1800001c4071070400d40c0c5940301c41109000c404a206509403070b8818401100c00e40c07450b0005a030031200326a0103480005808008085c0300c070001103055925444840d0030310300380180c22a00d0301c411420f18810700300140200d50242c10480100b07400d1094a0142d642c0e00d45e4090901360048040700081583ca949000e205090030901510030810a110b0000c100005001111030407015415090214000d141074405602ea041c1c00c81a004560348400507249440300b400340c032040c1d001e40e2a00320004241040c400d048201070180c1c500013a8825030000d011403c0c641800910720407014940309100c0c1e1940c605048040c2c420038607011000441c1c4071810800b1440b405618000c0d0703c4041003a420099021012083d880e00c00c1d07451038038039941d40e80190151071054800420110020b4810701a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 687752428 1250 687751178 687751193
    0x1e0c0901080d121e020304021215100b120103060c23040906050603070e090702010902031504060b0a0807090905030d0204140a0b03090714030c19230a260d050a0f1803 73
    0x800c08c3c00242446040c2c11541030051030112150790080303141d111031007080714401c2400f0700304005044000c0c4841c6844003682070350030265014040140015542c09002102e903210320764071f04850025249041d500c230b40b050f00402140e00681b2408412500341007020540307051150a6074060036241d103031050442c81d46070401c2092034009040d14219940c5000d1100940d500308400048240e55040500b4241041d003000000d43e0030b0700c0105401040085020892a180043d07604119040444001228141e624069007944200003c0c2088c2500210380499000d0502d003105104e07040440d41011110343d98107060aa03400110707005802904000400c0100b100614954117041c2c80040c141c40f5224803c50002d01c683c80d032400300001920442d24180b104040141840d141c142010703030910120313100c510004038901254040e4445c2421240c01a460000c60202c00101103144001903030903542850000030401e41001303008500045150b0303280e038411030041d4800c54610850103030150070381d801c685900c00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 687753678 1250 687752428 687752431
    0x141b010516031413030308180c030a1502040b0304050705040501050a1208030703020708030910061205030318010b0a03030302031918021e03030c060414010606021e0c0901080d121e0203 81
    0x5202c00c3d01000003d051001c0440c943c00070307510a49408040b81403002c032841c2002049404180c460707209a510b110260307000110b844082d68007800441000128804220282c081e070b80c004621110044140010000b000c02d07003806880e0706880401050703070b940041220708512445844101000711403604046a00e50000315807040031130074050701c0c04255942d5081c4a03441100c8903009500512491b12415242c1d000c0d41c0020180b058030783c03041e1640d0b61603441d20ba10014001c16104070402109603040e01081d00b080404050040903501c0381662420050302a43c401c9444280c040058076114241c41054820302d40380c8d2249441140d4002c1e00c980c01d205050000f516281c200c0d0b50600d01c0446c00c1d035070410040c040e00b80041c0281c0101d0500d4648a11210125204a5504d904041c002c1c0700b15940014005030328201d0205803010aa00b0701032880c1400e605004603a009003003400003141012000a080b110041665100d901c00c080006801049408100401da05203010810144589207140c0245 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 687754928 1250 687753678 687753707
    0x20a05040b180603040803090606031c03052508010611070f0b2208070305010f020a0e2209030509090a0c120902120d08190c020a0803040609141b01051603 68
    0x8030b04110160000074200c0d0000c642c22194072400108108581d0420f0003000d4100c1415401444042c0d022080000012001d044148c10980d81354000340c50060200d0900b0f01d540540c000034105061a039400508280003409440c0114003031b849100c6001c01d0024100044a041c800004011801d02491123465400000300d080640412090201c01105c80800340005200c2103004044c450301e542381aa0a40c0e44c584140071150703105010341d400c2c954001c3c5c4032030034088080f41c400c4032100360781014400a5030074106a482c01d510700a0588101908a002810301e0401110031102654600083c0000c0c3c440e44024000041c40c1315030503110303000d6150005070204c1d1008100030b02c080846582e042ca02080c0e94140c000080075a014400710490380492005000545501401880c0340310401039903651046100078041440080013034203021443d440140540e038018818a02e03400c46040b02e9540e40e03e4404807142d5080c2c3c031740800c011907005000b00c5013041200b403002140407443d510150707808403614080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 687756178 1250 687754928 687754957
    0x6010b04050409063b0114060f1302030a020721020706141b03030708010605030f1302010c050102130608060d0510020703020703050703150b0a2409080a0b04060e01020a05040b 77
    0x2042c0300e100c60905075002000d424944003a010a1707620511100003400343c24081c1603407402c1c09440741e00004160159211105944d10600400a5004200200c158003446109207201005020700d05080760000c040c0140036010700390b01c4400c801c94a4101c0004415080c016a002c00c10400c42c0c0380c020880b489a0b020380305040d0313080c03181d40440590081081c0c01c50040580000003007040054000a04901405076071400320b045180841058643c1d400241c040c502e02c02c105400041168825080c5540c1d00354003030300964640d06c41c0107410605040380e004140102e400c1000140c540c3c1011406690042d4004004009460032400201c0003035000e140c0c20307411801111783c08000719400308103036002140720b003407294502666111300400301c0c0d0b0005000d51040ca00d4000030068031954480d40700484600c4003a444448001000030340764044642e010000d10300400f40201c1c00d00070070314503403485070340515010b00029100c060014202e104152400010440030b000501072200514090041114410345 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 687757428 1250 687756178 687756191
    0x307110c0d030201020c070b160b0a1e05153304030807030801090f0c05070818040c21020306150d0624030e0c01091202060d0f02071406010b0405040906 67
    0x108081001e40102500540e40008001607045420820030300103041700b10746141041c1307901c1c08415000f124064082c009442c81400b08030b48006548c0a05591001c2e4a019500b0148412148011306002c5500882030307034620361404041e0506d44452066440c07549400b41c1c90024140c0c1190b0103003805175414014540a21004c4005a280c42c01401c1c201e000361100070996150529180c2696148040d400c4c001d07083c110745a0005030058141c0c0d9050390f1020102d0781307400781148010720242021b49110f90060410007210085500211050fa44c4032016603140c034400105014801a480b003034a1782a00204413600310314003071180701e020300301c11422080041046a6205d02902d0400c062800c09141506e209440782140d0360984551108019030101506d02e06030700400103090807050b03100321142e621020700701004540d0b90004580c0d43e10038841041200361740d000841700003900030380d1085902c00204015808e01400020321107040320103402120380f070b2074104410303c400340c804141d01310360345900c078039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 687758678 1250 687757428 687757453
    0x90f0b0306270a0f060e03160b011503020715021c05010305240403080601050c01020f12060a051503011809061a09070f09032a1404050703050c030711 66
    0x25405a503035034a800302c654150000005000319150a0a02a5401482d50000090302c43c01d80c0003265400c007400141c1140300c0c0c2840c605512030007004492034810081a0000c000224a000e07043c0c03030790209c200c9e05961902000358100d201d0910080c0c424081c8500c4c1403080d0741d8035002050f080340c1c2d4424207020700387c2081c2c48205a07030081e0000c032801d401c0006107800d0002d045c040c01d513401001c0110340c0f0705428103482c0a865040060300090400a00040060100d502501100c034070041e41881681e0791081a20340592405042d030791070307101e10000341000071246820301c0d01d0310305c07107032220401450b5034648090401c60001110310f04203002c1e210b520303810200b40980301d024050b020701c1c800d1100f024002810400401d070b00030709141c2404001148051400d5200c070355002a0780c0d0200880c008202c2d94240701e001c12103101419040f460840401003100c05003550740028106085d0360a2000c1d44a450303007130f026a030007154550f0711544280300140c4014410203600c80340e8121613040c0c426480030f80b07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 687759928 1250 687758678 687758683
    0x90c0f150d1d300901110f0708060f0106020c010210020313080403060218060c2e020a05040f081216111e0a080606060f0703090e0a090b0a05060a090f0b03 68
    0xd080c050b41e0360032850700925059804000002d440300c1c090200000824800401d000e81d000701203045042003d20440005946010084009040240b108840703106540d241c13599a55902201c0d12481c0e0300d070950000565500005607aa11168141c000c0c01032800c02640c00360007508002c240d0307011020040000300204003454014800b41d4003c290140c0d81e0b4040340c00710f40440d100490014003d800810015a02050100e0440b180003600c4150143c140720b0612403803600110000000d5605100142452a0b0350300240100200c401d00c1a074404a19550500c40d03488030799181204500d401d08000e5405010200403903200394900c03a65012860b11241400324102c560a0001c402c24010702c080c00d000c5501e042c1c2c25580051072500010b0009250050100300345000d2940084409071000c40c60208150140100101401e414000e418181c503010702d110740680401b0a00ba901080f030300000c81d10300b83c018041c1520070344018107c100107502d08034940005250f01c03465040c099035a03486030107056409 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 687761178 1250 687759928 687759971
    0x30f0504050a150e0d17090303071b080706170c03060d0b01090213080604020d0803100801090f02130b0906100504030b10080f0303070806010f0c08070b090c0f150d 72
    0x3066203c1c1c83d0183d100384058501c1c548141081c0c8591020b59a61001881d40c0100c1d01c4010135455a25484030510800709103540901d610042403118018100c04080ba070b440e01e00c900b1036200004881c4002c0c0e403400c042d2030800b0b60094024900380d81c140000d2680b6051401103800440140000154030480d0321404003410081e08802c030040e80000e594003101400c0020040070b40519409486503080c16400a01300ea000340b40020400ca00c04000a216007460040364401402018028030a090403450144640341c50848128810040c08444440b903103a82c3c450003030050401f8040820944804d0f0400c01500d02e1280382008100080001000145203421014018144450798522044c2002c0700c46040021050300c102c0781c0c6e4001e108011720154070021a640107823003800c01d4104c20440103001c540013400400c0c040c01c0b0150000d034000403c0a4010400d01c03030702004040c0c840154100e005c0001034440c0c1d036a060f0788282240c0e112808904040f008020202c070044000074284044101e196030302ca003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 687762428 1250 687761178 687761189
    0xa1b060906150902040b0412061413020319031b0c0f090b030c030a02030a030302030901110703020c030106060906020d0822150b180a0207230705010327030f0504050a 73
    0x1c880707103a03404805201e40e00070007a0800c503c0550829081c01049000da020701c0c0300d281000711000c2050000e001c500d9004c0030400400440e4119a4540003600c100d040002c807808a0081c030445240c40310040801c2c900700d54456041c0d50322820b21038180310301d0400308848a004d841500d050340000804c10b03140c5007201c1c004d20032010049001c00c052000c160402018920042c083c2d00701c290075000581c0c020034070403426030740b5040042c2c0b603070ae9080c14035004028440012154a200007004401d05400241d071a804080c210300900c40141c54520459012246202d9400580d100710740c2c0002207801f800d8690b40c00304650050304540c541c4640c440080104814007911320804200000034079500c1409000c00c044c1068501c84100840c490021003803007001401c00380c602c0d03404100c98040000c410700011842c03854212401c10202890b10b040c1d121510351207600d002c80c1c581301501944250792803140c089074100c460b8446400866803405c1c1c1d080b2100d14180020403408200108141d651024070501404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 687763678 1250 687762428 687762431
    0x10f020301170f0303070203030c07060603020a060518030106051f0302090904030f12020313030e0d050a060f0b04060b070210210213080604051f0b0915091305030a1b060906 76
    0x460942c40c40d0502000100e9450076400800403c500c0d1a0000300b241d402101e541500756540c40c0764241040203250b6904000d52145641e03200042103507004000d0440c01205220301d18040f07603410100341c2228264803590b0b40009006d03141c171442100c6081c200f000700c000c1d03040c00342c13410380d03c440020120b070400c40c2c0c11000f04401c21199640f55500540500100c002c001c4114a036081c804001c40311ba903403042006013001090301e0300c050030351540c00110302c02540c400100c40003280d640c50450050300b143c4140c1521541b62840000c050700c1c0501030101200c110030344580c42c211050302400000390000c11400280700c510a2000c1c86081400d5084008804001005880c0d09540900d0f03000345c0d84070f5000340c09035403100307040c880415400311303c828441500400c09540151581e1040c3c0181c4549142960f2243c0c0b042d0802aa10150a14900a00c10b0032103201c00719540f030303031114568135101b0440501070394010f000340341035503004408400b8402c03610501000036054540e14141964070f1507a0496915 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 687764928 1250 687763678 687763709
    0x905070602010c022b110f0a11010c02061c0207080d0b030c040603080318070f0303110f1603080310030f060b030d09150e0f03031902070909021e0102010f020301 71
    0x15428403c141e8626610b101038142c4542c0031043c00d506402004403004100c601c00b1038080054090300340003050440c50800c6c2c410614408016a032612000319040c4e41101c00c6482e6200158030541d4103826495005102d141011840100900600c21019074a840c040e820489840804e41c9000074000c104007a20020610808040615052504c4100128003980c244070303041c0700290520043d01d1740316540b400c001000c42000d01e1898506190b40d032210b01ca2100504021007490742c0880001821024802210030940001600035954141c140602d0440301e0302030070500014039080000c540182c91910404415078580d1100340542c0f14101c4100c031030a5903903081180b98103043c000b03403442002e035040010409280c015070080460300c1e110500100701c01903405685954800701d0940008030040c04481d10341510b2800104000e804e038610030094071a030f880015248003540121481a540646a01d000f5030309003080e4031480c111880440e040d9501d40c181c4908141051028600034a8240d0343c4030650b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 687766178 1250 687764928 687764939
    0x61b190c0f06050c0a090e040b0105120c120307051204080d050f0408031b1b060a030b1804030c0308010b030601020c040f0b120304090b0102300f030703020301060e030a0b0a0b13090507 81
    0x400310f07645c42000f8001a070f01c00c0101140c0d2703c5134803d0444800303503841050410400b03222030400e080050115800b41c400840f004c510716000010340806449101110310b6000c81e0b1014114600817413155070442e51008444d2a5640d210718080c1940800b40e2400c2070800f5200c0346543e085810914402c460015480e180b140c0b500340403c0111940d00c0d0004030301e00140d0614002c030300d0511490b0000c00c289510391541d0849902d50100c1002c0c14490b54806030024102490010500c0075000015400a0303c03200c00861940707901c00c100ca00960703050300103103040ca00c07020a00002c0c0c1910700b103000c05195a40f02020450b210407019040310791008003d90740e100d0900251408807001000840d04650110301003141031104911001d00c05c060000380d0604541030038050200c01d1003900039242c2c00550100500400e2a01a0055416601152500b48901150704141583c0d540481e1016041d59500c002240c1c0076109a4483e1600c20300140c81050150b490800482c160340302c0c600215070652150004101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 687767428 1250 687766178 687766187
    0xc030b0a15090e091002030c121807090c110d0210181509050c0d11011707020a11040605040e1f05010807090e1608061b190c0f06050c0a 60
    0x1900724184006100303400440014005100ea000d5080504a604081084400100443c2d0014820320006560305e2030001d0394105550002d84001d40c115400301d02155400c204c4650900b880d120318801441102d150080410150002080c02028400341e04241340e003001051105140d1100290000c1603000b03000c0c0c2c816800c460743c200001548104124240300000d074003c2503d880341070b1085002c07030040c0c45810128203004036200d90a40c402c8202104204200d9010850414504241c07102d100c103941e03694403120702c000d00f1a05540140c001e60b88410004205582c09400480007400014509444101140460f03600320080300c3c20350b100112100c8603c3c4101c6090300302d1100740c5028055940342c00c0e0320a40d40c400d60700034141000d440303038181402910200b11040780c00c401e04020003036461341c90200d0341c4c4554003a00d13000301318040c01c8a551086050316045801d03029101186a8013102d00e41c000321504116050125100703802100c02001080c1d49015043c01159041e02040c1c1d100d15061001c0c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 687768678 1250 687767428 687767449
    0xe0d0f0b10080105060f060c010209062d0f07060c18080f0f070b0703120207080f19020d050d1e0509070501080112020901030f0212060403050d0b0402070f021507060c030b 75
    0xb8080c1c2c141410840e00380c440e000700e00c030094800c0c3c420a45402e5201d08150190003858401d40e00880041051806055001e844800304042000100500600e10606132111302c00c0c48194190500d0400603580068030030341c40038000c1501450303c0c0ea042d4201407180c09020f110399000e0327440c0b548954841040341109008511061032910001c188c0f0321302c0d04000b00c44901482e14080c1c240b10b4486c68200410b145a0102d600700c60784966240e6030b5441c0100c000d505074109038807080310f00c62102603203002c40d4000211610340301216103481741401c0c491445503025046907009644502c528105c1040704150501840c2d000d20800006440c0c4281080c0c001041410b05a00c030040d8510000c14100c0544c0355036401a0540f500160003040c1c140140c008a1198903007031090b00c4052045030100001c0c150700030701521807940d82c00750510080d142481003206034050001d0140c0700c0341d0b0080c40c040c0146810311048c2c19001d076441c90759080c8069030715031208450121030280c01094072480c250100e03203452100c52 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 687769784 1106 687768678 687768689
    0x609010303111015060909150e1305190614070918060b0c07090501050f061218160806060111030d051909030518060a020d0e0d0f0b10 59
    0x819100c4d00c54850040020680080442c2c901d03918000c1c003081001c0d0344030303c0c10380c4c0e400c2468082200a000c5c00000b44c074010000f07200000351007440b1102410114125000004105041400c02d03174411004c10760b41003112200f00100150003058000c1617500168051090008011030070000340501d0700807403642500440c3c2c2071400980007858000307449207820188413690341c4200780b200c0c803a01c1032034083d4004030034021740e0501d42c240c1044642c0943c0340400d228041080302140c1d030820a403149070b040642507011091080702e01c201301c0341c3e402c204203103090b446c80c11694500584038004c1c41484014552100c012624242c620446400302d41c9104404019129192030081c2c42a80007444a540182c1002003806091404c5001d854226480b500508003403200154101c1c0d6410303501e13000690014201c43e4240214014401c0d0a0851307108981e030b0041400e0411070084140c0465005 = true := by decide +kernel

theorem cover : BRFrame.Cov 687589928 687769784 := by
  have h0 := BRFrame.cov_init 687589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 687589928 ≤ n) (h2 : n < 687769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
