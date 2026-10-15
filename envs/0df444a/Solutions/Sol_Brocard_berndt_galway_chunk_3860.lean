-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3860
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:53:32.273236+00:00
-- url     : https://prove2.me/submissions/8f5e4b99-313b-47aa-8f6e-1a6e16e62229

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 694064748 ≤ n < 694244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 694065998 1250 694064748 694064783
    0x2060a0923030f0703110c0105040e070c08070609060b0103050601090f0b220f0314030f0a1b0c0b090a08012d06050616050c0d08090f0103060509150a0b03060105190c 73
    0x20346da103100351104016200e003001d400c401150280624055610520ba2403c08102c0c424001c1400c2903d41d88a0b03011542400364940b60942120040c00301582e40681f907030a44103813076905120390384c5d200d1001d0901160a030f0078101c564071881b8490140000c0c004002480703079248c480521030410702145c280030010703074207880d1071011880250500c0304441810090401441d002c90201c00e03100d07542002c40c445400c22080c5038084909240c2e84943c0507882c140101c00d04041001070701c008000c3c2c565000384958a0051105002d032561450740f0018841c1d2501c200903080c00150710a107400030003088140c650301603513845154020a015408103a210200140e20560b556a00c91166280d40c050800d946107000070400344509040e1b0644000c3c1021000c000c8403146282805030f9541402040c940020701540750310100703080003c00e072010314079441e40c070119450305d103001e40042000d030040c10055410f509046001904038014100b0942450381d104c1e014241c42c41c4181300d451040340d0440d801d08803558005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 694067248 1250 694065998 694066007
    0x2030702011413080d1e0c050a090e160503180601060c0c0806060d03110a05010f05040b0709080c06181c0606050a051507081209010c02060a0923030f0703 68
    0x180c20040900c901075000942030300e110083c2040468000c0040c03031401244810620080204850444014219001c00d403481c0700c06204800e61012503460321940d0700305640e4040c0001c80c0c0c60384846d035a10035030760070001c4541004407030030b4143c19181801900c03a00e40344510141d03081c20881a0f21036128001c000a82d150f4010616003020303016900052080c4d4440114940703e40040301d1240e00007140030380d4400040c1c40740207a40900e243c12426101000420b544090030344018005d091080c07501c860034030003848008550590469428100b1524581c9070424090329101c54000f018401d00f404541c038a895442e0b03002060300d0980090441c55014070030b4080c0d10458011603800e03a000b524201c1d02043c40d00300000d8407410740340000c081000552094644803820740c01110225915401031024642011400b020107000314100400801c0f00c040400000340341c0b00e4000c00a864450601440d10042a039418902d00ca81c0d4540071008451032510310001e1451140d0400c0c4012440002100c1050580c030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 694068498 1250 694067248 694067261
    0x20624180c0403021003050703050c180906042003190c1b0f1a191a041509150305240a0c0903051204090b06070201020616020703120503040506070929070203010203070201 75
    0x220703101001a9262842a05883d005000e503a2010450b41c0c0c0401460780303403400c0760b63ba000750f006202040e0b000c04111786040d090383d444001030701c602021050108003540104582c0c818041c5890400000600074030003000580201041169840c0300c1704d51205000c4060700c91402d10303400c81300045030260301c0c00c0060405541100c58100380d0150369079860401c0c10340d005048004460040b08240a04a40200001410f0524520364414010403000034150283d009082d408110700c80101201851414400c0c1003040c030302b40d5181e44122800c01c001c0c04030300c0d040340c0d150005454036002400b441080b00640744140340b50001f078441d21550244100790010b540081c801d90761824000c0c80000aa0b4040c0310381342c0071780b150081c0560071081c00190894041012983c10341d0091048640351582d035181c50000c8009640c1034000144000100710600004204054210101c0c1c500301d02c41c9443c10343c404e0560750300801050228000e80e21000141041c0c8800e0310f141903001002156a420182d00c0a8020b008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 694069748 1250 694068498 694068511
    0x903110a03171f060504030b0a050103030f050f19090303020f031201030f020607050714040f09110d020d1e030305160c030f05070b010b0c06070206040312051305030a020624180c040302100305 84
    0x3030315000101c0309c0e103050081604903a4035031580100355031070a0f07041d0f03599001000c40821800c420f010014520747d0300c8240d8070721100d054442c200203900b0350030700905020905243e00390300e51041100c1c0d030b1400794100078141103035002130800c1010b1a46100144452103000310250080c444e5000200c1d0940450255070308001c42100c0402c02d14861f440108140c074070081028061a4110644d1000c0341010401d54165a200030300659645589a80f0b8202803603c414540ac403402d00041d44000700360309403003070f0340d041070119007a030200c46a8104004c1c208440b40700c00404002c00113a0262819001d0000d503100d6690007851183d1641e1a6807070a4038542168640102512440011a0241d0700102d1214020b039016510280038020707541c000070103003001900303520780340030260802d0000c180c0500142c41c4203462075001e08621b0030501d00c3c9031034010000900886084508059003c1c55407911030071180c065a810014a40b0342e290200242180030704d034400b9412049144407c100168180c3c49a842441c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 694070998 1250 694069748 694069763
    0xf03180c0409050c0f0a0b030f061003060e06040f020f0408030705060c090a12290601031134050a35070809030f100903110a03171f06050403 62
    0x1280c8000c00041da103280902400c580c010403184500d03402c0103c605c00052001602054056964110001d140e13401251845032a080110502c04149809032041280440924091101900b0070704a00003942d0003820300c07803103a0750b03a6071040003181c050b40540d03513090005550191142d580b040c1031605c0b6030040f0401c5413035000300741c00078a1001c2890162460510098160b00010341002440c080040c003001c400da60b4010802c181d420010003441704914944010080c810090900800160a0f2841a000781c2040c000a22600304c0341e09407000310842c0341d4048034040102d5185540c6520b01148003080250640c0107441c14081030002c030074021070062900702c4910b041200c1000941c0246e102d6249200900d074001c001d19401314400c600030344401c10005042d500c3c490402c590305850001001c0c1d1b825030103516401c1c0c80042c036070800303070002d541c100b0340003e0f10701c50403a44d42c01041c01034042c208910310781c01c132030208466030341503107150804980100c55003950b00d4442c0e0000c3c00c1c541142c4070440b61031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 694072248 1250 694070998 694071013
    0xa030c0b0408010f1406100c02030610050415063e0d020601080c0102030f07031b05010518010b090f040512070c0512030a080c0306011101090f031806020c0d06020f0318 74
    0x500a01c00c81c05c1903140704200000030740740c103402c001401104242400411000c103c0e40c03070240c0d60502900d80280c07590310000b02e0107841d2200f403100343ca80380044826551800d81040042a03008074032541000f0800440e40c030040150003003290b0355102600070381c207040501841c40d203441000141800000040d902101d0b191b80ea00d1001d103686003000d03035859006030024400d0441440c00040034107a20340c46801c00701e8011070340c40071040c400b6072940401c0d00c5030380d101c005001d8403407424480c1c03440518545009001c1c1c51240404151500e0f03014004400c15194980024140b10b07041c04010f085440e442c144a580301d6243c14030300c0c06190917000c0c2d180310301c0f4840d410084844000040302c64030302c6203498400980c0d41d0245074448681008254906124032481030300d01da010203200b1160041d00c11404182d074400075040040880700c500302211803500c003440081c07000c0303038002440620200c003ca1340b2414280440c41c21001901406000070940b450100600085c035141c4514800d1030010b0100300c8005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 694073498 1250 694072248 694072271
    0x7120812090727020903030307121808070b090a140c150c06071413060c0b0604091703130b2401090b04090f0e030f071b050901090207020a030c0b040801 67
    0x64000314450320a07102540350410a0302803d4070b004186890006500500740a070307400c040b03401c40d07104451440024240c400061503810180c860708548070407805071481141c00310742e81e950362881b4208021b04407040020000c0d40c0e640c820410b01a200340e0049812040c144540000d590b05c0001090351407040d00c020a01c10348040450382580c031000c0e0f8070401020192504001600c0e01480c83d076018003050030070040924001c80c40300c4c500008050960b030b15201d00c102c0c1d041400c18003601a042600c124241011074000c00c4420f02401341035103030107409640d2a1901d882402130040b0954000f007041042008000c20f521009085038603800603002c5800d11184090b004550f4800340d130245052050301800113205010007a48800208500900b001980c0d18060303402c1c80c40d541000c0000b1010b03c4000071440104003920b091420b000c40e51840c0c030201107041400058015005009103406035601150403020b540d01c4028450003150060b030036500d01921080000443e038007600490180c0d41c20140251071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 694074748 1250 694073498 694073503
    0x607080d051608070e0f1f1101060305030436020703080a110412080f040b2205130f0209120120070b040308060303071a07091202030c120712081209 65
    0x20002da680d450002c242e41e103441c1030390001c0700320202c590080c0c41500402400d441d00c1081c2c201d04030055078010418903564400501010f01158106002c0e41000c50070000030788008162029140510205141c2042c0d08001d16610307491b41c13888850300d480c1900318503212401c0d98001e10516019541d00701c000ea5a006102040d070740024008031030750108010811044030381002800141d480b0300800c5181034014980050540c00c9508802091280000c0e1900c92000da000c080c0810100c1d255402a054900800515502952609108826120000881701c1c11a0381d0480d00180070003020042182c00f20107945001b4030612003100d01090104110b1046d0035825415100300b25440480d0045aa803966030072101c00f40c000d84400e415200501400000960800700d01203202c0040c55050030a01c0c0961005001c040e4940c80104081c0e000340303005000da03d01061001803108181e490301c05140b9a05034191500c4416403040c0c0c05141c041c0d0514081120311001803140da490f00328240340710740726048100e4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 694075998 1250 694074748 694074781
    0x1a0106030b01090e10030b0408030a0507080403050f03060103020d0e0c130e0703020f1503180607050301031511090406030b0105040f0b01020d0c0305090907020d021e120f090607080d05 81
    0xa000c943e0b03012007049031a0b461502e40d0b0b4810201104003601030303526520034101240c00c0d1012a10140007208020618240788111903005105240c034400e18101510b005d040e510810401c10301d14640000014556400790f0101d8a00c8800000e0800c002c040c002c0d003050b161101c20114074407400d8181d070b050144461a004d04c0e2008803010003e0602c062031582080b51000740380c5409034001224920300c106d000d00600c0510300c00e45800050310500540c068619050010007403941c030900c441480140301040c0488048140702640910004000d02440720743d144900910078503e91160401d20040200140403560504030384c01a54103000203030f80c140319002690402a10240103a00a0751300001da10b110700f40034402c55005e824400c0ca002c4211000ca40d688004491002c05640314000034581c0c194104a000f060809805880c80c80c0545400d03001e444050f90038840700c1d60134001c40c1602c2c204c134200303007100c0201c200200300716941c8046103007c2c0c4242c0c00484404011a1130400050040001008080b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 694077248 1250 694075998 694076021
    0x12060b10021e101118010512220501020a0306170c010509090a090503041d0f0f01060e030f0f07081204030c05090405030d050117010e0106080a02101b1a010603 70
    0x92400440120640203555411a030041c010f104050743c080500341c95100c0c0100a0408001003590f4031010405403a10000e1807820700d041001c1009108690482e00c0300c0c45170003141c0102c0312103509012041010071030f9000c0d00003900a5200203041c1c14250f402d0340c0103400b103444086150390300301441341c01d07140c6445140e104240820340811842400307190581c403030350344400c4501000403030301a540c40b9145140c2203900f221401300080d20b42441d8880315004c0059010080e102d00d00102d1400341507460301404103100c1d01f424011100003120300c50780c0a0240301e2003805603108440600360300030304107a5200060300c5507a400d405010340440a241ea884c04560a4a400c006d10200e01c03407900d000d01440e03110080003036a01c1e00051124070b0260480740155402840e8034030101ca400c2c11142d03d02404c44030083c000202581c9002010060090f002c07440c040020b40440d0016021100010240c811008208846c01070040c0e5510001c101300c60804c200200d02c0c140c02c01842146e880b0b220036421642e41d400f45 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 694078498 1250 694077248 694077253
    0xe0c0907030b310605040b0a06050c030c062a071208060f06180a0807030c0e040302010b0a03120306090b0d12020325060c022407170112060b1002 64
    0x5120a0290b0001e0a503100c0c0502400c40c02d154003004003642e500b80d040c40b0410003000400601c1d00300c1e458041c0c140038041c211001c0108040340f50000325292600e1041000f840320110b507802c10f005c01401035076a44a0710320285c41051070031902062612400700341a0681c21003103d66030b066170a400341036400082e032140d46e8680950f00100c0950704240700402c2c070340d0300ca41c0b0040e4906164855030003a0440c8003003181a034141e040c40b54104041c1c4009a00840c0c0c00398009601000420146a10b030401c503185403079501e400b07407200c0c04d00b2409840d4140c04113401407103060b000410400025241520801c451341c08000507070b02c612409080d200c50407608c0e41d2007504205814041070115030f1010b44080140112860200744d400259041ea5800b000f0140c41800301d04103c0502c0010f0003014203041c0d46102500381610300c0c6c03000002516402249807103481203040060003650152135002d4410020301c14a99541d07a4542111081c00030517070040340c0d850300b000b6242c071050420b0044d600200d82190003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 694079748 1250 694078498 694078501
    0x203070203031803160305010b0a080c01090e0c04050a03080304050c04020a080103030806210705011b1e05101a040f11030105040c0918060302100c02010e0616021809010e0c09 77
    0x14103d504590400003141d050041d600321303080c94200c1e184600010343c4500c0001c2000150710b000c202c4058102c7d0700c0710307240d50400c2e00400c40390383c0d12008010030385070b03213141041141c2c0360b40b089007005004541109422420315440031091040c1e10780614032540c8103404449138110100288010707806800030171004564032070010703c0001e015000701d40d0311401c09001e000341c00d00e83c81b49005116007945028202c9421400c0240b1855078000400f2125107a01000d920a1424039900c280b0001d00c03003500307d941c43c8111403100301044401c1c0000604401e00800c14080040f05016035441110103646507446185003c0c1c0d0300300750114a00490034840c08000e85281507a29000c18480030b0701ca41c100c01c0e4104418404042140050316105000081b0340c01070008400e81144148030307052221980700b0040c041c42c3c0344640010317a400190390180300000d40e40d007a1240002c0002d0f03c3c8107081440c000b503001d03603514070200b0320425400ca8184584041c4000780500101607a10303607140d103070500c043c2d17400c03062410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 694080998 1250 694079748 694079767
    0x32d0509061b1b0a02040609051006020a050c01032c2d100e0c0d0b01060908070e0118020702180402030d031a120c0d0b070201050a060503030706090501181401050106020307020303 79
    0x104403455207030301400340c40c05004c041d4002412110a42c00c804d20842da2003051068852075000c49070060600c034002460700c1f00598a80b640d4800d01d100031241010303240c1c0702d40525074010303035100030074206400d048000d40e603c200b01944c1c80750b107107115080e2a5944804100700440380c44007491b400d12101c1001e08103210024591002401c1124502000d62050428058880e01d80d00d0200d500280074080b504455410030300018990200c9603c034806d80d9100031414010b00c144058041c1c11520650800018840c101084501030b0250500182d0701202000304d41050040c4500c0c0548a00d01c220252026440403403019800c660640810900b054001c10040d5520700b0051906041014148112101c0b4205880000d10b100c440309030448070700c28070f0000d00070115024042e90b03402c01c0b12044144200c6060802182e030728000d04802030074a9845400703c405000003075100c0e000d10446a0320404201030181010011480751215100d03907903182c000005500351005c4243e0b82515402070141d460141e142 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 694082248 1250 694080998 694081027
    0x150c1603080d0f1b081b03010302010f12140c0714061012060b0406180c030b010c0f1703100f0509011a030703060b160201030506010e10032d0509061b 66
    0x2910100341190780d0040e01d02040c5041302c42503014480741e602c103101450a0114501400c10190781c0c865824400c2c801800182c0c1c0040f108100b5199600d070011040e94103291800c082c09c442000303040700c803a02405100744a0318403001440e80703902880e890301e10b0049802c40c042c1d4401c1700311804407584070384200500554036070700040c080300350103418080788a0030010001003c03226240d0000c81041c944030300007111f0084601a0000c0c07820681010000c0404403000030b81441880d00e070052014404000000802c10b100494803aa046d031003e000da1249081c11112500747ca503030140080c0704490000c0080c441c81c040d48090b0503140000c6c0601c003620755480c040aa103410183c04d042c00d0549402000c01c1120102010b44441500680c0c0244662074500000d011900d01601113410000900320b01c05040d11345003181c00700600c6070310380050032078100ba6520188103003096050584040c0403007a603824403c107400071405401c0c1c5806480203030f00d5440c40151080d0540c0b035101da002c20140280840d80210713 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 694083498 1250 694082248 694082261
    0x60e070e1e13060906090b13090b0103080901051306181e150908060a09020901061d0906012001050108010e0d0c110d0803160e01020307021c03090302150c1603080d 72
    0xd00b00101d83c00d13031650789100c180d0398141c0203020b80666410306e0380d01313515285d11a141d10000000342040350341c255844400d07020505000c060041400003606e20b00380d0340b1603000c448015507070801c0c2081c4151603000040010412031284c0380c2401240c500402c0e8203c40900032800b4006800c600712080f03140a19001c0001c400140c40401d05c401400002044102801101c1c803030107035081c0c00111601240b042180810061f042101007080b03007015960b10900c04848401042d0080342c8020180e5180740041b6000c803a4640c5165280311500050060440150030840c141e03940300009004281400c840c0e01ea0321b11744240c844002600340300b0b01d4000319901c0ca40c02c4040c40300181407900b464020343c5070700200f68003c1ea2103031403070300788202c155004640c0840311041500091019615041307868000a081d01c41980207030119aa02c80c1c1d0f004101070140301d00500569001d040e406100d00b04c98083c0960f5088003509410134051080401e0000070720012100641303601c03d00d0300381080b00b20700100000b000c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 694084748 1250 694083498 694083529
    0x3010209010c150905070602070501021018030305041b1e17100203250203090a06051c0e0a02040c091406030f010303120609181106070803010302091504060e070e1e 72
    0xf135403003440b800309009001c80d070041c4c038a5400030000549014002880c0012000b0080902441d01295000050601144121243e05480c010a1a0700c46042409510034410080c5a40700c0c145080002c0e5050b1050301c030101d2004503115016038a5a400300c1a80301c0c61306242c2c2c90099003001448100b6420141c0c003454000c1141d140c1c589810b1342e149092080258541c07800e0016a001041300941440c0070781c0c3c1c2201070b083c1c5240450030300b41075200002440c0a84280019119100c92862541c3c03c81001000401c940081083c0600c80a003c1c5c05481140702d0b00407400d084100030801415070411004a0740102d11440b080310300c0d80e00c2c41d14221480009082c42c2030711143c40f8540001d11200380d0287d0800008040c20802c02c0c0c40c0e06141250400880340d607000d0085206100b00004030304e00c00c0c1500c4c1101e80569000e0015569507809000f01d0017410300d1540c0c085e16000020601c25100e0805501c14242ca4403900c01c0c000f070410402000c0e803a03000c3c2c00000d8201c00b051032442804c03c60b184107000f01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 694085998 1250 694084748 694084751
    0x60c030306210706120e010c050d0e0a1b050a0b0408030d05040f0b0c191b0204020705070e0108150f040b0403030b010c14010b0123070b0612060403020a1103010209010c15 75
    0x55200100070f0034507225600413800250340d64501001c1003494801e060f804006034008101030002100090042d01810340300350780b02a0381d2103864041036400d00900103882d0740507010070007450b000b90f0b445003c20000d005d500d0098140c000c021a00440000486080e5201c0c0d0b00214140100903403c0700240a0050049030b8a00028000c40300042107620606d0007224942c040a440e41c0b2180d400101c6481c0041803041046100c150340c41041c2ca80000c0c5c5030300b580e010f030340242e554001400c10a1070060640d0103014412142e2000268200d004079034444807801d001e02c2681181c0310f04201228012040e01e001e070a48002d240480e0009000340e02c0465021011b042c40c402c00e0b00142c0f90020341c1514542c610312565120350742117030340b5a030040c814007402d41c1040c0001c89021002400c0304490103031400042503a02e07a030011601c0341ea103000380002180e441078102e41c06071900b0301d0001d40f2004080130454000e0710b0b03c06242c98031318040c000d60303014032810303500c801c0c4208158803010510500302c03403602e180e40e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 694087248 1250 694085998 694086049
    0x20a081312030c0b06030a0221011418010c0f05030621030d09021206070f080907050a1e0b04140906040212040b09120f0405060a02010b040e0d0e060c030306 69
    0x1d0101c00148078040e010352180a004442d9007002c240a90340109014465048a2000c000690b00e20700c0150601c2e01c400840707224005481d0307103180141303540d01c3c0d916000c3c00607204010688411001041c3c3e600c00d107800034000e424031028291001c1084040c0d00008c5401440015014104009005007401e601d401c4126621005601c0604607400050010040340d19201454158105580d00407082c101794030003000c0b0307807400380d100400f0800d00481d00b04c20060450042034035441c0400035003024200083c41c60b090b061b62407a0254804640103150910200c120100203148000705054908650748040c80810005207070b820000c0743c00004214941c4103030f003031140d80000d0b41002076032407240744070391303d402810b0405e00c10f0203192007040c01b808080840100011b094550b01003040c1d03030460303100750f9069440300043c4000382e0151115203950f0703030442d2400c03001940c088000904e600902a05444506124115030203009081c410031800340f046da4405c00120b11682031900a072200c00901c5041034020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 694088498 1250 694087248 694087259
    0x2301030f061806140105070f050f030a0804060b01020d1b05280215030c09040b030f1203060f240f07050f010614030606100503100b120a060e0106020a0813 68
    0x2164800d4220200d400399a849401140202e48140c1003d0100d02a20307120601c1048002000c5100b5120010407110303140c05c03154100031080060b4444800e06206580d11125410801050b55404840980d580b0b8146003980c0351550010030314214401490b0798144804541545101450100031011501841400075101d600340206c2164080d924891081031140100c0f40100a00b0110034105456052070400c140003141c5607110484000d00000d94001c00c03219800700c000380c1011032081011840e4001c8807840070004c140c0c58021032207840101ca003510011403090a101c0c282008200c0c42025030314180f214801e08a04d00043c104c1c5900441d2a540b802c6426070f42c0d03034140b00f5951a2811503a440d50818000200040000d90703295500350002e0200389410000940600344100d61802801400000b00343d01503440800341010381981c060260390341c00c00321006c03201070500f02c46041c1e00501d0311401040740300c1054000d030f040301c00d994014034103858603884c1c1384c00940c4410110411482d840c1400241c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 694089748 1250 694088498 694088501
    0x1d071803122c040b03060f0609070507020306070309051902031518030a08060a060e0d0f020f06130302122d0703120c14060c120604180c0602010c0203042301030f 71
    0x80b801100300c0e0350000380c1901ca003840143c0d0300c1c841009200c3d40248003003110041c081c0c5a9298001011103040781c02e9280d50b2004c0d90644909680030f07425000740d07020400495095008442402d1140f02100c0c5030300060300d0307180c16540721054025403542000a5820840704440c00c0301d900305071003582e007400c070070300c00b44500d440c55103c02d101c0404550282d040040c2464821382081c000c058031700b08080340d082ca0034000740c0380034140760000b001886004264015525450a0122040400740103165507600e054a441c4803019148002c0740310b407a03202a03608600c10b000c5511400d51103804e05c045441d8004124204860184040e036440ba440340b0600040402d0031801c03641024509900c86001940403428a5124002c1d0010507141503070180c000d101c081d0314070004035142d0071030501141c01d5039141d00b0700003006405191010b000c03070f18585550f5010300280250640441e030080d0000c2049181c3c1032001d9850380107611505070401c1d540080c102002c42ca040e51003044000515000609150b007003403280 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 694090998 1250 694089748 694089797
    0x204050616020a150f0909050408040308220b09040515012003070b16021903090504020a051e19020105040f03050c01020d15081516050c03131d07180312 67
    0x300094000c2401403172594210701480050400b1020900542c0b500382c840020a108130706c00101080d00015000c005026030b4008030005515060a140035540d44402e0801c0c0c3c0d42102e00124400ca142401143c4801690944451310801c1a122841d0742c940128a00c4503403070940c044020940400c116000001c0d46880790103101e0b0345c0000c56900740c54440d140007890700004881d0740f0090b401e07114071200804d401c1302c1d02c80200d0300c0485025903180100501280c80340078090030011140a0807110a055102c0640900700d140c00c0440f003684000200c1404a0a83d00c0982d0007802114035201d000700420b214a0080c011489000b0000d441e018900c4110011102610011010a21804030a000c07070b078010f0084a828544140310b80125003071460b50081040ca011034007405100300040d5041c038108060091f80c0844800000e0403040303e54440e40140c1d00100c101040400305003c4001507081c0b8041d005030516a54164004161541075507500700904400258240a111410001303140c2040c03c0e17500b01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 694092248 1250 694090998 694091039
    0x12020904210206040c0e06030604080d0e10090201180b030429070804030207050118050603061c110f0d030f0804030504151106010e06030604030507110409060b130204050616020a 78
    0xf80090b25060a003014503152a0b0072181007440d1800c140b001d2960f0015001c0d802540060155960742401d40045005140400d01c0700d281d80211901910726075141d41c0a001014004e803260081c140e64005129441042c3d40285075500c3c0040c0042004100060000000716138211079414240740d4610b0070440000c000c071110030014a55504000030150b06110f42c1004020030300307010021540d404485c103120315070341c0183c0f0700403040440050010307a91460040c480641042c1030b032054040c20f003814800060555106030281000d50f1008489051140a00c18099015902c40d00146660b00e0119810300015100b90100704050001240000010300139030010b54440d110001c0522400104a007000d030140e1110f92941d4011302003203060340b0003081c000c0e403103903152803c0c955840741490041130382000601c506802c1841d104081007006455800b00d00f11400031034550302621812083c0106a01c40c038000d464000e402404900e44408400c08000d00883c80145a89980d42e111040b142d540707440394204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 694093498 1250 694092248 694092253
    0x30a0207020a0b0c1015030b06030705041b0207080d080a1505060d020c0f151914070503090c09152101090609030f020a0b0c0a02151602070e01120209042102 69
    0xfa288904c0c02080b046441c40602841403111315440e11052000c1e00180c8406002a03a00c1d10010b0f01030b40d41440b00f40e0107080c0017030003001900b12641480c3d26001c0301401c0708015100d4560049245e10001440444003604d680d2001c880f613550403442c0015002d503800000144030f06200c042680e03a54540646562891800010f8a0301c0b0030f4000c4500c0c1040120b00c6440540081e002c0c04101c020040146510810000340c40030f0004070b14120000400c10301e41c85903041e0004e82c0511161a600200643c05400d40b001104c01002d031100820180007802d69411905107440781030321619040c000e21050807800b00e9071840310b40b69003045843d0300f514100c01d403c43d001135640b0740c164100764204144180c502182e1004200030395465492031045032000c0c00e44500c4140220310000218820401d031042e02003001402c0c0941c1c1020380c00015000407070300400d809401203034400718a081c0d00345466030488454034086100c0b0101902881500c44010b041503038154034680c40f040c071400481880d8209559030b03500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 694094748 1250 694093498 694093507
    0x13061e0e0105062b030c0201021e0d080a1e1104121a0f040c12020a030f0b0f01060e030705040e0109050313050a090506060d0b030f070801051006030b15030a0207020a0b 74
    0x2c02010a030702403100d00e8410204646182400d9130f501140003501d40c075007000c0034084c440b0300041c2d2a00800c84583c3c83c250740d85c0644030440d103601203041d0560700407a840b40d40d03403510390052440903101c0c4c40c1c2c030445180300307951250b007440c0b502500606064001c071080c0030f1505c0c0c1c81d00e400f0b03103003007100c054252076040c40c036081e0740282d05070303680002d5120303d002110602c1c6041c15519817110003014410b940b0142940c42c1060195a18505a41c00031688540141c0c1c1c17400142ca840421250125281c1c070944249030000158640251303040314000a000f406422890305020410000344000304000d0b002e90344e182072901c0040e0003000100801703108190344a01079031921040010340c110035042500110b0405041c444c0c151aa1030a41e0f0203030a40c150089000c244000101c0e242c9215a603c02441748034240000440c00410b51055005101c1301c900c440790f254071640190b055401202c181500059094408040c8001010241d5046564003801514007c0b2640000c4c4400405400503900c10a0005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 694095998 1250 694094748 694094761
    0x22020f131e33170f1e120f2b06050604151d100309050106050f0303161115040608101404020a050d020304030c0506090613061e0e0105 59
    0x103801d080c1e5185440d4144038032440000070b50400b1168001c5a41c40200030800c6031806590703015510007404025000b01c5860030003c002981c3c807254402c610400c0e00500811501005128843c240203e003014010403c05030352100c1e280d62948005c07031100800301d00348440360b200340742c0c280c5090f4a10071101c02c54030000b1810602a007100c141d90301062040c40100010000d801031201444c030308100702c4c01c0c8408200d0f008404010301014100342681d2107080300054041003501607020031040ca0141008000d075548600a0120100200c0d03a90703030380366005120302c10300002c074113800071a264070813450b0100342040d10000c00c4a43c002c140d4006c0318084041001d00031240e0041105034010003041884552a2400c074404000c003000900590040e40c0005444500e14040c108a0b0003992003004115583e24250800900364900b185044401d4040e201c0843d044920000d00c15018003a4213103208001082c650303883c1c0c018050000d80c500210743d18065030000d11902e100d03089048000000114aa103080c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 694097248 1250 694095998 694096031
    0x5010503300a1107091a060c031902070906120f0209100e010303020619020a0903150b06030109200c0303060d0c0506030405071401020d140c01060e090a060605060322020f13 76
    0xd4005c0c0013054605101511441000d581192000d002035401981c0e8004958410b419440f0711340200c641126400c1e80545c0303c80d40041e40c0801c85019000c00c10116848161100346503910b42c42c05001441c060300ca4201500d481c03216540c10200002c64400402e61310300d202c40358003509900660160308a00f0070403040d00c10807429080c09140e038110446ca400d54268018001d0700355800043c0541580720040e6000007100d074450406c0c400010601030b00c941e50303081c43c0302c040e206040c52090030403043e01420a4610b071840a40302c207400240003840c02c560b110402d000b4800c180740c005551241115100280780d8850314001c501560090004d480c80d02e0501214810b003080c00000c017811544001440201c160f80301040366082101d2606050b900ca52082c103850140030590000120800040305000f0703001c2c0e00041d00a801e80c0318000c18010607642d402088607900040311140b00744c9088a05070b20056242c43d942a25041c4024031901c980d111306000b2442d01505a0419140580e035007120140d06800da = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 694098498 1250 694097248 694097263
    0x90a2405071a0603101103040606080a080301030f06061d04210203070b0405151003060b0303040b03040204201626070b101806030209060405010503300a11 68
    0x29400c00510340041541c0e61102d0b0782118820519192800000c01e4256800384010040100c100d5014003150040e1903501103a6401524110b0b00549445400105d442e008140c620101d50001911815070b80303540c950340000c40a08400320394450f1340f002e0100740d00460348142800c003001c00380c111080c0e15261401d642c201222040000e86501012004800302e54000201d4082c69407240c5100340c15180c03071030101c1c03500f80d015a00c1303440d0451250422241555000d4814100c0b40075001c248800c0e070741c11040c5500c0e4804c0d03009508001c2d4082000030f0150900780c201205100000044405100548080d2a21a0043c0c1072841c9a00000403102c41403080e611411003104e0766040e054502c048c82100b00864030710402400600780c00c1d413903000a00e00011100381e030004142010301d44004280c02c80a040003020700c3e001c101e12440340c074000b00e03500f802e0900c42c43c0d040c1c840142c01010043c102c0350502c0c03000c8080c2c4402090503540110b640080c4000c560241c03006010a4072111078403580c11400a051014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 694099748 1250 694098498 694098569
    0x10e03121504052208040305121201061e0f0e09070801080106050f36011e27020c1e0a060605010503070203090f0d0812010f08010c1211090a 62
    0xf80b90522030489410135440100710760000700700450040c81d2030041800e006550000e00b080c040c12401d00850442d190080026040742c800507030311a138807040e05480d0314062844132018240d0841440c40668001c400c0e00040c10003500b814094004003c000608149045845000154504004001400e400d000d43c5014200440c4c07808280404903000c102c00c4030012400516882464104080301c9115030007040e0f100b40c814008540f5980c4461690983d42100342c1c00704c1102440c01c2d000a5405000d0303030802440c0b61020f05d410540c0300d181c000400a508510050328031801008140445400ea100017061035900410180905d4070b600e003081d00c11110a54492410300c0400c00412500c1c1d03034003100b1210032620490b140c44a8500030808a516031000c124020507079000040c4403d80d11203032100107070403180c106200d01e920541b1040d03c203082c0ea0f202a642c001150388040d5010704a0480e40000701503440c3c0400c4d0381d061038030f10340c0040c2100322503a10003041c0350f0340764040c039084402c0fa803c1e0805160 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 694100998 1250 694099748 694099751
    0x30603050d110604080912030a0c0b0703060513050c0d0f0f180b04080a09030206030901020d0c0509131109100507062f0d0b04150806011a160302010e03121504 70
    0x4502e03807001500e54034024070050084000041c4849540c0e680002030092204513012aa1503085010010b0280750044c0400c0d14070031040f200041c5c01500c40e01a10f01501c0014082c1003040c46901a4a00601405010281c081c102030010344848034031071141c0101c0d60a800000304d490f500c1000554116100e07102d0801181c04c816100b10040b564a2008a40141d44121642c0c0e507403101d1101281d0342403a5030002540048004140301c5044415006010008403000040283c44541101600c070ba11580d000711390001031005440700d11414070380c846040a0780c0868894600583c49000804603001e2540c810046807020401c0b80034807240c1d101d140800800d0300410807644580c40d200325401c1001151b22040c00310005461640740380c0a0b00f14092a020150040c81228803071242040e0400413401055080e1080800015907082418080c403503490070030840b00d00e0800182e00c2d440200504c04401e4066640b151040040032504000419241e10b01040b91581402d10401c081e0015403203046103441a03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 694102248 1250 694100998 694101017
    0xb13180c0e0c04030305130506031005030c010c051911030a060c0206090601060905040902010203130e061c0809041d07030308062d062b09110d1a0703060312030603050d 74
    0x782d4207141200e0590f9014101a034031100f041a608442c250070350402e41e0840400300074800e88403400703890b4200707503182202940c110f02c00c600c00444000081403c09403203644242d80c0d2201110049001084843c040e424038a070074542100072902c1c041080c0340071540569254a1342107240e40c1402040d800044840141171154501600140100903502540d442140d840446204582c02041201c103200d0001e640c6a040719542d81c203407179185500310381c1c1c035000c0c0c1203800350010405860491013100710340c040419403e201a030300600004055500b038400c42c03c128111a922801e2341005548021407180c0d40e28407403840d202e4207005001e881c2405c032000240b40b09a1010040c01c029008042c81d160a0303500c141c84405008460080a00042d10040701041c004030050101c03901d0340000309154000c140035a24030301d00d0350a01401d0f0640007006001400707408100b2a6803007000c425942c000c4103a1401195594a035101c2014200c2104030705004656604002c0081103000d100036003010ba20f0381440b5041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 694103498 1250 694102248 694102261
    0x140c0f091303030c030b03101b03090f140a170a0216060f0f091d010801060e09030421200a080f070e0c1204050618011a040b13180c0e 59
    0x2005078140007410305894101100301e02c1d21943c0040354440004084824010109545000802200b228902c0c803c000303c030f5481d034090190007201c608076840801011a012951640001c01d03012085849042c0a085808004100c0018110340141d051680c616611326070011301919255540354a80405140c917402005440c1e0050101c8020403480e080c204094420920203c608a000e0342200030220703070005011044480c49000181030341c20140082001ca51112007416190b0012a0449850b9008000501407000140091225081c09200c000c80c81c004c82d548401744682e00c1c40c91411b00e50101c10281c01c0b10701d41300760198014103215001d0220300100c4004191039010501134400b0002c5058003050016004004135866940301c01107941d194141071a00d140c5400081d01c00038500003103d80b0651518074180325454947c5114084003a850088805010203803030700c80303101a4005c207003411100c0c814205004202802e0075000005098401f00e10b481080e40340150032105d0040c1d0b900042082 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 694104748 1250 694103498 694103521
    0x50109060f0f09080f010c110f0a031409090432101a0409050f07230d0204140c09033007022116050d15020d020403140c0f09 55
    0x45008a14256145018842c02500d20f9801684421514400c12050140b924019840340702003125680e5518282c0c0c65203850155114a40700f01c0001c0c0c1e411a05a2100090040003010402e56010803101d003400c561000090480700220340c1a140500000005083c0c188024101501c80b841b01d01c21028001c1c400d005250b81c1c4071041880c5c081d051313840001e801e0000b0740c8060703441d040f00018000d2000b0021803500949400402054004621860002080c06009540390302c102020040e0140c05024440c4c082012803600018183c0e04503030381d6804c1080f00c598080082c0d2080c03002035074103603480c11410141f41c9010405504180c4150382402c004034001c50501c4140b03407107003038440b0700c42d01c1e055107000081c540701448070300d8401c01001010103490701c440800c64078501840c4c0d60702903494a668200b131020301d080c1444010010b03220040b10001c101a01c8e8060004482004401410240c2725682d90200700c2501845034074a6024411302d41e91807510200018142c0016a250a80c0d0b0605d04501c1c01c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 694105998 1250 694104748 694104767
    0x2120a0c0b0f270a021309020f061615020c010e1c0921031107030308070207050409080a0f0e0a0905040204050901060608180a060903080906090118030c050c0a06081005010906 77
    0x1005060810750303008140b000c01604c43c00b680c00510400500c52034403400d1008040285c405c900402601524902a1411070280c0e6034400341c200c800e4000c2d0403144d555080d41440100c44411459080c800007401c05800d00c556421800d1500044c220500700314907007811000000c00c002c0c100450540c040c444601114029075180d1060100d410032200285020f41c1c8144079035103032968038401d102000090603800480300d4041c89180e000e40c4c40c0301d0b407a8418082520407291025003822070402104c1600391051014240d000001e19106250f150300c0c00c0000c2228a440e8420a941600c40b01400151319141c4203164114a01000030007225181c500080e00080300101610310750303030a8500041001038180300c038002956001d0b10421410700c080c41c01414440307040c2e80c0001548507000008408075070500c10040780242520243e888880c10755030846003005922811030b4140120f443c800c3d859128007003100060315503a1260340c40c80ca401480000c0410559002d80e04200c01e000082011580000160 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 694107248 1250 694105998 694106041
    0x40902073819020f0406030b0405060f0d03120501080c011b020d030507030c0c1205061806180a05100516050711060c030705070312091a0f03040302120a0c0b0f 70
    0x440e00c60b510b0702e00340c28000300b1071202c100325103000207164100080d40d14010029602d0546003003000406100501003115003c0311000c1d04031043d0003180400785040c044c1c0180381e40c80f901c2d10701074000240c0340840946000380d2084c021a0b120030342e001d040303682010214a8021900c14500c3d80d02003d5000074800035240c80c806030034802c0024114090621981c00168401d41103030303120451541e200c3c0750300d00050000c0c6098545001761401305400f4100c2d10320311800c5089000003094140c0f50314804500e80500300c0701d940b1052198100740000503c09121020211084e030a0004041c500241070090001c101460f480410104001d0100020f17950103041410380710561b45161100c2c0d26130300703e615501c55140041c0c801d2007102000410090080e01c408981070903682c1b51000344d6601e81d6146d5014040b03000c6000b80000034080c001d250342c0c0300005035078010701a10443c0c24800090380b5181282e030000d503110b000110720703007160390034091a040b0040e00800d114161048074582140014011150708100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 694108498 1250 694107248 694107353
    0x102060f010611032110050105160b1e1501020f070b0301150c050a05070513021812011812080c2701020f0d030506030708031c09030c0804090207 64
    0x1c1c03841800810070345200842948580822030031702100c004403440d0407242070030301c0c0040b0b200202c0c00f940f00d80d0940725202d0300307900f80f0201039611b82d4850f071007000c1c01400a070f078990300c9101080207100c4004860f40030706079045007800c0760305411000a04200e001003692100c0c0c6d00141081101a820100302c0c1d044a540790504c0d64141c00c0000100da0f000d512000c05041031182e01c0c608814040041451821642c1c126a010403d490742000303201a40640c0411880c1c410034250400483e0030002801001742140a000065105a8198001c000401ca1409559403420003102c41d02c0c8a400091150300450390034101800d00c01070b90000c0b02c0d885002103401c10f4a400095040c085c40e4020003201c0107030444070007a01c6085ca00d4000003002414201c5540f031080c804e58100140c6104080102c8203543c107422050303811010044c0c0d051004c2c10501c0400c4042003c80d8000d4004100e0072070203070000c1c02c1c00810140e1f07a1b0755513040c0120f030301c00c420b8004900c1085000388010f0030b8119408504150209404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 694109748 1250 694108498 694108517
    0x60708040f0206030a0506090610050406080a09050616080a021303030c03020f010608010c0314071b15020304060209012304121b1d070207030309030209190e1b0102060f0106 76
    0x144680d4001801c0310080d0040004420302220010b90b4010700d00c00d00c0b00b61101041c41d5528004c000d4400e0118180401107402088123005507841029825846001c072000410800c03050742d900e07807804100b29030b10020342c2c07510a200d010141c2d006211035040f4a2070181035041c20f61460b451030f0001510700c0000c0501012454220800d40248040c480190080c002044107a5580c08403a000c0c01c410084000002e15001804455007016460381d802542581d90f5000c840c0b07014861a00b000c02d0500003524645038620102604440300e0000b507118a114503c0540c82d60704000c00034094622844940d501d035400364514108031000301003a00c085618100d01c034407c2c0030b40e6040c14103500c2c9001c0002040c040c01480007140c4140c030b20301d0100c0c2009003500002e0036507913004403ca0f02c540c4680402030010303009520402c09850080c008540014600d41d1003070170300c1d60b40c1c2c210b8001c031307260007019885507000683d140400c031001000200c0200800c5c00a881c8078502800602e143c00b00501841e0103100c035186 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 694110998 1250 694109748 694109753
    0xe01030209240d030206010501020f1b09191506030f020306010c021005040905040c03140318040b0f10080a110403030816020c030a0503180f062d0d02120106030e06070804 75
    0x200c1018002d0103400c20302229200e0400946130f200c24003c0c2c074013512840014052050001403003002c5007003a6007418208421307000800c000c4003400b4281105210f1410386003d0081070501c074104a1810380b0450040741480d014002e02984e10f914051f210307003441072040003000c0e60410850521503604881c041001404841c1c2542c0f00e00541d04103902040c5004100810011200f00791000e032400f034070707054502075003143c0c609a880c070901098500064500c82e09000310f05164100903e0040001c02e141c1035884c2c0394000c02d46e9540e4481002001074900300500ca8081c405204420720f0840703400c203880c9010b00315140604029000740c0304106c1e680c09501c01902c035610034010b6402e00500102561a0240c260070000d0b620382110010f01c910307081081c5070041900d41404046205000a0255801c200b0344482c042d0000e03903850181c0c4c1c240000507078044001a034000007003124680c1600010384a00c0241d4501c0d01c6428143c214605240ca400c112441d14480003400542c03141c46803501a100d9a07691 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 694112248 1250 694110998 694111051
    0x607031d0703050703060e0610290a030902040b01050910050903070f060503071205070909020d0b0a0f0e01050604050a1a04090c09231e0a050a030503130e01030209 72
    0x19280c60914014610040304101020030001c04582c0210400d2011035a0294103d03110f0b10b0699181c40da004503c07100304400ea5066054004026100600a200403071046060342c0c80e6102d01009000260f42c1e01641c4210f182501c258004c030142845c1850170b11701d4480100b2584820708200307400f030020100c2d02000f5540c08101c010060304c1c00020729840035581c3d140142880d00141c882c1c0d804074568103c00c03100a0541d200c0c1911038006965404800340c40c25190f240203601402604030220744a05e40000141c4a004040d0020440a01d0462959151004c49411000c040e04100e218400400c0100802c2c2d0302c003902c01c1c00341c5e108620b10050f200071020411249200ba076000e054800d04000c01d00d400e241d0081e40807000c030740c0754101c4a189021410580c01c0d50016004090b40d0200c40d1034422041c180582001000d0814007909145101ea1180700282545040e54000c4449510000302e00300c00100480c11034000b031410800a48042d41107a0000ba041c0c4401802c940791612210700003001c0e18000d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 694113498 1250 694112248 694112291
    0x30905011b1214041a12150913080c06010e010807080f0d03111e041a0a02120a020f160305160807150509060705340e060a080319140705060703 63
    0x40680c40265041c5501018517642110450950945008001480200d24518180d6007041c000b05104020307565100c1480e280e8040504c16a00814184140c040f11401084031501174400c142500e552585400f0304940b401d08160070103100e50f0410b2144c1190044001000410600a81030105d042c440c2d048260b0118095005038000c5043c840c2c245011080515000780151124407036206010403c4130301c4001300e482040c500e440186d2000c0304051401c40c140d0054510700e20544159540540d0050182e845c181403110003500c104c00350b00c410400c00000b0000020360b00b107080200c05030039142481007610b80c4207521441c4280540c4121850344940700f40708035074520100030000e60700c2d01c0c054140a40d444000b001c8803c0702d1000d8142c0505131440781c10000041c040c100c0308030094070f13061003680d4207264005060301d600081c414901151920341800604200032414040d480e505003054401011950010320044404604005080204001045044e4050b003c5d040110304a40414501d000318041d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 694114748 1250 694113498 694113509
    0x30f03031b0305040312050f1b090d0b0a06090902090f0c1612120203360a1b0b04060801090b03161d100b0301031202010b030a030905011b121404 64
    0x2541c40124401c6800d6403003d80102d01a94449201c10118004401220001d42d00007502643c1c80000500c14100800d0080f5085001040705040840180c0441c007040c2c0103802c100c404080090410141e501c07603100714401045801c01c144440301050700441c0303000b1000350140d581e80442600069075a04000c086481c038410102c102c1c2403020785414000180c1a44001280c00100f5040002c240f881c0c05009030303030007207586005507146410720701140041d2403142580001001c185a90000d20440b0038801196000c0c0182a8000c0640c20030003013560070341032034020f0101d40005000600c03803960b200c40c9840c107440a0369400038542c1c19000c0064508840c1030f18903060111001001b0134894041004017500d4150812201c000f03459454184607088a80e0042c404500740500040010802070460580d0b09243d03800006002901800800e060007400c1c030054011400014040100e5640002100400c0c090604204091250b690303443d03c420240d80044020807070151551b2503517800d068200e074001d20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 694115998 1250 694114748 694114781
    0x1110a120809060a2016330507050906091c060c0e0d0f0b060a180501030b13031205150612150a030b011203090504050906010e0c090a030f0303 63
    0x40100e4014031840040300c540c580e500072903011400c1c00710790340151070020004a2500d4001e0b1941c0e50002071580061008001d140340286c0490041840180c100d0380540030350040c40c00760000b10f2400713000340000c843e0b061020340c80d00e400c002e119503219050381e02813041101c0041d0b86000e0180021a11603030808003040c10310460760110200112940f00b800e081509443e81c40c00170090400b00070207180701c3d8030060007109230800c0c110000381140c0c10071b036409680200700c0701c0d0321034880165164010243d148020580d0340c1d04018010700040c0403846a020790741042d2480e819000b070b68014460500e0100c51a5501e407103101040b4048450500168025805000c058484070082d002d080c00010503502c0100d414041c0c83d14007040e0410301b007010300f582d4100303000d00d08592800000c0314240c44004002d504100030344d2000b0400d66203a0180e18000d203041d100402c03c55050014404ac4180003800c4404000400c000040705a100c0b17035804422260000004a0307110f840d802d00340e003c0d0926002c40301044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 694117248 1250 694115998 694116023
    0x301020c0c09010f0305100e120409021c02041d06030c03030c101406011d04110a0305061005090d080705030c010204030320070f050405060d0203010219032003040201110a 75
    0x40c10001000d09448030202d03801c2d5030590341c809034003030341c04103a002c0903089401160b145882c612850301301c18402c15200381110990541d80440700425000341d0000340400350002601c60b49018045400440b40c14242411880c16241000341141d10700031090440080660340c000500d26a02840004520b050290a03282e40303091007444980c460100c2107140050340d18020308001c0301d03440104201d2081c0c1040e103451800034510007016600780a441600d9500c191516410290200c842015201170600c9440200b41418040100100720000300b1502003002405d1201078260340e60400c2d4000900d401c64512942c40c5d243d8280641503110b1011464129800064000100361b030001d0300c80d0110032a402c20300402290380c55283d4031351070703140700d241d22441c112101407203a0b150503801070360800c100030081c0d810002c00d0385c0460309981010741c2c040d1001000d400401c01039501409401b0110161a0000f40340d1801204680098007000d04040e042040d0300485005840d803c22403002941e81003074100320030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 694118498 1250 694117248 694117267
    0x6020301091e090816240207030806090c040909030309060207080304050f01020712110a02030a08090a0909050a03030c05070803040f030e030a0f08130f0f03030306050a0e040209040c0302030102 85
    0xb8041c204100c4011010b010301d800d2220b01c0c284905480750b0b51140030340345070010080c0b04490442003401c043d158021000b8500501800c070800e0b00b01801e5484102580b61081d0303040c050f10f80e140051034140142c500a0400410b00f81e000205c40903a0010350000509089070304080b4010000080020a4584005059018050341c0380c042d6200701d01c0342c0100c410483e0a00e500030700341e00071841c00410b528004805082d07820f014280701c80403d41400c2c1111012481600000d203410078142003901d003e4000919006c1e903040403081c00010b062080c0d01400311117425610a659605070050140c10556078040401c02c40e440381c0212402c064009800340d0302c0c0c0c10035003481050301e076001d44110081085280c00c01014240440c5071049a40c00c904075680308940741c2c5503110702c0c1e48407000c81c0420000000300030481d13603500c85420f00500b201550303540302c0710709600d0050219072098100d28403480140500300000680310000c03942c4a80e0541f10fa00c659261440c011440d201c95420003907140d400420310182 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 694119748 1250 694118498 694118501
    0x60609090115181b0e0d0809030124080a031205070c1b061205010e070c020f040e060f0c190509010302040b191d01020a0f0f020a120b0109050c04030318030602030109 73
    0x3070f400d0079110100420000c1c0c407802000142281e8840000c10030300c511a000b54034085404a140a0103500c80c0340c03401015400090854600b021768085100d40e0031021410503a400035180041d020000c0100301c60314858801404103960080c0701000705440d0070010b107445100700740600c140e66100c10034400724048001d400d00d8000301ca002c0d510008071070f0420002510002e00030b0078102c40d03d0723029400a54540200455015026242c2a60030000d80000711100d51214854000c00c0390f281da0182031103080c4481d05034a1202c0160082541d00e8061003081c0c100780500b144440881c1d200d0818683d6410700c200160040d01440d0b01041350400d000c06c0c840744026640400090981c0075581d411164030344c41145e5440d00400035200d40c01070780200f18920028030032420100700b4900800352880b041d8140c1d800280300e01800d4110303084103088140c2c801c0422036075504950240101460900c010301d0442d180d0ba00500039448007a007000030405d101c100418a41c610403019503007011040d556580c64084500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 694120998 1250 694119748 694119779
    0xb0f0916080a05041e05070e090a143403020a06211104140d2114210c0c071511071d1008030c0d030c0c05060609090115 53
    0x300030540c1c04000a80168151180b1849681c0c400700311040c0d0402001681c2e401e00103800d0880b094480d0a201007224142846d900788500040e0340204107400b140c3c500051503c0c2ca28014402650061030081d0100c403072014080c440040407184000d01040b03141c030112a00380035500c0603400035140c0380049403c581c00407025030300d82401307160104d9070700c50080301004079102c21041710985802840240448856140102c001110003000716040c46416141e03215003800c01c000100ca203100c1304c1010a1000d41080000b040e03407071801400c5041002c0400355035007010100320014031a0f0b410f28001030f4070101c1d0005039141103141c282200d0095403644054042060301600803800b06800007141c855580c0d0004082c0203461060810a05d0740c40c41c0f0309941110500075181200c071509803500400da8a00401c05004075040c00780c010011450030f018003804a03180ca02030403042000c9070940602040000803410340200080d1480000c5a070344041c801d004040f0040c4440c80e02e0121200050400004101c26 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 694122248 1250 694120998 694121041
    0xc0b07021605011b0305030603010207060e0106080601060903050304050918101509060b09090601030b0d080901180302010806010f020c03070311040c021f020a05130b0d1d030d0b0f09 80
    0x16075141e1a01c00649502030f01401c49140c040c0c180b901d01001a1099004d940c0252000d0b0015003040801c0e5100b40544101030720500041e1f542d000b007041401c0c0e0410051b0300504203400d0004090742140c07180c644030320860051900904541011540c000c5e034a107c1c10003591032020545285401c225600c03000f811940c40f000c00d98003154280071400210920606045a1034030b01c4c21850f0040301030910400c000300034009818165200d00c510724640b1080044032840744170360030140c2e071000540c00140c40560103481d5030502101034001840141d8109000c4c170340142c4c00342090030089115200403440c0600e0f51102c7c580600409400104201e035070340c5c5064410204440c203000034140688100e0b40c0304c4400204c00300340422550301080440b40c41c0d00800401030a483c01519154510a8200c00207041307034440c20200c00000360300303607017558248034611a0303010071000300e68204844060540c1c0c0c0d01803502c0701d00200c0d07074500e6000040d60f9801030980e15090050714401c101d00c1c0007607210007c1a00b040342c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 694123498 1250 694122248 694122283
    0x4090b011119031b0203030a1101050a0207030f0e0d120201020c060a0207031b05240412020a0b070e0a090603050307050d0e0d0822171b1c02010c0b0702 67
    0x1624403207020907440c0b40c54030741d54802a201d86481e02d045408503404000c45400300e0a2403001030150714180000d22844286880341c640d40c9070000c1d2106d0840303200030300081c0780038814099500020303400010143c000c4132518020f5500b44080b80012140aa07414004100040c0c420311607402c250103401400841c0415015500c0380e583d0b10810400341e20039108018001803410b900d200c80102d00b079202400c00b90041e030444100b4400d18003c0501c614210100030180300c805030030001002a071b90300040d06d581403440a0941184280c0e6040300b4044003424450512804060000d8951070303c6050704014006001d05104041c1c1d0381c10100c4d2030794460314082d0780c24040e104a1441450040340d1142d07401d44003a22590780c10340c041c1c40d502c50f070350000880c15030410711003100d40c1100840040d808002e060b045400da02080a0f4900c1d10349007148c16003104c400c490410f0700402a543e01c104110226120221842c1e60400003440100c03200814a000100b051a011051142c10365000589a11a045da1030744d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 694124748 1250 694123498 694123517
    0x40605060903030d02301506270303070b04060504060e0f0604111305090d030c030b091501020c03150405071a031303092601050c04061d01020c0604090b01 68
    0x40c08001d00c542000e1580550040000c0d281c3c10010758000d10851125004100c4141c107002d03038128040aa1a0700c0c0d40c0f64141c0c2005110400d50034502d10303003d02c0c0d0202c4000d458002e194400c0307440d01381594480340040e4480c075007604068034248215074240d42d005900701d40525091a280b0020701c0d064a090365150301e801e07060f860588000400c0300862002c03000518842e50380380d5036006101c40102003a5040240c40000c101080c1850203041d01407403000c005010412080d0f0402011a251041c0d20800c140c02d2850b414265111007940c15044201096050004018080142c1c40c0000492056815114402c1e4003107001107a0703041d46000e14031880a603005603a450040704012090a02c0e5001d24000030404180542c1d40c5000d200482846030410000103580c0b1044d1442803111299404410f41c4500394441141a081c4103041c0e0002d07400d0301c43c508003400c08100610049001078040e0b038201409407142001c1c2e00030000492075501c001c141d65943c5844201600190013205920750115000341d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 694125998 1250 694124748 694124759
    0x30705061501090308040b07060609020406020312070305011d1b040b0d0608010b06120405010e0615030c03060c031b0d05010f0602010e071404021309110919060c08030601020102090307140406 84
    0x15243e4122908029800e080c03606001000c02c20f0ba0255401729100d0341e4490001800b1460350020f000205450b030051621090a82c03148069908001c0c49007080528110040c844190171202e00415005c000f0382c220364070b40d904420a00320108051002e10803000115000401d84072120003800d1403a5541d40a0002582e50a0700600b03070b5081c2c02c1c1e4660f0081c0107019008905500c602d40c1d944c02070207030b8000b05510a80d14071403820a0015a14170b10203d134503c50005607400d08200c0041618000e80052280340360a8100d01014000a8422041001c0441304d554410200e10252030741c0d501c0100b0200f105581d2050008145a41c0c1e114500140d4200310001c040e103c400310743c081c12030762a00d8025505040400802009503c80c200c4501d408840602c041040081e83c8121030703080616010743c41e44d4503001c034104120842e12001000d1181c8041f04180002c0781d0040079034880030b9002200640340d841d11300040c1d01a004004841e0742500c900040011032881d490030b0018003c41c1650308025068449e03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 694127248 1250 694125998 694126007
    0xa090504080a030b030c0d03090f0b0301030b0402120319050301030312020306010807050a090308072901030f080a0e1c060e010e031b011503060b0301060b0909071808030705061501 79
    0xc036405014078205006803000c0a020b0b4000c0c8542100042c1a18050038440e00010b528103107032002030b40002c0b80d03050306010724400c4480f41c2010b80701e0000c0d89403c640c510359a0b6001408001d00090203200642080040d2880c2003040d520844251301412840c0c103004078004000d80c0003440141c0016103401c03c6500c608074a442224040c801c10713510303618517a48903101550b00384d100b00c40c8002008040000040441c03000d07005000c1c054030036584007118041d03075581030402c401c1c51480016071940b4180104001654500c80606481e804240307180c80e101c20f4841034030700c4800d8100482d00642d03501483c0580b00200c42c20031301503501c1420200101c04046d50424200c4d01245003040c4a80d02c1007200c080503010b04548511900980e000200d1010b18114552201411540c01200e400f40c230380400f400030b8a42801400090205442c0032401d0890400004407083c0d00513028000b4042030f0608081e84140c8140090058202001100c0e17499286150050b41d640d0b04a40c0240c0c0b22400e10480f02c1c80b50f119 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 694128498 1250 694127248 694127251
    0x25030c02040b100e010f140c010906061509030f17041238090c04020c0a032307060902181501030e0303010608010b03090f10060e1f12030e0a0f050a0905 67
    0x5981d11200740304e000e0300042d100d50304414280c400748142c2041c400c0080d400d050042010348050307400450700068030302d0004150741540e080303400c0d889100b101c0d816245502048490840750800701e40d40c210f0203182080010b4911b4800341082112001601007030085002411000340da10803190119941002060400c070404110700358281c1400001c400883c103031800540e0743d045a1104180d82c0d4240d540c0000604a91110081e00c00302d4002d0481c0700181908101c003405a250900040c1604d801c0c501620ba16610541100518050f580c50385501551141210a01120f003c0c103a106968281001c402502a48180406000908000360080740d50350110070f41e4120766141d11040e8550742010104c00f0705070402004012588038aa044c50200e800800035080c80300c03049200012514101201d04c020030a000b0080da6500004034282113041004085280817640074150200440f0854503045a085102c8081c040e0320900840c80850141d142e0000c030740031140102d5801c807d559540c1c0c03584064910 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 694129748 1250 694128498 694128529
    0xb06040b03060106120216050c1002010513300815060f0d0b0d080310180504020117090115080d020618031905160302011d0a020a050625030c02040b 65
    0x102c0d000402590380100380e00b42400301c1800c0c0150801008a504400c010f030051030a441581c00520308100c00c2c00c08211541750413203144001c0c0614907040c800301302105681072005001c5a000c800c014101c5521100c21440402e100200c2c94000580540c010004c43c01076400e910314800301c40314007000e840c0c81d00803507080c40e440490301d605000d4800c2100e0010000412083c2c0c001030b006500d4000210618011031044054620b004801400c09400318441d1005c5c41040c0c256034504018880540c0c0c100c601804058406108100142e5840783d244d4050203c03000c0840300f191518a0102c0c91490202e031404401e18564220f903000e6a500301040165801503113424099001044910503003a1402087c418800d07003400d04610701043c5403030400755182200310aa0046c0d541c0c030001110040c0040040c00d410000c07000600c0c802c0c10700d400091100d4014030a841c498040007410765071072074262a01c036020720005d803940b66184140e0b00300500348174481e01040b80310710310b030103a50301032032034424482d03a0a03c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 694130998 1250 694129748 694129753
    0xb040b090a0b150f0703090509130f06020408030a0e10080f0a05040f2a1401210f0603030c05070b04030b010303031a0a08150a022110090507030204030b06040b03 71
    0x1c0320000440028a01411aa41c00110f80c00b100c590025030040142265440400d40c0342e5a0341190400801e02c4002d5009688079510070300900c0a002187d40200c0c00c0b41d90030811035420000c4a18103803000303118070340c0441114080810300d50000d5400050100c41d490f42070700e8407050101041c40481d5044812070396401c090740624080b9642e10f0a42c0e01c110760192040c1c68141922050741c0b03c80700c0900713004209054001040340840c824003180440e2000419011001c034581010542c0040c02c4100c000300c40301c030125001f81c01d2303900e80d050b160451412400011000c010054890038003c01c0244850001c0d90035100ba00000a2020007007030071139044a80104e1001030590070f640d021005404613086031001d00b4000c800b802142e6440400450040c01c6104c004c20500d80c50011484e280000140503e95003403040c05424400306502e09442031280c8044013800584c0e4a082110405034915004018018501420001d6090b019802070082d81d00410104546940b00750030001900c044062103134254 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 694132248 1250 694130998 694131001
    0x5040f0f0b0426060103142a04090609210813030e040b010c06110301060f08090601030b040f2a080c0a0506180301050a0219050a021504080c0613060b040b09 69
    0x1405034140603c50800d41100242500100b81ea00700e01e8203030207800c1542d004010b4011112009001c00049021a00445441900b040c001c031217880100720024040d8041c80e1140d402e0801c10185910010350a079102c0140c02d140c0001c240e0310b00c0e00b1840a01e01c60301280c0b0307080202c2d031010b8901651000071a4142e80e041d18011082007400050a88a50001d061181c850b000d400050402c1c0200c42c9001c00c0c4103001c0307842c2d6140100c002c000e002500c000740c1c184081c1000f0f04c0900400031440b1415030743c0020012556443e103203415103201140c000045c120305504241030140c03861011029030784140305650448829103840310f0f41d80328840740c0b0303c0715400342050f1800c01040c01d0800180203c485002d110214405400c0b01283c00d5030000c458007840c01c0d9000030b003a143c19030381c0215080c2c00c7c031003850454100002c03c0b502941c0c40c48104450765507603d0380300c00682000300c0308040300c11488101050f18980d0402d030480b80c00402c200d1008462260421100944a040c2442016081d000050240515 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 694133498 1250 694132248 694132259
    0x1308060a1401030b0403121107050d02120f0f09060f0c010b0a15080f0a111204050d05040f030807170703030e07090c0e0105180a0608240906090a1b05040f0f0b04 71
    0x104440c0d80800071f004c0d407a5080d8200c003500701d101400c5801e0051000d014410a00c0c07500a003004003400d0000b803407441c103103c541c2c03480f8408829108215151649169101c001e100014414047c80040ea080c02100144c0d54419040c107420041c00342c4801d40c2c59a01d01c945401044007024103100800d40011000c01c000b902c2103043d81e842c103802042c0740500140384546010f1340b00007540803252800521980310248020410200410070380c014140c9402d0b4140743c1048842c0c0d00864440c40054034042c0301007002024016600241a040f070b8103d040c543d920946840c1c00350103080c455001c0001801844400900d0034401c4c000c10381d0481c0c00c0c1d500e0600b0061960019622904014410303401051340003401c3e081a1543c0d03040c50080e003001d4403100c81e50303d008000040900d0b100e52511038410300442c111642600c810060541100c021143e4501664039461001c000f0004040b4002e4040450320000d0145500b150090081d05c000325000306503e40c8559400d10741c04100c1c8108410342c60204000c004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 694134748 1250 694133498 694133507
    0xf0d141306051302030316051203040c180b130f0506030a050d030e030c010c081605040303090918060c030b0102151014130608010204150f0e151308060a1401030b0403 73
    0x14403c601100340803021001d50003103480c5403c0b400780c8001002d100144101805000c000394001480444085841c43c50a543c50200104003840323100220a0408524004440d20380c0046041c100c01a00a1644010102401002d00845060800510f00d071102203420782c280410103400c2186c1206c010b28001c81c24801c2103004052030b50014417180004d00c002c401c000400c0c041c9031404000c60f42c0d00711141c24901901104032840340152014000704100c2000041d400c14156000c966040c01c0000380c104c1c3c4804001e04048000100410b00f0389041201c190581e09a80410f8495101f039086609440c84001c001c0c000b20004d4aa03444d0620700400304010741503840c603a440080c10042c11008030b80c0e107604512016100550030120b156500420300f801419a6600385070400485460043c015107035445001c0d02c49a044483c2c540215690785000030181903244c210740d20041d6011030030807020355505205e5115401601d00c11002800c218000c404440803031b0a01d8141c98015807a2001d9840302c0c1d4040e50b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 694135998 1250 694134748 694134751
    0xf0b09150a090203100303033e04150908010f200705031c140a0501240203041814010503010b0a060809070515091206010f0b0f0c030f0d14130605 64
    0x194022401c1002084205007400074601641c5205610345040c2e045180c081c0980701c413030814880306540042507162003c0da103000404002c5000e40081e6025800b17854000c81486190415400d410b41032098003610f9520100b00400c81c0d0b00d68000f000400c089810b100283c6009001c00000181d03190070346005002000024a42c1d00d01c1442200e160081c9250340d0341040048408a07150550b5500380c1e11040c40354807000320341c0601c0c90b039001c1200c0d40c1803081218200e240b082400c0007000440c911552303414002c1045802034480f200307407009408540c3da1500007425420b0042030403034120500000c3c2c1810140540c00340c0c040000d0880c0301c060700340f0008540d1a8801004968a4407a22800141e20384510088020038a064a0b00e1941c424954083c003074445c3c0055001207503580610010008802c801030040d06a5080914156984801c0ca138000a03901070ba8200302080d0000281c9001e130307124040000c06440c01c0410b802d0040c89a80c0e203842092020032558046407200328006000003403110750005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 694137248 1250 694135998 694136041
    0x90103020309160b0304060b0d031b170301090b0a080f0606190b030703060e0f0103171e0a02061e04050604060e190602131e1502150c07060f0b09 64
    0x103c0c884041c07a55100c100b120309600804d009040001800140b05260181c15503400d41644c0550700f8600d1580c0c001c041000308204a10b20f050414509002c01c406421080c000320164007840761a561a00c040300001d000e04002540b14400a2400042c044400700c0e000c0384072980b0202a20040e40d40d1818000481b282c0211f0600c541100200420481c41030006075010300e01c141c0d400511941041c140c25a01e071005450441800b0f400e400410000312036013240c0032a020b0070b048081d2120312030002c00c0c584101101c8924540800480c250703d001d603002500c05e2084050100c0c3c5044403103854110745401c182030382c1c0689903411260000c4d01090311034104150342d02c080c50407681034040203081d0502c1d05402c43d404446854000a0a15056402c20300703030700141c00140c1700034504003849203018011b00214802c0316038100400f5414101c00c0d0090002000041c00d9081c0300c55035207007080848c1c100c1d0344041c9003180c00501d444070600c030280040c4201400140050041020f40e15104000070404c4040c4c00d80c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 694138498 1250 694137248 694137253
    0xb0a0c020a05070902090424090209010e09090606090c070c05060a050705240907080a020d140601170105161b1e242304030e0d050607180b090103020309 67
    0x1440c00050b810071080300200001c540044e1552200700c100820303540800c181d00100b0524030303441c00c4268516003604040388c80c10100180d0300e000440060310080103841040e0303800010441080b0040001084c090300c40ea5084551509a545446044200e4050942c025140c03010f400e00c188018104000208140405810b040d4100700d070594600e0310303101d941100003101038021991503900d5510a0b0040d44c200c8100d101420066003044c090aa50f20a00d82021780715000c2446c541c0188040c2c080e80d82000c581c02c00c00c1e03a04a41c0c441a103d00d0f0b445406200f01078640c0780c400001c007101c8840c0c0d005201e54001e666a0441030b04c010741c10100b00c201407082601d40c0300048035503c0551b80c01507030800c4158071565803010300130195098141d02402007508904030034182503e000c0030148004644198400c000a0709955468505044460681305100c40703411031640400c0c401800400103c441c4201c07001c4e0384480303007070034042c45210300d9004070b1085101825003808609001d6000382c02650344441101e08 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 694139748 1250 694138498 694138513
    0x9082a071e0e150f01090506090910050a030507140907090b031b03010f1d01060f1b050109080912210703050c01061d0a020a05030f062103040801180b0a0c02 69
    0x40034444050705580103400d50030041001483c604000400f414600e0007400c01d181110b19110106400384200c2005078860740980c00007800c0e01c2e0301c0d48a131201034540036105a88440e02ca01d071103540e80019000b030f2a0400340300010ba281c14540380340b28910591007681c80d03c280d2880d001e0070700c16035000a010f040000009845080d9031000690145008220070a03000c00d00c00e1500300d40342c2c010b02402030722a5070714080d90018401c0075003020018800480c9850950451000c10030b4800440c03d034920001c0040d402e102070f103410b0040b9080a030110b008210384441c210841c5248196030f072820f0302c41e548804110b4a00c2039002c0f000c0e03480075014042c00390a10901d00b1841403604c81c21102290014034a00c090b5540940b01e1074414800643d008941400442c80d2400e603c0c2d000d041404000c1c4807071111240714002550a841d203154000c030508100081003200008500846c1c0c60750454003c11485600c3d1803010742c1c4100ca445207207048960008581c00094440c02510005000c05950031000d6120b40361 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 694140998 1250 694139748 694139759
    0xb0d0908092d0301090816081606060306270b0907030219060305100e0c0d02040e040f1b0b030a0b010908070f0306060504020a020309040c030b0409082a071e 69
    0xd60718040030302d040000701c01c4107040300d00d81400e840c00070340300b034080da14040c074950014041c142102c0c800382c510701c1aa400081c05180c4403565204411601c02c8000c10b402080707081210981142056a1140005000d0b00842050a10784c000c94070906c2a8611191603c203c04206030241c9580c0062a5200b0340e1035160301c0340c000c03449020615158406a1802403010462564140f00340790300b01c00c031100800041c038035142c200d0300ca054003c1d1025640c407600054003841440140e0444001f00800c014140c06813401d41172000285070001020380380712409404228800c0d42c0e00780c080b01a62103601d0500c1c1540c4404e1404001090306460450500c2000c075000708004000300071600c005c0c0031058a01c6d035840d0461809009603101c40d4000c901a5006120758001260044181c440c40f105c251800148000785240440242c020902c6498019140c280f1050038130030901d0082225144400a5954840395804402882034854040c4821600a16000e10400d18000d070190a01d00c00c6000340d4800c1503c0740c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 694142248 1250 694140998 694141009
    0x80c0109080702030c0405100314070906080a1101080603030f0d0e06011509050f010c060e010b100f14040f030f051f0501080607021c030209010309060e070e100b0d090809 75
    0x31402900d41d050046008821441d040002110248041e10103100c1404c2c81c40740300c000000366010041201314050361315281c0860070464180149000340e42486420740e02c1300002d464100c02c09064851114100c0c00c100154041e0322440e024480160040d4035020baa091245141d42022008406054031007480c2d9560344c004100303180c081d00715451000410224004042c000791215030140e40200304420b241c03aa81c0ea04402100c1c1000d401240104100c041089010300622a0f401c008e41d111050841da21901640001003880a120b5a102c00703441559490416950f030080344101c100f0301607900c80505c006906013060b020700911400840c0c80701c0560f2031501d4802d0454807103d81103e07036540010401c0b444100610340d044601ca0000d0010242d04422062005510750800070038103030002800c6141d80d120b0f501c000225a04a10108011203c0c1d92186845a00510642c4201103901000c0340a90ba040200c41c411100c0701c160040c075150344c1c00c4850007c1d01c1000d81c142d40c281d87c1844504400c0c0c551 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 694143498 1250 694142248 694142261
    0x1020c030a0b011e0f060c0f050601170708070b030114010504030c090504020a0b0909071d120a03090503030a0f0c0204110706051006030c020606041109060c030c07060f021009080c01 80
    0x14000c2291190f041001403404c001d02c10070141030b04c14480000308225418040e1440c191038041c540481101c0780d50500403001c070031082d8001c10510609000048114514245100800c0040d064640b00c0d071740c07001015990352460080c40030304a4104010080c0303801048900107107450604000c0d081681e41e0f161a60403180e43c0d8001000039445104010031454186210340281200c1801c2d03504040d0b951000c41c5000c0402400c18040c00100200d85000040943c2c88000d4010010103040401202d00e10045d00c691264034100d000c250042c3d0301084514000c000d03110040300075600d40180d040d441d441194802c40250041c6d030410b42d50780b241c0700e00c0600034004020740c0340a03410100c0c07103041499208402d20b000d035111504240c03030040b020181300c1e4003042250308494221004141500e900070003061900c10b02c040d503640324a0001e00320040a40100252001c8048a01501c0d5000e0f45d8440036565642d0f005110300040c5c02c01040c07021545203984c06028032354007030740040b810700c14100c50460071981c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 694144748 1250 694143498 694143503
    0x7020102160902250f150e03181207080d0f05090a0603020a02060702030406090306050a0b06120403141e03091f0b0922150f0c0905100807021b01020c030a 68
    0xc00181034207001c000a984403640138400d40c40c400001c90f031a181d007980b1180fa280000d040c000395401e010715812880e00007030705000b007000c10340ba951403130090f18135200401d004240e800344009540f04240c9020206006044501781d00181812075440c140c101e61491814600500303004051141e5095030b02c82d0010a07020308080c0e10010703900c450004c80685041401009038085500802003407104680c005820390441c0e034001d5011615403591b90759400505440381342142c000101160440201a40d24062030142c0e0190700c070000d16013509900001039220301030702840c101008118245564114000455000030198151800d4541d107401c1c041204041e404000c40351919041807650601d0500d01841c4c0000c0d8040700040080741c0002e1140d846a481c0502070890600c408000d9000c1400d41c226402d41c100c4544100181403c0680c09442c64020b801a980a103000c00c01007d00d8602400c0141d000703030303100c3d0000c003130f0441c0c014504d245846c03e2200d1941103000d80b17113000d441c0e078034104854244030f403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 694145998 1250 694144748 694144751
    0x70507030225170607050d1a0907031d060103050a0b0406150801060f0f051f050f0d0507270905060a031b080115031505040c15030b01021e06010b070201021609 70
    0xb440c0200c80441c0642c8020f9214003a04504140b21284d60080e00700c480c542c03030301c200108040340381a140891641d1500e100c80d800c4a902c904000c1425416130000701110002c41169401941540400c4d41c0d0b20024040102940d00102241c000702c0c2c010a03666034040e01c121000716414140941c0403089041c02d82c0304c464260b440342c0c4144408090310400318040c003030f200211440c042c07030480040c0d45d508803040d41048a10024410140c2e16110340202c030008001004400d69964400441c2401003400f100c0c4140000c11001344001c05900d000d2585002e12000042031135000e0409049000510000e01015402540c00400100050300c0c00c484128516141050b8114549004019425600c0c10030404102c442c6904040c0000b0b500f6800c40e1103842030384000021a903480740b4050402080c5500316a1520041041c12100298543c111114201c400e90a81d03c0d541c03140080941110b004000e0382441d50802c200501c1030012881c00381c4980d600500c1220068040070681841c0090260010010607 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 694147248 1250 694145998 694146073
    0x5030706092d08030c0405060a0e04050c0304080315031903050711060c07031115070506070f0806130207050a0f0f30080402010c05100209040b0f06030705070302 71
    0x11804420b100c44458a080340c658003402003082c080402802000014880440400412070000c544002e59015010246c01d80c2ea4803070043c43c016200c61101c8000301c0c4a1410700000684c012840000d90707000f07990210000e82513499100140c10458078244c031082e0103109483e0540403800000c074584000600a4a90643d94070310707410000c1e19000025611f9009290800000b080c1c4040002d00000310390708610102d110031825400a1180001c50584100808000c111941800300100704039000d05903c0e00c440c10741c2e18179140159040b4008413a401da0180062030500300c41060742e0014283e2920400a4500114103595802c60403040140d0039521082180740c003104108041c079603500108200519580c40741e502d24049004418030b0b051210422424902042c1164020010104515800016074401c080c562036944c0081d0050081648075130708054034080b05040c188500710f561140500303410b20710b985650007075605a0000c5001c80841c400c0882d4072048850460300d084043c8084000c01050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 694148498 1250 694147248 694147253
    0xf021e0d0e19050c0603070c080309010e122d0d02160c0b041d09030a030c0219030e0f0d08070b041704060203090405090d171009060b03010609241b0503070609 70
    0x4c03c800059110b014400030414401c02c507400200c1089080d6001c45034650780da803041d035541c0c0900699a0805900d208504404840c0403842c40981039402402c0b101c514103e04417086200345c04040300c08040340c02c1c0200100d44004400d500201440d01041080b04401300d1071303a541c4c0707601056a0f0b00c1a040c01201007000c6c00912407803591859010280401440c6a08091403090703103e10450194409056441c414400b02c54000e01058090041c980c4409101d0120b504000e080451410030b05c912400f00569103004078603140703401822042d0440203103070500c2001d5859404035803024005407800e00c0640035108170034205600510180034594040c2d42c480c05a4824001900d030003070103c10341900034138145111594480045070101900c900442007d495207150101594807580010002d0750030200007094100c1000010740c1210f030259154402c0b91307660b58030328021041c90400030007030f182c55000c00c40b83e0750711805100301c0c3c003500980c145060040c141c2da4649968802002212565120b4034117806 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 694149748 1250 694148498 694148503
    0x703050f0a022a07090e12040909030e0907080115050c0304090e0c030a0615050f100f050f13050909061603090512271912050c030105010f08010f021e0d0e1905 70
    0x106a06d00045c46403204428070a1003501a9000d061500780e610180794003418071541021450050142401c086820003203001448000d0034080c0850340e0803440c0140303440d184078004981140003010301860070141070002d0301005e081200c3c1000c00ca031151744045909a64284100040c8602c641000140f000e045c21135440c107002e00c0c2e840350b84200c0460590000c280c403aa18032100a10301841c05210107802100c003a62a4022141c11104540700801d40580b9460001001800c0c0c6500b294452040c2d1754110080d55199070032a010042054a041d015062034000e0300400803092091003900c2440019130f030480c0c01604440c200800b02c01880400c1c4ea04858001a2b10192041c20786501d19614201000c6448100aa2049074442c0f6580e0145005105050140d0215280c00070000d01c07a0f540c0d603071040d069848040c00342904035403811502501c15042882290221441d680510b4810050740c51500706a0304001000e404290300ca10010f01864002d01555140005401b13500d000782c0c1141c2081031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 694150998 1250 694149748 694149761
    0x150f0f01051e010f090e010801090204060b160b0c090925020d080606090d08040e041e020a0e062e0f0201020906091512010e07080703050f0a022a0709 66
    0x80c0640904880a1054101042c01074030000082c00c20000e8800d81c400308440041c41741c1c2c458070021403984004a80241d064202100c41802150244109031b00c0d500186101d22400380c0407040c880c0203032860360024010709203895000a5102d9200d0410002c00049480c0c5403040321400d071508420548205c125030318034500040440039100030104030180601c0a031009001420b206c3c8031707041c0440c1e240d049544d1610580b042c070354458104d523240d0b03a4a10304005c0d2440c068608641001900d00d803104115040b009120340ea0b50014141d0704e0191404481901c0040c0142c141070300310404452540c07000708080c911225030340031070303800c1942c044c0c4c0803100030000c041045200b0700310390041062280c0c07036460340203403208480202c03801e0040340307414190f1817000e109000380340404040c40740c0000342681c0c00c11078031885007034a5140c4010699880d403085080314030403120004000a0240803e41d00c1c040c0e035000d0b0803051100d0040210202440c070039a4000c1101955a00346540182402e0080d04014050b85 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 694152248 1250 694150998 694151009
    0x8031c06060c12050c10020705210c2a0409050c0a0f06140a23120c0313140c0d0c1d0603060103030309060f140a0c1b06020c150f0f01 59
    0x514020090f5682e40d00301c500840812030801002240d244007802c0305120303240da040681c41c1c08550ba4000c902c0e2080d150a8031118407400ca4840e0b10081d00b100d1101021500140303481c40240250312444065a07a07000304804c80701c0c8200019102c2c0654503110f40c8542000300d40614004d0031001e42d000100208540c4642180c0d078030952241e01040003581100c6541c0c00e0341c00115626844041011044440001d1204041c030740903070396038014542a0740d100c01001c002d000d52104014595031426818024802641c0004c2c0401c140c011001c0403804201c0003c0c1c00f20102c4050760b04000d45040042c054201c0c8140584042400000801c4410200c80880c6000720b00681414060f140000020340c407418140301c05814561038412600820226500241e000101c6a01c100201d84100c1c500421061040316a00075140c0b40210f81c01344203020b0f80545a51707203005120300001038641c0d5101d101a401000105016104190482c0410740d0116402c91184550740c4040b1650700d030000500c01040e0341a40007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 694153498 1250 694152248 694152257
    0x6071112010b0f04050c09151909050901030f0201030f02040609091401050916050409140a0f0603080306130902040501090e07061b0b180a061d06101202010908031c0606 74
    0x2c405500c418402c0d0903500d0045900050a5540f514000f84621620003ca540b1101c64600d001003501e150010b4542d0925100c0010108600d01c0d07010748000b072040c05000c1c1d00030440340040000400c41102100440d01c18940400c0020047c42140c0c2079800a0700030f040031400750345040c82400d440e4403600e05890005c04403615203502d08030204050303a0028080e46005d001c40d200b03203000c1601035000c607001030248007070420104203031003000302000d00c0035602d40c00d0749410602050300d039100340c0c00382805490700f08480500d9512090100b0000c00f501c07010500720b41d07854228140c050380d26442218020020608041541544604c082c0e01744461070708410148260965002440501c002088485c103600201100058558003410a401d00e46a104050310703100c0c441200e000c0112030f40204a020a003d074848034502c00300f540d829141c1c003044891003001741d080d040420005580a4103088000d00604000d10310310f4444d10305508540c4495071540e40c080214511304249038180c800c0d1030040281d803a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 694154748 1250 694153498 694153511
    0xb030d03090b0a1107050d08070906031b03020904090b0129040b040b03040201050910120606090b030415090b0708041a040f0609020f0a03290601120c0c020607111201 73
    0x71031002c0d402c40a403804082503540d000300001031000e07004441a4a81040441e60140d4091100034807500d000c0700c0c1c00000580a00000407518007a0183c0d10024000d038410010581d0b0103881200250003490340303a41d0103a00d41c583c81001c20700302c00d1003038060408103540522602d008d500f1413140c0c070400c3c01c00410103941003000300044120a01504c0c01e482444404960300c0c1c50302c0c0012501402000440e0f6400441e13a98440b121a1700a10a05103103688010300788140350b030712901076034a44e00b00d108400041e54100300090005500b50104801091404400504004070761900031700c0303110450300d10001c10040310911040c4005a0450030502a5003140c1b06540e24090b952140500c0c1205001410280c44004000455039401200d0412520180122502030b41e030382030159a80d4034840030900160403031901c41601c0600c160100748034800c10307114182e1b64607500402000a1050303108030410000c000b800c040050361010010a070450048807100c00092449082004113001c55850550b260b25102 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 694155998 1250 694154748 694154753
    0xa05100207090c0311030705120c09030a0f06020c19110a060e0609030c060c24100302120c130c0e010306062f010e030304031704030203032e03060b030d0309 69
    0x181c41095410941c1e01290140c000c80e02030307002c5c0000e90008403200b5004003c2000c4194004050409a0540c40e85407403541c03917400c0d804015110b00007905070140c110800b820045410149030010f958411000113141840a40742c00b030511206110707043e41c4255050014051048090303129040a03800c46000c45690300d440006002c414411198900410b4007198006995400b4000c00100900180c07030703140e8954003400d051740c0314040c80d42014419040320080c084244508504d00703215020071f40c035098250b0b0954080120008805a807500d05210341e140c0980152038019020788403200d01140410001c4811802414213000306c40c2c0641010710b0080d0030060f030b9a01510b41850403084032801c2c0044c0420340061601011618542c000c5582015070201004030000001e511071030003a522603655400b0300210502414045d01e000c1c0c0140c0c07050010840301e2180c00c0040801c200d9080f140641d024000640c01081041540b05443c0d15a5810b00700c59107083c28401c002201d011460100101d04184d07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 694157248 1250 694155998 694156003
    0x30d080f19020d0614130603080a11031b1c11060606130305030f0310120f030e0409050a140111090d1b05060c0d0e0907020a0b150a03030306050a051002 67
    0x5112010007010101001144007941d41154035007045100240207098035103690115841c074a1151900403a014420441081c0080c811502a65400a911072400e803c81a00711b43e94408410250014001000000c42c5102c05a070082098040c00700902000b0303c001110000c00c10188014406001d0b101d44010b48200c40440d25a500c4501282d005072241094020030082c6c0650741c000a1281c4000640d0302000d005000207188a5140150340c2e501a41d1a844103084c0f048000350014041c032080c050300350019001d000740c070243e00405000098004025100da5143c08242030781a9000c410100031000410420b00a40315216140c807a824685100d00011940d442e205c43c8019144c000c040c1462881c910000c8142c0006181c0280011b4507000582400f6840b02c4045150030003140a8541ca8552404c0500b83e413445003009801502c0300740d019445d0524084401400818039007d08035084005039581460b41000e54020b603400558103007000180455100d182e00b00c2031181d841000580c40c1d49a00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 694158498 1250 694157248 694157251
    0x1b0f1725080d020c0a05010c020102070213020f070b04030c0b0f060a050603192405010f05040306180b0c271f030b0409031e1103090409110915030d080f 67
    0x24400384a40602400c02488a019111015040c64000035410058007400140d9007980c80c018030003002406420398080e4200d02c101d020094001d100c003a0204100740306d03a400341c8000301120a00515100e51075540182501c0c1c00c83c2e04038081040880b03a030b018409680905c550200141c20411024107003400000e180c8086841070620a5030001f000500c40404003e4803042c1034400d6070180142000c05446034402140390342c40001845195400080642c0b01d8501c0d0220800d880d192039141c01c1c00c54880002618080107021268544001072000150080310080e00c5101c039101402d44a6501003d00303100001014003114690b4403400244040f030b5501e40e16203c0ca55501c040a1800054105069000d090000e00c540d034451b01d8003190005050308008a41d070034034440908085030142e142816140c840010340080d10301d50040c0820961401c0650041d503080340a91100460486514000b5541c03410803112001c00d031001c14102c4106080c10400f005024200303003010b00c410b1030f0050090040250 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 694159748 1250 694158498 694158547
    0x7031214010803160201020312010e073b010e03070e06030f070302101116090c03050c0310032604080d1119022e08180a030206010b0a1b0f17 62
    0x4d62007810216802041201c3c04c0000c905074100c04c0d5a90307414545c10000040b00e10780b02107200b0620001d4501440c00d24038882c50755410302c1c0c41000d044134002d0103111481c003070241d050040c03500742d103051560204102c000901200b0704480301450600145810002004502c074000d80c012103003840160340c0e41c0b0200007074501601d07003441c80c1100007a070545000c225117080352a400c0c1409000c41c20006d2600849414820b81d2414403203034035860780c0d030070030343c4003c5a1480b0a015248030034800280030118200350010a850803002c05424010000480d5025512418140c0c0c8582020700c10103400c80211010b4103d030201038030304000c070030500584030380c01c42c00000c0c49501d80e1032208000e09942e400170744c07400c4a04065418000500a00070307140d5031003510902c941c1e226540760000c0c01c800c00140482000da0581c09080c1d10b91809a54840c1900a46111402d1128840e1102e080542062a501c50702d401000f021170014141c1c00c0c42104100d85094042058008000b0940d141d0100c8038840440031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 694160998 1250 694159748 694159777
    0x14010f0b2202070c0b0417010612080a0f030605030714191d09120705060f16020717030c01021c0c080402060a0815040e0a02131427010207031214010803 67
    0x180c42c640507004c21000c1e00400b074100303400b01e40421003501403103a04134100001c0c0c00801c20b00f03458026603000c2010510000300b00d040104081c440280c85015030b201440918100400c0d1245c86000203401d00145400401c2e20908001c01500b49142005602e141d0950015885c0000303410100f1600c0303600c0c1031108049a4417003c1020454107031040200209080041c000e1315102c0b486841c141b5141d6900303542039440e03c00390b0404610743c000c4e42080380e00300c42920707001458100e00e0103110380003091440061040a0205000c1400e41d800280002d0100c0018080038034810041a158002242c2c0d01030598000c0103403d5003000016110503084500c0d801c0c0d0790030040d40658600485a14070307010340318a9904a07080c0300591025000008400c201c0798030860340c45d1080900d4082e40403c03100f4410076146400c0e44803002c00d5800d00054095058003808814040309542c05007151800c1e42d00c550801c40003c0d800713482c0140314404034030914503110741580d000700c025454102d0b6140e603400b50104081d02c0d01d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 694162248 1250 694160998 694161007
    0x2071a04050301140612070501051b1603060203040b0108031303021c20010f030b06070f050a05030a18051008010e10031403090411070b070c06060314010f0b2202 71
    0x10891509540041c0390040080c8900f1118100d070207044042a01d4840c0115540e6054a0403c080803412005480b03041c0d5400b802c00b046042c180c20081d05001114919024500c10300c5049a04120711402840c01a100981d583c04d2031700e400f801c416070580c000c2010b50030a11a04100c08040c0d07170380000316034040300c000e142440b46160340f0310140c110381d40042c54600804c13404841c04007103603180901000240c85030503840008140607402d886513000c3d0507030b00010820040f40004c480440d22406030f801003003225030b00126551840d00c1c6a0024607220040741c60381da07001c12601c00340d01811001e0714055803443e038980d20360600030f08003d0040c000d000300141200300089845e1241c2c03c0ca40e00468200c5e040988040241c6520b81d200d0f404401d046002e0390400608005030161041191034160303020310b0b0040700c1c2d0f49031398049408500b1554100e1340301d0f44844d0300002160394141d0160000702c02070000075030042c484030b0010807101d42c268038170b00407201d18005402504a03c010701d00c2c0c0314151003001d81d1340d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 694163498 1250 694162248 694162289
    0x5060c13062a0c082d0d1407080913060302041112070e0319030903020f04110d022206081e070e04050c070f0515130209010603020c0c0a14010206160207 67
    0x25891076411040d0944201d4104802c03007450359100344088480110100f1000f171041e071201e0340f180c0315009024045180c200304400d070408040b0041075603600400f41581014802d00015941030026107240c0c2201ea00c503401442036103010b10070080d03009082c0d002c40f0b1801040703582500010310002d00003424001204918040e40c1c40c14010002800d2407114591660020b0b40740290182006000c10b0340144050054881241418401c2e00c400c40175401c44207086c0341e000005c00001e036102000140d00201039012020000c3c520306c4103003001c0c040540f00c800242c50140c100162010028a40c03d075080f20403014815601d4000f4902503103d1801d0f2800b060b02d0f604c0d001c0b070a003c1d108800f40244141102403c0c079090080105484140d62000300020b042e41d01d8407084443c480c000500f000e0740c0042503000400000d03000390b000b040b0480e0030400703aa201c244036200043e81c00351950b02110308140303080d510201d03d6a040c025203902450f401d100309040744c142400290f880180f4003550f030769201c2010440f0764 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 694164748 1250 694163498 694163513
    0x10082109010c021002010f05060405010311060a090f1211030a030f03240314120403080306010507021305042102070e15010917010c140c210705060c13062a 68
    0xb10b2075005000d0008544900070300038002c2056500ca2141179152001050b007600d0507014950489400c9001800107203401c4040060383e510070321003107081c44100c00b400a0700f03014032004071001b05408401c00c0e00d102854240240038000503c4d40c80e209410a030b14a00000f50810701c1322200702c43c2403030000380000b0801e070040b040a40804228904800080c8008104018542003a01c0554000d003035441540c10084c1980035401070f4000103010110070320005086503c24400741c818540002d1002d1400041042c14000301da0041d6000c0e603031400b0784030140807201d20380d03144101e03a0f0083c0c0c03005107600c0d403800740030f907000c920701600d8450760402c03070752b440c42c2aa03100b4020074019120031170541c00010208140ca80c001c0003100500004983c0f803005100b52440c2501c140c030075181d0008064140c048103600b40f545448484c41032040c8404040c80b4040100e402080003611842d80480d0f00b41c3c0d81d981c402c0f030308071100819034404401c020481282d003085402594040e04000303220780b00000c4a107451316000c207 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 694165998 1250 694164748 694164767
    0x8010b010c0b09010603050a060b030d0203030702070e10090911030d0c081e090901120b07050a05120a110705061008280201020c10051306030e0a030507021c03081008210901 76
    0xf411f910070140c441c1d041c0700559000002c030100450481c1c0300da20750413400303030703141c1c01b044070800056040524108440036070759030100d0303010002c2c0c40c0000d40140c40b00d8103070044031452807003611000413070741d0003074191b0a0400c0031549405060400300d2240c3e08a9842d1a0540318265400c81000b40e044807041014066009450706044001c154950660f181c2040c0050610040c8013920009619000702d0005801603007280d2224005550b002e240120803282d40f61400c4014150751040790780c172107001d4403246038030001d01126481030303010f0011424000034200100d14140c01500b00da40002e0340015051640e049074200000c410303400c0e10307544001c0340010b03800d21201c03c4d142c6800c42c01c0d0010290f030b000c2d40840206500d10250030305580f000d0f00c815044007158804407621513250702840520000c640204042c0c0400784c4014040540c100d45511103030080e070010707481100441c8010007030010500d034004400b40070b03104d01d600620300f100109407000142400e010b07202c21041c00000b40201143d1240b900d07603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 694167248 1250 694165998 694166003
    0x31906081b04270b07080f0117070302031c021018120315030b012102101206080d0806010906050a05040e19060b0a110f1203190501031101030608010b010c0b09010603 73
    0xd656030b1018100543c000881c9800440c1c611500000141402e40680d0160780075025160400420b80e0074601e0446030001d00c0e2001d0b5440e44a4245c3c000010f07581000712603100c2015030b16500806031028030192419030308001c5450b680b82030420303070a4240c1c09000105031080c2c02c41403456007001211001e4008000e0820742e40d5030b151b40c1d1040070090081c01100c00781210140c03001903d045280d020ba8400700e81d89040f0003540201d400740b041d03502e42d20501445100074044400020b40c5a5108489480c01107103600201c0494081c030204010303507810010800c01485c00e420410318004104000512511a502070f21080100000115220380310400c1803480d82081e001003084882d8545100317800340e40201082400041c4108800ca0700b034040803130701411840c44100280340420040c400c401c4c481e00014040c2d613040b200880c22a8038017005004c3c440c000c60103110140e01d0b640807000010107a860759040913007a03a0515030104ca451742d00000b060303c182c0e00300d50b441c3d000d521413a03001400b40c1503d5001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 694168498 1250 694167248 694167281
    0x10504090912121802010503190f0c081006020c09040305120403030f0605060c060604050a0e0d09030302120f0a11034e22080a05031906081b04 63
    0xc0000c001e140c0ca42c42c5080881503c64198203a1251a80d106031031a02842c100481d070b50000d04c200650054002c0c0d9001000c40c042480b850070401b4141c0c04407241c00c00b064079a140c49028003c0459003080d01b0300d0300207030700da06031004140c1060006076495a039030424034051030401d000070301418402d0040e40d0440c00c0d142d00d5000103003040d082c001c0141282942d6100c14a00e441e0740003c0c0d80c03034134400b215141d4900d60090701d41c2d130742e85504102c002c01c0000d1200301503907201c640e0142100d00c1801100784841c11b0b6140d0f181428198140240f404d104c00c0c5100461000c2041092542041401642c4041c0d060f49800100394490801c50390650252800c1f00c3d101520000301a0044201c800c0c480f0590f403c0312a89900746580440c2c1d0a050340310301000c00d0f02c0000c1c51030202e0f403e801014064910640e0107003840c503504000b43d482c0d05840c0c1c025403d00700003c5011051080b03d03140401e140d090703a9119001844400d081400742911148410340111404005030344042654035550400c601000c5c01070341 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 694169748 1250 694168498 694168511
    0x602040b0c010b1017060409080a050301060327021c051b03010b0607020a030f0f02060f030f09120a050a031103090a05240c0d0e0f010f06050f060a080601050409 71
    0x1031a661641003110901810b50909800c0364690501c2040c0b01e8440d40259545011000c000c20b50042940010340360a4100303232186046808034210000404c11032105a03130b8181d0740e6240c150004c0450781c0d03d0b038005000703120040d64100032411140e00c28a0f80d54044403140100101454507a192601c4110300500d5030081030b86030203103040048140c066403070341503000303018605606003040140d01c1b422030700a501c075100400a02c0032604e4259140d100324460031404801e4541c0d81c0000b01c441e000b58030a08450580003080140b82c180c140360203500429401c00404001c01c16500e004100d0040103c44000c1000206054881a120340c0060744100351064401d80d030b03410f20148250f02c8030350019051f20320744201101c007070f60034601c108031982d000c0300d03d00899000c1c2c581c00b240c8402c5074445d10038007040a0311240300302c0010300203212000807100c604000080c601c24000030340c01941e206c3e43c007961103424460902a801d407100d90840744510f106242c8000c4942c0d8410042c1e889009903002100755034075040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 694170998 1250 694169748 694169759
    0x130909080414030a0210081b040305071a0d09050709230a0b010c0b01141206070518060f031e011d15011b060f0f0504120e0109050607050c1c050721060204 68
    0x10b00702c40c0505104480c0100c90843c00c00008c0aa21a41c44001e00640c000701013001404002e100b0180780000c0c01060920f400104103c45040e6501040b040d90160003800080103200d040d4400e03c00c401051400d46038000d036010100d0b4001c03c900418140450b51148a50305050384114100005241d0000c915403c13542c5900301c205580b20401d45440c05101000300110f04500001070180c8109250340d2114030344070309103030803480502c10408501d81120051001c0e50801c11940c01851283c0f060a080e02c25586120706125500d60303060b4080304815052030410883d4001d010340302540a034401141903c2c000682c00100c03181821308905140b040c14941941041010582008000c0c05891030180301e4000000d441008481c402d450090811582a1001c03003668011881d8244801c0141444100e150f9100d000c14000d0340005c03000c0310280c01005040500349003c101c4120000011103000340341c0d40740b0341d5031140c0d01c070000d003e21004800031180341d941c92404465554411540b181c820b6441e141d540707 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 694172248 1250 694170998 694171007
    0x606040f0603051524130e09030a030c050906090904050a050a030f0206010905060f130e06091608030f090607050304150504090c08040b070509030304050303040308130909080414030a0210 82
    0x10b4544d4a00740a084859154910308004241d00c2d0400e1200102e040d422003094007500380d03203d08003e4840e250080c0001600d0120f1a030010300c600d00078400f866585500314401811a84200502c10901c0405c2c00042c0c41031b12900184c03050290103880700c1c1703101d4441d8280280790551480b4002c0c01d502c5184900340c20140c1c00104c2c09510b0342c0e55022180c0d076980b510300003030a542c4100c4a054205400c0900f65025207007502c0400c100664244002560000c0c0c240c2d1a41020030403a0084010341c8080884044051100411001004250061070a005100d403500e02240304142c1e2146c07040001280610078002c0c18000c503001461f4107000084602c0e11240c014042e03030031a1007072490342407811042d01d241c2402091540d10817a406020114544d684d000203407141e4101e040b42c950103100602001c01c080d00c04000410203140a0350101d516210411140c4882c6142c0360081040ba07810203a202c1c000452510a075804d64035003410b00a02244c0a03030110b8507003115050060f5101454071825410b45421 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 694173498 1250 694172248 694172251
    0x204140903090108160210021605160602300c2e06090915020a020a0b040605180a0f030e0f1801081011040302090c19030e06060f10080606040f060305 66
    0xc0c0c8420b03c0710354071000c1310041c04200000c1040940c2000c0350580349150160300914910b0809c0e04260400c50362529500c0c545285c1c2d51011042c84136847c0144406034040281c15144407802d50f160740c40d01d484401c05c40e90101c0c1000d81d08034003c004940b0360701c040001c0c01005202030010003101c4031b000140c0c01e41c41503110f00c94000ba030024640100480d00c0412409201c4200c0e4100d231400c4a081d02c60b00d0074400942c480c40c203007004c501070310742c48030f0004020802da940202e0098201103103d0030003a0022180805031900c04445078050400c420000e940004080f06940c0c040c200190322555060100300e0130030215500c240c1c4110b880d11400f940458185610341030b282038508a452188030080010111401030340c09906202040c0400c1005140109109038031500d2844a0f0b81000d8160143c03d040300c400c1c030300d10000710792250105c400c0e0340350130441c8592001c0d003114a00e4031844a40d000c1540e406d00c09409100308500c200c001340c21a25103208640040c81c0104c01080c2c0e55940d010024020b000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 694174748 1250 694173498 694173517
    0x62d180a0504061a060304170d24060c050703060905070b030c13050303180d2d050d02150703151509050915031f110310080c01020105010305030405010c0204140903 72
    0x2910703041c00f401040da440d02c80c80444014006a21b161160f4443e5016286140445d0f1a01e240810488240034580e000703001d80e142601d000d41c0c00744114040490108100c6400090400031260030100100b100001e032031040702e40200340000c0010960400343e08007600c54001c1c036203035007000082c440c00909170001001154185180420019241e504050f00c030701c1540c450070303190000c144120f4102d15017446e180d02c80500c2003503000c8031804400502540c20900b01c4c40051001d10007400c201c280182030144c042c0c0680c0b00c0c07028184082d200d0050000c01400a0b140302e0800d561000c001c59010400410034001d000c0b18401124130f03860422000345500d0841c065103000780480004035054058520313080542c0100100542200c001825103d40c0203840c440640c2c41880c0c94110324011030310030000440c0564043e03c040e060040c00c102c00c1e87d1910b50800c0702c85045a1502c001000402c4010051360143c0b403003480d182480540c18000140980380c0480d00842c4051118103020500c080000205070381413 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 694175998 1250 694174748 694174751
    0xc031c0c0501110408160503100209010c060f021e09060304030503070c23210f0304020d0f061506080708160905131a03030c0304090203041a0f01050405062d180a050406 74
    0x70620b003001ba0203c40030322910f90954013402040c0c41503000c68014000d07850303061400780c1841500380c46d96400e8820014200d944107600150404100e40304a020240c5010106110f80c41c101c2130340046005440014009001c0010101c041005248512440d25003913421a00c00c3c00790b8982c3c17220b4244030040e1026009420300c25000b2410716000344103003800e04089401011400c0494110700f10752550701c01403049900214084142d40000c1954205108507400381070001280c05581203041885005034003d00280006d100030010700c554844082c03a404002e140e4400d403009a950001d40e140145034101c20780c801d01c807401c2c03000360000e82c2e40503090812840c6012411a1040405d01d078a900c1216001200c6400411003402102d0a540084d40c04c58403c14001c45040000549100d200d00152241c094040501c00104060314150043c203402410440d80c41903204074401c07501d400300d1204041d803410710248081902c855640c4003540d800c0017048004010041c54150301600040c40111012215603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 694177248 1250 694175998 694176013
    0xe1c030506040608031210411f030b150d0b150f031902121504050c0a201e06090a030806040b040906060b13080c031c0c0501110408 58
    0x91600d0f00403901101c07090300156141500c1c14019854a0794000c00c2a00400904040007503c2403024401224a4140181020907410030b402040705400b0b50900d822120a1001c600301e07402d40d50000d10010b420200503110303000403640101940984095000c0552100c0c40d1149504070100c00c8009040b1012400d03000c01860040700100a16000590300d4000b60303050501007032000c006114011074003d100440340c03480c01d550543e10707402039900c1074031101d540c540901c05000c0150496400c0070080b010850303042c0700700d140000902d045070040f9841c5504002e40e4000501c1b50740d0441c0c1d0000c4d00c040c0d21030242c4d4490408644160407881001c07003420118801c0d01d000800c490004160091180d80c035030b80e15400360310741d01c1c1044054550300c0c0e40c031580310f076a4113503107000542d80e48180345c0100346050034992985201400301040568a03403013481c00380c100c81480c5a445e81c0c00708030740da908c101c80c0d6502120104010785c1200c0c042c54a041c0241290320f4100200551800706000c0d2044170300d14030403078428 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 694178498 1250 694177248 694177261
    0x110705060a110306190308070f060f0905121602090a0207030909020a0c02010309020102190507060e061c090c0e090703061d0706080c0c100c0f020d170a0e1c0305 71
    0x40b10000d0a181210700001d10100d012454902018401c40c049501c030043c91070340341d0b107803002c0a40c0318040c2146c00f1040b076940d00c0100012402886110740400f2006c100010031a12034540780c5c14030300c41101d000c1d83c2c00120451428a4101a00d09142d00505001ea803450007100c04002580210030660220302c81c00e6002404140342d0003103442160155581c051680c200e9401507004d844d03640402c81c15070050b401c2115444010071100c4114038000c000910703030686041005009521aa1100ca010720ba0400640403020f000e0b290340c3c03101210b6004002800700480c20a1915120140c210b906982c03c04400c0c0043e043e030004540e01568006d9408020311b400c0d410712041d90161030009414181c000a50801415000c1c0c015544e22500c1c0640e0907142c000c0c2007118a0409441100c80004a541d41c0401f0010651140415052800c0c5000814600103104000342c8100701010961001250690000d140c000301ca070414195140140101d411482400c0305e03a10041d0943c2504100291400000a0781d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 694179748 1250 694178498 694178501
    0x601020c12012d0b270705070f032007050d0b10030c0305070e0c0c06060108071b031808010203040b0c130302101d03031819080a03210506060306041806110705060a 72
    0x604129080394114040081c003900d1703142160080400e014030070180485004101142d8261150600c6580c48260701080341d6001c2d40804a0f4180b80007071544120410f01c099143c01082070341e100e400612005955036a4000e0b0030403140c25810050900044400000401a002491406481c604840110075580310300500340e035405100a044410b41c00b05000c02c1e0194095440700341c10051504c1e1010303502d2200020310790f407080c0300f000484c00190505c2d40021017010640f0000e0280005000962071820a515569138107640a4400f0450f980c000401e04080c1c2d59400700c8800031580544008001c1124542c0030307100380500140318032280e40389040121305103004411074002e170078102c1424800c480307003070f0034802d6002503140038601d41c100c90030000c1002841040500c150074401d907554540e1280c0f107a5040854a000035000e107419040106001c0030b03941d50800d595021805407000905048990400c1c043c100d10440080d10300c0e458010340d481001246001801081c1c0604110340c3c480d141d02d4036680 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 694180998 1250 694179748 694179769
    0x3060b0418020613030b0112020108010504021620030709020408010516020d03020a0c0606030c0513050f060d08070c06021c091503091b060206060103140601020c12012d0b 75
    0x400c480e5076110580c0042c5070007000741500d245280c0d8054102900c83c0d4403560000800e800c05210410000034030011503038810388460241006036015030422400c403000b10085504990024400c429011400ca540360140d1302c180c5086500500f110055941d030b5080070000e5115024030b840d01d500f80800540700c2d009413201c140c02c4072020780c020040410380302c030100e0094210001c48401c010342d48045901081c1d5a0180c040a1070294180100c00c038030740810490558680328880c800607003403004115164140b4200c3c140c0c4082c0036036210040359840d25144031148100c210003400c040100710302140c95580000c0620301c0f2190503c050b401c4a074001d50644240080f4440c030203100f138102c1c042c2110903119400c00080140f20341d450340d81c0c100d00e01d511004010060382140c40107a00c03400400c019503905014140e402421100c4100d618180b8400003902c031040c0c2381c0064028000c0040c03003001c030402584918030380c0304081c0701d02c110548045184c0f0307448605c11550410480c00c04095940e40c1c90505501c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 694182248 1250 694180998 694181021
    0x5060a0207061d151003061b0e0a0312031e05150114070c090209030312071d0a03030509120f0a0302060103020406091b1101020f0a0e090709081e0a080c060103060b04 73
    0x3494900301010412111400041040c43c0c0c1e01d01e031718000800540640108200d21006203d448400d0608440051120004249051050000c02e0040000c550340b908a171038585014030340820038121140c01d8005421800b070b03d08141d01c0c5400200841c0b040c1161341072f00820000d07a120402c031001191114500c0c050350030050800404a0304c1008000050b5006001706c18002d0705585c1402086406903171030f00000c544002c04912101552188134905014402090320201d80d0080e03c0703401c40d01c0003060350062080d00da020b20365661040c2c14a0004125180c40140d45900301d84e0408441e00d4029184c50003071100300d00075410f1030701c0030400804500414462800f2005140b490080c0d0303003812035185200b1311590744255402c0003691200158003006015044007600d030303050042d03605804d021074044010403500400c0031f00641072241a80c04909202d01c1d0b609001c14000d50210001954102135070b00400070104a4001103c03401c840d80460f0b0f05048030b01860042024422034800d000941e0556100d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 694183498 1250 694182248 694182253
    0xe010e010e2404150e03011401061b12090608101a030c0408060f1e010b0a2615030706020a0302030702061c090302031e090a0e0402060705060a0207061d 67
    0x20340e03195042402141241c0c030300c06a01a01c01c0500b09081c615540d200343c1200400d42c100c950103889858000310a5207403a0001d8008100c1c00606120040b103004043c080e813010044101c0c10146039003210925041d4281e08294400c0381e03d5801040a80310100600c1180046a0a000007031200e4007549148c0003140c40000351280c081038120102560340d400103042c03910f100700520001c0780700f030780c1003159a119803001920103c0ba420041040b40b40350300076040e1344180d08510b80c018080b4001c5c10f001c0c1c03486214a401c040b024801d4400441c4146210144c05401c066010380820404001c41e8403446a481402d500b03035442540c944504988643c0c00e114041e003d640300304030040c010705000c1e00400359640e0390501a0b80d04061566080d09071401e1042c2a00140d101180e40095003043e18031401d854070303125503007916001441c80460b507410428400c80400c106003c0010341591100d4044500059004003a2085072174550030900080d000340030161400d515045107140c50400d1a000c8074041a001c000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 694184748 1250 694183498 694183517
    0x20c0607080601050f120f0c070c050f030a0203030310031b03080906030c0d05130506010b0903071206090b0f091203010e0402040b0f13050901150303090b0309070f0b03070e010e01 79
    0xe094890000c054041410003200304001d61419a8540107010480300f406d48503500303420800065a0400d1000c1c00360102044100500000612000702c030804841040d1070460403d800100040e04000c0581c50103901070000008115084104075100002d89110f1b180740550760b44d0021483c85420814000281440c01c2001824510314105000d9079015140c070600c949020881d481c0d00c4150360040d5010b4070455404c00102c82009000d02c005401340858000d4181814040c0300040d03503038001d620075260060718944440040c056a601b00703980171504450448003500303051065446c910b404841c0d4a0050190405406041c000345044074100d4003170800901003526147400700401407025160040c2c0c404050b20030024244c07100c404600c54440f11400009041c500b0b80149402d448081e21100c01805c941c81080c00025045203881c3c2c05d84003007150b015206d0741e0310b40c200d40c038140407904070044149001d1000a21614000b00a42c441c128660b11807446006036001510b950740050480f5000c2a415013 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 694185998 1250 694184748 694184761
    0x7060c0f020604090603050d0e01021606140c06071d010e0f040506030c1e1f0f0c05031c0c0e03060c030a1e020c010504020a0e01082119110c0103020c06 67
    0x14148a44a000030a090f203042c1d5180f81c064101c680d203074000c40f00e9420000800b0340b019081581d01d00840401e0018221111914940350107100c0a030091205101c50300200da845511100f05446041d914041101c4040c10141b0b0080e25020b07122114084402031606041c2d115481455404e01c0f02c9009401e0000649860027000040d001c010005171f018804c40304013804c40d50702e8139800c4d081d59414141c1400007910440501511414505070b6045282602d0010040f6540c0241e140300141014034050b20301d0b031410700d003050443c440c14200700030565070710b10b03000903d45640d4072248004c80c460f121142090f032820241925440211424101e40c10140000792620507981c101c8000c81c070201440056035102001d014007241c100351060511a03649008200841c00c03c5082c0d4130140150030202803076589080c030310700e82d541c212070900c002c0d2080034170341d90803020300c1c40099500c281c29698400d014200b00001c02840d0814040400034544500c0e2a40009075002e80f0884183d40c4601c0003401c09a600c10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 694187248 1250 694185998 694186013
    0x80708160e04030c0512030714040e0406020319090302030d0f0b01020c040b011101110c0f0a0b0402040b01090305030d0e060106030603110f0303070f0b060108180d11070512030c01050907060c 84
    0x2031090b4107000300e4104c2d0300001502400b100c0c0104200e00c00c0d807a00d81c00c10031002060340142a0028403e01010001072040c5440c6660680c2e000d03520480160742c0750340d0217400c1817086440b016034103204c0c0c0c1020010001c058012000d040909411041084a40421222481543c00c0f4014050140e040142e20000c03078100358100745d0092006042144412141901c0542100c10790283d80702004004076980b4420002400024958940d1500074108100c02c1d0301d070b82a035078201820083c8110b07a10304007841d450740a814610021600001942d0f1110407009505002e040503074407030810340c041e580c0042011402840b9642c217880d0042452080c1d00e40d54028002e4004003540340c268580b005218010004400d60f503261000d600c00d884010250801700000340c9800700c041c0c45c4594420b0118115095410001440798172a4041d150019443c401e658826041c003c0d0358010503003005c0700035440008488000000c1203602d10b0403000b08059590b2680141d10784020b8081d8800213403c1494840100d03902 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 694188498 1250 694187248 694187251
    0x71818030e01031b022407080a02070c12030c032d0c1e03050a020c030105070509040f060b0d0c090509010602071703130f080c18010b07030c0602070507080708160e 72
    0x40c10006011041562414807400d0355040b0000180d120a00004103111341c0d20501d0000011b10310010b000f401c0c0341102400d10040104040b2210707901080c41c109204802040000910070880080b50a590302d060040905101b0a0b080d40400d200c0b07000d0580215603001c031186c2e14030841481400c621800c00c02103800e40481542942d0202010101c988517080c0c450183c26401e00c00d440d540d95900345000007905045654543c0c42c80399141c0001c00c0403040c1c2250480c0c031600c0c2d040390700003113129041070305a0003007a003500841203c00c0c0100d0042440c40c4c00c4d52240d2034983d1140c46d009043c541e51010010b5a0809008040040e0005581005080b80e42d082c03800322000c01da802e4034108448201c0c1b487c03180c810750780041d401c09070702035007040450400c1c410345511960513038581032051010b40c04e0151411061040c124082d40001b0000145449840000b13a119032010080d0f40e152280d040032680c803103441c0603220702e9014400d400108000000380f40c840700300c09081103188940c944410001107940 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 694189748 1250 694188498 694188527
    0xc0504052d280b0a0b12090601120210050c0d0509040f0b18040c080f03040609050f180a0605040212010e0708150d0f02060c010f1512020d06091407181803 68
    0x1160a003043d06991030fa030350100036241d082c01840d1103840d03000880d106004054640c054540004005120340f45001042c15800c54050300c10803011803c0344400c60b064400d015407850f5038040d085d01c41c19840c0d0f00c50300806800c00215810b11160100c44000c80c1141c2e6812034181d8002c5004402810108007402880c1d4400c1c0141c50342d00740c0540c0d502c1c14900f070007440c20407500181c000041c10700c4640d42015039080030b40415a61105800554408a4001c0c104a803043e8454480040012030200d03494201e400a480090815504d0314000c000c021f80b801000e000350031494951100145106226042d520300c207141d814544080c00100e402400b050800c1540e003503030038403401d84010340543c4030032000f48030b501c80074800003c100600d403094070100c4101da6030480d401d81c1c04032400c0100511216403c08280c1d011a500850f292091524400030315080a004000c11380800684411300303c041107401c01c0b030711031208003001501c080202108485806080c020180100c01c1c140001c00e114010803494440c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 694190998 1250 694189748 694189751
    0x9030405030304170717190c05030d050c06070507021e040603060c0c0c15050f0f0d1d06060109030b01090c2c0f041104060c0c0504052d28 61
    0x589400210b070a680c020b030070041c3d0b00302e90029074009400f0304104450041c084ca641602c2c9200c265030f541c03a100e07107180c43c24500c0d20102d00b16800c18011800407c200800009007124040040c44101034843d82146102d109203000e544000781c4514040c004482c003003a80200300e40d892034a800c81e0041e4070803419140580041c2c0c0c40b040803002805d10322800706040d0007512500c03548856458003010f03040054000c5000388141c02c5844515030b070400e06581da800d80000d802501c9118000e0916120300038801109200e50a11807200c41542240005008200c406410384002d542c42d82c0040d9610b0032144802000480c0301001081801c03119840828000c070585480240005224042882c2c0b40740c546003045074182c6502803503450b1503c4c1070003480320103040d101840224110210303807465018a1046800f4440010001010040740003000e0020b0301c0c00802c10002802c0c00240340d4480440b01240d100c1c2c9000030204401c0e140250400d191090b00e0b0f40e034603040310703010b90b00c8208003890100207a02e0301036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 694192248 1250 694190998 694191007
    0x50d05100903030501090e0f0c040902150d06080f0105010602031c0b090901050a06090b0a2702040b040f080a20062701020d0c120c0f2102160f030b0903 67
    0x44140504030a06000f40c0d030200325035041c1104a0304865031a032000305a0383c00a1802807202c000492410250380b000c540014041c101030020501410a00104000c42d90001031a9076900009910042c140c03000c050440e20141d0104d040103003290004c1c055000940d005100c65041c507051070b150041e0409024101003503121007040801e003003801c15142c1142d141d440394200a03418000c1e201e0fa400030702034140180212000e03080130031800c03210707406504510104880580491620308040c60385a880e030381021036035269a1050186150054040c904404102d0340000481190025100001503008428a546d4550008403d203914600031080ba8122805200480e500102d004414261110100c2180341340760241000908114841c503c14045c01500c1c1e0f52403000c074100f040d84051140d0681030003440140c0300c0c00c2c08900900c010200900d803580800c1c18040d003000c41c03071401003481308135022a205600c3c010b8840e403032600280208403601c2507002e020030105052241c0c40d074004001c202030701e203007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 694193498 1250 694192248 694192273
    0x6230904061b03061802040302280b0f120f010302032a0402040801021c111c090c060c0b061f050912070f0e09120405061b0601080a1a06010504050d05 66
    0x120b15691501c101007681e90804001d1032607242c00c05542c6104003042180703020300390741c0010440c241881c1d8141d03502074184c11040b480a14103441c1ca0207040c2e4070103020b490314000010041140c0c001940f10142a81d00c1000c10700d0440420310301c60680350b000b005054810108210908101300c9400c402c405401210201c00180c0c95510003040a80041030000d40d07216022031001c2d1041c07080382c103504181031801c0b0341a1889501a8107603109210001407801c220b00052a07003030003900d003092000d410325150120014600390482c00c4001114460340c904400781c0c0e2050100003000d10810020108407500c0c0514041e1548600006c051021005020160b1101c098518510b0321105801280c0c1d40d601800e1b00f0b03c039240703a90300c07900c0e80200c5460003402480034602d0441020301071031190303e0181c00d0204a003c0350041900134013104d003a02d00100d0f1519a9100185565288000d0040d85d007500041c408a00a1034044082c520901041c2c41c2c0e14030b01454901403009001c2400d0042d1554050014400300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 694194748 1250 694193498 694193531
    0x90c03040516240221041403060717040305040f090b040e010905100b060409090c050910060207232d0126061807030204060e030c090a0506060f030117010623090406 72
    0x202c1031000f24640c0b6141821207c11104c41c0403101d2900c40e41c071800c20000d03501d611500200841a002d0140d09060f2100d00c1c0555541c044d540004242140201010031000a2a8881e00000c4001c03941403115508865600c2d08071510400081e12540281200795500585a04841240b000191000e498640e40390202c03400c03507801d0301040715032540b0a00200402d1070a03101c0c4c1394000d500404500b0f800ca2602e0070203562079180348602c400003031064130910500103d0341d201072034150b00542800500e4401c01c20184450001c1e00003d0311400322140c0da45940c0d4422181100305404440c2241400140c1480030309001c50005c2c03140ea88105041c0000410801500e420303401142c1c661005070300c031800c100703000d001c0c1c120030f50549000340c4c044c4d0364030003040c0e0b5a138100540181c0304d03ea001446840f0ba2020030814420f0180741020303010000000282c6c0750b0404400e03454204c40384002c11010b512074030302036000368000c801d03540d40c51030b81da0031042d440c83c0c24a04150003e01c039900018083d0040c203503015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 694195998 1250 694194748 694194793
    0xc0f010e03190207060807030b040b220c110c0909012702090c28022410050609010c03051c05040f020a090608030403110f090c030405162402 62
    0x240c541d040440e01c082c00301c181d00710803440d1201500262020700e08128000b0140c4000400c1e0504160f12020407a0f4142c56551080b5a840e0018000c000010901e0a5902800448046101f4881e15020022400c01e109428000c403611002c0058440d880c1c082003088082d0502401d07203601950b0322000100c41110300258405801c200031820042865035004024652000400b1011006802c00c80780110000900c103a403e103099070084c00146c00300708803003280f4109580528250607007082c0800074501440c01c1000b4840e846840c00940303052740b2802480503c2c0113403a08240401d10f95102e0500207406035000c1c0013403448851031041038a90b00e18041d001d0340c0317080c0c0e01900c040d0402d640c04800e5080503000354010341071114091104515103444503030389100d1403101a2419089000d628040e030746241e03080382110802800f8500c5400d02c4d1010014507801a9000c403840d00c180031118003001c246d4a80f1400b01c03240c142e500c006680c024003140041010b801e41d010218000c848580c43d45000e50050300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 694197248 1250 694195998 694196021
    0x4150b0c250e07050304021315050303040f080115050d0206160b040305070b070801082503060e0313090605060f0d0b300a1e0515012309040c05060c0f01 67
    0x6030007551502c1003407280108050051030800504000300009070316002841c0d00c0d11a0a0600050030215944640492124a0700300743d9050000040001c1c800310140d0810090b510316030001c0110b100d030f03840c1c9164034004512849401900120700381c4050300c0c003e00601003490701311a00310310703c0c1c081c0d544150b5600801c0b83c0840c041100400c1d2442805142e42e099948160301d03040812a5506100409a4800d50a12410303404940c03424005004102e03148400000e581c412002d1003842e42110b07041e600c1c0e41048201c000c0c9442c0400001a000055000b490100c40c009170900303240100002481e40e2583c4814254015540c0340c10141d12a5129030701018070291124101000c000049400c1d00c0d420360007600001665800aa607801c0441c0b155280700b9481c0b030a580c1e400088441d50b20b441401d02e15070030900301000710400000101c1005903c800078240103645280900e40311101c04100142c40180c2d000360035040303030090602c031909286005000c43c164072001c9903080b0603544019801d550b9280940e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 694198498 1250 694197248 694197313
    0x3080a261b03100e0702190c0509090d14030c1c0902240301140f0901030803190c02060a1a0d08040e0901020a020615041b02061504150b0c 61
    0x800c501c40c1c4090010508154444280034918100107422050001d05401622142c01000000c2603070180200200b00d05d45041c202c8001d0b4441072800e00c425460850300c184c034003500c1c01d0000500708040218220b0392001c0e00341c8900030f9502d1103000340b41d02c541009254821b400810842010404c204aa504803000071f11000891080d1082c41804455140c900c100809507107410a80c200c1c4548450075a410750312040b01a42d0080304000000d402000c000465940001d030000021080c040c0c03200007144030700c480100c13513001041c20100c8141110303205203003800185c101c1e5001ca01c000c284c0e500204035588101071440c0050034010000368a0981307052044402e841c000504002d2940b050110320707440203040000318106084400080e440305001002d500325403d0003842d200c16540c942c1d01c110719641580d116110a822680b43c0030b996420281c41ca0758021103528810342881c03405000e500d118400c00031210f00640d00d02501c10820750421059948580034041c450007210703120b0301c010180861440e11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 694199748 1250 694198498 694198501
    0x3071b20010e0145121e020f09180d051e03010302030a0201051c0c0c020102010509010b01092c070903170315060a020c0918010b010c050703080a26 65
    0x340c031076074000746120305101e10342d8240c03c1000c408054220452156000c2d645080b81e00c0c201120f8101120120100300c0401844c0c0442d40810300c0e0003400b1182c0c465a420441003c2040e0710042140314400025485041548042a9802c205480340d400802d40440402189826034a1034100703100080070703400042c0e020a070301e40713502c83d201e400d072500f48001d80b91140b41d03504580220b500c4060400020341031107070015441c803007180114882034a0017501e15081100492600c00242004241c12381a8019030a0201054007108184100416806e058440e070304900c0c50541408281405e0303810080c545820b00c80c00141400e10811621710681042c0d543c1000a411031900c90030f01003180280501c6448240200100d60310342c800d201c181c444088900d5a114400202d0403403030021024a40758000c01c2180912030301d100640e40d003211210410300280000e0b01a8401100c0309140c00ba8084c0ca01d500c040001c02c04203107100300a0000c0e01d01c9203000386480c00b00b91703a0590040040c408000030707036002c0710 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 694200998 1250 694199748 694199813
    0xf060901151a0d091704090b1512070f090911130b0a0212090a03120c02120309090a0c0311040305030a0216060e09101205030301080c01030b01020303071b 68
    0x26a080261180d4450740311015045011078615000360145884480d03584c042101c1842141c9283c0c401c4215520081030b6200e413104150400f81850400d40b600a0b400358015442040d109019660340e1600200e503100190745284045807540343d60301c800c03020b1018502c0f0114188203580607500e64942206092a518240c1c006014224100c03a40310000d400301c03c3c42041d0303240358041442070741316800b840013640f14244a0000b4244400300e80c002130040796013628001d6040c1e04911000c425900072a0700250015084c0021a01d0307126210129600c458010300180c0285856841441400e00c1d628002545e0b00c40a4001d50703150744242c10503282c4c0c0d4808282d0a213842d90410048511850b4101001100e078600000600240102c0d050039100b140d0710b10000710f140842402d00801400b11120140013031241d0f051103620703a8000e0003003585600072050703144140d500a008900d00200183d0045156a5030741000301e0310400e0421846020320020900440800d50102858520074200c0009141c07414215 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 694202248 1250 694200998 694201031
    0x20f0102010c170604020d0501090b01031103060f01030f020c0712050705041803081b04060504030521191116140307030c061101020f070302010204050307090603080712020f060901 79
    0x5514181168101000ca5580035880490640b02c0e01020b03410480799210800014041e00a10340d0810300e044c0340c00c0001030400c445400c01c910014082c0c03002c000d1668107000414036480704842058000030301e0b00071070341301d54131030750000f40401c451810050415080f80444c0341000000c0c0e0000050080011162060150500440d4005c0808980030042280610f00c3c40c8001c3c1c2c0d03090700107014800e811000074030840031603030141482242000d400b07035140d84840c00540307142c00034003060b0340620800268580d0350300640d004411807a08075164505005000c1e02199040c10125003860800600d841e08030390031542080521903102d20b483e040300106007040024045422801d40243c800d0713008440c1080803070100038199007541c0942c81c001c0d115081155000b800391043d400c8002c2030550000d84039040c59419400390041e00c3e011002d4801280e560300310360b010b641c154000540391810800429000038110070000110000a005440c1f50110144c40142000c0084030b003000240d44503c8042400b0011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 694203498 1250 694202248 694202269
    0x30106050304440903010e030a0908030309071502030706060b12060103020901080412020c12060406051803191209060b010206071407110f060c100f0b09040b1005030a0b0402 76
    0x41c02444403d88400c4450b5024024450080c1c800c0d80f1414501c2d1500c82e1140c04035400c500000d40240402200300305407d64941c003007000320000514099011618940110880380519808002004e410342000e0110f402454140c3c244019840104000d00004016000320741c000d03c8158902c40d122900032810f44031a0707900520090406104020100301a80c000541c260006d0b001104003403103a0b40311030142c0c81c000200c10350583c4043e80c80940c0781c8c2007000184941c4558401c2030180002e80794001d4104c00c2c101449120318080c2c1041c89400c25101d85c54505414440c490b1602003211400408040c08540c9900c800352040c58843c0003d03005560104901da810901a14240341c044400320410b101e2401030480c02003074045c110744821f41c55641c411300780d0507035200108032681d5104c4481002d03545803111601070030820b041089006040c05c0303902c03601030b843c20003419206403582c440c2c2e42c000e01258010420107000c4140c6002103640c0d1001c1003d440c034640700d151115014101380c010001f15025 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 694204748 1250 694203498 694203533
    0x1518010f0510030c0c0b09030409141f050604090c02011508150c03070c14031e03160c0b010e0921130b180d060f0906051e090303010b0c12030106050304 67
    0x1081e00c00d50a031341e4000002100c958100d95142015101d4031902c0d070852045522482d401410000520002c0c1c81905406000b011303102091070300e081d4001c0010503a100f40e0302c10035038025414002005480003a4209640280d640c0c07000040c221781544481c08104001d03040702d8642d03404920183c01c1030701a26402074020440107c46419441c000340000c04659175004010126120700440030307040d86e0100151580c407200d500c840b803107601c0405000d51864200f200c10b035441c3c00380c8401c00600c981c0903103008100d16410050f1844182c1c2000c00768500c092002e03186200604c02c4c0304003602c445c91031900300503804508819041e07039504101949100e4080503000092225410405400c2d080342e400480080c440d01034454481422290606c10000c0003040d00e03462400d4180074030a4104001548840d1140c1c2d40070002c92603a41d111002102100ba0460300d0901d580d20070001400700d00d5041000c1d052441c185030494400c42c0040108040d15042a4400740103d078010043c031040041c03800f104400b070f04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 694205998 1250 694204748 694204751
    0x1b070501171503061312081b0a03110a08040506101508061f02071509050d0f051018020111010c0903060e0a05030c060603060106110c211b010e030c01081518010f051003 74
    0x10120b00d00007105810002d41c00f001c0d23000245a00070f10b406900074600003c01500556112024610b0241041000711800c9a59000f003500060b14161001c10030320990b01e504540c107a0340e14409005480c0f4072000f60209600182e45034003070a4407041c1e0312500545088603800350006521b0100451100030740c01c1c1c7d61206000350384c00700b4004ce8840d1031a003158141c00841441d9041040d080c100d0030200180400803d15003014200c0040713a00b4107428810b044c2c402c0c3c0e136280d07072002065295800c070307400202002d00066052908001091540d04000170b4121110140c1300281d4295544500d03562024803042c41981107007040104a240c14440207004101c90306101002035142c0c502540c60303c00036212103105d103800608404e207001c0c00445031104807800d00120741080408120312003a0741c8051906a0000d02000712088150901150b0211400d1301070f142c2940c59204e03101480d08403e42e000400b07810440c0550003260318410101e10500900c0b0303c0d0584007609090505000c2c054080258940030b05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 694207248 1250 694205998 694206001
    0x240501030903081902040f0f06080609040803040b0402010e04180b130203101a10020a0605010b0c07050409060e0102161403040b030a051008121b07050117150306131208 74
    0x30b074000c00800c1d07200015500a80005082e813080078001d0045070010b11200c21003e0b808291803e14806007000d4440c2da0701c440c1420b54a1008014a41d1011a8018010941400031030001000300100c150070510505045a4010403400031404862020342001c05480c0d260200c0400c1c0b02c074541c983c58000300e40414820314082ca540200f50b5468500c00407010050b607584003a4001c001a507040440a03c000700222043c03801440d0096442c0c00101094504a00d4080006410040380088443d5207590745e003e014aa0319001c00c200092050010540b00f054841110042d8110700303100508042400c1c580503070b0092840e041c420350515200049084e04c5e40f0400050004440900c10381e03510841202c40814142e854802c8100f41000f10741c44180360344140b0025003c202c440f00050107010031103507050f040c880040302100d036461030644205030100e408840c001900b500c074600701503402080a05001c1f00c0f0000000840e1070683c040710f00001d09030414488038100581600c400b000c200f00d601e051f2819 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 694208498 1250 694207248 694207253
    0x40209030a0b0a0603081308100615030c030207080f04030b011406090405041a0a0f0b1e040b0d14100f020c06010b1b030c0c0a0e040305090d060905012405010309 71
    0xc5482040380074005901c60b600107a03065296802c02c501844e40812010784487c500b60900701070348240c1c003807061580240c01c14051030100d01d224081c116660007415444c0700c41100300c1a0024480c20590000305602005210b010441e05001007500c529a28882e0790b40e5441d50a1182e50180180c0000c401c880713640c9510211682c070300080c0d8000350000c440000304c0740c032503141c0103040380d03e0800d0041c90103010f0b1040000c0020660700103d20f11750034a400b070044c02465000c0080034a40038081c101d520000301242c5065040560064403030040c0a026107843d044280c40720343c003000c060f03001000c0130340c080481428480028050355a45c410002419410301105020103611210140103925060a0104c1c0c43c0e086944100c80030b4880746680019660360f20040d40c003903078440e048036000e14050032030348074009241000741c21410720450709551243d040c12040000c000c0801c150500076100543c4414003d03020a800788103000d00c00e4031030350000290b401c60109105507182507070f103c1e41c1030614000c00c1402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 694209748 1250 694208498 694208503
    0xc0b3d15080705030a0203100e07030c1b03050301180b061206040f05010503190516030f0b0609041a0405030706050708040605060a0b1803010204150c03031b052a010f060e0604020903 80
    0x104204800d030050b803a40d0351500700301c28190304c0b50f1100d81c4120b27180051024450b007543c4011501195942c1390b1503021003030b032030321501066a55001000520100010898403003589080c09403c0c1d00520085080d050000000381e50381c00032490701e00085a0700c41482518641886407004081c000d02050001c0d40c0741c04002a00c41003030944144c008511810324800300001407018408000425001c6c00005460307040c964010300b5014012580030400c1c0010801d00d19220b20164842c42d0300c0840c40a080140c1c5d6100e0009181c0500102d805110a10070f8900143c0c450080030f1042c5220b42d03c120386071500381040410b0301e80142030a03010707d42d0400c02f8044400300c901110780c603072005540002800307503030f401290080c8255800708029203001c1c0740071905154442d0503504002d01a40e42030156043e0342c0f10f0703034100026001442d03011401c108604c02e00440c2d0307000403800e41c0b510311090b2141a0044800b44c0c2c02d4610140400d120240d6950050000d03110510100d07400000a45045007440310f1040441d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 694210998 1250 694209748 694209751
    0x5090c07060218300303091e120423101b0206160c030b0c04061e03240612091a06030304180b040c0c0b3d1508070503 52
    0x1418181c00040d09200701c12a0460002c40d00f00140c8100d403203100c1942e600c00c00030740102100c80303000118400703c10451400415a8040c40807100a804c2015610b00220800008424030100354000c604044280d041810003600081c070401229031b03070800200012800c142180a4150f100f0070030008144919940701000c0d11070501c0390075200c0d401c00d10780d00000750700d0701503d2145e0720200c81e1200e1080c10003200d4241c090499110329500702c01500c805102d48441d0141d809114009807061410802d100c04801c210504240c06090009903090a200001600240801049400076584200304041c5a02c51590040000f041030f04114500c107030351360401c84e02c1d90040307012041150038020a01940d020b00845000f003031040c061030007514040c2101006041441d007a24031a40c07401c04104120782c01660070303d10740307031348284c0c2240990740d01d648003c1c1d00380031543c88810700551107c1e00315030f01080807988529900200d100303012042c41c05500403440d00c00050f5140422030b00d80c043c031100507040000c4e42d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 694212248 1250 694210998 694211003
    0x90f0d0302180d051c081308030a0f0207031d03031201140319030f08060a0305211e07021e01090902090105070c0b190203160b040f0503040b030f0105090c07 69
    0x503954401c011038403811200ca12403400d038003d00b104403400820000045a0341500c40e1076a040740405007550f82542c5003201180d010481c400c4a0401c2400502c2500003150300c05102040080d40c408103400c0700c0100e8119001c11004504c6194980d0200e150700c0c0c60446620a04030300851070440708504940704c0c01410303c644030790079480684540d000d84d003d02a0000c3c034480091194040062824010180300a422804021032804408580903061401b00303036007600e80020007071640440038142940c1600d20885141e218070b5040c00261001841c0c689603211040310b80c2700154540c021380c010400c0b5440e071466500325101c060000004103980001c4401c0894499240058a0341c030301900580c1e0611507a80d005014010901c00410b03100100006020007414901c820094540317924801d036a07038403401c560089071031f501581a6002030708854005901c141300300003900744000565102803854000d50041c0380c00702c07404400c10001c0390454400314018001161009103030306044007108103038854150007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 694213498 1250 694212248 694212251
    0x20414061c05030708030717011d010618030206160302010b0415030b0a0e010c050c0d0e0112020d15030302030a0215101a0903060709050a0503010b0a090209130c090e090f0d03 77
    0x20a0706210342031081c3c8600c0341c1c00a26417540d914200400030490540003400580c480c00050020441c2001e5160306c035800288241f0f1134a1690030542c00755140140c000824202d003120507000b000503101c0c00b020b030602c2c154800d004403400c81c0a00c0d0107420f4421000300540560f03d0880038685694100c540541181d80100303008203a40c0f101e00c8204040e142c1c132003c50b2280d40c28103484d01040c503801002007e2640201040d184440c030184401ca81c035030b02141038a4005015244000801d40c2e071a80240300b5a01d4044002030929040e000c1c60b890400b007580f0980143e0030200d80c1000144e0180f05010b03103081820b50945d114030f008078005010341d08602a4103071070000d002005540c1114041200e0044500404035085498a00e200600041240c02500d0090610720300008032402c1c14011a481124000c2a0034000790800314802c00075041035145503880380400340c1c188000145882008202c90050303070369031083c070b062858071648940c016181c512079621005d09003055031f070042203510000030f09140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 694214748 1250 694213498 694213549
    0x50c010c0215030112020f01020a0c0905060a0302360f010b0a030f09050601030c08010b090604020705160b070210170601120e0d0503090d050918090a080d0902041406 73
    0xc510b8029600811918207800003001207503484002030124001381c804c49601400d0703501d94004984a500d607610080103112130041c10300040c8943c1c1c1105602c414050304d4002c17100d60fa5000900406a01c1d101d80751041d4210800b441c84040000b201d6490301c4e1a041100468140f14540c240c61010520079607464403400f2034000c107103510a4000c0c50021403000c1d810f00480c55503080042c1ca0340401c0c4400c480c54407003a9000904075406000e5001040802414900c00396030310ba00348000b07540600e0003103900d4021145450b01d880c200c4100d00c405800b480d80b02ca6200c0704244140b1452082110301003007404400141900031350603074503900740e20400a10704000d5468800401e00041c010340c0c1c40c0e64205028172a4202c40c82c81d8407a01841c420000038040340c1d0b401d001001c0c00d03102c510a0000054014801a5890030009000d50322190000f0050040f100010300320345401e03c0710707084000c00340c80306600c489080c0190310b07141c003c05282c00b168061051003414200d00048518018000a05042000a4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 694215998 1250 694214748 694214753
    0x409201608090a09020a02030a171b090d060e030c150c03010627081005060a03020f09090f0304061124060f010e091f1d010b03060d020a060e040612050c010c 69
    0x7422140100b013255400e54403400101da0181d20ba4000040b2400020074107545401d8400113020818001c1000080c0c0c9000e01c9904407010b1041c3d80300e940b60580083c0c1907201400001d100d44144450030852001454890030000300c00313410084203400b0905000085c1091240e807501c02400c41e411200700307003401ca002400c01115100c85624000072859200c0c049540080c4c4504081415201e80e56401c03000c000c6950b85408128032411a070202942240b12400d003c10181403421000380c0060f00c0c1c83c00c680701c51071b400100614540c4544c1040d0700041803407080d005c10420422459141c10144038111903e032038520144807079002d00518140c0300750601d802460b03144e400745407003112402c806040000a4a400ca850a81ca40c0f00034940d04443e080d84400000c000610f00100745420041500f070707601c16460024806442d400c0a007280303901c48141c2c00e125006a45896942000f4480303601c0c0e40c0302920840c2d00700021210554440b54440d44003134004000160041400c8007000760908107184181c0890 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 694217248 1250 694215998 694216009
    0x61e021b01080a09141e0115030201030506060d0501060504150807080a020d090c030609050d08150105032203030e0c030703050a120318050c100c0b040b06011103040920160809 77
    0x110280c038000000d80c0c1112181d002040220050000f11200340390342c58803034071103401c8411588c409148200800340c1400198881d8000c560450b00081026042040c044010b4089510a9014801007400001c0411160100000816001e402d40c00c0018907072408d20000350440360011b207074006d6140e0010b8900910301495106024868000300000361650322882c0180003042d200000384c50921440c80d0b4000791754800d01c543e03803180c40d80a2420a030601d252005440390307000a014840c119099982e203401c80659030703a01c00402030081c0d40208113040d15a201d5820701c8803014259000c0d4010780c00c10310204c0c000107164403500f070b4007688041e0201d01e907890440090030792900c5c4d12030400da16400d81091040000d58151280c408941503c6034543c600380640389403d0075100200400380c0000040c000c1607100c19503562200d01030404000d101a407a00f06030079035000d50000440595280c0802801a0752040105030b08808608642e24010442e01c0102c508540f81c20020018040003400300056201d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 694218498 1250 694217248 694217261
    0xb0108041b0f080c04060b1e030901060b12150316050d0c081f0f020703140a0905040e1b0306060603040b0a0e16030303050f010b1b010e0601061e021b01080a 69
    0x206800302c2000b5100d00c0102c3d191203107041828452403c2c0b10001c05da80049808680100880c404404100280803000c86183c0e0401082b00741c81e9580c4600008a085544004041c403200005c0501020700c0d04c100034820302503104a101c0e01a40c00052066543e000f10003044054450440703003001da01c07031546004851100b094106810070300440450380c4000c610040f549400880d01101071080d0f01ca4818a6402c0f030107241e1029001440b411425900280240c0061206440914280300b56949510102c1d003500c1c003e0102c0f0005a0002542c0d210850020036100ba011804074003501c8542401400642c4038003000c3c0c03004e040b031201c01000c28150380840e030040825480b44030070f4421050081101d001e546181d840160086402c15000174288006031020034182c60034a0300040c1000d48003505119031021481c500400c566030348101030b8450008000650091401c2d0707580010a5040e0300d14100c0001c1d51010a41c259480b1000c800781c1e800c91380f400340034041000e00e0700115540e14403101711b01030f080c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 694219748 1250 694218498 694218509
    0x12061005330403051b01050702060d0e0d2a0506040209070c1703071205090714040b06030c18010f0c300801080c030c0105030402040b010509060a0203040801050a0b0108041b 76
    0x1807a10112125010000103041101c2c0100c1c292001882000030300001050306020380360015504200300b038010f107080300142002c4000110001101c0000c144400d20f0a160794603403e0120344013410b000031480d42c1c17404212011600c00401d06a51029964950b41c5001c0500020f1040025000184142d481070180380030858126200400140855103903102580c020381e41080001c0c8001000101c2a6032b03405043d015860640090404038504140e81c20b03484505420303994855190040f0240035554071003d50f01550300701d1245903481404100400802021617105414040762820303540b0310542040d202c049041c0c101505900340d0b9107101c9170741c0c81004200140e00140030f460400c4405594090000c6060b99554800c41da004c8207443d08060b95030b440200050700241d0708100160050030980c02030400000181881800c0c06000d00001e642d03608020b00c2d50300149e1000c2410001000d0900503150403468100b42001003040b0f02000034091600180044e2480c640928021903c00b03c08185400410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 694220998 1250 694219748 694219819
    0x40b03190b10030c080a05161202040b0703030614010216030b09120304080702150f0d0e010921080c0304080403020d0201120516080603160501121104030c0512061005 73
    0x40d1108090020130011a42030002010385c1c4c0010241b42040c81098007500c1a04c0000c900c07103441c1c1c04100c58046d90780074200c851580030b10000480002d068007030940e4501c01d0702e003c508a410170624420100340040d0880c1154410006c41c0450030600114000f0349030440c0c81002282d98080c8924a00781e1b6035107441c003220800204020174000e80308003900c0100d2080f00e000e48020300c680400040350051076855009106e0403c1403d400000ca5030050020f0030041001040003007050b02c5800702071000d07840744800704951201c1c001c28503a101d605644d000c0c0240154600f0760410340c69010315070080d800002e004d10040ca0041055a004040b0020300030300c000c2e070600040c07a0410f51441c84400000b600c40100b110313440412014500450201516800070b400700c1c860902d014011a59002c8031080212840c0c0d03100b0088021b4001031009202840c01030b4035044c801c6151105102c055150ba01214141c1e8020805100c91002800d071090101c941c1150407510348624040c0c0840c1444062400c400c204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 694222248 1250 694220998 694221019
    0x50c1c020f1c050a0b13020c0703050601080f061006050a0e2101020a0e04141308070501090303150603020a0801263301030b060123030a05011802040b03190b 69
    0x102140340900c0c0d034000b051241070100d915060041c2054030b40d1044d140e03a210010300310107004181190301811100902d84d0840d4031895480c0c42d29400e1040c203801c80310403900030b00080c92000030108022900000b2944000b40d480380307003540c0103005001d20901c0d0300030880803d1000c1c11554841a20740160b407942c0741c0e007200a0040c40a454004d5110140d20780100d80c00d1003034600b03940b9140c030a102509040d0f1444481c0c80c0d68600c1c0a4410410740402103840c0306c018024000442c0b024030030700980d54443d44002404400c1c0c001d10340d05005d019400442010300421010f26801e5010b00458115501d034070300b254500c0661581d0107612405049942c0062207055500911480201d0306449a00b41b25000b1151070510002d80c828418400d000c0500603107200c10206051307501c20040702c10010340200c0561000700304540104107592040c1c07000001b65480d0030041c803c00c0408400ca1018001c1c40d10114a800d28004010705580401804900a003101c20784605901107141c000c070107545c8000f0b0501180 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 694223498 1250 694222248 694222267
    0x6110705040f2c06070504212402031b0316030e0316060603021009080a0b191b1103040609140613060f0806031603021306030b0106050715050c1c020f 66
    0x90800c100419030280c85400017090029010340c0440b8150b840c1102d0b5400c0c4860717504d150441074440400125145c450344090b4881e5105061555190700c5042000541d681c2030107848035030f004410383d500340403032481042402000780ca40f82c029200e40b802c0e0b00340030412020b030401c11811401034510411038211001c100e01c042080c0d561081060300d1003119540d00c1c40036600401c40e2050f46601905090b5405102560081207490074103603880304445811b00e01b080400d161600a5030418000c0005903500b011b80d0a02c071035009000c0c040855104402942060715054000f040282140705100e6010840c14070310352951103005c2107980360780200020800e00b5554540050401490407003000005000b000482d015107000314250380314413200d65115a1450454081000800d0490b009101c8195503090020001d0400303071302c040c000c240da034903242d490b09101c1c242100101403804881441c00e107880c01300034079002d0150035102200c40c2481c4032030000d600c0c144c05000034840c0310803d081410b0301043c902803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 694224748 1250 694223498 694223561
    0x10507020418081306030e0102030103121d0a0e01080d030507050d0c02070806160f02030c15270d0315210203071d0a060603050f1f0914040c06110705040f 68
    0x112074650307800300700e03061f81400200d01301e010078000101ba082c3c11840007019103110385030a4044040c200e000780460700c0d4500010f07001002941c4130030541020b100040103d15020f00001c19040003c5c00c007401503140403000145244501000701005681c2c5406000505200b0080f03603014103a9502150f1840c18003009141850030074640c0c41000419011f100000d07148040107032045007050000410102d82043c0344155102801010b0085642d01c440010100c40008465005080382a4000e072a0b59114104014182c0c0d03085080000c5030084c105003001908808000f110600c904503c1041d017034089403002034180741d032a07805400096241c230040380394a2110780c0300702e00070f4100c0b010401000b40c0c2e559050f0181c50040ba410003e9020f180d0029424101c84070103803036032004114196820341e40301d96900c812034140501c0301074100010410802000080d06042e4007800041c10141c003224209038560b40c4d038440700d0040e14000e503120b03840100100010b40110200021841e40e10340201e0400c40b04a6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 694225998 1250 694224748 694224787
    0xa210203060a0f06121d2401053102070807050115090507051614010606051b0303100918140a120e0f150d0507080a0b0102060601050702041808 63
    0xe00c64607071540e000810183c0d0103d0a400c031486501c40202d80001d003001a001070031501c3d00c4105460320408110300342c0760b0a00000c10380c0101500c0c50320b04649001e10032400d8500580007140a00d202050460707c41c512041c52180c7d240b0210301c00c81d01c1800c4182d034030b400380c012030200138100d600110b8a0010004190040c1c1d2202c090700c241104615035511880c0299042030391000d010400400c40d2000c1102210001c41e0544e000380c9005c10310840005006003158040c2c1c0c054400507201040e07850480b0703070b900082c0e0322944d0140010740c02c5017004121500c24610520901c03035000e984a01e079000c0380f212002030340101500300300903001d03000c54107140540300e030b02c400c8049907100740f2108440c540600a4031580008440034003941034640f030361424004a17900f40b0f04401000751042c05442003002090080e24800e411958880300030381824940c02c4180c2c0c0740e1420302e9043d90440010480d40c0c0e684941580d1806804580215010920b00748620110000c4031026282c500c0c002150781721403c42c0300489 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 694227248 1250 694225998 694226011
    0x2040f020f0a021b0a032a09020405030f150c031302060a0f08060d0b070c1b060c0512120a020f1612021509030403030302031e040c0e01290a210203 65
    0x40d1918041000540b2242c4e68250501da40303d82284070a00124050a001547c0c0340803c900303001d070a0b4080c03055440b1410241d8800d4102a070001010b10260400340400703d03450404100070300d1104295042c054000344020461070060b440070000a0b01c854920a025400ca41c01a010565031034080000610b03004501010002154201000c0b8601d820700d204204122a005220610607440e203103c212560116031500f0383d000c2810307040f00601c24114170300c980010142911035600c0c0c00b11526003e400c0568551013085034040901c0050a401510202d0310f600000c00c000042e41e81d12a602514064010714580928800c4c00c83c2c90f010802400380c010002e2102642c0807100c0611413203825005070601140d424000c0c0d001840308000290103600034580100d4604c400d4521810840d02c2d084403000f0455080d64100d51006d801c00010f28401e0589000d000c85419215480345020420340c440e14241020401445000500003010362084851181e500c1c1c01004c0c031a40203441d0617040c1b01030340007561003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 694228498 1250 694227248 694227253
    0x70602070302070905070804020d1709030f0a0219031212021b300904090804080d0804020a300c0b07062004083703020604050d0f0c06020702040f020f0a02 68
    0x440d140300c7c0141c280794031840d8010209901c050003a600c0411040b550340d502c080b01013050240d42001c0e501444131760b1508007000020108442c0900410030140c5240c0c02046c420301c07801c4002d0012800300030743c1146000c101d04021400e14107905100000340310380f007802c050040d00c4002580440340c0100c1c02c86494115080c0c00840220300b0110203450110b80300c044110f4203010408149242031a400c0075144a000342c810754101a65003d06d00e0400301c030340c2c1c1c4400008000c00100800c40c40c1c200b02c040090310390100e10500380c445100c182c45413a02e0041489048030b82c200031410400c02203a0321403019020700c02003a0f0300c8121900d4500701800d2503a11000074001c0c0b240000604007417001c01d48007124800ad00400040c101d080c00602413003180d0401040201e1030304c004448280144c01e2a00609c1d210398010310f114a003a00f0014100070b814500f1204100160544401103030b40181803840362038004030700603aaa0b2140c40010024131300701a00081300380c004541d41150340300d27030009048240c00030303002d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 694229748 1250 694228498 694228501
    0x9062904050307140406030807080a181412010912020304050f04020a0e120c09010312121103012706120c09061a0304080d1a281703070602070302070905 67
    0x24900460040340101c581661010b0020451072030903c503440030001015100182d80c0b0b80301e0315801c00e03550245509450441c80014440049544880c007034401d1100001e5a01000b8106401100c81c003c40c40d40044c0b1516118203115165030003940131100065111b0010300e0406003882020f912508540306045c0324405007401c664190905008440a610b1075580d420303040007400041143c213012404401c8003603c940851141eaa807101c0009078080c0d40200c1c04984a109d08901c000d011483c5040d0f904c841078289100d05240004030000e40341510b05003088030f03001d684550455a20b2490500d0030941460601000050340c01c21007103080352040c065081c9000194070341241301c09071600d0b480b500030f1400f00c0720708510021013100082e5401c1031044845d246460b900e4180303002940d502214008440d448a440c5280c0c0c1d1400c0b248034584426070a046440c102d50b402d110a0181c5420300c1410352a0180030614501c00d0300070300c100e07a40607a102004646030a1a410000d60354002c41c080d0541e01440e040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 694230998 1250 694229748 694229819
    0x315090c0315010e070c0c1d09010c121109090c090907020f060115050715153201031e0608060109020f160c121103010c0314070311040906 61
    0x301c0d01829910050203042076464030750f0713511a200e0000c05001c10845205c0184000807905148800101204c04c1160099903440300c4000c91800050440758450703145c0000c803141950407000c000d0150340300c036000090344549880e080415129100c4966071200021041092800740c51001d02114502620300c1030195550501c00c0c0c0e61462200c00441c026400a0010403003c40341810b445010300c2c00340780c07050510303209954488031f41c182c002a0855032a00c840104403030720390a5201900800754624222080070f42c01b0f2a0002d40a180038400000c1e04500c012030245074004d400451551719140c6c440004145140e11420080c001070003540201d000d06000022800000d00941d2200a0709100b15860120f1802c100308038205510011100031120100003d4004805a854802c00340108005440c6c40c00301c504041c210359000389000203040c6400440e5034a6000d14076101d60290a80c100002d214145401400c01d0b801203910a408441c2000004074100003140311504944400700011a00d41a00c1d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 694232248 1250 694230998 694231003
    0x152719030309150c1a040f32030306011202030a0b0a030503030a0e070f15030e0f10140c1207020709111822021b03191815080903090315090c03 63
    0x1d40060002c945400946a44d0f030500d24903170342c00c14454042d8403032400b0607554880240703140c21401032301101c022003008204902d40c18600700700150580654514902500041c05034104000350b2503000b0782c0800040d00300d240c5036000d1480d140005050444450b500e141081d07580d40201c070f0780c070601420080a00d00201c000295641500c041000c1c0900300c40c2008070703074a441013900101504054540c0c410201800742485030112841070100075044a001500503401603c120b4820006084a88020441c51490b05429140551034460821040c2d4540450880c80c1c5665500b18034601803915140042c1140503100601c0002c604409030140c0c118140c081207844840c0030b403007904203110035640c1c070351161440c7c1c014200340009c44010003001603a80b00003851a00854034000c80d08000c05c2c10440f003144c22881c0f03903c5803642048003080c40341c20110045030101910000d0000d1000200209043e110140f0a68030344000150884203400c00020094010240c20307540c2c0c00e254000c11030000d0850401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 694233498 1250 694232248 694232267
    0x203031201271e180605090304060311090d17041a040e1311040c110601120507050d030e090a0f140105010f0212040e100b071115271903030915 63
    0x152036065000c1018508038042e00710180e50420304071107850520001049031146c0c85c001e0704174000a5449906154010b4120340010700c030102c900d00240f08000241d03403899002150107a0042404001001300c02481e0164000c940010102136998251510f003581030101070b200704c030201030108030661a00c24001e0051210075002070078444100242707100c1810a40c109580d0014186417a0800000b440981c90801000381c101c5120320442404074001e021040002c030f00075000031548803640d403030385550207850340320744c00d91407401030b00c0f0400040c0005116030b0100f03004000440d001c0c44003480645690426020034042c5034045914401c5804100d440020520500000b5000b142c0c60311b82020b8a02c078400100415000511a442d030002c41c491043d03070080c0c0000780c400d090100c10744a11710100070f4895602400384c074103240d003070250035040468200350b80c1444150503c2c0c000c10b694a00b0110342001e0204d414100f01c1e585031040001090f50250741c40702216140340c103846420450b1501140d4800300c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 694234748 1250 694233498 694233521
    0x61501020c060f0d0e1920010206070519050412060b01030e0115090b040204090e0615030c131d073f02010f120c080711060f0a09020303120127 63
    0x2003031148203031803081d81e4408105081c4841c01c071240b0340001500c0f0401d00e11b60000403107410b11803410040c482a02c0300c52604080340240007134070703907840c0221000b08070b8040d40c60704405600f01d4100c07407040340340200101c0340600300c0107549070395000407404d00d4806008000c0e00140040c0c58404150740e100b4041c41200b010701010010744084600d0030100d80050300a80c00f49603030040d0300300320005042c80daa1254031281c07514080902001d2a04420802001500c0d81e43c480c06600020110316075541e50542003a01d2003052170002420b9509540c09035504030b11400146250b214280011030744200b084040341480c20342118084c401c4258181d1102c01c4c010800352451381d41c003195411401503002d140084d40004003490080b20051a000c1c01c0c4080d211044031481c04900358105110320b46900c903481c1e80310000d000d8028903075030800401305000c60703a0080c4651090f96035001c1250843d50b06204481d80500500ba0b5030740c4650f100d8840c42840c582001e402c0544200000d06040b50020740d0140ca68030a0703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 694235998 1250 694234748 694234777
    0x607110d0b0f0702151b130905010302120c01020c01030c0e090705032202030a030e180f01060801080313031b05030111030702060709060801141f0e0102010b0315010b1b061501020c06 80
    0xc94880c3c800d500765070708a101b500c0c0c0110910001028102c1007503080700400f600780021941d94594018080d1480300b15a059600d600040c60140140c2d80000c0c046540c43d40078600000d01010140301100e50040d0492030a030300061200900408950200c0594091031074220401c0700f005152820f0b10303042582040080d010b8101b103401c00042409030340a580981009010380c040c3c030280e0f004200781c54800b1104003401c1c0f040c0c080107100550340010503a000d00700300380040d031a1052024407210b6961071848020900491045402c000820100d0960010100034009120713603821410742c1c0e02203410450302d58005200c0e020015030011711411823503044907250303111429641d00381203801040d2603080d214a504002d4189208446c4080c04180d0280500340d661000d84500000000a080da00c0b1841201d12940c401c3c070480f02001400c0404a0444c3c0ca08045145d5402d80108140d0150308000729203041e90266804000801e0181d44101409036000da0035140341c10790358410410a40100c143d18010700717 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 694237248 1250 694235998 694236001
    0x141612020d021c1b0221040f0314060a09110d081b0304211a0c130e072d0507020409140a0c0f0b0a1803020301020a3b0607110d0b0f070215 61
    0x381300c246c5c0c0440010382c04200d0302d0940c60b001e04044410081e441140c0c00c42c0065004448000c050010315080006c00380140714852071500e80d01589a001800035205038201140784041044000c1180c20309080420b00150300080040300c90307105e402502c520040c000a903c480d50788080c4c2400c0c04403100d60f000d4180e00c056244ca481e81d00394407a000701940101c80c420070a03081080b8540f00a880141040c1030000001d1030082c0004068261555111780200428000c3c401c03a40d4643c80b08249180c560b20300385486d4000ca0000074040e20200310087d06c90000801824030201c030124182e14014000e0750103007011503840000305c401005c6071041480030001403203500030440c41200300d0401c40041035038072512070352650000303803c907401901c0b810046008007040071101c900e0b18805035640c06044d00e00903041c80000300c1c008003038860200d419103c0c00000034141c041220501d0840901c20008d4401c0446400d1481c0007a600f40301a943c2c0b8980700303030501c000380c9014030018201c40e51020130783e0180d045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 694238498 1250 694237248 694237273
    0x111070f031d0a030c0801140105010210020c0a0c08010917070804050d020f031f0b06071205091804050106030212060907060806150c10141612020d021c1b02 69
    0x1a80b4011010101c521001d00715040182e0b40c4488020196015050007516189012549800c49051040c0c406072444000b0041260b070b078010414403c0810548030150fa1003288001403420030101c11001081c544141e40040390501055201d014080d00c0fa940704d000200001265034180d0164940c01002400100410b204038109840c0703140140d40301078022003800a0070000030b4100340024180c1c841166000c1c0a903882c02805005e44889940103540c0b803403400f01e440e00c4481502c032803440c000c014400000f03a040c0c05c680740d40000010a0f8600c15443c180c2d41003500e4400c0c040c01d0540b000780d214000b4240c00c80c14550303021032001e0141e101540207050070381c501042035503d075100030701c25544552341409010b21151038800800c80c41c855000038205800080300c03450f0481c2e0344142c0c0c51310380402c10000c01c0421280600d00c1046000c282c1810b80c0301243e0481c05102070b10407850103000c480d0010800e04103c1040c0c0905403610700d48040103212090008400f6056800c07000340d41d81c0107070b2100200015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 694239748 1250 694238498 694238507
    0xc10050109021e2503121802030105100e15061e041412030d1a0a03210504030b0a050408041208030a050604050c040306151d0405070e0f0a0b040e011a030111070f03 72
    0x150341d0305c2401d0150641036114601707811107440c0c00690084c4104a2010400c614007807042c07540c4000c42c10040c03072403c0c0c201529501080d1006101c100b0132529800903002b2070740ea900598100c45901e01c0541c001c15005500f00f20349030041c6c07003254407035201400e9080d903500c0d20304020031421410f0001141481c40c0503266401500105c0850350b4242d0f46621401c4a5803580d0360301001a40c007807002c0c0b440d080c04014203001308130001088070007085400e000501c0041c100c0c0e2403481c0c220349448808551901c07141040800f030b02c566070014051070840c0c0070120402c100900034500c1581c4d4010704000c56a80e1800344005c0d50000c941829041ca0100310a00000c0d030960b206818007001c002c0c8041da002d445840c0d5809940c0e18055031188940303030b80100800c001007007051401422004100f4142c1c1d00f00f0540808028070042c1042030032503182d000720f050a031107650000103000d01080092208403a4007141e01d4050140420b0b450003542040740d5074010f034003080201c1e0407065000000e000344001646080381d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 694240998 1250 694239748 694239817
    0xb060f0a03110408030a02190302191b030303060611010c080606180603071e020f0a03141c0b1e0a0620070801050f0123060c10050109021e 61
    0x40038142e550010030040d2a440020304040d20b6001d000755a80d1a0840000e843c0800501c090079608460001c420006640401d072408020403c59400d141041d192400b20b0300d0108a0041e00900b0411150010605500d50040401c444444e118200714004d0541c00c20300382c0d00790707110040c0400c017010045110340c140340004010b04955804480368030528240011035503801500c0e00c00c001903030a40d240c0078182d0b6206201c0203044d41d45c00140b1000b50001a0281c44401040000d002d0104004860051100110446031032103880c08000d44040001038820005010070350244d80101c00e44030480e802100204981c0440100003042d92091a2603c4811030310140030a1007421100040e407030400030041e0801c14140588a42d1001040e1840c284202040401d016840b03401e541c820340c4002071126000603400035202c40d054509a50b2246081c0f459031414a00c1050348210790b00d400000540c1c03906560207020521113000810580c02c645410b44a41c41c0242d51004020711500c403c5000d00e440c5500054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 694242248 1250 694240998 694241017
    0x30e01030f1107020102070506040f0e1302040f1a04060b030c030402030114150f1f08040827040f05090d0c15060e1e01060c080d18050a14010b060f 65
    0x1ca12402091100c200351229111400022030010500004640c2c040c4021801760001361022404c040c94900c00d600c440c801c5104c0e000c40d50500a0126418010b0b0281c0c0c40b0690340c0141017441027590303c4045500a100a00f6505088610100040200d2030503001d07400c100c9100020881c00e5450b81620318500380d0010b17204980c159a18080c1c800c8403403844d400c0d107102d4402400640510358000c0306100807a004a84018414080032080c0340080e120225908101c00f0a46009480e0345d03624503000c640c600c140e90054407111141c90410382c07200c10f105a2089080025a41806010030000450058600580b00e0040c160805001188184d1040500c1444039004440c0c10403140505e0340e02130101c90b450b80014107020785031020001c141c020705074002c000294100022102e585803450050408980b99002884140001040521085140c11138030050901b5584442c45c2c142a1420342d958120111041325032a9034500c01c00500c040c10b218002200002401c1d56140c0312200c00c1c6082c540d404000c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 694243498 1250 694242248 694242251
    0x806010504090b032b03060b070c0b0703030e1b01030f020c0a080a170c03010501020f0c0303040b1c051f210609060f091209050d0c0311014a030a030e0103 68
    0x24450007200001c17102c00180d6041106005c03003805003070000d0554901d0307005210485c80800840c00003c0850450104a13aa0b10140d80e4482e40c0e0340c80c04078090024a4000340040c810b48a01404007100504440050711090301c4c2080741c02d014603080800e1340185010a0703001d80090980101241a00004040e00c9540e40340c00c00f6050070107400110821400c0e00c1c040aa1780c4048018401540c040212480714081c481c010032080c050b24000035964860b5000d1000300f201d0201e10203100f43c400740500e48500c149403000303124038a4000300e0041341c50608201c0f444c18044200e00003408664540707480705042030124a01720a8002505c030b0300003031b20781c079202155801d44d6a000d0818501c0d10b032040b0701001c0c3c0705510080001101030130082c41c02009401481c13003140600f481c0400502c0c4244650126980700c444204400305a10068031040702c3c00b1924110000f00583c90a901420f003141d01401c05107640b0745205a28566213102e004514008d22140c00d50700c8540c8240109004d80250f0f140c0f101c2c145030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 694244604 1106 694243498 694243513
    0x1140a0203280209042906040f05010509120a14010f060b07111f110129090a110d060807090c09030305070302070b0f0c06070806010504090b03 63
    0x145111039a280b07004220480d0301901658a0184000c004002010104500039030300c14101c40103003500a0f05510030481e074680300c0161015241104d0700584c44d82e0070480151180e44c44140300a90003202e1040842d5074140401038101c0c84e511814104140c80301d83c2182500b55a801500c01d03c00d45c0c00c000c414021b114080c010382d1704054110443c0c06400f6065408146140701410300100000d0040c415180310940100e40500c1690080d002080442c0001d080e003403009107028081c8581c40701e0014002180e15140a819801c421015030000d80e0241c05510108a9440103a07044145501d499013041540d8003440400300507c248517040c40780142500d001040b10f40f15004c01010b00c000401c0d0f150902d80308100440c09425282c440300d640e07410413401404503811045c83e01a140c81030a00040402d071080344020302070441078454030b0505081180c400094504000300d50307054030540c1d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 694064748 694244604 := by
  have h0 := BRFrame.cov_init 694064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 694064748 ≤ n) (h2 : n < 694244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
