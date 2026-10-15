-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5171
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:58:35.608825+00:00
-- url     : https://prove2.me/submissions/9386c9f3-ab24-4709-93d4-1d15f4516d67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 929856115 ≤ n < 930035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 929857365 1250 929856115 929856163
    0x190c0809100801051212030f090a12020c0910080309010309150c05030105090c0c0a080a021c05190905100c111503040b011e0e19060f050a1502061305 66
    0xb4000e07401c54141c400664940d440050103600341503841d13800c429036001d400c030140300042203000309603003980e40a0944415288080c05654031b205041c4511900302000d80c110031200a00380c10056900c650001a0003041048113203088000780e200d109a001d82070415454920040600c014020b10b0709985000d10010005400d030701c0f0300100345030028084d2500c280c1300c56001c2640e4107008400c1d14082c000b08000340080c8034450790b400480380c2c040d4243e102540101100c1c980114400241c1100c030a41d1742d02c945965084410000e1600d0121440403014011040c10070f005548030610001c103603102c18100707003440072040c0c00c01c48152603409280551100c480120340c0c56490440c0007850155214080c0c0f80503590700c41141c00c0f9985680c1044150720b044042d400c202c01c4000024490700510008003058279000d03000a290150340068120b4090500704100420041c00d2168408008100014481d10729850b0803000a440c0d05010b4440001d01c04001034502c1880414080c00c21981444261480e80b14 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 929858615 1250 929857365 929857367
    0x708040f0519061404020f0d06060807060e0415060f11030702130905191106180a0b04050f0406120230101803080f070201090c0e0912190c080910 64
    0x10702d40e0084070390505105210482090406507980520b50081c002c101d00040c001c140008401a4001905c6140d11110009101c40c0c2c14401703000540444c1d0345000c0c0181c0718070f091100740c9414000525484101440c208083c4d9030082d16100ca8074540d152a085c1484d01a45035445d50003000381c042e40c4650310758201760301001181e00c20110750307210b48150b9410741c0307007034103681c020520314440a40080ca60170b81283c1c0784d29008006043c5a88040c1088020340c0c032103004140d91600c1500142d00081001a05020629041100400e05101290244070190410820140040900100a02541c4480c1c04e15100d07900700c111510848c0b154200205030141c2c01c45485596042074000c0f8002e01c8d141103481006480401072815100341c15484655041e1182035601d201c0c08401088403046558551180000840000840006060640152015007400f0700b40c103091129203da2008484420046070300240c124200301000c00300c00d410b00c11090038441c20905070034862800903941c00140150504011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 929859865 1250 929858615 929858653
    0x2d0703051533031312031d0f120f0904020a11120d11041d070e0d0506090f010e0d05070606050a0b0a0905030d1b05030705070f0905060105040605030708040f05 70
    0x901d5100c04403000000a40441c40b240c1d2006a8002c80250500590900422255450201030340c0c0945000201010341e245d6680069080e104140e0540d0041040701c0c804403020010315204101c1018118a8140070028034065882050323041030040d5004180d0540d00c50240c2a03040c1440170303000a8403401000d0002800559000c50034100b481d5160400e034458203200502a50143d0390700e00308074601d101d0030b03500c50480c20b500207240004100c0122051701e0281c0325070b150b602555100e40020120342c200104440d0614034094000d03441a0300d4020714840c05180001d0041c921102d505007940c2d14131040c20681c000d400c050304203541001103004005034240041004003026002030395283e00070b644460400d0b0300c2ea09201c07065000900905800900005114a01c104035407080c800caa190502d19070340d041c01e001856001e0703030001604400c10081440540074240e84143c0034648145040c2c180340f0060980d000c0039144d41c042085100002c0e0412030700070055081140c0001c00c58018100031a042c07841 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 929861115 1250 929859865 929859919
    0x6010c0209180313031505270f19151505060705030d1a030d0305010e0a020d0f1503030206070216061116091e06032102150f2d07030515 60
    0x2543c4c2e14411b01c441016410706c100340c003a00f80c2140b02080000420ba406401c1010a023804005020b001b6440c3c000030000c000c503a80c1184a05c2c0e1900f2801246e092404031100080c0d0902c680030f050136404540100200704040030b5800840d200b41e200d100d18100701e4a58021300380c107814498a803a06c004038070240340c4a01b0f00ba14808404544030300072200320440c1503510030310405241817a480d02248040304030b5005095000d2003141e0005410b0811114174007a03407440c850441e90310005000900c2450760500c1030980c0061a40020901044000c05407a103050542c824841049003034404000c2400b0140404010b18581482c1009003035100c0400000038a114541800741c00380740c00020150030300c103001e01c600300c0750459003020307001004400c1078528204050700c0c8411401400210006160800c0e6180c0c05070142c9080305c0c20510f030648a20301e4410913001030144070080c194410600b005060001c0750703c0b410510780400d10f80c8135100d0b2182c103600003161240d400310340403503075a410921014040c80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 929862365 1250 929861115 929861123
    0x60c020304030c081c0e04140c0d060b121906031211010501090b01170a060308070b04030305071106060f12070603020331030311190e011706010c020918031303 70
    0x50842e0b41d40080b13641d10b510148030801ca1000098030010818014071300d000c000380000d03001160341c0d0715106014806140031107141e400309001148466181c0454803460020b03000b0382c80c40304e10f0140c0c224440789807210300401020300c0003a2401d043c0d010003401e411040003940d11411901c60f49100710702c041c01c1403149004071505586030800000340501e0381d0107424040c0074103071180f448905047d02e448001e484c00401e8140f140391a0b280000c0064105030040c4a020301440083d001c41c1894980141520380180ca80c0d0300f004200459946041d50104605030040c00c01c0b10902e0310424045c01150f400300d04c00d01a03100901846100242964151300214441d121300180941d190100011144404c58000e034607070b504520844095000034083c1e40700c00080160058004e00b81014001d25551820200c80c0100c001017110301d165186580025400400c010f885151682c149840000203107501828a80171307202e150010b0102d031300d51421031715990002d40850166940d070461000e14094911952004403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 929863615 1250 929862365 929862383
    0x9040f020306060f010e01080421051210030c1401030608010c030b03060906090604081e0a03090317150409060b090708070807030e0d05070501020c100c0e0402070b06041503060c02030403 82
    0x1460f0740c604040c104151200c140c4402d00151a0300c0011175503480b000b0030858014a034501541030f000b610b0400c000c500607480d43c2e11569012003803a120703c2d800010b0640445c52101903030610010399203c061606569030070783d282084140c40c400480c0586020b031b212540a529004540c02030550581104004502c250120345103900d820070a030303545100032652130904e6001240880c2c00200144002c2010030340e030307905005c14080b40611301d4003182d001040034008641d648151908142d008a520003d030014071401c003840340341014100d03282d0b03156540a0b80c42983d45204a41c10043c003603000c1d134042c440c046c0c5103103c1480d04840c0940484402c1e140b90007c9030601c00010800f030b101f80122a02c0300d20990280ca1056100203091700c3c0fa411020041312295000c2c005138081c40c4d0104150080030303882c0c480118158401c640040c00b4481042d0055002c0d6004011030004955200505034001c0e41c01d0b00d00040c0780c20140004454510150401003900e42890321140c8015030001c00307001940d004940d9a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 929864865 1250 929863615 929863621
    0x150f1005030307050a0609050f030a090f0b0901090509060105040b1204030306120f030f0e0405042303250615060806150a17060114121008010c090317070209040f020306 74
    0x540d880c050f54600034856804184002d0020f00c55400a8410ba88034030111201c0c821400302c100c0c10354000a0311800041d41d0580c041044a13048050744008140081d0102c0c5091034000008154502c540259405112003002040144e44603004583c0241880d80c00c183c0c0380e42c80e0880b50a44601e0950b0150006410003401040b01820b0382c1403003003c140d00100400418445076420f442d200c070b00091580a0114101010b09682c070755010b00e600c00d030f208454040004000f60030a803410110300c212a290740c0c1c024003140385010f510040c5000302c80103003403101c800c03216689002c8000d030102560407645003442c0200011140e070458070881c0240c00031551f103403050b41410780c0003000b4003981f1071010020b01c0d0321200120903480340c458a500044185007010781c80b00c44403040f0440c1c0d03008110016104481c00200000020504090009014184024400079500c0000142250800e0101806185040c8803405c030701d100f03802c200d40f10658060150504d52805080c15828410001402d0340640914000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 929866115 1250 929864865 929864869
    0x50114121204031506150c14030f0a11390409050d09080c2d1f0c0506090d0519020a05070303030b011707120c0c06090807020a090606050703050a02150f1005 69
    0x1c00940440300d50700c0c641d103040c9580781c00302d49145c3c0d01942c0f007260104101c00b1754081014ac0045c040f142198a6100d0707043d40308144180342c400581c18080050b01181500346002565840f045030041a01c0000364110682400081c024440244010014031400105840d441d4104407a841241c04c2c800a8940845002c405e0255503180d54081c031540d109044070782c18168110110000c1c0004000d02a01d2078416074104815607004c002001901085c1000750060030840200141644001400082c14030000810720203003642c010018552481c0440200c000b00c034620800c21000043d802804466600d0794905016004119403050039000034800c0c0e031160400e2448049c010300910f6190740c1c103c01d0541c203040000050002450800c1008450461000428880e00500c0c00c620302400d11180d8441e0544100305a062a07980700400f0355003420b404000315a000000e0710350003a00350a0650780c40c0d0f0700c40422400c1450701d28140042032008018030a58401c103440e0729100790740a201c4c0741c1c1983d0b29142 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 929867365 1250 929866115 929866139
    0xc091508040c0909021305090a0605040b15040b031b061c060515091e040f060306020306041d12030403091701051014280308040e06040c03050114121204031506 70
    0x36020303401c2541d60f0199500c55519900a540c0b00e42c003401a100515801e98511003654000d6900b0741c0e9404042e801c1c4204010000c50688095008035400c0001001c10e201007519490400244201c85041501c1c0788050380714402120240303000150600c80480e02020360320010640303070003524024503c802c1030481100d80e5008807614100001e102041840880400b40040c0031510340300341c2c20548844510b603145c00c00380500300142d40705900c0542c4a241070010f00007250300d01d00100d0071070350142c254504078860124012198170340c00d29010341e4980c0e69003400d641c186216803110540011810901051101c1940514018a0700341000a4415591051030351140810741449610826040710040e00c80b01290201035103040e461304010071960342c0c2c5c4583c446a0032030380c01028101300901c10017181d0b00d81481108014400b03030804000650420240049580021103070304c0c0144003503105c400c1c916504211003249144d880d1151580c0303644030324107482580c201d05130002d01c8509108000c9089140c03c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 929868615 1250 929867365 929867381
    0x70f1703070e2d040f11540d0f0c0801050705091306080307150e06040c03020f210706081b0a210906050f07020705130c091508040c09 59
    0x11a4002d1090042c84415103c0400e0300d542d10507580d07170b030a0107142e003503004103900e45407000e01003502c2d460b60100008442c08040280c0d0554a00816641c0104a141052000320089203040c400c0c1d04c2169051a401690725420301d681c41052520240208498107904103411880780510741d0b4682d0b81d03141c040f07086e5401500c8213000300b4820303c1000c2140c102030041a4001252070008600c0c07958581c412401c69000c4042a070b03040c0c413030200c0740f0424802801120284141800204160b00d032030303210061440c0f200e0000031f01c601c40c8000e80e0400c0765182c0c1d81a036808622810324030300c0b0b4031000707910719a1105c2d40d100d01004103810400003460320791040c4500300344246d0800c0c0640303403280c01501200c42011048216200c402891881c0440001c3e83c85003142e454403401c00001daa0501500d03690f0381e44401041d1504641c800c01040c0455114500154100d1000000c0441c00800300c81066680044075004a800c07100400060024940d100010b031f80194040c860fa81c450640700d0200c541581c50708 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 929869865 1250 929868615 929868649
    0x4181b05180a0308030405060105011404030503030402043b01150f1205030f030703060306060b031003080306040f02030c090f010908030a080c0c06070903062708070f1703070e 77
    0x24007054403031007050812141201001003000102640b07a0b510108160403d4078150f64682c4140010b0090756004281c180541011010040c2410324650b01c140d40e034400240028000c0703445189120b060340b42090031541701c0c4101ea074403000100c00010311700d2202c10034107043c0c0c59030360801107400035034012104108261803040d2010401281051515210800f0a0000f2030782480100321b24000039030f00c0c10280d4000c403520794021858510310f04000f0141c4025410268002e80c0400a20840c50442e4940404880d800840261a0f0b0390700c9002500070507448440390001400041000081790000004200c03841701101d17402070a0b800140110350000c1203020b0700240d43d10400905d070101c3d0080700304961012620307846d2171814142d44002405c02c00150f8200c408034600d00c07030601c01c00805001d07104200014441d13410809000320540e008492070010042c1280030001100d0090101e00030302c802d071254000c900e001c12900d0b000d4408407294011540240080e500146400302c42c03804081140d502421 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 929871115 1250 929869865 929869867
    0x140a0501140c2d071b0b040509041403070807030e0108011a0901030c11010903020106030204111c0213050a030302060702010501061803080c07090c1101230619050a0609080f0703170a09090204181b05 87
    0x62341d64403407a282445490764bc0398030041c4035000000713507110f00806981d071181d43c5807031106c4a01030000d0003584040c0c001e82d1f000f01886502d1241c1418820a6490803103003460045416900024160703008007031251000e030075500b081144020706130150801d00450b8400d0303e040021500c4004420b00364002e0020101c413143e03010840300202d031074503005048403207403140b400050180d4030700004170346081a6000300c0c0544c0001342040400c580a101d038900501080c02c02c46261001d041041043e4142404001e22000b4041040000343c030f0b00308010b1018014100301001102d00e002d4003d0408045805010a00e60900186644042c3c10016180b030700e81803500c40000c207481f141c00300246881da40c0d4003581d1002c43c40400003403d41c1d40003609402007003251610300310a070400300030908045400c89805842e6110038010030001e0b02d0f5110010744560342c0414503480e51580c0e40112161002c9a028402c03041c000b080216030a49040d0803506d44a4446104201203d60664000d8202400303d41103004550 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 929872365 1250 929871115 929871121
    0xc0a0503011509051801031a0402031c0504080105010b09151c18020a1701060806041a090f0a081801030c1d0607140a0501140c2d071b0b040509 63
    0x280035501d40e0440c2c90541000c942003a10b0300b001c04c0000300400c9070500c1c1c9803c02c00041082c000001b41003003c2d101841c0d101d22883c0340070380100e6a10040405102110040304111461092013541a0740140404a00a105d2946e680012807641c1d08420401031064624144000341c1101c2030080340c2404041c0d2480b030000da812000d800d4010b040420000803c540c10003031400050340c5541080300035011128041c0d40c0318500400300c41c00c552260304062820b600c07072800e00c004110001c81d4100003d110011a91482d45e4403d25241440d25690401d00e16220310000b000800025401800d1446907282c40f8141400c0200d00440c2520103080c0010003041c0101011281c04800340791900c8900c0c009820715240941c10380d2035024003035143e820040d0315040550343c1010002c0c02c0c0204c0003080c075620810300c90360401c01c0d90303022203104d1004034040c601c1d102ca0f04d0000d0880742a40901446d51154081034441402d03007040d042e21541141d12550a110040003c10803030f0910b0160b03026560042c007070740e04c255 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 929873615 1250 929872365 929872379
    0x90603050c04031202070e100e0c160c0e0a0f02040b0a0c03020f1207050c0603041e1a0f040b1f0b0304080f0403121124100305071d0c0a050301 63
    0x240c040d0004074a034030100b002001107020f040f8103100d07410040d802007440c00c1c50000d490340b0602002e1324024164206c02010862181b00c121810f802600fa0f900703040c2d950394441107550701c2452111f4001e11000c4010303400a0b03070b000708a80d45445241881c0d0288201d07c07090b080b21017284501e0040c0e284038a02408407451031840390400452940c842e00458564080c2c0220300380c41c080700c1d040d6188091900141c407504100041c00104501041981c3c81429410540d5a103222003540c01c40841e6481e180c101ca4000380400e500d080781307403402d100400c81480c1c208641c0c9aa5031540071101581c60003a04008501c070041c56042d2803900c182c80100307032807003a07061005070303015130f440500182c4034401c0511128004e00b40c007600400055200f103404a45000000002030503e802208643c0e03d1034200512010303584481004046490301040c1030310806030381c1c6442c620000c0c2d0164002401c14440e000002c6400310b184004060f8044000e0050b45203a51f0312803101048c2d03c940b2090000040e41440100486 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 929874865 1250 929873615 929873621
    0xf01060608070c0611180112060803031803120f041b030203070b0708090a121e110f1f11010e06040f08090d06090b1b03100e18030c0105091507090603 66
    0xf180b181c1004213000a000480325460b40000d651910180b200d000003160075a00500c40111040305100c0c20b01c0b89038a41005291a400011700724280840c0101907070010340814000c0b1031281c1c02141c81c01c4120306015003402004802100c04549104500007801c0c4100d80440400303086a03801002456080c0c04d003100d80d1043d0304080070880700082c0078007440c44155100550340001e404190841092035040f0304100f01d07805021240460301140c07105825003ca0b080d005031082030720043e280c2004200090010a802400c0c030b000074012507035504250140c0740d46c010b2003c880700b5a0f000c000d010048212081a8643e002550300403e000d0b10815a080010000000352154000003010703920a40c0c1c8a03100c4000b911503601c41103a08111800800c00703009102c491410f06c0c0c1809100c0302d0b0441c45c111400d05c003002051b010714902070501000280758054141c00e1038400800d900b0640f0b40b28100d0f2014240a050140c0b00c2031514000c08030f0710740103800c805000911615483c2d585440700c4d03290440035801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 929876115 1250 929874865 929874887
    0xa0209031e030405030f061b0a020a020d020a0e070306050405180c123f0a1704022101021206101b020a0510080601020c041e0510090606110f0106060807 67
    0x1190100f8000003031503a4007446180d00080040b805000c3c2d910380403c81441c1e1094148030241d40003428040000e9284d400034041180ca5415a20380c05805140d0000400040055104000003103801701003259a56058120608482c81a1020710954840b059821a8840805032104055001d50b01c010110307e0106c251401050b402c0c2c00792110030310420a0325401c040c01000d200300400c80c0c0c85040d44102024400d03860390b00b410080700b508160200f400140491820005001c001d01403d010800307540d100482c003a1001d9a0040c2c05550a48207407a0700c1c040e41140300c0505503009190001356050516241c001d9080d03100e55140482c41006040424007100c0401090341c0080e161035010415849100c60150a01080d0325103120b10b00d0800002441d1041c00c1d00b41c50b0288e420a550b45409207200017590610001398400402c40b59908040c4008202c130f00c2d0702801c01f50781002400551550824140c11380004154280c403207120910412a00740d4074284245000222000001104a4880d5800440e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 929877365 1250 929876115 929876173
    0xe0f0309060d060305010501030b0702071505120403090b1903060905011a071a151207060519020307150606080a05040b010e090a0b070806010f08010308031812030406020405090a020903 81
    0x20f00f071600c030f846550031280240c0040b90784c291540c06000000b83c04003c000002c0c40c25418400702101c20101c01492400350174048402070031880d02003010140101580805005a02c8074103440320f10848400807509141010000447e240c51808161300d140c0707000d264144d8440d1035128605c5015400b011107107074040c4d20150340000524441c1e69900500c8850b15003d000c4058401c6100080b0b50104036480e003080c0807801e2258020a000c0029a0708042940c0c10380610a040354461912a101a030a61280001c010842d08040c001c218040c000c42c4d10550944143c0d42d00e0040c3c1d50b642c101d11004a1700300352009440c030403003440100170408244461030f511103444400d40c0c2c03206241d82d61709041980251340f020b020401500801c0b94559000c0c0450241c04043d19080400f5459903d03400941e1002038410f03040c50981000605000c5800c000c2400014803241c4142d960786400e050210003034010b4040e4a10528102010038000c00940c001da500310740000b400b91025480346028a0746d81c502d0307281d00745 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 929878615 1250 929877365 929877371
    0x60f030212012d030c03020906011d010e04090218090c030703050c150f0c1b180105100207051806040605010f1d010e030a030918050f150a2105010e0f0309060d 70
    0x15a10f1850721103080194411903940c50790a0039441045000040200854104450800d0381108000400c4e66104038000a0a14a07a40440d1070007080140c101a078020b500102801c1617007042c0c900049d401803107114201c007628101c408520803d030711004107201c0900b103644100880050303441c003840d204215500c40c0301503a00e03110f0a41d001410719080100010340c1c42e00030f2440d000b0f44108200b41c20310000c800302c4140340302001030f0160004500040c09014010070b84e071a0190746141c0208490000303000c00030148071a0046d0300d00d1001e00701c8800ca8240e07000703904023300010554000c180401440a66458142e07031454000c01050030300301007000d42810080141000c05503500c0a200b002d10342c80c02640c902110310304024804940e003d541304d480d40404d1420b000c011651586881071600700c0d07a100041c90b1071030810303c0000c059000710303004502c402011116540302e2541c0400b52501038be2103100280880c00300784810b1030316500d440d0350510780d507041004008103900d131450045c030300150708a07000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 929879865 1250 929878615 929878679
    0x503030c0a03140c0a1d010c060e030c0a05060a06050105070b070503060d170c1603120c050c0406060f1b0c05061c0204091508030f04090507030b0d0309060f03021201 73
    0x62081980f00f03803101c40003000009000040c15501c142d210036101c0501045481c0c002c84200024903450940f03102501c420740d0344966030760004080c803c682030810824200c4602c2e4250341410360300e80b1004c0e1801300383c0c14a042e40024007540220152251242c0010032040d855555410503141a0300080c642135004901000c041e0008020309070210703c2c1e492200d40d440d02c2d444a0303801149003e040183d11180039170004010000694032154007034400b895407425010320422460810700d0550342103001d9070b10030f040840210b49594049500b00e00840b00c1e50700c0f03d050301c94800390450b4035490050f02500540c8030000034412800c14400500900c80d241100d0100c1e090003102d0141240c000350008609203880300f02c030b1341555102c05550b8010704000307c0514580405507000b40c040740302e940f0a80c0c0c6225242d0000401f02806580300c840581c1c0003070194004203407145401400d20302e06006180102c1e65108100401c54400c2c42a100e03c1c0b10340080c0300c030240c6d08210343c1010143e03030903d20058038035000d040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 929881115 1250 929879865 929879891
    0xd020f190302340e0c0729010308030402040b0609182205060105010305010807081b01030e0a0c051e030a17040f12060f020a020604060b060c0a0317070c0503030c0a03 73
    0x10020039001e0001c0303289080031990340100c812031a19803080390010300d45000d00080101700c504403843d49a0101e44d1402028000e101c03200c000d4078400100340200013030304c0008140209800110309c5688225810400c0c91500420000103000f0500380b1500145480803a100750342c0e21950700c94000d09181e420b4031482c00100b032991010311118030215410703000302004000958140c054940034000c004060409903041415070350341c3c0c2c040c2e80035003111049410b03450012079009030b01c510b940aa20320180d4209540074140064010b18a104c0e00d400b60407080307100264401040007c40303c1e61801009004440d8480e21084c4c1181c424498103078018900300030001d210303010320307500000070403030b5141307203d0304e804c213424040200e5106104080b02d0f540104a00020554049500703544180c2c0100c7c0068000010b0740410114000e00703003161711920030070041d40301345900001d1003000682d42082e4a01c00d0f0b070364408210390700b07070070365600400319441400482c00c03c50a16001d0501840c0d10b02e07002900c00c00c4001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 929882365 1250 929881115 929881153
    0xd09080405031906060f03210e041107171e07051c0207240905210d2a0215031f181523010905030d110d020f190302 51
    0x5003d000030074180c991104100d800c3c0280001002c01c0700910004510f19250300e0b10344040c800164030b6500c412490004031501400c06003800d00b202900811401080031003c3c4400c1e4006201a11000001884000d9050003078044a914842c25a0f995010804521500b0700790740080700100c80c140203d400310703e101c4d000c0c1d050840e015401940213207140c41c680f03107407020b01c4c640c07025000080c00d0320003405250039604009004102c2c1c0003075883c4540e0b03540d00c0c60441c0180e81c240005079100c0c025054452602c0e40d2107641580032031a410060304031407400d07a940700610240e0740b5009400102c3d00d23003d852441d25000180d90320044981d00180041040c2004d0300c0c02d203d00c0c0d00004001007110b034020340c180d003240c400c0182404414502c1902c0c00e00304040c50110301101c0700d20003000b040716540866240d2290b068000181001350440d52501410300c0c003d8007029044a60341114460f05000c020b40e81d1002408130604070100300540390030780d01003080402c1e16103080b0090f8250700c18601c060b248000c21382 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 929883615 1250 929882365 929882383
    0xa0c0614040c0e1803160f0203010504060c020705030c0d08070320011d06070206040b28021b07120f0614070816020c1c060b06030703090512040b0d0908040503 70
    0x812581c2d02c982c10001c06075030041004e030684905072010150501044030003c2100d1041101030f0312002c4100790f524156044900042000303405500b01030502c2300300709694000c0001915280c00307440200c0d469106041ea650b0240d00301c0e0380e11a03080c0c40160b011400d03000080400f10b00916284890050310529003038200201b01140740341c0ea6455018501d681850240b92414000306800b40030981000f420095a8510103000500445c0d00100482c00681500c02140348500400b089040d40c21014031084000f1740011120f0624014070b207030f2035005c1c504041a98000e64524000d0201c0402182e180e00789d640031120400c4481039590345140248241600f00e45105280070740e07900410780343c4002035610080c42c05691500b598045004801c4a41d5100350a694069022122450343d030924101100941048140281c00200000520006a615412281e0110301480841e0f5070a0ba103c00304105a2107a0720513420509018401c18510840700c0d004240298014a03940b03040a88590000b41010104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 929884865 1250 929883615 929883623
    0xf0b0a1d070312031d03040e0a14180c100e090105031f020d0902130902040b09010510050c0a0209041407150e04150513060e01080105040807080d090506100306150503030a0c061404 79
    0x45800c0011100f45070000340c0c850349c40d140034090149401740612001d1005005450700d0204a500c0b0034441608120005064000408110090255039400361600c4a8080c04c1d9000700414000401c481c20005103100c0d04031400c940c2020004c512400744030083d044214105e0355103845a01010140e6500021034a44c85046280060400920310400046403205c00b8070074020010800100180d5451400940b026105414050b642e1002e16100d5800c2203580e001c029842560281400141700c000e884410100c01c0400031148004d0f203d01018030004030b00b10100002525802c10101c0a04080d042241301c05150018010042e460f07100180e9108501c6040501d9659514001c000030350100d590b142c01040f00d00001c104904040d2a01003aa0ac1040d90180c503c0c2000540780341d100c00317568054034009130440107807a11403e0013120521043e046120642c0d1941c104401810b540d0a048810422114010000e600d04110050259007105020006031036083d6240002c400d404860744006214902c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 929886115 1250 929884865 929884867
    0x60411150d11030f1e01060e040204030c030b0118020310261c0e010905090606090a0e0103151a03060610050c0a050307260702060d090f0b0a1d070312031d03 69
    0x241d100044c850002c11003c0c46528010039020541c428001c0c00341544c0e92032418020001041c004600684150f50008110b07a990032000014450030808090680c0c400031080180c1000640600c81a400141d440700d1080c0742e504000c0040d0070301d65600561000f185d203013204a000480040501341351515000d1558240c034124085050303544800c0c0e40100b008242040822503080078081102e001004243e04c0c00340300001070b1211a03917204441c0c4001080d0020b40a0180d40c0c4030b00c0d007a408450020a0140c01c10306080c2c0c0b0342000d105c408406d40404030060028000c1c2d07a10701c020020081e240181c0581400400c12801800c400c0501001c801640108c000396600e01481c500800c0c000341005800340680d11980f12104920300d03107403c6482d826012501983c6912114031198000c16022070001c140f00303400c242c4401000156013550b4802c4154000030408110300b940c01028404050240d018183c1000c4003e000003900030f0710325080c180740d03850001242002079100e0688030401c6d080d403804542c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 929887365 1250 929886115 929886121
    0x18050d2904140102070804090e0a1202030a090911120411030a0f021207060206070309020415120605010501020f0c01030203090a020a0b070b06040207020f060c1006090b01020c03060411150d1103 85
    0x101e94003252075002e4007107000314900f102c5600e404000d0700441c010220146c0c1c07280e0030b00704901400c001c9000015045440440050314180010f556640103400e00400f168010400040d240c21500c03034041d042d0381c002002c03450804030000394480303401e004008075a242c921566911003600c00b04050080184210040b266078035083c01001000d80d0011809201580030803801d001485e40480c046802001508022604041902c00103010b03080e90a40b01c440f02c800c540700020620354804190f4106c0d80070f048108200d03600d03580120b8444d9020581b9010580c04064000400e5201398000c0d54003001030300c10fa410340001c990000c0c858860310b501c0400900780200e509024403461511558000c2e1040360214640752007a400300e0342150290281c10310450020865500c500401c0c44980c54403208034034104056501c9809590003040c00c161541e0040c41404201c10707081c10001041070185401001c00b10b0740103d507408200001c0b0042c002e031001c02000380251480141140075800c52548400715440e1245 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 929888615 1250 929887365 929887373
    0x130c0b09030c0a030f1b08060c210610050702030a050111070b13020a05040f0e0115082e0504030c1208010303170f0a0b12030d0b0a0618050d2904 64
    0x102c0e4610051045040718420400100a401300d500815031010070001c081d4022941007458200b10f52000400d0f0050404120341051400002c0c4640c582210030311000c009251100001044101c1c0c0740c80d0803081c2924030f42d6541d03005101034510301b0320040840f614103e990380c0b0301d400d417020f01c441c0d4011304201044800030000c0010007560b01c500b50700842e0928590580003c1c5c6d554020344110381c05280c0e00c50610340491010381203007031501c01000091000da001c22034180401d100700c1c81518420f00504600701e0010a806501e0402448203070f041c09001004207016400600d030107401242030005030b00c0c2510008a024810010b400c040791181c00c80c545c50340c00c002e45080480b80e4002003280100c0104001c03900203581180d00002c20540000d00444490007041c1c241240250204940c8070104d040310301039107550844050000c0075210001619179409041d1078842c4c410b2003c21003620080c10610090405070a181625030040f0b507168400c2d141000609405e01030f141c0200000c80140d42040144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 929889865 1250 929888615 929888623
    0x90804030c0b071208070302090d050a03110102040e06040c09080a2a030b070309020127090b010908070b0306040b1e101103041e0e010f080c0103060e01030b130c0b0903 74
    0x100b11100980e40790244075034416031805240f448100030700c114440840d2105220f541620889480035042d20fa80c00030b2400d0440d51040d07804d404500040d48294101c00c0010b060081e5011250030340c12512403a202e0b44104000782086120750400c01c03411413000070b1244030400084091501502c601f003541c40c0307aa403494000c480554a03403041047ca0417801c000003164242d00e03035403050007460001180c80541c40102c0b58111200d449206600240740c00c48900303500348020307404940c1160001c00407600e00c040191ba220341148102c180b690405501001401c00f0f10000350303803204006200150f03002100300006c00704901001652a880b441032000c45007410404d0624034154110f0410507080041d588900f40d41c1d10860241245203503a868044541600a0300080044d144d103000700324456031150186540c07902c4034803400d080c9214000c040301031940244140c0041c0c4164891071041390382951a1450704050113003c034900845404640783c0070442426030320010342802482c5942d80e140e00d004140c50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 929891115 1250 929889865 929889869
    0x30f030709080d0804260a031410080d080a02190e01030f110d02071109090f07061806110c0307090b03010f05090303060103110d020409060609171b1201090804030c 72
    0x25500910740c080482c2c0d0050851948a54410708500403000c071420782c50b21001040c6c0c0160101d080119075589034940540150344c0035104000c890166903035129034500640001d2240005079080581141015481a40d14540c005a82c00d0050700c0c0039100e1154440c2c01e2040c0018000054200c0410307845903030b16029000207405048018410000c007090980c0161055404403995540d0002e042410007125840201c10010005d11074000c6140010181e620740c640c4080c4c281990140072800304119004500180c503c0381c83d211f00311b14403410000e003038800802c1e4031000c00440c890f402d502d807840c0e50104902c4c8083c00c1c0030640801e0400a04007410f080d692600c00302c0020318107107420044401000001c1d41d03440725003480e02044081451503003100605c6061140b05810740005804107484640e5004081110000c2c1c0e030b14281280e8450141400b20100700c0386c00301c281c02c0b05c0c031007541055505010340c010110051031074590b8034506000c40d0845400200848240c6000704040007400070100358000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 929892365 1250 929891115 929891129
    0xa0803010f0602011e020c21040503070518370e07060f05190e093102130c0905030102040e0a0605030c10080a0b040617060603010b0d0305030c0705030f030709 70
    0x2051082c0400d030100405c016601180d981c0841d00c0300f2881001c11514240000d5030b44912540b00d410608010a90b106010f07040c007a00c034a400000d00f60a0540c01c0c0c00c0591000141c150380c0784c0755010121722820301b007111204820b180d00642c500d10300070741d007229180d20301d4120000748441f03005014500700030242c0e01801c2480340802010494603000350498036031107000701c1c14181002e088041500c0d00301032144d4103504000c0035404c0049543d24106003401c502c414500f10003003100041d0f0000303011030b00028001d400440001a007150b2a0042c0c000700d1200c8883c1c1407681e40c940e100c6000c2422a0010f41c4991805580c820510904036032500c10352000d060280c02a001c14040240450425620844100b040101000c0010b02d00541a0b10080000708010020701009960302d016003400203400300600d80c18010a0f011451038941441000150308019001c0c0b41c040d14140c8042d10b05070001000c644021804100150000710b0900003054000440b261041d142d0800100c0100500040d401c260 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 929893615 1250 929892365 929892371
    0x60a0e060a031e06050f060612100f120b09070303090b030403030f0e0a021f09060503070212120a05060409050705060c15100608090a030e062505030901030e0114060103020901110a0803010f060201 86
    0x440d15038404427031002caa41c0700345014503200c0c0390301755400051650140400303542244010604515820b90442400e001c1d840041030354661160036034883d032071b611005010940c0d0741c400700011818100655400707406400d0004120302c110b01c00009940c6c610940c6019500250308071021072424184400140c030400b46801035801c07059a000c1c02c54103650280c501800000b00000c1d9405100b000001a85c48602d040036480e8540224503400a900680d03115409605000004150b810b083c818400056003140c000e200c0c030343c503250070b2080551207140c0c10102c900640300c141c1880036108204500038100a81868008c0d03180c1200103110440c0600044215004144150082540300080e110859000c907050303551240d004041e00001900c040001d01c505070602400070600c14088040c1071482004e032800d00c07007017031241c03a0a401c0700c02070840e400c103403400000800c0465200c0d07070151003030b04010b0400d84160b00e540c40486103403080190088400140000041c00b102c281c500350306c00202004e0000b4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 929894865 1250 929893615 929893621
    0x1207200f03070308040f0c0e15010203070507030620030c0c06010b07050304051c02030105070807080109270c120501060602122701140a090f060206060a0e060a031e06050f 75
    0x4140c0700d100340303070002d0100181c95011406000310f9148078412541d018441074001a600d100f0090f288a0440e1070200c00580d40103100c1ca954000300841320010b5002016102060071030f69060004c003540c0c2000c0300c481d80c1c00d984084819820708015030243c41a030401503165540a0307400da14003001600030f404001024400c01c000168000241e4040d91011030700e06001c99190030412814140d01d11000c0d50560805080c071001e19000b5013400d0007000b041c0d450180c96030b200c6071030380c0a44558041d5124000604c06805c010f00c110440200802481003aa41c00c105503038080c46c2d88101c90041064481d039640d188104810740e010000f050034010154012810300e141700700c03c1c080c02c024100c0319101d503200d1a420702615a2103254071690140c0c000c0344080c0c8860b48510020701450840c001e9a88120b180c500200b452400010f000344510001005804003d040c000c000c07510031800741c030321900142035005c00700c0010340246001c07400ca010011400c0900000d414200c1c25100d0207040d04030030980c20024 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 929896115 1250 929894865 929894893
    0x20a0e1c020d060c0215040809010f0f050a0e040f0c02030d060905011406031b0315011101090b070c060e0a0b0618101208040302041a0a090605061b03120720 69
    0x100804a641198002481d24013401c426410150180c1001c1c2d241041c2c04104070411102e200644411042030b1398681c20701c0003540050740c02d90070301440d41002c41c100340064414180302d480240c0c0304580240001c14002c6a202c01d100c241c890517600c07480943c00200c1e000751b602200740b0135500107094844080c841c035454007001c1f1400c3c0c0b4440f480c81e80201400030000310424000b074030f544403404040100c140d483c940188610310540c030f60844240015070040c0d01d230341f190070305006402156800c07944495107619681d40c152544009800c0454069460386140d080ea40418800760050720300680701048245050b000300401341c2070403c5000244040113003888844422780410304152010390030040d0312a583c034200941d180c02107500082d0f06c1800c0c46600b40002c440120107090300740090700c01d1013025440b000c558003030b2821405000e4011801b88100c01d8450f800d1180301c1240340c1c02d202500e190500005148611406c00c807001c1c40455803005c11100c00840742d00210a04542041c082e100303403035403105 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 929897365 1250 929896115 929896129
    0x2010501060f020a0f0f020415030803100915050108040309180b210a1106070804030807110904030804020928051b0a140c030c330108030a110709020a0e1c02 69
    0x103000381c14406c1940c1b0701c0045442d554804150f00280003555846035030741e40b40c4400e00b58002c542c0c0540300000d21200140f803e015004d241041d00e10741500041080c1440d00440700c01100500c26001c022088000240208001c4044901208020302c00f10340390000301c05200c001d0304c45505411081c001c80c039910941c0d00300410840000c680c0003046680d0340ca4500d0024040d805101c00180c20604009400002c2105101c0107140c034501c1500250440c44ca28400c00c2145d1800f140c014001c07694010004005181412106500442c82d01d000100805d940901605074542d03d0080c048480e501c609111840c1080c62004030400d0400308080e140c07503600b01c1c00034180c0e0300b6189407520005010600400000052058840c0e10000e08200d4081c0c2c40000220714000381503070449190402c1500c001803084840c458024182c80d20000250316200340b0010031100c4010151015151703008206020565000d680014108440207640d44580d00b0584e20070461044400c0414622410303900c010500162203101d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 929898615 1250 929897365 929897393
    0xb0610050c210f04060c020901090504021c08120f2712090414191103010b09010815040c020a1704081e030405221a01021c0c021002010501060f020a 65
    0x200b102c4888800e940c04000c698029500100f03400d4002180c0402c039540c1c40740d00710110500803185003a5590341d0381c104104956050b10081d40006221031506131146900304e805140d1071040386030500d00422240080100c00d0181e03203290340d60100009010451400d40122003120103903010a98001c6007900800c0e03a25511810340b841780e00804101c07a40503681e0fa4ac0705042200d030708004442640b4040704104408440c1c842140d81107440c1c4036400100c840644141e84c140c9440c46420fa00c0d0180c0c0c4001501e4404006000348404004060702c0400c41d103483c00f901134000100e0f001800030001d44e10b0600300c2c0709400300341c8028100d014841001210030018600681030410852041c00300c3c6100b101c1d1f81148075640009402c0b0a01510200d400c0586021040d0714005103039041041e003903a4500080d02d00d1001260350b00503480f0201900c0c03c140c604c0303030800820300d00c0d080030b45811409a01040000304044000e8000d46d6403103004000a60300300007034506504c194809080c00c10101d540c0c0b03d54450040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 929899865 1250 929898615 929898643
    0x12010f1814011a12040b160e0136030605090f0109050c0111071518060305100611070e010311012003031306060806180c0604050901090b0612040b0610050c 68
    0x514006410080007804840041901c50340004080c50607051a01c070900090b602c00855451082c0581c4207a445454045035008c070503075a0910007a0010b03020404500c28218000d251940710909644030425580460000c5105410105903490301d403c01c58104010f505207440584d0409680e10300040f404120250080d9003424841e82076900c51110340d1600c4095000058600c4c074030501a803441ea0807601d80303242c0f6100001e213288426181d000c00c81c10f6440941700c0c4e42030505006028401c1740d024007202501085c1400483d40c82c295109042c0c840024281d1090b2101105220030900c00c1d41d01c4214a12800e0440303039421000e001d00d009007980c07484024000006005e80302c03074080821019800403001000098202c8007103040c021807011035400d42140e25180c901c80e850890b83d16080440a580403a04014003035100c0c0d030300c0c1500c2d007000b4005a070300855000744100144800f550724460081e001da03001d421503030180d00d03000040c0309510004c580e000301031210510480468540010f024440d000301 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 929901115 1250 929899865 929899889
    0x1605042717120103051227060d06060806040b0a0819050327010906081911070203071d010b0702130c090f08031e0c07050d050312010f181401 62
    0xca052215506042040c0440600c90020b20910302c41414100c0700e06aa000e8001d403103205007039034070391010740c4100640c070002c04a86444240f100d2074422145680302602402c02c0345051a41c12190701191116040640030440d42c0c800d01865040921900020403025200d00c0842400c024481d5525020f0311426050a2464001c0304100030046c03044c0c0340300e0741d5604880e40c00300c0d000182050520300c0401c40a800034024078400a80341e40300300d041c0c81c007500030380c0c560201500f000c801c00700240000e200341d40c0b08a40100560b00040c3c80400104000388081403800103003841448030448100c6041e4031a80760170f1002e12003040035035940c0a075000115042c1d03000152081940034103607080c111951100c4800c00085034002840705010000300801880c1d40740c4005d03a81c0000101007098015a01c1e9520107611801c230910031803c04413555002640540f089a0500066120010540200740c0052240c5a4681d00802c081541203250341800c0c07000c0d01c028850315032803a88030420031324140b203001c2c03030080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 929902365 1250 929901115 929901191
    0x304020d0f0512070201020c0d1205070503121305070e160c0f0b15040c030e030901180e07020114060d03080a200714210a080604020408030c160504 65
    0x240180c4469461079009065464450700303005141e40d5504158005d07405801180310303d003183e2070506d543c10a4954002d1410b01403003003904040391190001c0c0303c115401e02c01008907924120300208090b100d981c152401494500107440c4c4076040046541c000b42440b048002840404411500c1a007501100d61410140c40c21640c1851400d255500c0d40c080c0c00010104103101c824008131400882c100d90503103003800100d071084012401c0f03030718100511060350414002d025007580b10768040213541c44080302d03080c003550b02c034900d900d50f031f1606555150150395103036020ba42d214075500003076a108c102120416654440e9490141601c9401000f04404640e40e0504d02c003071400011911000030011a6003545a98151501d59010700030b44807404010300c19942c03c100c00314200000042080308040307842c1d0408005400c00d6a811101901320340d803094003404081004501000688421083d8600400c00d0403100c807007010702c4080c03980000c2e000e00d00b40164065200400e07200340e00c840c2e603c070003040441c2c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 929903615 1250 929902365 929902373
    0x3050301091a120c09130201080604050c12090303190b01050d0b0418080903071406120a09080c01093c0611030108060f071b1e440304020d 61
    0x312505030b00c0381d000501400010380b60000242c40b60781c24005945240c415201d00d01c00a44c038482c1030310028000340000c00029400e0500d41c2090342c211044854441c01c28030070a000d2440c0c010101c1c3c9020403a030021003004601c013108140742250044000041250144680000382140300d054500103102e41c6400022410780c54581c041c2004840501d0a29404100c03441c1411190b404081f10b280f29208209003ca040d900010310820403944c0100383c649040680100901110030091038046c040c0d981e8410480460f03481001002e50342035002c00050403001c1460081100c1d4111800280090020052511210a4540718800403881c1d412603400404161610301c0c05411609070503c0300d9400031000145802c40041c109014450001041c078003070341c400404039040c14020a0040d100c034400100c20000c01c00c50550904503940c440620b00c5103141e55190b89000003524840c0b0103640800070119243e940b802c0301d06801603e1004080d1043d118800e88801a902010b08060b11035440142400200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 929904865 1250 929903615 929903651
    0x3030a1a0f09040f06061203120b0603011703070206041805090c13091401150609090510090c0e030604081e030103051b1201180209150904030f0c0f060501050a120305030109 76
    0x10b81d80c00441401031b191030301b5483d41c044130920300c1200031031001001c0719505100c03406448581700307000d4041c609507881c0c112140c019610148403292540001c104000142c1c541c4002000900034050300750305c8001c1000201401c03540024900882500010484060303665280d201c648408928440490742c0d900c54108401d84440c0140d645403150310b40701341c001418581c0441c03041200c07481e40301d0951013030741e0301c669000361902210840e0000c44448014000352140342d001c1c049681643c81d00b00361901903400864680300e000e0350165103040c408142c06d1080f2081e00c030307a00807000f0303480000d0f400e65140d6900d030382d601d4030001c0410b500d5008000f0a52820f0300c0d00b0b8400d0322942c1d9428000c1c80b581440b03109031002400b072200180e000e02d0a03e40050451140f903512030320507210141401da090394460328100c0300d821005aa640400c040f0359160800720b0f04c0c030008400e148e4040d101c00a501d524290400842e52955030040004400a20310003007c42d070080c060b01d04503030484401060140b650f00300d41c849 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 929906115 1250 929904865 929904893
    0x190c091d090606010503190911030d08090316030c2010050406020c061803060f040302010c05091003200d0501090606020c010f2304080318010302040807140a050409030203030a1a0f0904 81
    0xb4081c90040c8c044180300000d03941c003030000c2041e0103503010610040790480b207020f412502d03007100c6d500c108404c0201d54006203c20205900a26143c101c01c00943e030313021442c0080c403490010030110b2100300b681c2403800715860880c905440c00e2651800b40380103c003940707602c01024594864500440c0f064010b0407810410b950141006007517a0892803c07600c1410500000d0724142c00542c81c000503c801c0601690031680040e500030001e101022100074118050980d0003954400240072410070045143c40401400024141500110340c540c104010303032045441ca640702c0800c41d803103010b9410719a600301180a41c43c0010345040c501d641075030002440c00840440c0340300c0014a0000340010021008000341002000e550740340c6040300c1908004405a000d240541038032900302c0d09080143d016680700800e40000054002000940d451b030000e022901c241c0400d41c01b5070800000c1084154041c403485070304030900c00402d48040105030100b0f0100c41981e0506028100b203401142c02d20000c02c440c190 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 929907365 1250 929906115 929906161
    0x140409020d050f060403110a0c03060c09090614030f0105060d0803092b0813050601091e0e010b090106080108100509011b031a06040b12190c091d090606010503 70
    0x30f070394000324415a0f214030444050f80060281d5429182c0f40c0e8001c5120011540c1004408020780d045845410007405d400c2c6011040c03100701c50740064070001c5409000d0051045090300001074014800b4141452088a08840142d1504041020a81d62102c100440c02e810800f00c2e516176032a15052803802940aa0075140f0040f0705400c000b48083c3c403039051841000302c1d035407507500e03854a9039000210043d5060007401e503000f42d0014040c0c424141c0c801603084035192001d00040001d030f44210111081d0b15010b0201c0c0e519060b2190705e07420a4138031a0300612083ca4104c07100d601d41500181c95182d50b220300100700f42c680d0003040c80c0c0c0c5800d4020788003038043c43c1804c1c0455801000041d006100040114010b20007406201d0554030300302041d14101d945040b01e0b00d24204803180203509a400061500301040220002c0c440102800c1c441c0302d80c40c410545604500b00d06028200390121200522882e404411204009030b808020070441c0d0495802c0c00d02c56100d4035500c812407055800010000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 929908615 1250 929907365 929907373
    0x17030408010f021804141503160b0d110a020d08071716032304060b01021c03020c0c04020901050909060103020f0a020105010306050f04030f0f30060807140409020d05 73
    0x1050207a95078010480c1140d945155090011303040140020356003c0303080003c0780200e01c00004c00030060240800c0130410000d040c0c036040c030742101c0751840035195900122508a0080b0b012109524103200d59081049005981401c000401c00001d5403141d40f4200441002182d00105041d0781c007441030f1100344c456803e0b445d04640342c0064011007980007154802d00190600300f46107001c82ea421003104090008104120940c0d60320340320b400252054840c080d0462099030000d007044d144c0710713036011880d045031b540242e6200300d09080c040c0350100d02c000340b0b0f10480c410440049240e8014003100e0b403502055406040e19600c11005074000c2c090340743d0714040719a00043c0502070b1070703040d03001c3c9050300d03c2010b040101d5102c07800c000748a01401c0750000c010070a240c8d1085c1c1e0320b84c054410840806040d2528902d006c032624180c40c5c0c008070384071031301e4942c0d1b04040240c000d103600f40c05650054003041c402881d0091800c0e00402c1904407545d421401030740d580303000d1810341d01e5a4482500c0150084111 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 929909865 1250 929908615 929908631
    0x1902070905011e140607020906030a0f1a0f130b1308161e0804170c0406030c050f010201110d02071518021507211e050a14040e011703040801 62
    0x2d00701101d00c48000103c0030182c018007242d50900422400100f00000d40780c9420700d00035a00f4015014800b0b008070703505200d05a03081000410020032144c98a100c0c01c1ca5010044200410704040c0d4409800c0d4406071127114100419402e0071507181c80100d03003003040d0301030030b0b100d920061403c02d08540008c7c0c0f0b00b100009030059480901c2944035203540c0701c0c3c03500780500034003c0000c0e598a5a96500142656810001000801480301d84d45400242d881c050f603209500040c000b03011120294022181048a55020459481c0c546880030055100b800280100b480164141c1045e201ea010303444a420b6020800c0e506104110030701d01500e04400800f0444803d0300688503144c0d201500c02244200f200082c101003070b11a032815180611b9000010341846a0991100c48101200401e1031080240c110b440900241c100e0003e18441d0010303450341951030310031020051050f140c841000c001c2040c104000c02100b005034442c0b0341155680174101412007202018282144030340c0e84407504d558282403035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 929911115 1250 929909865 929909879
    0x1302010507020f0307060f090b04140613121a070507050d0f02101103060405061002060712110313030305101d060d051e0c0108040f1410020403030210050106080c190207090501 77
    0x4091147c1030b01e440d00c655165403845d604510b4480d50050680100908550b480541000000b81000c0703800c00d0032464455841d08151383c119241c0000a03540c500c141c020440020341e8184010760004461b140092030648161a00e42d5181e0701c0c1202e003810044c0e00107100100f54428061002c1d02c90650409101410000702d42d00311540056134520321492512000c1a400c1c9032660b20f040b0080074a802034243d070b50310610260b9030f403802ca2400c180c50584400c81c0405288400000b944102944101854040e02c2401c00030201c80e030040c0400d603182001c00d402c3c059049804025505e04040f860340010913507888020414030521000010413903c0380c0041e401441e06e92142000b0b0b070303006050841e0304516011004494620b02510083c0c41a84c0112440010070b0780020181070340e40c08007003100e5120b14075401d4541268055801035006820040c10300c1c041e460f0394025580140303404c0c64109180c2c105100c80b22410311032008009204810200c0188625009102c0c0000414840c41c04004d150380d01c01d1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 929912365 1250 929911115 929911127
    0x92b0210030f2c07081e03071509061103060f040b120f0a051213090207020406030b1302040516050f07050106091a031c02070513060812211302010507020f030706 71
    0x902e0140400038410f0031030803504000b41d010120b50301c11340144960381444035028818148860000f649000800c090804a40c907030101120800c25030701c0019905549083c00c8085a0035800785002465040060103038a686007002d0404541c01260700288a081c114001085400511440081806102e000015025010583c4000c0c24011001d480300c0c00c0b504c2c000300070075109034000c01ca8001d0b9810014820460143e01820540380b0140c0f000800640300d480394504044212a5030100030f080ca100305003141003a01074590840d085040e002000b201d040303c042c10a01601100d5035000c500072922105100c025000340c0c0080a4030002000102e0000c1e07420a8103006c0441c640c0d00030300c0b0313044001807100c01c841e614020f0381200754007500a4506110401005101c80c488528070f950302c80ca80071403022014400e032030495960a20080da40d511aaa044140c0030b9440b0311982407001d03400c02c1040e480380e107105020034603609281c04c03661110644006001c40c05951190b603014030810b60040340b101e40000e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 929913615 1250 929912365 929912411
    0x120605040e060129121314031b030c060105010509011709010504060e0303070804020906010309150606170103151104091404020909012703030e0a050102092b0210030f 73
    0x1d00000b071403011000504003204200e01c48060990010000800041c82c800d800e503802421040c8117541b03241940e151500c41c0000c1e01a2030000381c0002540d11001408c10220701034640859002e54104281180d0298880a0510989041c40000210303005142c0c840e80176883c44081c9500c007600d00341810101a4028a4225000c030342c120300c1c0003440207250100006403407040d44190340d4950541d803140c1c00d201d4000000b5151605142e141c01e10b8078001140100c11800c4880340302000240c581c5454002010705504246418096000400510100303002030701c1c0c03085600d460080407410a104036440901482103501500080d46080711000100300c0100c042d80c090b030300841310740c10580c0b1800319080c02c9640c4d0310300b620403d04404106e0800d420700c5107007544400b170281c20300081c0140041c002500340700000c1000c4034203943c0020304000510b401c02e860b00200e940301e198100302c80d81482002c82400030540010b40f0440c0701c401e500410a01c02d4004810040518405002c4291003110b0b00503290024 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 929914865 1250 929913615 929913629
    0x60c020705120c130f020403061512080a030207030507021f0806040e030a0c05030d05070c14010501060e1c17070203120f0304151b080103110d05030406120605040e0601 74
    0x2518005460b2030650a0384490038002409400512551000c00c00c003a503060042c1d119160b21141501d1280c11184090700c0194081d400103e40e03032911074001012800d154004001000150340300e040400c7c01101500c06041c1541001a40c071180f904082d1b030a405001d2001394000020301c0100207480c41004460311030100c81d2101003ca4580d2010841626000307003d100450744180410301f0b106125900030152107020f8010f0b40c0c90000b081d0368140581364200d442c40c0c040358441080d41d003046a01c9112507400c1c041c02008114550514000412011786540b103180b188400030403108280ba2140380c0c03640456480509600310f80c0600107441401d42200c0e0b0164400e00271182c0c0e08580d100740c07504981a846040100c41d180d961a40e4540b41c0100d10320b1980100c1e00c1d902d62442040c9500101c08801007485030b115640d1641c0745180200c0d20348092501c003030040b920a1245400244000107803410340b00d5500f020100e441c880880c0d0b00082c000360748110342c01030400c0d485c01d80307144d030200e03110f8141d60340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 929916115 1250 929914865 929914873
    0x506041412040f0519080c10090f27140103030e060d0509010b13020f04120f1e20220b0d06090b06150706110d090605060f1002030d15080703060c02 65
    0x810581c0702c5410700203200d221244d81003594007c03000d00d0102d100100034003090400c541581e4450850300c829100b03a41058108040031548001040da11442101c1018407008050010500760100100c1200c030600c8010180030301c8411110f200c0c0d9032f541c1a034000e07043c0340d01304110b0703031404045440c06070010f00543c9008280b04400007101c01d58078000c49481025080c520341c5403134a4041d50300ca80c910000c50564080c10000c4c0701a000480640d401da0300d260404041840d000050b0504100d224100c0c0510355036041380f0b000862060b111060144800003072408440c080081c500c16002c017a11814801940c844030096000003045a554080c0040c079002c0d11400580f5a64401440315441d001506102d0341d0001f405008000303070300c40c0c003d46024880ca6140c00d051142002808058450441084600c00d880382c08006990804031649000c1a00440f00b0302030040482c40065102d10649022107417490b04d42c081800d80d6911414140024601d02e4220392101e0381d2402c1440061140207202d13001405 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 929917365 1250 929916115 929916139
    0x702040c270f1715040204020f0706020711040606080a0504020406090c0908010c080c03011217070b06030607050412022e020708010b010309020117190204170709090506041412040f05 80
    0x40d40303c00882100490303500404c40491500c0d072801c0c1c000340051040340e100d9000c00040401c1c12002001d010704510079500582c407503510340f404401881e0f404400c14000d6217466010003070b10342e20405031a0013000c510400666500d450002c50050140b80c0c010001c11030920749c5081140780c0c460140c008a4020200030031080342c900400319140b90090740c0780c55030b46a00b80014020101d960401042d001e11580700ba5520140c00711812042c2d402584003541c841009000f089110300b02840380541c8610136241591030b0904200401850510581c0003900413006100200089158505503074494076288060302c80c050b8054000955490b85030080b00c0e569400c04990ba403c95009018803101c486e030503121040c40040f002c40d4480c14060091500a603030345c91070b074085080245440140046c1040f200c494103c1040d85080900e002d505510240203140ba000d076000c00714901040003600300b90f03c00000e001921040e01c401b4034102148061617100c1d9000500010700e0400080900c00b1990180d510f444e01034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 929918615 1250 929917365 929917379
    0x40c0c200f0301150b280905041d06070507050312011511120712020313080f0c03070f0e0c120a0203041101020a05122209050105030618030702040c270f 67
    0x2018800e0010310484d2060050080031000406801003510b11310100e55641284040105039450105041000c2044450b0500c61802d003070040c5c0300b072074407000507000204900c6081030342c1e640c6000780b14400b08600841c184042000910468841c4001d004c1980200d58480f89184080261042d103c00456021000103503000c101040a000c02c84101400300d0520142d03488542d00c40d0018608d240450000300800360441d00c1056101d8050401c200080405241410306149041c84240c50b480c46540001001c01520341d14041075400d13580e440c02030920b29101d04490354002e0080181100f0030500c2e0408001d0340c6030244c5e002e18403580c000e20704070f1070354480f01d801a611022103140c0600306400103901d000203054034000038540601c0892558443c180d4081c60045402c0f43e5811048680d03490300e00400c042d00c1c2c1040040c0d0081c2c0c0c5116900e5004000b20781160341d038030552b440280640e8a0361200c1c0c41250044503040382004601044050641170103000381c00380c4441d8012600f5000e00105c0200f00c2c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 929919865 1250 929918615 929918621
    0x31e0e06070809091b1903180b0106080c0408070302040903051e0d1503050d0c0212100e1b1c03051c0207121b0303050c071211061e06040c0c200f0301 66
    0x1c030b80d500c0041c5000c4072440d51101140c1620700d0b400c141611031480ca4000c422265408e0281405072420000c20350400c20010304410002d88048800d04084c4400d0200030720110b601012607504841c0000c3c003c1e194601600d041c020000c0c2100010b00204008c0780e111082c1c0000c1940d00000c0c44200030000402039103125410544c04041c1c101e9002110b001d4180b4000e408040d50709000401a00482100409461403c910f400c01c244001d9242c0a003404000c00802c01d1458400300d44003448041c0822002046004004104105005030745000c0d800c181b602030400c44030002c1030036071110f070429500d40708a00a0360080404684d11102c0c0c21084107814840c7c050508502d100304101c13480b04005807011005031401130501407501c03500300070240000710049540001c0c4101e2741c565220700790103040c00a0030200001d04400503001124a806942c50b40a1440d540c8200100d5000400c1042c020701111201c01c010360080040c01c608035003425449628074010f00c3e0714000c07201031062300c1022040c1826 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 929921115 1250 929919865 929919901
    0x60b0406080a02090d060203070c200d0f0c08070605041d0705040b0a02030c0102120f1608010b1b0a031d0d080403060b06160b060a050607031e0e0607080909 69
    0x159000e0200e07181078283d800411029038010000512102151102c0d001c81c0e00540e803507008605100452420000e2a0301c290011003144448000c003d1a0007000c01c00c66040040003c00100c1a8181c0c4410850180300381400303000d42004131200251a000050502d074454003606c0c1e54a4071501c4c0001c903100101643c588500503681c0c810382040d2a00700300070010342062a951080d404180841c1a0720700c424805482d0041d90781030130308481e0501d0442d8212051007d00507607800ca2510388410301c0c0ba5001111641110081804166110403490503092011850b070150072035070003001d44040916503c001c0c5941000180f14440c80b840c0f82c0c840030004c03880030448c0010300c40327141030104101198066000400c90940542010300d0501911110411030f55801d804941d142030171000d0002c0c504040510a02a06044e070304107281000c1510b001e06540e01d46d101000c03403180c071110099020b520405aa1002040c05000191101c00070b10f8032002c26044010800d010302e01040c0021024649641c072055 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 929922365 1250 929921115 929921117
    0x801060314060f13240e0105100516020f120714010203040807031101141b07090203060d0b0705090307030b0f070207030f08210106020f0c1002150a1d070801060b0406 73
    0x40880d401e00f48414000b01341510341a1a60707030f4219a071000d400c00c0012078000b02031842c4402650912002005100040c3c001c94000c04a07040210061500041200c14103040894041384110451001039041070800c0d5089420a4009003000c00520340090044141c07045101040425000580120ba990040d44903580c5964020380b801c00119032502d89090030980103150080e04480c0e100d0001640c0d034060000044000c1900d844107070000800d21100f8003911544c04c003540b41d41007203c0000c0f0b03600c41080010700307000301d150b001c5031960340140b044072542400517040da02050340d20b082004e81450207e8405180b0440d060000340e51510216050054035130101512460032403945446d03046820101010700c50100710485642d00120100a0f140203051030303401842c0c2d0080040d921802e014002d0020b034040c0050b070020001c015004204500c0e500440c1d1400b000b66500e000f101c401a02204038800c1c14003125009a5852402c041800016507120748001d0040c150f940312050003600c42da200f030030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 929923615 1250 929922365 929922379
    0x61e081611010605060c0304030314040b0d02030604091e0215040e071b230c1207061d042a0c051009230d2703030318050a03080106031406 61
    0x412a207001d80030201c01401c01c1c0c0000035249843c1e0b40480c100c1e60090800d502d10360b0000c0b030301b00101a4080017220f544408585880c1c1014582000403e490041c98409160581c010000034200e0310f40d03034426025103810080104070446403150a41c080d42c8450402d03401081100058840c4441c1035044034112441741c68000265a00c1407003c032098081e01d0001440c2240524956020070f40442c030451021101e40c0701ea094082c180e02069140240300000c15006604000c84200d9444001c61107008949040c00c14408400e4a0006c0008411a8204440d480b6282211b4940b42a0182c001100c0d071120300d1a10703500c028403200041c1c41c1d00e01540e0700148150f000e00511030040421341c02600500d4440c2c4800b5480b6a10011054501964440e6440301503000b401c003404544e0b40451840031414026896546101000140c0032000700d050202401341501e60022a1110803c50040d800c080c0c1c004013602e8040b0100d1900609100313080c402c1d000000d0410039003003901c0c5980382502e03011b40c10091201c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 929924865 1250 929923615 929923651
    0x71d010c02100e0316080303100501030917032805060109120b01050f0a0504021b0c1206010902030601050c0d080906150d03200d050705010c030c0c0f0813061e08 71
    0x2161043c42d01803c8940501510741c0d04818000503001c2603028200107005540c40349003103019040e41c006070340d0186040504080d450b80c0803900d0b204101054108084443d580e95843d0201101c40401c104c00048522600b421500001c20865000f00e00918090340c03183c1055a49800c00700c0d17030070003d01d8007034540071154004200518200c4090003080c0000307441207419542d0b41c40002d049070441150220001c1c0d03844084c0c0b60300b8400303120303075159240c04a8644403c03107a041c03c00c41d030743e0710140981f24044d46e000020408aa000b581a100508881004c480c00b5001c1c601000b8201c0307000391081c1341c4070300c80d420101c1d4001d44417046061703070810041d14010030124942c8040320081e1241a941403481c01c800d232401c03240c190500c8016014601c540343d050383d5000d00c1c98104d0071101c18803441e00070540343c00c5018007603580c0840741c081c0303003502300212899602450034256400d1190000b04c0c0da20b03a41c4420001034460300008043d8901071540700d4909094028001501c142e00205d911405440564a103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 929926115 1250 929924865 929924867
    0x6140606030f0703060b0c060703060b0a0507110424090507080402130f0e0d09060e0d03140703120203071d1009051c0f0c1e0e0403030c020a0506071d010c0210 70
    0x40b85912020030314001c60425507a03001e1a80315404010101295003014003040502905070045200905180142070324240181030000d040b03010f0904003c0c01c03806108907840c140c0e50b80d40c000012041407101d8544485600d600c0c4641c607452a403003a05402401d140001318418060f0003070f28170858003c0c01000d8a07440d620341800042c4400411083c03460f41d90241c102114000b04803c1520007901c2c0c8a0000c05420f040e03014081701c186004072071150082c0c007015000207601c041c00c40030f8000c0700b81c1d940b500d84030743c1c0c541510540d107101500614644013008100b1004d5002d41d96040307400482d60004058001c640034044250030520103c80400c407400b004100c00c2c02e084046003c0900c902010744801102c90703442c0440000c3e8a03800f601c52300c00c07100b0309010078000d481254800c00070002100c1e2441746840d4101f48a2640148040d007415030755020703074828500038000f0250039a070000680c2d403c0d1030082000b0342081c044d8202c5582c103800e45030385400554051005c60014640051001c1401490500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 929927365 1250 929926115 929926141
    0x80109110f0d0609060507110109120c0c09020a200a03021b0414010b0403021504060c020d080c010e06460b0d030302090102010506040b1003051f0801090614060603 72
    0x10030789402203a8480454040345051098600a40c0716550200b03990529180043c141c0c194180f4400e0540d24200780c0c1c90001c1c60030f800b250103031005420103043c071800c0c40c1401c8a04000b19400558100e000151142c2604e0380440d82c801c2c502c5000319440407030860300349001c3da680d203104002405a40034035010107010300e00d1407400c44513a40042c03000c12140076001d01c1c00c251800c2a40280d040c40d901040c18004c500e84280c44010100510401c0e0303091520700080205180103c2c00041d0056411070203400900003171108036441d0003c000000e11200180c00c1703080c4d581da00200d80f43c1c112608a4000c0441240c1440c00e03440e20745101001c4018401541e640b100141f0002011501034030345d50720351040140e04c94110000515009807001030311040303070000182c00e5a600508642c440c6141c1182c58406a0381d028010b034402071076280c00101966401c444e4444441314051802d46100c3ca810b0026501005411201240c0d01c122400e120000d400035401984610507240154860803e000051094042c05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 929928615 1250 929927365 929927389
    0xb030112140c0307061d0d230c040203040b07020f071a091305010602030a0e03060f041113061707140d0201050703170a0605100c030e060d0e032208010911 68
    0x1090b50b050400304000a4a800216806000801c1100d881d40c0d802019000c0940d4800d1010783c1c000c10101800da580a84000d040102110341d01030584039000f40200410140300d030204050803c550342c2c18141441d10002c007003103c180c0014460981180e801810205260040701d040390500c40340c0c01c155403684d0090f40c1013602025007141d032144182c0100c69050007018000c0080d50040d540e92880f01000400c40000d4490240c0640e00c6501449020b400d0f09001c5a44140c01c2106400c0c0f02540310700094000c101100b03120010390414038045040500b4011600350b825400c030864480980d034140c94210340080c4c0c100700360300150492503400554068401460713001d00c2440c0001c03206102c0090b80300102d07400c0e1443d0750312036a100014481070074208080c006441c402e080220114000d5a8000c025100007200c0500903580840d14020200050300300302001d11a080540c0e89854403c514012005510694251201d1040c076000803060700611400580d59081481c1c44c401104d0b400c10301c50150711b04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 929929865 1250 929928615 929928653
    0xa0c060c050a0c030320010b060703200d020c010e040b09040206030903040f0f0609063b1807030b010807080601030c110a150b0a14040f180b040b010b030112 69
    0x91850180018480d0f9a424081c610130b849079424440c000c1c4c2030740780d11030b4414031200d0160f25007050f203881030f40d4000554603920740c14540281000d585100501501542c00d0000c0034500c40c0c4c0d81c16042840e004980005145800c0e6603405c4021032900400054400c1c0c0e0507040d401514810104015003483c40c01180d000c85000c0c12286802d944440c1922508096801004548907401c0180b1040d98461a607000a0445190450400c1707035000c0c0400b46921169000c1030b101000d011885204c00542c3d56010071040014544a03042c19000c610780c56801040f20100e000910304141040d10b58003809150b40541d0700c0d0b964005103691410015402080700d1074251080c0104150810000c1808009000d40e2510030721490500000c80780a5800741c1c3c81c0c408807a0310030050310b00240501100440104a01e100071030f008103000d910303500c4c040020301c224403210400a41c0300c1700c004107100e4140c0182d40200d01c034020f030944580e80c42d001407449000a0007411352843c0407405407004516498000d95800d000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 929931115 1250 929929865 929929873
    0x10b042027030304030308091005010b0306091504020c0a0c0f030506070c05031e130e060f0411040f0b12010f030f081308070602011a09130b0c04031a0402030c01020a0c060c05 77
    0x20000002e803454000b81d00c00c9002940c400e00b000100507040c008100070402281c014441740d410a0030f600d8a6000007010f460190705032600003003404040030503848480d40081c02c01c543e17400c802c252203522441e4101098500746801100080d1703080d248101c800403280c010000d481151111141110b41410080c41610b09110034002884840220024010040310101c002c913502e9600d1348001402500c160300c40071141d5480401c21415071a0501c81c4d40c400d120803907000412403618580d00e04940199000045440d05d034074004180ca001d5030008000402109900e50071030b030390311515140d10b42d045000061100d051032603d00c00150864000e002d1042e0b84201c07820300c86440348150380c900309490b800400141c0d150800d88000c480e4040302584000d6090f20902c6451611b604207405004150800030403080c500800941054400400d4a026650029240d1040c2241800388924072000b038409074445e004041c43c503102c640c000104643c0c0a0f87c0010b42d03121481c40c003201030f82c11038408801036519000d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 929932365 1250 929931115 929931187
    0xe060318010606030b030d0809071509080f010c18050607060207020f04050f1801140f10090905030702121902190e0907150507031d010e12010b0420 65
    0x2082c05200c01414043c0e400007200e449800805103086103401912050051100c240030b00010301103104820780e558040700e17107203280301c2c00000c844428284d440b51005000700080d072602c490064200d012400219591081400c42450001038646803912900303034003031010402400007030700320b40140404900050401c01428104400b0800351442100d15a0034000d4038401c1203510b00d00c0029a0592480107002004a0002485000b940340c0c005420400496031041c00a440180c401c518900a0403800fa02444603050f24070304140e07a81c022102c00c82c411400c040505c545040c0008801402c0c00d000c1d1403014200705982c0a005000c01c40b41e01c88068100c07140e001042c46a020065980542c01d000010494545480c040144849002840d6010404204441c0780805d9002100b80c00c40100e01003501641558034005840043c10710b1740e85a04200300d460003d0350000c0650244460034401d40e8180030098032884c0ca00740700b070311070402d2002c035070410b00000c1c012440d1007181d200010040070400188030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 929933615 1250 929932365 929932411
    0x20705090712051003150b030705060702040624020d0503060d1103012702040b030d0c06230a09050c1203071b0b042405090108061c08040605040f0f060e0603 69
    0xc000b115280780b1481514810020007400f0106e0000172013844508001d080040700000780c0b6605180305140c464100840c0b44019980c41d075104100400c010611703403205241c462070402142005d4266000580190040080c0c1540144205d0f8400d040040c060440410159146202c04840030305007501076590b42d00d149940d441c180000c0b01c1c100e071034081420a1084501c100030030b65481c056400e000e6000180c1801400d034010f601c00f00c486a0007900030640308041c0e1100d01041c03c17030b904500440340b5944140020b1303410f41e52144500500a0040d142e40012030000d00004c7c014030a4002d5956004000c00004035881071941c1100c034400c1c0c004041c80650f100c0742400140c1064000b0248010402c40704a03500307086605003200179186051090802c4030600c006007000900926060250182d80c3c1030103a03a6400b0b03003104420985c040c0c045030320745840710001032164000e401a89001c0d070130741d117000c5041d1084404403011100941e075a15000c01c54402440020707003010b010407141c2e4603500d4148000c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 929934865 1250 929933615 929933621
    0xb191814120c071a070b01060c05010b03070e040b060d11270403090815061c06020c011d01060f0b030703150b28030513021203070b13170307020705090712 68
    0x706a42002400e00c0c07414036000410b8030340751302d0040907592003c00214000070741d12824141103410500740001e4085017401c00ca4050007112150039414040c926002c21500e03c1c0c0e0744030a0056020b109600d80c0b964038401488107521220501400d00d048804601209292a83d540c041c0c0c031840d501c5c0030324002d080300c1c1c0c0e14035550000e45040b0089550b075030041c88405400c020703000b070000403000181c6207070800d00c021034207105034040c00250a284000c1c10a0500ca850f8045a0070001110f00070856006d0032840610202d40708a000301641d420b2010000e0008545210082a9005281080d1a680380c20390243c00401c51582c41e0190685004030005800e03c4600240110700744130040f03a442081d440b55204140360701e0a040100703041c83d180070300c00d480081c0360421b458598180c500e1000c412903403851518600841030010144c1e040303038041040c001c004250103c070b1244144400840c040c01041c0b8044036002c206d81000c01a4410340e400c108602d0510280e582007030300d5040483c1c214444240d24415 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 929936115 1250 929934865 929934877
    0x309030f0303070215160c0c0b070b060a062613020a03030221030c0a110309040e07142d0613081608010b060403080915070b19181412 59
    0x45a040030041190081e018404c400d17064200090581035171616a840c3e0782808044100c800401144500c4e250420070036100c0e450140150608aa440c0d441d6441c06001c140070460750315014403100c650004586008100c0d10005e0b03541d444030b415000ca07a907450088106001400e414000c1c001500510158840801d0500554001d5020700000302e03140041c00a10311603000c075090080820020844215100c10507a0305074240b03850a2100c00184046041c0707107000b861542540603180035a1442104400a414401c440410003c003c503883c04604201c4520092071181400c40c80150303418941342c082d41010315800800514160034861200c403403100b0003280342c000d43c8040d407040c881c0e400740440e04442d100080c07035114000d0114540c8000403035042d003d41c0c40010800340300416014a190f894503060500d5444021085845200504101c40075030300c1078820340349041003c04100b004122270300030000200c1c080d00001a8210310350350b0307105e61611420309003c42400349000f1241c07200d11207001805 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 929937365 1250 929936115 929936143
    0xc020a030c12060b0a030b0106080403111903090503121902011e0b03061b0a030b010201181110030b240705100c090501020102031905040213050a0203040c14010c06020c030903 77
    0x101010b020300d00307101100d001000b400c1c85048070410400c0018001c000c4181500c2c61468203404d6912079140c01d494264003601c0280d0765029120305014130000c08039010510b540a0341e00c030007074556650305240d00c0707000904003014071180401811030351b040c0c0000c1801440c24244000030781100c0a042041d0170b08081118032054607100e80c144045407070200b00c0980c10070800d40204a407030501d500000304034800c45081d401031507104c201403001d9038001e5010004c0f5514881c518a1034a00ca071810203d424200d801644c4540c0308114a1a2300922a11031802c203660040e08410340307101d559109484050307800001c81c4420300108032200c0007810130701143c01c04a0307402a02081030880f10754003405403815904043d04680c414410814202c01c04100200e00e101001c0d000a101d44480c00400d101c03c0f40d039004609103a05140c2031001c0c0c00c500790f00840c403e5024a55102e00b582c1c8400c080a9041d0780c1140745400101c01d4032003030300441c50b1a4010f0034109070020850703150143d45d00200e8209840c6002c081 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 929938615 1250 929937365 929937389
    0xf10051302010c0f082d0307080613060810060f0f15080a06051206062119030e06070b010602010f1a1e040905060414010605031b040f020301090504020f040506100c020a030c 76
    0x124113145458020110031b110f05401d5142c040700044c0008001040300344541c150710b24904c6140e0095214401515108054654580459101c0c402030203203031058482550b405400091002c00002c204002e0701c2004080065110508404030307501c0d08064502041d45039100d100085955440300241c40248100780501003510306041040514104c1e010210b0309280050300300c0c420b17000045403490540140406011007800181003c07600c8c141032411807900f00400040d00018407180003031440c100ca03180c0c1e00070700610381c000a410054074504106c2140004010525440c2860018008031128650080c0301c407070b20381d80200040a03212a0700058407290411030078030040c4802c4645031032092500400921a0f28505004241d407942007554202100c580203000c40c1d0b0a83e6960090380521038004400d64036541c42c1c240c010700400054808034443c002048404c0c0f03082c00e05026442c401e1400030012040d003490680300381c94594100d139049a101c01c02580c00300020311350303052840280c520780d5414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 929939865 1250 929938615 929938657
    0xd021201033903060f110a050705070f15030209040905031b0106050411040506031305060103030806031c1b0206120103050312010803041802090d12020f10051302010c0f08 75
    0x280b2607032403042c0c1d000109055800c20b21031120000204500840e43d00442c00100c01e0741100c0590000d0200600e400c80035038001501c02c00c3c1c1a40300000d8001540551b05541034030365608201c129041c0c1070321401240b10b0b140c10001b04041d009038090114800054000708020f1050b58400341503034443c140b8000844000c511040c0b010382c091085402406080d1810411903214980702c41d954003642c031816108100003c0000c07001c00c810b45c3d041104561001c11a182540c5918002d010300000b107034071900a2080e80318010102219884481541b50b17103841e03400e40d25814103440d41400c00d00e0035050740c1102d010070200c01c0040c4076004030b500031400342c805540c882c15104508040c084040e0b204d040070f07600038001407180c00ca0307103000e10080360b0030f030307940160341c0c040e1080400d0307181461980103005110700d50361003d01c0ac0d40225940d01705940041c2924802011101a20101c40042c3c803000403900e2542c182100650240f00d2020b6054040d581d8440c003011107585508056100e006030000c410078492003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 929941115 1250 929939865 929939903
    0xb040303020714070b030a06080601080a08131a030f0f070906140705030c101d060a020a0306030210020706020618150703090b130201020106062c1207060c0b09010507050406050d02120103 82
    0x5e804089c00324400a031110f54504649140d0f903005408001e0b00e91040000e42c581920219202070009060203500700649158406000855400c1142d800641c112743d82d00144103a201c680b04640300380b103152101d00302242480021158601d0002d0707102c500070010480301d07012800420140c900307488088018558010660407050903542e8040000c1c985034850030aa1001400204405a0200005400580b1007501500490142c65254000ba4000c160790554024241d0b01081000036514540c0071207c40b0740350381c0304d542c2c0508181c80c0103101031303003107011018030f8680350343c9981c0c2d0071500720315002c103400700030f61900e0006110170707144258a41c0075403066408658081c041d5500602040c10581c1c20707251100951006034414201007a00d82e951020b181c40c496680c841c5802500c100c1c00d04075010283c895601401410010100351a003028070303800034402d00300502920703102d11040c4e43c0e200e0500703140810981d13160704806855940304d41c080c0188a181101594054000c40c0107800240d00780c025040c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 929942365 1250 929941115 929941121
    0x50316200c1002060f240a230108090d050702040f02040620150c030403090e01090b0a050402182b290105090c07050a02090f040c120b040303020714070b030a 69
    0x440c0b030941d0458420021140c00c003411440c0e00110340421841044c1c1d02040728440400000c1071035500000220020546400c80c842c548050840e01c07a111140c0030540b401036400600842b50700456900401c00c0c40382c058400c40191030040e1000e0030214250b144003000c00c0a0382c00c2504000001120381d4194055000c5150f1090841c044140c00b034103800c03641c5c54107485803401c0149030b07802c1000f00102207001c051184032440002c10071004040902e5031602c031007038003805001d01001d128003040d40b070100b901c1c41c141c8211460b2a02c9900000355510001d4103001030444880e8400c485032502103441140800000c5100c14014400c0031201c2c841004c10241e4000c0e4005c8840e50040103101700b0040c0040d44031200318641013140c01d05074684400709460306502c0e090f00c0c205c0013034104030b1543c18020040568189540140e00c1011034035101d030340307405c04200e103031203030580c050000c81002001c140460300030360040550034005d00d8950905030113a402503281c004c80d42e0090164510010030001c545103a88 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 929943615 1250 929942365 929942389
    0x2070b0702070e0c07111c1218050f010c0f060c020a0209150d15020d0f02131e06030207140105160305100e18031e09090a06030201050316200c 63
    0xc0380030700d03d4100050651130a0060500013001d65440c848032010035542c1c01c40c20311a48402000003203181344249001103841034802c54050118000d0302c04030003407150110f002002d548000d04010411200c60004481041032030304184e40035440381c91090049010750140c80301440e99034009000c120f4403403043c06002e100003803051040b990321400314060b0741e8441008175800d940110032041c0003140030051070020300c01c604d002603481c0e2903c028a800f8084a0f0050303d444078120300045015541c842c00300c4102c100072a6003c141860326002800224003d5000d081c1c0c040c06155004918100d00881a086a000784e4030482c1e9400e1150214124560600031135511424504065040a00d0401c0500c02104050069410081140612182d00c141001620307101d60751120512a00b00b401c41200800ba808251402c0c000c181d0500000c9040d80280106e80440b50706944180c1780d50390303404216005040c0001780f941000951401001113501400000d408070381d4001c042c2140581a10800c0b220340300e49 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 929944865 1250 929943615 929943629
    0xc0203030c0615090103020d0b0a020c01022703070e010909061d03030a1b09090b130510063b0a0e010611010e0708120d18060c120509070501030c03090602070b070207 73
    0x20000500042c3c07a80c23141521407030b51201112100e500c03a610401c000e4010751540780300d00c0d03201041540301040308440a840c1d0048403081412415504420316844a110307009440c01ea0402000410184c421a0f01964116024080c0000c0680c540380d8171580c00120f01c041011a07502c04001d1080c2494a44a15048100c0790f00d174466141c2101d681c0038001c51141e2041d1002c95684426210042e143d0940c2c00e1103120031000c0c00c00c40d501c1c0ca85041c1c803166025005001c0040c00444000010000c0540c0d00b00021640040e4600450003c0a144110340c401d1540c1c039411090810700010401d41c000d100501a21960300d600f4007600100e401e07e0300311103155500c03941320b500c00c580401c00140c0104110200c000312034101a51200584101c4c006446040068542c0d00300d03460051040c00350650084083c0b00d803035500c148900303040d0350020003a5030066400e1841d41d00410000c1255600a9010100d0b00d940c030300303000ca240da4032034803940101e820031413042d41c03250304120030450103070760521050003d05a5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 929946115 1250 929944865 929944879
    0x50108060d031e14120f07020106140f03101409150c09040b03030412030e0111011b050a0905060409090b07020a0b0c090a150306080c18160c0203030c0615 68
    0x3064900610081400803e5000c10a020b10503030342c0c892180c148650010006141d05560340d500400d80aa0420201c1c1da510144000d0008281240c7c410b0158404443c00f200b900340c080002802000060b05c54485000d60510030300980707202428441c062401084619a0b1036002440c01405050511400d040d510104035005800c01c0940028241950340700301c81503c0000d000e41d11000424a50b2056402043c400303030f240742c3c40904056001301282140882a0f940400d00110902d203582030f0340d40249401e1854440700e241c04951407060020b401c01b40345601c0d1280300c075a954800300f0f00e01d81c01604400b61040d01ca1004000340010710500d80d400030741c14070007003040c104142c440d031228801c00303490424804000120300313026568030702e62003018202034a45e03c0043d8104160181c0102110320030030855026014101e50303107280c5030b80c16035680e426070300c07180100790340e0719080e506100c0c81100181c081c032061503024009038038100040d0131076405000060a05040840062558192410b02e151103004c2e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 929947365 1250 929946115 929946139
    0x20a060f051b0f0601030803190203151203160515010e0603100e0c0a060c05010e0304120212160308030414011802092a040320030304120804090f020405010806 70
    0x35101044070100c210400c102d80394002c00041032410a6821000308140780700d05000441130159200045004160003401c10b0b00f100700f03250400c01030b80000c88aa0310048914500d16a1a0130501440c60300c07841480240d07440c22501d001c40c4000e20800c0b844c1910b15512462040b11301d01c0f1102540c50141c070040840106038942400020b0b507401c1000c880145207070725003000d0300403e00100b02c0a03180c69001024024282d80302c0d1401040340e007010009584642c20869030f5250700c5000b101301c0d003c1e6a2800e40300b040f524102c6c1c007440705001e950b0203074076070911502c02200c0c1c40d0141e031602840a1071280c50b082d41d41303040a0528607031b050790801000c15141d140c426841d40b26000000d4407402e081e81030360000031560b02c81c510884107070444100145c942c2c46c6441d000d25040048001401905e01c0345182e040d0325449101108002c681d841c0700160598401c001c00d201001d02e030040310041c948181e404903d0aa1913485c583c2c1583c601e204c4003400d464010a0502c103039a007040c40a54404019128840c0c101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 929948615 1250 929947365 929947367
    0x40b130b010605090103111218011130060f0d0c050402030c03070f030c050423030f01060914060a1202030f03120114030f070b030c0c1c081b0f09120f0109020a060f 72
    0x52805007050b50170400071042902704040079045410304043c816039098442d210400800c1107002c405001c0070b41c034000e081d40400107006001c641030080c44003804d0f03003046040003010300c50344a6031f0306015554000c050740001049c3d41c2d10300040d031042d4541e918241c2c0700d007008070001d0546081001d2080505080c45101200717503500c4026034003155400e800e1454030b210140c090035840c03141038408036094050b888000490080c1500000212446100304200603041412403079a086000d580c070359841400c81a08100b41003c00c408000000e0000301030785d2016540c2e40e281451503102c4168904011342117401080300c90007400c200b414109090380a0101da1880c204103903150821401195801034000c00481c6075500e060080e600c030980441c00700c55084010311603100da00c143c0b105d4410001034071031001820480e18942015007001c40c3c02c08440c10603004001e03e4109800c080076050b085001d410700b885980c0810003000c03244905650002504800600500010507401d40081051050b80e001000000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 929949865 1250 929948615 929948647
    0x50903120c22150e0d0b0f0f09070b0711191202090709050603070f0216080f060c040605070f0f0c032f011d0a050622061403040b130b01060509010311 66
    0x1040c3c0d8074000601060490000301c10010200000e4081c1c85080c1c00c10001d8800c0380f43ca82d0240c028100c0d00400da6440f03900c281c0c3e0701e600e2805800c40c90341003446913400144122041c140c994000801c80880b000880b4100d07800d01c40c5d945e01c0b00502c4800c4407000d40a5092149401c1d030416824540180401d0400010542500c00070303100a00b0400d003143c2c0d56140a109204401d40460802c080088080da9068141d0352250320444802044c02a44040340002e66810215401c4560701d8a4071420040d19458403c0040410101901c1141580c0d80c4c000004a40040001c09103125408040d01d08107200b1190b001d4195069107140020b134801e001c0102aa0000c90280c1c281c02101c0c0368148154a000100b514080c2d141d1140d0380002010640d1070b0a2104607003041c0084280135040c2900c1a51444101c45038521349088486950040001c103021038420000e5980c090725030345100c0102641e80c0e40710f102015090788104001040850b42010070342e8907005400103140ca0303254072410b08002c807410b5026 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 929951115 1250 929949865 929949899
    0xc051801030f1a07030b0315060108010608090c030d0c03020d030b06040512011b080610050702090703020f07050f0622120f0c29130b0703050903120c22 67
    0x115041c2858408200280200f8500c0c1d400207104094942840c84024020344a00c485003403182c00782e1840080040640c1c0c0556120b100b050351285903903441c013807041d100b007040a0081903546c000c623560609940c8080200a80d8211651f03212480a4460b08000b810a8401442d00042500301052500b00ea40d40c102541d094900485170b10703810b030210545160051110100d042d0702c1007144030001d50060f8102c0e003081d10411080d2040091000099022600c0d885101e4000350311541c62070108101601c26809015504400100780349014215210103143c41d442c078000390080c0c1c1c04034003000f101c02c0d28250a0500480f84441c0d01c228460140d4034651601c2c44860313070008200c6007595090700507200700f5113006491b400103040f14411208000c2044903405051400c0f08041e0600041044d03066481c14041000341c010441c00019160610308901405001e014681c1512090180200341821036007401c1c003501440c007203242e950313150013210040c0081413980e24900c1c41d51405c00300507580fa0b005500c12 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 929952365 1250 929951115 929951123
    0x16090b0a1a070c0f1706040308131731050102100b0a0b0d0603060605010c030210200a03020c0d0201020a0503040b060a090509030901020609071a0313060e0a0c05180103 74
    0x1550325042200d05070a0040e8440a00142d80030759001070340d003803400c03400010380340000111034a08622078041030382d51000380c0d4003c000890100010300b8520b02c4811500c00c0c5442007295140b803c0e5004505612030300003021078810b800b00005082c4420f0003200e41c64460720400080d0548062508001039140e0061801d40c000054860002101c00c0e9209040240541501001035803500280c4003941c00514081c04111003951401030045a20742c00340c2d02d00880168036500809090b0601900e01340078007540c1e07a0005044a0f180340d0702e5a10000400500540546030380c005881c0c811081c441450310702c9012a80c02564410000300004580c030078100e84e03000360000c4811545407103440c04618103018980c4001112460f080c14009004c2002c001001451400d0b82150415202d0482d400d458078824850804001080740c840703095036002d040a140d1100109008018550840d00e919041c1d6031400711034491a080031041d101004500210b020203000142c414200200040c80305100b840010f0201074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 929953615 1250 929952365 929952389
    0x30501150810090912030c03090b01030f061b0f0815091602070b0f0c1509070909110415081002040f061209320a020f0909100e16090b0a 60
    0x20602d90071448000000c2c8041d110810980f001810060341d90b96001d11001c0002e401e11145050aa12900039040000c1d00103540c08206d03482c540d03406813500f03100607045403820303280c2c3d0140408882d504c1c41d0403180041900c4032000c281c0c90030b00092041100500039510290f114141c120140c0f0b0344485d0a51140c00a00c052010311440c5409a1034001aa03101000d0440c0009241c00300100000103072580181440844a00005040c00040c1c480002c0392020410350000900300121b0341c00f5085a2400c50142030b9810b446007071000481c0550701d500d0720800156440c0282044035407802c000c1145008081c86c411810542440d00300484600a807240d4010010b8507105103070034015660000c01c0f0942d220031060780c000c81244111151911a001c0c190180c0b141106d000580031001c58000c0b406640103140c40b00e009005000c0024090010300008014451400964030843c941c0c4a1f080d90750001400400c02c201c942c0c41d01e510481a5504102d8650b410700043d150541c0764008010117844420030b40c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 929954865 1250 929953615 929953621
    0x101205030d200a0f1d0d0b2206050f062b03091203030c110304080703150b1012181e0525030215040614030405030f0d0f0b010305011508 60
    0x100070800509094025000b40020b602005a9000349000078106019100c0c01000009005070419051000c00004d81144266907020700042c05100200d61040c1071200c10801101510751441400416400880d01c0326562814804002074001e003807944a04101d5000c80700e10240030110200907800c051810210b201580c1100400d80074050300800340c40d00b110b084003021140c0c03c005020745001504480480c02030300d142030041304040219010340c0d500704002c102051075540c40740040d40740c8115142101d90780790300034096a61010300d010700508140c0e89082a15100c42c04000441d641160b9440d884501c2403c1d100c0068800c89500b541741090b544041840c030301900741142003d00303002480d80f00904010305070b80c0e1100c3e8540c01c8002d03240280c55000c800c1401c404112001d2003a40503d00114808400381012545028011980301d442001524100200c512440e0002e810414090450a03150651480c48403c00e01c140711050000f480c0502042d450000c120018040003104941085041800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 929956115 1250 929954865 929954891
    0x21011208160507150c0341040b040602060108191109070c020a06020a0c2312030909010e01030312060501140702031e031306090608070e030c030d0305101205030d 71
    0x46900108a0414410a01104d5400042c01d4048a42003180443d280480c03101c90300c4071003160250120100b500111200b5144d903c1d00c005035140d0700300360321200070410000c1070024464024000400e00ea4000b80419410050b00e10705003075201500c0c500403d40110400003040398245450101c800644401189031100013044031269000c0c50040c0d00146503c10028015038005040d0b40418000ca06c6114415110b150400548000d2541d03840d41c544400320350b03081c9281c6103500840c000703521000c0b20700d8003141740081740e402a800d1384004a030b0184140100140f503000000c02c012118107880800840e8109000030342042504403034151400384c0411450110340302000719520309444c0304a030003d01c0707410541c1c0d96902e41c003082d440400e0031941d0f0000601c26000d01404030650720161524082640d030100c08a89a81000005691610940c00c00c801c840d1014400007400000d1907501007028035006a005012041e04e80c06242111041070894000c00c1011007500c1300b08a50139408070718405110a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 929957365 1250 929956115 929956123
    0xe04080702120601090e0312040605060109080111031512060f1302040e100b0105130e060a090c09061d060906030402061c02030a0516021504080c03210112081605 71
    0x1200941001d20841d0302c1c1450305002925904842d0070040c14860f0030f00f02c1a0450b1640100f0410010100d0858040f5002504a401c0740d039001d030041c5010140c040c0e541c1d80c01825500b42c00c181130000940081400581c4407660343c2c1c0c4800d03110030b4449000d031882d01c1444e181c3e00d6030020728002a460120021411070a0046810030100343c000700103011218030038038031a407111600900324100d079190921341c0c022075000e4000d888042000403104100e807807400e2400440c85100418445c1d021000080c0898800c2c0f0620410074600741a69410340810b05118002d084230f404888071030000d203c08100f140203641c560007194003440341520019160384840c80410030b0b900440a01c01540792030f00f001889900d0041e4007070b41c42407011000900842d01e4a04071042011020001e0b0b10068110001c46182a4444d50300e45401c1803103030510620f0300c40e10400141c216000b6402000d0310003503068103e00610a00880d0902500f5003601e01110607803607688110140c841d03842080c0c18200414030182c14800140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 929958615 1250 929957365 929957377
    0x501050d05070509030d090f1202060a0c031b14060c0f1b0a0c0e0717040f020108060a15090e09010608370c080607081b092b1703040c0e0408 62
    0xe4100c07100c1b281c0e46400641850312902881905060034500099005003000800d44030f1500036210301d203081c803c2e60301110854412041941400042d50704101004095181070190a00400b00385072002107214816007404000381c40407242c1d2500344010690100c224040340d01009070386040c500c20040180505041c0003280c4070240c0b40c00c02841c070020740c502000310828803e140541d0769460070b2540c0c001152810800740d9002d02459604112000154028000c0503000701004001481090b550b4002c6991460030030300c00c4000403036801003003104800c50303041d080d00029808028040d02d4104013450f945c8100e10b41304500d001d80901e4800045a0201c01c400b20000c091100307000711000c0500b000242c501c00e03807140002d588548800602040e2150f41d00b08d00540340b5180010610390f0280180d000d03604141c0081e86d21801400200035000c441e400e0501e400c00d0000700c20f000c1c0f54021300304803113038a0003021007021010003002000700064200c50381d01c0650300518286039190700c40c1d00f4041c2c01340c0103c2c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 929959865 1250 929958615 929958619
    0x11d030102030c0319020703081603090f23030304110f06120906040c06300e01060e04050712030e01140f0d14060301023c03070c0c06090501050d05070509 68
    0x8203001503949180001e5101c0c0c5c1c00d2000c0d10040ba8602c0503010101c1c42640005800100e0680100d0040d6455040540c80352400346004224400da544030781170040c048180c1291004c0c004442c018044041202d0040310a5420016606614090700d86c4d100701003450000a106580e0b9140d8000140d032868159602c0c0e450740725010065140242103140e407000140e6043c1d89840e024900006c031248541d110f0b840c1c005000d44200404030540310700200403445094a1180d00c3d45480b050b01d1000403d109010040c001c1c2c084042003401c09040032410580c81c0e400030444c08403a110303000c000c0b0b85c000d0f5040107020001e18061a100c0103150003d4545d000e24124481e442c8030026240038100c1940e00b09849004008060b0182a100e040416080303100e994154115003500d841d00c40144501c02000c1c035841050342005c41c107000808070070301310070b07500803034058001c6981408400103011881c0c04040181c40c441c246940081d091030000f90540c0510622008004d07143d10008075154458020b61b41c02d0140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 929961115 1250 929959865 929959867
    0x4020315150a05090c1b1c0801050f0901033c050a050f0304120f02030c1504150e010c1104060b04061d09070c030810030f060228050405011d030102 65
    0x200303461a4845200748407140b48211020728000c07a5600d81003103a13602616910030f4042c81c00408080e42d02140380c120214002030b01070070084c0340204518400303803484011655641c2010b58103000400c0524131050f40300d14013841040c2c005200040d441890780c07054078440300c1c5451222491114003240c04401c08181000d80c2501000c6008100303001400030039052190b13040c1c0e40140c03058040382e5500d003d58466020810303130a00484011511100d03008550314000b4003607c4008049201041c1001d07484a16110f4180000804005a008040c103040c3c0b180030034a041c20f801070b00940000d00341d20b400031740030300840c1d0810340c41e01c1c496075582c0c003280c010b2641e0101141c444c0c0d80c541c0b001d400c2d01c41a00ba5080160041441140d49140c442b4441d8402d0381c894a45048011407510105c1e885400102030000709904001d003c40494130260b1510201e038400c1201584e10440c00f08401e2108201009003003012500350104540c41703820805440c1510401c1c03901a0411341808090001c00c1d2a10010310b4240d44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 929962365 1250 929961115 929961121
    0xd0209030d05041706100510021e031306030603050d05030c120a0b1008012d0b03012403150b0a0302071a0106020c030304080a110a090e010e070b070b0105060304020315 74
    0x1400c40b014104450401070320a5028540901290322008100c80252110300c5901041c4458608075034802100c120520458004410320000000100280010881c01d90f001051110b59082000d0b040070107080c0502d401d100b814a1a91820780d500400c0200c80c00b44540400020400e90308035082d81c41c0c0c0e205a1036103404504001540000620003102c0c045e01031817240119542050044000354101c0302c0020f000702003007545280114901201c0543c41c00920812480016a890031402440c00390803040305401a06108440b00900082e0b0414010189030411810f0050110380c01260f10031501a07890031a6200403c180c200c0003481100380042505a014042d48031845103102d816040c0c030300d135408032410740c9228000c040d50b030b000c0c0b4450b0784d50b643d0010b20488005004540c1036045100064007400b10f80e0744038400c00c800d076200140c610f50385a545016550100e8820040e1038010881000c2d0145040e1f43c07602c41c0000e070300c014002d90380200800400708086441c200603101c0390260814031540141 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 929963615 1250 929962365 929962367
    0x162105030703030906181a07033c0e1e07090f0e0105010b1e0702040912031a0a0807050402130302120f071a07030f0e042409060303080106050d0209030d 67
    0x4280b0f011354806103020603400716402e0395081b14002c00e030448140901d224000c090350140b400e0042180c2e040544800d0004010345100c0e262082100d40c0c02c801c2080101d040301e10448141030314400181c09070031f06104c0c080490002c03d00103400701c031840c003d80c06050300929880c50304100c1e502c0070340700741e24203c2c1381c41d2440c20070360058410310091002404203981c0c81680c00071a000ea0690700b086100b4801505914041d16001440042d01c051f20201d4480034640fa040604c501c0a41e50b40302094440300c0c1c0c6101c410500c0c030341100818003290410781c050306202909070744143e24000c1c030340160340c002040100601e80071030000c01513074010800c000b041d0200001a85510b18141900d03002d2084030400724544a0803c00c2000e02d03d035002c1c20300c3c1048200e031811200e9030b50740885041401450000034034130381c03034034011100d079050300d10056040110034500e03c0c0248155a4850720206140010610010b58800c500d141101c12525285807100a0346228a0080c41a00f210075810301c40c1c48a000e01ca9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 929964865 1250 929963615 929963621
    0xb042d05090603011e0b210c09040615031203140114040f0e0f03041508071704140105040b061e0603150303190333300b090d0216210503070303 63
    0x81900f9541f54000f1141d40f54141c400b018000c0710008113130414500d0401500303208040651242c011031010950706007030402546220314580082e103084985285800300c6a4141c0150100410014001d8140d5850661020f40303104031140d546218a4071024440e010382c0580c1c02221000a07024103488503406848404c1e981c0758458030030007aa00520009042107507006602e4188182500d4a9000b101103007078059842c00800208102c0311074150864a0028070030900c55948160b10541080711641402400c010b6811804c03a03c0a0304c0c05217041e6035607456161181034030342085007102d03908030402c0c0000000c0d0950040c219010706650b031201d02e0744410781e0316401804040b07070307101e0200000c3c2c81c40c0582c0301c00c1202c089000349080501540100b02c08034840000d1005028408280c03c5425456201581c2c24050314200b5104201250b0500601541c2070084155032200c5d4002440840146442d0644580c454481e40d0501d00c111150204441c40c0c030a07402019580c880103595888101c0d28000d002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 929966115 1250 929964865 929964881
    0x4031a010e1605070303090c0902030f15060c1c0e03060a0f0b010e100e010318140d1e03050c13061101050c0c0307061a0306010b042d05090603011e 65
    0x3031086030402044002003a01e10382801c2c1081c0c0e548452500090381c0301a405000a5082213034a8840b50000154018040c8040d600524040e807040c809801c280103001604003103010f2951242c101007001e2140c104000602e2104094106181c1c04189001130301500c0c503000b40310540360180614020004210b446038440c0540f001c410000b0415140d0201c011101040c041031041d0b0840e4000b00c1031710300d2a011300d000e40c0c9014814034001c16094000220041c2d250b089000c111440e1001c3e036000e2048010610801104280c14a009001484464103040000901d2100202815521b80100b4041441d003c125903041c042c0035021414030b0382d1110000c00e810540701540b240f6504c2c10010544039a9880116032005501c08021410b000891320340000504050320511020b180c0c081c0007102c2c948041c88451300901c0714640954485280501e06034520041808082014001c00101001e01d400096140103030b45040d500702c401caa030740c42c0102e0b00414001c003085d02c110026881ca56500c8103170b5008040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 929967365 1250 929966115 929966129
    0x30e0d2f0a0f030207060f14030a0b12030d11120402190503030304031106070c080f0d09050717121309110702130c120908040905071404030302060402011b1101050a0504031a01 77
    0x7585e265580c82c200c41c21551010f21030300140600c0303032285601080001031500080000c000080e40044500050101100c0c8510400c10307800126240300440c486224180007659041c032500e10705110000700d9104154000d10080c8100c904c18441204c00528a0094010380b5014085980c0c074202424090080d00030107034440c050b07104040002d102180314048120929a100b61424184803204441c0300503134104928042401c0c1d602c03512280842e5040003010000d01202001c0c4140d030042810300c90400940c1d0282e148024002c01a00804881125a000840d4816400025a0010954204a14483c006001c0e500c6032040e07486401807811070784a14078048050301c03143c6c000400c40303941d103080e03401156020380440c00612003048400c0c802d4010b50307403064036894035161f441c1c00e99450800a40240d0025401640100e0801086580200c1a41010400700c50741c030b814a2802d58508081103401507050341084408200300200501500545018560000c455103400c0c40241103a80f000400344075000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 929968615 1250 929967365 929967373
    0x9030e09060d0312020a03111b0705031b010509060720030c030c06031803070c030b100b04081b0f040c020309030c1c260c0a03030e0d2f0a0f0302 64
    0x307000c51500d20030712034030203a068540e41030745030400c4441c00082d045114840c05064442d650f510300201c3c1100100110000c0584542e81c004410410320f1038100103812407806a480a80710407101c85081c1642c102809007464242c2d134039101d1001244181c01101002000e00302030011012412480c6211480488002d0f41103604e240103c2040690312100c00426640000042002c00c0710100c214107914424001d05c4126840c04ea41552441904000c1e82d209039400311000b030a00038404150ba2802c0014118000e0030340c200b90031304c001291503100e44944000700050300b401d8810661118100c020305102c00410800004586000294681d071060151620070302070007182100701d1078025001d0014100c911919159455140c1e40d40c409501404030300d0144045038521010301b801e0740703c01402d24801100162941c00a2031078054150303030120301d02d4416900301440c80c1c604590f002480c1c509180700d0300a49466000c01920842072880d480071030080600071b0140003814048e05140d6008000d00c070760300719 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 929969865 1250 929968615 929968621
    0xf1b210702190f02040e0a080d060602030a0909020a0e03010f06140d08090904063206030f060a09060914030417010204050105030106050a0e09040b090706050315010302130909030e09 80
    0x12030311002211091002104400000004030301400c01c100c2d01e043c405000000c4d054000030100341f4040c0712240481e5019030015041c5001d1000c0c0c002c040c01044940011420140070550142802e0a18011004515030100781d80c0d030142d21502c80e40840b0030000e8000c11027881041c90400242c202e5000f810700941d042c1c07102c001d940c1062601c15500a4200e007140e424180e090040100c410005081500e080e80c507007078000b000c19802007000c02070b0f20304214400600d20500d0801360380f9100c01402148250000304415400c94804211164080344030000010800d10b1458a10b000700740020300274150303100644120120440000c0244183c819404070f8075120003400e0851403d074400d9000d210300141051004201c11801507010300036074410340c200000300305c1840c004a841507904441c181d40c0b4001c0704c002d100360f5100c2404060302818103864964a5894060513400d1103034040c980450406a00142040a0410380c1c41900c010f4400f95409105858880c00c0090030004a240401d100302c0c802004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 929971115 1250 929969865 929969867
    0x31906020c281212050901050105012a02090907380f0a03050c0f03070201141012020607140601140102070906180b040b0a0801020d06050f010203030f1b2107 69
    0x1e101445102642c5101e11041655440f48140e00c28101c00140b00c3c45410088480307841c1e003d04c0b4412411000006620340c9010001404080301c80b5117040f0084034901a20802a08029003100f50f5030152100295511003103422803501a05070711040c4a039080c2d100c03601081c0c4d0b00d000300b010004c0c0f41544100b0803049650035080e5510883d9845200140100f000900460081d001150311190260506080c00c0080021225940c401c0f40e03500f006035540c40c1e02d01000344d044000c4603000b03c0980d03411440c190800008901c420440040030b8810fa0700450b501042180d80d00b05030403100600d0080e6003031942c0d41c03d0103000000284560794054080e001010401e00c040380700320811104800d007200f2481c28180b135914024021302d84420340050b1500e40c002040c1e200d280b1110001c1c401c00000582c0e030440c5016940484215410140c0b2409201070704405d41c0c0c0e80001500d4000403401e00c0961991649a68000380040801e80440041c01c00310b401e04950324164102c03042c07001440008442d90750307040c1c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 929972365 1250 929971115 929971153
    0xc090906070f030b010509060d020a0906110a081e130311060307080117010b030102031626010513090f210908060705071401140105150f0d050402031906020c 69
    0x1030680c0028801089422103502c00c4e04510030501041c100707249080020300103d01c0680c022000d00c651030f40c0001b00c82d62119844041c5000a007201c2c504070b040042140c10361031321480c2c1400045c019050204030721016401c0007172005846880283c0c0707242e607000d08204910030500142700503503500c80050102c10aa0500c00c0442c2d00c07031401540c51040d03d0b0300b014050010600208054080c944d80c8010242e06038800b44011405481c051000c0c031540d03850404014210301018260503003d0750307600b01c1d010075050003a041c1819204100c441c00710000300c4081c2c0320b00400094034050300718103021031680306200e1b410075a440601e014441900d00d1410310b0070309486c603403264841c403660b940c03066001980309445034010340a0749200d0100e80c42401da44820301803d44450b0300000010131075403001001503290a02c8074180d601120800b0b58201078000c8080a07590040c80340c41d800680d01e400c009001c5603820b0046600700d011441012020001070308201000350001140c4000c2c0b4810300300e592541c144420 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 929973615 1250 929972365 929972371
    0x210030e0c01080c190809190b06101107030b0414060f0412050d0204090e010b03120702091308030a0e07090b03071703040b0301140405060f1e06090d050c090906 71
    0x70311610510400440e29200000c2110060310300c2480b048203503030200554960044065901d982c0725050940e0401c0c141520703607011648805c05c54012030b0025042613500356200c9421a00d2501c2004d200e91f0a403100802500f54842c58082c40202004104200840303c2c0110b00820180c503059000314030143c0c1e5004150b03040000c0204001c0000d0008e01800b0002c0c030320417400c0c40c0560808140071410b0090382c0050701f084181d10784071580103044001c00d00c01e1329100d981c00c0700107200b020382d40210742d599440b400300040d0041c45060000b42c400311110720141d051507400385c51a5aa407404110301ca0003000b01140303403000c03805050340c0018841c000380500580441c000380541142c1d403600ca03191049c82100320080b00d0030f000c2400001400c0d29204d020354002c2003a8000b9050a00d40042080122400202902d2082010301200c15440d102d00340342020031b100c070038511110107001c5400954180501c800d490340c4040b03081c070038070208400490240c178150429607141c03002c4c0e100c120205888410131 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 929974865 1250 929973615 929973641
    0x915050408030f0615070f151125121701080714011107050907082a0304080703020c0301020307120f0504050c0607030c020d0b192007082203021003 65
    0x24804283c030700c2080450a50803c0000308084408280c0d288074000c0c68020440a0340c4a2120280c40740c00c1c025191880100d8201004080040941c2100340380c02c076003d141c14026100200399008000c20020001c68002c3d00c0e00010260343d501c51080c0020407201d40c00010218200d1322800009040200040034000e481140801016124100c001101e07140583e40300020b140c407504000080b0303500c94201040c020342680e5115810361414444190a100c40402040000082c000440400c46103010a0b20741041d40702c485035a031003500d030800300c1c609003d02e4161031340342d44000144408240c004071a4000071001500c14000410340441000460340119030151072170300001071910740c1c1c4c505030300146a61442410305080602c899008108004419002200c1080700c0c001800392070b0580440341030441100110504c40368170401d03d480c1c038600c0c90303401006c0651000704080081001e028150b84110207106055201c1c02403002901d1041003c0748020ba0140054548000c090703031090040403101065 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 929976115 1250 929974865 929974867
    0x15080f070627030f0303060302090f040f0f031e03051803090607080912010e03030f180a0b07050d1542050c010f0e07050d030903140c12010915050408 66
    0xd5100030080b1041800c007440484245014003100181042d4440c102c214000e503000103da0b401c51040c064100c00c040c0403d000c3e16001000c220000322000c0d079a41010b544104449041181483c06969002c803120340303821038079440d1501c4518164181c0c0b001e03210703080c0c0311200281c1d024540e458036102c1c13240000c55508407004212850104054600820342c0b05005021104440d0700d044d030541c2100c444a0601c1240c1d0400018480b07000d844d03802980e004030401080e015031500703810582d07076940f20004c00180350021840010711407600417016904000e2500000303100090028514002c1d1700400d010710400147c4000a000d1000010030852071201100c0507061200da04000703900c02c05009201d00c400c2085420021102c0d602c000303005040803010401808942c1e4044101001d050100c1c5410060141c40c0b07a29050340421390114002007100e4111150003061240708541504017054030a00c0390304651201c05103078810320f0550120b44480d0180403c443c000821500d080d00342e40007a0b4000e0701110b4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 929977365 1250 929976115 929976137
    0xb090f1b0c06131a040605100b040612052203110d0509031e0a06140f06011d04090606150801060206010b04030206090906040618020c15040f030f050c0115080f0706 72
    0x5031905141d034402e02911030600d50140c0444001c0c0c04c00700c100e40c22281c0a40f142c0c107204181042d00a91005080b4240c551400c15040400040c0714a04a010a2540c9501c0ea808a5403000515180b040c0c0402c003007004044c2c881c00c50901801306846007580d9070040c42107a440c1b070300c55803240c005d48511500040181a84104d01402c110980303810f00d100f020180200d0085100003000c910071007520141003005c1d4100340c50807005588002c0801072556043c0248200e000700781034600070440100400841d00014804000d04200c002809981c01208103802038031043d40e40c02e50010000c1c1d04882060703007200c0d0180c1c0c9656003080709000d203100003500203200303202062403850409803581e440720b0044d10000b4004c1d0b4656070403d07440301060281d4801d640c0040c810302c0f901010b00840e00088103411501c000c40c18075a4402e611003079007803405020088420030180340e051141044903101ea041030300034000c5d1086064600e40400280c403500341180300d490110796121801084c0c480444545031103a24040c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 929978615 1250 929977365 929977381
    0x19020c0402160f03120501090902010f0f0203030105120114010801090c290f0d050106030618050402090a0b15030708160c120e06040f090203061c051c030b090f1b0c06 73
    0x407003c079400720203010b40800241495103452282900038504000040303000d1040e80000b40c104034124401d5030400185900c1c590308141c0000c111384c11113500f42d801482660956100c24010300350001101201d001c19030000410b000c05400001203203005918411826680d400c655081800840d51b038410030321506ca5a00340c50010001611041d17004035a01407800052044407011240c00740c106130b000c80d668400134044444840c103c8007500c600c81c0410001380c2420303000284044001098803520300d0f25003e502240703031a00644400307094a4003603481d44a082185020700220b40444640070510554a918803819100300004140c1c10740050200f200600110021200200c030407050740e4001e403040000245c100a42c1e000300b0000c1003000c600584904060041140e001a0405801c0480d0701c11050480410800b041000703111003580350b81402008242000d402034040c0941850f40081c3d44020003520307801c0d480f00b0300e11030320308844000c3e84004501e404c008103001c0c0d40030400c0da55011b140000c00c18 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 929979865 1250 929978615 929978633
    0xc060c0d2d120204050d0f0606080d0503150607050727020f07030305070e031617010225051f05040501050f070e0d02060c0d18090b060702190b19020c040216 69
    0x50340101c0790244c40c0980316008540c0d52007110008841c0121450755880c1070040d9441408044c010100c060300b00745405080040003400040c0c030503a07024001c00ea80c082c0d80d9850310101d51120f90b208098030500c507541c03c0c1445d51803411b11103440750102c20709500300c1c22072400e1089401d18185d002805003802540d440480090400422031414011289035403d4195420040728545410800c1840c40050030300c03248a69010102855501680c0144207101046545102d215060a10340411b00e02d404100e04110713140c00d011a1409812000c803030301d55140c3d40e6164001900c00e40c003e400900c03a50303e511200020750070088464000064001e80c01414601d850070744404954001072142c0d04246404803030b10b040010011000340415948480b0680e1880e80c448180c00130507000d20208004894000030510b5845040d01c0248110b560785000804182160b86040c050490791030500e40720b090030107800d41e00344210550040544a5a4941c3e801441d050088484d85080c2a440700400c01e83d5136a41d580c0c0f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 929981115 1250 929979865 929979887
    0x110d1b0c140a171b0714060a09050619021606201e0309031207030203251515050a210812070c0312020a0906110c060c0d2d 54
    0x40c080e502050001c10b041d20740c00e500d902d00c110000c030b81c0c0b40b111404004c002c10340e91210000300d4114400130400b07403e0f0b2803000c1400755410346110b41d40e0a4400401c03150640107400c6981e00c0000030a00325a0980003031105000400e06400300d80045526240c01c2940303681600c1400002200c3d0800300380740601001100140100c0344003111265400b0609000c0080107a10031031701300c1d60010490400c01c1c0fa08010702d50700410151142458081136450003900e81c07103041050403940d948604d888108901780909014455009505285588c00ca42c50701c4024212403175030501140c0c000c00011071545800040e58003120030007001a41c200024000641a014003070705c059850030001c0c0030b03101504002240b0a4840e0f550b9613241101c2ca0b01c1440c01500c9103540030b05414902e80b0500c040c114681e08106c162043c2c91190030907024100c0d0101c0340300d25140e210b50303806400207004281032051040c0020403c10704815a1504851004204540040c64003d003202c0c10003803940a0001c45914066650004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 929982365 1250 929981115 929981153
    0xd02012003070b09012a05030411030f0703051b0112091119030b0c21061c060e0c030a080d0c1403070806130501060c030e0301020d110d1b0c 62
    0x340308040040aa41140c00514080d0f40b409540020848105000c0c03041a110985aa5042d0680301071401c842d011426214038031400d02c0800000325042c070661520b682c41040008003100c44809200581d9500d07034696200c1118684190b05d03028042c0d40d4101560644c00c84117a540f8a03c8050b4040140c01a0a40d808141c4641d110304640c0901902d4101d0032660150301601e00d0540030f891442c0c032810201c2d000701883c815034018803601c01000398440c170702401c15a100100c0260b42d01c2d507200180405440c0c0d802501d00c0340c4158150000c0003035039001400c08007145001d8031000103004041c1626400000c0c4014050341c02040440c00c4a4901da000c01c80c0c450486c0341651482000d00d032050400c2c0c0c01510701e1001f04100c10100605031428034290b03001021080f5080c04107514044010300000851308009046c0f103400180000540c038250306913100360346d28240910a03621034603240c000b01c2d80400040060f90b4102050700c04c141c001580e90b10307011861681c0e0001b07408559162000c001d003403030403020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 929983615 1250 929982365 929982407
    0x2010c08040b03130c0b16020433030308100608010b0c03041508060f010e060306240301030b0106090806040519020f030607051b1507080606070f0804030201030f0b0d0201 75
    0x4151820b07881c0c0590301c5043c590641c00100055401d002a00e500e56520400d0107060811a808240003e6101210f150740d040e0790109008105a003800149156401e240c0d243e00400034074084000f1308042c0000031640a911100701075220403940e004075041700d024142c080390b6000010003600d507040c0000c0210908040581e4107058841400954440d0b10301c01c5100040c5544007440001c1c94003000b001881032003401e2030903280d41800f001c6604c0780001458184555546500211580c0b40e408207542c0750242104000c0d42d035a143c0c0b8103c01808400e014190020319003c00224444100142c014081c0e43c100000741b41925039088071000000c40c0c4101281c20030300410001d18543c40c03c200300340c041c40050700c52580f1500d03880c02c020a202e0b404090400240d00242c1c2c642822404d50045d190840b225150000c0903545401c0070881a02c40d4500080407050980099001c3c480348401500c01c1d82d200340d03420f01c04580c680f510042516010f065456000e1000c1c00200015030088415640404a54042c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 929984865 1250 929983615 929983619
    0x160e030c191a040e07030905070509130b010b0a090611030403120915020c10020106180504080f0f03060906010e1818010f02030a0e01020313200901090207060b0906030a02010c0804 79
    0x2c45200342c0b002c880c12a0503880407400340403404c0c6010390360754401d0951908101840d401e46401e656028184a075600400a82c0086804c2c80c101c483d0720b400c040d80107075105180c0d5a4031094800545d200306a0000004c130125008203101e4455500308a10840c80001182444e09544510300c010300103000740c400744402040c0c0003076108041d504050a60071280c01800e200741c43c000500c109841081082d60442e458050305002501c3c5e00801c140c1003400f00400042c8958442c0741c800b180f4441c00220310510300012a402444421480c02144100b41c151103071081d6032198001034420891450f00258000d400f0007000e202c102655a841e80d120460600e0201d01a10108034942124050380d0103410031078002040207503007030040c01002e0744098860021803940c6400c0c0d40c1441c4040362514001c01c100704401c10205417000c0d01d2181071401c1401400f59580b0350395003040300005d51104d107040b542e003800c04500d10310b14a0152515071044801401030a4440115801100c050103221000c0380d14038414040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 929986115 1250 929984865 929984879
    0xf140c040f0f060e191109040e06010614070b01060c051515190b091c020603010e01050f0406030203070501030b1206040f031d03030f0903010f05040b160e030c19 71
    0x555040c2880001d000645080d0524060701034901c0c5401883d45162038009101c4410706260703c81c0055001507200080843d0843d4008440d481054141a4882c0c1450081c9041260200d14981210612745890704003410280f5465150300490b4006044900440f004110480c003490000005612441c00d031503d441f03c000d54140c46440c2501e811000f2814803001442d107080101500010b44810a0100469460f00d20710031214030514151900807001d2101c1c01c00f882010341000310106500a000c245c0b00d6848100320014081d003440f0341d9201d0708060b1003c4103d42040c0c0b08100a40b80c000d00039108075420800154042e020f220b40c0660000040303110808920710900034540182e12a040e60004a41d81c1d04004000380001c5405111035010180c000030559000011a440d0002031080b90b0384030368100700080c0c0100304000b520540f85007001e0070482003114820700034ec0b00c0c68850000c004440d040c848210307260021600000c2e0035501802e5500c00f50b1030940f0140d0141e03094116020021621425 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 929987365 1250 929986115 929986121
    0x30f09010e090a020406230415210f0b2409011106090f0c0306010f061412180d0f0e120a0222060603180b040303061721070f140c04 58
    0x4007064034944c080b50501030903610601303a040300520207507034072000900c00800300110b05c03c6210380400802e100c40400c2030680a40c580c008401070140340702c040c60060309c0700d2901500c03400c400801d18500c0c058404242c2e01d000b010340122100c41c000015401da00600303131000e03594000c960b0103060121a40744280115000c20400b8844c201c860702404c40980fa00304040d113090b401843c5240f003500014010301c030110462140f541121003902e041032000b00c10f000d40081610070515580141c0c06803500300002441816249a40f40450304103c80d1000500d03002101e03180002411075000420080001304a894040c10004045128005596080351180d0005000d00760721358101c1c0420510704c2e545900c650181c85400d00421250034140b02c080880b910920090000140003403800d0724035000f140c1818420791100010f4012840c540141c84c551418003a51020324445005440f50242c11036082c0a5880064800d5658064401458002280c1e2a0080d04001d03202510552194011403c17981e620341c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 929988615 1250 929987365 929987371
    0x150315090e0c0310051b0304080f0403230303010f0b070213090b0a050a05040c120f02300d0509060a02101805010c0f020c011b080d02030f090a05030f09010e09 70
    0x40010320030b4884800502d8104400181d8078801203240c04204411141c41c4031800c1d40c4d00f030960f05c00d1070780c035500c1e0700d061b01c130900610000d80d0f1325800c0030401000b0000c11b1948021804280c6580b020600c600600141d49c03880f09004a1500040603841000000342f070001070301c01644020a006101944064540100d408501c0d0a90300f403c039500a1050b0340f10300c0d00c12543c2110021900f400580ba013a2540c03d4204003d00c45c0715074030503c45602005000c44c002c258000c1540c010f00b000b4960b00e10b00c454408807100c21309010340d402c05403198803102410018070910b4200030303515407504287c0c410b030401c00d03181c000c2c4003090b0039405044d0560f0f17440506031081e1601180300c680d81a00359110790905900b12000104000300784011205400000c540001c0e000405c40402d20304040701d094070001304c20040080103001030588502007055002850960059881900304c103031903c48560382c0202140c0d549000c40000740440e0010850100244001c40003080c0540060500c0461920500c0102e0b00c0c8103011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 929989865 1250 929988615 929988641
    0xf1403070203092701030f031107030506060312090f090910021201060e0d0506010b031801060306050f0f07050a14090909010f06090606170a09050303040506070f0915031509 76
    0xd07a840207803600b0559445690740c1c29022104c421800c0004088040341030002074516079400300008100742c4188031040301e0101441c2903e480507503e1810598400040d944c4502c68001e040301c180160f0f007000181c0d2403102c001803400303050244003000d10003801c602524442130350040c0e05c03d000c4081603c1c0003d1403481e88030007002d0346561500000600313201510489503c43d855101502010a00004405064507211940c066490700c2d10940300300c0c01d10480c40c0040f22542407900c00003e00c403d5602852141101010101d060b58560031a0300c400d9004840360408100305221078450144590505414005407125151428400000162425008540b00d0b001d50f9154407034100401e40d0f40c02031400038080d1220a00030a0308003100507042c16100c600f4036542461203000181014055040480700d190040240c0e07603a81130505045842b214100c94020118081d1a003080401d44690459812106204c0c8812007845102d04102c0142030903640d0b4080f0161564400320380c07070106101d001d40f00506 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 929991115 1250 929989865 929989867
    0x30816020108151c064107120b0303090a27020702061b0c0d081b0f030711030c09012c0606030c1602120d030506041b0f05041a04030203010e0615010f1403070203 71
    0x210192144d035011303407124044001c0840c4024020842d80004802c0c07800e82c008e10f000b048803500900420f140d40215a105a03100d0441000000c4000045150116000c20b030b070782074001b4840f100ea1050580c0302e9014001e4000c4000c02c122102c4003254071002c080d03118107000790b4200c4010680028411382100000340c41ea803500040c0307403003214400440241c0b0709030b03008090540402e000ea182a100d02815402400111070200c1412040d9004c0c403d180a40304010140c40140d41c507440034200c035412000d010342396111040456105601c405110764424003004040e50b00e5a47c4003d402ca45940281262036400031001c10740c000180c0d070780e1048243ca441d5140090032488509000102070b1007000c2c107034038095450075140800c007414040c1d004151060070b048c4008900c0a4610807147ca02c0340d07a101c5d13504030100302861440d400104005004480c000c5000344400d114074070b01646c50716029101c0c070501c15620807441000354020b20f10800068a130741400400c1c030080d001450b8059108480c1c440060700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 929992365 1250 929991115 929991191
    0x90c05010206180715050d02030109150b0301030b010b0f1b0c1c080702010f020f07081608011802040f0b0d0c090c0c150213030816020108151c06 64
    0x107410814180e0040500300e51001d5070710340a02054640c400d13802105104942c14411410b0903028801711415035902140443d900d41c0d4901c0c09500410320f400320301860804140000400c3c0401c181585d040c0e030340159003070059920f02160003240e54801c080301c0c500d041302071180d80c1c500742159034540f08010661000d07044841c8268100514210220348200884202c0e80906000c2200f54055500c440e13420308082e05402a1480141c0ca40f0b0040c0c003408500307200d0035074040b420f0203010500300c9054075142c50705c1c145182c80b50340481c00e139540c091003681d900000e400c02c2e002524041e04040d01e8001c0401d000a0f2200d4060040740381c08402e10340c10b50320342c10104400c0010f42460301c0343c00000003c03840d000e000c4500d0782c1d541403403001c098400f210f0103d4001c2044100d105141c884503000b5130740070002d903650380f4036180d418121504025081c0c3c0411104800612801e1075045501070440c40141003003141c1c4803a801e02d101c011074000041c4d9186035590302c441c038007650807101949000f0305082202a003c1e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 929993615 1250 929992365 929992367
    0x30b10030504150204030c090209010e030604050a12050421030e030a030809070b0307050a0c1e15061e121a190b010e0d29180705030d08010302130f090c0501 69
    0xc00200c0c9891592040000304042447d8280560640344001800b59446481700c004030ba841012840043d80341c0940009d01c070401000041c02c0351a10b00c100c00e070050440b000c01c41500c01c1c0c081d900c039208000c0060301209900c0d104070508071401c2c41c0319082640c52440d000380032074500546410700700c02290031030043c0308464034204000360007407400400481c0f451505940042440c0070300f10540c000d11030800304510400c0040c0c1c1c00f5208080b007510300c09826103401d04110145044d09503044103458507000b008034001040d007088c404511000c4c4540f041036484d100702140101c034010710545010b4611a54030b0707000e0012110450003800c41004510310524844e40f12811900000d50303050501150704200c510320307120000c0c060482c5800102d954000c0750565007a1513944a51591801d400d103080003048000c5c80901100406401201c013101d0b5180e481c3c0c020315035980d80807010100814900c1d00104011715002e002a0107800b414880883c0008801c0c5042007a0341625000300d0300b02c101c0300402d014035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 929994865 1250 929993615 929993633
    0x135030a0c20060a051602220c020a0809011409130c14070b0f0a0207020d0305030114150d0203191b031a09150303090a08070503240f0601030b10030504 67
    0x90840088007490103202c2100041d0359100302e01d1840280079006c901e02e8405190b54800040b40d0317030007a02c9000012a000340c00d01340b0044589a0300c0d08146001240c0a605100107001130110362300100030341c9011056001900c00f2100700011884030136080043d1213964640320792828200101c00004a40b40d400860040c08600c03414000c03101003003081c080c00300480d80c18202e0035044901d1740a08c40b00d42e1034825458000c0e10501c840650003581c0300350240c00301036004000b5412522006112154200040108441c01242c00888004000c0031b02c440040d6a0240e4000c540181c0d160312180d41c89d95500050314140e400c60000e440c0c2c49051621001c40082c0c0500a20718007280214110400d01d00c408001004c00102502c01029180c2e008a9a07100340c404000321012140c008103c102c07006c0c0d0f00c08240c3d66903105401140d00030702414404000b051024040f0920140b0003011a2829139144040000b075003000411060415850740a0210251502003001a00d180d4641d8081841c0c034080c14480e01d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 929996115 1250 929994865 929994893
    0x60405041406241e0f070b04140a02090a0c0e0a0b071101050304030f030f1e050a06080a05330c03150102030a21020d110a0210050135030a0c 62
    0xa4488211140e1100c2c0003a030459107034031502c42014801300c1d0460501c940b42d00485901e419420f000003058010701903141a02c5100d60301c641500c155035030500c0e013403586034540540002e40041c81c1101084890b421a000203e501d006d5241502600c0c119100185040c0e50b0b075880642c190200054200c1405910344000c400c8240a09101d46035080c950b400911104840f000c940405640346050b1010350002d03040700c55172922088940d204101c50308142d1008240c2591400109494000000784865020a44044040e00000236004002064490340b841506124001881e510584079407414030010002d490b010703201c038410f615101c0c944802c1211380045280001d505541c820311543c000181d020b000c01008144625030b8424524943d94400007a01611809a16441c142071700003614110744d4001c0c100080340f80d0b00f00e41c0c0721890032019800f01c5400380500034000c1c4416440f1201c00e800ba1041a142c07031310603207281c4070001802c0c40660858102010100015881000703c1d028054200400f200d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 929997365 1250 929996115 929996149
    0x140d022e030b010c12030e0d031a150f18040c051b0726100f1e0b0603010b090d0c03051605011d0f0604081b120d02100209060405041406 60
    0x4a18034900040c0c55110464401814510341e0b10b00000303000d00c203405ca0242e03a40600c02303c983c40316107040040c0c007520240614040b4078071040e4160009103405841c1215000c10381e4a007901d0850100c0d0010002e92003074480d246440940080c0d05001d4585101c3c0243c014465a5001d84462101e0a0f044003204411071004459025080c14028580d20101c54401e210704a01180d104108018400f4148985001c078007907640c3c40c101c01c0c28500c0c1d138103070440f80704107034002c8070f07030421140901008007101c000640f280d400c20403d00c01400185400070041001101c010308964040d01640d40b205920191030300111a0b40c0c100c40c1c02e00c1910840280050003400382400d1110059054000c0c02c404402c201c941603109032071410103545c0c40d840d40d40407200509110001c3d100a1a850514000e02c10284a449070140c00610840000c0413408500c0c2c4e6094075142d405410380d041c00143c054060f4100e8205039500c01c83c100400505a611071280303554500038000c1c01c100c1403a041041240450340350790025 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 929998615 1250 929997365 929997371
    0x50a030306170102120f1302090f041703010605070b0a09140d03050705070503071214040e070f0c0213050a02300c04081e100204180609060609140d022e03 68
    0x9aa460781040c0c119511254040e514425035469101e8207c85000d0300002a40008241c001c3c40548040840703200c3c4180d0160181680c2d642c1c148000c080c2600c03007403095a0014400b4010000020b49090015410285041c0e0200c3d00e4650b03074403546a60840e15101304040d920111911583c40c1d05800f6140d0b00140b1401d1540c2006a10703202c8649034414001c00811031600081801140340c0208060b0445100050340d0984540c0c840b231604e11100025201c91005c6140000f40031880d901c10701c1000b038846d80c05440c02c0542d034000d10748803001e010b011f083d60715502d400313110758204040b61005901d900c240c00c440c02c05841d8182c4c1003115107180e016240642c40d0030200814000ca4000044041c00041e40a007503600455262220a081118a102220809000280001c0c0703495400d018580c286010b00820040650384840b02c0d82150040c0c4502004642c10000c1000907150403e6100802c540140ca400955003807039002840305130300700744400180c0c0c45070108842d00000d0701304040d07864400c03410300f0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 929999865 1250 929998615 929998627
    0x31c020406140c03190504090e12120612011b080109061409090a1b0e10030b01050112060f291e160b0403081b03240d050a030306170102 60
    0x10200c2c4032800c0101c0550000040030209910100f00f02d074102218550015846442002e000300a0345c418810300115900b85001b04800c0c281c04180400141440034800340740800a00e03101c00f000c0b070002c09607a8400e0711038401080c149428024690440d064a002100c0c40c95a11800703000c4500681018190720301d0410180110038054200608240d4101c4850519580700f501d6946080d015600090140d10f0501050a00d920507041010030340716468000e42d041c0e590503551411b00622880043d04074500e041c010403103540034480c50071000c1005000441c0c2e4076101c80e0500402285c0380d000501d200e1680c00d11001020503299042012203c03040141c0c03500545608503030401802d1042107818600004100841080441c85107405039480041d207540d502e001c2c200541015411124103010180d40c00707103904102d640c4030480b403080000c40340c400547c23440085264103c5040ca080e00341c000c205105000e010072820085d065040c2c0c807940e804100c8071b0900d042d220b00003000307542c041c8127a80103201c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 930001115 1250 929999865 929999867
    0x40c0e1003061d1e060a03140c0a0e06010f080603070801020f0306030601060f050703050f0d1505011e08160c0c09051b030402091513060618061701090c1709031c020406 74
    0x18080101d03450303041000304c9031644400a00540710f582d100501c84a086140030110b428003081549407100c0844410603269614032504072801001c480490015406011364410039000f23280d425040750b800b40495107906e4542c8800e608981c40300c41d0300c1c201c0c8000030040200da0300d0204000e9014041514254010b111001c1c0e0141c014010410700409002020405c101d902c04203030147c032206174100c2c200f44030010940c0015040c00865001c0c060004d01800d820810035110011304030072400290b41c4401c582e80d12051600700d4002c190071280c2c00c0046500454001ca20030500c6200600121600090a800d100000b90407058031002c034074000d4103090040002696030812029030121116190f4403002d04814000b0722400c0d40c1a1035100c25505c1c009000c07850540c40b03a82004000c04092407204440d03101d25040c0d0748203008141040c00c02126000502044586070868001160fa608090307254046240700207006a004490303030300c5a42d0003c03842402c580310a21881003583c9501d9030440c601030034648 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 930002365 1250 930001115 930001141
    0xb01020a051c0318030806042009060f0702030105100e070305040b06040506010c080415080109020c0a03050705010608240a052509050301020a0305010510021902040c0e1003061d 78
    0x106045000b44640203901d966000e40c02951180101c501c08001c226010325000d08001c0c41903170300794015440c012148180d000d000c5840140c41002c4504c07076041c007034110100003442d80104c01040c04d03500d080c00402d0058034240a03c5000d10200c01c030b200f41c030354140003001c050723184000c08000030181403500344400324503241c2e0555080390003524082110303640c1c0001602c400c3c0c0a14401881d81c0e900040000e1028000c001d000c00903082540c07100101e0340d03290150010b9024442c840b80c83da4024042400010780503500030024644100000b107080e40d5904c5406003010782c0300c00030340b1038504040000700ba8020414143c076400004200f08003c141417250300d9050711118900e41c0c40c2102c2a030000729041c10b000700145401000c00030025542e41c048001c008024010030b21581d4019103103804401131050012500d01c9550714081029079040034541c0030000541311501141c4184004601402241c7e15680b60b07000120303600340c5000c40c4192030044046502000042500f0214070f41405100c40307414891 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 930003615 1250 930002365 930002383
    0x100c05160809030616020d0905150319050f010329060f0a030c090902120a0f02010302071e0303140a140105090915090d030501060302030c0921150a0b01020a05 70
    0x640a04040c1816180c4071015115509038964584106403c120700c1000100010122110950a48004545810b001e07206042c481c066680c2c011324007d0b40140e044460809113500031211814035a864036401e44403411101c068840f03040c454111401401030044100e01ca194007607408219044001d1200c0e90032100c0d0b00040c2c4003030f12031660700304040402c3d038a86031080c0246802c0683e0308411950303204004002c05441030228081c41103001d007281519004584496042d400c001c490004c04155401107000f940b01c284102ca10070403140c4e0100d50551000c030607400040c807035200002c020001c07489240144d07030f0041401124604000c2102c0c002c2c1c158405842c11610180c602c0c01d4140c461090340d508242c081c140c0307034100c41580b10402110781c000051071040c40300d00d45c42c100b0490340c0700c0c2c404905a102c101c0c0c00300f12840e010000b00c100e900341454080039001c10b08404c600d6074101801c0440c00c1064001200481000800c01e0043c1c1240034030407000c031040c00b40000d1009160a644482d00c03803900c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 930004865 1250 930003615 930003637
    0x41e03080a020d0315120b04020102102d0c0912030228140c03152505040603050708011212090e01120b0603150c16080406030504060510060e300304030203100c05 71
    0x840c0212301164000c0203412080581a002400b02c4050702408040400b2240680300d4010f500c45031207048a07010b8030806d05100c8280d600c00010781c0c2014200d003012a07008000310304601c1142030042c21482c1c403c00000b81c1c1c640445107002d08410072b00b03008550200145803002c10b42c001e40c84031001d96400003079040e00f9600f41d21200000e907032884448a02d401c54020340b44003100e4500e5010040076441f80007803040d10582d440400903500c56090482e845c100c01d0196800c00310f030b01054240400c2d0101341459600f411440c0015043c0d813074482990111103307a000d40c445509940b0340404110100300d103650300c040180e00500d541508208100c801000c080d00c0c4018040d80090055030301c3c125441c03000304044d0440001c0780d4495942e98002d00402c0100d50544102d45400302051200e41d000c450501140c46039903400b030103803003964200080049408064214000d1349010f00c803810039116844044100418007458440745180145404d00203001c05610890b8a4000400d102c160400c0036103256082c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 930006115 1250 930004865 930004883
    0x30141130603020a08030903060f040308280c08070908120406110f030c0c09060102010504050a03140d0501030f0b090303010b0304060c03110c010501090b060a05041e03080a020d031512 81
    0x50300d40020014241e640010790401116080807400d68030000007030504070300680071100740340c0c2c4158224600749426500100095200400b0a007030140c1840c03445074400c0c01070b610079040c4104075040022212408170b0701e0080340700c0301c003004141d94000205500510f003e8024201940070210b41c82c0c07042c03182d030288405116400900807401c4008004900000e9410021240d446e400700c0e80e41591100c1c2c1124151107948034400141c11544180901409075602c000103207040c816581d01607982400441c49901040c0003400f083c95007245030f00444d8000d500522a0140044690609124a150081025003542d01c20001048403090303400c1260391041d00f002c80010150014542100030b841100c0c0b117925800c2000c1002c40612006600081c1242e81c1c112007009002102400d0000c01c0c007030101d090000c10818882004004414040c44984014058100307001d0384e1650344461154028900200060b4010911003d40f0782d050b124184145410440341500c00789000d1410103150080300d401880825 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 930007365 1250 930006115 930006139
    0x6070c0326160602040305030403050312060a0602030313050f0d0819060e04060f320a0c0c030e150a05040e0105090415090609021201150e0402060a081b030141 70
    0xf9255054401850b84681a6a0755a50724108555640c0107184070307040004190021444500c1e0110040e400c8801c1a00030711300b0740e500d80c2e40e500003075034100030152064003540160300805082444501000b007003e44032050141000001170322000d400590030030344180f40c10018018254108403003584158000380201e9118000f80a41015140010b041840040c1d0032520000503000c40014a400b10803c87c40340e1070a035580304d0000d017642c062500d1740c400f2030610200708002c00c3c820403190354043c8001d800741e2682ca00380318100d5030b2030f4403c1c20310400040c4082010f1142106d49400c4030300502d4110390141c0304e81003540b100e003a0340f0141c00d8074103a040e03a104070100400c60701d1303000404102c1e0005e16500b646a402482d603406481654080354411041c00c00c00700d41101c1d80d0520501582d009411b82c1d041507000e041c00d03104000d000c0e10100450300d41d281e008180c49002d038019406448590fa070042c80e4143c04100c82090001507191040b031110801009a0200003070300713032b203e001ca8106c030608403400d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 930008615 1250 930007365 930007373
    0x10032009011814250903020a170309060d0b10030c0801090f330e1e041406071814100e06130e01082b03020307030b06070c032616 57
    0x1c01203641220320043d4070000c04c440710600348420310821800c2028402e400150b503800f21140040c5000003540200030602c1400b9440300c14001c00c1020320701c0c01c1141d1404540800207001604808404c801c0b0355141c1e106000d803030404c800c040740c61b64200e0400348400d141101029244007414042c2e0200070340e43c1c0710f0500010a0b0364003c2600765035221a54481030316110780030284502c1d414504401c3c0030403041d00060305001c907070303170284654400395141468120ba000c00b540c1c1c490000d441900c025034000c1503068651000d006090040707680c0d80799119510b103803407807c00700340055600c04c040c5940059107040c000c3e1250000d0141c200ba4515200500618060002d11140030380300b03019070381480c65000402d00609010280303050361420380c102d078121807000d10b114000c0e01c189480001c04000002081c0c480358040e03000382d9000403490401040d031610b1500070400c1c5401a00e003d071036260032200c080050010340b81c4c000b80c14081b0000c000b0074000380c00c0e40416031132181c2900c512844a40754481820302c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 930009865 1250 930008615 930008621
    0x521070204090b0a060f081c020c03100209040501091a190b07050109050f120a110309040e0a061d0c010818030c0d11010b0a03020f0d0209100320090118 67
    0x59640244208100d24040c20300840300c12003110303240c40c164030f09000030a000460f00c0419084604080c02010702c201aa0080c54070202c100b05240107501c030b000907031202540e09001043c1c12500008005880e4040c00301000280c5106078401c0000038a4460303500800e00c9c510b642185481800d54200103566020075035039200c41016406820074010100c3d1000400006402512055000b50119990004019481500c81c007400000c104c10081c03c21414081c6402000003164140080040d01d040c052a88041815035061000541c11500054941d2040003501d20600300d102c180c803030403c406503000080b016a07030300d04031400c6414400440300043c0042064000c01d0b8071007600340103880e1900d20211a0a64803004404d0150104101100d843c20581051062071042800101505000e924613001e002001400d05480340d04032202050900258450030b05550103170b40305c0e030404500170340385041c4590485200340300c09030301091003d5180340070340e04c8603178607410356188610941d16040071000b82e0303000b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 930011115 1250 930009865 930009877
    0x20a091a0916092c15031204180c05160c03061802010f05030c122e0f0605040e01170f070303020616180b03060414090610120521 57
    0x8025403074010000c15030607141d03004280c01d4060700c54010103a01d980016a035260b07107109052901d82100303140c4000036190890780340c203d904100101c1c100398080002c07a080400c12030048000540014040043c040d07065036204401002c15004c2200100e0114018028450420300301c001201001000f03040c4a0030540110085d54449002c020300346d81c00b002d00107c20313646101a404079244284c4030181500410880748a40740002c202c0e86407030b40e80030030755003000f0300580700403071000c2c104c0c0c07420f00c102e9208420380303203084440f032180308110789400700c40e4858098079008501000020f00080150b0350045083c2d034107444006026072121840009528a048091480480c0e28811100000141a00480c0080c083d410800769440b04050041d81550034075840c804000400c0c03442c03002041410420009903400900091020409411030640498640802e58449904e500901c0510540100200e420001468032a0710701d4601182a1070700c0d0b031160b0226464004060f20024004660101726003110750b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 930012365 1250 930011115 930011119
    0x10b0303120108060f040f02130e06070903060506030307080711012a020301050a0b0306072016080601120201170a02040e070c02040509030c0a110402130806040c12020a091a 76
    0x511075150000140306280d00703120703800e200e0241e0800724059041103000725108a0f004595244841c031036a007400314009007045000740c415540c174030542031010103008035070041c00d095907450903803429818160106d802c0a40501d03c00d0740204200300009554105030341e485a040078011000880c2c640060f40e101203c080d0b2400816281c01a1040c80e09010341401c00e5070740280c008010036a500e00204084642d816402e40e4503030302090000d00414480c00020b29010b014150f900542d268400d030307041c030f0404c1c0552805003070701c0c2d1000e003409200002c00078a030041983c46801c0c20420f40d1030300042d000c1104130680c4044403540f2400665184141e804403801402c0d900d680190900c1d001c0c0c00100240031890041744214100300115201c030800106403240c0c948400060002006c090f650703c8124505403e8803901305400340040b00d2841401d01100c0d0050541c3d0016008918083c54007540380e844070741140c00c0c02030800c00e002d0056215450608159202c034800010050042d01351400325520880f4216 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 930013615 1250 930012365 930012367
    0x1110c06070305130509011a09030c1e1203030717070c02150a1803020a091802030a0606031205040b090409140f0d0315030b040b06120a0b01230a050f0102010b0303 72
    0x4802c01d64441d00400b444c1c160050303c1040f0b141c8401c10042814028816801e00a089003401010b44140100038007456000800700c1c2e40f05030b030301004511460024607840102030043c510075442c50400880c580390350702250001e9441c1d49403140003d440002072980c00aa01d148280000d40d88a00442c480300c032180c3c00a0516000c41400c54542445500011800e07001803000e00350084103144091180c820369034010011708540341040b41b00b500602a402500c0710540c501c0c521100541c8050045200543c0910b0011614904609003800016a1201d8101c10008100400c00403038030304070182d60492000311800304842d11107090028245196222941d8580221180b043e50310b4800074649400541a840510807144008907a14080100d4400a0880d145007000600092800ba28069126a00400307243d035a01603401c81e0b0b480c02446000807902520840014400e0700620280404a207001602e000e502d6082039010420440f614414140a5100190b6590311a03000707410001480c44050102c0b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 930014865 1250 930013615 930013627
    0x803030a0218010813141e0d09150504090917120703050106050f0405040216050706030606030f061401080406110f04150c0f08090a030f290108070501110c06 69
    0x60003580003090310304064040501c000b4080d40204501441a503c4480702e030f24a54054603604141801601c0b0300c0c00d54080c01c1d81c0c003226421000503505071003181c1c0c8024800e0304000c040103402d039041070704445840420642407030006540314048400b0b0711005040850110340034a010340660486c50100c282c03201020400c040d0740c0840c0619207100c1c50055070148a642d80c0c50034251000d1041d1070a07151070080411041c041ca003403503001050300300181810460032901c261034090400080b81c000b40d0001c2d88030a001c1041c00d605000d80c1c90810040d8108000309850700009440c1481a860006e0520002500190a0044030340c0160303100307005020b0181da600c01030603003804250300c81d000d00f1003110742034911456050f100354034920409501100207014403007645c1b5840001d4000d1002c6030341c0903405ca040840000d07000c0f10700b651618070910450003246000031803004d50340440c1003070b8066000c59030300400940c100000e10a045540030b092022012020142d82400d20182415003500201e00081c9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 930016115 1250 930014865 930014881
    0x533030c030f15210c04060b040306050a0213030201031d060a061a03040803280207030c230601060c03020c09010e0906070f0e010e0409051e010f050103081909080303 73
    0x95200d90342015082e5129940c6a02829a10340d40703000841d000f8010811080758020048040c4001031515401c59804c01c01c504009410b0396403d420220384114003240410410000307000d0710f500031a1002040d0304288141e5481a0000d00307601c0045d04158554030340c080302403130404035a82113440c000f064600c03034035040082c2c0001c1c02451044801d08a0503540d40241d0940000036070703010380d5120340c1c0340e0310716140c4005180c00460a0f144101c01e400740c4001c2000403004e1031004090311803103030f101e14060f0051070624240c034007180142808081c0000000c0d10b981d8801082c42c40c107442050a2108100d001c50a0480c901402010029000301c1c90100224040c0c250048181c440e24100044621540c5d8501080303d08040381e20256011540240c2014160b41c02955404082c800c041c0c80000d91550343c1d11082e02e803001c984540301121900400c4210b40890030302801c802c01c00d000d4020b001552450340d40c0c035154400d04040c0440b00d004100c40c03100691140c40054010001d41c0c085030385a0070705480d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 930017365 1250 930016115 930016117
    0x90a022101052b06090c08151501050705060a0c030f0e07170d0c03051b0d0309050c0d0203030301051c0c080624090a0e0c030f1b0603010533030c 64
    0x5407610400d0103400711007124400c44400340d04198500c2c2482860501544c80002a10144e84220f03080310000a0218110804114000803d468012002d600d41480c000d1001d905802001e61410843c0410040c000300d00300003207c5401030801071000a4000000c40202c00038039405a0300180981813510700160441c0001d40b04050b98044243c000a400d031138000c03d5500c09240c1400004120105501d074040390195020b007028500f403ca4440320903040c02d4041b400c0580014145010a07510402003081c41820442e2052081d8155000c40100d100c0d81c0000303940380814400e03940302d80410800f44540e9502043d40c84126070784a4014204c40307440b03886080e102c110403940c0c0790121302218015102ba20301c101c43c40030b0581001d007007840152603284800c000f0b00100c03804107403140b040b02c5030140c42c0d44003003091090810303681c0003812030074581e1141c540c13845075501050381c4501d105000600c190342d15000480c0d218101052107180c2d40b81c8401d59550304d862036524030041000c011040143c80a2060 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 930018615 1250 930017365 930017369
    0x23010903180e130605071701061d060309100e0f0321060306040c05040203072a0309080f0c010c0f0606031109060102060103051905150106050c0d0905010e090a022101 73
    0x1441d40d000d203580301c80d00d50702011401c41d540120716803820035071004034a9a50005410250354501499620986001035400c0c040aa1000d40002d41c0c2c2c5104030003504901e610440034a0048428510b1400d01c1d48a0983c0c8604a1005614540c0c0d41d111007403282c00104500186411070606a0b600c1c1c0000c55103140000044844100c0c0c044003030800500c403031030081019072055500603c1f40c494079044c10700303000007500018502400d11103030110111001041d005054580400c002d03504000718010700d001004090203900210741079020000c1c05003108800300b401c1c501c01c1000c0c41c1140f403800f800d04185080b070b280e140d80034105034500b18010041c420b0090441c1c01440b0260b91006e00c03912040700490303aa19007444090042e070084039010880380380000d880e5103414000d0702115241501034141c800001821303030121002c00c40000e0811060b11007070060103803050850400b80000b51805001904d0f000d0780d404240d104250b4400001e2810700140c1c1690710112248108109081030b240f6101030603034080c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 930019865 1250 930018615 930018647
    0x70b0103051e0a05030f25110f0405040b0402010c151107060e0303040309050f180a0510080a17030406140901090b150d1205040b0a02010615050901050723010903 71
    0x70207030b10b0005110008030600c60f00d6002c0000c3d450400ca036413101e515900b000161700c0b201100301c86030910131072499050150350390064010170340606c001c0c01000354610703545041c1806981081d0420002c0b03030420410550098081c01c0c100c03003000c098604450b2404040c10b0721200c0d1840d241d602616650500c000e08a8a0710030340b400c21842c00289185650fa0004503401400102601d00501c013034280a440742d001d840018182108a180c2c032581d000c41e888048840d08001580d0f2000c000c145160300701c40000400c1e043d00502078200d41c030f0300d5030380312088491052099030301c000002c142080305942c004034108041c40b000208505200300114080c15090105656500306070004c20a40d140d06084900800c0c4028504a54210329540302d0640380a081c1030b03e024098103020014500525030014400c12255a000084032410181c9115581000703030a01c01c10050140301c00d08540c0d8000c4100c601d403603001440154044a20601002003101d180d403c540c0c0b650030001000c0406821649800301d943c95 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 930021115 1250 930019865 930019903
    0x20f010b22020f1c141305100b1f030203041506060512251121041a0c03220801110313020a05060a0201020c0105010e1515130b070302010f050f0714070b010305 70
    0x7904070043c50441903d41b0103081500412040004002e80f580f1200c410b000c007616111590640724035501c4080c042601c08400309400008020030085a41d4245440f119103030020884a070074033764010440d01070f0400725281100d01c0c5000c181010004244181c8203c4c1c902d441c00101c2952803802051141030040502c154032910000d1800290110a00b00c8a4080c2c41c140c1c6050910300441c0d4448500c403c511040c0c046010400c5007090007050000707006550b90f43c1ca40300b0f4072140c0c4090100c24048251b000703c505074580700072942d05a1320141141c2d0801002188440c0300405400040d1840d00d196004507448800010282240ea03019005007489040d19402080281e81c0c583c010900c40404407000b903603140c1105903180c3c0c0391505001f03c5807030303a03e00007640d4101503040f4201700c143c10701e030b41240116150110740401010340c24007420a040301005001e00c11030a20414200c04010080d028000384600000389580c44407558084d50741c1c0c960071071504460b55949003400d580301c07404a80303203c600c0d40e1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 930022365 1250 930021115 930021121
    0xe0727020702102f0d0c030c150504030f09140f120d02010c1808100c1e0c0c1e0b090102010f150509010b03091216060c020f010b22020f1c14 62
    0x139004407583c08101010014215502c52070208a4980d80b840d4011001d01a10542841c08070b84000c00c8112a4010001d0004545c00c0c035040152120201881003c208003140a06005012104482c01b2846c4410b95001d0b00780a0184001036409052501d042c50310310500c1c144000450781500049078642540d141c10f084031540b0904209030700b10078000c007040b551103c5c04101c110708155022403030280707180c07800c800c40415240404014112585903100050350005800091100064014000f055802107600c0310b03091f68030407200102201e21400d81c00510210f00030f0100e9000303402c07210f804d041d0601c04002c0d0710411080915000103600949001c2e030070540000c20785010316811207000d0003142c002014425002c1c0c015040b9640b1600e680c02d5481b01e0303c00040300280041c0510007d0171041d030041c28240c8503001d200c5084030721089110340701e0fa440500c4c52010b03c810212805499001c040e0260b903441450584e02440d102d5041c85c402c0343c00304000f149400078540c0d03102e0740d0054030408010699807 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 930023615 1250 930022365 930022427
    0x20112020901021203130f122a0f0303020409022a010c1407060b100f1409060d0e010b061209070504022a0a021002010f0e072702070210 60
    0x102031201c0311030240c0d11020042c0410391039240a160f0010701d8020900d028042c9581d050041e07541180b045070752094499003450803c3d00450b0085040c4490b580b40107002c4200b0707110030050045510050100840040c0d81010b0501c40d0b0100c90281100035010740d50fa0b91035440e04201070b95030700e072541ea60501e03004483ca500c40040c050989001c0302c9565008650140f24092982d40e400079408442c1315613105603921a580301c020101d0354002954982d10441e85519201a05040c00ea41c0480c1e8605400c001c0c8900b1507962900f83c070341000306c1c0b81000441064840303a580c01050040980303070784004017181c1100510040d0000c41e22070710b0721000740c41d00310f42d441060005034050320a00c0c403008840004003040141d903c001044103000704404032421020250041800100f44800c845d0050351510304290b04400c0c240910001105a0b100500010f407402c54008403482c0b0180c0c10001403100d210b41004180c80c0742d015514050b80003000396802c1d0700600c60282c00b2015100030996211039001c5207180d10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 930024865 1250 930023615 930023617
    0x405070f060e12070e0103030513150309050d0c050d180b0c0c0a0e0105010816030219020c040b0d05070b1605030a080a14040b010303230c16080601141e0d0302060402011202 76
    0xc5e640c4a40106169003142d0701a0790a8100b61060b20144805070340000e050422000c00424001041e280007400408904020703061102030107070a000c0c0035062403c80700054002030710140c10380b600d00e0105664610010240000c0c000ca62080200340c0e400300308051044000308e201c0101741d000700c994042c083e680d07043c5005541d01c01d10843d030110b183e820010b000440c50087d00c2000c2500b619005192803443e00c800c100c0361281c10090700060780700416614250409104041d03158108a494607a113114a03a00c665032510301d40a03000403d400804c81c3c03825088081186c890f07503a4024180d031b44400308001e0007051300100300d40701c055a40c1021030b90000424200c4020780030390740001011440d6800c54030300b13584162031b00c10410800c0d103008001901200c0c100c0b010301000e11030140607003030401200d1601c658100301030708601030700c0e001000100251040866a03c8655006850042c0c502e6480c0b0001030b0700f0000201c8454102901e80c810000700350b03021601c0c900ca68401d0301c2d82e5200c802c0e43e81040d412 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 930026115 1250 930024865 930024869
    0x1404230103032607030608010509120904020901020705060412030201050606030903090d0213060816060f020a110607020904111504060903030c0602090d1202010507050703170405070f060e1207 84
    0x180801100620100348114580c1100943d1068032000c0021020200803030440c0855080f00029512038003032007507050030b01519400c510b40c10014443e0500214040c144d910850389554070540c2d000407002c0681c2d00a102d600001e01f03000b0300c450340f540c0c1e4900c49943c0860036032078110010352a11000031440d00c2c0100940c0c1c06140c01200450511100d036060200c0d402c04042e003680e024003c7e04c90f290043c402401154080c121a1015000c800c203007240460303480145400410030b010000300c00c90042c940c0000c052401c2a08076801c00d45038080d001c0450814448c103d4003035045003142e800c0009002d640a4264000f2070300f501d20301d41200740d0340310f1904580603a02405001505425042010030f01c45c80c20400c04600902005150503142c4c0d0008220741e04000c411295100416070000d8100c3c1c0a01c620355008405040061601c080350741c3c001c2c5066044001c034144054403e0118061100030010701010380022081580d04c0d9407540000781c1603078a6008018418868602c41c018407080102e80802 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 930027365 1250 930026115 930026171
    0xc03050112061d0708010207142b1724030c1003020c0f10060302090c040e010b0711030d091415030a1806050708070e030307050601030602130509011404 67
    0x4444801ca030303691005440000072108142c0d0458030f2449021109209450082c507250b03000507a5080640f4000000d2503814070120616040280d0340500031440801807004d090020f80036082d220716400c41910340745803002c080e0100d49070400c10800407007462194062884c41d161420340c6c620120b0b10406d542c0f01d9030010f603950445048050000c03e5800b980142c1001d4040005981c680141407141c2868245c001041c14400703600c8090070410345c14024090341d00301c03918500142c40c144c00c240f000d44481c213042c8216010107500003125030500c208240d8105032084c005050313a0b100944480010110800c90043e0305500b01c4038a0440344c00d207000c0074114403032003007034090a00356942c05403c40010310881a8882c00413100303010940008081703106031807040c2d0003a00c4d4101107003071100300100070f050b103c44900d00030340c400c120071801320348001100380c1101d42c03100e030142e40c0d2031452002c5184811140d2109070800076420012810f50f0580c65074030303006c0c030341643e0030001414558a110949160000014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 930028615 1250 930027365 930027389
    0x6050405190e1908032703041a0f071a0c0703020a1217100807050f060d0c0918020702040b060405150906040f14010f03050903040b1c0203040302030a02010c030501 72
    0x34042190b00000c0c9a00d2500c8140c0e90a202854003034403481c2042c101c1107030300b1180001004944082c035441e1100c3c0183c60b551420805a400f41c0070396403446140242c007141102c104844000d034007000d049941c1000b031003104546400c0145002c440300414482080030701e00301980041d082d04101400daa008a805034000d1241c807203903803a4066101c1c0c0202c200c5081114803945a030a61948448960140d880c1c100f45c0000c06107454005410b10516800c910303c50308840a07004250340d00c440549500390125800090454452181551240300d103500080c1100c15440700c0364480c01e810760141c1030090098400340700400003181041050b115502846a0009242070080c05a6081340c000e03013111000604140cac60582c07220313440c1d401440e03594040c031610303800c500007090b480d40d201c4602d01c10f8048078141400103060003001142c43c1e001e6400303000340003680416152011440708440804000f40b50303c00319070300c1c2041d080c0291a0717031040b144c020166082c4800040e103e442481b40c0ca04031004d4000c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 930029865 1250 930028615 930028651
    0xc0203060114060d110712120b01080c12060d053309070e0a02070204020d0605030f0a030e040b0103020418022502010801051302090405090c04061d01060516060c080a06050405 77
    0x208004142c403c100030617443c4103121240004083e05c490150181d15504c510302ca50058202c501e05840c8064001410400d00405111164095005a8541e0036170f5826004d01943c0340e0002c0386107422504d1010b4650310480d1a044034615107200d550300804102d03c500c00e175060841c00011325524056640b60708962140364200912142440d50f5500f02c048200d015150202c1ca40024060384c000400c5510101e95500c410400351038200b00d82c2d1030417213010000c0c0c003100314a5103000d481c0007030481c00f1034042c4e9240c0c402d00304607078405e5044802400124601d80600160120100020b4004011b80031401d400319001c0812400c50401e22441103034147e4820106038200800e201b484000c41c100c0b429160303000d00000390182d0340e4ac000c1e41c2c420418800245408140c040030802076078080d6101d0080c8544484000300c1015a00e000a41500c08900f01659540c50000c180c0c06062544400034100e0f51600c520a0405a44146003a0040d0780360321081c80510386460800c01180d005589007994490300b0100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 930031115 1250 930029865 930029887
    0x7080a0819050c030f160903060c090909050102180a03110d0f0204020c1510051e0102030c030408070911040608060d05010204080708011e0e031605030f0a0c020306011406 75
    0x400d55101521403004120032503440729280907124240d031020003202c0d0200070000d00d00204240240c0c04441c000003021a5001140007400c40c0c0090f000180070261908512030005000b582c80d40300806409404000184141c1400e50003900134043c00c2c110580811000342d10303490400c2040080c3c94100e0b5a030245e074007800c810001042c8007140200d074194811000000960398a10251107880709040107000c0340c0006c2c00b001414418014142101c14080080c1401aa260f0f5811040c58854145520003842c0249006030301d14000d14503d01254400043d0104004501003404c808552200501788034210310003030070302c286000300d000e114002689500091724900d00b8001154040d40900001460036444030a0142032220030b40001c005170b9120110310320504c05010381c0106002c0007040030021541001030300d945901c00c0180d0100e81d040042c91b50f07028854140100c1c1d4101003202c400503980c1c48542f0000e0507205024905a10a0040800020f580e04456401c0101c691b0000d00e61441c0012a01c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 930032365 1250 930031115 930031127
    0x5090c0a02010b04020a11070b160305070812071e0306060f081015050a0e030a0305071203020c1b24031b070c0b09030706090605090f01020114011e0b07080a 69
    0x2004100715900d034030f00c00f0420384440c0b00400c0140c00d140c0c2c40c038546149424181c1c0ca040215800000a2030302000f40f000f8012110303072001d540a0b81351900c1076684000b4200404140180c55100361a2580c0c0e80500600dd0341100707004001c04082d01c6405211034072140e0a03000c60300d044c411080400c0241d042d0305541c3d4441e144595001c42c2c0b0720f80402c1c043d40c65030800000d000000d10713100040350340091140800d42c0c0111000411101c1140100079902c0d4546d0020818001c0c0c03440100080d901d40e6200039524001d80690300d650100300c00300c031404607040c1e2440c021240303400829800382510203580000c40402601622503170300000b0219207103464808141e6040d01d01c81c000440c14401c203001d030710300152a41050074006c0010300503d1380c580190808060900d41141e0110080c051022410080d69801109880c0b0080c022140e5040c00c480f1000140d000d0001d401c80310407103600c85000880e01075508560118800b00002c08140c1c00c54540140c0301c1340740704038900070301072840911036244250700c111 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 930033615 1250 930032365 930032377
    0x607080408190302091e06090f180a330e13051501090617370b0709051012091406040f030e180a0c020f120301090509060105090c 57
    0x148900d06480c030758402c062004902c810400080c2c00146429075454603184d5000d10034402004d0b41e04800003480060359a20410802c0c9000f0140c0080f56040303030b0780b802c0301040d201010149450701d03460b06c0b081c40b40083c595003142c01403540b240b200300b40041c44032000103407a801c440540c004075241030481c00c031038814008221401207011294001c002890501c0b06e50842034909003506e401c7d50400700e264040c0d6905070030040b000051300c4212100102c0000d03002908045507903000300c0d81010241200520f00b40303400004a4914241610400c01104a5040d8031526603507907181036058859041003c244039400441000944811289161a40c40d52020a0140c4510120420240d11144507030500c40104d80a40300c40c90030196000071305070424603491220340102d0328810b20f80b0003c039914510301e101074503048007582e4842c8078401540c020406c07281b0101100741114030009454503003410a43c0240280d01c049070a14000c644008400989103040e50300040108030155036940000d05a60022 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 930034865 1250 930033615 930033623
    0x1104030803040209190c0e09090a08030118060e0412080604020a09140f030f030a140a0504121403160c05030307050d0c1109010b0a030b0d110f03070f08060108071706070804 76
    0x8483c060085200324886d9912500d4691a5581181c42c603608005410000408801c0c132030704800e0700741c00001c401008590555819501603441c00c00400303481c8009062507041044c02c0b4400d0410300080c8200b080b0103c04a20059480c10328a686400038402a402403a2611000c14502041409000382c1c10290000b0040041c00d103c80d03802c0040000b900e4010382c04d00340c0c1c01c80c1c6c01c0050141211503000c42006903142c9040c01c1c5915000c07082d00002e10b203200d02d20820640300b40780400d650412802d410003022a41164040b43d4903162902c0c2070041c2c0502031801183c0004a141d80007820782008070a8031407098103e0050985040c251000b6a5080c400c424212081d0b9101902c03541655210380003180030700b06c400441a1951070040340039007200d01e1882440e04c41d003c136005a500003424940410060f107016240e805d40c1d110380d180405c1c6080c00380d4005000c0031784015004680d02ca400102a0704070b42c0b80c4011540c0c3c11741d480006580080740005400d4880e0043c00000380c03068095001950030600c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 930035971 1106 930034865 930034891
    0x1603050912010203130807080c07150e03120a0315080d02011a0906030a082d09040501060c030915110a0f02010935030c0f0609011104030803040209 65
    0xb0010000b881d110001401604110005094420f8030703c9c9002150021a21902e100e0845000e601c401c80c00a40c903c40071120314640045c5190742d44d4140c007240c0c0c0c034150380d80308101c01601005070044401498044006540c01c000c03c0035141c0503a80f41d0002802d0390800d00382c207280d507416030035252145003142d041c40300d566030120300e41a81c10383c80454a61741f0320541c02607040c0044810441035810003040041c1d82480c910fa4010220040121f8080203a43c1e02d680307055900c1c145e0a08003800146041e0414042d0a0b00c51008040011450030050b05d4100891141e51500c00a4401101c440c55010500d00440d42c00807200d001620010394840401800d60380081d40116001c4001180b019031144045818030050040b12040d0002e44155100e030102511760f507985100590b202e841562928940100340d100036000c0d00c003a6503000100f18695240c503002c1068004000d0460490250 = true := by decide +kernel

theorem cover : BRFrame.Cov 929856115 930035971 := by
  have h0 := BRFrame.cov_init 929856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 929856115 ≤ n) (h2 : n < 930035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
