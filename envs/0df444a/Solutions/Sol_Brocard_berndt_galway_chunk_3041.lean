-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3041
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:29:13.275282+00:00
-- url     : https://prove2.me/submissions/9100246f-ab38-4f8e-bbaf-712798a6bf99

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 546762589 ≤ n < 546942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 546763839 1250 546762589 546762599
    0x90109170403031e0509040b0310111b15070807140301090203010503061609050d060212091c0201020c0a0b06130509031b0601050d0204023015010c150f06 68
    0x1408040540c000030504549807400c52801420154902440222020f1601c0d00c1110865200c41200c0c0c065401b902c0101c3c4540880740400c4c940520396002140c01d504020307100e000c00c41d00001074501503c400d01030b000104000740a642d103c0941d5400c2c0c1140701e0700303c40011307070080c0120316158000c181454000074200c0d400a80d0600786d00203800c180101900000100650f1804028580d00815441f02071500e0140b4110082c01c421182c1c81228010302101c8104014040d40340c0c1601e9440c04401111001031901410041e202c01124030100d040030180805000294414400c1e9898401003e00506030780001e074440c140c0050009044590000b0106426001c0c14194015280100c014100640e2188a809074085080c03c824120b51440e903c160010400391b81da00c80d605005030380540380142d030b50080786111a0110542e04006030000d041c1d40455405141a4000c03074403401080d05994001284003004441c001c40c8168007030181030716040e002801480d2503104e0002518046800180e482e694 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 546765089 1250 546763839 546763853
    0x180405060d061d24061207090b03030c1002090103110301140904020402210411100801090209120d05090f040c0f0e0a1e0509070f05030121061121010501020d08090109 73
    0x180c44c0321110020325aa4000f00d06500d051000e41041007121080c00003403a03103000035902c01c000c1c443c0c0741a0546030380e030303a0039281c030140203c510031081082900c02c0611484000c0f8040c0d8000703160b00c3c1c000703031800042d41840d0f8840c805590513921844005213000208004100031740d40094016a1b01990801042c1d00941207003440d0380a46911100c3c0f10044d1500d82003444020303134480c8100340500300189841b0b2600d41e00c250014190358407098010303100d445c0d402c00b10303101404040142c1514881c4180403003440750001302821510710f088650341140011501480295844425a00c0110388c0d04007001c2141405112501c038030304006010b980c00a0b90302e00b40e01328500c1d2100c1e4500e0041c1407020041c0302d541080d01c3c0e400d0740300340a410040505071014400400620051080d0700d843c0f015a04558400c1c0c41b05803070101500e40000c01070024502150f42d101141e0701c0b840c00d000000b101546520550384206182e54101c1780143c015080041883c1800d468840006046810b40e5585100703d00004c0c440c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 546766339 1250 546765089 546765103
    0x305040b030a1e020a1b1505010b04080610150e010c0803011805060922050304090219020d09140f1507060506121b0103020d20180405060d061d 63
    0xc07600400c042e059104000710303603803200d82114803d81c010880d03052500d030840c45500c06510600c400b0103810140307003003510200446820216002e810072000056010242000e44291081c240964150b07071a02402c01000c0801c178030510040010705116004200c1c0902880400c07000181000013203240c90343d035009200d42c030907045010780550302c48086006406a119540d48484282c0c0c994a0301c1c04c0801020111f45003104011104038400b0501c40b04101d01881902d005022822055483c0d41041c1141d0f0400a075001c440401803003051108042035200303e5041040b1000e00c07000d0180c200d031000c1230010a8203480340c20740e0401c224000201011074200020041d040c040c480c00665410074808102081c03104001980aa03444054003003142e0003404441420110242001030b559401d5400f2500a041040b12542c440383c40b10f40400c0050342d4040040441d81ca884090f40003000c0c86c0740c1040202c500940d2860340214403c40b100000401c254000d001c102811100d100c03030007510308079152400d22 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 546767589 1250 546766339 546766351
    0x230715050702100f120b13020903031201060305060108070f080a02030c07080310061e09260f16230d03020307020a03060615050f09011d031005090f01270305040b03 72
    0x1382c0d44144803009544820f0b0700041c488043c90502c500e2400320005421117040803e0040c81039400228107110b03076010412520b07612513583d00686c1640e90382602034001d280884060b17011540100008e40ca07a4031611003481c0003c7e450700d03020515100c40c81144029000140814650b040400001002c6150000910721603868000c218828a007013142c02403900b210803441d049440c101c546440407841d00580400140d0700700311030f4161800020902c0c0303800c260351010180300500030030409004004000c1840700c03a10009a801818036a076415104c500c40000d070b03c20300340050342c8490303807031080c40c080e40b0122030349029104903810260740380c00164040c0b13440c6d48211503180ea2035500304444604110000035807103107401c0c01c074103000c0d5140710714a8a12030120782d2810041c076000954510f41e4820107101a003080603044501c0400c000122800405c8161581e20340d03403051441030710b0004014000e002e03a146084601140d60625110101866518007034202e003484400d010205a480500014521401e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 546768839 1250 546767589 546767597
    0x810060f15271206051b0a0207120521040f0902070804030609050f1209010314090a03050a05120705091e061c020405150723071505070210 61
    0x5840c1216145003a04035030712030310314818801d511007900c50300140742e01d82104011074a00280c000c4039180a0002d80340b500030310749900c108000c10050014075441300c1d206a440c0f01002c01c0000c601984003906015408828006901c00c00c400d0001c1c00361b14200001c498414000c6442a00e00c1907200401405044030369000b000c000b040400840f04070f10800d100510280f842146040e0854840181510642c04040c2609444105450400c5020084800140c005a0039141103c80b0a20344400c20380c031540c06140000c1c24200c0130f818030301c2c040b1141c03030150300180c1c000d040e0001940c0d019a5282c1140c0780c01d0f811720a0a101b45021080d081d8003407407084600b0303658141d0f00c5200004211500b60b11085410f030f4403100200d61941501c0d03c5c412540780a5007800c0882146441040e83d030003900c03454000a070072040404184940c003252202070802c0c50b109031150701d040400520f240150751446039203000c045c1d1001c2c50400400010070140c44150203140340443c50400305801161081842180240c001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 546770089 1250 546768839 546768851
    0xb04060e06100b041a09090103050c1302040b031b070b160f02031204110301150b1305220c14120702060c0a02030d050a02040e090703020406051c0b040c0810 69
    0x901001d228003a030105000b5000c4403003604000c00e0701c1c494080d500510044090101c0c202c581183d0541c05d50703481080041548003150707100e1600513115000d410b04580104201241003011107110b00a84090710210650241166500e0b00da40310031401c0890000b00c0303145e04000100116403a5003806103d060004404c1c0e4009110040041065108420844c1190010311081d888034240e2200c0a4001e50030440c2e00c5811150f0100080c0100400c015022040460010000c1c1f290b981e4405002c9890b0302903c41e0305240d91301c10a00418070701c4103100c05c4080c6902001c0d400103151035442494411301d1032410f42902c1d8103a580c144103640c403074080c5400d0300c04110304218030780c5d50401245034002c03503881c02e10b8107140012074041c0d03a0b40605110504140c2d203680006d1900a003950550b4000c3c40740065001280c20700c1030704030b900e8100351300059019908188004c500c034104000031400c40580c203941c1e03030b608403c1e03511801030f90310b8050021140f000300b28200149c10901045101411000340c2400586 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 546771339 1250 546770089 546770111
    0x905100c050d17151f0c12020604020a0608090111040b070c050103060b0d02031e040c030b060409081603020a0203010c02070509150102061614070b01091d0303061c0b0406 75
    0x24049400180400b00107842980c00400708020382401e40054012000e284c624540a0020320340016032075202e104c0388000200045141c0d841540481c000b8003400181d4407642d1b62140c101e0b20303a141210003030740219101004100d410b20030310b4102d80c0b29000ca000050717449000409185a0b9202d40e000e150080c0e000b052120a00c041400700e94001c0c0401d080c1005040d1078a500c0c545940200f190021200d40d012002503400910702140c0603012000d00d51010841c5414609507202d03103180d001c00c2e078003031428000040b428140361044540d183e0308541d9541c02c240c21a26000e40e00c19540800300c085024108183c1e0040c1c909010f9545249210340103043c2880c1004c0500c0200c0000038109c0c03802c40041800c1408a076000f1503001d42000700c45801e5596400c0061044d580f500040c0d45c3d08070b4601001500c01c0501180b20311550580d00310450500000211403400c810104482d2081078554100b040850021f14144925088543d40cfe0301c1400c184442c2a00e86060401003283c054407059120034410034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 546772589 1250 546771339 546771343
    0x1b091801031b030b0703021305090c0c0f010209090112020402090307060e030c03010b090a0507140301090207140628061715070228020f0d03030c0e0d11040203070905100c05 76
    0x8034101802142c80700c8107181d41c40345528044080c0c044024144c0c001494000e2034254480500a0000604107200314107005115101c9580700600c42d88040c050100d551103203460600881c2d0307541000500d01c00080e400e0040000003d154920120b0784503508001000f2079880511002e401080f051b21001c400c0a0084103041c02e180e081c00d481d0740300380d25280b2596010707034810803056000040101e00281d15540e00c1d5054404d4442e1094040c00da09010000003818003e0b5001071020340d10031800c10441c20075000c010340d551030b000e84072861900341040d0b04600000601809c4a449020a41d0205515507608041640307400818030402040c1c00001120310b541908a5003075421440a1004001e203150000380c0700e070a020400007070002c0841010a00d4299500e0701c0c0031400e50140202913160042003442e0281c0140407900404000c14425581d441c01031070b02c0225000c18175002403403c1803105086007040000e5100a1510041c0451400e012480b07407110400489550480d84a43c0e885901a0411078 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 546773839 1250 546772589 546772613
    0xc080a0c09050622050a030b09072c0c0409090615080c06030f072a0507050f010f110111070c0618052d2d0303040e1b09180103 56
    0x3800707102610034100442d80301d42044032002d5801c5080d40313100c80d000e50a03c01c003054981e8800344e070103861640d001c0244503504034614040c000c10011184040d554109a80140030800300e498075502550144101c6407007010100caa02c000a444050300d803e03100ca00310812a01c0615050350f511755130300b401180040342e24107540081c056040c024100c2c010340100088282c8001401480a80c81d110080f918460040c440c1412000c240c0c800c50f54a078160143c41115810005000e441d20720840c040054a800e0254089200c80d0b010ba4484064410181c02030341d04500100b9034003910341d604e547c41040d2401620240900e030388074003000c10b4100d10342280113001c2541c0d03070804080780b0011340081255981d4090050b40700c1c100101c5094001c0c40401146101803a00369040b0b411070140d650300107103000007101102e084a400032410300412920401e059030f9010fa030050850306405000400d00f900c01c0c1c0001c00650184920741e5a14140780c203004509101c4c0c1103e040520203030b18000600800000c0e44d001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 546775089 1250 546773839 546773861
    0x3100c020a05100501050f1302090a060e091602100207030c0212030a080c09030d031e0608100c020f034f060c2105070804030f1b06020a08030a020d0c080a 68
    0x90144c1c0d41020005100049100d0b48039224268043c9540c03c00740007601500d01181000f403412003000d03502c40d0b01400c4031041c1c0020b1849124581c001607000100d903115070f200e050320340d402018480c0f49002c0c07800c0290f02842003a030522074544410f200681d50406c030482a012150040c2d41c0358a9054400350004070054400304501d58248941312b40d41d01c00082c0c01840055500e80850030a401040c3c0f2215407107065400b400850801c40c0103e03400000041082c061142428200010070a02e00d049071994003509030003010703030020000703090000049402580c1103070764000503190b604d1800c10020040d000c1190b064104a1004164a0f48480740c10804001403405060080801e030680d512000c66641d00444400c103051115898105d0324400c1d41500c0019501103800c9039115180e0130b103503a0414483e001110780b0810502115130170301c1c8141c082c02c103da8103a0010080100b450341c41c502d00380c000a00d40348d1920780c02d00c9a003100850768080d00360342031410f4403942c0a40c06c0003018a010354402c0349807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 546776339 1250 546775089 546775091
    0xf010803030403030c1202190f051c0c11060702010b01090f0501121d190215070c090c02030d0f0507270902030a020906071209150c0206070203100c020a0510 69
    0x1000a500040126988664140740c00103550000b450706441e030080191818039001c5c0b01241d9118030740d600907040c1104140e5030703d0740c03000402d58010441da18412569050002e14040e1412044800345800141750b41200b42030440c00034541001d06454200c0454903280145e4541030300002d15600004c1100141000f0740c80300d440035050200181070420300b040c2c550030603030380c07602a136003c0103039600f40d04d0005100c81d05440da00107020190000c040c00504050744070b0048598003c4109480741e04a6040a6020442c3c011551810404400400350982c02c00294041040021001e00d6584034580c0103089004000030f0f2414280802088140840c44070340749000d000700d04c107030720082d05118a012a01d01c5840542c2d280d49000c2148081c1c01403a41064100307001280d61002c2100d441106500c100840d52401c610b030765503000501520b0004580c00300413400000141003d8103001000706000c40c0040e04559600c0705900134002110380b0310400f240140c108034503030000c101d024000100d0000541070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 546777589 1250 546776339 546776341
    0x170606090609091e011710050106090608043e010c031b170a0801180b1c060b0d030203041a0c1b0a0801052d190b030c040e03070303050f 60
    0x200c1c28520034210680d00c21801c5030300042e15600c83c0001c009410f0301162008440e075a58030910402e8030000a03811400e401020300c5108000300d64400e15040f1075003a5100010503140000607214150040c0082d640c690300051081d8120141c1c1940404040c80d007240380b4000140d0b1010303142c0d191185051903041241c42c04030040826132000100d074062800014800700c003900352502d0040c0f09100319002c41c00b1000800c03009503091308015800d0407100c06041c1e00c4024040c6014010481d20540400c81e4418012034040380c01d6480c10104078007961140c1c400140c40c402800028401040880040b40103900c00202407040501031132070401090702c100d4500f400c00c0c9004568a03210503815401107248207580c03018411381d50314041c000d4024003040000308518140b150300c4c50607200003244044592940c908070400030a840018807031040c0c1c50b18600010f480e00140c410b002901d0305041c126490310908024001c0d0ba23130f4500c60810f00907507200003103554400f1460050242c440050504210f041000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 546778839 1250 546777589 546777607
    0xf0801060503040b04060507030e0a05010c0306120804060e013b0d05030d020a020c12070329060d020a0518040c0b0a0207210605090a0506180c061308030703170606 72
    0x14404d03035002944903201089941d21100110000c001141c0350041c5c6104031f4050b4400d0250661280180c00300d10303078050044030f4803426200302140c0342e4030340108000b03010482080800d02c101286000d18a0500d800000a04000d4002c501080c54145a9140180003004c14a1540820708004242c12045c0c6500000c1001904d40a840303011700840403100c190005120720600b4420710005041e2400140414040365924102c1e40d0781d00a2800121200d400362045041c805a00780001c10600c0710b00f118030002551030406204400050240890704103d122001062950715030352071016120407450031703c40e2481e06041c0346208480030390000d01c048404002c1c0003811640815503c044e0340c00b421086500c030641007241c0c1001040340c6006081c0d2881c08050140080e80841d03102030340d50142d17003114459180c0e441900240312504000d40002c0d03201c84100c4040303003407040c09083e00c0c55910352486083c542c1d4050a60031903000d0740c8118006816401c4281828a50108031900001c0640da5907080110745 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 546780089 1250 546778839 546778853
    0x1803051515030a060207020402091807090902070804060e12030d15050d1e1410020c100c0f0c0204090b16110d0503010b030a0f06090c1112092403070f080106050304 72
    0x41c480130300200e80000301074040d500d07150115000280007800e1161151090701e0403000840f010381d05800040c0340094000b420441a0094500480e0814405032070a440c0c988155450003e4112040d00b08142d50742c4e9041038442403006c0c0c800c61720800404259a15000105450226160445031082001128000c081496426100c0c0741e0700c980c21082c04c0404584c00e1002c101c43c0e26103013403019841443c0000c100744009070050040302a000b8103d80130040180780407410746408404441c005084000d126024500c2001c100c07400c540040c0c030003e8450032980310344010306421144001010054800400015403042410420540e403501074118281d440c000184603210600c90ba4186420220100311110503039401452020001c91080003c00c0e503941e052b41c05001c9540410703000c14000168039184200c0460071503100208284103614009004040200c140000d00c0c188000420702c000c1071500c46c400d0401507000300c4031a100c000609100c600300400980050b049103003041418010700001a0013 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 546781339 1250 546780089 546780103
    0x21e0a060b01110f0309040f021611040e25120c050d02120114063a110d0c05190602030d0e030f0f031506030c19180305151503 56
    0x800310001c20a5070300c45004a40c020080b0b02004002e001c0c00300f01e45a0640004020b1041031801d0301c003805070040c2140810b007203002d14600341d04808880c000f444005102107640c90204c01008200180440204030540c0c81e004800d20070007046120588a4840c0700c24400030140242111114541120344603038030000804c80307030320a1500892070070300d11200715039403c3d410606ca1607410300200402802d0002c9185a080161030340d03400b541e1020b000850801207001214102c00f412500406c16400b96179100c1c02e9205525019034000c201c41400001c00c1c4d0b51407001703c150a00070303103030100c01d5801c00f010003489200012510b0300200c20501f04006042c3c0200a0f604400e5110000107420031060300f0b86130841c81081c81d685000000003c00c6c40030701802102442c050350541000b41700340e03c400c20500007544001d881490101d90b0502000c412a080401004400e12441c0303480303100f0a415921608560711250400c9915400c441c0566028100c180b440307176400050f0707103841d0040c41064804240c603014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 546782589 1250 546781339 546781343
    0x105091b0102150705030a05061c020d06090204050403020d080603030301030f02061e040b0d0f061a0f0913050603101104050111030f03163c03090609060c021e0a 71
    0x44140c10052907802404075150070082c04541c1802841c1c0404018078030b0f0700441e07454070203600e0803001c90310604110800c01c4c14800002e0300301c602101d40d80c08110020010b44003c44400c3c2d200e45031640181c41394019140918031036002055540e0b1107000c09080d590008115601039801440108040780f40306c0d26a4141c141c040d51015541c410200b01200c00c4007070700e20307520700c031180c00100080c82044060060a000c00303100c4080211111401c11101a0b81c0188034a030901c028602c544080c1d007080000801026074210609840c214841e07021600321161402e400302150740d51402c108140c14240840b04228680303440405c0f030007840c810521010700807030107a10304020500480404d20b400800444011450412005403607151400e12440800f01c541030f504002039840c0804081c4624245905500c0006c115840d044040410721a2011085004080701055280c802d440c02140041c850303452a14006c21000ca0400306000005e45800081d20270031418249514000d40c40180c081103a00c4029 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 546783839 1250 546782589 546782623
    0xc0e06061209010b0d0506070f0203040f05010e030a0614190b010f0f02010b0904050a1b0b0d0f0204150e030f12180117100e0a050c0a0c03141317010509 67
    0x248032902c800f070040201207209a001106205a4824044000380c0a480b5000603940d032140020808801c030385a00992189114406e40e03880180513540c026400c00341504009411241d01654588415055070301882484a030707201184180b2480d1402c0440f14003400e103412034180302068030b00c40000d10100d0b4000d011820442541e1102184920070f4001400714440200303000340740d0802e8100030b6101d00c1161401c03034444242500c44034006410803000f03c1100c81001100341000c5070350503000301400030142c1030240399901700720100f6541002c0d003012944e0701090b40c8032841d001c1c41c01c1c181072074035240310022011540303e0701861480c59803520445840024461201e0551514080183d481c007020f51480d00081c5c00390000c02c4480440d03040f6110803101460784180080d250008688210b40066400d69503420302089180001401840c1048a60384249816444c922900209441b035400c501c0d4035503101c00d9891810003903660802107840c5032210050003040203061031100190b03640c1d4281c091042d22 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 546785089 1250 546783839 546783841
    0x102101103150402041e560c030d060504020c07090b0f0a15091406030c0a020c040c020c04050901050f0103170c120307030c020c01080118061505070c0e060612 70
    0xe51116015200282034080030440c140741028028811b10110303004400c2c045400c0c1c500d901c410428000c00d03410f41d00c62540e441d13101d94451403911010b901d4003960241c01c81e03051045011419400c4006049034807c00c00610345410b100200802030300c2240e400948524018009481c14020100b01c0b0012100030f6140000c45448403070200741041c0205400f81d520042c2c1040024403004494500301040803035954800d00c0c5c035103078074442c840103804089160b004002030001910008104005055500c2a801210b12040300b0000103820f5079152079145006030802040a45241002e000f42034200000d007000744031524102c00d03403081717014051001400d070000619800400628803811100d03007400303000c2501c013404040794030701c0b03d56803044d10b244001134070f4030201000030b81c07021403100441c100c140e44a40841c0d18001c0341400c0c41c04d18103a44c4080301e6030f072070002a4645071100c114243e200c40f61203007612804281400c00d5000e07015401012008804020007a1680d241011144800e003001c6104002e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 546786339 1250 546785089 546785131
    0x31b05091302030106090e0a050702070302010f1b030504090e0708101e0606091703070f2604030b1506070305090103050c07020d0b01031202010b0a03020d020f1009050102101103 78
    0x1056071807403079214010b840040040b50150784682200151116540744003202d131182c0380d0304800c549048610324010307000f012003440150f1080450240100c1c0c03514069140840052011a90008480046000c90400207041000039030a0092a481643d014090145d4628024505407070711100d8050020a541d00e5030303080201c45051410004401da850410004252184000307401c000040c0541a4600713904005900717002d000004503101ca0390b00040d444140c0001d503860f1550b42c01c0080b104001e141611f10070f2200e201280c00940300644c0940d160120b20709014803c54440b40304030454a01800e010000ba9010070707080412110846000c0c07900084640c0e400011008a00525400a503c0107540c0614000e010004500702c0c1664000c1c034420b0543c14081e4020b0b404c0743c030584c052a401c80c102d0401003000d0b160010b05074107124005841203c0803002c00b000901300c1d24040f0f0300d00303020516030f007400e11082d641040310aa03100d0609404111483c80c0300c0322148207010091918103a501e0a04401c10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 546787589 1250 546786339 546786349
    0x2c010c140a050408120c101b0c1e1a0a151a19021615090e040501200304141f050a06080d050904051e0c1b0714090601031b0509 56
    0x14107110050724485c3c030400035154643d03406554845014400d06100410300e035640c3c402c81c0c1d00c2c1203d0100200d101c80d08160195882521500c0c165030002082400003106055103920386072552051100841d01c444040142031000405000120000c0c07501d070010124843d241a190160ac0c00c4044d912140079545141825038480da8103103840b20020311600740c80c00b5070005030103c4420801c1d2501440161141d000791200d0322802880b5001810010040204d4a2009102e9070010f0040001003621586940c5158200580b1014030203a084000208810b102d98645992541401140601040c0420001d1a1205284a100e80b1640344d607079404188100b400d0f500c008024002041910405042604045d041d90803041040f802242050005560980c4080030301c05c0c5010003650041d41a2140481500c0a4211514860040000015580110b001005040c004080300074ad40e02114802505124080303102a184505150812044100c002c46061070b4507195201480d181d600c8051a01c0010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 546788839 1250 546787589 546787597
    0x8010513091a092506030e070b0703090302031005041a090f06010801060819081914030c0d1802010e01080601090504091a0106050c06040b060a092c010c140a05 70
    0x9002854806140b041182148225840b40d1400c40c2600d80012510074655500c1c0320309200403c81e1100311005100480c02540f061460f00928021603800b15120440000164132084090b00803035541c6008004500e42041840c18601e81c0240900041c01d06a0b00e600d003020142042000c0c0c0b0a020340040e502503410441241000754104c100d41055a4805030b1030700803e618041c00c0d130b42d40074040d40c5a1050703442c40c80e030302c2449038028141e520300b411b00340c1c55404100300191240200901072600064000c820710165006010040e1155601c0d031140e65100c085070b0104540d0482041d03607102c00030140c1e030491031000b0742000a00b0424a107964000040740d0409143c0c01c03e60f4024982031315032042c0000c4804060240305000b0410300d031643c03180402e65003401010300340c00c00740e0300800005000800d01041590001d80c0072b44002002078850014800340d0b49540d204c19101c15511841d12000b0a19000c4010001c2d1280001c00c071030040c0c140000c0c0108460500040e14440014107007410520590841b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 546790089 1250 546788839 546788843
    0xf0f0c0f0d02093604021c060510080d0c02090703020c0303041101030b040902010e10021212040b010f051f0507020a091e060b0904020c100903020703030e090106080a0914010e0304091b0801051309 86
    0x7010487c00b07481d02c1c0005204c20344211103061960000810500c2c1d00080c495400396036621204010151542003000800e0001e100e1002c2580911082d480c1c104100091801a4424060f01c5c100c40303802ea000408440750100f0151181d4241805135015076041038054030482400c0e29000030003032800304113a180242c1b03030880c541c00c2040000c046150428881500b8003851141e5580c80103070b6070741d82224440303500380d02031180d000b10612483d90381000c1e414800c042000c1141041400c04204e03400150265015034030144449446c2e604c40190151060859200851410020803400c0d00f811103c885074019100c00364003c0384d001030301c0515580c0801582240250359002803011441c240f400a44904051008030302041d0500d041e603502d40740c520409410b03604103513148551596851028030240500302400e0b2452580e602810011181c03e0242203c9058104002c542c1c403450f10640300e08440702d15800a10310403481080305402d5030700110180c1100d4040385c10300d210340c0c40407881500412000c100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 546791339 1250 546790089 546790129
    0x6080706030603170f0a08041e081206013f060902120112030c120e030607020f0f01060302030705010309021302130e0f0f0f0c0f0d0209360402 63
    0x1500c164540c001c0d1080c0e920070b00c509076a4490014080016000e60700910b81501700501a84402c0c0e0702c00c1030740369485805902a4031103641d00d243d04000081841405440b862000240034a2107040240b007142c2140b0286018143c0260441d03a2230b420540b402400462420810000d104410040c5a60045c10b0842c8404020650340d0f910603900a50003603800c1c2e224000e03140000908650400392480c081a0180c80300c4035407071000c1c0d48512030a4ac00c41e195106000c07200c1000039868038200880e034400c0f0010380003041513400721201e8501d0500400070140180e81441c20504c0180c8012071030034102c5000b03081c007040c0383c40c1c1840000c003032200480501003910b10200d0200c24412000d2440002c031907040c1000c51940c0c40c1e10180341e205423401c9440640b40071034003010030541081c0e00e0f9400e52281180a5542c01e000b401803400d00143d0050561a117802e801050014192500e4042424040c5281441c1ca0803001c1003502d040740110860180f9030366004450006041d91150900c0b00705460807402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 546792589 1250 546791339 546791353
    0x20c030c010f09060b010c0309030803060d08071a010b1c110c0a06020304030f080603060723070507030203070f03050718060914070305010f0501020325050a0b090114060109050d03030608 82
    0x21560300400184005540c914100b503d0403d280d40a00c7d00c40740099010384d200410641103849101c243e82c0054045504107450741e4002001c200c40401404c0d200344200c600b0324902c0d85444084169200c103800568811500700108070307148440b5041001056402940854003041110440541d8058103070501240c2c051903004c0810400a0380c01140f08510984856601d0141007500b200c090702c040320103540640c0841e0100303802034003e4034041c0c41d80401000c58040400c3d0190a04c0c015048503604540d5940080380500843c5070a1003010042c18050784000b059602c1c603117400d55180020700c00d600c000154026001d2800701e60741c00c4880905403400f803c0c00042040c01d040f0b902c2d06000c4400200080c9003500100b50703008224401402c82e03005078011814207640c050154542c2086a110102d81194152160005042400120700030780c000d280180c418030700700314610300f9140c46151007120600c400f42000440c1e03030000c0303600c401c0e20015124060301051f10728041d80100303200d4002680510500e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 546793839 1250 546792589 546792611
    0x204180b0d0c240f0f0c0c180e0111090307121401060b0301050f010e030c040b040b040e060402011d0915030f070e1b0301030b060d290a060e130303020c030c01 70
    0x24030582c44007081c2095104aa00340484d668071400e04c0860008040070181d0468920034420042c019004002c214109035071541480403c5d40c0883d4181000e645480d07a03404440300a109010044e510b140740350b480c0480450001c0c0e2036202e5400350b01150980c415015040c040c5058034a03011040700c030020000e03135440e0059110140c109100305d80c41103811407030035a0594480c0500751400075000d002030444580440070400600446200a1b40040d0f889241550654440c000c101d8280748000140c481c60402d40001000c06100c0e50b080950307050358002c032945940b0340202c2d01d5880145001c40c1d82c120b80c0440000b0f410503990300040c0040c0c2c800d005000c52580440c80d0014000c100e150010200502083e15802c0d07a0b000904c0003a20003208140001c5450415980306240d03a4420400d10f40a1140c6161280c5020f081c41d4000381d1500352030080004c141c10324441c82c0090280e40c10000d8462a00a940b121111000c0800030f04058020841b070b400240c082040d504c0c00100d8130002e00c8607038649 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 546795089 1250 546793839 546793859
    0x60c21070209180a060f020706140406290607062307091710020c010209190e011706040611090a24080903180d1a0901050a0204180b0d0c 60
    0x1400d080e4407906049002c211200580c1207000801507000d00602200c103100e489280c014018046a50340081d003c11806001900600c9002c032081440400c0301f2180c101400c00e5411200c41903d2000c150306081f05480c040c15081041a4103600f04450f441c1d0b564159240c070304054129804101002c560440c48041c1000f501d0301e18a220f2000355036449102c41d941c2001d41040110558805055000100d900d00c00da5900e40003040c50800510000d450701c5210310214003042034110003082d2010365020700384034510400d0840c0f0700500840c100d21500d4842403c10b01e845080152000f008203540d000d592441813502400c2c0e0340150002800302000664600800840c0c0f4020807400c080c02c8c801d04039029450b0f004800550081110200035030410028445003906154244115503200a601080c038002408820342000c0106d4031014a1249003071000718182507900142008052b540180014071180341d012001320a06080c80c0c0c1e001c00c1c074803042000306210a40507200507241080055010401081c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 546796339 1250 546795089 546795097
    0x406090504050c040c051812060103150e010b010f080415050106090303110a0302070b030912040b07110409021c140a03020a0b01060914061c090c050a08011a060c21 72
    0x80054640000e000e004020071190000c200901080301845421920840c0964141f20038401910070324944804000507880c00c00d00746c1c01210801c0001e00c0c002800d03240c034040e1004150b9600300a0120114400010346003c410140c40e00420009100140500000b4034001c010792801c03003010441541c4807000240b050030b85010035070100b0719410342100c40780d0002034800b03c51034046e40030386041420103e02240a60001e0a0008188070b41200c2402e910318041c014030040861a07038041e81d40209151606000003117004035031145246c6015600580c071480800070035080d03507203048080010345103415041d03226003001100383c030310824200c181050b40004082c200746024840e80b16050baa00c4500b140c0c800c4450144081040e0865480c0c0c6190800ac809002e44031104030132900d012083c02003070030481d01000b070f043e40c40d0341d1090710802040c00d0200481001d8a1514004e016985440410024440c5c0400c11617009440001da4241450014454841e0a10041084e144070b882c0c007113440403150300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 546797589 1250 546796339 546796343
    0x9030d1b02120705030d0c0c060e010c1e140307020712050a020f120a02010302131e0302150901020327060403060b030d0f0f0806030c0a09021b010903050d0c020a020406090504 77
    0x30461903a010302d10410000e4034a050740c480c00651800300030000391005040c00e0400f00c8140300d6001950800902240548907940c0c44240002071072030b014020080080484074030800b0090501c209510080d94060141a100404404156529100c0b003004070318060b80d5921140c038501d04440c0d400108000404c551030f5442c0212085007200e0304a4042103402400c0c044c0d40c0d03455a0002e01503030010350090b00500002c010308400840c840e940c0301107051064082d12030326180302220450610440c90042d2090907990403802c90207081800c0280040e5a038804c070138040002d041c140d00c902c0c03140246d0000719004900050001516240d40740b8004d80078110701035103140300703000da03414420b01c0b1031207282c8032400c100c010ba179001c200f4482c00c1070980b40500c02400d01d54040c01400326010894850065442c0100b54071480144c2d944402500e0b076080c4130b9034419526140c0d05014000c40070a50001c2554214607030360f10f0006400034088801d0317150080c510030080d042400c2520000c0d60380d10350341c092403150f8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 546798839 1250 546797589 546797593
    0x807121e02120129071b0513020304140601080a02130e03160302010c0c02010806120109120c030206060a080d050d0b131a040903140f0904020c0601170a1a09030d1b02 73
    0x4203128115442003c00035120440303a070800c1c81600c0120b1030f8610354a48804d00380101144151704e85c1c01050070042310061554540740c00105010030440c007500100701a12507100035080c00d506082040c1c2c7c0791003007840068031610810600f2003030091590f008541c4c1c5d54100045030b588481c0910b40d140041d843c0b460580155290891560350315004120b2000000e5050351040104e90301d140401003c1509030700044030b991b40e100d444a00103440510700003c0c0c21f04070f0f1110388464190741703070091408000410550045414110400001d180010112100551420544e03140c080083c801001800d4100c80c19900c00440741d100005001194060403400da54074440b8000f4070a810144801d850303201070001e001030148003134000703900d10210241c240181510b83c1c1d945081144400036040e03800001e4040e0307158000303800400c541d0f808560314140c18070010b00507003214221f9480d1007183c2c0c81c01c544101c14844000000800001060040b2105d21042500820410340e900d0f802040010881c04602c0141c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 546800089 1250 546798839 546798869
    0x30a0c0203060a0207030e0915180105240a0509030307170a0f18180f050a05060f0312070303020d09051c120608071202150c0a02100807121e021201 65
    0x80700f014021140c003540c0646076010300d40c1c001401e220541400512811882c40440e4414245640b058402d5550780300010907522994103142c100450300207001e48820100003440c440105900805040e07860034080c50030042c0c4c454400c8800b01e410b505c12141d0040c1001101c001c0b0a0030b1321248800340040c420b0540c0c0d01c200034501d00c0e905981d10045022406035038201140e041001340e4000c140701501120480c0d0110301c1600d45d1400e80152102524000104c41d160340c100308103400d041e0b0f8900c002d103030b044008191070000c08144400b030f03224100002d8100f60700014141c08501d45a007220303503401e521108681d4610b01001c081d01c1c2811074100f0400005032010340c1d160b001c004034026901a68007920180202d545050240640141c0700f030b108a800074481e8544007a25441c00000e020201a81000f40214545c2c0307104106584480760985014010060284900350380c0c400c4180c1072401e210078002401c004001040d02c2c00310070b5003408047c002e00015540d411b40144032600c1d4100c810020b00c003100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 546801339 1250 546800089 546800101
    0x306140a08061303030608010c050408010b040b0a03060e010207170c1c02100911101101060e04230106180f0e03070512180d200f031c02030c030a0c020306 68
    0x841030a12401006900140100d416991008811440548682400900c540e035850340c6900f5605880d01d0f11010682c0481c0c1000042000c0c01130403011f0100f10740410a02d4042000141800f41c03034040540519961400807a800c1000d42c11600c4143e0090540440604d559076815103030760103d0100c00141c01100489500c4803241440100f2804c91034000e80360100502e842e04e0024403c1034401c3e035214480b4803010310151600704002c4200c40080d910802c000d24284201800d5500c15030000d100e0b202c0000400c800b04e442651041c030032820203a403400486555900040c05091141c110b04a41c46c183c01c40d1040c810b0060303000001c0a0f0200100f400070200c481030b07541d1240a2004060441c1d00f00c40113051000c8403240081c0259207400000c40406180348000c19080800e40e28100c0d10f07107074944109034800910100300030303240100701c07020b0210003015000720b5200c43d140c2448500c030300340f144c4501001078001e00039161420001d00440351180d074010402003111200c0d02041c1d0207030044e4808151 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 546802589 1250 546801339 546801349
    0x1602031c0b1e03031603051201060806010801080c06030c0d0f0507031e05130b04020a0305030a03060306110c1e0102040b03040c06030b03120316050c030705150c0c1b1906030614 78
    0x4011200401075402e100c07410329400e441c0742080b04100e04115003005082c024000c80d50340c8c030380030303200b540d03201086464403100140030303c64103800600c00e0340e01c03089000341030b0b03034a0714102c86e4410928000d49445290203114200a0200d9450005000e800d09042001c0e05e43d00d80d00155000b0f1040760203901941c0c092031400203c40782921818241104880d03180c000c503c040001a0300148068156980d00303549440325030954011220400020343c40303040c10004c2c1b003400e0050185030b00c040050303d441d0001e2601c0003943c40c00c084220302c48a03a1800c035001c0203440c080d03040d40c0003011000700c01c981c1c81c502450b09030040441402070300042898000440c440c1e0278001022031045001010440c0b658950017a0096184042560740080180410030100020740070f0001d07001203807148008140120744c4409489078000010515044841d040c490300410040014003228404080b0030b18901544210000c582d0312482c0440c1100c5450103424002007050f1306a01504c1250350942c0b110b8050100c84c02042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 546803839 1250 546802589 546802639
    0x8071404030b01030b0402030a02030f0a020f180f0a0209120f010501080604080f070f170a080903130603020f040504060b1207170106120f050135061602031c0b 70
    0x35107100b44090060001801c3c0d14107603a000360006080311002d000c41d600080c580405004d00707aa040d0008403d01d001c60400c1c00d0f08201540c0100c1d0000d0a4000c02c1110307031425200103001d1a0146c401c400450640c030a5541152405040074190301c2140f5200f2020310398610078002024100d40c40d1200000f821000451480d00841e0f00885243c68603a922204103690b070809401621074030003e02d180070010740d504510440030003040c0000740c6c9031168490003408d840c9004201e804140c00c100a034038564485901442c06440d5070341801a01d40d5042041560603005640240360090314101c00030600b01b1012001c0d1041c0b2a03030300c03208402580c400c1001c540c40c04410000d400682d6855006224407030045811664580c0d816100003101000c1080182c165072080c2d000f0b025000c00c9000b5100c0291500942d003000066200c03054007401c07600d1888503903c17a4000d04250b4101c00a048400f0003610900859091540d6440b00c94810382a40706514010402d1291a03407043c2011b028001608124000308 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 546805089 1250 546803839 546803843
    0x10507121205100f0e0c071403120f09010c03090b2a0f1b0109020d031d190f06021f0507050c06010f06030b030a0c18021303060c0e0607050a08090612070807140403 72
    0x10341440c000d0354800c230b07056104c001c0f02401c5d4002030000e81c030800e16680701c080c417540360103008444500f46100c05078211004170b0018001c05041110040201348100d60980c0c00890005040418152112410011200c0140d40d02c01134400000c49a102c1c00a0401401403464100c903c11180c98400c00300c1402c03030b072075508002c0d0845840d010b0310010900841d0300b20000244e00e0038800c03140c3d000100186800c00d03050302406034030403011004d018407056035188001420580c0000e141c4110040b112070682071124030840b84040e220400290a0340c4120161801d141e8104210740255841e000303020148030b014007541002910342a0703210183d203000240100e80d59001184146402c3c01d05012a110310030608840c0019074081041520503038008045000850044030002030f03618201d0b400500d12405444010f119100030700c2500040390000c00c1c00c070249076114042d6561165010040f8a0300e00421000304000034900003004246604510b01074480ea80ca0f42d154038251308002040f120b10301541c040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 546806339 1250 546805089 546805111
    0x2161a01060c0206030a140405010603051009031b0201020a080c1c05190f022406031002090a30030201091403040b090415032a05060405010507121205100f0e 69
    0x20b00541007000095800c04c02c0c804000c2018628403a0005104030283c4044405079034501c005c0042c050140b101c12031040c12034602b0f0020510644004005141804c400c10080880d00c1d10801168001c20000020540c00a1090740303c0500242d0700e030f250040b010051401080166008860030300c10011500e036480b40545850078030440a40c1100d20f02d400003085001d5210b0280b40d202070141c84500125602c2140b1030620851906109042c144800b00d0000c1101d140140100110f80c1d0b20360054000782d5600c0700c40440c0204403c41e03420800c0a941c620702c900c5800ea6022241810303819000308402034080c00c1000c2004030804442980ca1146116030a45100180074900303442c605500042d140d00003502045080717503100d0321005862800340e281103249a20549045940e003410f00341600007000111040d03802d051928001820900c01d20400a000102840c1c05500c2c007030003007940c040c120b241500100007900e0308802c680d0704400d80e80180c903402c0c100c0940000c0c1d15000b02200c1c61061004a007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 546807589 1250 546806339 546806357
    0x150406050108071a090a0e162705010f0c020a0e07021b010e040923160f08060a09020607060509030406120912230c07090b040e070b03180102161a0106 66
    0x14801c106600145c0f1010380c00020000002041000c8000e114095440007001e0741410300d20410160055501c4011a4240c55160b8a01001d003140060b0070707800c4540c01e0a01007101c0321039031012209180c02280082d403060700224042902c00180e01200e2007804c2507000c950480e281950040602c8008280b260b0000b011a000c0304014200351300403003040391280a0320f1920b82d42d00c000e205e00d00c50304000004003c5d4031070b41d00c0c200d180e03403c4c0000070001d102c00100d10303604604041c039142d00c1c0c0500070548495103071284001c40454485030122003119402003010421400d017102c0d042d44a41c014824440020320310800402114428403a441080d070340301c1090206003901e44401d4a500c45800b400040f155014014003280130322007401400070140207400343c0351050030404590104e41145034418003944c6042e030001c040d0b07030002400d08140d60702288002c0d22039840c904001c41645456919198a50000c40d51a081c2410107070011845031280b0302c1c01c0301003129074202e0311101000744124000514050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 546808839 1250 546807589 546807629
    0x912020d080d0603060e0c01140403030822050319080c12040f05150f0402131a0f0402040503030a02010b2b0303020f07020904050c0405011509060e03070815040605010807 75
    0x8010300c2c105410002c08569203582c0e0b00d4882c115000841141c01d641c0250403503071050369002009a1444880c00c03072560030103042d0b8074020030780300c8010f0030041c8a0302c1900c0703100c01c1000c1c058094510ba03540b01c4211b039034034035814903011341180f00e40c104407001c2000f210128040e4203000c010780d0004c500003c1580e801c1d90b210b03101c103007000704a0081504c09000e450700c0c5e01c0307011660f030407810f201c0c0e00510b214000904003807041c403400c0c404512041c1c0c1640e1614000481e012401082c0c62036031042124514640c05121380080e000f4402d9a0085506100000340100c52503010340150703000050859410980240c5403101400c1c0c07411101c01401110700c0141c0b0701000a0090f070103000003100d6403800ca4140581a0b002c0750180c0e03815202541d0a074054458074800e481c0c01d000d07241c0034264401c6601c00144c3c4245001d4090302c9140a000705100507894034103a151801c1120300010021001100c120864292380a03055590659060340c0d090301b40000821941800a0104201c44049070701a42c551044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 546810089 1250 546808839 546808853
    0x60203120c0d05010e010e010503061303180504020310090f0b0d080304080c01050711191e0201020109150e070b09090c160b09030319050105060313080c03030106020c010912020d 78
    0x1054041d10709014422280304840e5441154042c000c01741005a40354106190800c981d40141d1100c0d2182d4400010400610707a11003a0700744484d81030400d800340f002103001d01d42294000d9041560050310110400411800c01400141101c2401c00c0030400000660b41000030703075a070344465a81060b40c29040d00c0000d40100f00441c0c0c000e00880d50359003400310100c8950b094a9054442100007800400c0c0f84a00c040240180300d80507420040341090805150780307401c52001000c4446d19202e48449403d015039000b0340241042a0f44004000030b00401e1800c2c580040458a00e82d000038804c0c41c2000c940d03490003004036105203000800608141c2c0e6400b000c07404661140d002403210314080c48460380001c0012003400e028204800246482e85002129000c006d820382c80b50055490034000100010346400d4210b0b0f030008203100b2000010385260810003114451b07000c0c031544603c4000700001d8803070b50202c0c4da0b4480100c2603840c0c51403140d481030100d4458110001c060f50103030301400c020700001d920f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 546811339 1250 546810089 546810091
    0x1090501182d0e06100c050c090615030117060906010f0510050f0a0206180a020d2a061106100e15030c0a09051f030f08030a110301030303090302070b0406020312 71
    0x10700010b1010402c0c61100210360000c264004510074411500344a0949409452820120f965260030b0b4000c1115844071507442c800030416500444100300807907038075180c49400c508019020742d441c655951b510030070b08000c0c00744a0f1007401d060040e070b40030070007180c00818250b04841c203181c00404a9400c2c1340c104881020030020320818441e0800c086d00d0010510b0b400b4201d5494150054101e41c500082080b44016071a01114886d400c00d01003540160303503054241d03000070340004e028802030000700c0c9480074603100c0301e00f002d403c40f0060200042080c0e01c0501d001540d1601e0b13003550150b07211750803050001e614500a0080036030080c0005000d0521000c040455581d008080b10050042400401c40c60022500045d85c2c903500c0d0010011200e41c1607869114500016200303007504d51840c1c80e2000445810300004261a10000110fa0840b111360003a10345507a00d012641e0350395070b4926020300109032407801103000d4018010001042c101200c240da0480d140c90300610310b4140001a58000d40358 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 546812589 1250 546811339 546811379
    0xd051f030b010f0e091e0304121a16020a03050310050a0312030f020a08072d0302071e12080432010f0e030f07050709060b0c06330f130b0109050118 65
    0x10080c800002d400007009c03240b940d00c9008000555501d5040d04200543d0000200148000100c0140860303080c1d90000d2110728040c0c140c80d002d51242c41c0c240c80030506905951009911200c0d020022090259000c202e070802d04103602d0401c20201c0522079001640039004440340410740480000d040030b4041c40c0c100381c107151306e07614062203407120303220114908120b0b80e0880c0c00640c1c045075050401042003172149501c0c00000c01c1205221460ba260807644080301c802d0810020104081010011383c200008017013201444441d982600d07103029330b40040000c1c0e200074010b608040301544080600d120f2480c80002500c09107190520801c901e200d0b6034082d0b9000c40ea14416400c000400345418407e02d8003030042d00c2049603840306541242c88c5012400f500d4901c040c0c440709900700c04807a00440c03076a0514080140681e20154500c0002c109040740f03201c036500056610030303884030a80c0aa00014445a00740c880356001c9880301c00449070b0801c800307415040b50601010501540f0104941058058 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 546813839 1250 546812589 546812593
    0xc04050903130f050f01031506110312070c2102060105090601170903030a110a021906060302031605031c0e0f03120c0d0201110703050d051f030b010f0e091e 69
    0x302c00e40034006040314407070303110051000708a8800d0243d450030800c501c0c0260403d18043c42150600c1010100c1c50a60b4402e40c02880030401c20072040c280d083c416a20003041422a00c101c80c0707080c6101400110f84210708886400c0006181c4c140d8081c0000c550807000107950040890344e080c08140006840090035040c10322586100c040c07083c11503a20700317621030080c00004d0f5881c6d0074035018907000e82e01044010881140240860700b5410b84c0041c00030002c500b000081c0c1c11503d50340c10180000c0c589a040a905401840c816080e50700c8406001c0e021168160220354031041ca0180d031a18054111451400251305001c10803c0c614180842200915004003981d110440c1e0440310301e40350b030110071408055040108041403a80d021f00c00c4101c242401640c040c9081d090781d600030400d1040b090301c40409603480c0c000ca0700014040001c00d0f55510070f42c01100038140c8a04001e014481c0034410041d111180728004105c2e40c2004800ca8060072508000f000100301c007543c18079005403000b00d01c840c0c42c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 546815089 1250 546813839 546813847
    0x90c0f0313140d1d030307050a0f03030f020a0302030615040803040902030c1306180e1b0304060f0204230f091303140f070219030c1401091208041d04050c04050903 72
    0x305001c3c07010354000c0c41540c5450100c1c1e074080345100c0f00301d802c40e09024404d410500010020400c046801c9294582c001700112610030fa503c0c0c25001400300417400c40c0c0c42c2d403001c10418041070b0503034000e60040c001140c803182c9042ea040c6074002c1c1c2c1e21403402503090982052008018a05081d0042c42e000680b11303c26030f0820031051017480c60540c09030310a00014038048a00c1c07402c0610122aa006000c51606c1001140b41c880752020524000440e0392040c4440080001c0c20f003c1ca130360022607402017072034056641d10b943c2c0001841408220f121042401c210b1592141c0902e40703003201d010300c0741001d45800556554014130a60410003208194240185544030f101da0101d0302c00244461103202e4101c1d9100e1046005100c40c0070b10303140e4041a4100e007250705002040c00c410300941125500d03004600b1004d100c800407a007070701d6698401f01031850b102c1c20010401c07810501400c191400c44103020000889200d030b800f400740f0150360180654121000603640c6042c641c00c8950310014000c02c82e4030b4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 546816339 1250 546815089 546815123
    0x11e1205010f0507030e060916360b12030403120c0302190302031b0f0c060715110301030c06020c0d11010c0c0e010303020c030d0e0d081209010b030606041a12070f0311090c0f0313 79
    0x6011303030f40750141103c03a60b182f06152b058070b4201817620441d007813032004506041c19a40c468208007000701005060200408803401013502c200301414507601903d040c015021000d1501a60300c0c0c004007061080b042d44110b10041e42800041c00300548108000288203050040d400d0124603031000d001a00c1c21010404249510b03800742c001d070790824030020f840e190f403585141042c800200c400c1e04010304640201c00030b14400e0341d86a001640803508505c42c00c2c061192223005841c41001d00700300a0420090300c00c00a00004800d20a40c105e034025001d81c1c25401c445e900305510b45041e500c92001040f2403101c04c0010303040040c551000d40384500c4400d483c0c030b03c00c20320107020114116220303461a0345403403014800382002c3c881c0940113102541c090202064078290b00e0a082111100c560142091000e50b5040501c1007010700d00402c0c8401034103c0440e181e003400080300c10521161030082d449180450907510b1384404a0ba00c6845510038941103031503400c0420083c0007a07440940321030074803140b034041c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 546817589 1250 546816339 546816419
    0x18060c0302071a340212090f010e0f0a061206050316030311100227010f17090a0605130507050a0501080f0a09050d021005011e1205010f0507030e060916 67
    0x403542c8151401250700c11300c010000307141046003403041c11301c1001031020502549600d040308401c20002d00b41020000c0359440440c0c1c6c00b0314203038611680100e010500140054000002d45408000b03c0020301ca816150380c1416031b038005500f48440d40101c4107400f040841d100c1d0401c2c00070781d00d118081d1000d500650510000381d810510a04014032595100840781034140b441075040d121007800d0100c000804114041c1c0b41031080745104403007144080008102d542c0038000d0401096105904105904001c21503401003070031210201da41e031140346404a541d01e0171102c01c0080f13500c140d64418a5039214610303035400b1400a8010f0a0b1581c40781c00d80400600207200c0304080302896402010740c04490134481d415070388181e214140a002c44094490341448c40c3c0c041009543c2c0c0c04818480c0041a454003c0c01001c2007219542014905800d1203c035035072641003000e60b82100411503e041d1504d2040c0e0341c03106c5003409a09440003401d003040000b42002c1c0c04101000040540c0401c10b100d003244420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 546818839 1250 546817589 546817651
    0x1209050619090f150507030506060a110f1e0d020613060c020a0c0603020a021504080703080403210902090606132102060f0301080712260d18060c0302071a 68
    0x8481c4035004624031810051031007426841b041d640307010302207414404085031030b074826004c20030f04210000102c40c0031418108540300306003074020100d40c00142940910710443da0840644810f0340600d410f025041480010098040d00070018500c111700c411760303504bc0c01001440066810350041045c520081204880e034000208000e0300d000d6510181e03408001d00f400e50800080020310441005d01c800b18039144296440b00760b05007007441080c0c070b1794141500e4022482c4120b0f1482031210714003a911069581045282d0b40c401c1e518100162643c03020040309008a1001392032071a540003080112081d04c01000d01e110b20b403003820030002c58050700451b515511042e2640a52003001004000b0341c0020840300004018554210205d000b040c0c1e40c0303241010209440382e42c110700c681e807028420305004044518602c1c2900003009440810b010008a08420b03100035070300146482d11083c1c58074064000c80360441e40c0000042280031500000d0040880082d0075110000d004c02606c800d0110103d541b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 546820089 1250 546818839 546818843
    0x31707020a0803070b0f0112030509060703031515091203051617160b07050406050a0e010e0d060c0e060f040504111317101e0513060c050a1209050619090f 68
    0x5000e14142c441c11800c1b02d0107a000210308802c5103001e10121754804240d48011700100e0740c41b5511507260408034081c0c548440303400d807590841d102c0050903410404417060880ca9079115680001d9550b40714004031220039102070049a8100320032070019520340c00c984401840b606150b40a09000a007881c2260010b04501106013402c820364000c2c0111400915031203c500e1501038905410000010901c1c0205d0106c7e40610802808040560b070040d400c4402040018100524507020760403c030010307107e00701c2e92101181c2c0b40301403820241840400c8440c450344141045d882d091038034003400000c0c0a1032161100200080c0000843c3e4150103039040010a2090302c01740b000b4220f00016401c1c82190540b0b090841d00e8203031820306140f03401000d02c43d0078001e8000007500da075410b16442c0890b0340c0041c1c010100e130f00e4040190242070300500a0100030b5450f58074074404004e183c41e44001c0b28200e40000c0c1c45940140000b401102a141d000d0031100c030345001c0400e070040d990b66000b0603190f6003841 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 546821339 1250 546820089 546820103
    0x50108061005061b03160c0902161202070515070605061212091503090319050a0801170a06060303030501061b02030c2b0c140f091b040b1803010e07031707020a080307 73
    0x1b0b07070b42405113000703001000e0590a01c086240c40d003410808030910501a2000700134070303031400d4480c80c5a40240803000041501a00c505910141035213030301003541c800c5034102c55251034400454180e0410f020501c94814040008003109441c0300059072242c0c019012047c0d01144040b07200c00c1e200500000395000700c3da000020342d142c1d07000d100d060301c0821189807030604020090256550040e8803452041c11204028040c103545140e20040700d023800320040029013a40e0400303400104050381544018102c403c1c590350255039a4440604000e140e070f904801960551240b90000d0044c0f41031070301030000f4000314001c4412411344149202c9804420042030304c510720000020020504125488055800220ac80510050000740099100000506a030381d160b09105020154140040102ca02410103120026102c2e10303a260446262030031003680c1070295090888000e804a030004140301034035804a011420f40d81198140003580c0c2005105a92050f103950300000c2c901d400313100902c191401108 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 546822589 1250 546821339 546821377
    0x90c0316060f08041e03090503010c020d021c020318190303090603050615072607060b13020c0d0302090102010609050406050402210d1b0b0709060201050108061005061b03 75
    0x7a001d00b05415990140701800102010080019038403601000482031010842c448001c0c3e80c14101e0f056580f580115405602e0244010f0360310703030002480c0d40001101c0c0c0c201d4004062101503541003000040001c030142c0e106208600b00540c0010800c02d0200020340342501d1036100c040b480400c0c00350350740b007034011441c241402d000e41c95140c042d0710f9010500b80c07541c52401e5042502c0c84017a01c0b8120029103400500a502d4403d946549620140644480c001548038009418407000170300e0707007411580c46001548a036809080280c002d8070551084038000d00003141d03d045c1c00780d0183d44103d0310207045560320200411142c016129090041d17004290028280c902407050041000021420030b500071200040b69008070070018003002007410511308090540c00380030030900400402c15000701503100e004c04006603658006c40d1101100c10030b500a000d107980e84c2032626260041992580700052001c00240001d0503c50010401c200580e03c81152056420b01071034210b403c10880030300b951602007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 546823839 1250 546822589 546822599
    0x20d0e070303051306020106031709010210290d0507050904030c05340e01180b09040803040b070507050606061b1605040c0203030603072d260d09030b090c0316 70
    0x1001c1c40170302018002046114250744800d81c00d00c9202c6c8040e14003410021b0f071901164428401842c09882c80c6000b40a402e40e40141050a40c08a013000c0420070003418000e1008c0c0741c2254121001c5801a010707166190419080c0045201c00500550900418024120000c0c0c000c11204619030b41000307624008440b02c0090701c5003c44840440d200f0b80603404410705c42e816007503e44a04541d0b0144c0c140484440c036a0444016240c01d03c4002d90241c1214100000d000c042d40045208070706c00c0c280b0751740c80d94a9880603116800b070242c0140031a131000d0005911400c1000c01008442c9201c0a000d0703036100190011071504003080c0159520500904042099040c540102840604580051411441d112001c82e0350b60701d840c070504405070000c030300c14a161280e4034000340c0300c0c00c3c0c0313501c0710001da07a120108000d456403c1c44814070b0202a00310b1505480d640400d10860885013555810b01c114a1503c0c0c0510601014152200743c2c0900c042e030360510394041000b02c034114005005000014a02 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 546825089 1250 546823839 546823867
    0x12080702011b0f0b0f0402150c010e150702190c0e13140c100203040819020d08030112150605010804110102030c07080f0f010b01050a03091a0a0b03100c0210020d0e07030305 76
    0x40e0402c02c1718090752007030100695a00318100082120304282da9200d003155011140500180e9541e44c2c040e0048140302202001e41c0c00505c2e00c40d290325001c0360f41c5420103c100d41460007809401401040300080d091204c45c05036865560001180140c840c807242140c0c40d884980003692000b00e200f42d008040350110750a1100aa02c00f005860020f90704040c07074201c242d521942e0380034915003010702c1811410300315074401c950f00c03a2554000408989a68481c0c002140824200b4011f4542c102d080c019800c0002a030300a0300181c40c8103035644500c2d070700c2c0c2d580c8490051140c480c0c1030f4154082844131b5002c40c2030411140d40240b1610740189031203908800000c2c180350b840b503010ad500e030b4103112100d810359030400c00700e92041c485464001004203860900303044180c0c0c0302030340e100c900c503000c0244030402119410410030074074110141c480071742c0311181c09801c5a040c0c1c800344000da0455201181c14180e15401340c2803420b08040c2c08556415481c0226062190303581044010520201d4030354a102c8070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 546826339 1250 546825089 546825091
    0xf01050603011b03050402031203070f0e04150e06040e10020403200a1815060306060f020607020c0d170a26040f14030903010501081e0712080702011b0f0b 68
    0x200350000c12000780a403610a00c3e0200f00420390302410b449501080454808119105000d012210041e0310b070f0038000002810030210110400005101003202c86031460b0900c9000d04480b010000c1d80150342c541100d40381d0040d0000d1405031b229543d2a8480a414018020151000310798000142e90b45c2c19031600c603100300701c02c1c2124440040e070030300a000e275921007101c41c20949080704002c00c26241002540b10292100c0a0101c0400a02450010b042a01030300304030207031101c41d00c0d0b010520403400f104a907200760881d0b101c80142c0c04001c6c02d10950414068480c0303640d0090b40d04200d961201e240340384469100b10103000016040c2c504050400c1481c8000d04003003602148407031003a0400391980c0b81d04070180800036104403408100c4242c03020007001111020000903001748070643c0e55424298590004680c00200ca2540d108140322100011a15101b07a407111941444c3e15005a1607001890300301020403418840c40340400c0b0000c4102d0b032418162503100303241410701414140f80040c48408 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 546827589 1250 546826339 546826351
    0x9030106091509020705101a15130b0306010c0204091209050d030507150e06070c0c09020c07091a061602130b1f090b160c06140409150906080f0105 65
    0x8038050260111808002c40c241c01c98521490140c1c840d4143e09009092190b10604420402e02c1d1083c40581914540c8800024450859811010000d080d0303001440b403003180c01240c00c0354040c14090001500403805950000010700d440c64194250741c0c0407800701c0b44581400d8910802c001541d0220550001307078400a4102075525008110046e50003a02c1c90040c400d00030980d4500f101100c0c6948001d9100000e002d0b1007504a8641d8100b00d8000b41400040d0401961945070805003c82e5440c1580212903804006000030181e4515011081008054100c0800c550400e002241780450b42d0382c401401f407a030880d004075440c85a151041044503696908042042410400e1180d0942c1c0c41c40d0340031184d54a07048884d00320040110084400f5002908101c0d090388010910200d5100800c0c2441a0544070710001d41030603480c0c8000350340c80d4920140d5040402c1c4100030a1004e610b51303030801c5110040c4d0480110045480b054000241c0300d60343c004070583d6006ca40342e030150b01d45c24000d803a0000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 546828839 1250 546827589 546827591
    0xa0e0a0f120f020f1323070c02090a020705070e1801050c041e030b0114031504020609010518060f09010210090b1f030605040c23061206061e0903010609 67
    0x241c80d0448107100341071500c0d0040d00800140640700d00350b40321010441c42a0000a041c407000c40160600c0c0c00042c000e442c05802c801c911034043d80640324088100341d0241d0381c95142d000040700698200030b0115001058032207800e0302070114100041081004e00080d0502102d40c0c0e5140c5040c84c1d02c0316240600035440d030a568144414004e8412400080300c040d20311507186c003010500710568060783c0e025540d0005060a20354070000400c1c02c4013001d46c0d44401c20841c1585c103200500e45800000c0f540a940203135124408200c080c11540c012001802e00a074801022b01d000032840c80016495044684c0341e5214800000c0c15181e11b40e4180a040d4510003849410840242e458031606003500e0028141c6503030200c540082243c061404a00900450f8884000d008510305450841440c0903144250b042c6802d011901c00c1e5444500000311551f648064031050919080c0d0021400400c4054000c60f0071520800c4411790100040880e512204150b04000742d8944812080c1400c6405547c00f0340995 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 546830089 1250 546828839 546828869
    0x203100303080705040f170c100207091406060a030c0903120c03080901021207051308062d01180903110303090a0c05190302040b010212030f0405060112020310200a0e0a 74
    0xc03246c41e803060700a490282c0e480c200c0c29088003c0e407600d40f0780380d049082d6102440c11010801076900040b020f0548a107a0820320003402400710300b6200585c10b98022b80c0c0040b084c482d48210724071070341c00000c80c01c207a86030240c00142d5030389aa0f2080c4105d07038141c0f800180505510401d05420282140d0000400c81c000c61512035412280d40c0c08080c050132210401c41c0c00690032401c020702c42d986501624111069030600d0409450720300e5001c4c903011081d008400990700140e500441620894100d0300d0114070031007414880781c11a40201709610f070403000c1c001e03031100d55200d00200b0070146208004620080106c440607040030180502c45070301c00b51007200c00a000203144111800054200da5040c0c401091040907580180e04013400503500000c0701d100442082880010344030141d0240d4003031820b80d0466600c4041401010301503050103074041c2c2c0100c500c1340180d515a80814bc80b007140300710842c1314081d202c8001d502c03580b08000c0c82002500060760b42c40145007500e1481d0080c084028080c4030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 546831339 1250 546830089 546830099
    0xf0e010c02010e280e06030d080906040f02060f0309030a0206150109030320010e030d0b030307030c081308060a0905241810150e0a091709060904020310030308070504 73
    0x81c0920002d890b401402c2103108601403501300792168070300d040b40000c06411180c845c04503202d103500848410b4401e2281c501202c51090150100034000c00300840548556600c0d9200c6810310205c5802c104c1e0002800c214148030000304602450190314000080c50f80c0c0c0f403070503400915001000d010b50740c007509099444402680c012826400b00c951500f0904604031180305d800c2070030b021401201b501ca5003844082c1d905820003000a04000c07110308820080b505803403040c940c2e40c0c011010f0080101310402d0402000c40e036604003800c44c02d4034a42d03104407000e4454130110709201059488400c416218a480400c001c4240a03060307450b0126244500d015180790002800040e000e01106020f03a60703446250700002042c40031598a100c003450a1141003a80682071180920078410140503003500d401280900680d0700690b105c1a400c84e4400b450355095194424156204151542c2d00040c204a1610252107071700145100e8201383e0740d0a01c08902d14100a080c4106c0100358504100c401c0005001e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 546832589 1250 546831339 546831347
    0x2070501030f0f060b1b160614130308040f1202090a1d0a0b0709080a0c05150702090115140307050301060c020f04020c010501060f360f060f0e010c0201 67
    0x125682440c021038000d0403018100014140f0300795089407542400c6000c6005680c5a00410b40c003200b6012030400c0e42d800c8610540c45010001d40c041c076051542c04104003461103030844244c04901040c40c1b515120403801c680541d5030b0b69a20841c0c0c3d189001c90108155265407503c84010300c00c0c102c100901d20256400902041001803020420b256195007025145071100400c0080e00c6035002280d852019900b4810b09c05541101c1c294001000c0c0d039800b00e840c070300c0840e80e09081d907881020211044e04010400440c5050171004900d00c2c1c100748004805aa10f03403126900034109039000404404113003800415407909004000903240c2c0410600140036882400c59046074543d1510408482a0b480043c00c100c0d41841c20b81e9000d8000715000c00184419801981201c2894441c1642c0e0040014190f03a4865003900e0440710255442d020201295081140702c0c080038080700f840c4440762251003915604915801140025185030300302e1220325005000880f0703221003400c00991b00001a40024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 546833839 1250 546832589 546832603
    0xf0f0d02090907030f2f060a032f07050105090c010903060f1b032c030d020c120715050109060e010605160503041d010b07030203040e1018020307030e070602 69
    0x90066006000042c81c2950074011070002e980c1c46440109240418140640c42e440014018505540518880f41d00d0900c0c6000080d00c03481c1c050062800d018000001b540104080c004007445905030398a02040040d480c1d2400e201c0c078144021580e00da42a50520900b10f560060a0810a900500c045100f5a800170060011290310500104180e10541d254801820781d0050380184d010380482e0050165405402c009034411402002d4407100700001c022031445003a10a600380260030410089402c0038181d001410140b141c3c2d02160a24403046a5901c0290320400b4155424010040207a190b01d01d0303809040d0042616440600c1003d0400201c0c42c5000e0040c407841382480380020318000d02141c480307440c04007681c0100a07a51103d5541c14041c030030030014487c00c0300c0c0742c4108001144896944d810b45040c10b802d44d0040d410642002640c42d880080070740791002c505001c0d00c1c000340f4007504006090115012f00b80158076030a20540c061300340d802130100119035800400003405619800a064 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 546835089 1250 546833839 546833843
    0x20406050714030d0903030209190e060d03031401240c0507060f03090c03050c01020f03030c03041b0312030b0a17060406020310050909011a030601030309062115050f0f0d 75
    0xb46607016031490200e8654411124000c4409040030072800c107258059002d42611142501c02c1c440903c000d070b8070315411198a004400c801031014002c114181007141c51a18058400e0400083c064444a0050b50440c02648074072502c035246040410a601180d5800820308018202044032400d2540c1d03103521245a401803001700300e00d03408034a002e60720a400000b60741d60080064414141c0324100b960311950741212442c05882010741407001410000101e0744100140c20050b41140c07211f684030100315024181c80403200310041e80120104501c5444018800e149403400aa030074154014040508a1071707220505400a91032080c06030000418095801a400340c4010b07520743e00c1160f00c0d040d0304031a0b00482e401040c0f0000304100c1c4941584010740304010200240d2540b00404101966405c0034000200000d191b5841007040502a00e910020b00c0c640100d415004070a0300644002c481c150101d03299100019038040081e030400b0285c070040c580d010340d600d0380d41709000c102207504101c00d9000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 546836339 1250 546835089 546835103
    0x150c030c0711040f0903080c0a09030609051507050a030605010c020d03080601051c02120f01030206071e14011a01090f05010c1b06080a0f051b13030c060c14010204060507 75
    0x188104410140c03442103044008108010140110710444005c0a20020860100e42c07004040740c892070010040e204c44034841d40e01c600c0d001e425640c0e60406000b4047d400c41d0544aa0b8002c500b4205d6045400c40c880c003240e5645940314200450000d060301c0a9901440c1404011008100503071140c3c001000d400d501800d020350180c460900407550382c4185880c8a121400c80d20b22411003c400d82c0051400b404521402581d9860380c0340c00c841100340c01e100095000000f0014540000d0852032080301c0c61480c1e01c0e00c400b9202d130a031509410200f17001c08441c2965500c07a07003084c15800c0180381080141080c13a04811548c146280c44146400c580140741c18406250701c4401044080c000d44815102d4100071441c106030f440304060710f0780005560f1210f030f95080c0a04082c502041d4840c0900c21444201c50152030a034902d015500d44e80035032542a480803881d040440400c0900b01410010b0515070748480ea1032029003408035042180d00030f4401c0b240d00402c810800d9507400b0382a940c1d0745811500c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 546837589 1250 546836339 546836347
    0x50702100f02070302030f07030605060f1c0507030204090c0303120b030615030a050d020f06070f02210d09050d02010f06140906010c051b12030901080406050606040509011403150c030c 81
    0x8000c2e45040b060ba44000e526114000c2c001014001c04200c1404481c8118002d12058407034500300300c5002010002c85821901e4000c0c0d03c940380201003040a2400e00640640c2c1e03901c1d480c0c1c0c01240c01d41d01030601c1030b03400f41c03c0b0302c60400070150301980d040350440818508009140001c0002031f1102c402030021031a040b0030b01c3d5800460355040c000a01c0361940a41125441035030b9000194898400341c0006a241c020303100000c018900071580c480051200364060210070108003002000440b848032140741c04002488000c003424164402d601c005405000201860b4602c01e43c001d094500340b0f81c1c02640341d42044000c015440e9400104d9203420b03001c84030080e940e543c4900480c1d82070719158026010f0b22903119080c880c58010b00440310301040546148448809403003c00317659200300d9600070b0005410303600160110b9050380c80941c010300c00030080d52406540b0400201881d500b030704500c41d040e0003100c90740c240740703810404e100020710b8042056602e03240c005902d0600e400018001d20a40740001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 546838839 1250 546837589 546837617
    0x81302011d0411162a15050c03070606180e030405040c02030f0a080108060f010303020c01030902040b1806090f0405030301031b0e1f0b0906250602040e041205070210 73
    0xa0807012840743c43c11203050f1614601c040720b880e00c1ca148103040c1c0d0300c04461600040d94407180c915440101c1d01c0d41d1001da003014503201002008402c52004007040110038000e18200300011300c0140081805070300041a5a418805203903000e91011500c01c04181c80c000000c080000c1c00300a0700e01f21002280e000a2004050302d09900b180300b4041d241026100000d4404c80c5241c0009406058880031000c0b240c3da07941b040d00291300000d0030b00020703000da40164241d504662203501b120050b2071015001080040305c000100300244000e9110301050340b0403404021550600d5030110340e001307a070383c683c21003141007603152151240300600001d0140c03405122248940c51547e04a000144100b10000c20381c0d06e4407460005440d0406007110f812074000302c40025540038940161204050001c0000d864010003130300e80c0c1003551100b1040c4071207080d50360138040420300503c0500010090302c622030700720b8030305441d085480d14180840c0805010b07051041c000983c42d07e09107a40d6404a41c03c040301100e4070700c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 546840089 1250 546838839 546838841
    0x1050307170106120f030306050d0206070f030e091008120f0f03040602120112021c050d050a180602061f0e010e06220b0102070f0326120106030c081302011d04 70
    0x16400c0f003141c2004200900d130402145c1800c090740740340640d03002c101c41c0d82c41c0d8081121980c0f010f88065070100c0c0510062001c20a0043c4210840d4400c0c00c1c56800206a5004076003240340407110b4448000c4192020800d41c8402d1200a0316820705120342803a1042007048148240030b00c2080020301c24001c070004040081c4d0340d040750b000c031443c816140565a076958104449440e1288100e00400171115441e00020820b202c10b600300d58898050800001c0752901119940c01414101c0c3c10005030104050000725001c4488000d40025800b5112a10b08202139500c42c41450580701c580d43e11605080155000031300d11181900c0c00505255180d85443d00064204c01e401816402041482400014015029031205a1100302a02030301d0341c4036603a8120001c0b640d802d110141c44104058840c00b41d02600890f03c1d00785004800d0300c2c5052080c04200b19a03116401d0f0018000310340d81d62141191940c001d1482030f4040c14143c0084000491a800281080074004e12450060854100018140d0311 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 546841339 1250 546840089 546840101
    0x19050403060e010615170609090a021c0b071403060d02010921031d09040813081f140108100e100908030a05060108011a070f021c0303060503010203010503071701 71
    0x5005120400119102c2c80c000c14062281042c1d408035070765500e600c503010704191680c81c0c0311510041c0540d9290424004081030007840020305020b180390080059541d0f40c0c40d1008071010080d403040240040c60089040c05000c1d0000c4140600703841c18030304032201082100e520090580b02000c2d4a1610b01c0140d85002c0d20b500490354808102c3c0d183c01107034264051059056009035100b100005400320700306c4100d54420087e80d040898000040c02007086000101020440381102d216801c0d40c401900c5d0404291380031800c1040940d1000d1080d903c49401480e491400510200c01194074004034180d60704604424642c0082e290419980d80701e0301884520328000100c030f01405250ba2030300d07010072260302c200d8081017007900e82000709596512a40559050745d0307030503255800d580400661a11260043c0404031180c440001d40b1000585465a03040d50781c500222006813020500d07e40a02550503a0700428001d81c07050004001c503690000f807401c11188032100c85110785024401c081d0240071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 546842589 1250 546841339 546841343
    0x6040f0c170319030b060d050618130b090114040308191802010207090c02030307110712030e18040201051b070801020304030f021b150306012105270319050403 70
    0x907460340d5400d058101100070700700d80c05621510040d08a414205904603451045000e40015092040c0e1104420741da100700e404c5200208400760b050904c41d81c0f5441410b0403100004040304070800d10040100310380400341c000fa07171003009000b0141017800c03034401800c009001030104074030080841c65000500c000c0e012904030402003800040070504034140502c6001038101d00501c2180d0340050f64050a00c640505a041580554559158510f00300c580c00f80460014060f170040400006501440340c091142c014030940710b41615100d0381c0200100240b8880d03030451707400282c908000050fa40038007241c400c5403140000c01020780d80c10351403d10303216980c0c100b0030b415807000090005041c1c200251242d6444079900700c41c100c810000406403040034060381d0035000914a080a4078441300c020255038004c0061401c00b51242c60445060508682004107a8202d541c0350240034091420708509010490305501e40106002c05004141d501c1c4900c4000000494045482c251814402e50840300156 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 546843839 1250 546842589 546842609
    0x2031b18030f0f0717060115050c070305060703050a020c1e0f120c0105250507030e04090b010f0803071709030a0212150105101205060609060d0212130506040f0c 71
    0x202c66045019035429080c51000103904c221200020b01120380a00e003214008840090003c0e07034030305400300f880301c488085030b034091000030302500b4801001009408000e60007400284054140800e000d0101d80001e410200070303600400000001e02307800144022041e440401c00d80a1180a0740720a0603d289450400d285000b05181c003c10b03c20b144002e420f110040340c00070040390315031220b003980c8c030b50200407850aa6129032a4800b240c0d802203018220017030003070800003182c41a40000a00715409200111034000e940b500602c003001150030400c01070030414005501d050b1503501c41c1300f07998442c404c0c4120710120001c2c0d2404c403900c0911882d207145501411200340c4650700c648080d00d07602404074901c1c041c4c0f142c800014442c9800e010b01440340701603403200c040c00c010030075480e001b401e40100b48981252003003000c1c801c50b480d1080244a5480742a600680f02d41d84110f41c0404550050240010b40030034840c513401182020484640040c0c1c000340d98001c13003809150900e81c82e1007990000c2c810f1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 546845089 1250 546843839 546843853
    0xc0b0703080406050604020c1207021503071e030501050105121812180d1203053c090601050105030c0a020703021801091508031c021b0309010206010902031b1803 71
    0x141c120001e2401244280d03c2884940d45e2001071008038080c08241c00810380c00094003014840a410040241d50700107030170314052440d8661117080130344c0182c1d010b40006402110001000504030302d11008807080e0b14080c01154900b000081482c095041140034243c2608003050b8020f100d007030301da20540800b5055440555000381781c0303460f036040b11600341b0150480b00d005101c6840d1100c0e50000040d4011000d01404851480440040000418108101c1002d41d10000300324009804100103a8024016040c000040c0070b07000c030a00c401402180305a400240144203980e084010f481e0702481e000c0b4030300c1e15076100d01e100b24644125588003941044c82403014450704141c1c5245141a0380d041c0d4000c1c8002c002d0209800c25440c1d86100c1c00074a0b0f0014050044403084103070814200211280c07000d41420070700c002415800c0081070807121680c4c4006003d030415601400300500611840008604502c0c1418000f06000e4040004c0148180c00295841c00c42880c0c00d5410a070207005021a540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 546846339 1250 546845089 546845093
    0x30a051605011106070f0c0305130f0513050f04020f180f01150c0f0b070215161b031d0105070b19051b07140708100c2a0b040c0b07 58
    0xa00c0c549000300c41c0041d00140c080000b20b8000a106030041880b550703442040c0081e44011100e41244440480400404014a01143d2900c03400080a40442c00000308014503003400c003d010704041081c0c0c441e490400b010010342c9090001c445a00a40503608017440302d0100300050102000c0941413000c0059031824002404200d40285040e1862041e0400c28246c40c800140c0c1c0381c1100002c005c01020201045400203590030458682010240c0121003840b95004d511031584442151101c3d4001001c021a0728a594003400203204d8031056801511201003540300144212410500101c10b174420000d1000c9a034400c2081340c14840d0400201000d60600300c09648280340c10342e02c0042c0880c01e00d0040381d090310070403900c80c0f44428038040c4940761807031a944852401c19107148581c59405070103c0055070010503c0501e007400941c2d44000b0b010903c0f0741c00602200410540122041030f8200003411002c40305003c003c046030000c04000031030b07540c0d203481802c0c4500f507040303501c0c2080c1c04550401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 546847589 1250 546846339 546846373
    0x2031e0a14060114062b0209040e25380301060e030705040507090509090c100f03050708041a060f120a11090609010303050307020c09270129030a05 65
    0x41610b00325085490044942003c0000b0b600500d080d424900121200c0020b044586418400c1c00302d000010141c1010141000103084034500c520180c4980c2203032f12410610b003500c5002d0301181c002180d80310300b95802c0c404052051050320004549558000c42902d0080c0b181494501000c085d0418170b42d035031340c2c440100420010041103440d029110b01003000c229403500d030213098450191035699400b050318103c10000380f1000981405603902404282c1b00c20f64480001022422907962a0203110b1442c1080080480700c0013080d0f9030030440030300d041c80005018154804621111003140ca8000e40301c0000042103080d40b07560066201d081c0d4402ba0500d01c1010440c800f115004400402034854280d05000c02400101c1d07208d5030101c4400d00510000f400b4802a43c0c02c00b44607c1101c400440c518080303500c181c02515481030b5810442500418242060322150544583c00000e00101107802e0103161002048000910340720214454400281c031304101c2d803a0350982280459010301c1080f51885 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 546848839 1250 546847589 546847591
    0x6011404050f06011d0a050303041403070807050d02282d03020315070203040e010b1b0d0816020336030a0506041e02100807081302031e0a1406 63
    0x94021810300c00010714410070708102502c9080d040e16080e85581c107900a00a03140102e07101190f00c80c40044000c130305a201000a800540342034905071011000078001c0510f094401d0b444500703154400002400755807a00d203441d0301c1859058503145500100700a01040d008030208081c0c41c1c40411440003d01080500c1c140c506c04403800d0180d51030b000203003070402c004661078080070b501544124106402d20307082d2099998400b1451041d01e04243d00d40103140b645217000c0e44802e040340c20101e0400c110703101c072039108607901848500130140000c401d0406003803101c000b4000d4400c154030784040c18405000780100e4401c3c540c80c908074074604400414035a458030714040103120501d0315206e0300080b81400074034015515082001010f090355143e440e11051125030b403612100281007030302070f070050301c908200428105039501c40858a190985004201680080161602010804050015031404911401d1203101d2002e80b0003010500456103207010303050580100140062100b42100b90804221700d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 546850089 1250 546848839 546848879
    0x10080d17041502180f0312090d03030b0310090c05011b470c031003150f09050a05010b0a120213140f0702070e0f0105040e010906020a0c0204050f010803030c0307110601 74
    0x1210596405c6014165141c0c0d0a10b0b1216588004000f583d082d4034029055100c02403003443c02180c066841e0010900f0704d45004510b0b48a551100c1c4503404004003c1e2068000d0302087c40c159801401039544a03012203101c190180101d480c0b1180808008403281845038030480300c2c070600038140d5003490300d840904500c00c2c082541c20003038404100e0308001c0c0c4044a004280c02404011150b00b151105058101c001c401d11040e0390b40d44600030980d00c8a40101c40722103018502400c051280c0303080003030940e141c4011280c85004035440920040c2c10b80c400181d0a81d80555001c0f6003081070001282c0200f8401c1e07a003516102d616000c001c0081c103071420081c4140300325400d07541c0b616618005c1d120030340b0042d00d140188080600042c491707400c2c50f500c2284103881c05400810b01842544030002240d1025000000003814000f040c400c1d03003018000c290704400d40d0031a0040d40c1d072510752695201c0c00041c5c207840302c0c4007001003c903c1076446900e410080c02103200035201c85503941d1054041480c1a2049 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 546851339 1250 546850089 546850099
    0x306012624040b0607030f092c0901050105060d020702031905071802030c0d0e460c030314040f060306031101020a05070e0606040810020310080d1704150218 69
    0x2000d0032414103000b002c0f14940050943e6041211654054408007810715244003040300300c440025801805040d0311980200e0b03040c0300b210280c10303075000c603022440003400e0300a140e04000041106441c3c42085444104120f42c0c0103032074182c43c0c070029080280e40401498112841a04c807001d1000104115045030f5072007030225904445040c5090030703400100e8001180c0d40c800d002c3c45903591500d07000074040616410030b035040201c500d10000502ca89085c1c42c50100900d003e0700c620621400455118000c0500c00e0f038009442c2c8070703600d850105c01140401002c00c803080100c03600304103604003601c000d0300c0c8100501a110f40c803040001c00400b132510080d2404848188448102e5001150801100360408060701c2034504054500007540005000c040d08030000700000142c0c0b4009001c6024107604801d0056900c0c24858845038007080c0d10703004a9100d400040f0000e0b41540c0142d040354a042400b15a0705080d5141e00f00700c0d0308150b01300c0c0080c000f180006030407020340408003072600c3c540c01c007155 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 546852589 1250 546851339 546851401
    0xb03010b2403150d2609030a1b030507030b070e06030105062b090b01140103022d0409050f07080c04050d06090606030f08070b07031103060126 63
    0x4000440341034a041c54030340e1400c00d00510207200311000965110500c0007075524414a43c10200d045040003003810f40b6252000f09500c1e0716101c6142c0710040c0d552040301554100303120140083d44606c1107032401450410644500c43d8038944600310400115002020b94503660b6890a1800000001f1100200000c40085020f502490302c002968180e42d0003600319801e100200d0000030180301600c01a6031001c0441c0c0041c90045010f02a8601040c40f45070390f8001d952412011a180c5010b542095040c58014060000c00290042800700d1041c0c90404031002480d82090490b103a00c540d801c841106400d00c2c0801100c0643c2e00c51082c09450742c0e90f80c0c076015a884502060150282e0301445502016600c08800860300d19040b003006c55004007070029280d5582e5954100c0c000110a08440d40d2002040c80428004401495a4001d40500342030118043d0031041440302d200c0145168140060000204c03100307803003c00c0c900c1410300d200311003201c5401c05600f071403c15001c03011080d00d040c0c0128 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 546853839 1250 546852589 546852611
    0x8010e07060c030e0f0a1d0603010203150108100f230a241b0309031502090102060103031b06110c01060b0f0301090b1311070c090e0604060c02100608010b0301 70
    0x1406600311005030351031501503034140c0d40c1184e14210f0301542c55805030100107813241660b200c0c0104c0c0003c024500c0e0041c50050800286040c0c0000100382900c203034414003c2111400e485002c044800c2000d291004590b51441050034085c0095040b281681d170881d140803c5a00584070880c0800c0000e520850002c0c6002d020800394911a0003981c181c1101d901d200b0b0f0b81a1009a11182c00705c090b8100004074004089406c486a00c00d00700581c00585000410801c2c00402c100c5140310b034a14400c258503041900c7e001070f5032014107100041c03c021708003040186041c1d09100102200d588070106200b4040000c1040c040f0380c00060f045d1809500c2c001002410840d5002107808030400c00c01010305580c40c2484900042510181013034100044001c0d2200344a0580b180200b440b041041c0140c4460035410f00d40c0800055400c03e4005500e4510a00e00c400d0000902c16030045d44a20003081c20825010300300e0401c0c6001803038000060074403c0c01f0601e000b0640005881d146c00358020003101041d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 546855089 1250 546853839 546853843
    0x50304170a03020a03030b03070503010e2824020d0e010902010809011505060c010608191b081b012007230904030e04110d0509070b0301060f230304080408010e 70
    0x1081d40100560300510b600b030006070098000003400722008041d2049507541d0fa006ca030a40e6100b002c02503103900040c06122030411440b8032400c044032419000503000c219a030300e102111b0321861a034042004202002810382200e40c040f1200c1c020381ca40d0501411941031404c0d8060098500c00724081050240010544034051060413100115940000e10030f52910303007070101d030394041c01c01621695201c04d0003041c165810002410840c0e84142d00780744207003060038891001d10007000c2d6454103201100040140750400204a2500c81d0711280e45070032603c0359001030f40c10111443d024054041c83c980c85415440c00400e0001c100c1311000460400005110703882c1c494041d000c1c180682c8502c2070000700340071030f02c5511502d03103032840900001400e00d0b1500104626412032191641503940300d0081241100c41400414010200115011705550619101030142d21403c183c1c1801c1220b03107001000f0300348130303402212440c81c02d081880f5924241800c05001540c0203016014056080c00154000c00305c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 546856339 1250 546855089 546855103
    0xa06080a090c0b0720031e070312080108012901052805040501021207030f05070c08100903030f2d09060e060610141207020f01110c0f032703120705030417 68
    0x1d01030541f15540080d4007000d5071604020040314840c1040110025072001e04c000d40c0d4200603252140030358500300340c040c2500c00d030340180e501286291040003203115083c2010044a00242082c9803186000d04000b51004510844114002c1d018a1400c5945401400030415108280d00384c8004140d500d030241c0c400d210714800100080d8101d0013200085100c0c070003410210340b148100b05101641c58070b00314a13210303215141d03145ca00c0d0380700300b5001016094410b0b1948020f02400600500803204451040c03d40c15a8881815040c801d80c10010110264801c0710901c1d40103604003e00c2d00000071041d135a60080700d01600444407a4541c41c07425011358078030600711480703c00e02407609401c800140302010f009000720b0107604c944408000b60280a0080178240441142d049403034901800c8124945203a401410700c068000301310301ca002404c44510061007c1c80c401e03101350210008004640760080c3d070384050001401c0440c4c01401c001d00072004000309c40c1142441100108940c00c59919840 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 546857589 1250 546856339 546856403
    0xe1329010903020f0d031101091b0e04030f0f02030c0318010e0a0b040b09040612050d140a0909090218010b04050306071b060f0b1003050a0e0c0a06080a090c0b07 71
    0x20814418440345d1514082080700180f0a1410f03908402c5685d4420f800d507010050112540180c0b00078007440c0c95a105141402080c032100350260504090710090305549000080d0030401c1a0141c03002d150600030011502200c42e07031021295190359820840c0140c81c50003410500007403610391780d61064a8000ca00c202903074030a042462506240c112400030360307802441480d82040e1210070014900c0c4a52071040541d60091000c1e215480781d10900078910000380e03200107042d150500c50046001d5110305200d065403007401d40020350301001d00004404c010364240c0d071030b2825400700000c1034074502d05d0060300c00c8480075002c1b00d00b070b500e51800070360313034a81043c0d01902c003039846c502440081020b0703821000c4801c620740800120b9000110104084c1e40040c0855000309841d10244600302d0324038443c0a00c541c1400004d484050315403400542c0c210074610502040000b0700d00131404500c82036100c0004243c0c45040360006541d603091500503900003a401341c4407951040c02680303c2c0c1ca0058410b1568107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 546858839 1250 546857589 546857599
    0xb0a1809270204090b01080d0e0603011a0714030a090906080304030b2205031803060a0501030b0f0403050405041503110925050403020d03170115020d0e132901090302 73
    0x806040e618420784441d9903059038402e489185520209024164842c040c010800151407528581400036000d00103040a20f8090031042004101c068099400038240c5940f101d085590f07140f060800210b0700b145080381030b45501000600804442d00210351a044a03803e5505115040e40c071000c481e1640920310000e0040f01400c0002000803900203d04032250940d180c015415008a4689900d035800c10700b0428404070132030104a40a2404000541e88504a424280000d6045544c0c0441c1c184003d084d954421071010042010140990107072005068040c1040040320f10015024007480300d14031064604003a5905040c540d414400c030740911900180710280000c0302e00d6200d4003004940c013104201049002c2c1700100041c0d1310882241d101e14000ea9a880400c15100c58801c18100306900241c4400c409095a040442d001700d944100e050b001d0501e0700001c0d410b44040350f10320000c22100c14a0901d41803040229031302c0c10200b0585c0c8540c60a41c068060203410040d10748010178000603500ca = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 546860089 1250 546858839 546858881
    0x201081008030d0f14040b061804020f150d05040c05130c0e061b061801110a021504110306190509070b22030b0114130203040312050408040b0a1809 65
    0x5007000340c1103944c00c1ea941040006607050030544242503460f06590458018140c40c083c0440b81c80c29070694440c0001511086800b41410f5001a6110140030b807a0790080201d0740180e0700103241c08095a41d0703440a160b090140b03252904d4025803a0507180903451246429a0070546001114800c400302001c560711145e1031440d210040008640008c940051907203568009a481d4030b505004003806140c9484501c414120703154120381c00e582c07482d04009a49001800303203036001640010610b1704a0a20444500b65480b207040010b008066560400e4062086105000300c0b00b92426410400c02c1c2340f00020032454540c10b10050b01d48006101c0c1d0008290107206141150485201d800311a190f5000c0380e291456a0740e03150440070100368085400601a02c41e41290b60810f10000d101c0c02055120851440c6015035000d402c00c144a038045800c02d0780c80000408001c401e10450340039112021506489903c603a4006040360305645080620013a00d52000070b203520039004600c1c112025503524070341 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 546861339 1250 546860089 546860107
    0x220c0806090601110336040e1902040605150706150807180f0608030406021605060403080304030c0212030a17090d050f04120b010305150c040911090604060903020108100803 76
    0x1d1038103400031300307940410040c201410b030b01c5140044640c0074428000580291080301c2516908a041009001c0c0e800c0000d212003d00011508401a01c44a000110784103642c0c004180140302a0f0042038011146424207407460b201040505100c0e803040038144102219160311001c100c031284504500c40c1d0000c0d0b0306009810702e030301251403040007141002a0640c100000102074030307196407101b00301d03170800141441800d5042c090840404810012000b2851070540802d110340f0a52001600205000c004102014440d4050151a035002401c145070442d410740550f03260780c00046c0c042c0c0460128242d4420140960f401c81c0d114041001c050103001c81c035107606031425407110201c805000c41c10007000c651281da1300c0c4061111802085050b0166041d45407180c50040c2041e0762896000c004010043c002030301104540940e0f001c404089090b8a113410b0101c0c1500800018079400b00011501003103032584460f00d0001c9a000b40d80385074860700c8100c400c40562a882c000c0c0700d410b8000b0420b20075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 546862589 1250 546861339 546861347
    0x60e0a2a0f060f05160305070312020c0a02010c1b0b0d1d0303060d05150f07080c0325020a06050405010203061005032e03020405071106070e0109090506040605220c0806090601 77
    0x195084280c184940303072000d200510802d81031180801c1b0017007480403611400340355100c0408092694040000c41c608651003c04550b51545401c0c002c1c10403038a030b5a800700b00007500d8018032044505c2c0c48070b100f0f41c5460b42c0701040701d500012040810149400c481d001800c02d482c0c520034012a140d00078501c0c54a805050040c10003602c4425150342c07044401906c0500c00e0b0016041c81810310b6085241d90341805c0100a0499101603d80ba060040500078041400703036440b00207001e0501a900b400042c0b03001c201c2681400d60390500502000c1c41c0a0801c0184070064004500c80c0b6001c40b00222040030442e41070b10180400d43e0031b500d540141aa10154150320308003100c9090240c5c18100486c00c0d035a90014007680d10072504034000030300708414641190340c00c100c2c0382d0300700c0850708000452204850000786030700c2d202d07c15156002d0303c0301d01080c202d80b035642c4403c0180c00040d186280324110280d0441c030b01c41041458103001454030360301c8a0254030407025035015013801003501c9031689132440110b03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 546863839 1250 546862589 546862607
    0xd1d040212041713030b061e01081f0f0b180d1a0919060e01110a0c111215011a0f0306010e03150a090b100305070e04060e0a2a0f06 58
    0x9800740b4041045032a070201d001c84c8000154412211820346240c20303418007006c2500c2e00ca41c6000d90300f50310540e2a441c1c0e00308480c0c5030301100d1a02052000e50b00200801100b0043da48640c1d085401e9050102c0c0d20841000242a404c42d14403024007221030000603c1005001044060001c6220100340100754050081d065040041407003254500280950256040750340071004881031644d4624240d0b112001380556451043c462001d10306004440501404001108c000201070b104040c185000a0740c0c0e03c0c0c0b13008800050340c02201c884030701c0d0302d0742c000c5d22250a009813503514074510001e010b07511013403088549140c1802c0f21581182c480c80019144002c088a1081d41806075030b17240f82c00c40941d004118440c0700d0240001c550b8095034181010700040280c50b0354400c413610041400400c0c4002070020032100e003a445200d05a6803820880003c0c86004032018041c0103100488061140c070309811003220b804003c0a2904005207040c0d088144447c0c8a015291358031410200281c6015140304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 546865089 1250 546863839 546863873
    0x11040f26030d14061206070e010c050a0b01060210060501020309040f0f0f0209010e010c0c0510022b030501050303070b0c09060d02040b22030f021009080d1d04021204 73
    0x1005203003900d038482811a00034601000e0b050f60f68480032441c0c0b9800281a64005200740c4400f81c01380c040b4103249840d9803004140f5001c0c07241510104940364420505040301c140c105040e01d81c4604180b17170001003c0420f01c1860300501c2148100c105100c0180304810440700d0507002585032105000511019001528503025002c0e900c0d81d500c81c0d80855801801101d1020040050b6613401020025050000740e10055042041e1240507000003110b071240002601c0044481d03050001c1c040200b20325020103403181508034001d41c99195400081040b0503079040c80d5548040c0304903a22001030640c0c034050080081d0000042001152404291704018a980880a081d0525001b00c0460b01801e0742d000d9405041000c000203000c2c01302c040c020070b2200000e00c0901840e00c03101d01d0f580700c01110002c0c03c0c0d4082e10481d2002c55240c0d00d0381c0150a008001c001c0801030f10351349080404068104044024100340c8210460070a140900e01442180c181c813203025400107050301e894031080f91041c0711941c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 546866339 1250 546865089 546865139
    0xf030f060b061605070602010621110d050d020d0c03050304140f011404060606081006050f1209061803130905060607050102034011031e0a0611040f 65
    0x54050b0780394800140040300140b000c42000c00c0041c5021440c0800550161046914114051182c00702c0140d051485042d604842800c0c2070751403d00084003041c81c1e410940c0b11180c03188920800c02c0210790004191002d070240c5101000c0d001c02654800416200200040c0041002800040b80520100300405003c8101e45819994940f043c1c00c50701410108181c80001c401004200300560041001030301c22460101d040c0d040100008218080d18013400080c480d0100703149202c0440981603406207207291402c12110b0030402e80840e1548425143c88002404501c1800b014510000486005104800201014dd441c0188501c001c200240c0215400301041080a0100e8000d00145003d025240d020000060301305c20343d5861842c03d005c40000341c0a20300c030200d4000c2d0000c01c005915030b070045100c3c22080c440070b000a003411242207900782540c12050b14551055000102c1c40440d5201d94030420900780524103109041c0180d202d070520400841c039050206180344803052001f504500f031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 546867589 1250 546866339 546866351
    0xe010f0905150705210421060f0507020d03140a15030804090203071214060f040219050405030c0105090904020d14030301080102031618030803150306040807050607090f030f06 77
    0x40011250014032420010b0900003140c203c007030141c203102200295030b21100c0c60b4050300191000341014043c5200d4072101c031606003002c0d00120715404c0d2882030f20790702100070807d0680a074114802000c0c00d0300d40e98018422402c00107100c90092240601c41c651103440e081056a9000c6010054840351140c1034140c00c40446c000001440400940301901d07451201580300d01c0c1c103c02c01410030321000008079190341401c401c29440688880380c5a00101d05840c400104c0701d100c004540a4418807000c10103014408140444d01c5521102a0081d19000c41c161484002800300444c3d03c2c0c0150440c42c0d41c00600d0768046001850003e109401551107a194010200b0050140c00e0450300241d00c00f44050750000100706041103c40100c400040c000d08080520f034442c02040340102d04030303003c01410454000003142a01c040c1207500c1c0850f4a0043c01c88500f4909498400c03480e03000380e5021079003840b408020840031409403502300156103980744000c409514540719454410001c86042e00e20f40c2c4e50300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 546868839 1250 546867589 546867599
    0x9020d110a03140c1002060112080a0e030f070e0114221104090510060f2c030102070317250c06020d11090111011b230406121b0e010f09 60
    0xb1480b85484007207040601000400502401039402003d60700c0c5c01190807440041c814800c43e09441305103140c00202484e00d49980010586186c680d40c08007070340c0b6110710303101e519114000007481c0c8140d404500661900340da841d40d0741ca40b002d1007111034036031141c241060700950700101212140d6111043e4000300b000e03030403512814480d9205400c40703841070f6210b904128007100c2500d00c40c0010061341c540b8051209840f00d008000c4d02c016241801c446610411024000517000601010307620014004c5607182c0a0345405401c808415640100300c20300d240003c1e507450074a80480c264100310078019000c0d44c02c014011200b81940f0307201102c1c03242d4203100b0041c81e0340c29403203460720aa010200f103e0f44d40d480034002412500019408204d42d82c140500380ba80c007194010715127802c500c1d03030828100000411200610700c02244041d10304030080800c0c0040c1041e2f202d0341074090008050020450704240156281800241c031108501103215100048255440f42410b8524a4994504038444940703030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 546870089 1250 546868839 546868853
    0x70503300f03070801060c030804020d1103010c031a190519030501051006020f01060305121b0102030c031806010b031305010f0501170d08010e06011107180c080a09020d110a03 77
    0x4982600010304003104022510703401110645c003400d081d0600444c400401d03a0000d02c1c030000100000c4c003a8440800100030850000b040b00784440c0018001d01007088800d80080c000d000020500203422561111030001d07052100d80c0201e0700c032200307a2030100b41d800c0c841482440245007041c2c0003c4d504642001010503028402c07240208207180e40317400c4c84e6152400003845c0022000b03101c2140e914250707080002680000c1c42030456101b07601e1954860b405100c07014020505503174801c00c5540000704001c0e0020701d1200030b61203441240d807050041d4070b0225805e90750b14002d0142c00b1a100c000c20214101d521000446040288907900108100040010a105590082c2d00c07003603100780061854140382c20180810300501420b446c01c0f030803d601d46200c11135465800b40c04103043c4000c610365041da0079018003007480504609055000503640384681030004203450313241c2c10b000170034400100d2200035050158480b80381c0c00400401c00b200e206d0b00c0300ba1001402007442580703c0e254050000c009128 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 546871339 1250 546870089 546870097
    0x15140a210f03080703140f013006060302090c040b182206050405010503160e0a02070f0302061608010608180304080a03110601050a03170703021501180e07050330 71
    0x40b0303560321541400d1040014065891607072084402101a000704681025418441d03070454440c8544101204125010260101078030112441e0080240d103035007050200580008003181d00c2910f040721150b940c0610341e4100e024030300403809802002c001e03018a5020540380140114401045c81d40d030311511801100364440d4450104445580341c18081005141c948940f40c01054241e020b8480c0385400340304592010054060205000009000310760388070540d81c166038840d0761020001d81003081904011f0354030001211807505540000d2603030703801103105e5003800341210610f4980e00b140303889025040076a584101c2c12013510344130a2000040044007085142e0701c040c06600c07a041010382ea0700e641170034080c058000318080c5051100c2000000e8070546111f160441c88251592a51b4862800703d007014102e442803000d40c0c02240001c039580200d4044075090381018842000441a00d80040792030710b80c01c0c406c01d0f5250304000c16401442e9211401210101010f4144204806000000c44a6900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 546872589 1250 546871339 546871343
    0xa0519080301141f0e01080903091302031b0f0d050618010e25120e030c030306060f09031209030f0a120c1401020c160806011a0d0b03060a15140a210f 66
    0x903a55605142c00d5030802490358010114001039442c041c42c98000c504404490b00342f1000c4154000300007120080c0004102d01e50701c00040002ea913451004e1440e207400d400c00b81101c03403502d2401001ca4a60310313010040e00e55080100050721684d80c0b0304000d407003944500902e03420403415900f0100ca00c0c50400c031b07200e1504103000d80302d81c042d084502100760122112010000060361003001605400d050000030f581e44080c0c21644966141c0c0c0b51102514240105110141c252140780d0980e1600c140c40c4001c0c0c03900b100309a040b03070380e2441c3e00c6507043e9842034000c0b4050501110050603901c814480c4038423000e424020810309106143e1790780c256089070300404a0202a41021451000003000c2442c948014030781000100300035410003401035050400060001c1c5c00100021791403000001c01c1d001300b01e001d400141039511a2800820502c05000f0741c400c81c2c0c0a0a03448400887c4040880c8008454450040c041541490414509011401041106040140318048200c0000d2020744089100034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 546873839 1250 546872589 546872597
    0x30b10020616030509070e1905070f030b0904020d110d1406090706050f0a051b0118050d030c120b040908030903120105040911131d0a0519080301141f 66
    0xb141030608011a0321150003204201410001440035900300007030f1840c16a49840c040040d123480fa00d0301504140508580181c645003440304119446804c41020548c42940da10140203680c41142003281c02c52084030b0082d801410001030402260f1104100441e524000c1e242d00400001619100d4510400034050940340d0f2007075041200d000414811351008100e2030a069080c00248540701c0e45500401d0840010403c000c24111803d1205205c1c030420b00c032080c0020041400680030354405940008400c0e100c9102d4811002d01c168800e02c503584a5031080c1e903584212500660580001e8885205115406500d448103a4085010080154090104c580c000c6a90318400041051305110581c0154426840c180ba00340c04501801100b0140d080c0803208400c42c82a800030b800010070034042d40c0010b040340f5030540300ea40368000401d0900f4501450440d40012804003011030041300e6414010703d40700061004014240e4050107090a1042c001c200805c151202d25041e03010040da40300080c00a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 546875089 1250 546873839 546873841
    0xf180c140f1b0d0c03050309010f020f0703030c02120711061201060c060c030507080c3901060b04031a2a04060e01081b0c100e0102090a1d0408030403030b100206 71
    0x80141142a41050b084003030010f00801c03441c06815514070010203424048000002509000207502c103c4010b544003d0464036034400312015400b0f900300410480100e40707031004032081e07a400003a0b80c0c1c0c041a07030311503528a4890310341d072803004880e081002d40f6003040050203603220144103260000e01900e02c50750b42c2034404840341041c030152100c9101c6a801d061501d003e000300b00c0da101b0791850303024140c020708581c2c50302e04604000704100361f072002d007090124003410040c203e06009658031241e00c0c51002404003644172900010b040c860703840020910318002500083c240d40590b40d0301d0303014090a22070342500d038603014842e19542c1060400416014001028000380303030003031004050f003a001e10b483c40b158170f08450452802c0d24a24041807a40c980842c1554003a0410420380d0001d4004101c18401c102404175118082c0d0003901040307104a036144408515000101107450308041c1c8510328455a4445480d504060313440a001079080503102e8120030036a0300d03034080003080301c1c000350300415007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 546876339 1250 546875089 546875107
    0x150118060c0b011d240d0c050a0f0806130203030d0903031409010b030615150d090507060f02030711271504020a200304080d020f01060f180c140f 64
    0x280328058004d06204500b203161107180d400340d400c2c240c1c0c2c81694100d4540c000d40d00d03203e120045643c0c0c02100c0b588441a180302e101007000c50544901255020b5070181d112a4031404485d41d0a4114050312096502c802e00040c02828a0140d110741c060000d0190b0381b0303081031080c4d000e040e01d0000d1000c5c3c0c00b00b511342020500d071040d000c031495807101441008014030080c150020f5161840030301924a1800410402407882e038400704020074580c00e0000d02a502c0403802d10a0001e85494041503555026000b00090341c1030041c4c0d42c0c0c00c00710f105503000d589030001c9599444400b0910368010303900050056441070051010044c04190740001d8203e101c041d1034001183c49400704400d80d00307801140184802440e11703422062001450071005425502440c400e40d07807500e18021a07100301040d114150030700b441c45801003400a031607000c0c08024000d81740c6030040310b02a14414400d03542c60703114502c3c1842034002c1c5a4414902540c00c1e01d024420707201d0110420625421103445440080400502660 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 546877589 1250 546876339 546876353
    0xa170306120f07051005250204060504091506080705150d06090f0f0f0c052b02131a030105150a20070501200303190b060d050118060806150118060c 65
    0x8055011454240d00e441800c2002c03d440590b000030004050803821101f41c119902c5030003d1015007005841042401c02c542003c500c0d02824000602100f864030a010640050100d405001d88801070040d00c0302c02c01085241c81c156010030410110941d94a00c0810048601d0045409045c505040400c00c4810a10180200d42c495519140594036186199074a15004819503901170341030b400440031643e01c1d01103451408003d605400b882840010007507400460720300518161600c0e00155000a8641900b2454501c001c0c00b445034020034148400021440c54001010841807030300d841c2c2c505402c3c070803c3d2020071526031101c1c8a03030b8011758005d200c6541c2c401d60a01704076603c0d100703243c0c04280c0c81c0006506d1f444094180658007180c450082c140c805141c10024640e8000340050355034011500006009000030700a6590a241016091040728214026170090310380f441c024100b56140c200941010946151f1050305000f4001c000101c840720711540c240041c100e5858418121b029454080c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 546878839 1250 546877589 546877609
    0xf040e160206070f020601051002030c01111c0c1416020a030b07020c220504020a0f0e0103060b120c1e04050a0608061b0f0306040905030313140a170306120f0705 71
    0x5000c11001d110402c0701c4c00e9000030100c4c1129802d4901c0c0c0c1c0d0810300404201d00b103100700d50910711103600f0030104c1588118900f0003018550010b02d6004814810003841000766448004128002148540c0c14002e2810450040079020114440e10030b6191460340800e410748100c0c0d02c00d890240c81c407000c2201082e0140600400b000044850351440c0440c140c40480c818482c04101c01c00c29921340c0001d0464440c40781c60401740100102907001c1559074103c0890014090200b10b07945c5040407400002c9051202c240c1180c0e00e045405010781d020301d80d09000303601d800c5030f03400003400125650707025094855120f0280200c02d451030205003113007002052440c10710041c108083d00344019500c0ca5405282c607040d0f4405505410059039a0b440d1040002c02a0214040c0a4a54000001400f95681d8131580c1d44840c10f20900421000408524000392501012040031f003217005c000c0d402500141e41e4200440e0703c0400105282203940b10f070000316281841c110202e00e255800035406110b540f030315544074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 546880089 1250 546878839 546878851
    0x6150806091e0a0c0909080408030f0c07060507080d09020609040c050c120f071401090c080102070b0106092106090506090604211b030207030204051006080105060a0c080f040e160206 80
    0x1000c980f505551011000c4443e031150480389562003c08004200121040341e0042030b00c841101c0e1108032444041c0401e6101000e2003003e4410790000061003400f0308280d0348c403a03403c1741e03401d820244c072845c140020380341169003242d004da010040104281c0e00c078454407a001c1450354542d0749403007002303001914002c005030780702c085014107008500048080703000f1a8a0b441c0d002c0a0612400d0582281c1409017a0a210040030059582008600494150701428480340220101c142d0f42c0d0365480c3c1500c5010990241400c001d80180301804001c4000a5034400f4521810340010f1102c0f007034a03511304081c0700342d4804c0e2280d00007105010600c25002c40002001c40703809502c0c03800d24102200039241902d0501b002c0c4042d05421740150605000381304020045030040c0007400759180c12070b000100500301c0d003e038402248a00b070011440d0300300174050304d0f45003401c1c3c0c0700c00044107100e071109a01034200d90400c0140c0b0500700004904042c9103030000d40115501c0c01e45800c0000c5603d0083e003440c60081030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 546881339 1250 546880089 546880093
    0x50c0c09010b03061c02090c18040606090603090c05090a0b01200606010e120a0506180309030303010b0313050304140f03060601020718090c12020a0501170406150806091e 75
    0x5001000340c82e03040340c0d04214201e9100d800a524043c61007040d800245020390b21200038002c0140041c0920010440605400304900c500705c2010b040004880650261030300040304500c00340b1240b4020361190301c1180c011032500700703d20f0761782d8001454501d04035074511256440f81d007401f200356005512442e5911141e2054240b91840d688603940d540b4008202d03504000505810003019102c000c14459008150001d60784602c1582c10300540e981002e84282403050f018480070f40c9c070104080140d40001702e0050240d85181d05e003054003015900301a103d20f90410500325004001401000240001c0c9001c41010b210315500b541080340505880c0c10950003504190b01304a07844e80e011800d401681c0380300c1c2e100c002c030740560700c0340e400100600c0e4030051006000e00308c0425020b0302c0340280f0640e18802c4480e9040719480c1d03001190104104540701d8450b034040703000f00300001c4030b5402180032144000544141103940d400550700d8010143d81c6c10440b500070785003541410141c020422010070f61400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 546882589 1250 546881339 546881341
    0x90f170c0624150f0a030b06070b0708010501020307170a050903030d0501030605010f05060901030c03021b0f0d02010603030f050f1312020909030f04031e210f09050904060b0d080406050c0c09 84
    0x40003e030314810b460402c02260741c0060b00c0e402c80c034000e611000d0850405030009841e00603078504540058001e07a41a00401c500b00b000007560341c800011501000d0f400007810403c091401c0030500355410003629042440814170031825a0785041025009191b9210008540341d40b440c00c041e401c9070b0741070b085a69000102181803020b0748880781141e4540b002840e0015041e004881e048000740107040075581282d88408100c6809440090341d036070f84005042c207444400d01d10038800c0e0308a6007588002004101c41e201c281071010b0117400034003480189030910b18600b5114002040c00360702250015100d4400c600056415800c0c80b0010650000d4080000d44c03801041002a1080340541e01c8010301c9001410800c0d100f417441d11041607003160380003203040031250307001500d004c0680301558024000b44030741c40031070704161045008404940d00607001d03400e2a2110740b90b900190244001c0590080140d0340b020001600ba000240000c0111766a895220500f441142d1304003450040c1030b921800c2a04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 546883839 1250 546882589 546882619
    0x16060605011b15110d06030311030a0c02120c09010f0e100501120c11100c1706090c0703050c120418020c100504050a050f0a0312090f170c0624 63
    0xc403040b01035048050016405040700b940c802800210340c40e036501c0c1102181d0f0f00c41c864005c0d0032000a49200c5d44400c084103004c914116580c0c00303a6080800010500029100036041440c030180a504212065032800030301d01c0c000c00c003040e4082e440031804a488050030400a50001881a00090b0200015040c0381c60000003c189804840700701400360750340c1c81040c3d280f5000380306801c070400b102c4040c0d410384480d605280e402810700e00700e602c0201b17150f10b51246414056450240c0b01c0c40c001000c81c8001e44402c00070401640040c0000c03810b0080c1045401c40b2031100300070050007005031402181d980c90800f542c4204111100b00450700050050019000c40c1c18042410030001c185040006007950322401c089142c8041140d000c1c000b0b009040304c0701610309010030308450350b50180e225580d14a4402c64118121210088051700030b0301b1015001000441e04018042d0045401d41c0c894208624100304a0610304103403054034503001c1180c01010b001843c4203400d030542c181218249100e009070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 546885089 1250 546883839 546883877
    0xd1113080c01090b0a1115040b010f0806070f2c10090f0b0313080c032104030804030807020c100e09090c0105040306020f0d09060207061118010c0c0b1606060501 71
    0x15014002d40401c0100c1c00f018401d20603640c1406110a41c807c5498048400761018034020301583c0640307211891000100d144002014142e0894510340d000740482c1d91507420071680f0350024540142046985010032010a149400d100c4160300b142e40d107140d5110b00301c07003000080e4034200070103030074020020700c204590703904040300e042122640c1c1903403541c0c0c0d0785080850a03440c078090b000034500103011402e03c8030660000081e0031402034424000d85001c03940d00203503508080c02c0b2002000100d101c00010f0009100d6030141d50400c0d0540110b41c54503441c00001403081d0262464800000d040ca050041c486c40c120407640d0b0802c1c0000081e150b03c1d142480000c001c1e10850001078010b640001c0c4a20210b1800e5080b9094000e0a02040060b0801072605101070b5000601c250759190802140c1d003078036955441200e904230214040c1754100900500107460800342a442078440c0c4a180100240d004541c40c02011001c41e600e0300f540310340c46289056011140c1ca500902c0c108002c1403544458074945c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 546886339 1250 546885089 546885107
    0xa080c0d020111030c0102030f010e22020d15020301080d030b06030702070501081b030c07060b0907052208070303030c080901110702040914010e030d0e1f090203030d1113080c01 78
    0x203203407240c40903e420756107610314811100081c1c6907601c00010842d9456103550118140c9405103040c10164440215240d02e540000800354030342501c840d0000c1c018034050060104180c440c101c1c5100c0c03080704803142002c80c0c00036808108190000d40410041551504c02d14820000450795607003036050a41000b0740d900e031540902e40c10300401d1404680e94121800b8041010001010f5995807403a10b404015016009a80111072071814103c014011b0f1a00307a2002c1d218420680c0c501c0e003400c0192600c0240d06011402c4c012507140c601c00c0c00310b00480c0c14004003001c0c50294034046049c001e0351030020701c000c00090280000b40d00d0078200c000c1001500085612842d011500840d62503007500f01001ca418122029856940c40c140c0b09045465010014108004407880100202080d415884e0748031040d0700b038078140b034810851000103a000e40d907008004407800541220b0a10044200c0d40c030466009242c04205c9400114241584003145421140600012400f41040c91060800a0802c2035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 546887589 1250 546886339 546886343
    0xc070e0c040b070f1e030f050c1209040b04091208100f06050a2d090f0602060a15121b050d110f03010b060703051e03010f2114010b0a080c0d 62
    0x10f2035024851505103a00030390303411251402812031060803d01500e041000201c010841c3c02c00c0005080340140140c2d1450303030003900034100c000040340655905910149045903c5540c2d000c0350041902e85121382040c0520480b01800b16123603044002d460404014102075410655031001d008040c21134516030112801030401540703032031b600e10b0142d42101d040c2648042e501d41d98a40c40a50102141d940c1803142025120300304010748410743c14540c0100e40c000c84015034480b1011984845507a0700420a601c0e4007240741981a80710007540b5205400043c045c3e0f071a41c124420b40903c0c01409080e500201030440300408001502c0d510501d020781990740b00c51054044042c85c0301e05440a400c05215120020010340d600e603601e10f0050f05a0308440c0c0700c62078281d000211076081200b1941101d0694018001244003545048107031004000c5542c5000398100c505070000700041c2c400c0e000500880044800440d0344507601c003c1c001d26481c90b902a40c1c0c140c0c05000a1030703403500ca144205507190303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 546888839 1250 546887589 546887609
    0x50a030509060712080610021603020603131b0f05030c0d06050406110307050c100501030309121a07031d0106050913030e0603090102090306090309060301140112110c070e0c04 77
    0x70011000982501030b000d800f9103104580c1071019451584205004d11882d411107a9550b00a5188003c0365210803c0050784600e00b00e8050900140c40c102003e15880b10881c1e500d400c40c110103070b0303404400c84000e000c00710308051b40400920421246807154030180005030024070355518400d000440d920301645003d441180d0745c03004030f0184411a0480030301c024040849503501c0c1000c00b00108640d00180c5412071601a180170401c0140c90b6000b11070407a90569210700c9030030700304980003441207540b01040b04e0349a001e00480001d50f52003080144200b0107510000b51419455801520f540c142505c45030442e403600324140416603a819095400c04448035603046d02c0401c520b020703501c907005a0741d00359201501104211038464150003e1554000a0b001c0d100240c0318140003a949002d980c90090b8801c43c00d100510908151072009141803605150004820800d4107080c030446000105070002d10303100181d04221645c007040114000c2c900d4038008942484c040d8140d41c054043d03805200d0700a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 546890089 1250 546888839 546888847
    0x4170607021f0c0e10120b0301091101050c0f01051e01060203030603100c050909010905060f03030a020d0c17070501090318030c23060c0102040510050a4e0b040603050a0305 76
    0x80c07055560340803004d0058070340d9003810f04900c0040d05450f225001c0c5814107003407044c407400303908040c0540820b07a90301445041a0300481c2c4015100c5800085d040511441590b0b1032040b059004d0007024042c0703020320145038a03544200556080308034160001401c0d50300420a2100c203450014240395000d60b07440d800a81032600702400c80b094071800102d580d00c0348000c000401c3d512241c1c0d200070700540c0202d0f0134507110101c3e84249900c0c3d004000d00c800243e048907000e2000140942d503418000780c4202c1c16440701203840d10f2003c4854004d0001903499a549105203810135800903808540703140c004c895801010701d582d0b5106102c1845002e038442002404200320080c03003800c20520100c0c0070003401c8584840c400c26119000b9001442510f101d804c10000380102680144100c0740c2807003c0d07903112119500550810f0107012489031b030034078414441c0460201d0241d01c16400740319078106140b442e00081d01800c17441c4141c401191101d4401c0c0d01c0e00004000103000081c0c200c090316410b0a0460b1a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 546891339 1250 546890089 546890111
    0x10206060d060e010c0206160206060105041208070606140a14061c0f0e100f0203010b030604090311160303030e03040f06080a0902031902010206130b190b0604170607021f 75
    0x501001c283d42c41d415801c201d07510104c103401061a03407180d9a0714030700071550b94103090226a160015644030707000c00d10402c4217001400862001c00384241c020780013185011300b142d455804a034a2a401080000c1e9072841c0d20203d0310780800810014010b00c660810b0748c0c3c2c10710b0001940d41c8070b4000b02c003044115400303880d88141d6040e0820181181d0f0789400700401018049004d8031341c8112004000514904a27148040080605c03c4d0303416240c02810302400d5644480900004007814503080d020f11009127500104644100011403120025182e640744083c9549400340648a9001d281402ca07002400103100e8016158000003c40e0002d141846558a8202258004148000001c6c0d05402100d0607402250b4031070120b201003a20030b9085401c1da03a01c038121000d8503c66400010145817100001c2991050341100c0f100e140e0040c4000043d48401c00000511070782d000d503203c0d0318003604c03203012060021024003455500c0000750000d401ea001403151400c5102603620150481985d5800440c10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 546892589 1250 546891339 546891341
    0x5040305030105040e0f1b1017011211100e100e030d050a0903120f0e0f0f1002120403060e1e06040303050c0408030a0201060510020a051b040e031b0105070509010206060d06 76
    0xc500034400c05642c0c0b04003002d42d88048010140040b03d0145248c1c10041685511401404601d102132681c0003000780d0030700d044007810b003802810545500302441d2609203140e94800942407418203940b40d00c5404444034040c481c0c03414580811074140600f41c1701154003a100801c19007410303645881c0171595240b0383c0320f054a11101c80e81003e400c0380d4030900c450300055004102c0c114001c055448454003805182e007005850101e030000d1a40014140802900750300300b4025040d00d10701d60b270054540d8455940c81c0800170390001d510540d00b09444040759003500030140314001d13100480301020a000a480303030809984084c06080102050340d154009540d403070a4600f038501620129088d40d6964645420003806070400d401903520501c2c40211101601c3c0c0005080c0c2101603220000c1c1807608121742903140c11201c1900011f070040e850383c2d0741c0704d03403500140001e061510001c02d0700a00145038010007421514000d00d01400d000c020000044540e800140d01640540d0031190252509001e03d0a40c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 546893839 1250 546892589 546892603
    0x1303021e030313020d0f030302070b0a0608100e0316050705040b03030a0c150b060a0f0f0503060a090506040b06120702010b010e13020d1e0c0e1f050705013c05040305030105040e 78
    0x14240407406c002501c2015031507001003c20302e005030b28103800c9450b580e40c64400c40d0f03204e00c0b07092602d9000410070301c540c4000e40c0204084101143c260b03800c200001401e00d1122a00040465903a00300c600280031518042c8103040441d48254003e40c1001c08a01d405007452140d40c9000d002d80039405d41f8100300501980003868941c90241c2006d494441e4484040c01103072110b080d40700403a04000403201860710036810359224240c01403100c64401d10305030303580c2c1c0200b102401494201e9201c0014809a848030002024684080c0a030284140f03800c8000a08403030115444504005c50300b2110071035503482c10005202e000e01444016620111100c51500405081d00740c1010b00d08441c64024500030540c2c019040c0e06e00c152104030790102d038a020000c05421500341140300104840e0907100492141002d040725500c1540001180d240510413117507000002c00c0320308000c0a11881c0e10801540400c0001e12160031150203100c9400c060750003500a0005001303d0b405941d40d51820b0440d014100048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 546895089 1250 546893839 546893843
    0xf05100c0309050d080702031c0b0925030c0207061115160e04092307030b160932010504171005090d0e09040204020d02031303021e030313020d 63
    0x400c0340401440028000e03164a4505442d030f40100804220400d0040e03181134820002c640c05180b0f02204c0380001c2c00016000191400019a5545500e215840d0a1140e40c06025825003010000a440f24940300400528810408060034460101040e60300018a02c0645100f42451400c1c44648070060385030020500b4183c0742c4100b500c040c445941024103a802c0950302545d14030441c001c1c4c090510007a12070030300009201c880400d09460541055801b2090104040002e940c4401d56a40711031000d0300c0d0a41e0b908003040e0030404901e80e96900103100b00d0041c005103030440c07441031036164504944020240803d80c00c9038005c0103808568070a80446000d80158214a503900449401c499510044001c412107050315140200f00251000100004080c140f80c0d1241803245000040c0b107030ba51005030080760003035001e1042c1d00039041c2c240040c500c07820403501039120080141c203000385402c120300341290100c515900a102003a40210442e54007001048500f0b042050303520111314100c01030180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 546896339 1250 546895089 546895091
    0x33061b0a0606030c1203090911040e0c0c16060f110129040b190308160f0f020a060810050621040b0a0f0b0a12050c03241506070f0510 59
    0x1400204580c590000090328040d40a9260441c0c48901740d1112070440c0078054041405540200141d400d01e800203004040c01c00c500909080d81c1e488080000740c8156102045a0340c0407070401e10507401000301c4041d002c9103c0c80915024a030074000f034001908500c0318020040241001c03408a01c0940003403d1aa884c0361403110080705034103171070419035080e070303421751289007000d014520915101c80c52201c2265240c00c1c01f48c0803451030780c03944060b034000fa080c200030303050350117510f00031a50051400c0c440c01c0c09211841008403c5204000c0452a80d82040042c0301c203a1050102082002c003c4500751030040d21469900c08e02a0302c000d202026445160713000b030002404100400114684c018080d6002020078004203065150520558002d8050700d9003016550908004110b000e0a0550744140030310140c51030881d110700444d0801e0390721500b070001402c0d54014040e00d410114580c0c0e6000c140c000b02014404407500c005006481140300c09030203090006210802c0c088180104443c148500b00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 546897589 1250 546896339 546896353
    0x60301091209030611030103050c19120f26030a0c14180a06031829070306051801050a0302090925060f020d0c02130f09050633061b 58
    0x40100340b868180011540d00c1d0900031030803c07030301000e0156130503641c0c0034011308000b801042c04e1040d80740751445c06000301e010700100001d0030081920440f8055004004180359124581806079103040c00000818403641c498040c0f0b00100c0b021426a5045072440802080c6414032a10480e403524030094000d2002a001407810f08400c441100d8403104030047d6214a540b944d146400d4044405041950b80001040003c1c5800115001e0b02d500500a1f070410843c03440e41000840702101c02d04841c04400b095a51005012501e40360303d055500c4c41581411070f1f025030500c0081074075040c8a20009000340603010114400351700601000c9440280b01e98480e265021102d04000c910101c0c0c8144004601003c0480380114800700d9043d60203440750700e6491162107160300384036450640c480c9082c12507540f02050205925540200144540904010301c00c6080c858424202040109601d102d1a075114001003c0704400d01400c80400d1002c4075510b0301c1d41940b050b809041030480d64105034034010b1071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 546898839 1250 546897589 546897623
    0xf0901031e050f0304050117070203120a1d0c010e040e07180b09040506010501170412080c04090204080a0605060418030f09120f120207080c150405060412141209040506030109 77
    0x4045c1c030407a035090b80d44039401407110804013040c040a8a000d40140c0041101c480040c510591710f68003c06000030010b07451601c0c601c5c1031036800aa010b07500880c0c0218503820103569101c289010032460840b402c2000a940c5103030305a9072003603840f50385010000c0c0c000c0741007080030300c0e4025090308002500d00c000502d002d00d400c585903c030901821b4007288510740b112035a9021609964401c540c00800d4000102d03c3c2e140540b20000020170300e854880d0300b000081540511800600024560703000104003264446c035040c0c0c280c840082915009914092102682c1d8902600641c003594150600d01c0545508010490f000802d9802100344c6031103a0241c1820000444074103d9aa40100805040c507454105c080340c403110f0620036441503a12024005a45180c518141180300c060300030014a01340d41c0310b02080c51604280d100000c0852900d9100041c00414029040c030b07142c810001c2e0007001c4c1d0101c10b01c0f03c94024038440341e018a940d0000070342142c800754028006203820003c4000040984 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 546900089 1250 546898839 546898843
    0x803090607020601080d0804020103150f06050405030c030a030915110a0f1406060f06210c03070f05040510050c0f0106081606210e150a06140f0901031e050f 69
    0x107480c0d040040c03140c440002100d51020401044ca03154554a000700c07500d070b5400441c054220101c400d8a00190038000046031a500c206020050406840d1a92100c2c5400105420701400b0441c00b400303500902110400242d10929103c00e5458522064036014028803044409a01e9003a40707402c584502d5800c0e10600060070340c80d06c0c2c0c05110712410703c2660740540266071a86403d03500c06820043c03c1300c4980c190300d406005011150680d650800ca035240080101a5000c030588203404c2400002052000043c0e100b5211440c1c3c2ea102c1c14200e10342840e0001083c0d05071144524402044004503803118500014044030a284040000a1101a4560b980320f80c6521062181c211111110500003420b079005a400b810740c0026a5100300d01007481058080280100208404c407030300540031462240001c5e982568050f00c1058000030310b0324102616502c05902950009108016070418044d56545600b81281035030b50000c0800c0007110f0100320480b54810504d4020510300a41007031040d08080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 546901339 1250 546900089 546900091
    0x1f080708010f062301030f11030a05070e01090f2105010903020c010305010906211a0108060403030f1404060f060f03030305160504031505090c06040b0d0e0304080703061808030906 79
    0xd99201000010396403c0103501030300150080341511141c40c14014545d60082e48600900c0403085804121488a040e030300e1a544c0c0102c0d14401c94541d50303814061400e0784049800800074003824920305540c00c017907241c0c400408a2045030640a10050b03840e141ca00903034011600301e03038480000e100c0e4904514010b51a4924504042d00192808000080b0060071f4040c4800301ca4440e90003c020720354030345e9080708480c8540410b907a80240c02d20400c03068000b044205008095a20142010b4207140c54000e040c0c0c0c4840440106007130070f00201d04070b00843c511b8056003040d400040002e42c800b60010100c081c150542c02220b2a01103414000241505904418414040c82c860008a0070080b902510603003c1c83c040603204900b6440090640c40030340e40b249410180b03510855010341c0381c1c0000a46183d010303411408081c0000700d281c8445082c0c40c06101c02500382200518180741c1402e40c0725a54800c07a104c003410198880ca003070aa441103000540b18002d4100e4105596890000c0a00341d0342e82c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 546902589 1250 546901339 546901361
    0x60201050a2d02070807050607050301090c0201060f0605030402040e010f09061407020c130209040906020c010b0102070e061512010b090907090303050f09040b120723091f08070801 79
    0x400c2684460724142c03000b800d210056880203140c101c2c4220301001d24000d4014500482d000c40c420843e880100d807081210303a11500184e51502c1e40e81d81413140c40c00c01e50b403c00601e0415681803100511210140c0900c40d010344005151882d00c9985900008018280c0784008007081c1d481c10096000182103500203003840c601507a0180104078000000c0c0000a03821a298070041c0c002108203046858807095482100034141000b5080507881c40000701211440384086448690000c0c08100ca080d081c0586940b140742400a441c0507882c02d0141d850100004003400d06c2640381000b448c2407041c041c0d05a994071481c0542010300c66840d00048031031540b10802d054450078043c00001d100500c245465401e5962650b0349904042088620000c0c94019000e5154429154400300d00c2903101d1820102e15100036000900c00149440c805185842c000200c655031202202c0310b030f882c580c035244882e5801440007282c1d000031250013010031408407029000a002e038001c3c814001084081501f161030840 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 546903839 1250 546902589 546902591
    0x30302070510020f0c0d03051c060f1d0103022b0b0601091e06031107060f051801020f030f0604060e040c0f0f03150f021309140702010e0703110f0a060201050a 70
    0x40300b880d1040ea62005414114202d551081040d1642800d045040a081a109060039800c003d104920421071a0710080704c40c410756652042080302a200e8040b28004140e15103901512020920001246000500021340505105c0b05140d43d00c4811803641042a08188a1621001034528250400f00001d031a0036000071400700022601c900b07034104088031441076250002c0c1d4246060800c0d40644240340704002094020700119010440ca8059029002004140040d1070300d0040074001842c840c12223400a140e01c144140e14412818008407500f1180c1541c000b101680c601d80002d0280c440da400408502c1c0d40c03030b418403041110f4090440b0680303074041401c880140c1c030f0f040cac0450003850b5484007500c50030700740d00280c2c08a4915480f100d0f00180e5550051700d010a040c1201c81000350507400400c032959100089102c075504061f4603608010548000e010400d55200c81587d11009404050b10070304003d101091550359405103681440703005844501c0741c0d83c4c4c4d0302c40a8000c0608840d600111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 546905089 1250 546903839 546903859
    0x81b0408030d1b210603150c020706030501050105090111030705030c0a140c1c0312060b0909010b093a1101021506030d05090d0f0803041707051c050d05010303020705 73
    0x900c4400d4800c0c0f032044c1c2d01c0c489004030880113507404c041d204c0842c144150b80c0320710100c042446e041c880c1401e04010340300400d0860300c1c1c0c04028038180e13855210008052030040140b007a80e0f8070100300c0340b80b00000d2800281c1d003001c1c2803da07411b6128a03078000b8410b00c000681d402c54410085100d0310418000c5004000b00c0031640220b6465692104107a5440390103425601210404900e000c10418000d02d000d624040d0011000403c84007a500111104013010405440350702c2d1074005140034040200b8501d0401460b02c01080d0245001c3c0c81c2140c01c1002e0704403202e07114919904030280c010195941c0100c80d07100341041a00c401c40b02e41583d0050044105c854020703110065524054000a001400150364400341113400350008041e080e0310580c00840c0d10041800488607403040e41c06548c100380d40c1d0509242c82814001c035855022000c450600103400483d00120b000a066404100182c03c0040c19400440d101d1003045d5401038150300d013500100038907500150500a07102c00740c481e0094 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 546906339 1250 546905089 546905111
    0xd030e01180b2a0f0c0607051c0509030d032c2e0507020d140c0f0708160503190615170c0310090809150f0c0607080612030a081b0408030d 61
    0x11501c41300310901403a13002015103444c9041c1000140561030241090703070b034080c4480000c199402c14102804d400a0707000700b04403026250a011202d110559410100b194084100d004450001c000b2503c0c201da81090500c0044c50100740201202c00800f144901303111010803250b00c41040444002c03602d80c40c5044c0c0081d1019000041800000340141c40c0c840c469801c2d603805000503801a5100c00705802212034441401c07070b04202000c05030002c4006004503902c1c0651292802100d58002c074401e40c0220140305d415a000309541c02c0c2c0311380040021503441c010306401c1000c80707101d61100c601e40081e002c08210050001c41c1071461004120700b5500d0100072a0004002d4030702d0804007500711002041108040e15180200c80580380181341401d05000b0201c07034480b0300c1c1d0072088001040790084400c00c0402a03002490360b600003001c941c1c1500c0d03068040f021543d40e0040d20480350503c4540404512040076204025503540c481000300c2d0b0f916070f05c80810719120741050312410710341402c02d600058 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 546907589 1250 546906339 546906343
    0x90c02100608030706090804090e0c03160f0608070203090d110406080610050603060307050613150206130b190f02090f090f04030c110418020108060d030e01180b2a 72
    0xc899010b07000394280161901c800c0f0040c00304034000c40780c40c80f040000064807001401101040b20104001d01441c003038070301c14181000c10351030440540a0040000740210306000c10b0600035103030b8030b1a0402041c0e440c580305a00d544251b01082da801540c0311005000c01428a00e011880801900d05026542d5900f04456440360161100328040d41e100009103c1d9080c810091540800010119115203a407040070821a40c0310760840544424800700034403480401e04d40b0700e0794040701e600c001d00303c9241180d041c0c00c1048d080b400c01002d050403400480c5040c02125070181030004606410402240203035450002580020034043c01543e000d80c0b260803034900751103400e1040e884074100d48900e5941c1d03a8101c40c206c0b101e81e0119064900d15030a014075403620312078606046032150b0f241e04d02d99400d000140c03110400601ca0343c4507070240182071001076400410828a001d0078200030280180c015120580040d2540184841003400b02c0c05040711400307441c000490032903100f200d900301c03418210015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 546908839 1250 546907589 546907601
    0x1b0b06030d1112070f060504080909070206060618010c0c080115090615032d05060f0f102a080a0905060a0f122306120a0201020715031104090c0210 65
    0x8141d030061800300c18030183c010000c022140c81403594641c00140d550390300c000c9401c10388050724025000704281d41281405103596803c110503000030309275441c01c0d600166407881512003500c580c1650b1810522582d0195610b0010340d0350280240403040d031140c031414001d007040340d00340a004a40031400210107980340300e400d040d0b030801004da5601c500803210035009802c00361811440003210807604240c1004201c110b5005090350b0001040908080d0100304e400d030b400400e0399119000f074848082d030b9550741e11107400d450445810104a04030941d250441c41001c0e03010100d8801d001c101103581001840b00040600e5003143c4c80e8140b0745030b10f48041c0400382c050486c1d00780126502c6901c0817003080c00342c031000c1c50380d50801c41d02042b81e0a05440003e007020f5241144101c1181c0e004c28002c881c6030100c1009810b9a41800501000c00aa00002c3d5070b01030b03a20413540c1e46512200400c801911a40240e01000100317840e003a40c6550b0b5064100085c40340d42600c00041c002c201c1000c04580ba0743c0101 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 546910089 1250 546908839 546908867
    0xa021b0a05010e060c12211006081303030e010c05030a1503080d0e0703060c020105061008100302131112070206070203030f0105040f0b10020c040e010e060f071b0b06030d 75
    0x36140c0c0e0f0b02d0b442c14411264428600000d40784240e696401c0710140c5680200b03161802c0040d82d086529070007281c400c0420300a03041c41c00030b60114101b03001d07482d4000f0322968080c1450303030441c20101442c01c0690003010350b103c041425501f42100000c1c0a80c100340114000c907542c0d20200116407070407500c0b222601c80c0d400300402d1150104240280280c035a002901c500701307100e06540741d103641da541d40011600707150000c1025035194020068140f802030b402105103007880c149944207241038010a850130703000d400000d10500311120016021003960303100c0d481a404090242d0b40e1200542c144501003d0221400d41c014401d40000424040c07000c025203019202d4142260a640d00f0141003001914242e501700d85141d41d00e0f1504092652110400002007220741c000e44002010181840191071404403078103003036130414600d40d50402c2c0000710710794028640b11280d841512000c0b000c441403501d448100403a20001e8080d0780602640001480c05040100c0480fa00401005000c4d21280580185 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 546911339 1250 546910089 546910097
    0x2070c0e1014030a1e1a0f04061506050a03090c0f120209011409062101050c09040f02070206040909021207030803151206160c0506250801080303010b0f0904020a021b0a0501 76
    0x80c0070178500c1070940c0104440c414800300c54140b6a42d00e055420000494400e0a1002568180400c0c40941d01c41c0510b0f5001f25003a4002250401c44041c19074401d03105101d0426584146c6001801040340400c0054201540f01c403014070323640c45010b450940c181c1ca05a108014000c00095011038041a5000581d005848241e466031034604011031500c40c00c54196684412032a5640080000c2c811244101445200c0540b55080e8205010494a4040421407005d1041180da000359407460705440403104050400706444c1c45510214040d090541420b081078407908502104116008004c1d601c60007502c82d4000710804070303004112141551071480140c50b04030030042541ca0781c2100364051141681d060004055006940e1145050002c0310940c80015203002e4040d144520f000030034030480d45900d000300c6554100031300c0507120f1106114030642c403003000070041c2e2a0342503201903400100009008646403102600d019440d42450b0808110030186100325032494036005600c0005d031101030751 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 546912589 1250 546911339 546911363
    0x90806010b07170a08130f02040e15010b07170a05130f090b0402190c022b050c040203071e030f0c02060406060e09070608060a0806091e1c0302070c0e1014030a 70
    0x40d084109906007a42c2d2603035021f150001503201c0e0300030b2401040110f00117241d050b00150250071b40200607005015221020008140401c0c21242d9400c50341d9404034080b03a444031001e07801e0300d0328811034030100c03420702410100145400d6040b03070260441d0103d000c140400d41108042104034403070007915400340e441240d02001d0440c814140d000d00c2c41e00c064140d616660103132044102c02550b01070002400070b840c4000b00200202440703040400d8005075010740c19400c0600000d4045101080420342e07040d840e00810745610f220390824070390307081c0d15002001044400c180080d1225000c4406440c07103420500002110f02c80340c0c44541c032074031080c07004c4e00000b414a50200d404140240c801a4803046807800030440d0b0b80c1c2805080d006003070f410010441854149600201c09809401e0b22080b80c00a03140700c20840c1c042505d10000d42d04920b0016503d01503460300540000c07558000c2e607911528001004001e1b50200300600035904040b00358200d200c840c8042503a1001c1245c8001c1c21007042c44 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 546913839 1250 546912589 546912601
    0x20d0504060c0c050901090b040e0a0218130f0303060819020108070e011211031e06010903031407060e0d1701080703141905010203060f010314040b07090806010b07170a08 75
    0x710007205968443d00300c2c0220b483d6148002050081c080c1c002d15031071a42c1d240501414a41403085c132983d0354220300a84280183d540000d071050412510fa810401c2034a000249411103503001c94a115911454560b811325850800800402c624060740344c00740308420048003d468400410b409040d07050399280069507900f0300803500c1c45c01c041503803410b00202244068140b1014040d801007110980742413607d070300c0c01c1c010590720070302d81d6400000618108414014140da10440c404281c035090b050242111408a052488a01c14208090b005130310300b6402c13176412940450040d0082410799505014165000303c0b403c20081e0a100d0110154082c250410000341c0701ea01c0005100c840740d05444900300e901d003000e461424031807401c03a12a503000081145c3c80c50b00000d404c07405a801c0c80d003000103100290820740e2140c4040c1010307011200b00d400044040348504e481c40042d00101c42a00e0155070745010b892035607003110600b262814818880c2281d40580c04040e9200e8100c15920054103445207 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 546915089 1250 546913839 546913847
    0x2100c02031308032d09120105070f1701120f020402130816060203042c070309020414070f1413060e040501082107020d020406060c140f1510030b0108030a0807020d050406 75
    0x5211750443c1d11420301005070b0658030110b0b07003660101c0c3d420011602e85031042009000b40d940420040078420a540a51241c071a0034842c00d0646402900d90318031803841e400c000150242a41c002580706000090541100541951441c110740031003040741c01a940f88100c100c0d0b0344e03005014070340050744184420408100012841040b181c00090080f0045552007180d0848000440d101008603172034202441c118249849080c010300e4140360507030f0890a01c07080040c400442d203010742e0104088007411140540c540801ca0785440c2e0340300c40b040e807a560349203401303400104000c9109100d50b2a10700001280d01000c1951910845045410820120b19500400d030507003068106a8000302c00c3d43e82c3d040140c07100c0c070a0754050002a160b40c21325641e24901817107208080c107201d18240e00701c01c3c418904800001400006150031285008840e6100c0b842d500c8181129400940011007d900014170030b04080024440101c1954070050b4070b030785d15002643c0c1c48007e91203039000200304000800c0340d5489 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 546916339 1250 546915089 546915157
    0x60313020f0a24110c0105030a02031b04060e0306090303070c0210021002030c25030207090902040b030d200a020a05040903030f0912030e150a0203060102100c0203130803 75
    0x10034200c15151500c900c011001011200f4101c0c009070210b8030081180c004039070001c01d0054000a00700203c110000a005020280ca40c103105500840842d80090010700110310b640f103440541c94850f9540d020040503002c44003000c03802400307107101050050402200316842089581c507804214a05075003400001d9040b040b5020071805941c2e03281c507642c6a030740004c40c05030301c6c42c1c0034032501c0d280303a507005024270714101c0130540003a031841c428400000d170086145d0049a05006000843c040b050004c600a0005002c10381ea041c042c050901c02142d400090203019816044181541c56154444c102e070703959180640a540640c21482c10005413600303400540c1000d2280c5800304101c031921948005032901e0b20002c807425450000f034811025854818030340451041d90050901d08140121140e00c0a00a02a03501582e0004009400d03a4000c20886e503519078a210200704091120400075120303080010a811441a14500050440b034000107803802c546000310509510512682e407014a500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 546917589 1250 546916339 546916369
    0x50c040302060f0d090c03021c05060a0b040605090a0204030605010506040b1e0c010c0804122c011e050309060109140a0f1503050304170321060d020d1103010b06031302 74
    0x300130040c20310b0003621800790314801c910a03000e65244a0840c410031044001100c4c034040703056002140400030074000541d5580207400c4100000d40352620202080182060b40c21298000004a06003d0020001da00030400c8074020f81c401c20071a601d03642000924805ca01c02e0010640c3e00b40001107103000f1402c1d50074000c5988074400d42c038160103100a1800d5842840c06070000c1000d400402041c031000420344400c0300b10306d18000200151070700555204544200f101800314020104102443e40a420000c0100c00c500045a041c0d47c401500240254012640c03c880c9000d82000001c1015540c05108031a401701c4600b18120340d0f801900d00020300702a4110010940c44408011300300011000b040b01940c060307c00742d503403a070900c540c03442034464013480c540b486c0d441000f00180d420512011808842c0d000c200344899515030200040c107943d11044040d41c09680d0182d81000c024070340b0403101c0081c070150000c0c0601c201c003004114041c0402c864410800d000c9a80c040010315080990445501e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 546918839 1250 546917589 546917617
    0x90105072d081b0c101815030c0e030d0c0b0a151806050d0218040501141303030e07030c060c0305041e0503060603151501031b03020a08160518010c05010c030618050c04030206 77
    0x11f550390400745180da04820300c031310109695000b00c6590550080310740124804c260014081e13114041401010003518290160051152101183c4074210316003058058008405403415903a8455403034121005514501031065440c003040059203080000a60203000d030001c0120100304440301060040c4003000b8011106956200040800805c4c0000028012910075030a1015001d0900d406021510f0400c911101e50344800001c20003d01c1c060f1685085e00d5036840c140c045002c2502e0151501d0181e50401e0710b1013420b150300841015001d1222100310741c0700701c08580c0d50783c8076582030548418548090152140b6031100044d03040041e6030780760462040602d800908900001441c068081c00225541d00080d00040c10780a025808a02c141e040114080650309121460001a00c284100b503010301c800c62606489100c640e001d45403855000f50420020b05c400d8906c00002402400c441c01240900c078080444440d00008903c00c0d03030311030041c1c00c05561402c0d007036408010b10b03a088008890150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 546920089 1250 546918839 546918887
    0x203040b280f0e09040809060702060c0f06190e071a0405030303010e06191503051e0a06060908030a12020c0a02180709050105090105072d081b0c10 65
    0x448190034100681c04082e64421042d040050b40c0184450040c00c0000e00ca0703510041800041900311048500c841800c8550b207660b403c1d0392000c41c6680c01416841503050090814801c46500007180e03451107082e170405007500300d0701c0c1204084226020300078019180c0d80403043c180042d03904030820301d64006401c41c950b81095550340000e403075980260042e1525001250510496050a40180708907008180441a0b0141403452540d20f40d031f05069550b04242d25071020900006003420140c00240b0a01c203410040e05c1e100d900c0201901d420302c980c9000500300440011a4074010099403103101c955660202480c510351a0b24000e0b4001e40c000b29080c3c080c103240d04006a4030b01500b501d10940d51102504245040040a0300510080d032000303051000c104035002c2581c1c5d100084481103a032041d40d080d8a078045030800c000003600c15000c50402c0c0545241c0d1400d200310100a4a101c0d4401c0b0003103420084030614013911050750608160300640c444140c103a8890054014288203480c00908a0745 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 546921339 1250 546920089 546920137
    0x601030204090c03150b030403021b130c031a030613030309060f020307020a0c0609030809060307020a0803090a05070f0308030103170702030706080a0b0405010e0106030b03030910031b020d0203040b 87
    0x445250524590104e81d4070f070b41c3e08020328992003142c0c000700b00050740c0506500c0c154030080c0d102c0b1008840b1505031164820320700c4880c1c0c2c0f0100041d61010b5884010018660750310006801801850042d08a00c271641402c80202d14001400510452801c1c08021a81c5510f50303040c0c01800f8529000c4070070a86803414046940d6252000e184a82103d5006240d42001801c155800c200160041410840701d9542480400c1b2524220344c41440155400c45d500d0303032200c6040381811040e00e0300400f03400001050080c0345c0d00010781c0f40f9003540260191540159907d18458070140b19120013425280248010404140e003101e400d0050301340a22000d203080400e500203030900101d5000383c00810f02200512001c00350344c1c0b10305075078000c0079502086154104140c4100c0074074140304400c20192110146030454070f01344185c9075942c1c809080390b038a035102c81c40c000c0c0181205914408940c19004d00f4941d84501c0062920000c13500c9401451405003080484440c0e45d201c0032a02804a2203025400e41c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 546922589 1250 546921339 546921341
    0x50d020601150806150a05070209010b0408010b22020912150f13050a02090702100204030804090e030f040509180a06060503060106090302011421040b0a27020108060103020409 77
    0x5005056014050641c1496895070400c12110708141c104001101042015181c092090081e81c0191003015200c0003441d408588900c5a0300f030082d041942080000781110382c3d2001b400c1038403c00340c001c2c4070082e045018003000c4a18000503d031038030501501c80c810445180d0042141540c0900790000c06007416200600d8014000c1d409100d50303000000300b0001c60100d46c002d1783c102e550380d040c0340060486034480642c2c0d0102c010b0064030542c0071a000c200300318020400c2d0580800071110654450756071317051000440c1c20620400c9640d17404c00c90316640303000000c0200c4141020841e032982c02c0c40d040c4410300030116001050410380c9400411090341e052010000c3c070340c2081c840c40e00401c101e81045d05040c20000181e100380180410001d041c00140c1e000030320000005401940340f5164000c49032041c1005030900d02c800c045a40042c140401e021409010341c1c8200c13554541800050b0000c28680c0c03600d5102100c166520b100e01f401100190310030840603400c11700501d0054105611064410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 546923839 1250 546922589 546922603
    0x40f05010b1e03060a05041a0a0b0a061e020111030a11043302030a02121303020d05030a0f0c4d0a0909030516060207080d0c031503050d0e040905 64
    0x1d0001c26000c9210005440c003009a90b03403091200c5406d00c50303803c1035030710610800d03942c0c12030600114a0000040c59800310b940646011480101600c0c1c0700303950748030042c0200c2c50385035040c0840c002d41d05407002a00e005008090020004858003891035407048070240c0280400d03003032404113141c100070001d92741040241d0400c0511f00d0303500f404401d40350b00052a504461204054040d50018003040c1d1004d90046600c2c80c1084840300700c907946003e00030b105180e07402c198100a61022000e1645014000d0000c0600b040803503684411051000090050f1000624211700401c0000b04001c0b12002400101c0c06845030181c44105c98480c0141d1145140d2840040020030141d08034a440602c0925113180c03084018000c01c0c90800200c082910003c2051040601c0e9401070312010000c3d400f042050303070450f4107454106070000d84500c115074901c00640040303050400040c0c00c00f02e102d20085031542c443c50403079600a00800d008242160203848007500c00c0300d0f055109580707500312004684140449 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 546925089 1250 546923839 546923869
    0xf140a0f0c1a1815010b0a110c06070602130605030907060302071a01080d0f18050d0807120206181501051504180501030203060709061b080c01152903040f05010b 71
    0x40009400f80c10f40103031034085403140c2c9034600000c940040100d480301400b100c089142610f801114801803501d0203141000340400c0e103800c203600040300390900c00168090f00e8442000d410f0f003d1030580e0781c46c08480318002644c8100607a00080c200300300a900035070042803014031034944c0c201d850300300c202d0400b01004240c2c070068854101040303c20069a00521000404a003401c0c82100603c2e03c800b200c24910b66401aa0f00400103c0520814000d140040e05c04081d404100c1d50005100d401000b9103440059800d0005010301c18034043d40c0c280007099a810540000240c03071328583c40c000c100640181c600121a4034103400300300104404001c40d01c010b00d181d040503408203981d40766105046c68107100030814001c010140344103108041c0d20000e461080e0025812307813600c010b45030804894610400141b56003540c42d014003103941c40f0030000500d044581849c503048084004140f4400c40071000544c1c039072415400c01c0080c0002d840c000c1800a813031b01480000455031104408141500c07000c03100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 546926339 1250 546925089 546925111
    0x90303190e0f011b030213090e011410210b04120e040e243c0103031d060309070605180910031e0c0501120e0601060f140a0f0c1a 57
    0x165101004020342c0e5113503e101c207280440c5804c54440c0e0320b0303892010600500e10b4840d00c41c65004a02c038025002071030b000f802c1c0441101d2a05101e18043d0602c030340c91042494052102d40c50750b40c42e012002554103440e0f0022107200ba903035141d6071110510910380c40928140289404201d1f007548440c4207542c000c45051005151561040703c5003018001280755090215100008001030f20010a82a0307070b00c0c002d141003142803021080051141c0c42e120842c0d62910901c004000821300d40e01005900104860f030303c8110300042c440c002d0003070610040715039029035840f00204000c803910410051000407106c0c1807900d003040a503130019018035001d4800030500040002c090003070218041d0300080540c150104240e06003810f0b9205845d080302c6d0303c505814010b80b5541072465200700c0d040810500b0440d815240f0643c0c540e60f000d040740c1c00021103200003450440442ca4918140c108403490028940c9800c07240c1e280c07001040b070708003800c03da00f1105010100c002c0300e01440038080c0c40c0d01030083d03100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 546927589 1250 546926339 546926351
    0x909041437021507032c040e0d081314070b031006050a080a0c03140c0a020c060301140d0c03080310050f030d0e090603030f0301150f08090303190e0f01 67
    0x2101c03402405100c0c00030800d940c1c0030075040340103a4500300003086441450b01c2c0709407a000740303007415161070300d41d140305078121154010680f4082e01031000c0d8580a00f81240c6c200324016058100f15603440360340c01e40c0790104500c50301040c50000c41c1007040f803c49101e00160403060340b50842c1d05040508540c01455500700c04014800714024070324449024001c2031410b6820b003469810b000f00754407006442803030f88566a161007800c080c1b00381c0101500d101c00041103e02c504080742c0400c2c1d03950140c0700c80b0006014010800d80c0902c5d0030070450341202c58809010032041160b404018004e0000d039000c5032096401e0300d0000006440d20b0155209803513469034808228541f4043c00000740310b692525100f03030440800142c1858100c05403111400f000d5402603010342d1510301203851031084d01d034608107840e03000c80002004070607034889898080040e40c0c0c0c444901ca044030151840d6200743c40c2c8200d1904103000091080b42000515170b2045490240030038003105c42d41d045414115000c0e0030b658241d440c3c4c0c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 546928839 1250 546927589 546927643
    0x36010e06010609120c0b16050a0506100506130306051f0806010e0109020a2c03011a040b0d050d08090304092f0c030a200115030c140609090414 63
    0x801000020101001e90301249081c2e9034810f20a050940146c41100d8001304c0c1c58115413103850800c8642c241c2c044100d40b20f14409040195843c0c0003120041c11400010001040c0d900f001da040c0e4070115104150003100a06507907505001e00b1009040b00c6101102c4201402c40030a4070342d1070340040a2601c003400e0303075505180c0c2d50094084142c1003011454010070a000c90702d644640c03181c5401c500d2580141124411120348490000b032402d080e40c0c10360030504401003102004147c901a03410032281006505480e40500410f038a00090180c000d4103c10080340145005095055103d0201829a442d145c0c503000c4484c222070b6000240c0034052110030000b40f05101340c40c92071034030034902c00d83c89080003d00b41d00103607a8400c401c1030100300508032201c503850000c00d000c050880010140203200c14100040c2c15400000c0a00c0140c0d40c1030030300036002880d41842d003c1e40d009000d01030151407914400c20188402c42a010b00300f06c034146484a402100354a0601144c40c10411080c8402411520a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 546930089 1250 546928839 546928847
    0xf08030c0a03050a0507120e0c040f0204090f18170405030604030504031a2502030c07081f060b0a050705190605070e09090c1203160804090c020636010e060106 70
    0x20a0640b14034901414440119000100c47c0c449121036030002c1041c1c030700820b41c141003113040341c41a60007074108000141c0c41ba01580240c01541d0803450100a2550351010b50f0f015580c42400d55109006000011804200c5040040c1c80400c0034240403403903c4e54540c0424035100085400364001170700400c0500801124440c0d8518621580e4090592400e00c2c106a00400d0150185209000c0076419080301583c002d00c1500c03071901084060311802599100150f403a00d007454440144010030070211010342c9160302c99942612000c01c051030803d0fa4004043d1283da0108c00c0588c2c29100f00030400c0d48010084007003c0c1201e00c1554007181c4c0742422036010705040d0000460a2107038000740100182c4c00b5001502031801042114a0b80b0b58684170809541144203840d0707240954056044641d09121f941c0c0003e0080b42c0d0014020410010701b010102e85a06043c0c030b1042809043d01c2c5410003805604c101c64181502c000701030100103088881860856019503640c20141c2c000e10010401c0c1508 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 546931339 1250 546930089 546930091
    0x7090c08150a0512010b0a030f111906080403050706020c01060e090a030206040807230a0c0918060c0e0303070c0312030c02030a0f020c060304031206050f0d0f0f08030c0a0305 77
    0x1403990a031420400000018089802c1801400e028a80c0c4035695030581d1004d4020944490025200307403801501c0b81040841c41100042c151841c04011040f880c00d07060458041311000c1640950301d42c41e5007080c1c2c0072180c1c800042e00c29070811000b0300030700e0041f454a00c02031080c0e4140310000110207240c280d525540f100c3c010400a80c0350029031880020940218a19501c03980c009582986e825031454100b42d129106450028181d14180e10910000c40015100c031006000f2072400500030f903140c000701c0a581c0c0c0440261504034525440100041d501d0708040304051a508100c11165114000b0a02d03542251005448840f4240001c005002800e030584c810501c16140c10f1102c0090070f00c02950768460b0030188410420741414015017039109200e1000a581c000f003a10750b07641070600f4018041c59146200e291700e2840c0020020f0340d4a2312840c1201c8100000d0103000d1001d80589802a645081c01c90580f18544940c03910400651000300861041320f4401c0d09545403608548020f040b00c038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 546932589 1250 546931339 546931351
    0x30706050c0909150a0509041b03031112210403020a1b03170405010c080f0702030307030302030604050a060f090e1509150f2818050105060316030818030f07090c08 72
    0xd803520313518425250000400700b91403007030700e00100645031031034404c5043c103100c080d14185901d100707000320415a10840ca40c15181c01c290440b050544178039085801c0e0301c01c09011210101c0d20802514060500f021100e40c054040d00603505042e0607500d403502418541404404050030b045001e204200e80304e400da0740d001d4003c3c01e1b4681001c0c00c107070010307214030442413014100b014003180c240c60301f40050b4201ca16040d03014091b02c0e114000e9141c050041e41069031400d00c154105000910480d00f00c0c4160422101e9528121420728030f07290b025030082c440030011003030501a001150450500b0008154011460b9100600b40a42400c070f400484000103404400902801010b2105582107120046910f189690f117110202100c14001703001000070f8410603555444441012043c0b100c10340c0483d100300c00036801d444107031030041807150010304240401003c0702c201b802403210003107031601d40162910018040345c3c3c80785030102800b8900505c1d0f501c040d000326198a859030940d9480704060f5000740b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 546933839 1250 546932589 546932611
    0xc020f12041a070804030c0e060414070f03020a05130f08060c1810050415080a0b0d020d0b04050a0b0112060b0a0b1602151c061505030117030706050c0909 68
    0x2802c1418602d50b04940c035003541c0240d400411950203100540040340e000f551301440300b0210315941d00c941101e400c1c0031100503114514010804a484076061003182c4144c01940c0e4032903410340851000d40094005d503415004000090080e04804100d001c2d104018201c48684001e500d85010107407840c1040040992010b40d20a0018000c98544c001072449070b140100c903200d01c546c1c11050102d4240c002d56000c1c9075400b0a510444402c00d4000b0100c40c01900780620a20031940308406001c205c012800e40250441000c591000c0441c0311281050b41040c822000e8581d01d034440d890f000c138086401c0e0000315980c00321100c0d040401c00382d440f9000440c141174a401415030700e00302841060340910104400b5100300d1480341011540c4083c000904044902041d1b80c0380c03a1a10881000c0300620f01c2e4040b45646464804038081649452042ca841d03040e5903030030b1542c0e017016264403500603034800707070f000d103100c1031102400203416400b03a54030034003101503d21b8440e00344908000aa690280140b0040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 546935089 1250 546933839 546933847
    0x2040506041401150311030a0c09080106060f08040203011503030216050114030109051b1309140c07150603020d08090f0f151315020102040503070e09060a1e0c020f12 73
    0x42c03000b4085283c1190b016125030002c204c000c0b10b080d0090014901c8655086000200b0400840b08580c811407500640c2c3d5511761507143c0b60b0a00908841c418059480032803c0220446174aa00c903080066104d840078002150004855070846141001ca0300100e0141c0c0021010708000740344038030070f0001803070246040600d468203079502102d01e202c10f020b0040301c0c0b41c4410000d12403a0f08180443d1300002c41e80a559034035a110340c28007802d00454080e82e5039650410f411054035162a05115008034498000d6034a003540e242d8546100745080c41e440b101c05510b818001025a540c041c41d100400c2c003818165640e40c00fa02c040002031506840024401c844043c89050983c5446480c10135542e074003484260f0310301e0703200c5c008a20300300ca6a2000c1c10130011220580041c50303040d000f80c01241c200742e0840307040a0321520007245412084034032101a5001000042c05c0741c0c0c0581010708802680503c1d02c0701416a203035018191160403c00d2800360b8480328001009420800004100001c855032507424 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 546936339 1250 546935089 546935111
    0x7080a0f2c09060d1a06040f0506060d0905070e0106030902040e0319030b0301110408010204081c0e01030f06050d05060f1b1614150702010507050703020d1202090d0f0204050604 78
    0x1900101d40610741c01a20010005069500c8241c40f949445800070f640f403a407110f4420000a15440031641180a50b00700700060401a04600685004e00303c010910740c204203d07641d800000b00039181c01601e40d03215203400001e83c2580b02115601070403140c1d07404290b41203503006000031354200003d03401c22a8010000640e031000e5515000200354075a00d00030030381070307036001c002800b4001d940d1078100307103050009000620031415801001225406025101e03001030b0b00e000c01c1c441a07047c2a039200030031300e0104d42081562295201d144104c0c5040c00002b8400e444401007050300303043c6901200c0d03d81c0f1040a010f4140342c121143c56009032004c00d410079012281c80b101d0701d80e02030440a1501e62104c03c1c06042008410192158048031410031510112099165408559402e5074030001551034440070400300e03841201240e85031178140d001070104551000d001c894000d040c00030125015030030320001d0f41c2c56850401e034505ca14011300c0820144c1d169401004111840641598030451500302da28032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 546937589 1250 546936339 546936407
    0xb0306010e04050a020c19050f061b0703200102130807050a090f0209060a0c0303060f0b031801060306020c15060a05030705090702190f050d0201050f010b0f07080a0f 73
    0x103800311040c2c40116003a142c420091004c3d004241c151203150151091002444050104030601540980100c03040c0c140c1c400d501c01d8880500f5600b100c0d00140b1806094102a6800010b00d60f0030311074940000d880c8000340024041c4210050504400c2e50001400d25030805100806005800d555000d00f000078501000501100010320400d512103894107000e0600507441e030305482e00814040c103416038581020200808641180700c0450100b403070f003c004605080e035520b094041c1e4103030140c1b423451600c4a20042070b904014440c42e01d00e0b0364a54202000041d41800030300005407a0400420102e240446803100c4550004c2c9002e01a00400c84104801c3d0303000034404007100c5069031100081d4441d40400c0f41090074940100740c103940b050b0101c00400000300c1280401900407070541c0c1522600c01c1040b405c1e1502a284403480c0c5009600520425011500030b1080d5244104c0c03075480d00c5541c0d0386103451030b00720380da000021900c60200600d07400d400100984684c038024110007030031080141459 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 546938839 1250 546937589 546937607
    0x16060203030703090213061706090307030c14010912200f0d05071a010b0403110d1208060d020301051f17120d1814010b0a080c09060103020f03100306060b030601 71
    0x2008240d113400408041d501c41960120f20007041c18014086c041e1900052607640e0480302021000e803180300000351000401106544a243d4181c2e00e640c0e4118444d22002c550f44000e44036a00c5555071003440600145111024400040301a12803c100e90b0504140e03c4015a003901100c1c800e800407480401c0354440421560080c0f00b01c4d003002a2561218105550021602c590032980d0100040020401c5102100a0000c90f40319082104004102da403d1103035601c00103800404a660304034405064030300522039075a014401400c0c09009480c5500000d09450098a54400c03206404083c02a083c0c1001d800e60003502900782d02c5080c000d0302c80001981c0b4200249202c0c2c2c5001b020034504032401035904544da101410b802440883c200da03091100c074600e0380da20134050540c41c15060b503c0724105600c2034811640300320003920490012006100454100500042c10154200000907810518a024500404008641c080342606501e001000c50310681c014000d001c0b002e0080202d181e80c806608 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 546940089 1250 546938839 546938851
    0x7050a06050415110307030c15020f0306041a15030915060a03060b01050f04030501020a03141504110708212a070203100608010f050105090705090618150304051606020303 75
    0x740c500110600021a00310a1180d0360030010b01000450200b49980302e5482a2300070700445007032807001e0361294050100c0c402d05105201c124014000a2818500b40d8014110724213046071500d00b0485020003e0a443c502c511402d083d000040280100d843e81042000d140503204151600c10782131078070020780090340b035100084c0101e80f203001503400c1d41d10501c01d4405551604454513200c1c4d84a21b0b00d02c0c041d4101c10002800a071810641d001001c45214a050080462001d5114403040c00b00c103001c090004000d030020010001c1242100040411008200c0d024442c86040403581c064400008130a034081c2c02c0141d81400004140164058411070101c1c0c100600900b40c2d54a44510201e0b0803c10641c4020b21a946801c02c00900003a06402c2440035408042c0b04001a03a01e0341c040000044007074a5000000700288556942c2e4186500103101442090b02003403040c5528a0014284034000e1011040e910008000d000030020100008144008104a03045855051160007990390000a0030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 546941339 1250 546940089 546940109
    0xb030f190303060803040303080403020d080628050d0819031a040b0d0614011406070b04020d0206070c0602033402090a1d01270b04030503040c081c0207050a060504 72
    0x1140342098003d80c0140c000b40140001e4a4039160781e4200075044040407182640980168101c58121034492031150740300b01c81c01064011b610045440e5503c98050000356a006903200c0300c40030400390748480710043c4c018800d0281c5d568031402c5542c21441551846600c000b03050805185c5420065400c1d03030201c84450589000442e041ca510000380035541c0014090100d46c42c10001041c14003441a107070741a6150301d40f0707500483c402141804207900c41c0405c00f901c0c61200798089030051511815417420b42d40010f00f45410f00c40152210b00b680c22907640b002c80580c1c000130310340d00c01501c000a04000c0a07904c50303076444104d40314100710302145100351001344074202c000001410300a03135900100001d00c0d40f500c00c005603181c2e041a54001c1803085c5010000d440c00803540200c005050485001c580c0c0d0248210390703151100d643c1911550000b810854003032000c100c020800c8442004004803892851a0098400d40c0040000c1e04103246a00b00d28020300c21074409000103500704040314200c41041c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 546942446 1107 546941339 546941383
    0x30e13060306051602060c2b020702040b15032701060609080c0411190302120903070b010911090114070f0b0a0507081b1303081b010b030f 61
    0x10100040c6d02c1031000910101021000d0480c0c020b100761245e03138002c070581c103620300e035a8550802d20007240d01040c2603041d0320f0b15004100e0b0b40f02c000c4e00e80c04e0110300b918034680020f00c40107280c0e59510710005d2203102d9145400700c1128140362002d0081103e01e48031a80240b61600c036100d07204562003080e040c504680f50910a03802c14290034014a0f10b840c0c040d4031070300500b0300814008010700d41d0a0050007008481d21a001c0c0c41550800301850781d640e164542103100744810380001c480540703440074a9031a002500d0803544a607e090808042c82660034007030f85aa84079240d40145203280301243c03d420414580956030150790744000520035603654460459004404894400365002441201c04410080d00001d00d80750920116242d40c0d55165101c07050300b0340c0401c5007001901c2d04814000400982885125000347e03049024100c520364030300340556a907910b04049030f4010300001d = true := by decide +kernel

theorem cover : BRFrame.Cov 546762589 546942446 := by
  have h0 := BRFrame.cov_init 546762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 546762589 ≤ n) (h2 : n < 546942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
