-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4174
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:47:19.32031+00:00
-- url     : https://prove2.me/submissions/e4057a46-c45a-4291-8ee5-f8020565f1bf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 750539568 ≤ n < 750719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 750540818 1250 750539568 750539597
    0x120108011109060a0806040f230a050f011505160f0b09030306010e041e0c0c05070806060d23030406121109090621030406080f0f0c0301050111070305121b0a030e04020a05120c0406 79
    0x80b5041103406240d10303402040140101000150960b501101c0c620f00700e8540401d0141f403c15040d9440070456070206011c03c0e81e01000101c03400558403c050500440c158504a80001d0580000709686401140e6850012401c1ca0000d0601d21522504003410300007101041801081518802d43c00da406000760304001c07a8465001c61482d0040307038000c0281042d44902d8980143c2a0740e00e1075000d0050700421150701803d041400544001c01d900c1c1c954108001c0380e80302c0d00702a0340c4860111903249504000030fa8890b0b0f92880c1041e04004250f540d1090070440c520310750f03500c0301000b07142caa0038440890700080955000100c0c510540240990b18603580b28092840b0034210240c0305181daa48041c4014416544945611b02e0384010318000c50707400da03035241c036950b080c00c42d01c0d15010240308000071940c00a01000c000c41880c03020b007000606851503141ca00904d000344107034040344220340004076450218820400d554152003480c0403032580d03003040c145202c00c40e4410b01c00d5a001c18aa500152003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 750542068 1250 750540818 750540821
    0x20d0809090702150c18030604080d0e0a2307170703020f2d031009051507020307080f0f04051f120216170c03120108011109060a0806040f230a 63
    0x80302505880c0304d03059104c3d58a880b07550740010916016400b50032401380401c0c1c2d02000010300030340c001c0d4425a540d2035210000d000340c1e200200d10011580c000c074403500009061940c109440c5510f000c28100510b010040d050801d00e180d80003010509401501040c452804914038003268401c5903042c2411507072601f480191042c130502a14011070700f40f100c03034144594420100c203242c401820384001000c1c183d03400701220f129010a4031507502c0b40307040c0c0040d81d820030661a000b1586000450400303089956000305441888070302d422900c804034400441c000c1d120143d4001c2e00c0c009000e06031100700002010308400410064000081039003542a402140074821190019904120b400e4240505d1701d60008009070300350038901000080022084116003440500300a07405500300b495554940821070782510903204091040d0b02d410000c1e40125920081200d048030802d082010490b1b5800e80003a00810038008800f050a051498414140d48020240d803016104640e4202a03500d8444c480d90 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 750543318 1250 750542068 750542083
    0x3230414011d042a02010b030d0203040803070809031609020307031d0304030201031805010204080d2d0f0320270f13060f0b0d0c02010c0207050d0c03020d0809090702 73
    0x40c0d8803828100b04650381d05198104c90321808102c1d0002620100c03628600a280210325501c0b001030759500d1060303c6500c1c042c4006410807800d4030055003014240a41a41c90b441002c5004109540004418030151000e0151f1030424004803030b00041c544c0c0c1c0c0e001e04400f139070041b200500001c7c81d0503544824a5801c40c148807401400b403000f1800c0506650041d0010308000800f44981c41210200c00c0006109000602c0907140c100c01801404040d17883c0540000c2040120f041c1504113260b040b8808800c0355103010002c901e07480c0c45520806400800d4000342880304002c81c000c01380750980408a60010000c052010b040c0d2004c0701d01c1e04110030412591880c11190550001010121031000c1c40c20703041e0060040301440000501950f10020750300c2048003548250b10408001c20080481d480501c10611804503a00090000648880c0c00940351170490040510400d5000d14a00501c4682d0411002030741c0d0146c900e0011941c1418540070320f07002080024880c410040000c0e600324400f0441a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 750544568 1250 750543318 750543347
    0x18010315110406210501080c10080f040b04030c1b060e0f03030405010305180303040b01050f010804020d0b0a140f0405010e0706080703051b0a0809070f030c030f0323041401 76
    0x2074202428420201c56200e41c441300c0d4110b02c5100403100b0078082c2d06100700360084c02088010700611042909108204841c4804841407180c200100303c517002c80749070f1569210360f01c800380c0c55441d03032949402d6500300c0d460a13016085410080265030108078402d250400c1e61090b484056140e000c0504002043c042460784540540003400208869402a0050754219a07082041400443c05130381c19451604100c078103982c0d00c00c2040041000e41007103008810714840a28000041d40b40070b40101d00e6002d00350b000101200300e00400030700f9140559001100c0c03900107942d00c5142e814100f004052440e007e071400d80d504d500e8480c803041a00800661032040303420548401103c0d640e42c0310150014080140301000101d4882104c1c200030321404001c0c50019003d46500ca01c50800741403480c9410200d4120460b4460340543c00d00100e40b01c1d081500c1140e40c003120440c400002441c084603145006d02e01c0e80e0000382d120244020035001c0e000a001030b03a0f00c0c0c010600b82d0b002c0320401142e89516080d503a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 750545818 1250 750544568 750544601
    0x6270b010812040807290a080f31140709090c0b0a120218100203130b0a0c06050a0b09040b0a05090d12020c0109050d17100e1906030218010315 63
    0xc00021080984c284d080200c0768080300c000b00380c0c0781405100c40d404801018002504c0104101200c009a1580c90301319461a01102d014500e50b40c202c4038a100840300446411162b007401c03410000c1e03840f1068880880e141c02ea409540e80c6580e05005003240500440313121306038510200e0200b0640042d201c00013141d81e54510b0701140007102c00025032160b1100d11950324080c01d026126150103031011800f00d801c1e4001d43d0380d80c0c2249000c5a01c00c1d20350f04401380b280e10402c4481e61041d8843c100b1444135810400000741c640322000c1070002854040d900f190041c2042080209004151590b944250060081800260782c0ca4407080d07103030f45252115001007040c0400e02451010141c1c040c1800c05106000000d65080c6922550300c0c0c41c00f02c400200014422105540306070007071884150300200c8440c12103018a04240c10140d015500400b19144901843e4403c0c004980d40d030040da004540182862642d9940c005400c800c1040c2408242d80c000d200d14548601c0001500c0b8440914401307060 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 750547068 1250 750545818 750545833
    0xd0c0e1503011203050903030f180312030a0c050c190326010b031e0a0213050a03020609011404090204080a020a080f06280f060f060503070c06270b0108120408 70
    0x101403c0201c050f01d0540030401d003407002c201c2c0c984003000103142d0070b00340044507a201d4104109101078030b5001c1001500907080043c00031040056481542c0e0040d0a5074408160343c901085c0464603409408010040c62040101200400d01041c48001c0114013a5907041407100e5410825055501d030280102c24907900f60700104200c800c074401842d0010844055400e1082e102c1d5041d4001d83c0c800da501420580c0d0001d84611400b407581003140080c2000e40300c09003100d00c0c6400080781c0d401258407480c1806080030210701001188000c503005099018411916980c89800c482d03030b100c2010b10103d029060008000c02c1d80140004c20b51141507003040100301a40c2d07500008220701d1209440000c00001c41d81903410074a0142c00340504142c1001c40004100e0700d412a00c0d4541315440d4000d00034400c1c10014009596070003110342c81b5064200e00003007110403a184100e2003a00a0b450304907480d640700100901003102c5015241c0c100c491501c00c50b00c885a84110502c1e0520861142c140c5907400a003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 750548318 1250 750547068 750547079
    0x3131d010506070b191416200c0d0f02030304182d0e070f12060f050f070f0513030f0501050601020613030e0a080601030503070606211e06020d0c0e150301 68
    0x141c1800221203240f4000c255100c420312207007031b40d050660f0307006105080b440e0440c1ca0694003111301502240036411401d0317042d42c50054140c40d90140211503001d581209611070074401c058200c0100d143c0c0c0038084a45e51a55800d180d040381500098041640b42010303960141c5010301c8030071013071802140300b1107100a60b0412b0340d440140440040c40c2c04600622200080510203840c1007401085810f94600c4c405501e490300324202c940088011305000e00e4607050040c0c003400060740c10f6002b1183d0a09140021141e0301c00c0e03a00f030243c034003030500807800c003071010040202226104548a01c60b9000f4091030b21a01c0059072204821601d440684683c0c42c03511012a00c40e001601c4811000381c00d907011a910b9820042c00c141c0240c2098406038000a1a4810000703684614801080480c01440e0100c80c218802030100d115060050078101500822400a14504244100440d40704008542c4c0d00000007807000a004600c030300303d0115400c23604a012908200c240204150120012a80f0390b80c2400d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 750549568 1250 750548318 750548341
    0x2706050d0b011403010609091404030905060a0c050d1e0206061c020a0306020f0306100201110a0c0318031112010b09130305040b0c01061a0702012003131d010506070b 73
    0xc90400c80c00040f2585541e03901c50055001e04100d0342c680000347d060420100585410102c01990001a1810440400e0707100075010240c034401c480c484e41d1b80f206000d044800002483d8060020f000390b00000c00c405401030b101354442030304030507040030165107618181e8990204071015600b180e50200049030992400301140107030387c4024045485141c4a444000485e00080381030032000c0800001d1005925008100d203c00055500c024059106181e0354440e25000d101903800500070301030110020140251640b0060148015440100d02d5603030505c420640e615031240c40c081c0d40505842c102102042c0180140040e002d4906404c40d202c0450b02e00c5400e00900c0d080d802c0100074007011601400e031030024203840070810008920700e81403000341c041c03d04e508104400034143c10406200180d8010500645e0104c074031200039030009060181500b1403142c080070000c0c407200440c4c0030a50000c40030a00d442029180007032040c40ea00c03001441304a01c034403203001c2d241e103140344000f55208101 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 750550818 1250 750549568 750549581
    0x2160807151e0305060312070804140604060c06020306011b0c0302042003062b08030103020f180f04051903020319210e03070b01030f02090603010b0604140303192706050d 75
    0x2c6e044a13510502c07107010490540181608641c0c0080c0010100228041c450343e1102007001114041d10307007031400c40007400050800b038004201a8001c0005a9668085e10040c80030030100d01c1c40007000c202900e40003405003118042280300307034504900da1078030950314507090280003401c0304403620b503803682000c0120b01510750888800c400c10702c1040c8030069450f078142c903040d00c0c42000003603100d50542c8100500c80c2c3c000400503002c3c01403160f41c02c0507005038440c0150803e0900301d5024058a5034105142010900742c0801440e01d00920341c0701c1016070010040080000792641c44401008041c000c458103d80c0f140e007856060407074603026190301803d92014015040c11400c891402016903030b0804040c0c0264416901004006039100c00e605007104e50f55800b92045008201060302c0c3d400045160180b4021b40c0b120b042d0051400c107090b00c1c100102c942040080c003420804030304c603a80c010080b0b640c2070142c800158145001e1102d840c0d4051004081d00c8030f685078113003040302119210340203050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 750552068 1250 750550818 750550831
    0x30f231303050f030301080106050d2a0b0a17060301050411151201061205100e180109140a021507080f0a030b0406030b0106030b06130303030203060102160807151e0305 74
    0xe5490000001d20104001c501e54105180075545030340c9010706040c01c40d4042c3d4000ca0142400400600c00201641c20903110388540c80c583c00129070301031040e2406001c41d50040200b1080c0000d0303010901d60000039101d020a2510b071600060b0341c8440a05003a6078041d100188005030750301a50b280c61506402103c10040348445031400e10121055140807410300307074461400314008040841d240c03400c40c05032640c070114446144100e1842c000061035031190007019285069078800350400444000e4100540c0d594004a07110706070050320301e107982c60b40650b4400302d114104071950311548424210a54101d6a0030108840c20010345a400d842c842c1d22003010f40c0d00b056680c503400d440654451003410003a5024044e031200c0f0b5810118098100e800e8402d909101e44c4040c440b40c441d00c101c081448050707a1f494a0090b07200d0b00c4140040c1c0c5004415a444803240001c0140401c55400006000b011141c100c0081c0c41e0200513003000303550b4841031021642c1c2d00e002c852111030740c80d4000c2d00020380140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 750553318 1250 750552068 750552097
    0x12050607030915051005040c050a0804140c041104050306072318030613060c02010603110409020105041205010c0e0103110d091b03111201020c03030f07031e0207030f23 74
    0x8200501d02c0080b113070100e509101c1031011072418403240c103281c419507102c1880c600744107182012851000d041c602009000520303440708840c400804c07030420701080f40d43c100068400d00c02007070361a0380300105802038051342e8000d10682c400141142d01c50148580036120046001e100001d0381044900694410b0010401540909606241c140c038100640d0b44564409403d118803510b4619000c410b9400340c0c0260421a81000414004101038031060486042c040f40c0000b140e500603c01070b540d40c051a4801010019201d042c441072007010341000c40c01c0210784c0e80f004a19504c3c0f400540844030410000990a241408000001c5115a00801d0b40500403000003007440b10040848440344c1813030300107e50007000e403040d4840c60b0810000e04606000403800960601d070902c0c41090340c0317020080840d0700d00211000800c140030b000381d018100410848421003214284030741780380042d62003424201c3c0000d103074a2800406030321400c800240103001c000c010061340d4540001907d150809682420300d034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 750554568 1250 750553318 750553343
    0x30f0415032c01060b0d0905160503070e04060f02030408070312020f0906160210030e16122003120c19021e130903020a0b09070605030612030c070618120506070309 72
    0xca81c00020b8203d28000e8080484c20aa03a40f42c954102001d924000303006450410707003444130b032f40e020441c0301c01d0300c40c24200705c101c55956050010107010100e00d10007000c5d00c00000c1c0401d20a120008040351030082c1c40b034a0358484036640e024101e2240c43d0010202003018011440f25103881d000800601c040d005e00c140501425400080350312218007145e4000c260340d41c9200030890f506210100c1610010380d41c0c01c3c285071415103900d03242c1009400003080008550038242c04410300d030a05060507000a01200c0070400d50042c921206c3c1c1c426920009c6520421100380c9844902251003048258080c090b110035006c2c541c4122a01007120f814183d00009114071080c1d00e5800c0d115158015009600070164041c140c00d00a1903c039000d000d003841604005400d110141d000011682c04c4801a59150b12540000c65258218011690f000c5070724094500f00148541e8010805a081001e680024642d02d50700c4141104c8401d002c01c0081560300008001130501d13000e64054485103019043c0001d45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 750555818 1250 750554568 750554579
    0xf01080708060c0912010f0506040b09010302090604020a0903080a030606110307050c0f0102010212150901060809030406081816080c06040602210c0304030605041109040b0f0a0e030f0415032c0106 86
    0x7c1d00c51010754500781d260360744100f101c145003e000d141d90344d2800741d400142c0395040d80c002c10b1001800030302040c0550380015000300c0803032161826100440d04180042c0d00d43c250340d0001005000fa901c1000c001401211000c10405d0b0040222080a68810300405040651034103000101d00c0e001641415950300b03000c61900f20300c4480c5420702c074a55000360044000c0e5082d081119440301a0824000c00c1080c40030801140340000494003170314203038100710201c2c5e80c0e240c10780612140d40c0d080103155406204c00da018195a11150442914130041c107a811000707400c0d007401450b01882c03254000583c0092407960310310030104a80c8102c8cc8a04900c1890207c1d254000e921710350050b8400c944242c0c1d40d1040006005203c0c00c0300885650407940c5000c0c80c2400d444034100908050031121020b40c2c0e41000c145054015031150300c8900244054035190010100c10034034982062003150310200c44110003100f1241700e0f2080303002c42d10300d02120f1003a406901f002d2030340c4400d245400c19555903a80901207039 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 750557068 1250 750555818 750555821
    0x2130b06072d1a0a0902011706061605100b10091e0306060e07020601060503151e09070c020306130507210209040c0501120504170703170f0f01080708060c091201 71
    0xe095000f0f900c0880c6148038a0b5030f942c4041002414410f00301c1c40c080c64040141e80c08511444559600003c00c0040d84510000400c0d03803141516601c003081211083d242006800300e2401903001401d10100a0030007503c3c00e0000f4176990010140000310800014000c5c19103070180e4082203081c00107844c524076200c0c1d4a800844515800040000801d101001034407641040301e540502414a440e608500b0310072080d00160903c3c00e107803840b501c0c1501c2004801428020b4000f081c83c40103142115a003450040544019403002099000380079620006004014405c8500714944e409002072241620f0030b00050b40c07284604100b4599003100d40d400d032000d43c0e52440304500440c00b502420002c01d10f001d001418010b071181480390080d05140401001c0b49036104080451081030403200d903140000e1a04403100c8007032685450302c80d5000c8007440190319821800a1103402c8220b460171069072500300d130710b5071002c15214010b0207a000100090309500c040001e0010394002514406920042d0300b080c90 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 750558318 1250 750557068 750557153
    0x1602040c0f050f133309120611130f080708060f0f060d0501020307050306130b0901031e0507030c050316080c220e0d02010b0d0c030b0606120106080402130b0607 71
    0x10500f18040c05d40300304100341114440501054244a07072000e2404030305140240c0d003c00003030401a601c9040320385500c140e500715510303c50345441800e40592105850b8a0002c1c03c0c0c01200014410548046104900001c5050184c1042d03151040b0541d9081c0001d504d00305c0013030059410083c0324110000140c02400618050310460301d84070b03100d1078003400b841206019500c10a04650514421115545a00c03c0c51070550b500403651032802c2601913120a025480110020010b2040310f000009000c0c7e900610000c3d075808805807801841d5204c0c0c5442c02442034010300250340c1010b4002000c5180206100119030644141c50a0030f2161a50801c102c03941c011103d00700782c2042210702c54103070307080c4910217054500300d50fa00c1100c1c2071a00d03071324000015400014441003022010841e107684580640d0021408064040b6142d038580c2001000304800b981c04038050408010f554400c840e590080201106016104509044841d04c075107108800740c2c88035031000b5000d5000b40070542c802c0301170003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 750559568 1250 750558318 750558359
    0x80f0c09060f09190e040b06030106050a090603060f1118010201110a030504170f0d1505030a15110702090c130f060e0310020301080703080c010b061602040c0f050f13 73
    0xa500c2d40c40714801e10244c4900900c01800c10424828240801d031041c0e07405981182d0084140c81c01c550f074200200e401810146c00036075002400901c00155a50309400c25401c0d2442401c003488010030070011b040035070b4400c200c594a815403d2000d8282950f074081010fa503440d0500c008100d0034a1036190000941c0b06001103400203484804100900c5a08007944641c08c18800703116150010107600a401030140090780e030011900c1d03103040420f030f00070b080e0381c0005040000c0540716059040c3c078001c03102e02100701c00ba0798503500b442074100044d81e001d01a100002d40240c02d44241ea912041c1c020b1641c0c0c0304110b03085080358200004a0130201d0108048064141c0da103d0b00c250542000c10580b82800303086007048140c0c01000140401140440c00a040380d900450050310b40303014081c070b14050202814039503008040801d84070f584088044107004028001d071010400b01410407801c481c400302422403d0085201005007880c40c2104400400c401000c010340018503540b6208500307000200d42451 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 750560818 1250 750559568 750559597
    0x501060e0a0c0e0d02061e13090c1e050d020306040e0a05011a0904120e03031b0c1c051203100e130506070c1a041a0a0606030c0e01080f0c0906 63
    0x1c458019401c00c503c0c1042d001d0445030382c500000d195002031581c2c030405940b82c61201082c050520750441d0402959200c40d17040400c51461034170b0f000010000d2030107084050000c0c152144001d194160550541d41d03c404076501d4a2404d8549080500039520107445250480c1e80ca0115454800042c0092040305100c0e00010a0ba008801c0303e424480800e00e1000c0e100360301c10414070000230482d1000c00030642c100e0921200c0c0c1040d82000031700310702031608911002180c1600504019802007103802080e031040381c80a294500640d07226900c4074070510010a01d03840381c42705c0070140b2140340c0036540c4503d046e2b256014040d102e80c0d121582c00320640b0850781d47d01017007030745004008003407041c1c43d40b00502d40303051280d81031540c0359441407800c1d00c15101d00e044540c41c0803405100759407000f4076009550414803036840c2810041d0100804441c403800b000645803100340f07000140b04003201c0d060713040141c1d1a000240c84019048411501c05441c558010b1820403505840d521604064050b40008841 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 750562068 1250 750560818 750560831
    0x210111606050702250909110303040603060e0106080705270402211501080a0c02011803020c280b0904020405100903051002040b0a0e0a030c08011a100e0108040501060e0a 75
    0x380ca03100e1180c2041c0c00504940044c0c01c0a80e40c410b600200301c90906c0004100201b030b81c1040d90503440c070300c1507680e0540400200401c403d0340680041c01101c00d070340140c07149a070386c1c0c00c4c084480300c1c815184c10000030f40c00c000c880611088840b60b0240941c4e01c030740d02168008100001800c0340c0c048001c204000c0100340c908500800740680d42c030b5201d000002c60220480719000000c0c1085001070035502520b1b540c1c9100f60046100f54001c04003590281000e81c0c4070200c1d403c000c0c0d61a25414003081c4904500381c00f51071103c003100402d0204500030b040310510282048110005900030102e0f09401c10f03800d00c00010b1035076540d100c0c0082880701e80c07a02c1ba80301e411400c066003001561000d68960030b00400007003040c0c0b00c102084403174010300d034941081c40060030000a40380414550020341400e80c03000000c11905011b5001000007090300180c40401c1381c0e96001e1221240b030740030410010413900c000c503100550141081907402803081c0c0002031000e885410601c407401040c0d40301c070f524564804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 750563318 1250 750562068 750562081
    0x14060a05071b03360504020a1e05040e0403110105250e06070b0f0421080114032b17060901330f0806190504110408190c0510021011160605 61
    0x4c040340c00b4003004e4506615102110300041d21038080031450072000312000030403051041c4114292000f40281c0302c60501641445e040003041c0c4c544540401c0c0407546410081800d030212104080034010740c0c0d115500c44002000001c1e00d40d00c10000c0c0e80c81d0070807001c00c002d20000341c000300314a200746004903038084581400c3c10322200e103280305c201a840000101076411452604044c89034115610346041e82c0e401aa10380c007007420324142084c40542c14041002c0451009225000010041510342c0c51340f41441d8071191a90800500b070320102c0d0010310450060060741100b012041c0d2074640d03114810b030a0000f517200340556404441111001034003400d8034901c3d4907401b12143e03402c00c274103d844040d40d00340c400403214980708503c2118407481d6104100303d03102c400601a94001c1c601c0b003044d03c070f4814640202401507000100201c80c0314441600120b00c03450100e4504060303043c154020903851703102d81c61030402000e1803400185812418008010300c00c07a17400c882400c0d41d21410300414903003080f9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 750564568 1250 750563318 750563417
    0x1216030f0317041a060a0e04050a02090610080609090312010b040e010609182f04030b1312030507031122090501050f13150314060a05071b03 62
    0x810b00964010302d002d20010403091841800b8900035010700075071640b03c40d0002018820140e0007a07201c1d401a104200500c01c02050908e05240280c41101c030741daa400c420424000c0700d03166540e0109801401050f0281448c0705999845042003007142e00d40000a514403060f0f1009900803004004005014410510040740580c01803816003068100319051a1075094080341c034102c2205000d0380c0c0c00c400328070b0401010003901d10b1568900c00050144100303900840303580c020302040d1644002075011a98110300840c80480e007036040340a010440c15820b00071030107400c02906240c100754072a0314850420701c1c1c3c40010155100494035144040b02d100780c191400c2a960f0f032000c1c60081c54140100301c16104c02c1e03010341e0840021510014800c400341c1121000b070000a580725606810f0b09000710800022443c02984007000c03d04507012641c1d1003040a050b85d0007251780c03000045202440c040300ca140440381c140170030f01c80c1c02c06010007050410680c4801c014841480090380304031050500541c40e8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 750565818 1250 750564568 750564587
    0x204050d080406020f01061d060a03080309101b050f1c02030c07031d10140d02030103030201020a08090307171605010515010908121b031b0a0b22021216030f03 70
    0x5d000030b00825107000030381800341e02c044c918043c074404217400240389995007034603000c003455018401649a0070000682a03a50b484840d12401c4c042c5003d640d450007100003682055101119610035103421201340c0001410b4101c290010721803201600710700d99001c8603002942c404d240038041e00b911101c10f824000c211418903440c060000205284076100c41c0c80305e280a12400440f405c240141a5022440d101d85100d042c0041d007400c0d101100110406038190000c00d801b5086070383d443c60304d80350b070b0038000d0f1079110380880200140001c0d8901e808100704035000d04080315500b00c200340c0c0b200280d107416080d50350840b2084c4902045558514a079a0002d803440c014080580040c42d203a801c2c4444086a072051104103454a55401e0f901c1c0b108210820440350a213a08854240700c0310001c0b8803c944e0380c14040002c8449908800010307c08142030181c1d60500d4000c070010005888990302480f00c50082d185043d40d142c02200115500841006608801075104100030300c403480d603034203000f0a014035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 750567068 1250 750565818 750565843
    0x533070c1a04020109050907050903070e010314150726041401061505031302030c031c030507030c020a060e0106170304140118140109171b0a0810050402040204050d08040602 76
    0x41c90018003016036400b0b6209800d440007999040401c3d290400107880b6401901c40340c0742d06200f0a64080385840300c0c0200f07641240c5c8075161154007504400310198458900079074899107140d000000420151042031310102c0c040003108070107650740007c080c0f00e0303401030100c0d03041c4c42a0505005103480707141c003441132030018042814002085049050000d02501c00500545851040c128407502507590500540d038055000500b00d400d919000e4110110400d0300d22100c1c0c0100e4a048001000f4078024010120b080c013081d80070304010034142e603501c802031202c500242069035944501250006441201c05c20901c6110001c54030f50340761060703c411002d802521a410800f20b40300c0d03211a00120b219107006d64501e04041c40201c0c140c280101d56803003480c2c1c000e982c83c08160004c90070402010400c542d0580500b11410075503c8400b062001502d1a8400c0c0c0840d0b9000c060344007590102d40d400355400a00c001c0003d8513141d5508001203010503d403400391240c05000904010b440e8041046591300503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 750568318 1250 750567068 750567113
    0xc0b1c0203090d20010509060a0b0117060d1a0112020f030c3114040201260c090103180501060503060a060b041203110a03021f0203040533070c 63
    0x2d0014480d41e110700c3c2100440003882502c442e0846035080c2100d009080c0e400c41002007100d03190035800a0303550b0500740d45590f082c40ca4407008512952151030390303e520251200c0305810340e48071b840c144006101c3d500c4040e81d4564002c0e234000348080c1a1642c842c002d060b002401d030f1400d01540100010020b55840ba0340c030070b47c4020050005a200e915112002c0c0d4144440070746903c7c1d904688030f00303101080d003000c2c507007500d0194400c5c0362150040f0b0140c0114000e0b038402d09240c0703043d4001e44d000c4103108a501d1104803540c001510400c0c80c800203000c098010315011404500c0d00001442010080908941a9455800c00c0c03015040420034254041c191400501901d45401030100c02881503010b484007003400a1840c6080c10300070a256120181d84c10308451460800b0304000751a404020145a45011808007821504080340260ba00940e0014080c100303000340320500083e20044861203402850381c41010b00d80001805031140c0c0f01321620b07240c401c2941a14500100406080c1d01d0084440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 750569568 1250 750568318 750568321
    0x130204050d0201050a050f210a1e0b010e0306040501051b07030c110d0206070b070908030a020c0d020a0512010b0405100312080a110a09080c060301032d0c0b1c0203 72
    0x958070072003102651602130900503510010100215082d1040c0850502800ea0010741c40859402c1f68404d2510f050902412100700c4d00c4030f80640c0141e44180910f1041ca00d80f01c8082c02031940310ba400f24490304014180b40381950b000c0c2001c04d09101e0211803d8410b65500c4080210300b050128a40c00d44205108280d0700d0140d40d0364004d4074400603010007803c0102c03116211041d84d1662440204140c2c1c00618403a00d5929503d07000128020071550540001c03140030000940c034500200380c0b00c0c9030760b00b038000c0d02000c0d40783c0082c050070001c014002d90380403a4074030001680340c83c0c03010ba1041c404680000815440c2c1100b040c8000d90307034080c0c69007440d113401d504c040021030150342e00240003891030710300407005481f002030020103040484440b014040c0d000402044103900050700404a030444025a0b0400d03442d08208900d6000c00d10000c0c0004442101c0000a41c010361101a0800d8410a850020300003e071aaa034544156070006a410000002e401c08010350102c41d425100546082c10f41c40c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 750570818 1250 750569568 750569579
    0x80606040b07051906020c0706022e06030b100312080705030c0a02011d0f0c12030f0703030f020d061e03110409031430010e01150e0909030306130204 66
    0x991140d803058800e514030225064041040911070b810301c1c80d07900c104080d005005800e00200079404040070035030501c540d00c0c001418030300220b03140c495403440c3c01c1e0f80c1c0000800e402c080694141e46070302c03680d01c0b03a41ea0100440004c000d0b880c45da000d682c95240b200002821880c0c22000301c1141c4d0b480c4024000701000b0005155484411694802c01c1c882031641c98200b03449041e40945084080030280c0200c0030744100c615400000d44030501e41064044400003e8007200740301c17002c2650001900c00390420003020082600000003040a944280790004183c0004001c1504030b802a22003c010795803501020030120500b400c0d07100e101444003c031000c0640c40c5a40e603140502c070041031180203e07160102e007024140605003040054081c00b1419030390b407280754003101300042c20400540040a01d00501008110002c2140303041c0c0703d40300c2981002e40d00b4180704502c100751720114082040043d044803044c0e81c07200106103002d601c0c07820085403a400c10008201916801c41840c030205841840b04100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 750572068 1250 750570818 750570829
    0x30321051302040e240a060b030903040e07020312010b0702010f030507020a021c06020304060b010908070308030106141b010b030606040b0d1b0f0f031b0308071502040906031506060806 81
    0x41d40394111000100030038821245400d254005413142c2080742c141401180745552880882e00c502052a02044001d40f644000f90300c1d40410b5541c08480d6000348005d114400d081143c0a401081d1401103034141898200c074030b840050241c001410781c1d4000310f031030301c11560404003400301c50000d400d0900051514400c001c4d40d84182c6072008c0d210301c2100144034000e01c0b4260424080ca0f411410a541d0303450942000d1001d058180d140750700003807943d400000d1158000c01c01006483d400695a440c50b4a015011900095195180608030300100000300321418495003501269901070008680c000c103010406003441801044140280d00302010510503960b60010054540c0d0f2140f64909400e0b074021b003c00b454410354009003140312080b0b41c04038514820b061044112442166104015000c401c0e0a03500c08a4902c0028000c45003800720200244031004492052001d0100050420380c0d505104405e90b001603005803051400003d0080201c6a0360140034050b00c0c040c1424511824680042107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 750573318 1250 750572068 750572101
    0x12011d0f2e05060f060f0c0706081608090106050604080c040501050f150304050307020901031a070311121305191509080406270609261e0a060603032105 67
    0x7403000c0d50b01d50016034190f40d5682030b44900c11000d000705480b030426424545042c0e0100303414205c0741c4104480000c62074802c283c25032181201d04441649028507810a5412041c05000c027103055403210400b00b1103840c0ca070040c00c001c0954800901d590b031001c0007403004a9174103805c0309010309250013152156445000c1403004042c640003020340d0300d0762a13081182c04c1d400395100095008078408000001e01c0740c4c941301c0400c03001c8101172003401c1c0c1e200c012041c0c0864081c0301540034111414020a07422a5081903001d41c000c100c88003070b480070b100c543c1d01c1034105140340302003521444550245100b481454528891080c0d0b15140400003030000e521500101e0040303100d0b42c2e0400180174086016402400700c14180c100100c0840c4030541e44815021707242d030060b07000d40802d042d0070000c1000644041801141455080400f61201c19070504803d035280034207003801001441245000701c0040c40707a01c500c200070350281c1d031880344100404112004021044030407645250a010034040308070710325110340307 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 750574568 1250 750573318 750573403
    0x3061401081c0905060c06190902090403081801060303020f010b0406050612062202030a1803090510020a051207140303011a03280f060f0b0912011d0f 66
    0x60b15081d00d4000201c8003030515410054118401042109444000203180f0b07008001c102c480100a8104d0350320781080310f02c050350103548480341101050200e40115007490f000040200740c0704000d00b42110391130a40d201907001300d0050740048400400c00800784a0180300e4101181d00340249072234240014107502505000300c05043c821004108070355110034000c150400001c400702d41202003041810000d4000b218489441801c2c00264554884450036441300c19a054907945491400c0a06009000d04005811015845200c09000203e0401c00003a036034049a410310965440c02840e03c4200c903040078803002d5241d4410700060240309082c980f00e8000a1482c90455185d075601e6502014407130042500001c1c0c1c0e41e820103144c10f41da504e1740008911081034007051002c40d5a40ad00b020b0b000e01544502c64900d00244021402440c02441071801030a5080002c17943c000c039541c1c42c0c0442d00345500d25150541c40502c3c0f510a0003014412480d008420382594045181c000f01c80003a0b0740b9412500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 750575818 1250 750574568 750574603
    0x506090a0b090d020312030a050a050f1b2203020a0902210402010909091505150d11030c1f0f021209010e010c0b010603060e0912070201051806070803010306140108 72
    0x140456480380100043c0b5541c0013001c0702d13a100c0c40c0144941c440d502c1640d90107007550410300001d503050041c3c010540604611a90444640d0b13901011060007100010040c410020401c69520b10011840340f13400c0120b03a41d180d01d009503246104100081641c0d51126404500502014406908005110b5a24040780e890032646545030b10040302d00c0042c0c1c3e0132245100c4d29110454003405007020750207084c00840c100400160700ca20b04801141503204c0130322a40140d5000304100027a41d040d8003c041d40c54007408031442081603000041e2a500410021121107503003000350f00d032a5501046454908403240090941040901542d002512a4617603843c10301410342c800081c164070400b0350040b40da070402c00c2c192181d615807100801500035886000344501d40301010500301100810400403a180c642c085c4c070300d00320103a8015181d075040116007001e00c40d815045000710f5214030002b41080d61040c1010740c2d42e0360541c5000302c200c461841c1d42c4607088100c400180807170728001a0500240018508 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 750577068 1250 750575818 750575827
    0x20402040929060318030903070f090b12070513060302100e03240708090f0105010b04050a080309130506120706120c0c0f020918070b0405090112081e0f0a0c0308010506090a0b 77
    0x404d1446c5d44281e148103509445503500c001032450f41c100d0148140d904060040c060304002108000c0402e400d081c200040e60064070701002036161080c00807c0c008080ca00100e070361a6682c0001d6540e1204102041c089a5480d01e6814a0314003130200c50a420542b20b880c0c4040407420f0030007850f4090080c64103043c0007400000c5111000104042608001c1042c002d0050390703150400d40d0590307046882128000c0c00c044901054402c1d011041c3c3d0152400903002c0b6204d80880c0303e03a000600400342210b0340140c501c1d21903246954051226a018015544664110400c4c950100040390800489801040040000d500010300c00c02a0308000e95012580b4035500d40f98110b151903140220041050184500c190001e4004c0d07010026008071442128082c16903a81c441032080702c2e400303c038802004580c003001508800d400300e50243c0407000c40395403d503082c6000502d200312561301207440c680102d0b0302582c00700205940f0034441800f604090300c90354103001092000c16510540ea01038140781100205 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 750578318 1250 750577068 750577111
    0x1b08060606030c071b03170715020702040b1f14030f071101270506012702070813090e010f0c2f07030f05060f0c0a1b0204020409290603 60
    0x1400d50f440241c0040b04c1e07280074010a586036100040c1c612040343c140d0340d5010001c1c00060320b0000d90700a01d270441082a14400d031034643c0070007548071220803a0f2196480110154580701c1c0c08110b644140c5440300c9603015152154083c0200401d8400c50308030007410410000c0c070404038882160814054244544086d02044100e4054180034291492402c001c40405407094101a0b6812240d806230b415204140d880c0e0380460400203200f5900a0802c1c0e00c5500c1400f00081039008100160061010f18200b03882800c0010304100305500440d405510780d050200525001c1c070810407481c000c004c0400014144580140140d0500651191030700c051460180b00b1400001c516040810343e01c05407000c0903102c0c031700207190400c0d280c020368061090070f0010f1246140440118018130007940590b0401500e400d08460a40f0000b4600300f07281162000c0c1c0005844900140010780320b40e0802080c0510000e0440d10030030006442c9a4041590380e0203140c0607140d5000300c0742c102e0250b49201501c1c41410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 750579568 1250 750578318 750578341
    0x60e010305061f05090f0306011203050d0908120a1518111b0123090a061112010807080c010509060d05040f150b0a0803120a0b01120e06041b0806060603 67
    0x1200b0700f80d032419000810060742c076409001441c5100301201c096681443c401300f4981e480c0f40034007a0002c4001080801d42c0803d014101a01894090010126034445130ba81e50401c2a007102042c220103000312014003c01842234020311803074001c0145207804852800c00a0001c0444000c0c0d1125921f55401022501580078001c81e00c284401003c0060318010306040e03d40200042410700d800d1101c04c01a030301010400300c0c1040d014182001c0180000919911380304001c3c007503820704600c15241000082c0c00701c0c84030310306175000305000720242203107038a131005c1720341001c1c03c03425607604114080007001420780d1100700740c0300701c1d045001002640c4d503640c0c500f01f252100f80c1e00c0c026013070491180c88040c51940729001750340c07035440950711151082c2d5914101652802a00500d0090103462000150b02d20312980c8a00f21018051519240500c2c00d880000c08698900000300f4060b0030440801c0144400b10001c0314406905080c6080302c00d1904130061740703500d005000644a4040080031806950a1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 750580818 1250 750579568 750579589
    0x32a0210060b0a030605151e04080d0801080d0201060609170109150e072102090619060504030b06011115090a1e03020717070302043c050907060e01030506 68
    0x4000040215030b07124001e90007250040020240024141030002c80c140c101002c0e02d081d08035a58030407506040140c001c1450304041c1030351000c082001404000b502080801c000b04045071140c030789540da9410304040c5414071030788030b0004c0150380c14104100545580040300100700c5203100c0f0364858042410000d1170142010070006004070800c443c840d00903106c03540c8181e8203420b905040301c1900344d0304c89071812902c0b0703100c90002c03030030582e010905c1c05030a1000d54194030070310043c04151002c441103504d803803011468002000241d40070074203108201d00e900050307410040c2424940f120175081024956a50f102e04c40300301c00b00c000080460010780c8100a40300034651310400282002407400c4040455400c1e6080c140c4c0107101d102c2000032410720411941811899180c05030000314110b03003c4c4005450804010811010141212981345c0804500000810a030016141074100507180c80d500380c607009406400141c119402c20441d01e80c10080d0386400d8030080c2004280d65841c0000661284176 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 750582068 1250 750580818 750580843
    0x80c010e030c160906050f040213030606060e0a1e031b0503071401080f04081614030a0521100e15120c04060609180917210601032a02 59
    0x7002c109401049008204800d5421018903400429a80c510b800020354031144622030704000343d10744a8900341459001000110241c450b1100490b07030765612002100e140c0d5002e4070006018000510581c81e01c82180002483c032810740020011598580440c0d0540c58403005092140d18051020038100c80c4032107800819000b8190f401880d5211001046000c80040c013500056882c0c0000d411504109022801a50460301d1142000d514042c0481c40b80b450035001d8405000400c000c9071210410402040094503039030702d403611000741c85a005004101c10007105400014101002a903140010b40e600490300803c0c100d400031f4803040c0e4a103000c4c1519400250304103400c00700904071408000b4008055140a527000c1121729500e032422205a101401403807091b4000503c0c040c01403032542c20400c8018001c030a140d6401500224044071070744903030b40701c090f103002c4100c590f52161025940113901c0582030030280500011240030766a00208032407a115080c041c0c205100d0000c0c070070480d850a416 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 750583318 1250 750582068 750582073
    0x10501030b0a0c02062401030e031305040b09011a1612090305071a0405090406150f05012d0c051e010b130c0207031e0605070831080c010e 61
    0x16100c0c140440941c0c41180c60400c01c07418400b064103043d00c0003e0082c0705244480015002060503141e124070010100304043c101510380840c504010310500042280744410782d12641403900d420180801d0f240300301010b038410703071b1007500400005071000103010000106c0040d880d0780300c41c0940c002c904c9004151018010f56418050580b0f480e03040320030041564010000c40b03a4460b6202d08002c540048605070000307480040c04108a035080041e809900544920004503c14441501c540c4181440c0e81c040c034802040c0c81000c104658000450807000503d58803040001c01c3c5460180c541d0720781c0400014100a0381c1400318092000500c0389a400f800c500c0008120960759500340c9018100151000703200b49040c0301d5424946070240715264024441e90040c00980340b9640b41c44200710461f42603800c0d040c803d00c4103c00080c116100e600e1040210361104616411300b035a001c40c8210001809110010202031601c01d0380d4907210343d00d40e000e580500341c0caa0303078000c07a40340c075000d85030326191841d462 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 750584568 1250 750583318 750583321
    0x1401020f03340509180910151a070c06052502150c0a060e0601030f03080a060b0d020703080609010b031501021c0905192103020a0b04060c090905160f0c050105 70
    0x1a5806002000201005c9400f49141c100380980c018441c082510242050381c080c48030789031084032a4210301c903985000041e0780c0b10f203030f42c90411500030040038020001c03160340001d001003007200903c0b046001e0800c5240490820310403072004160000b809004003003040054420703c00b155500d44c040d14001c00003100e26034442e4645403c0c40c1d0b90380e40d840000c940c85c90a151246d040e141000420300c1c100ca4001d0030041d08803100351029503080c43c0140500c842603440e1400440c0d0404144010126a00346000c0140c0d206050304004120340d0000e08200c0c4100c503040b00411000c0038a901752504100d00090001c0a2400c0c100141c0c03500342035484600b881c450005207000d4154201c180c00c41207034001d0b00c2600300092003a1100500010700c1c0140c030519440e02c034040f650030705104403903c1d0382e034841d0044076180d072001d88555800400c01c031821607516490b6085011034950140d260b00c02400185414803090410350030385121400c06071b840d4803c201440b200000341038807554403800c80c0b58100c1e0003084503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 750585818 1250 750584568 750584671
    0xf02011817070c090608100b060d02030601020a1a041e020a0302060901020712150605220908090607051f06050102150a1e09030212210712060905041401020f03 70
    0x542070500c1541668080c0b1441f451030140f0701d000e10210414002d240da0302c3c202002c90b26a0080d000078010034114421807047c1000158403140907007d0707450240540101e4540740c0740000b0f0741000c01070081c1c0d084404682c2e0500689980c801e000a581c2d044941d1603ca8000c140100d1500e03003550b10032902c032245070380300c0420f212410740300c4201e840807004140031254680d424084040a9030219801910301a211404150000e0303004120340c601c908407251a0000000000b911904480170030307038503038028500700f0461000f20750b54030404203642c85090040e1403824001130340710300b50540801600300d040d80c0014143c03600c5071300c03080c5c98540582e024010405401c00200051211600c201e01510500b079011005203006401d03117010560b00f0601003050f01c4040604081c1d140c000d80b407601800321690620441140e01e0099001400d019440050310703145c00d042902c1031030358500f0180d1881e44100074484228608c6001c5036031082040d07940403150014488543c640c6c001d5140001903143c0d101404004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 750587068 1250 750585818 750585821
    0x60d0f18060f0c0212121003081c0605030f03070b10080109140c012118061b021002040b04060c0314070803041a0925080d08070f02011817070c09 64
    0x30003410072481000300f00280b54007a40c2d034043c1c9a20600c41d20006029031b8a034403d1030340036658040000c120700308100b40d99565010b45504014801842c1c4149404400c2072200c03188900702c0205401c03030040c030251130340c95140c540300e12030f6007c050718214450000400420380a05910000d083d594020059910b941c00e0101043d4640c0310900c0340d5004002c45000c643d8412084195181c000000240f022031328909810001c00707030740d414a02e5140c845610040420fa03d40f0920301c2900100c542007506801d03c0c600242020328900410440030300c140818800300032484d0640d402e40700281440a0032451030300b01560b01ca05500034a1130b1681c00021528200940365001e103005620408034841d0030860b0880400503410100c5002100f03504c0f01c0f0304040f1040b500c0480b00034110003d1240c0031100e4a8038119070030540c2c0b84ca8440c02041c219002d01c0b000c540d00880c00500d440003031008101080365640b403000202c0c0c0002000d88412403040800043c190508110f4620a50201e20808401c2d80c5102070750 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 750588318 1250 750587068 750587081
    0xc13051903030f03020a0509042f0405040b04091101110f060109060f0b120c0a03020408070f03051c020d0e0109181b02010207051e03040302120a20060d0f1806 70
    0x40c00225403100201043d03000f07000340c444814290300d0706424030704c0b80c0040c0401052003d450200000d500f030104142c0d2205502c03030402502207800e20541d81c1e4284824002560b0101001d980200d240070800c0000c102c1c050180500e00e1001d103441c4c0310040c0075007621442c0c05c0302079024919500444e400011140c0c4607600100c1120000044883c1d010743e00c03201307200c0900498001c601c0f0300550303000003034820040700000e00e0401500d0a006040907115034000b0714044030fa400002850070092000c0c818003000700510650321b42010200346208141441c001d458490384454401404594420200140e000702a13281c045d107020b01040400003803176042c6001410303103080902c44040d82c5510201c7c601d4418000c40c0c0c452a003010082a045101542c1040218207040350820745000a000120050392100f2a03003010300c601100421140115060030032880c01d00007103178100b0b015420409101d68450381c05594040b6100c1c0b0300000c4000c1194084000703042104400f000c18241d040e2120204100c40d800b85 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 750589568 1250 750588318 750588323
    0x703140c0312190e15070804180b030a0b071b032d020c0906040f090b0f10050a090b1206330108010510030b090c030f0f0c030c13051903 60
    0x342c0a140010488022900ca040320b2200004040408049480c1c051019040e0f01800a400740f01c2004c0310750920407403500702c01821241c07543d0024081044816403500e416565484071010443c04c4a1200006c0e51034012810041c0b649441a0004a9980c010510502c02e2405034203216400125403a000300000d001c41d4415010809080350f0420401442c0c8400129001e01d8000308281144602004111707a001800d00d940716072905406281d401070b50203001c41030307840b0b1600c40b50542840c5c91801903100c4018020000000d815204100c25562000400c0c07c541c161030000482c13410030780100d0f180c80b03c03a21645065101c0c030000c2c0500c40c1d10300078040844858044400d15440101c0d00e00350719511609408a00168001005000510780152a007090100505000495148042c00b0412183c411140c10014a001104024440000648440d0703c0050040118400d180904409090f4000034001c034961680200d180710319405140089005480024104075509140f0140002b01202c0c03030004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 750590818 1250 750589568 750589573
    0x9041202061501090909020f03150108071d0105010e0f041e1103101e090c08070915090b030c070606091a1e0907140a0c020901080d0804060b030703140c03 68
    0x80e020751040729801e82c2c4520160b40b1141c915240400c81d00181101080a07030740010b01c2000d01d40544d40401803642040c00c5000424499858080302504082c12503101c00720b07000c1040c9041403042c3d0101313500c0b41550703c2424814640310003d004a054401440304003a0031500d41420960101422660341d1104007000d2000d0000d5061200117108502040c1e81103901c132442e400301441082d04280510100c87d020710140300c219540c030800318050340c14150070100400c0c045400e00060030b81c004d0421024003100e1880c2e1020003104400140000c40307134850816003200c04004500c0c800c1c0004200c80d51550014010301c80a520343c40f44000904c90b90602400c0d00010000b14603d6081a201c03018460b001070301005081c404441c1404407a9600910b280204545508580701c4400000040d0071500155a0382c04100d264500c11f0080040317068105122640c0480d40f02d50f4032070f502441c07056100354040d402144a00503e404203280806982005020b14402c0c07603001244d96001030a0004c0d441700300e08 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 750592068 1250 750590818 750590821
    0x322050f030a0807081c0603440408030a0e120601080a030521280510031104020f042709020f0118080f0109060e01022b09020904120206 60
    0x401020010032a69150107400c0805100d0200d03078100c0c081d103240c9005d9034415282020341003003201c03901503c100d0fa01c04250385510901c144a09400b02640c00241075000c0c14032803c984644607106205085201059140622036852040055040d0750040030200c003102c3e00d40380040c902801c05030304a00307003030b00828048090080315100010320074100c031400d9001c6c22495413070b514100c94650000d060f48504c030f04110b0300d4240b240760303035a01144030799080002c0c80d080d81010b4042c200d036203207100c800301211800c00e030078004640c621101d44011640c3c000c1d2010032402d20800490003900520380748484204011074002a03803841002501c4580d1003444640300343c214244403080460700213890103900025024812a0716501032070b45c81015407240460035584558401d00d1a1074503d00790195542039442e80085020040b0501031800754040001c006d44c1018800c0000d0070b039000410038444c0c8084103414195080100d030340c1c060301101c0c1d00038000032100c0c9010305004902c0003503ca150030040c4140c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 750593318 1250 750592068 750592079
    0x1020f0408190b010b0a0915170906060102070605090a17070501020f0304080706121d0102090a0e0c03280501080114070c0b0114030309271b0415110322 67
    0x4180b0700003981e210046100c0c69003820140700064010026480a000c1d0014021810351400403048840c0705242c0e444c140d9160700b07180036040440d0054000c0300b0b0b90780181d041c0b080340e03038002c100c1d0010b50710203140c4a43c907400448c00241c62000f06600c610981c010501c0a90700340d507804176403003040d02d00a03000c0345d101440d0000d42c10364070320641c0318010164000c1103091100901c160790703107416046826804038068074100c500b1008003102408001442c2e43c00281010207040c040004001050301440d82d08d07051501030a900c207184401414078004101009040e0b810b134961032640e81002041c5401003081c2e41c0c4542c0d50318000e14007000340c5c000e414540b00028203e2407041c0b58112034681d0040e01c420040e480c00e0b040b82c2248803d1140c10768540014060b189003a100c20600e1b0030045041c0613901e2508131301026448034014084c0014011038003110000c011440304200312412240800e0251000101050084504007840101d034242400009200600044418503c507041081244c1d0603003187d5944 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 750594568 1250 750593318 750593353
    0x4141b030c0a0f03090b100f1401020601120f1b09050f0c070609050106081203010914040f0b0604140415110a0f050c121903060503030f191101020f0408 67
    0x2212100070030041080b55010280c4144003251082e06039080c0850b9405d0280c0e104410000f0407628401101480360040000b03600c1090008000c0c10b0804454000745202380c0000c0d02d400d0140607581e038000410f00643d0420000801d20405690081d40b0040c441d92030f00c0c0d4444001c07a81e44070b0503103480e00b820081800804030302c451703d01600385102d404d4940012039682e8070241c001545c1c1036646542c0e60f2000203820b001803002d004849940104195a58108400c900c01c403030030308240505c1e1303908140c02c2000090040fa01d210745075030404400c070f2003581da04001401810f1501019900c1c04503403400d02c001c0201c0310a604c1241e100010f410f02106c1401c2004a10300d000d14100c0313400240d1410f401c0e200580c0500b000701040c0210109881295001d03049011003035100b4050441440544030004881d65810310a44e0013030a4110b020b1480c048401001d0703c8107008031002e650164000160b8002c05d64080d800044031b0403510300c003e40d10340f0200b2180d000340d41c0041c4100d803d84c1c003800c409100c256916 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 750595818 1250 750594568 750594571
    0x311010c18030f0303110c0a14010504170304170715140423010b09010b0705060f01030f08030a090f1112070b030103060216050708210309061603020904141b03 70
    0x1007062480300c25186881d0405165001d140503424182d07100c0c051041811108020800c10149034000c0008040a240c0b8480007034920b106008180d2600040c40002024031080c801c41401c1c4a101c26101c3d01c07903041c03c0c00c203c1d6585540744441000040c1140820110310098994a08840c4040124400031008094807920440c0d00401c2c050b01d00c0502d0700402450041c6d2280841710400002d0381e440a01e0205503042020f8002c0400b50101185820400500f0419951301011032110080c0d254515035400ca100c11451900400c0d00601100248030007001d907104c0003002d030f00034864400b40f604508002541502c0281c800380a001c522540c1003080d000005d03940121000190703103500e140c0c40d60f01c3d090000c0d003244400083d503900c00d02404000c0b84082010074050800d04002e085801c0709046024820140d00160070200c030400c3c4100200d524000c0f61042d070006109154200341400c90764103c000b0f12800e2a80c0350311a18000000081c14a0b1940c03c900c150b0703c80b034901c00d40020488010405000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 750597068 1250 750595818 750595847
    0x1b040303020c120a11061c060f0503011b14090d050a1a070c0b0a0902040b1513150c0b0a15120b01081504030e0d08031906060f140315060301030311010c 67
    0x340344202170b600d0420b840242010b001c5845400203a9600a0244040d40c015903c24031104005410a000520f001c0c81a80071507064102c00e034261010080307020340003519800e1010142e840119810348140c59030406104101e030f000c0c0503030303801e000340d46040c0340001d200105490408035034800003402c140c081c10722516015003000e010041a81d40c3c8540001038900d84000f280c00680781c101e403c50f42e0b1182500c00020b10650140d0702c0d107600d6690520548401158001c81c404603911102c440026005000c400310070b1740040443c074944e500c860709400901081c810b1100c64800100c0009a94104141c00000c0c03030303114440d44c0902e641d032000b10645d2400041c1015201200c40400f06001030b0081029110400340034040310b200030b0b000d80740c24090350021500540c80d0340c102c010f02414803d0b14800c01c009131203542040d204090300300c1402020001c1800301c52070003520000125a07090303105c6189a5100c0002040942d0380d41c1c4074500100181e140c1d400c0d018481d8200050358001501030401c0d50304c84031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 750598318 1250 750597068 750597083
    0x30e040b03030d05040816120e0405150402030405070f090b09060f012a020603070906020f120a03150807121a0115050702010e1810050303120105010302031b040303020c120a 76
    0x240f2031911400804015004564049041100034600100603200e8018903004401c3e0140401c01024045c2c0084201880309101e0303481d060400c0005010300c40039a00c40c010a450060302c80d526450010724005ca9a0403900064141150000f02001640c100000c4200c0941e2024038a03210034080c80016581d1082280c042101d12512011852a1348942c2506080301d1054100048160f00404c400b680191000c00c00511500c5040c00103a4040000002c002510b100502c80c001400f810301031070340580540c10b0105900d4004203a11004d58081900c06030003860281e80c04642e6641c141100f00580c800c045582c40035641c542240903c0c031400d094100c400100e0b40700000000e0708400c9a2035030144071304906004660a070705401ea101d0707118405001c441c0c2840c00c815820300c280700380c0300042154402c071301c2035204011100b0700d81140d91080381118004e003005a00c940300c500f910100140c0400d00d2625080e40490000245580040c5162640e80180e0b28003813000101803d0903165003800c4000780055 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 750599568 1250 750598318 750598327
    0x3070f0515090105041a28140c01060b030a05040c060c051b0409061a040e120415051207021c170f04020111030c031801021c0f031413030e040b0303 65
    0x841c803180003003150003014509207150549a9061188403001c0c601812800f440100715a041e03040419801410f1800c4d0002c40b1440700800c100c018610072488040301c803018408074903d40000b0094005070701a01414888549918005441600801c4100c3e400e40e5218101003001071158000c1c0e01c05001d80e03070000040c00d12400d200d60307028901400680c0d05078003d942c843d010400b08416208465050821000c140c4040070244100016100c90b0401285980c10111406040d242040100c0d011104506441e8007180e060704019999406000d08404400c0d114404103c1c0c9164003080409641800e9222044404a040300459941d07403800840f159070086000410780543e000186940e00c144145400320044065019250450300242c0220100341e0021459101e00c014000b0ac3c6041070000384010706101800c0c602e00c81d865600807071020b0038002d000d81c0e00440c0c0391094101d041c50308141c4800714890f0600c50401d50a42c20094000c0d0001003100e00050708914290142804520700140190b091 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 750600818 1250 750599568 750599599
    0x9060a0f09050403021609020705010f020421140f07031a0f0a0e0c10050c0105150d0f08161a060d030e010302161406010e010f0302030a0b0603010b0a0e0603070f05 72
    0x1d02d0041c00030303011351041720030f0b1a0900c2c0b094a1040d014158190025803110030500d0b0007402e40e40a07040c640c40d014014802802118000398003a2010081c200304030810302c019041075420b0103412100b17908180a0a1045940c085001515004480c807501c00100041814003c1101c1800f0540b4200c0c03003440b0380c0c0701041d100c0c4d5864201e0144000c0e400b06451072940c0e40300c002030549080140040224001280070110800207100f0307603510110280905000901440009942411401000700006504040c0c00140303c0c0c8034064944c09070300d00b2001040c100c1c9034101261006104080c5030750411024000034010b01f016180c1e026516816202c0c440c1d4040c4290054001e034001040f022030030318010201f90080340e1481081c41e02d44054001801d425410010001800070b0140c02c00107004d0f8844504000588002403003804046d003141126a0588980340080d000d00402011aa44400503c00219100643c495030a01400d821411a84000c0d650300d084020342120384282d13648100782141d103840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 750602068 1250 750600818 750600821
    0x3040b0613111603020c0a060f030b030304050f1504180207020a08150a0b0d0b01090c08160c110609030d09050102010c0201090b0112260c0d0305040f0f06060b041409060a0f09 77
    0x3c07010720a0050302c0010003203801140510900d94440300000d403195800c03402c42c9405101c0d0303a8000034150065840c182c142808101010800c060550080700540c1c070050f0040c00d10340540d400740403500d00104000d1101488040a034000c000280d11501201000240e03030b0000051007079030726100f5044504c032039403042d2a04000b00322150b1026000180210008001140c482042e4060088103000055160b805080240207050081c4606070103840c1c20380ca540303100d4004109944140d40501c00741a02100350020640d640141c0940940501c1540400044d6903000040c00040e41d4017a8000c019003d2110000c9007600c03a26140507121200280050000e480d0001d41d8201c4076000d02c1c0c0c0104c990300502034200000c40c9036a5a5030620700c012480c07014102d01440040083c00301c5147c18400d5007442c1d20340b07400300c250300c5400030306000181c1c159070700300001c0d904008002c00260542984032680e4584802c2180c10b41949544101840307070008125281c0211000141c1d050031701418032442c10285402c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 750603318 1250 750602068 750602107
    0xc050a121e02060c16030501151d0c07080d140a05100303050d0b06120f100608060d0f060e0a020a0504110a0807171816080322030803040b061311 64
    0xfa04194100102c60500e00304015070110003580082105c2c415255090943c00c42c0c0a4011452601040e020b04004030820880c1d600885220300c01c050190351500d440c00c11945c40390440080005c940401d01d580c01e070328241d0060324014003805040c0d056a5070100800d0446070b003102e10b5801c4220190080c00801e128001900e00b00305074040001d00e07402e1020025009400400d11565107000c41410041c0704149103041d01d412400b5840101c20b00303402d050700136000000c014000c80c018034442240c2c1c01801040c00003900b90a800807010055014000c0c00c0c80e480d0304039504141d0050a0207000006c60b4246480740202441000d02c910b07040c025008811902c91a01902e03003001c0204180c0c0e521030120b101d030f94a0780108615081707007412001e483c0e4074a0811110748441540009004010801c4440210864503d4403c08075246203007070030000e401040441c2a040a8090328021007048100194440701c54040c003800c41d80e24451030b00a40078001513800d50300200f110b0344c6050040c0080038240011b0030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 750604568 1250 750603318 750603323
    0x10b040c23040b040806090f0307050c0f180c04060216050a21050f0c0909030c06011e080f030a0225092c010c090f1215180c050a121e 59
    0x1d15156403000003c0054205402030040c41e00220300344084198200448074010041a015505021003031310303607941341c2c10f4407080507005482036260244076607580c24440c0e0000c0c5640c504804103084c074221482c0290024011180503128000307412003030340c140c3c1b00180c0c1210002071060703001a0030901102210071140070303860200c00101030540d00040302405080180f5115000030141c1c0803090040000314207020f0a0b20b07149410401c01c814900700d02003000340c191820000f82459404002d105d40c0410050781d8011151030140a070010003000001c0003c100307080680c0c0c01c89010781441c001302c4164500c03501e8507080000200a00f04050700780c42c4c10040c0d0b41e9040014031a00159a441d0b000340d49600850303500c00c40d035500c0c42100c0e819078211960101810140400320072003410840c0f01c0c02e0141145e00094060501c04004442c030200c1a000408821007950107001144800e00d004000744003140103440c844d001003030340803a048580712401c94000b03403c180102c55440624074482031070f5200d201c06 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 750605818 1250 750604568 750604637
    0x7020d060c110709020a03050f040203032a190c171e011e0506090108031e070c09060308040603140f010b070f1b0f050607081210050d0f0302010b040c 66
    0x80a0390002c140705102c0100781c2e4041c050303038480321904018122000200741040407110303082031001503100003065030b000900c400e0084100c1041001d0005000c0c0f424000c400440c480c6a48070000c0b8a0003591600d0b62920030000b6a1110780c6507040e560108184841c0914654050b40c1c0d1500902c506084a07441c140681d800040c0064803050314020809114031801740742500d6105002c0c06017022603040d801031050b00081c60070184541c2d0070340c074844c0010030598030281021400b03000780001008008010280f610041003640c0c0d41e4900900ca603000b074801d0a000ca40742082c05882c0c600450003981c0301c0c2141c121005100d80c00c019541c01c045d004080203456842d8214104000141382d00250b0348221451400e4984541c0342200900691000390032032030040005010a03c0001e5400058540046261071b1040440c0d84e45041041c84207801d0788019071001009408006201c4079a01060170540030344d000f88042440761083c4006d89440c4850400010380304000501c109007030b40c0070746514100e030707a50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 750607068 1250 750605818 750605837
    0xf1202030c010810080312070807020c0307090f020912012a090312171503071703090f030a060f0c030c03410c0910020a17030403030b100906030e0307020d060c 70
    0x9845c4c0c40c54200907103080008800b4414400341c5a04041d845a21902920080400b80900030210b5283c00380c9106110030903444941e4028003503195010740c0c901382d001800003010b180c010407105003e030172100d8104840d41c40f01221084c0d01f00c9000c15070054005c036611602c42c1c507455035885901040d0000c002004000c4407128001c4451000f10990b400349100300c50f51144080e40300c04050601c811a40300c0c020901c0c218035248400c03400881590b10b40c1004440c3c08107490502070100303081483c1c150740209241d2600142801c1041c03207500040b680902560700308207402c8000000d404441ca90703010180120030030240040c0d2008204282e0038445064509885400c0c043c411107401c00070250b0340a1381d103100c08162100a401c0c184501414900e003880102144031554883d080c4c010006141150f03d94000000501403602a0300818480800030f0082070780c107100c0c6400140b90410a0294200081c1040e031080c440a40000c2907a1106800034116545031489958040083c404540303c007090216164 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 750608318 1250 750607068 750607079
    0x40b06040f050a090209280905031306020102040e13030806130b0d1a0c03010b0403060f06030c1d0a0501080d050c1618240b07050c06130f1202030c010810 68
    0x41d4034060f445000010808200510404c40d0034040181001d40d030366502c9801c000320008030041c41000c000d010100143c81547c50504a08500c80c109801d110f0a0311054001041ca505600030130840302d040c07052046540b00c00700e203621815000c2c10b000d00041c981c003020503010b241c4048103000c2c0c40c07002c110014409106001043c16240c58a00540d96024040780c1520f00c806800016544164185025403541d0b060040941035030145000c050807180d076902540e0000140340d0301c80d101071078010308803140c1769554040c02100304019407421118480ba40780400c0c200f6145001c0d06050b1140c4002802025a0302c61044070700350454100c218451080c0503440215100c518070060141807503040042401c0040e855420039617801c0c0e0416024210000d002c08650402411694145c4441321911030307541d05181440d40c0380c00900c0703c5590740032000192403201144141424011901c5041e91850155034074042c00310074200d54440607415422103c250282503100f205030940c0805a04030780c030341705030304c90 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 750609568 1250 750608318 750608321
    0x90203131202030409050f040302191a0a06090e010b030c1519020102210606070213020c12130801141501020709110a031b170601020a05030d140f0906040b06040f 71
    0x40109070007580002400f84294045e40c0907481c3d00c00c040c1380700c2d00c206091031f0754001cad5112284094802082c4810341444100244c0000a540112041d00714007198100b481a05004003000d200d1244114a0180d44910030b10040c020324524000040261007048412024050410b0b85812000301000c0200181d4841c581400000c51920036aa800142c031501140d82644e800d9401d1500300e294611100100040c0f40e889104649045605968600c02c0f960000c0501000e4080d4400749403c1d40904409100700d8100c18001e424480307495811089071583d502002400c0f43c001c1c00c0041c01c4140c401e40018a452071940e06c00c40d110310180304035804030b139031000c2900455107904000300d1003060024200480755454007500751103070072841154009111840025011200000e00d02103112411000039075a680280306451a094000059a64501a480708440100010341074400002c42c848042050030b0a11201c40d4800d00c030401c0105001e4403182c4508401e00c200800165000c0e03202e11028044251a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 750610818 1250 750609568 750609593
    0xe1e011110050915010812091323060102070f0515091c030507060b0901080a0f06112206050a051204020301060308070503030603060f0717100801060b0a0e01021609020313 75
    0x40d010b0100e0780013132041d0381034490040e8070604440d0700812000728074500c02000c80c0c0ca00c8408440010004d410200a20040c01301e6460348010303048401d4070302e180000c7d80c07120607101d91801d80c00d881049480360b400c80340c030707940e02d001d000d40003068039440084c1d24182900405411704000c000381d052610f414180d0725071111030702d01100021404207a00040000901a03e00c004d8021620202258108001d950744c1d902044805804c3c05141c92188041c083c080d4440c04922075031145c0c01d0fa580300100b8109080700081c100c051150380010f0400030300d40348100300f07072040d1090694031b070b07072030079055114903d42014013a006030b034103541e00c0c203000001881e00401095a01e1182d0081c40d1285003000030182030004c020720301e101440301e120800c140da81d07204070100c0b007040d50101d080000323440d002030079039040090b41c1000415600e40301010071000c82001c06014003e0290342c0c3c0200342001000120784070454110f920303012200043d410300c98540250091130340140c1c00c2c40170703603805101074440c0c5804440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 750612068 1250 750610818 750610831
    0x30804082214030a030c03052805090f1507120e130f140f0a0c030f02030403030501031b060c030e031c1d061c0e0a06050f070e1e01111005 61
    0x6459108200300c008250010982e010120054140c0303040c42d40380503080c003c500000030100000000e40d00d6100004600c1d006065141c6091f03040001000030b805081548480e80191190311140d880c20014034003344074502c8d001200c401c090400010350b86c8ca0f258030021010000a0102002400c0100e45031210001009100d02001146001d5100e00745011104242c9403500341c41c01410801c4032508038120216007080c800340000440b40c8a16400b14014104403400317440a40c0000103010038190305800880c140c9019800718514003e40321144900c45402d441441d01095407441100f01090080100c0041c8044c00f806607500c1c6941114901c510b400c01c0d0710581d0116110762804ca80c51030340c12054152048050340d56503d407040041080b0303c28810716240320a1944c0b54001e001e2120b1040c40340615103a4024018041802e1402c481c1c81c0c461812603642c2c000803800000c030042d5142101001d41c080c0f81d8071030600c00c1050174000450342c2e0307c41516100300358403076559140c00c40e40040c45014032580 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 750613318 1250 750612068 750612127
    0x1b03030a0f0b01080601180503010501031a070f08190b0315041202030c030f0a0203070c0b070618030f0e06220503120705070b131205011d0607020a03080408 69
    0x1030005900c1086407440022244403500e058800e42099801000440c1c00c42c400b403c18204a41000d0111202c400c5142c20503030301035003450300000410075a0300c220080c4988201b1440b1142e0703280b102c101d503540a06a034000000b200c9502181140c80544003082d405a0581c0000c034140200720b011910b0091004401040812200d0030002404110005445441c0c15840518a091080c82c02980d0701c1c00b071030701e0314100681c0015200520600070811152010390101080740003a0f03a815642889070465001a25503900703124251062415022a42c0c0380039a01d81c551141d0444211000c4034140c80f820602900b0001c1048040380d0605420b01022030002c144d600c1d08401c50808040c9030411141d1600752102d8030090080ca800240c001c9421000d40d00e03c500c2c12a21002c0f02081c4680800003a4440c042c02241c81030f11005000040d08450f041e00a1441450004d0000c40713200c41e13403003904940c0c1c0301c0140c103c060840000303481707001c0c41c0381c102d401058400d051002007a07910704034801d8048002d0440c2c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 750614568 1250 750613318 750613321
    0x604090612120201111b0c1c05010b1012020903010e030c030417121207090b1305030c010903120c060908031512070e010b03091e0606040f0504020a030204111b0303 72
    0x32103640071020001c400341c40244441c40345142e50300c05c0c07800b0f0304400d1000000e103500305035891300041110b08020007004160045010359100f42c0a006a0b034820207035955402c101c0c01e0b10482c2804461100c1d10b02042e920380c85940e001404007002500010b844a5165486a481859050f801c0000d0108501000042d41d9150f24001025580400308220241c03141c12040500207911014400d80b44c03141112040e0354040e1361a00d50031110548150804008a00042041c01da61000710701010141c070002d904031001e107040c0034015a064001b510004281c5000081c4000722103104146a26119110b4080030818807050b590344410703504111244403801c090030b101d00140f451f2901102a150724814050304c0a241445d8000084070014000c100e020a40000030590780b18040140d040c40c4400d410070451072090071459070741c8030101550440d00c0b0b58144580d4209281c012300c91180615801400200e07428910f500380701c0500505d40d07800b90114014010140074503003085821084006a1000c1c0d07640307 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 750615818 1250 750614568 750614573
    0x80703050c0a11041a1005070507150206040b090105240f06030117070e070914120d020105014101140403050601031a011203140c030a052a0303150604090612 69
    0x21034600c12032071003001740b0728181600684c80c1d11080380c441c000716103081c1e541c2d55801d05004d841e20502d50301c016110291271240241d20f95006c10300f240110300c150001d440d261031b1090f07064280e8601342c03948055104e401c24400049190a0880c1d81c624070701818921000d640f460001e14281c00c00d9100d0b602c1002d44100c0001100820300101d80644500081e0300114209840f000300103034880c1c040d8209a00039000240c80c16603840512413440c040ac94201c801c0c841811030001e020385400c1c45100d000c20070b40185140d12a020350b01b24481ca80c0c000f101261501c5205e91b00d8111540380407102810700c00c1150314400d843ca154002807020710300403002007145515504d81b0040c014544003c013055a00400c1c0144030800e46010503030700ca660540791014540254a040300300c039206071440c9103000c1c400040c18040f0a07070404040c00030f580d040300070941d8044907041b0311450302030b148601058640041000691a4640f5a003460031403030f020f4242c40c00d040d12a255103003194455000b101c40c0c5240d48400004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 750617068 1250 750615818 750615821
    0x10110111091309030c1205042106060f0810050a0f0c0c030e0117070302091201060f0302180c2b0c1223180f0105040c03030f0e0d080703050c0a1104 65
    0x2c440501007410095900580ca0080110055500040c1120603e04540d80c1d4148180151005403020440d02d8000070010342c090740e44c42041035400c945090038548005240140600c16400700e41a440103000440008134002e0010003005080034143c5540d403480145031321003407044c0c1945114a459030b410b5821103050150060b80000c5d15581008031140c4003904000d10420f0068001c2c5603070501684a6801d40006640d000c0c0c2c02481104d02d62804000080c139601020031042102c0c000d964500242000030864008010b084444018a00341004961103a14030017040c0c54100d80d104a214180140007030204050b911480d080b03034006003020003111580310302c51150b0f00000a0354401680c0f1a6040c48201e1480080184003144101d400741c0c011010039000c1c050301514131441402040607140038640918016000d01043d40000c4442d00840b4817240200c80120020500401e00c3d0440d00c01a42d4842495104510032020000188079510002204201c48004da5209111740110942004113000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 750618318 1250 750617068 750617089
    0x601061d041d03120a0c0e0409020d0b0c091206041a040c0b1305040605040e0d030c0507051c020c0a120807020a03120309291b1603030c0906110c1011011109 69
    0x86e02d4100d172894880d40000d801c5005120580b0003080543c442d000041902510714005004560007104103c1d000b04000020301076100304694100d000c81e07100c84c080740d40d0316089500038079003050307020720442c000e038484441580a80700307541080c11180c0780c410880e007581202c9010800104032342e509000c241707010b0051101810302554100000c0301c1c003050465031410044558018180d0720a5548192440382040310107440d008800ca5807210707100503c13203c2025030b08070301c0401406000300104240c50074402d140225408180c6020529481d41c9920090303501800089071b01102034800000054010290a01d80074030350f45000880b010b6901341041200c1914507039580303842d00c50015140380c92a4010041d00122601d06514801c0e548902c081400c0c131810403164075240c142c0c860480bc060b03158110707550589035131703070b0745007a01d5075580302610445c0c900c0a00702c1e1950000401c804103828005422001002075281410703000701941d10207800c560040d10348400c401710014240c086c90410701501c6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 750619568 1250 750618318 750618331
    0x41d01151d0708070e0406030302100c0513060e03160e100e0c0a1202090301090f140105220507050406060c062a0c0503121302120601061d041d0312 65
    0x307074a03941c500300c05924a800080c680c2c0e05000200001c11000351140c80c0e000602c55001d4420801d0549070b05019640300000e2007162103c41c144011218928801e0054801c0008454203180d00303581030500c15190010f080840b1601403041c9080209a02d22a10440004200c2c41c00f0380c420b00d017414007400d00000c0d141d070001c00c00100c0d118248001750b4500000c2300c07200703034242c07500d903028031540451039010384500401244e040d1b080c051321009104280440d901d489104400c00c0308a611001e0002c1d090318000c891000c0d4a058601440080e40701020b0944503c41c800c10079518246d8940000404440c9103802c40d00002d03c5104644c401c0011074402d110b5621804c8014503941201114003d0900d0b40021920307007000019442001085810419034009020040140c03c0e640b901c1c1c05000b090000d900b01c240d00c602902e944d45c01e020a004074001d4140d03a116510b1b060503040c02c1440c1c0911a50798440140c1044d40c0346100b4020f03684000300c80c081d007988070014560310028921700144c124006440c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 750620818 1250 750619568 750619589
    0xb040b0702010c0e1f110f011d19060b0609040609050106110c0906061308071811030708061e0a03110a0f0f090c052b150b09040506041d0115 62
    0x180100d680d411959172000600139607000000e40503030320100e80199036640c10042c0c51081c800f1081889906410180d0240c0d203210a820039421144045a562518a1000c3c10110441c2c19164003041840d048031054600c007502141c50a18000c1c041002c0314072a5010380300341c40c0c0d242d0040c0400c0341d0101d6071014500c5007000602030010300718001244481c2c0501014403c020000b004203101c620f240c3c82100801c40304058882050359941d4000c4162202619021150302d01103a0500c99810302080d03d0080c20700380c5c0d54120755a200c01c188824165603414642d1600140003000d1903950310b0b41c900300c002d188035880c01d075640d580c1b40342440b220f0310780342d08908e0701c88600342424426075403171100403012aa441340f00418000d40404003540c20b481070500195a008240d2075104485d4607603229006556451601000a520910b01034400a1283c0c0115800f17213900700540300d1a4900b6402507034020000400000d0482c4100850500d540f0740702c1c2440f0900c2e5110124000e4001d803581e001001440002e54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 750622068 1250 750620818 750620837
    0x2030606041a040216080415091d0a15050d030309210c0308041e0f03110d05040618080102041d010e0402010522030507120c1e06050c0a0b040b0702010c 67
    0x29000c02140b20a6102e40610380c003050740e40200f1074180c4054002c0790482c800e6070780c542c3c0311060b82140705407641283c0080b03108a040001c0b10400c805280110030107400703000545d61200d280803c041c009050305000c440306420300107e420b550392041400e00d10710980300010803c40c0c0740f40981c0c0e4002d00d04640e111002e00c0041c1580b0303e9801c04408600c51782d240c94281038a0342c0d0f901d40009000c030b0300ca440300624003030315454808100070b50886051090003522208072042c4005460355560407081908000034400384820000399014044808012460b5850001324940740c120312800c90304190700c055088004401070710118030030a0102405009011001960b40c070301500040c2c2540b00d1420820700d54400710040f1a00101d0700d4a00c1000780d075100e820780343d0300c0c0d03550103c481a01c0c1ca050b40c00d1b0780c40030350003070000f418142400309020311803003d140024980e4600001900d03280c00c900c900d08058001c1d400c4440000f0490000144101d01c03a4100030b48504052034000c0c21100001c1103001031200b1401c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 750623318 1250 750622068 750622091
    0x5060d081c0f050c040305010e160b1b010f09021302041d09150106020d0207170d180b13090e2e06080f07060201050601081e0a020f070c030203060604 66
    0x3044604000c861420059120000d10031400246058810707050710510340414448480d00c0c07280244212800340d8000c3c044004405415512107204000b2040c002261400400c4203591080290001001a00303c03503140000c0c1002190944540310300d03203400075603220544821440d25801030900f1008030201141410704100c40c0944040900b62100c4040782c03018000340d556403082020360941d66143c200c912695950b0400a03681c0d420b15404c59015014482d0003003000d21800240c0c4821000706002082d1030040d0202c00d8600302c9060005400c0b00d02c0d582408201c80c0d40240041c00403520b0442071000d22403509070b1003800c40b82184c0e4000304a40095521100c4080002135826008801400c4a6191030140344400700400c0b45610440c944e000302441c00c003d038407012410500300c2d18190006c4c80160707141d02c011119140d0031951951201c00ea078194407090032003080e006500c03482185006203460b030040302105150b00701c11002c0341c01141d105018421800c09011071600082c080d501840300c0386441 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 750624568 1250 750623318 750623333
    0x9100308030c0306040b121e2404060617030a03232809060f1803140a0207032315010b07020906040f021204060e1b121e070905060d 58
    0x7804a42c2000300c0400442c1c1c2c90f0307880e40d11031545600020884c1107440884000240c0b07409001c0328503545082c81224418a120020031005214141501c070b501000b4400803100704448030241040d80c541755518000f0a5103420039041410342c0c80400025912048000e000906a600c0111101c20381054020205003c407200d030002c0350064005443d801e0840c0300c1e01202c1e890241d0000c45250307005d04103080d4100f8032582e50b0110100340400c0b04207005441c0030f201b032220f030350300c0690b801400208480401055074103000e018180320102441030300c152640d0398499a03e20740c4018280c00e007903030340c00000341c0c20340104224143c0d60b6075004000740303203d6150071500340301800f4522000c1d000d690801c1c009909070781e403036010603032645203001e00710f40f101c0260301c0c5000c03040c100725000c0b148145400e0b4156103000c40010389014180344461401c100003070b1502480017203540e03910480c6981c420544c0d580e204070420407040500800310001070030300901d48403032681560f40107403c880c007880c2041d0301e65000c59043c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 750625818 1250 750624568 750624571
    0x5041d1b09040201111c120b06040f1a04080706050a0809010504030807050c100c030902090705090d02040f020921070b0705031e0717041829180112020910030803 71
    0x2400c2c026950303807070741c15917074104a46c1105409030540742a5440c05030380d822041003441c0601c400c0003080301504020500c000c621441c0920310403d41e108401304407030440122007e0001002d86582070810380d503100e9072480c102c83c540040b40810008102c4122095002290350b5000c02810000e004030b0509450103000e04002810703010400800086101c40399100708a040a0304204034002c000305409800000c00410111904074800e41f4a8404116014480d070709a90009070010031104040ca00381d03003004018013a54511a004ca502442807070b0b11640d0b01805044100c4850008004840490428038280115a0003448500d2428840343e070100300c0001c103072042c0510820409102002c014020f056600660710010710003038088004031a074804100140c42250701c41c1e203035056100c1c1099030840c2076803401ea000c0f4450780c090801504110007100d51400b582c00c000b8120900c0e0010000d1380c417200340d600760000003401002020440c21070801703480056001d00315808032040d260440d56a80500e100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 750627068 1250 750625818 750625823
    0x90504020a0302090a080d03200a03090c0b1b0118050307110109030c1203030f0e0a0b100b130503060105040902060d091b030311060a0c0e0d0c05041d1b0904 69
    0x6020a5201c0c100d4000d604031203c2940041418410590340c018860f5244101c4001000180c00c010540d070b40f044050a040c8003800c0d0004650f801d00d0702c030190807070090042e0042600c400a004100040888031800204070161b800749440d03105010800a00d0b0130340341c8101c802c8403140381c0c072070045000c03c0d400710540b04038580c4984c007000c2000320140100c030010382541028003012646417001546414182c0f10780c945a129032070a108200107545100c0803500f00040d09056134100c00d46080000e84c0486070300340d1241a180c8540d04035034413243c0850a070340000c0080180c51795001000c3c0507624042001c5401440125428404180182d010a12600400710740203082e03901c0d10b2502c420003500017003d66960050316180210070340d40b820700030148a840c012045290141c07002140b00380d40c0c140035104400e4604e468040e00c03000c00005021141e240841d003a21070720710821010070700d40d0f0f8901890708100c981e01c00308544003106d032210300e040050080b0028250304040c40c22040540303590f041c140d407154 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 750628318 1250 750627068 750627071
    0x1a0108041101050f3c22030b0903210103020d020918060c0a09080c1f030e190b0907050a0b09040204030203070902070c0e04120302030901020702040921020102181c0c030507090e060403090504 84
    0x300701584908240c8050f400061070070085004000300c02c10000045c3c4100081c01e001c01c02c46a1901b82d401499800078040a1741100282041cfc2e400350030a405001c0e0044000189101c01c03901039201d050804000b035400070190000019a50074843d4041043c1000c0d203025809804c00107003020001d240a02c00680c943c114600705040100c0d528066802001c0200a41040d01c082040585140c0700303400d034074002110511228000f05094100014a05c02a0388004c2c00388070b009402c0c200784080caa0048841c1d581e1243c0c0811000c40141c9080c02080c0007800313020400b40e00c52900346400c0300b403030b80160000c6220f402e0010402c8080b6901105000c3c0e42003ca040040e84c0340c032105401d0380a44518000030f50420304044100381040781c0c1001d554085100840c14900707101e16400101d090741318111330001c0416112460400c58130301002d88114030f000503140340445414170b0f518068000c08545c000d8a01c1e0300441c1c010000c20405004070302c071001c070440242945150603070b40640078103201d006144c01380303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 750629568 1250 750628318 750628357
    0x20303090d140d0f06050a0e04050d230d020406030b060f07020d0606030221070801110d1a15040e060103020a0f1404120f0203011a0108041101050f3c 66
    0x400340d541121006090702d03c0a0114080c282c0c0e002d405000907206140c0628064a00082e910380b40a00380c03070203103138400082d08048261120865038080009440b49000844508200c0e03034210310130042180ca400c40002584a51601c1c0d4080d00702e8960404080c040c4c5410000d04180001e000125006961b04a81c0b203500c011207070400100030302854000940101c911201845c0a110480040c900c00c0840b20884001c0783d15464503609a600c1014102e101c0c11062000000d43d0304660850440c10800301680c9002003900c1d40006c007464050490114942d178002000c2c0401030107840d840354005001c0c2000e505e00a00703044000e20380c160003142074040050480d4502000e80181045038000c2c410140a00f20404131414503d480c0d1600d00003c034030a40c0b810060103400d4107038000403081c080b0140c440c913a86585640340c0300c140608500419042000411140c09409410b40c0617000143c0c4211400710001c030054061000e010121000f00088803604500f5070b6000c1c844005ca070180759803c90140c411 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 750630818 1250 750629568 750629597
    0x1c020102090a03051506010906210209100807030b09060a03150b040c02010e0601051207030f170316020c0306100b0c01060b071217071e0e042a020303090d 68
    0x203000d00822280c0c40b403000301d800000c0c00790014030380400c10900d81a0708a1034a4003801900c1286162281d2004903140c1440c2a41c95143c0c0c7d198800d02036000e0101524150700071000600349602840c110000c00c007500c00b0300c01802d5140c0300d10001c5c103105903240910f50809038001201c010491000901d40c5846105c0c6850303005940e00500e2442d0300107442844805203c080c083d01904225601c4c803000d00c1031000000e074a1403c40ca50580390403040024050341829501d81a2907007200400940b440750b0000115001d0b0000c06006620609141d03210392220811041c000781007841a0b40d00a101c2d80c40182800b490b00c58074141f170011901660119552682c08000e079a000d4209603000441480b0089020b07001c3c40041c2a0031080c081503a5964900440301340759800d0150010f0307035802d001421580410344d81e2204ca061408450895080031140c03e1000000102612a00c81802100e59400e01c54050071482e0168103580d000514000386080d454110b802641e204941c1000900b040180e2110186 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 750632068 1250 750630818 750630821
    0x80714061e0a0e1504080324060a0c051f150501030b0a140f060f0406090f0602251502010b0432061203030f0619060e010818150a0e0f1c0201 62
    0x20313030608181c103003840c3c60103080c859250740048640322040311070880841c020520a410714203107400d00800c03c40c14024034540840b5640c1184008441d640f091281c1d0280c0e469400180c10701e5510781d0800428103000740010142c82c10b105511103810700d401c100c900c1640ba070300d005181c416159071200320700b0080e4041002603816600c108205401003000200c0d84010610307000108169070785a21039985c3e1a40d141480e040d0b2241350300c940401078005035540c480c030710043e1480202072a81030700342d82105900c402017003030364400e0307022410050703903541c404e104035801c150085000c1018000307a45652034041c4860000144d0300000308221020200d00003a206507140d01d44102032843c00d500b241c1d28cd10713091b0070320259050f080c0e68040c41140090b580000e4143d02180d00d0003910f425a803009060a40c0c18015640300c80041c00f503801080d9040c2c0005108a400c20002010030711607444100c49003012001c8a003215500c5401202c542c20291200244c100001800d00744103800d0341e0070300c04240d15004c00300d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 750633318 1250 750632068 750632083
    0x610050d020d020301050312090a03030f030213080c0109061b2303031602061f05010509010e131d061501110c030105070f1805031018080714061e0a0e 66
    0x61000d032011801442c1c188041d0702650598500344c003240c1c4404810300c110402e900400000aa02080e00718003440000d100300c981200c0070040f41000b5040c02002281d070b0403002c1243e000124994082c0e41c080c4582d42c0d101028400034200b605124440840313441c281c00c0e020120300009410b240754a111080600310202c00300e0300f039803041c000303498130b074108240b40036440f9040e810f200005104410214400b00000c0f0405404400f807070441c1800a4034041c015145600148603544c18040c20320610041c0e81c80342c0d40d44810700d8001200020b001e030f00a8810030081001c4c481c21144030b0784030f001000803a038400410b41d880b90700242401c8000454810003c1c3c42d0000d0601100e4065091030148240603422902c1c44c0c0080d8240e0306c84c0110070800f82100141c108a40c810140d06034455483c44a078501541e000b001d810b2107180404032941c0854032100195403045408881d80324110f102c94020090034443e99404c00c07003000345003c5036020310300c801c44c98410140c6188403003540e0b050918030709030042041e503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 750634568 1250 750633318 750633337
    0x2030d091505010f03170903060f15040908090112060b041202120102042310021f060314070501090621021305030d0c11040b090a05040305090a29030f061005 69
    0x140000c0d1303180c6603070b02d4550b041c500c0700302c41d0702030b85207910b88580f01e180e0243c030b086010160007040e440e07032846040107060300040c0c0145030400444284802036147e40c041c0c0003c240c0038018403503540402500044c000c00e102d03c1031340000b51030030b201800714801810441c0c04885401d041343c010040c4c0d40c00010a05400d04000084661000400041079604090002c4181240e128800e0407401e5541c20711405c040141c00e50341c010703041008000c0032a540010030584011444000058503522940c0e1a092400040810301c034581c0480d07000c00496900045071005820546018844101c820f41303c0d0403440e103a4040040b0842c1c003c03e09440130308109804000a0400a0480304002c60184010f411728513600c001b620b02e50011290240703642403902405035a018040e104034443d5441402c03043c01031030050000c40070050308011207840c5950b140d0f8210041c007194503280280b81c4080390010300402c030791201144004002c0c010002c0640c444070055a11100c241d83e500c8145400c9801200d2034846c402c00c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 750635818 1250 750634568 750634571
    0x80f0d02040519090c09140909100c020a1202011e0504030e060703030f050a0507050403030e031e1c0207050109051c0209070c020f030a1e0f08030103150b0901050102030d0915 77
    0x143d00c01c0b8450580590480343c03100820016041c00c00012200a4074038040c038001660000c9220b00b2a0400c0001250b000000c0000d444941c6490f5151000b40c0301020103c03070044c2d000e00719402c11f1168070840c043d204132150008014500c100b8601e643c40759245400c00141d40c0d40ea10025040c0f40c00f90f0380c201100fa0340141415a03600142c42c0140050400d0782800d2166450a400681c40003040e1252900449181d12a5814645542d03421280000058003860b0940604110000103600c86a1b41c0c03021345441d200035000101c6070001e030741c1075a03148404100455104510400c6140d800c0345403031003035440a5801c5118203078803014000c2c0007030b12820001c0d00465075504000145600c0320b2000d42040c801c80301e1142c42032080b020195110b40c8041c000d81768072554980c01183c00c0007035140d003481034480c9040e582c1000184e144c0c0c02003604241d000f80c0f110041401c0000360300c80280700300a00c803c41125802002d50404000039501c1c0500701c21944455590a006411b20052444005c0700c80ca442e8030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 750637068 1250 750635818 750635839
    0x3314040e18010905100207021504030c050310020712200f0d030e06060a0b1b010f1d060709060503090118060b01080915131a042607080f0d020405 64
    0x8403080825811201803400c0c00c950800c1e9444a0018000c1c1543d4640250051562001c10080030000f940f040b4012607004102104400e442903660740544000c0d8040e1940140349441c00b003d041c1486040f402009032548100002c0c3e00081c0450350349004d0030014500340300d10f80a0150314140c942c0341031000750400d10030102190015800051000d5400c0d080c1da401b0f101c50074240b2040c42e036482c2d007650120b43c4038113508820f100e2400590060141c6002105103424000724005035242194001c900951906496240c00814501e1b0b0f1003d0044034001e02c0020000c0303160841d001040360955005403000c0040000104080300000d41002c1c81c050052004118001e10a00d0b00f10010250344c40400e0216018a001924079280854000c40602c026040c803001d0307503950304528056035800a411652902904070300c003d45c038211030324a40300718800c110742c03c4071028034031038800361107440040801d04400030071102c400140a10306076480592032020854844600c103d801010f8020758009e107400954065 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 750638318 1250 750637068 750637079
    0x1809021c0f020a06030c170408071a07080c0405011d04150b040906080c0108070c0804030614090114090a1415040516240c052a0a331404 60
    0x218000c9040c0d100f154811446a601e6006405580f41c0310101004140702c2040b2200d054542c408081d1310500c500101407034034116998140801d404100c0c00c214002d01e4034200054990041c182d1a000601032441074203203454900020180203840d0421002d100000c0c000608d20f481c0c0ba00950307002c0c03880302806408144c0b03c40000a00d0b411a100c0c01c04e0690401070b00142d000b038003141c848120f580c1a92045000d40d07030510142c0390b0030100f1104603500301c2c0420002020886a101c1c54161a40e44041c40d03046091030507035203081d1100445580076000700780003840610a8001030810070141e120030301c9407840882400f0070b400d0558206140002c82c070000104010032501142061280101c00bc0e210407807074803550140b01d164001d14030382d20b200241c240060034081c003801e850801c151103103046510a012901101a1a03607003003c0b000500d20710134072890303001c1c0382864841c80034100004540d502038460b1b16240e00001f100014035003075464070700006080280b0801580841c8210307c00c01607915030303854 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 750639568 1250 750638318 750638333
    0x9010903150e011404030804080f0409140402040c18050f03150c032401050a0809030c010903030608010f09200112052a0a020607051c111806041809021c 67
    0x2504511081d4a0420304044c5894004015400b03540c01d541e9883e855903440c0d40d12185076010040c0035485110034040015401c045001e103403039814003612494101e0030681305100c165020188040240120040c0c0101c101c248400580212603080765142ea001c5044c5010038101041c01e14040445c11101e82040885000c000045001c2c0380d1303804402281111084c024160141200b64940c0003440420a104400c1d00c201441500800080f054a242180140c542d50849e40244412400301b5100c1c0010084a4400e11410401c550010418005c0020a0356007c0c0d030030074001d2902c080c4034441d03152812240d02c074004000802c14410002c200c039091003024402420880d40d80301055884484080500c1a00f1605844100c08940c00030029502d50076400e40326900b0840e0140300e030307021501400900c0d60b81c5000300d4951010602d0032a59510640c80d035a003850108003865405030104100400414442400702031741c0d2080700038000741d24a41440003038a09800c0171109200d0321a0b50700503100744102c6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 750640818 1250 750639568 750639581
    0x3190f0212010803040612050709080f0d0906050901120c050405061303110105070206070b04110a0620061e04050c121615090509100b070b0108070504060b0f0901090315 74
    0xe0125182a03070f80d940803410358038440d602490000800c2d80c4001940604c6c10f400050b000078813404c1c4910b103c1d46079134040d45014400c4803409005c3d031102c0c3c0700b01d5042da04a1040c1c0060003987c0303041c0c0c0c50b0807424000604140e00e84080d0214003659001040d00c2e0600c100151409405c00401032540c42403001c01c2640d1382c001c0ca00040d1641a0003084000207980154119049242d01409050500c0380a458142c0c1c2d0000080064600c0f50040d10001540e54079400298040c1c41c030364444e01030080035803c0812001144140e9107019500020a00c20000c20741200d0801c19940c251040009035518688142411907a42c081c0d50045481c3c0d420000e510400b045030f080884070035030480e03002d0b680c90b80001403850540149078045000802d0921040c140450a69440f21005001281442da206040d18440d80592001d40d000084040103201c504014032005000b05000c4809101050400e181c0c040769110352210703610b400c0030000d86800305901400c0207400854100301544145402c10b80064040c003413 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 750642068 1250 750640818 750640837
    0xe0a0807060e0f0319080f0415060807060f02070f03030905062508120601020105061c03090302180709080c03031801032003090d0513061b12020d14070b060603190f02 73
    0x719052840640f00e00700319071046e02e01007d483c4054590b80c84411100407036a940d04d00030341d15644081039651007009004c2c0102050764550003041070b01d4a0090030f2106640100c0c00c0802e0303c2c4400c10101307034009042c1090354401c84a0750341c1e8040010403020801120309031407017500400d2902d82c0511001001605a0401100f5422203580c1c0f03410049003298021246241d00680304c01d032240900307141036480c524040c800d040007002207480303400003003000108210020800122104102a031907002c03000100400891300145240481200000e49074084d030819060a034400c5000c2c000140e210341c112030541c0008050642083c004c9004210403980220390b440541c1c41103403120034000c0c0c8a20700b1981107040d0460310142c21400c0107004c0312000310592801d040482035180a0020800caa03003141e04801d455002040c06000116003c0c000d016810000c6044100034441c0c0ca000c034403441c1a10b503000c1800c0f120703180d9a640f00000b900316036480d443d66280b11460300c1c003d40004103140d40140800321 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 750643318 1250 750642068 750642097
    0x60403060614133605120316091202040f1d150c0a05092701120506071704111215010f051c08070c0905091f0e0a0807060e0f03 56
    0x501d00c884a4142c0d01c0c01e00308040c4000c2d00b020850041c10407004c400031003070900103d810030800d49480b1207181910580b07801400200010034080040c880b040150300c0c052280c144502c40c18a8840c0e809441d00f084000039000c0c43d00c55440d815901c415601148941c140800307800c58801c480a00a556144001d15090704031172400b01003804020840291540c031903803669507030b14120713401003130282c4107403001c3c1844007204540c080d1085071104105546d0180a0244240301040c05504140740740c158094021424002000000d24135040c0e2210b1603075005800803004000c0c0c0d41c0c28804910380c0c0040a00040c680c0c0990343c502da045400004001e8101c03a03401007400030554845080044c90305580d1011030307a403000c400b1702800149002001e400c00790f000e251040d080716680d0480c5c10a4030802c42d07550505400840901e00c05600c141c42c0314407081c207205401c01502a0300b03201e890740c5281c000000f92440c3e5001c9032030000c10105400060400e00c0307402c01d0b40c4003150f0360001340c0c0e0390360888840722401c030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 750644568 1250 750643318 750643339
    0x41e050a0b0a032003030a020a0b0109020405090c1b03130302241902160e160903120309080f12010302010906021506010302071103120405040e0613020609060403060614 74
    0x1422030140c0c07095528000c00b000c402e2891652541d42c8450368028002c0b1190540155444683d0300340058410360340107401802c80340c01c2e50f14141c01d400105802100b01c49105010a10250300d03400c0403d030741b000741200030030782d41c01948019131307102164100c1c148102d100000b45071380318550041c8520f00b242c0c400d4a101c1841846040e001d84400c09942d00104000000e000041045500380c0c0112409a0103005403004c440d208021004009840d410008800503c4810302c41944072800414854141d24501005100d0031a502c00e99603503120700400c42056120304040c41444030900c11130380342c03021441c0303002e9a40c10004c0da8040e06940910003603000c100c400c500000c481d80081003030300c4001609420000e8075603440005400942194000399004403110718100d03c10b8070104071041400f0080d984854079549842c08000540e0400306403012550000340c14070643c42081008010300d2503045903900d131a4542d034004280d860003640d001070282828200002601d00d01d0400483c50b82c04181c40e2645c15 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 750645818 1250 750644568 750644581
    0x20d0305041a090915010c0b0c07120f09090c050906040312030e0a052a0d0c051c0f0b0717040b221101210f1d010603120c0809041e05 59
    0x224080c2e082029000f001504c000b6291000c2544c001c40c02e0001410901c0e08080241c450032030710901243e03a40c00d0808005500e100b48004483c03280c899407040d1400d1261514515001813803d481072107140c00c000d80b0383c8820f03203400b40980c040e901081d1000c1c0c02203803555079a0400c0318a2000c0c1403080c1010914100342000001808a40034601d50f0700704004040114072020120302d5100d0225081920741c00d00070310f507000d136030720702c40c0524060b4000d509804c0340310b0514040000c1c20090124100c2a00703814a00540050800c1c060342032000c1d04a0009a541d9481c05403d03240f044488a80c400e004100030304110030800a0b00056000341000b1209459000810000e42c1c400c1100803800b0b01403414034419580d0039841900130305582022038044031003646482c6c030010240c88540f00701c880c01da902c80c40c083c03454007810904400000d003020006d201c1c0b503280d51208074120004168100800c00404c0c090800d0112040848030704881c00382003084854070320205144c00980c0e229103003c4c92820b04022502 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 750647068 1250 750645818 750645869
    0xa03051b01140a050402030715020a02091909110a0915150207180e060c0429040906060203031501180905040f0209090d121b180839060901050a170c0910050c07050d020d020d030504 79
    0x1d2402242015013e0141400850410b10100a0305a0110300c1580c20125242030100e0840c81c198a075070030080f030401c0e000390000d401c1c102e00500c100304041c41408200a00f44203006080e040c1034454400c03044d003244100c4071101c0740c860b50300108800f0b410110001240c6500000852103810b02a48281c040c124010044440e10702241120282030301d10802071200d24140d500c0160024458081c076442064140e0106480900484a11301c003900407100041071036401100c0b401094106500402c541c824080040e03100c6d9114401030010050380107000007808c041c455050010348a85030840c0d05107a2018403440c4e681035140052008a03c0c600070300c243c0c0c1034101d1401845104000d141d1800c015a1400440c0c00ba001800c0d04002c0181d08c201d09a081c621400215004504c0604072540c1d80564209105864504512450411104000105c03218001007054000d9400071138541b03a4111440c00012030304c40c401e03180690301c2240d06106500701a00b1400600403900465425000120030100c0d084 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 750648318 1250 750647068 750647081
    0x1210030203030703080a021c020c071202030a0b0403050708030103210e030604031412090706020d0519051b060f04060e0a03051b01140a050402030715020a02091909110a09 75
    0x29010b41c000d00c070710030000340035541040d0b00000700c01005080c42c07070300200994040f11070340c2c00409103079000800c0001060306000c2c1102400c5c00c1040c080c02441b9550219680740c14404002c0c01401c0d0710f0020504061184c2c089800450300500c000c4c0d22940c40c2d04019040842c07102d40c4120540840d100049003d00825482000200050103040542c0e9242c0b070940d80c4010320164204803400420400200e0007161923018043e92070080144003280c1800c402a141044581c0d508081c4030b000c0c481542c07007100105010891307084504d40180c4072888411984802032011003001903d014032410002c00ca035038020400d110b90701500c1d013804456140288552100c81810004c0c00190040040d14541c4550351004d02c040164480000342c081c400b40109003151100391030071800591107009010551408001c0c1030050502900c82e48000c5405150203940c485a54100900841e28600000d500c1000030340d030b60303124580c0350b0001c0c402d41c055450311164042841600341d2040d60505004543c40c1418407800c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 750649568 1250 750648318 750648323
    0x10e1218220c200f061e01121b090b010e0103020307090b09060c0316060f05150907170903040e2a0f0c011109040b0d200d0c0b121003 59
    0x20268510030055902410034124031005203c0140c04501100d00c42c000d0480c61880140064600c800c00710030340d50305001d405441051000301448912600034582d404a60446400c40e031001c142200034582480030702e526150012110a1503003000031024800d800080385e02d03401b40d039039040d0100880015070407404159030820010302800c401344420014003008101e0400c000780000d06040b00204018959440700d8441d4945500d8040389004110076405110300030b080c02c5e8400e001d14600b19045600c1d0900149580f403040114001103680c03a4055504542e03000d40000d0701e202c40d450b0200308070396a42e109114052100d01840c0019180e01c8881940c174a800800201940e002d41e40401c503080c864102c1d0500368050b1400308542c03040401d003403103000c00340400b041140380c580c8000c00802c42101c0740d140049006000341d0f041580000ea840207078217042c07040d0190740540e40c0f0003040070038000340110b01d0040149046d9030020460140720805080c242c246640440020341e01c080c3d062440b000c207031000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 750650818 1250 750649568 750649609
    0x1d070215060111030c0a0303150f050d0b0c070215090118120f02012007060f030219080a231f0605030a0c0536011817010e1218 56
    0x461100d41c440c3c242a10f042d0f101c1001ca07410100c010711a076090101d240c82c1103011aa48048202004e000380e0301c1030300281051007140310318903e041c012400c0080c8412008003044800ca0008080f0482202911000d5030081e1200c07801450300320100c001d40d40880d000310f021803d400120702000056403800e0b03040c0c0c0d00c501402c1c3d52500d251741e12203800d00c801001c128180185003414000c0381c2c8007201070389030346607409006006951070040c2c041c140c80e0101c1280e00030140108090086c06a503031490071921a00d03454547c806030b60b500c120800902c510841c030f01d03840c0c021003e01e2030007a54003400740780a64051002549904810220180c412980b8868140824014800902c1040103a40f00030b100c036003541803140c505451a038200728a00c420100c103107a0b840f4124005003520000c28605a4040020300f00640405110810034007440207030f01c41c0307440f50b180019100c06014000c0d0810443d03026400112040d241c86805601c40f5a080921840c1101c1e010500040301c92402203440c41014442c00c21 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 750652068 1250 750650818 750650821
    0x50307110415290f0d0501030b0a0e060601110c13290a090b03010209220c0908120c070506370c0b060301060503060109091401020a0906120f0203011d070215 69
    0x1000340080c102003c55002500c402e101c80c0d0400c0308440c0c0180411038091600113202e40c15032030000c0345030070f014100641d0140b400400d00e0f00070b01c1c00900c00d030304100242001034a0180c0703401c0d51841c0c1414240100d401158282c0989140701c0c0382d810002140f20841103401010f081d05009161480d810703a005540801e00100130010b52082e94028009894083c001503e000c840b0030203d4094503100316413182200340c0c40c542d142001c403070b8455100055030601c4e25a009c40d143c02d4407149e95580b080c0c07448560440c00214441801010020040203100103000c03c3d40307c520710109986186050104980500b02e001d203184214019504c01e104501d016840c0c07203480d401503869201c1e62580042642e0b80541d0380e100c0c0070a040e6402c00c9003e0080c100e011010840c08242d00d0080c0c000c1007807248903586a03005014101c04590042001019244a1b00e0000c03010111140c155004c0c00b01c1d0491581131520010000c40c039600950b2013802d50541d00000c0b811a6158010102d80d111011000d040903480e4000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 750653318 1250 750652068 750652109
    0x4080c2103030c071103012a080f070e19140111030301030b010b03040609060504050d0207060201140a240602101b09090f02040b0c0601062607120207050307110415 72
    0x4010705003960060305405d04040320030b000319017180c916510060f00c0400048000c202103804a0500e0382d48041c628003040300b0309100614895041d00940342c2018002031030003895103604c41d480340040700290035401440103540d5a103402540314031070081030300140e45042c4001d1401400000c03241240e911551810050380381480001c1e4035000600101c6000e0344a4550001155a6008050080f401440944030102090b28060318100c1561311100a40e41000c51600b03800102c401c10a42c0101c0080e0049401e800b5007800220120380c200489003a0a6480d8000c0348280e0700040340711800d0b130102001c219025804c1c140002c0444810a00000600c0b0841c2c1400500c1e801d40203000c11448036600541016250a5132040a03080a41d9107205584810010052168450303510b5181c1030109286000f81210756584000d40f1030020110414480c0440210240450550403078450755007080545c3c5c0c540b020391408900040c2d43d5032a080c861070030200384100210035030500703004071260300e03940740b07222005034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 750654568 1250 750653318 750653341
    0x603070605040b1c05040510060f0f030b040303090f080706060b160609150207030e030d0804211e0f030f0e0a06090c1d040308090313090b030f0304080c210303 70
    0x1c0c54410011300f407a04184050311806810f0180344190050030b0021808280d003021070f8481ea0041c0c6c5070003100c113010010b08001c844481d094a800202c0c0b071000f580c0ba410141d000e4008500d00505400001c4d00c0170041c41076440181802d24803402d418880c85035900002951401500c0720f0a00c2c0b2095100550002380b01c507482101868407501c4048540103450300d0300c000700c8e005120203601158104161001901c3c1c14004061f80140740e0801d031826090980722101110080121084103991445050341542c1c022048424440d220b10070880c00b9501003d00104502885042ea8004c203040c00074041d60520750380180100701d2841801010410400e07241d05000e05000f1000b41c8645c3d20b5000301003000ca9800c0d40e010100c10030858088450f04181c5001080f542c8028100803d40e0411b00c010109041c0a2640c41e04a0b001c0050100d92a841c200c00641085a000c29104652000180004510902180d400d0400c0383c01c4540e07401c0742030030203041c00f41041d00c0d5000d150380c0d820801c0010700ea040f00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 750655818 1250 750654568 750654577
    0x390b1506072a0b040909061811060c030f0a05121303021f0204090203130512070b0c0a110a03030b030f030c0319020f07030317061f050a0c06020706140603070605040b 73
    0x4101d01d030969a48484054950068000c6003005c1d484000d45000d00055008a500c4a41108007880c0c111209403210701c100409000014400c0754000303448008030504000396101250b10f100c24980c1c680c8039a0000e0610b60040d070861048a41c06400160b49803074030400e00300c603140c16030007808001850b039512803860007407241c003010385035824003000c29002000d201940c496250b11003105030400312801d006150103e500048464824104005030018040c442e20542121503d840d40f0b4848080603810b4844082100d40c121407846441111028580c0c5908034800c50740c4240c05580309481c400703aa050b12031090589480c019402081740a0010400d00c200040302c101c90700c15100c43d00c07c6210b049003032140356030080e0000b40d140d501529401204056054001e001182d00c1034644080c032400b20215407200c2d072140c0c00d02070085a841d41c6540144500c100c1240d102904540d01c90803454018002c1c410005140038080c0c1001c0040c1e541e0400180384425100107840710750810b4a001c020303018941c071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 750657068 1250 750655818 750655883
    0xf030d0807050d05040b0603070f1a07080c01020313021f170907080a030f021506010e010c03091701090510050403050304061a09090f0f030406390b150607 68
    0x401c2004041c094150b04c10a801944180c041034041c0c24000c0c00c061404415420421400f21041d0381007144070075680c59520343c682c03107001464689069007407202c150b00030320043e050194000000c003c45030350720201c4e111099200315040420220b290350308544244120003410003041c3c51010340d40c0700300c0840383c070075911050000407188459110b41d41c031030900c08403400480100304901010b2540903010f000c090103402400075101118941000000e244001d211201e40c1840f08000400041c144500b0038035014005c0d10100140c82941740504038000d00c3c8226041d00e035406142031111403500280500750181d901540d841c1c0c1940c03070301c0c1c982074000c05291045444d1414001904138060311140d411600c02c207c180e0103030210002c4403080310300f0040515811100398004000c2801465004035014a44000c640702900c030140400c4150007000c03a03080525654181c42104c84420042d5010006101e01c0204481860708400380702840518020035100400044400c400721260b0f0010140c2e0032140c00303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 750658318 1250 750657068 750657077
    0x60d030813021f081605070308090f010c0203120f060f090a021c02030601020c09061f0311040e01050a060306030f1707060606091e03080301060309050709051e060f030d0807 76
    0x40442d40080c010fa040760f60ba00b100c0c0e01c42c0203c140d42d89500201c80f1588049801c5131740c1e4200d00c5484c0028250b1107107a100070180480c40e07000c01d4441c9801c01250030041c0482c030080000d02c9006002940d03c0d040204004c0c01d22496a001600c0d80300d55122190103901c1c090310070f03541241600204414450300422085850b1790078003080a5001d880c1048802c282c10011005039030b810103400080c00c0c1500c4206a60180f9441c40c24410a511aa94000ea41040340b00504001a142000031070103001c004505141c45080403d011844a141c469094100c0d00d0803140c0b9072042e03545100036003d480a03071002400f00c1140042030408614101d0468040c1a44103149918241c5107980703080403640550094800203045100034480301c0c1007800054000c52040340704c415200c0c80d41e540c2038031a10050046008254035445a0000c200017042840301a00060704203010503d8413130351868a4000d80d4420562560042010480d9420043c84d02c80721307402d01402a0800003003414080c2d41c00380d0060403107810003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 750659568 1250 750658318 750658351
    0xc110706030e1014160c0f0308090106030f0501020310061d010e010c1a01031101020c0f04110c06040b0601080c0c0d0c0c0504150e072c0a0e0f1e060d0308 68
    0x10b0f82d80340f0600d80740c2502c034005822036007020113500c08050703603644007903080c0711200345540c0100d40c0d5134140d00e0500781d141c5485c001c942d442c890f626001d0b1006600c000c08034008005c98208005040d00518417410486c100400c0c81c0780c1d81c5c90103c2c4d0041c124800f007840d4859000450702954402e5807104407481060402001200b0f00d81d031201c100d5110820314410501400c1e0060081090903880080424024030007010681220300000d4a14080c040f001c921076542c0302c03070400d4410b04c3e140030f494441e02804240d602e545003038100b01300c1040d0308a031254001084540020f00c40c001440c2501c1030080080024180c11041c010280d071100c240100070348034a140f20f40001107994a40c0031300480708540c2850754844910b01050290790441c081c101c6014000414025148001c190102d44c01f41c1032840c4201202e9240e02001c6024440c5a81281440308092400c0003220234440c00214002e005400011080a020801124288400b600c0c45e6600c20020080c02001c00d12824119400041810312840311 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 750660818 1250 750659568 750659593
    0x1030326090d090503010209131806110a020c0a0605040905060f12031c05010803030402130905010903090501120501140f030c0405010801050618010305060109020304060b0d050f010c110706030e 85
    0x30600c046803040003aa02c00a10107030190703840200c100040000383c00030740c246226140081e0b0f81c0103001310626241c1d030383c0f00311196643c0204004040302c0d40e00701c00304120716114181840100d034400e401b500003510900342e55080b9070a1803110310040743c0c410340e034950809013410560005842e02400043d1f101d500381050701c0c841d40e2a01150003264030080300443d5603d0f08155001d003a8504030140d02c5500c1d01e401e004200c3c4806c0401142d80c401c1d41280d1402c4003c401650000007003010304c038003070003540c81c000d80c500c2007540100c40d107010768900741c07520140dc0486040000c10b40c4e40034059400d9400061105d5066420402512070074001d0040c2560701c0300d1044d0000c201115030907448010207a44900c00e100b000e0400c2503540c410709907440c040d98101d41c155240c065440c3c0b07040c40fa0b070b0841e42e4001300003024461564400c40b4582c1c4002c250a0541d265400c281d5035820f2141000c4800d0752070b01c5a4102058015140c01d0100341b51200588002407401c00d00340c0082c035490f41e1403191401003814040701c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 750662068 1250 750660818 750660887
    0x20d0c020d14060a18020d0809220b040515030a02040b060412080909091501030305160b070c021e0a0b0915131536090c0203071b0608010303 62
    0x42c011000c0002c02c07003032401000b10030075501e902d0028203100c100310344d40e01d0146c1c884581141000e17801c1070085a0b00c0c040c10000c66401c81004c100004000d0501c501c1c81c0505100c3d8201c11040001140c0038081a11408004522940300d02407059245d8007545000b401810180c0003e0a08900245001d050a030f880c14500c2c11051000304c11204282c000500d081145840c0c190907410029402c0142030285c40106008174850042c007018040c801d020480340000208030450301d41142e17101304030145900308154060a030500c8480b040b40b050310079080e40e5419803203150603440c1c0302000411080d40741d8942416181e103a48602c280d5500b00703c1005406420305240001044030f41901d861100a451900645208196a448418041203c0c0021800b581c04409411200902d80004003a0300000e007240d1000c41c000b5030307900080ca05400c10907141301131070700400640000c41c011401e0801906030031942c2124aa400d0081c500403811030710042c00400d00c035000810441032401420081c0c04030300d021051 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 750663318 1250 750662068 750662093
    0x9060405101503061508011a1305060a180b2b020f0408150a1415011101060906030b0105150313030504030204050f090d02150604020c0c0d080c07060f020d0c020d 71
    0x80441e4071130404024200e090314400074152094507041d14203505000741280503220140b42170034240d5020404032030b03039942c9400020080c54001d08841e070b1590301c2c80001c5c0c00003c5a450744c80000c1c81200c00051942940b01c00c407600e680140d00160800750002c0030200d43c0c070054240200d50190300307010300803c8074141c3d00107001801c04a0002c010660039080c0344005240000c1800709000d040c4002c0309502c071f00402005411000200e480086034912200480d000703400d000c28544103600b00900022842801d522003000d4078041e24401459a07200c400b4415500d800e2420000c004204000281c070140015004914191080c6000c030301c1d10340d694002038140d4005030740c410740d1400414244007142404001d1103100b02442d0024104020201ca580b10504600508442c0a81d40005180c80e0302d81007030046400401000b048168082c0c198104900d15400480140d18203200e1548081741513409101a0800700001e940106420800050704950440e013040c001c0340c105421004920005072561300c0344 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 750664568 1250 750663318 750663359
    0x50d0509060402030f120706052d100906030503030103031818020909070201050f1603020706060915050d0b04020103020f07020303180427080307020f061801060f050906040510 77
    0x60007681800d004050400078070340346850700703035001c1804086c0090840341076502d00c541002c0c0001d2269501c0000d88050b4441c070786101c917071450414a02e0b440c201c4642c2804d006544d05441003002c1a203801e103540455034140400744c807607801480104000391140702e01a1000d000c902041e51601d03558003a840140e4828903141d035003560003003845003180c00c18a8105900841d20b01c02400036050000d49484009c8000d0000c100c0407012901c158600e038069012200b44540c000000c1102d1591142606c00408981d5030f0300c0d2050140d24400245458042e152038891a0411800e18107030312281d0040d00207610a0a032544030010510200015a0341031002c2c008051840c0346100041c044c5104000c00ca8224025120074440411290030f00c800d0b496050314600c44c0d01984159403a242c070700d8140d150400c4404070740d24a11070343c03040155540480400c682e203105c20400078040c007625050700b003003e0406402101d070000300c000002038907440d141d00456045010341907007110241e200d506100d0065007da420 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 750665818 1250 750664568 750664573
    0x50904080315030f07090f2903120412020306060d120c03020a0f080d051b0405010c05030d061503060b0307141c020f120a060e060d24050a051006050904020a050d0509 73
    0x400c8042007e004051016440e004104000d8801142500c40380103160b003d48200050010700310a2503d040214591b14041d400185850b40d40e1101043d0325224403480c2280280a0140400e02c1420310030580c800603030b4031400c040c1c58081070303400807034072840c80b00c50aa00310700c50400c81348080350500098100d10380c01903283c50350712248079012100762030b0090720340a2020001075250706444440c40554041d81d401740390801103018903042c0985107000e1007412045940c0740c0f08001545160007900460300c5065504d003401020f0759020028985c0c0000c40d298070124008032500b0380c4200050004203400341c0c981d0003c05427030841c42070110880c0c0011b032005000c10000905107000e0b090742944164050810001480303680d0618500f0380c0c030440081c1c0200e000c0d0140581e60030802100380c2c00350620381c1d40c030b00c080d12a03802d03009690300150005549607594249480c01140368440c0c05201d2340305a601035140c1615020860302404020b500c104000410054144004500c1e240c0710b002d66405100c01c81c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 750667068 1250 750665818 750665833
    0x9063002030a1d0c0f0607080429090a0b0a0309120504291602061b0c0a1409040318081e0105160c0b04031b0c060216050904080315030f 60
    0x1d9141164420f841d510110320703111242d0120403800088404000c20180c402c1c801c00241d070000710b1194021044000c0c8203150100b40880c010700b000301d10000b1010f00c10345402c18414409070b811071500c900140190401c00b00441400220003907001070001c07210301d2500103180b407240c1c1c441c80c0410307081000180001d20700081c01c000b0301081c58080e00e41d01c1502c441c0c07005200c14400c441c850030b10034406071041d0341950320f03000070940d65118161313411404071a1190400c2c0f0400c010581c0c4622012180320b10030b68001d0030100d080c0300041000303400f40c040900ba41d61961940c0c0c4056076a51220744e508001e43c06055000328040000340206030140318555481d8071303180040b45006081d180c3c000c0004041c071011803018a03100780d0142124116a4111904500c60307241c508048824001c4850346072030610a0b0341d4580c0400c080340822004449142e800d0343c2e106503c03148c2603400d450b01d030321849074003210810100f404240c1100013550010003001d6102030a1f40d0807408130b4144483c004a034105a000b50301c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 750668318 1250 750667068 750667081
    0x80702060601020102180f060415020102040302090a0902060306012a030c1712010303050a0309200f010305090a0209060d052a090601050d0b010c0204020309101b0906300203 76
    0x31064008509000a60a10700004161050081c03040301d0280f145900d2040d0060f03d0b141d01013118007030034071460313800000d080c6000c1c040d000c1d500610041f409030345030a00195a0501902c1140f071135541c02800030b490b68035031100440d806200103100c1042181310250407074503042440c0b40d0282c41403080d00d0305021240c05040141e011100c10059010b0240e040180304540305124200505403070b458100b01d034480c45200d100b00d0003890040401013020510309060180c00482081010364094111100c400d072800c258011030a03900300303172091040c907442450901e00500c0c0420125034821805080f944240382d0f2625000d10304402e00d407003014002843c402c80042120030313102d00c50840300c1c1039a01c95018101980002c0403481010410400655a110b4414a5038841c0784542019500200259100d04020001c252102d507020b074041c5404c2d14065907449030300c04070381c9840c07010012522580710b824580b5105980f0f481e8108495400d408640c2070020410034045001c85540c16004070050300c914068 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 750669568 1250 750668318 750668323
    0xa0b031b1516030c32100e072903070c05070602010c121109042c070b0702040504150f0209010f0c0b0a1a03010618110310141f080702 59
    0x551281001020030440b620700e010501c440003225582c18030f070020600c8098180060034601c0d2000704c8092070040c0d0608008003405c0901811130383c91003010b0740c20700742c480c1d0496402c45103022610402c13508000ca00300031b401d4400200d80405882e804820709410603c1400c880702e41e1007112102c021420000c8500c0621104010003c003500290000704606450b00102404460707103444a03010064558000c0e4080e100540184e5540c0c440140080c440c40400c0d004c0008a4008000c9000d1034294070144c52a10f0f490000b01102291881c40c440380c5003c51030b8003032001614000b013043d50802e01c8503444800d200035030b02c1096070301c800b049801615954110001441202c0401c049000c02800d9aa46c1020070300552901d03403c111180d400054400c1140c0c0c50030921003140070a01c1c0d041d4a0000300003030b1801c06400d45000001003071800c01c00b90010101d00d2400f40410717901c006028540180a000d056126000d03a080e141000701191198500702068443d640a007201c8100000c1c6030506004019404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 750670818 1250 750669568 750669589
    0x60a0507140f04050f0a03230105090c010c0f14060f15040b0603072a080310090e0d030e0a0605042001031e09020a09111b03160b0a0b031b 61
    0x40c507a0302d1500c5001491480c0307901842c09410302c50804411410102d03558082190002c561181c20b20081d9001d240003004c080700d607050a0030595003402d00041200e0030200d40c2c40541c4405840348052010389456001003020038940840f0a0014004044501a13040050610956160800c003045150008602000c1c000c038040c101d01946c24240c81c8400703503503520160b03a03000b0398600e400240d03501d450f480d031041121041039101c8030304c040d07540c0401403001000c004c600c03130760003000e01c044841d0b9151002c00844000d80954501500840c15002003503200e900114804070541c421107164540701e0722620100c40c025942140d01d01c441600b4030301c613400d05481c1c540c000716090a041000b504002d0030b001525104031404045183d07201d00e08403c540d6000000000717080848810084540314010380059940956141d64040c1c9120f03d030599100000011942a5030381e00140c400ea001030796980100290300500440e07821526180040440e072020000305001c0c4111072006036110a42206100705402c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 750672068 1250 750670818 750670847
    0x10b0901121e061802040b0d0521040f060509040b030a150228050a080112150b0d060f02040609050909030415180305060f01090213050f0d05060a0507 66
    0x400c45108240700104a10750001540280c240c540210b020185201d62001481c3c40d2801c9a00269404c1240b8801c00440c400d84003089503c0302e42c41000b9010340800401090740e441001d044034051010001101c1448410291070308150326100d058080c80040d0b00310744001400821864000c6c5003502440d2010a002c0d0090461410144c5803101d1216500c040108010b03000154400c03025000000205030151444001a441c20000c03401007540d48881c5070364001a0040340040b0b082d40d002026500c1c0c40f40d11400306600e50003008003500180c4011540282d020980041e803d011030783c1030245100c4002c43c00001641e503070400202a000409a410080c000c1c0401c0040103d4120f0000444040e04c1c0540d903581c4003a10205411141d4009010000c001290303c01000001c0101c0020054041e060740b44031211aa83c988810070102d02803c0035450480c25003280812660902102d00d45107080090105010300c902c9444152a0a4050301c03800710640c5d0352002c000003103a0148903d882d201 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 750673318 1250 750672068 750672079
    0x6080d1710230904060f0b0108090a0b040c081006030c080102090a0e0c040b040f0806060d03120506010e041409010606050a09062a200108060114160b090f010b 70
    0x20320381d1080072051100e0280d12003256100c0c4000c12035030010000041075203002400d00a65140620703140001e0306030701000c1c03003e0504003a990100381d030080c44d16030b115503144002031034440300d03503103812641860141003a80d100550f1900800e11200510401c1c0706d1500d1040013042c158618584042c480499610644d11030b4410301014041e681c64206400440d4000c15030400309407180020050319100316441010384040c00500080d8400301107001c070003180c0380391007510140c3daa620244011850380860050000303c951404009000300c071342c001030300071106251000385260240081401c5500c05400ca81208101200b001b1044d1401d00075040030304800d203002c5040442860015205200f01e0254200340301d85114100110718003001c0c280500360080d1141940c546441c00c10f800034224012416040d007204481c203080f15402419103600404044c3d6481203000070152440c0380541048051030400d1203c1c00c0300c0008035030350601c51400340c5000f070701407c41300031003076a2182180c482043c03960240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 750674568 1250 750673318 750673321
    0x9151b1c050702060d0f1b02010c0302041214010603120e0a0f0e190e03040b03010302010f09051c03020a020d050f150717060d020a0f0f050a08030a0509010c050106080d17 75
    0x7940202a00c8103680c0c15282d490300e034940e41d103d85010f04500d003d090102c6103080c2c9421000301081029101c10550b58000304000240320000b1401e030320450080da548262651f803030301d0000300c81d00000c211101e00354000183c0c03030303851303a031042c1c6440300361454800010145400d0b216a0314107142590010581001403043c424508449080c2c1d10000401c01c0340154002903026124400e10b402484038095400142d035a03c94455041c0c0360f0941080c001640011312590201410a0003415072509039100284003000d50280d690080b000381c940c1d20022011406941e403084c00585640480c50740062141d4082c1c0088401182124a050240d1041500d01e071600c1c0b041c0800c480d0403440702d03501051040390b185480c0e590070f0049903403040602c2c0e009421a10307540e00041e504c4a6505008162080b50a0404106550b1030400045c0310131801840c015400030080c40d01031070700840050a6203401070510a902d4000e980311030703084403650b030311003402c6070000b8500c103001c03540c00b40400301008440a41111103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 750675818 1250 750674568 750674623
    0x1d090705041409041a0403020a12090906140d1203020403021822030503040605071b030305060111010e06191b03050105130204080c091b13170601030b070509151b 71
    0x300c0240014000d03a4175078013004642071500c00c1c040c034900b10350007070400480b1010400005042c10103c1c45152100d614000000c94840903446003032100d55001042e90b40101c40381e40b02c92803600c1054220106041d400c203c004010b8440d003030904100a8001c075450740d64074105401441141500c81c503040030012400c00c010009801c8400d0340e4000d9004440060b0315503803004182c2c1d2100395030740060103c94090605030100756243d04460311811302a40e40f45441781c1580b0304a400e861031036401640315004140001d041050001c0c954000b6408040c001c140030401e114044150442c4260400c006522100148005e041840d0345014041c0615821451f1030300c0c5c40385039600c80e00764116452191811a01041c42503080358000c106d802178041006a90b2010900d501d0070341181031044694600f0300d0001a0400040403031694102c0390441150009a0307210700301241c0ca0760040100c0c5038868003890291010425410103030a600c2888500701d044180c10400700e038502250000355407000000e52055495 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 750677068 1250 750675818 750675833
    0x2040807081c02010c08010911070b0906040302010c1817210a0e150d020c0f0f0d0e0402340c0303031406030105100603020d060510090303081b0a1d09070504140904 72
    0x4480142310700140d8010242c038106014890b12001034544900c000500800700c90100741140514401d8008101c2a20003039410350300d8400d5241caa90069100d4401040b0340740b1084000c2250a000030140c507031220042c4903003550155035100c414a404400308044441c950000300546031070340c00322900088100c01280298407840342070500348105030046642445408208990350f02c4516130b0060329180d01c0c002c03800740d03079030341003c90548001801d10751002c0d22800e00d80300b103400003282e540a001d800300005810409201c2c20a012003010700341c81e02c2d55400300e003012030b00030301441c8240d03404601301d00c0f07001c840b54075101c000c0c044600c281d140000740011440006080802c0300e01a04000d601d035185000d500d0f008083e9540320f40d400c152190b010300f80496025401d84140c902c642c0340c4014503102c1c800f0062400880101e1103d42c03080401c007030072440b401020715071107107000b0103080101c070380d91500801c20103c4145d0380e0b00f0104001190601500100c1107200741d80fa601680d1040e202e02e4113407242403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 750678318 1250 750677068 750677071
    0xf010b060418090f0602132c0408040801060315061706040b060f03011406011407050a02210d0903030905010e03070e0c0c07030b10050a062102040807081c02010c08 72
    0x2514402c4070210800e072503001a4641038100c030316002c1060107030030150081d41c00b008071981055520324000c543d105e1402c204441426100110207205485140218046900a00280c954407805d001c00a200202405400c1c0510b120700c0c159284041d0400c061801d40d4055000502401d07842810f0405c58100011202c3d409038021160394503644410300840c2264613100d410a4045d420310605d0a4030403001e01b410f83c01740c4400ea88515100c0b0309414400710341c0c01424801415500300410a43c050310b0402d107a07007044d40a460301424515440785050b0b151180152400011a0f0205010002d06400100b014003e0000303003040c2410b0504d002c0044c0c0c40d030290b8003444003000341040208441340001800d44040d802c6a108540d00262241403490443d801161a55140c1d50390700c10201d2981080c0c4070720750032905903460346214221650701000e03601c8000040401c1781a0b081c4400250381804000c1c0400034020300f4050f01d1382c00220800f030f00071408102040401d41e03042a120b22405648540c485 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 750679568 1250 750678318 750678329
    0x60c0c020d031d04061211011119021306030b0f0901021e1303020d0503120c07120f0c050715020f0105010b070201050c120307030e0c03070513020901090b030403030e0f010b0604 78
    0x252031030b075a90815450900c0758520300300c0c1c000c0d00d40b0a0101e584041c40700c548803c6800f070180c200c101f04461004441d40c0c080a0f00d11002d40c1c0103a043c1f1003144103200034a1106910007801484000d1818123050100c43c0203a106440b04075020040c0b003220400c484505030010141ea00a41c038011200c6d205203000442c050282e82c100400103410b8101c0900703e0307001c6000d1a80200312400c1e29019040581c0da07501305081e681032244005000c0f40c40b072507910088540c1d107035102d000892042d001001c01c0ea4114814030b01c0506003c4002010b2000440900401e80a402c21109020440340000c00c000e14200005c02c0201c8107a140100603c412842d01c400d840c0820760902c0d005a8a10070000420b08262003242041c090503004010712a0756509500003a001e502204221014421490100341d60365090340702d00c40c0c103d000a0960380301070a454000b00070001e0181401c0c01d00039914a941801076000301c800342c0000395107880102c03813400c040c08014040642d0304020b10010200c0d80000700b042c4580e1140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 750680818 1250 750679568 750679577
    0x15150c030f0c1401050a0510060216090b060c1c0f0503060906090720010209010f020318010e0d022101050603070b2a060709090e1b0d050102071509060c0c020d03 71
    0x190070820030144054004240f800d0000d21450502c144540040d200540c0c50310303541d001030035000c10600c1c0f001132080100c0c0360b203080b0400102e02d000c5080c001000c1145026401035000c22454a110f0800c002581040e00c1c10b602180d04446081002822a110b02c650041000403c006000c490f594034074405400c03040c00c440610694484c003c084e14602010b10050401403200e0038400711140048d0b015208141d0281c9801a18942c030f20b0041b40c4034032400e204044500e0460351040d030294858900b21150900c0905155541500750300050884503201c1c1c1c18410b4000b00c90281c0310042e4081c040c07190810300c04d4006004480c00c0070f0704640e050141154101e9899005600940d607200c14000c5616a40018410788209080c0b07410001e000352441d02074060650308001c4080c522071400203154540001011110001c1c5e10607074200103c014011005842664081c094034002c038003000d06100c2d4156410000203240102881d00500384d84a0b000cc640c20311040c8406000940c03203001454450035454070300b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 750682068 1250 750680818 750680837
    0x11060a0b040e0a0c0e060111061501050c011406131e050606040911031b03100b0912031209060108060402060708071a0106210b03190f0615150c030f 65
    0x410014102d030076451100b0b100d4000210b0a1101c464180800c1d1182550b00e800d02d81e40d064010f55600201d0000b11045920540c00680740341d0750040650786510051400307503c0c01500c0803500307007910700c06841840d40c0ea9200040c40514170f4103000030281000c480340c040c0200c12042560400000c54803100c8076503d622080080d003960740b580c040b40c001c0d00b03440030700308001c5406420720074050f00101c4030810b50201000a000014103440d082e0791041404c00b24003810306080041e032190580050b5180c5820242c00c0000c1800c00e04240084c1074500c010b202030075080c0c98494007461401c0780c113030b21000060b00034509100168842108580519820201055840700b8500d80000c000c2000048070100000d490300100e41241e00810040c0031f540c40b1892907010035492614030044405101c820380d8180d00c80301881440c1c015030005201c0f4640250803500c050591030b118501a0b400804841c104445e829070280030101502e8072004040540d0316181c501c4030002c1d60054800c0d02002c0503082402031004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 750683318 1250 750682068 750682091
    0xb040e0a1a130f0f0203152401020f030c0604050d0e0d020603061207030623100504090c171501120f06051302132c1519090507050103060611060a 64
    0x30700c42d100980c081c240d40760103141420f044000000900089109008000408940c0691447c1d154058900d20b80e070700c3c0b0004444a0790b030311313514104202141540146030b412108203000348090308900303001d00e001c0d062928003444c1481c140221100300e0014030801c00c540e4500c0c0c0c4c0361003180200346035040e656a6a651503150019210860104c40380100707210706080030040041a0300800c42041d200b03101d039901911000c0d03480ca01002c003200c6c03440d0a00030004040200d07282640001092030700400441d901e43c2e0b10307003c4510300349250b030380200500e40c0914895481c00c0710030118103005148c46c0e1a03181c4e544480c1e65074091020001a0051b00c90381d2540041048410552000060568002c0020040e480f00c525602c1c06810035440c252451005070400e04144c030000700c0d440804c41062406044c42029000c94665100c0c03000c1c0c1019107407041c01d001a0428517080c032803010028000c400a1803250714240004040d140d45401403020849008051803110030300190007500f22128031404103c1180d0403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 750684568 1250 750683318 750683341
    0x50303010b1804090516050307050f0603040c1d0115050316030f0b0a180b04060501050a080a090210080f0604110d020706020f0f0a02010c05090603130c03020a090b040e0a1a 76
    0x201d000d80c3e40f2034600103050040242c006990184019600c00340c0700440d60b0b4208240d16540240306007604001c0440722414280741c00c000440e07205100d1020180e516844103188000e400c1140600502103000c000180684031442e03c0340106000c02d4038265156140003190181500c65600c00030b0141900c400903907000b511150001e05000d0700107008054145e541e0903042083c107150680110010745045040001820180500c109441040c0c40e0240303007550600c4202c4070400000c107882080c0c0d80e503d1007100180e48200d00803e140c0c02a07900c44089060040d040385c1d09501c09001c00740f186180043e0100307002d8100050321210803141400580319061810300c0300207413054034140410642d00103084404002c3c4a0054030b800d0146500802c1300401d0800251030500c104690303613034000c40134000102d6254221041e941c400e842a1210082c10341c0c2c95010401c840320a410031022a600e0300d02013516404c09100b010021044000101508421030302d4009000c0c0401407451a40703e0300f50001501d40424 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 750685818 1250 750684568 750684607
    0x3110904020a170c0111010b09040201080912030103030e0f090405071208090405100f090b0a05060a110d02030a14070c0e10030804060201020306041a13051b030405060402011803050303010b 83
    0x3d078011003c0e0010015101c030380b1441d40780c0c1030a011502c1d040c0301140e549030501c102c582400c0068110502070702e86400640c0d101704020001e0b440e921a007001003e418a145000d98000d520a07214284030b02202c1040040118807040c180307000f50203234400c120115800080150455150f030750030400038512410205401d104602c080703500242000300344410340042203904000c40d903010004001e155102d1000c2015101c24200080e8030a032007590a010174600400140b81d005482d04280c0b80c00320b0040202030400e103803144240090b80020501e40382c2143c02031407400b407481c01420b41d01d160449690310441000058001c03001c01c86100c02c0001c0c1d0010340030f44504003454200600c3d680351550760000901070b50080312468000c0d41400801c40003d036040281c2ca400e200700400714000480b203040060014800144412400d010362890305001700000c90041d402203005a0180000e80350a000141007020807009851510b103a40300700f000030442c0401500c0c1901c005c0c00030036560f074426080d03242c041000e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 750687068 1250 750685818 750685829
    0x14240a0b0a030c0524040315020702040f140a020f0f030a151220010e1005091207030611030c030f04020f1f090506180d08040f0e04150603110904020a 66
    0x5070010041c090b500c0c0302c40c8101c41d0700b00c0d85080300f0415000325030b901c007020700e12071804424103120a0001a0410903000d2002c176400800508004590b00020240d034103010b540341c0344584d1503803000c01400d030305ea0100e540020b41c0e800a501e8461020183c180030311447c00e004030f8140d4044041145820260480391014081b111140b0003a07448a81c4440c12075100c2d24119041d609540800c03043c4485204041d0b000301058541c89404085441406203845107808220100001040752110b10360f1056001804c500011000300b41c1c182c0dd42c50608212201600c202c03270781c03003800c0c01001001078035981241ea0041034060303e0300c0b84c0d888510204000342c00021249901c0f585408105c124000c8400030219045201c0e0344202d5200d07914014040740b03100f108580140e844d4403400d400d806040144076443e05601c41c400701ca140641d10303002910040c002d5000708070b44403034080610050024000040c8000345451008005961940c0c0d00c0e480d5a82e254001385000c0c5030070304005015543c0f41c4490f0f60003000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 750688318 1250 750687068 750687079
    0x6140405221b06020d09050607061116020301061202210a1a0421050d0e030c0f0304030c06140a080a021b0d020d030e0303070309020307030c030f14240a0b 68
    0x1110b00d0301d42c5001c1d0614124103850070521000048030303440003c203000780c69a503856010701e5030300b070009005e0168480d04041e02e10705e8a4a01c2c4000c0e0180e418014130844042d003c4030010b14005d48101420343d0981e40c85404404079a088080150340d07595075a0010612004680340080d40c04460301c3d041c0f807036500000d1b1852040790300c2501122201c030461031042d8400c440c1d0440f9409040c06a03220311800920740000103800780540380440b0155400060780408100c00c50f814041d625008600e09840c540300c02400e034002103007c000f00040035176200c1c0688482e082c42c80c10031a04200c5250107015004070001003101c110041205e0b49401c0e8111200402462030307090680480c440465502c42c1205041c20041c4103401c1101c04140c420b100303c0c024100c07010051407458a8800045003c0c00302c03841c4c03da1341400b07100350000000381c082c030b424001180b00d40c40201d054005814610107024100900f0000d58000c0402206240791041c1507020445460440038101e0701c2e9001c84000500c400a50b041d000b5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 750689568 1250 750688318 750688381
    0x510140a091404140f1e0a0b010801020406030605061c27050714271e01080105060316030203060a0c23120705131404090b0c0903010c0306140405 64
    0x2c901944458032460040300101c18005200300748135a02c040c0b40c02d408025802c02c42c03031808004029200c00043d03502060440d50140410740300d420100c2020f030711030500740e035000504225481d00b40c0100340040c007003111620305244c602070303048002d03003148c00003564080d549403102c003004a0881a960303158081c0004610980d1564904203a40703d165010712071b039040019014900614004034900035a00d203902a0700c01070304035901100b2100401502e071140040310040c03005402d91502680c0ca000b000c04d203002041c6424034200b45424500c0c0e0780603401c00220350100500150301c1c00140d80703800c8205158002010b89032400c0856002800420000d449000a05040b038102c030010b0143c030081d510ac40c3d09900c603840f07030306040e41c03d4841c03607802c0145080b07250b000308480041c0540300e0200b20005480810168825944c081d041007040b41d2902d0122408501000789040c01d10541c0c0035040142401c2240506000c181210030004a003040d100715207074030016103580300c0c85100c40c1c0c4100d1500740840c80f1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 750690818 1250 750689568 750689591
    0x303020f040e0a0b01030e060c04090203060301020903150a23040b1015030903090b041202122d0c09010e0109020904090c0602060601080901020901080a0209120d0e12010510140a09 79
    0x5130002620b500d001a0070000c943d0080040400d4141c021081048150b181c2460580d1308006500300900d15a07065500380409480c41c1c0b0b0a0100c289407000c45141003001d072900c444524105c81c0b20384032a0b2862080c900e0a03c803030007070480140d900190846204242c83d520707804004002012900501c1504040d03204403034a554142d00142e50241c42501c81c04203003600caa00c0745d8507500892040e007105101c00c070a10005824024000036402d0440300980d640d032100c0c80c54a40042c500c40580d8904072601e0313610301c407000340c003400005d1403c142214030071080e525040c2103815044041c01950905030380010180e02550390341c0d110300074990303103d12803d81c40c940c0c030351010307440d5441242d01c14003041281001030600001031003240c6213040141c542d0302441d240c5143c054000d40200071038039005071140d00d6406403c001001070080040d22340d036030316a203c0c50990610104000c0c040316400268140320030702130380600c4000d0300303c00c0d201c0c019810000e81b91340000041c0841b01641c4040c0e20720b854000149107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 750692068 1250 750690818 750690821
    0x40206030919150b0904150c23031608091c020c0a14090606040806070503060409150504110414041104230403020705090103120c06020d11030a050703060308070303020f040e0a 77
    0xf2800c0107100400c9464040c1d828030000d510308880c024110421070b040c00000c41c403240d003c40c00454462511180d4201d0a4501589141280400103a810008404c01ca817a4210f151401040030403880c0440e528204428031960765400c040d22000c090080d450f4842440d03108204044d5030707810041403521000d03076070f5070302e03448241c50b42400502403940180003e4031800c190040b2011079241600802c80c580e00c500c012102034002400c142c0d40507440f00c0b054008100903070520218040d001e01c0021721410705140250404041e0000280100e0411444c24512120840c40716889500a000b072819070b00c40800040c0100700f040780442c62080781010003419091010050740c0300f58800d400310341030303241c480040145072002488000c10460704142158211441a605854102d02c03c44015040c43c681c00480025180a5551a429610007000b00304013800c0b94020a604200b0501301088510300b16114180c0c5481000e10207401c5c160000341d00030503021302204a0340180444941c035001810150340850 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 750693318 1250 750692068 750692093
    0x5040204050906070f0e0303090409050f0c1e0f130203010806010602070f0b04171f02181503070c03090518090114010f0501110109080708091203040b03040206030919 73
    0x30300032841d080c000b4008000010301c8601905241e01c0d44200004007090445200540c0c50100303802d80028040b126035601c950140210561080000d00072583c8400d000902d448404103001d07202e1101c590f041c2101141900c1641403a0005903850844008140d002c00c41a01810102c4500d051000000268500b008590b03a410703511a6820340d1181c594078403000c031690030107010340720050b40104810040c0384003c00500320030b0b10710a02543d074503182c1141c00300c00c0d040000a68500507900007454000040e0102c0304c8040b403100c122440c0700c05524000507180c1600004010b034040c00130340803914050500540e141d90040000415141c94018640645030304c450013039030301e4407640d802c140584046000001000d41030300c0c0407061504586240070011503440d0b008200143c0ca5542c1d9a810703d0220f15040f00030f124082c000c40060b591060b445003488041c00312448403041c03d0300288028014140d124049a81160301180c03000e07201e03112090f0084c00d01003c4114003940c2d403091403500302044030303449180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 750694568 1250 750693318 750693323
    0x9080702060705011b08040803010e070c12020f0c0105190c0f05060702011b050a2a0b0112021c110d1410050a0b0f030a150b1c050c0d0f0f020619030504 67
    0x505d070700056241c00303490100781543d00801c0b01d04280014006522802500381c0c2c0100d80b450f02030800c0300300f03454210700c2c8050b44007400c0060708032038808200780d042003080c140b6580e070030718003a460120700c04052443c540d240700ba1041040241a001028003400b82050391318260000c003658100c0c14540b9010b4001c104031040b18000813410940a44542c0c000c03c155000d010198441c4205204c01c18141a0b6044152113010040c0c1c43c10300454001c5070320940e046001e080800d0301d070941607440d0b004006280040003040050760310804190000140031030718648002d0740a4540f00500074552900d000700300c0000760969014401c04003107941c0000d85070801d9001d4400c11008008202c5040c003441021311031880c4140e090351040f021040080da07440301801486101940005851113a98002451101000392282c805d50340c005590090003002d01c0309500e460b10844d0880391780729007540c4500560044840c00f40c80340060705070030784c01d44d224181102d096084545031481d174103541050250091006540a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 750695818 1250 750694568 750694601
    0x11150a02010c08010e0c1b160909051e070e0a110a030507090e070509090405070906240923030f060c1305030703020609060c070b0d050a0b0301050c0405040908070206070501 76
    0x180007101e0034041406410b800070034919100c4410040c0400300b480604912035881881c08d50301c007000e9808000d00180641d18408941400c07582011842c20038181c4649041c00741d5403d6015040d41e0015040048841683d9203e0040e520360084400501d224100800c001c0c50009103004042d616034042841820b1545405510319224030000c01c0500081b2448030118800f08020b034018030f04408000c4c1d04c54420811913520030f0301c410f14034044d14125800002c40701111285404030003c09540b107001480e2a10380000200d1604407405440d580c80049140106044001d11441d03480500c651440c6000000072501103003844600080311360b001100c00c0150b001d43d000082038514002c030303041c41201c2d001080c0b6410000d214080081a5201480c0b00701c01d807054450004940185002a016000042340d002a961900404079002c0c3c8035460b41881c0300364500000c010b04158406c041e0340070b4800965000034140014030300411341e803040003806540050003044110800205421044400e041c5002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 750697068 1250 750695818 750695821
    0xc030e030a06060503190803070309061107081c020304030c03050306011101051810020c0d111006060503220b0117070b1614060103150b0402070803130c060509060711150a02010c08 79
    0x100c002c06d440070010081102030f0810214102c10300c00d411050a00b4003030903002a5020324648070380190f03801111f084400c0303000401d50024400160269883c02407c0000c03d501d546010b540041070b0345484a402020f000022000c00c0c8941d01c200444108888140000c20107814003040841200020900d11050303441408402403400440d4000d440203200c605008006c0242c1c180825034120640e00c248200e1846494424503e00303040e40034070b200078120f5403030303d680c2ea04003d43e0200c00c500d03095516501d0b04410524482c0003401c03807039945044034a030f0500903004582d081001418450964491055240003103000d03411021401c0d03014101c14403030103060034440391182e0840d40750a07003403002901c03101051001840381115504103490a8500a01c0146411010340d40d9000035002690240310390205180390740d0410024036841400340a0038245681007685040000d0514030648500030402072000e014001c84d91640d41d180084502503c019a4035450761281c024006c0145264220008440c2c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 750698318 1250 750697068 750697093
    0xc060203040b0313021c0c03020906040203010e06100302040801112d03180a02101110020c0c06070c0e1303030507031107030518061b06180703030c030e030a06060503 73
    0x2040354100c6510b81d04060a55a500d114109007000c4410141d070060745030f034000c162040002c0d64440d00144140300c01c05142c0d0460051014003040107000c14003680c4100b00521a05900841d501da1200d82211201c0340e5101403a02100607000311b901c55145582420700b8850311001c040060f0121030151891402d044c141410807442d4480540070b9000003000030000708d40040604070b600c403031340e0550a0071608401c6040e800b0070380c804241c4c010000004d100c5008200b40c8101401040c0d10080c84d600194104500101e120780c1381c8000c4190b0a210707800000e408000c010906001800070505100440624500150b41e0802c4c2c98062408400180c546000181e4860282c490704841407c110011390900748540e906548540c040c3c00401c07005e0900d00c0303880c0219074030400101094169413601120100744a07440e1441c011011780103641e01315441c0c122180b0b1517000a5468122500761511a200b6291410241d420b9800d1000c41505401b0301200f820a00405410101c100c52099048540055020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 750699568 1250 750698318 750698323
    0x9060812030f070f090b03070e10020109050316050106090f1b02070b03010b030a0f0e01060503070b030103023318010e060703140901020309030106030507151812111c0c0602 76
    0x22500d02020b0a078610204034010320588880b070103240541000f00200f82c0743c05043d840c58004030f400c0d100141c0e9003040d41d0124181101ca10f52058107600080c8864020356440584900a15020981b10892500c1e44010700009421140080003070310030800c40000030402a2000c0d05010f00d03000001d1100c02a0060071b01d2002507000304582030a022031341107900304007004015600c007030301c1c400105403100070450984505d0b06c40c20345079920300000050000d00e0320042c107040024076031160360488800d000420240c0c4951110102c1903644090103440300c0c0c42480da000154001c2c0d407549030544804501c0c6010310400c100c005000450907210b01640010074810401c0078840c510300100081c025486419031890303540c1c003800b05c00e44140103482c1064010030109084503070320b40c410354a0f0b500914080141180c280002c41201000785409000d40da0603403c01d803402e14051040b061360301c242640107424824070040d030481c0e0290042001c2210b0301411802c10400e211200281e030b1087c0c5070705001442d50b000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 750700818 1250 750699568 750699571
    0xf04140a030206040201051b1c030e010c050f070302011b17010b0324031f1d1c14070f141023180102071a060a030206070b070e0a0906081203 62
    0x76500400d0a95996401129141c10160010203450b604018800c02007000b40b10300c00402001c0c47c03e4004003a034800340142070f202c1500c8000303580d0745001c0e8140302c0300c2c2d4000129050491110000b55a0301000e1030100d004200840003ca801030103100e031507611039072080700088001200441082c5a0f40c0b00c2c1d0f007040e428882511800d8408090780009a40d4009540f50f0f881148401025a810390100e40300c00c0201011082d940076607113584146290015058040340f107403090044004142d04160102000900c00000d1074120502801540c600000031800c4100c404155100400c1a005841803600e2038200311001c520780a0382c01a924101d61081d480c1c440d80012000605503100810780c0714004a8000d2006801000a0081814031a0300e02c1030074001000c01c2c9104203460300c0414210303502d0650425000d0701441c4500a80d05080001d42e48002c141c3d000142c0110002256840300c400a41d51406100c8000da04000c1904d070020700f071400d640c000c1040321105410355800c20380c80c0140d400540300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 750702068 1250 750700818 750700823
    0x90204050603071110050c0a09080109030215180109080c0c03060609150402040b1b15070c2010030c140c1e0f010203130317090d0e04060e0f04140a 65
    0x1800002e0015100e0320814091140c01300c02d40e60854500c500e0312007600c50031a40510380660002e00800305a920803000802070150000030400f01c8560754009454410007903c007614104940c02240c0c40002e56000d25100d40325a10003040307034410601d0802e805400c040000081e6000d1a511500d032401e01044043c4100b400038021006591096620f100c1d05144e040b020750416400d01010403004000303070080900c20359490300115001c104800039458501210415504440d2110070311911542020090007400c1d030040e400c0401c05c0b111880c00020424014000b40e01c10042a107441c0f481d60954080350308022a50784a0300c1e8081e10710360b60030242c030820032450407991054203100d10b4800600d107255090300f0f298041d50b1001c1c910004031420f90b0010b9400d87d012060804070783c0c082542002c4190502446c4141c00c2d4000e10f40245400c0d126178000148200380b10251030514030795549c950000c805010f181d03e86211505000c440c078965024100c0b812268900c070004002030000000484002965 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 750703318 1250 750702068 750702079
    0x90c170109050708041b030818041503030f08060d051e0f03090a03110d0206120601030b012c0f100504080d020c030319030207061a030d2a050717060a0609020405 71
    0x110b0ba5540c040d403514158140340d1030346c1100100400040c0160004094403c240490a04804002400c000031140d00c40c1114460404c19a01003002a41000c0c9142d075408060134044c04035558913020903801d11010100801c540202803101407540e4003403441c40304106a403001ca4081d03107851075196980748200e0301015409000f0101c00c00008030416620717440c15a000d840a241d101d91503000c5007a6401c0b041d11940e00d41110700c10409196414441c143d0a03103024030380b49061140c5040c40e5440c011441e440e0785090b0180444034004c070b8545101907211444054480e0160980641b8000c049411a000707000c0240150b40a21001078070010300029a0031004020703626040344241c0f03400005034030b450b0130010305401b031001c0d8011404c2840350440100306500308a0700c003440c45040605151000703000c0414001048526030010104030351604a2000041d00040140c01034244940760280c140d10485409400382010b5005010100e41c5600501070507005001382e5450f220351505a00560040c280c011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 750704568 1250 750703318 750703321
    0x80c01050106020c011407050c0a03030f140424020f03030717131208100306020f0406030b010809101802031c1715310218030a150b0109090c170109050708 68
    0x846d4040040890b14402c00c100e4481269080205a11407580d600503004502e2034a4211902600606e19400d4012a110201d14042c103201800b4003006d1010102040c104c4698069181d0031b008100c0a0300854007941242e07200d14003004014141c111804003010b40503080e9020501201c0341c10301e024442e90780129031200d0408026002c64036103c0062031030118800801d000404128907200424407000111095075540e8100940641941e05000e4114100440c400801181c42c001140440310600b000d040881c8140300c46203000b0201c00b140c036029606020b032901d4071050701c01050030554038040580741c2d403503100400520040441d4003111850044510460715100601e0030b0140d0300d803907008200012680030700310038232500c1e0000300400801e03c007507000070207030009142160010007100080f401440030f0401c55441c0f00304081041441045161034903488c4034180e02885002d40500000c1004201d0107030f1b800002845040c1c0380721503e01c0303403015000205001e4281e0007210303c120030359180c0c102d55 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 750705818 1250 750704568 750704597
    0x807080309060901180f170f0a080c070906090903020114070903060902010c060903020d300b040204122405070c3e04110a08070507060216080c01050106020c01 70
    0x2c1d40c1c00501142d0400030010060307002140800110760181c00500344150106050100034100080d442151400640c400c0c0f5440480c1d030400200e8584071640140502d80b5003004603003891070520f0301d401007089941842404207120b00740d80d000000c0b0394002d6000388201d544403106800804000d031500c1c800140a07007410b00c04181160464140c1c5481894a00d402c0146600c1d80c100319044c584017200140c001100032880d05602c60340100b0032842ca03503851413200255103075840d21502881070f054455502c90f00f10460569031035060b6002482c071120300c1c10401c1c00501d8000d002d0700f0800844003440031410307071014910485104940c401c0d00c20f030310355030710741011510f58100300c042410704034071341c101d216508541d0440b40300c114160710081031503d01c1403da40102000306031280c401c1c60a0400c0703000d01c86006442e90005210350000b055040083d41c405803410100f000e4428002d0300440c1c41642e81200d0304101148000b0000d511801e0003c10850362202030898840b544c41504a00283c41c024013900c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 750707068 1250 750705818 750705829
    0x3050702270f07140309011a0906181305031c050c03061503150301060f0f12081c2703030b0406050102120d0f09050a0c0e070801090221100f0807080309 67
    0x10001c0c00303800d00507141380014600406a500444a8402c0c0703944404411241c140f424626407103811307040340c101d0650718203140454032200303486021100903a040000300300d071110010040703250650800142c940c0c03a007060724200c81000348048610522803070400007a291094413000d0341c1c000c00e0018a400c2500c0901e61800440d600090048070010703410100541d410380e4244100300040104007060250b1526141070a0b00e100c200358001c0c200300352094130180c00202024112085202019034042100519814520080c03004240c845d0042c907814542c1e4030100302d02d0244611180c4a95414000c0d40510010b100940d501c03403160b02e0241c2d1040040310110742950021b85001107412200050000c2800340140035108026416a03040e0804420711050007883c81011010380303403c0c0303a0510a810f124400900320001413040a1401e64041903018407801c02441c4601d414203100800500d41c104010340d20601c82d007a101e0141e03098912100001e94072000300c0c001c1c049807a400069418801c00106004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 750708318 1250 750707068 750707071
    0x7110a0f02060c0c0a090506010e0d110d05071a0909070c0c030330060302040e060103110918030a02010b10090f0302060c0c0a1403011508100e010f02040303050702270f 74
    0x2120340c02002c0c011461340e1680004100108225a00828181001c1d000501500a1030b44024007a0a242410300082106080e0f101440e0105641050700c1d40d17030314149142802d01581085a2408a91609278401d0820b4030241900d10000c03a00c468603502c03150000d641c0c42c0c007001030080c2480340585040012030701402c0c07401e007620a01062840310390003a500d030340c081003c1c1203902c0c400355603107420520640c1000d114502c89040c81c400202015411916111303000740c00e1f0402e040c0300c0c1030001c0010b40d100c21162862800d8410f244100c0f61250f103071200107406000340b005141e0040c2c41813030130750610600c1200b8010844074050094456a4115020300145030301c000020a01c1d0712440307030042013a844041003500103003d00049040c8801d0507404250940e4001d08051002d440d0103e410b11000030301085208505041150025441c000c000000e40541160174190041c070348003003400800c1c190030000801265200302c1e00c3e008400b104040140d440200140c10101c040c4078040019180f0b8003000c4180d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 750709568 1250 750708318 750708337
    0x611101509021201140a030b0c03040f33061809260319021908040204060504150602010e0f0303010b0a050405040216141f2408010507110a0f0206 64
    0x20058545881d14101682d2201c90b210803800b03600c000403c11000d0581203501c8280e021245c50741e40340c0c990745501084c94800b038031030300c05002c002010504000503501c2201140c0d5100407a4164141448455803400c04051032100300341c040740344c5c403241c0c09046114140c169070001d10344402810065400800610b260582100c0322080000710612000000d10780e0092440d001000c190380e85007045202114030f900c002d0380040b0500500203004001017180015401640515060203580d4490000602411041d403049802500c0d10b001800545030780c0c1118400da44aa400900240b0844072240b50703103d400c0161404190014401030002c0c00d900c0c1e00501100d11545000303824641c448001801300d030301100031240d021a82590400411031000e001c9400708042501078400d01034050024509540c503060046400c55031100d951484080308103914101e040b0424940b4121501e60060900038401036458101144034143c1c20300d03401300002100804903a000c8041c1e41031040e0350b402e001254000401a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 750710818 1250 750709568 750709601
    0x20f0304170c0a150f0905060301062601030507060f020c0a050105030601020709050f01030c0e090c01080603210c1e031219020309100b030d140304080712020309010306061110 77
    0x4402c100e540701109103002d420703051900181c003040a00050003100c0221940b509110381030b00f080009079101c10549044030301d1030400d00c86442d4280b241300b0f0100c50f507605540d2140d00140010092190002e60038098a80c562201024802d100200381e0780c03424501080c0341c0c012800e0100344039a5214002a640240f4180110380101d034a03043c5500035540b04a60341803014980d400104280701948400000070302d5080070f06800307410700b503124a480d8501915254140084030303010034400c0d101000b5402da511030352100100c00c88007810b0084001d40c00702055014510030175520040c1c410310040e4840d5004103250003540b42008849000c922000006c00044c50004108862109020300340000d601c01e00c00c041c00381c0700071591100e9a104442598070120700030382c00020030900c0c1c55008000c40c184011282c41c00c9449644928084e0907070b01c0340c414010030140b244801c900c50103130000040c19034403c0907281440202d860b0481110341c2d683c1b001541d4003c1d8029480c449916000364429020503612000c0d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 750712068 1250 750710818 750710833
    0x10902160209010914010504091101030507050c01060b0717400b0c1203090a03030f090623010806070c03030903020c0a1706010b0316210609020301030203060601020f030417 76
    0x24a41d01d0260301c40020142c80c5c1540d8015030b01d2485017140508411101044265069207071803c20051303a01c10123042c180c4c0c035004981d003680a082601c1019803820000c1c48100d031a2000c00303a840d04100b80c100c403020341c00e0107503840341c03c0e00d10f041e58440c3c44980b0001410200503003001c0c840304900b840303041000845076483d120791890400280d002d040c101046a95522408803071f03c1c03030034071503003210207404000b4030a0006038000441c41451490700f501c0c000c070300085a00600340003480c03584402041e091030f01340b200680c040b24052107000700f42c02110100c1941e1380c036080d140d160101119000700003015900b07014002802540828442402441160303020700300030001c80e100400e1904444030800b04408501c403203a074200030550151004903100c0d415810000d8045d5402e0344c40004020500c03002104580c540c4e82080e22292040002807010b02c410365a449002c8025882800103a009004410004006500000c0c00000743c0c46800f00841c07500f49000d652804110b882d05807038009026084 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 750713318 1250 750712068 750712073
    0x102031603110d0e120a0201020c2107060905130903170a150306050619030c05042016150b010806100c020306090c0109060c170d020906130e010f0b0301090216 70
    0x100051400d1480c0d04c941034100d00ca10104426070a5a204200e241d1303000c0c1a003040141d03400324200d28401000da0302e5103540310508116001c4880d070001114458400c250000400303550001d07020080310001d0300c200441c4000c007403a403801d0312604400035010400f070b00d2810801010039200da540c0101c680c0c2002800c0181c00c00701c0769201501e42e1080d10f4240d144d40038040c25140100500c0040780c3c0f81a85001d1035032840d9a0218400d010303100d06c91140303330340d1400d03030030450544107007044c14a84011306c3c1a982d1624000c00c0f09a10510242610034030600c0d8080c061075403e620940204090503110800183d03200001c00004034003040d0f161041000400403000140c030200800f5005410040192104800110004148811903841103040080448000011911126658099991050b1100e42d03840c0100c07041ca010784241f0448580210b00001c03405003089070700b80a0b00540e4400c009000c0e85999a60b0a044600300c20700031101e00f104104010402d4003219401003900020b00740c5c041405070100d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 750714568 1250 750713318 750713323
    0x601140d1517030703020601031415010b07032606131e0e0c01030506010516020d1e12030b0f040e0a06111b1b0d020a0503030316030b0a0302010203160311 68
    0x1090074081c07840004200703001c04450541d65030580c40407034004505101e0a82c50080d03440c2018480546983ca0000240181000600c40345c070302519101040001943d680714004d5156000303100c140c0021700c016400c040f40e084000d036024042c0008010b203442070b0f00c5503030420401940c0240c114540c00d9a0b0145046410444606600012540303000080c011220101090a04417180500d07410585071a040280c50384e000001e640014881e2001101e90250301c0c804101c0c00c4a0302a0064010020800d0902281c240105000030740d910035043c409100210320307000c0d006d581b40d0400b4298006004044030b1002e0825620003940502c1c0d01d411201c10315107a4640008407503410786080c0300c0e050001282520010000c061046258040d4004c008203a00303075030b800307450011841d0b0082c4104003002c03816081d580c4000384c940141000505803136480c146444c0011052000900b5000884d0a058151005280812040701240d4060300a14a010081758680d0389c0342088800c00c406100c480035250400c140c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 750715818 1250 750714568 750714581
    0x12060509012105010c0201091506060c080f0f270d020303161703010906170606061b100c1d19150242040c05010e040b04020c0703170408060601140d 65
    0x451b000001ca04910303003800e800080c0c0120920074010300f44003042041c10340c4507208501c803c2c1c2201e400360b01c8901807404460140304030540c400e20320901081c645030402c0c981d0780114052510b118800c1a22156500b404440d07008298041e615410a00501e03e0ba03d9011405140d014031911904030f00320400b15404c42c45810a0300001c1015641d40c01c18000d02e071440d0700f000302e90b880041c01011a880c0040000b0110300c50004107200c0e416800c1143c1d1200c031001c0240000c4803112420038003e0300500c0100170906910381e40301c410300c0c54070440ca03001c1e14184580c1d04140c22844c0191011502d08100c4210000850700e0001411403003000840100da651741c0714142c6402d0402051000340c40c1c0d844032003261440c5141400039940644005001c0002d565484007000c9520a0820140105000000500510744144000d130010b00015145000c04800301e1003205a80c4501d0755940501c0c1200c1400e4070341e004034019903040d640240046500740d0b0003404c0305080d11003070540d11443d1151308155003041d0707001c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 750717068 1250 750715818 750715841
    0xe01020c040624050309100c050c012f0703020606060c24010608060604060203120703020d06031a0c070c031403040f060f0905040209010504030f020d0f080a1206050901210501 77
    0x5440043c021100c2d5020140f680200e40d00d0040e0450030708400c0543c036500182c4101058540d502d0301a80454011415201d010314084001c000e1201060018101800b44503020240401c01c04242121920290141d80072242c059004190954599042c001503a01400c61010203100b103016007204c034080800d811041c40083d1341c009103103500d0100050022600501814841c50b8140310500c0685d40c0041500c1c42d40e41c0c55003000704a600c0307042c01030b00248a245091800c0760308100001c018070000d40d80345282e260180440c0c0d141c0341c0e0755840100240c00b50100081c00c41c104440c0410203d40c0140302c0c8843c0c900120152441c1542e23440070401030b1841035000f580419442907200780c4003500540d00a001300400c2d01e0070752800e812040000e260b845180801003002d40c2442c288800d40d241c510010300465401940200448000d0414403010b8001c5070107400007440301605454090030900802d011070328081c010b41c0159003829040c140000703204c056011010010400c45011035024081c0820000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 750718318 1250 750717068 750717089
    0x203041103010c0f1814010804032102120a09020609090a1413020907091a0d09082b1a09041103100510050105131217040f17010504030f0e01020c0406 66
    0x14260343c4050489140d5181c546a0302450783c504000c1c000f06c2061148803000b09113400c444a40d214034040c0c5883c1c9800c0940045000c1184011909e0010759004284681d0550014407041da1102c5030241901c1d140180250403000a1288004504008030b6040d0064204500401c0280139901e0b03002c0e030000c0c100c1c1c41a801c8bc01400401e015424080e46c2c0c140c010100d480c0015000342040e165a6081f542c0585114540c600040da50300358500c0303544410055a44000055a5404550300051842803540040d0324600c0352442c4030b0030b0202151050b1203040d8001011641e2400e101c1c410091803000c000c10503200d008a0100d05005a1b030240202c03107820300c00c43d000080c0d506001c1d01c4819200b0003900502d05109042000710100b0802030608801c4500700a0340b480550001d00d4000c03004074125031036141c6000040360204844c0b00c550340700c60a0700d0040d13003850352a0751001106800d8440c2542d016022800ca42c6401401e00c2c4141e0816440000c10300484104681d140003280407502503922480c03044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 750719424 1106 750718318 750718337
    0x17091f0201060b1308010e07080d030506010302070218150102010c0509150c0a080919030201120b31050f22020d0c0602010903141306030203041103010c 67
    0x1805440f0040781c60710000c0b204070110b0313441c90040d0001075003050070703d480c080000151602103901d07020051042c000e40038429002408060881d50403d5001c00010002d80c44000400048200c0e00d0701000f0300307281001050100c4010904054116410b008000414940c0601602c08454003200c0c0c000ca0100300034580d40e2944280d503850300e00f5000c1c0309104010f00402c10058004544156250204000300100100740203078140002408141c0c034000c0700201d1001d561003070342511005803124001c100803451490000b00072031282c4000781c007aa1380018035200603002d042d800404415404100d403c06103501c0048002c1c40001000c0221100051402e650392581804036035604694481d25042e00d84800a000e0101d40206401261001c4400e2000c0302c1e82c9002ca6190b10f021803000b20840e0f080810850107903001900558420b5180307420380704517030340c20300c2902854411500e03004502c = true := by decide +kernel

theorem cover : BRFrame.Cov 750539568 750719424 := by
  have h0 := BRFrame.cov_init 750539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 750539568 ≤ n) (h2 : n < 750719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
