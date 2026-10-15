-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5499
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:04:15.744087+00:00
-- url     : https://prove2.me/submissions/09f4ec6b-6f65-4fdc-93b8-35a50d9bf74b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 988848920 ≤ n < 989028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 988850170 1250 988848920 988848937
    0xa17040b03151c030207080d090807050909120703020d0f08070e0111030912011a030312040809030c0a080a0606090b0a180603050d050c12030c030708070201062114240c 74
    0x191500410500d4020340f60b03485881040c7c13403446110b01010701c29014058075416200201e0080560234a48403c01905020240c1050324030b000e07000c0c003d1001c4148500914415000b50020048032401c8e070401062038144961070b500b00100352040c020300c203a0209900b00c00580911b05600c00c40001c00d403090a44c460800d03900d5110301d101c1280c0c40110010b40003900000c0d1031100c90340c40c08034040141500c82c4074000080d24008203404c0050005040c1c3d00242c00482400f42c21180a520048041040c00c40c840d005080103a006540c0101003001c1ca00601010b040211400d1007410b001c00c010400b40e03c40341c094151411420035004d4041c000d1580000000e40e04003040f140100f40c82c1d0b10140580e44070044101c450300607a003400c06045030032021031703005000d04601c0381c0c510341e40c0701000c94840d100500304204554980c080062144003040d05028000c0030310310980801c016500e0608000702c000016848650400c106940b1541c510f070b10a10804131420300040712564880c6a50b001c10b101c0c0c0240d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 988851420 1250 988850170 988850209
    0x40c17041401330302010f18050d0804051906021b01030e070902030106170705030606071e031e090b0f0c0f011b120506211e0a17040b0315 61
    0x900040c03401c48074204240b6440440300c001c4030b04103c1c0c0c01c00c5000a40c0000303408610058012030382c02d449088600e402041d69403100d41e4850321000010071030503c85405588201000c2410701192500e080100e20050b0301c844600451407030f014010f501c5506805a00c003010552484142003030340032f03402400000b105841950116030b181c1e08120001d400a02610300003c140035005131002600c130405900500803500c0e200d05540d00c0d102003241c160301030304040715001c100b40e004015050960510500d81f0744203031a42d001320780983c40700000301d14500300100204140c0070000c0190b14404802c44044013002025603564074640c03031849103480610354017909998684610101c040e0070804142c01848840d0303032000012a60124040160b070b100341c134115030125000c2030140c200c01c0c0ca0018a0840101c0d8000e8900320040c841108600300002d000400c12034200c4c19108041003180f1400408070b55412240c0d5003030604021383e01c2d2071800001e01010058810481b40581541d641070550301d070f54213501c0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 988852670 1250 988851420 988851431
    0x5070215240604061202070c05090a05041106090a1701021306080f01060509100c0c0504020d0b0405011205060f04030c0c0914090c1003020f36040c17041401 69
    0x11003688089025400400c1e000c810301034580300a1601e4422074044404603030302d001040003c0c100030002503000720000c481c2c0109108000400c1d0701c07104049131203594071a03400a018074080c20302d94441e043c04582e581c403c100420041200b9a02c0d108190300b6a00b941c40b4414800149143c007a00901c1124811005511a010f0000da40359001c4003051013444c1500c07100580703036681d102c2503034240134480c0c5407075100da042e800740c40354076120700c00303405055004d90800e881c0d0540d070701c02041c100e91150040345000382d00c42c40026020304145c02868010f101000e83d0003a80080394480d03644a4038040e2a01d080910b43d0402b18003132601c2400446851608024950329a0780d441440c0717230080c01d0fa900da00580030003072030010354100b102060022038488042d00e0910300c0241100c2c201e00030341c400101d1808101c000d2201b00c484111180c8981410380380c007110381d001e840440c182d500343c419640c07034034500c01c0b4203080075802e03a658030491260082c000e00f92540d00e15200e034903141000000080455204d5803074a03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 988853920 1250 988852670 988852681
    0x20405030a110a092f13270609060f0b0a0f080a200304050114070e060715020d24050d0807050f120307030c080405071a0714010f060506070209070305070215 69
    0x2201c1450b0140c403038140c03064200317903200540c103031a015072150400d8a00d000c2004006980c44134217444506c900304504948100a811b9480044504a0300711880344c65a0700e0041c03011a05400052015001c42503205080c40701d01c0c2802000c482401144504100607000810032504460b000325030640911608030411281000807070307145030800c03503040d41c156013050a1810841082d103802c0d8007500712a5500b00260001d581804023690000b03c04880f00ea6200b010805984280d10290905000007600482c60404520412400d418981c81c40b1010101e482c3c0c08010b00d0740c0305449880010ba204e2070307144d1507490381d080c12030800d50b549101c12001d0103503c2c0e15848400305030000b0341c4240482c0c7c83c10054500012011911280115002892a40449001d000103c0c5d032040c903c54440e01d04441c0381c5419550781e500300e600d1030181d000500582d150300348608881103601841025140550714030707007019140c2c0c002400710003000e0240030501d0782d200041020241b0070301155418155030f41109200c1e0030131 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 988855170 1250 988853920 988853951
    0x20301300503071a060402160201080c0d05010b040e0c030c03010317070b070e090c1204060b04060b0c150708041e050102041d01081c050a0e0d0f030819020405030a110a09 75
    0x1005a640b8250701382200142d040d190a100307490301d546051201c908403480a80c010f4600441c090b1180206920611080d00f0706480c85c0606406010101511511140f90001d468407a040c094555130411005108100e00030456405a0b0304498015000c3d0386084940845185a489664800b82500001000300f041ca6504181301240c418000e0324440c01342d66400300c101c1350700d00440d248030f1440b620b440049008074803181c00c4050b85460041c400100f5540d40c1c0003107603155003c40b450040680003440c4813100d0080354400647e0180b41c9041c40c4540e0f150540d1a16642c1894400801062815260080a000302581501c0242c0221075103450003a0a14206da60251000d209411040c4039150f01c1041441841014044049090310344d10700b40301000e03c040e81c0d00302c182d1400c19089616a0124004100460101411140a6240c02041e81001d000083c00030204d401442142c50040000700b15a840010b41c45280e80d03000f01001e0500310038007000804040c0c0c45c0c0e0061001c0c0b030401e071802d4081d401c1d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 988856420 1250 988855170 988855193
    0x727150305061504140d05100606020a0c08060c0409091a07020106030605130b0c0c03070b15040b010e1003020d0e011d1b0d0b04020105130e090f0102030130050307 72
    0x112030080030070f102e50021000510031802032501c0141000c16000303060400480e45d6800e94131030010b0380c0184a5140011080310038170741c416001030b4000380e400c0c000e00c141e03040500054011038020b08954503190344500154070961013003070b9001da44c5051903401d00402c0340c0300b01100d814103038141d021428089402400381c00e040c081920301a14000202d040e40e10b0400d00c8004907544100d6200c02a40c3c0c90888401c00c3e00860001c40d0f4500040280000050311a1a0700d80b0403581a40003032070104484082c08100c503507016286040c4801c11928035000d40c3c1319400d071124403585103005a5161801251400542070510301041c5543c24508481c0360b44c14203450400c50381c061f80d13085403100a13102281040c0e00c401601c0c007d030840c40140350940070480300d030b548983c001e006040084c036161020440000d05009940240c44200261050081c00c031002d20822100048000c025130455060401d12860a8050074449240c455211000060405407901c3d1801442c3c000041d03907100c000b1410020000701 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 988857670 1250 988856420 988856431
    0x2007082703012f18010c02030a0c090f0b060909040b06010c020d060e1204031502070f0f0f05010605031203162106140406080c010c03030e030d020c010f050727150305 73
    0x83e142000c0c0d01880b10100192010310051321102c4814001c0080159200503a141050381c15018231181600400c0c024081c2c0e2004042030403001800305142c52000085601d000082480344404004000345551840d10a03900301d9004900c08049480e0100103072a0034142c5840250030401400ca0001030050640c0030070515107082c4252020b03185107601c0c1055500c92030000600a08005288106007003071640580383c80c912940c0d00c00015400c0303803611803448089003c00c98031042d800c00400c0801000f8020b2034001c00d000c4c3c000b8107001700e11007052003140c080100f080000035804181582258411404100540031175213151a200240c0c41c10080a400503002e02190010824400d409508151241004841040300a414120190380c011100b40390044030580425864549030300c0404410300040c03041c0c412081c00181c0d02d2211402d200e0070b5072403005603000c456150100308005950481d024140b00c209001031910505803010400c0da00c222240c024a140e4610510144403480e0076500c01350140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 988858920 1250 988857670 988857731
    0x112b0605010801060b0a0c03031d01020c121c020304260c0f07060507061e0216020102101b050c101811150d1a03030c01200708270301 59
    0x41ea21040058241e40040c880c0c010b10350f00c100b081101e003030710810400021912a01d404a00c1c4051820800d500e60088400034040ba54006802501d1607000c10208040300c81c001070440c1421400140a10f01c1c1d80b6400c0c201c1c1c2d00725000000141007140c0c170540d01401e00641c43c80d92464504442c2c003184141c010314000180d034032070340c8100240c0c02c80004010040b10b10a980b500d2510b01103564001c064851040c04c2c002000780502c040b49444854000703055450307198200c0340b80303140240c0002880c01c0121281e8044040c5001d000c208200641805d21002448900701180d44907540d442c003600c0d02c60303640002d030070b1540340000c02e0200b40700d40894031181602804035002c3c52500e01c1d00304100240d907001c0400350703d01e0030041102c003540c407904420480799080e2114184022407102003400c41c0d004407143e400d10f03555001012040318401e0a140a00e0300107451300ca080c801d03960340781c201900c25500c401d0b6080c102c4103071010f035240350b03030b0452800380d807001d8024031881d80b9400603003124410092155865 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 988860170 1250 988858920 988858931
    0x6011701062d08030c0d030b041404080a0207120c0506220b07120f02061518010e0609070f0e060706090519031202071e0c0f0b04050f01080f04112b06 66
    0x1403c400815034000342145006000d11b5480003109030000c0240c8403a2a40007074680009540c003071912284284101d00500a856550707500d0745009041108940051120180d1100d6a00c00b2070b80d810845000d03031344242c1d59940c4d101d2682d20780094050f0708a800d071b6180da407212030120792001400c1c042c0071458840c10204501000b20003054649001600342200164442000103c80c520903850300401d280c40a401a00c181c1d9007000b005401407c00d0700109001c2c03ca050521a02d030924146841d8030101c3d9103401c3d103152852003002484040154001c0d4864000420f01ca0300780444e071703070003c03c0300e5501c801242c5004500910501204e00100000d4021495600b844030309040180200c90030700ba4004000481c00d030142100446444410400381c0f0283d440c0b0601207a41c40b016110607000c0d20300e00000070744407072030442002400794110540750304203c0d000003408098041800d403a074103d507008002482e1401150003281005101201d85180300010303410206070030005940601c4280e0081300309002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 988861420 1250 988860170 988860179
    0x20c010c090e0a0b040b030a0b0f070804030203030f06010224060906010503060a210501090308090c1009060f180f03060515031c020304050307150809010e06011701062d 74
    0x1101c0146200da02e030307a0202e41e0000b5920700000c1e44060030301c0000401c00180580c050010a10708843c065040b942c0500716014028080d0240d0041c0f0ba00c114035103407070341d1180f8055400075203901000c2c00030b4881001c0c8001280e0706a00034041c4440d158000c841c0c00407800c079102c0075021040c400303560031400b4464a202140f00c03075215030210f9110349809015004510b15000610b440c5004e900c601c1507911440e541c030140001c50a000d040c00301800780d520321400c3c0c28038524060401e0b40c000c1040380b040c00c905416000032a00021040e048900c1810401c510b409113402c00e8415081d402d07984001d00c07030f0b88440810118400d40c1207009407801040100402d075604050140f0080d00c03a040180d25502c4036581030880c003450400c000142089206070b905040e91036020902e401b0b10f90f00b0400c90245001105401150321084c9690300c810360300700910440c0c100b81c2d1040d403100700601648411040400b10491500c8094201d40001d000f040d5449070050304178452241c0300e1074908102d00e81048407150018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 988862670 1250 988861420 988861427
    0x60f2b061e05240f0d02040e0901140402040b0607020a0902030106021e1c0c05070b0306091f061412010e0a0b010504181e1811010c0302030d050702010e10020c010c 72
    0x240c0707001820f003460007440030302d02e54020060550f028801d0481003006100b014080c40c05841c8101d6046030150715541045140800b1900040c0180d1140e8540075010740b45561180300250030079010f840c0043c401001002041c41c510408030003a4204082d4600081c8030700321980154100c0d1001e609640762000d40702c0740300054829403103003400c0a520011200c0c0c54146081024540700c802402e01581402c01c6a540d1070a0481e40e40c40702400003800f0080006034209903145aa0012141408081991b54003448284941c5240203002c00c2000a403016056081c048044904150070aa1b1480d0b2a6039a4020304d21030007821540b40d00d2071410002044801d50291080d40e094880040038000a034601d02c8450000f001c03100c0c400d54030186004040c505c1c100451051104007641d0060350458a80d25007096650924042c4c8035a041041a050340310100f6404800d80c0c41900c4800307408125500ea8640803405004c50300b1701c1e021207004005403a02612215401890744491282c004c0c0300904840c203094 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 988863920 1250 988862670 988862729
    0x13090e0307020a0311060403230601060e060a111009050105041401051605130312030b0f060307020a0f020315070f08010602011a040e0a060c05210105060f2b06 70
    0x2500483c1c540f10600000351a103c2c000b40101018201c54101940d98440520080813940080400301c101e5a203180803500500620380034081c28100500e020881002240492048000804c2046250b500c8107003160010b000800303000150311428001e88945042030342c0280800d540c1101e240c80c0d242d000c5400c03900306009151040ca4081d00c9030080d080d1001c0305843c59804845002008040c041001c400601c0030070074003d00d5841070350b000071442c00100c14030401548401000b4880c40040c001c00c502030390300146803110641e00ca001c1e0144800e50380b000c0385c070740130103030415413441d2602c4030410452660001d01400913860641c0c481c0b2590340d85850580c01c90304200d03411000107030450b08200c201e0a0a030071030354814000008441060035151208401c88502d60394040c0041c0f40002c0080e03080200307909510b906500c0720f5a080e000e514210000f811482407060001c2c540700302090002da1b00000800483e090b040c68003004011810b0303c1d5040001309520b00451781a000c10455503240da0140c141c55 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 988865170 1250 988863920 988863923
    0xd0611120f070503040f0305040b04060504090b0406032001090b0703020f060a020403020f010818011b03060f0f030b18010203040b07031d061801060b070807030327080f0702040213090e0307 83
    0x3e0919507161078480980e102c815610550a100c42000700054569040e4001c00080c0003030b58036180c507241401045402c0e01d000746d20310382c451400d05100307202040c0011880200c0130b6000030300407006144000107a4880244c1da0090305174590100343c40c020701d40c0114810402d1f2684005a4100366a0f206219040307004500021f90040d1004402d0301042d4041c2c0700c80b60304200c0c44144035618031607c840b1a800e5400c03045242d4140d0004003002c010450305406120003905400c50042131660504030741120900301480040d040c81102030114000524140c40300c0c8604441130004d5543c0d250608008281c010140d88110000c0d103414440b14002c1d138140d285a90000250018007840d89076005d003a028121500010f007019560356400180391440c0c440200389503485195640e450b0744480c20301408075080802d848499090118520009074225904180b03019030000502c2e441c0c4001e082c0e102000d016902d4002d4004c1e1000869150180f210b20b0804102c3e804010140404002e00c000705880b030117410f60 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 988866420 1250 988865170 988865177
    0x70e030c03070f060923010e041b090356040605010317030106051b070f06020601090c02030418180b01060314090706050f0304050a0b01270216020f0d0611120f07 71
    0x880c044250710918410230010b50041002c01d03541e09903c0700300c2c2460000950000030800f040020002c0040c40e000111400f502070b100040c51121004900d401a0307480384020001d2140c2d00c02c0a0f8012a00304882e030700d05c2c00c4410303851565152914081d40142428041a200d00c4104840d0341d070301c1402c00c4110382c141c038485c4c0d42c2e5604060112990300d1050b0304441c42d8183ea405400804259688800a4140200b42c00e0380204065407400103950211200d002e020000c40d04104001e00507001c0a50a01c03500c0c20843e640014450180301150401038000780005104d0850740000280280c0d254203d120032110b4003c144c075075901c450b11000e0382c46900c2d205980200300d051010150b0820060083c40d401b0340a181680c00e40c103203580c0c400b409610240c100038508048410000c40040e01002020706c200822b06046291410210001c1003500c0300d201c00a1140450000450958a4040e2140c0002d54012020b002402041e1522079076130f0000b41c00500104d02c0038001075081c02440040368011111030703c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 988867670 1250 988866420 988866479
    0x3040e0a091a0703140928030e101806030903020c0d030e0409050a051903021015030b0403120507210203060901090c05120907050a080f06070e030c03070f0609 70
    0x1c00b06402207001040003060550713800d44002c1c0c1341c0d80c0b802928070684c1c01e44003406100320003411091184401c41646161540840440da0000c0e4003c903c6003904a01129540368100720000110b0780c00181c100d4507500900d40e030710b0025685415800c0400180d2190b002d40380105100c1003842059403040c0000740002d1100d105142e46420075600200d5490300034000c0c0e680321400d64840c18600006c4a50480f0112400715042c824150f050010703c0841d2445d9009000b813144990400c1c5040155001c0070f0110039051f001305d01098010780c02c182c444206018103101c685452071016100d8007501e820844410420307020414100b07501d00c01c49116010050520608d40d0902d4002c000130410305a40074244541003044070f00d03410a0784a60751084824000401841c1d00300420303c4100850ba0784081d690740d01c00108111090310105d0815440220f611340080e100e140100080c0c80c28001190b2240c00d8081c00d07102189907a4507121400948003035803079101e50580e40d1079880c3e0040059040501c801c00300340 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 988868920 1250 988867670 988867703
    0x617131104020927151e01030c0309050a1a07170a090f050a351602030705060406170f090307060c030f020409020304120e031e031b03040e0a09 63
    0x2035020f0b080300c400250a02911a01a114103028801c5044616614555040400c9003941a40d108901091400c0c1d450104460214501054501421900a0500d626110381c1d051151003903000440c10750700541211052515410300b1013859900050f5080143c80c06800103420600031641e00b043c0080c04c0c24111b050713a54000780d80c13004140641049a812071051460000324404000c0c2c801c1c020701480500464132038040b0810040d0340019581d11940880c0e4621a001c0d0101000b030b00c0615200e1502c100c03c041a130310009050203003d8101c1e550011000c10040741040c0d01c0145031a000911048440554444d108064814a0119400e0340f5a83c020044c01001802542040601110504002c100c00003c1855081640c110703400034500c4d9039010041000744040480c01300840d500381c0c10460b8250561101003520f4079502c62852500401190031070003455000c204540103051803103088004028400c14141d00c0e039205100311400240c14401080c400d2608d88603101486910603074007000e583d5903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 988870170 1250 988868920 988868929
    0xc110105162105010b03010f1505090f13020309100e07050d03140c0319020610180908091c0c1d01151e050316080114151306171311 58
    0x605440c641d81245608001d02d040b00d004440c042c141aa0600340c5039030502c02c0c142c41800b00c0c0d038003000c903041400300d6402c012a084001c607502d5031800d6414090070000000491044420105d11400d4240300208212100801050000127081ca81c1c2007400741d0a0036046469585041f0300400f5400381520b4000000a4001c0c9050845500200c4150b0f0424804892181c19138100d038103801c030041840c10150031810f071f05114940d84649400c2c0e0090791141450104846204880e44002c1126074601d184818400808142c0c1e1143c076000304201c82c0e40c11034410040c1e004800410441d06401c920202041e410162407446010482c0d80c441200240c0c03800305c0307401c7c0c0d80580344101018048415100f40541a4a000180c00c03107650751075082c0d80c3c0c1403000e05070904450041d0104104186880144580500d0301d00d000c4d01950110f40203589149040c004000500c94030074100444141c07800006000798000c01500c1d9020581e00303506035103a6132801007060020544030014003074056000104501d181 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 988871420 1250 988870170 988870187
    0x190e06040206192d08010806070c021905040908090906100c0303091406160f090501120c1b0b010602122514010c03060e25140f0d0c11010516 62
    0x8081c40d050030071114030301d010715401d29652540c0e0700c0e4003d52030a040510b038000301d0f82c60041c00d4a0005103085e20302449c1c0100b0960902d4802446070340c04140c0c0d0300044090035420300140400400400000c0c005250040d815444429800e0284a070000042c0711840d280120b4142c00100d9241c282074081107507000c8004000d102c2c2d049900580032403e102c140c81e410403840384036a45a00204a00c1c100e82c03a000b5001265540707455003003040c200341c24070403640d2014803a00780c0c0130441004500c1d400402c40c01e80340c000e50006c01000f00c2d06646a10070a0100340403140b41210060340a032000c41e02c0703809441213548551000c0101c00c041d00380880300402c0302c0c0100001310500a07000c114640e039580c4115400e40e41d07822485000207484a5003800340c1400c00d0401508100b031203143d480c0082d4010298440c040601591000348081503420369650707446401260b03e07008101c0c1d04d007555030303280d08200c10061003d0f54250b000191065130541c144481480744600841c8c0c46503100c0c000c0070421108954411 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 988872670 1250 988871420 988871467
    0x1b031203040c0902040b030f0a20130909030c0309090b0f0f01090905071d090f1603090507062708030f0c0f070806041407061e17190e06040206 63
    0xb6110100003141000d07480644060710f89080c2c099500d04014810181820010307101e0b80403149811040320502052101d0000703030b4580c031003900b0f45030700281c03640707007070090480c2d1003a5442410700d45040100b50380000c0e01c146c4688285c9a520030304d520f40b5000e00403035814003a501d0f0041b0640580120500c1e20079007001404105140403041c1c540c8545038481590010750310600814407840c1c1550aa1580e00f0704445040c2c4162142600c0b403030f0059a0014800019050210b08052081e222141520a07000041c3e0280c00c0401c540919a0301c6c00f0040c0685800d03807020204401d02c100905c030701c03000100750b00203c4140c04000d5007441c40301c00d003c107a40d502040c55114140705440c21651801c50600c006802021000007400c8140b600c1e0a020303402c00501030340201c1c0c0e03402444091002c1c0341c102d100726003040002004425420400f40e01a605101c0484195528070401c80030020620031224104060201184c0d00740106c2c030b80c1c000d009941c0c02065500a500403018040d8000c01580040741d2080c90 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 988873920 1250 988872670 988872683
    0x605010c140a1a15011d040203091903080a050601020307030c060509010b0a0308091f0807030c1103070c0819020105040302101b110f01090608040b060a08010614031b03120304 77
    0x1d07a5aa0360b008201d125200000b441103c0c008100c007a903042a4040f02ca80d4081c00d20040b401103110450030b85c50034005609214a038080089003038014200b1505983c1c46070881c082d0601441030070084c004c1c0c50304490724884181010700180c13141d4070110980e070140d0b42c15103c030354601c801e0765103400161600500800c0704d50745e038004120702a0b42c3c0c10740400c0118024134940380c2e61392015040c07211144c030003203044142050f419142c500300f540c4040b0701540401d0502e40080c400c0501d00c0210386540404480c606140b1000c182241480414603648045608440031600884034002c552100c0e944102000780c0480c000780400c0015050840c000d5103a0385043c80c007088690b0301c0e80c4400100d450400b10681740d206c960440080e080c203242c81e100030305a1090a00114051078140000c000700c0005100030b150000c4440456005d0f210380d80f61001814030340009005041c2c680912004110100c10b9551113803003001c1c28a081d480d60382c00100b150132405005016003035240c11022819500140c411141c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 988875170 1250 988873920 988873933
    0x311030f191505030d090605120a11070803070f09080a0303051506160605070302090d080705011517161412120d020706051f140f0d2102010605010c14 66
    0x51260080080115400c81d022500f800141442d14215540507403e100b00d403401800002d4200065030303908501d10190020360740d11110741102605100b4521000300300045000d50412000c40007940c411000303aa0b4580900546141c2181c01e10150700c1011166080240c802d8042842600560303800074415281408a031506404510941d0040805440501111248804001d018001c0c113410000616049d8200156000011515004500c00801031400000d141040007030a400040565018100000d12150384001e00c03840c034440c42c0d1140003640034030352aa11921444094001c01e450824840080c05a400414083d920b241c003010250548684881c140d001c842c8038004001d0340f9404040035071241000e00d004010303104017170300c040c2087c21188090300350b039140844180d045030301d660f0400500d03020940124500240f860b446a403c03c8101e14820144030851840da62072034486078000480740c0b100c0400720300301c814500506e0300152341140c0d0003022038440005460340e0407024055030617 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 988876420 1250 988875170 988875211
    0xa200a0e07030c080a090213020c0c040509010c0906110303010306050615031f14100f0c02030f1b0a030302071e080d0f230f07060603050307140705010311030f 70
    0x2012207440002039103a5040b034440710307800748181d034024184000c107014a42d011350020701440c00c40504940705e00c1c1e003c924403107040810031a42055400180003005207041c417805580c080d2241c80329820105035030f040002030441c403030146203100c0c800001c0910f080d44d0859036048060711014044a80c0199200c6085c0b000001c444000e44c02240100000350010400c4030040d000712034654041c044e5054501c40e644c529031100c2c58600d00c0c503807881c0707808490814645410344409a020034065010720661000081c03800c03000820751507164030500701d104007040f20800c00015900d14000100141c01807070b800c000303040301000044000e084181c45000d0040d03d0b8000340b0314040c0030f0f811501c00038162004584002d50400c01c840e032800c8145c404140d42400d01c0354036054030710501a01d000316600005a040602c2000d503c601d000d0343d4042c040c3d0f83d80d92020306151024103209202000355002d000741c0010b4960280c82011080c110f103078034141c15a55400501b41c08040c0c014810f2000c3c0306802420b04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 988877670 1250 988876420 988876439
    0x120a0e0a0203030c07090b09132a1403011a0d03050304030c0f0f020f0a080d080405030f0703180b090108160e040e030a1103040f05190906030f02030f0a200a 69
    0x6a920b107a001400028501400e038800e40c2c7c0301c029440c1c0076501600a0141d04541c031102c036186035412180c40c004810704010807401100c401500664031010401d40414840b45420842454610440080c05400e20ba00c48104000d01c100d0794850744861f0048021001a000724041c0d0351150180c01d100c0780d1039076151078030b095802400c41c0449441304503000c45811890500c510040ca8801511404002400e0003001d40d5202160180c42c0b091010500c0090200042041125049010002c00300e46035145450b020b80150032044c7c0c800314485140101194440701d86003680c4000d4816590503c441d1106c150a201410507041301d5420040c0070b240e86107141d11140a2002c00340c480c100110b50710300300810010b10300f00200070318000755002004104103900b082c4c880e10081e42c00c22182c0201446a61100900c40010759018082007030030040000306100e048400110124001d80984907944040e600141c1c880d0034a0340300500759075189913040d00300700c0c3e00b280742e0012100144c10035500070303140c09030036 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 988878920 1250 988877670 988877677
    0x405130b0d1a0a110306040908041d06011d091909020307060504150804050c09060d060501090c030605010c171b01181208010605040303030507030615110c06120a0e0a020303 76
    0x2541d22204080050345480707107a0042c40c0d8000800441041020422807411006200240031103104d1601c1e00a03020034004a0342c01c560003001c00c16a04151442d0b02584002c1f000070883d0940c0c00301c0c03074424503030104903603020b0030741403010700100301402c140d0302d4400203000360038900020905c40b607a443e200e03030040e182003121402170203840d2070b0780e6121841c04a0581009106803c01030800c0b8001d001c2c880010300010340d181d0072200071507812466503a0400461400d40641001030609402d2000004540b65603502025a1032450707a002c2c042d0303980715001500c000312400c0008100c3c101806003140c0611007800607140e000045500d407010404440c00090079540c3c0940d1100b40d21041051440421250fa15800c6c2140d0607801c04280c90740c50450041c0c01400380f0721000d01416150f13400106482e03c41c1e40940080c2c4190f24100070804031101000386840003d01c1c8040103441000040c0c14240f80150075103c0074100104012400c1ea80c1d200250090300041156426600c82d4040080c016542400039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 988880170 1250 988878920 988878923
    0x403200f010b0306240904030e1905090f1621090503040906090902030d0813140d1218060e01020c07171b0603040318030c1d0109050106050405130b0d 66
    0xb00e400c0040303204040c1485406080c481c0611142c40c218403402100c0f00a8005107002240d81444d140d645003019542c41d500c041c1c4180c5d020040f294092143e02423014102c060701e9080e2400a155520501c0381082070700c042d548000320881c0f05a400d9000d41c45041d1880c0c01144c0c4c00140c00400000704640d90948815180444a40d00081010b00c40340c1e129120b2400103100784401071202c070003582c020a40303468901029400f00248034000402e1002000d40611b000c40d03008400e51084e00c5800d46044e101c1501406410020303049501d50080d051190040590520514400d10b03101c6282d550b54100030101003c01401d5550203200844401c40c0c1400000010414400c03116802c400d113420843c01c0c506172050250340c4a15070b000d11504c81d00c031101a039910692500f84200c0c00d046104046c03424030150b601c010035009000d80c000c2680140444903962010341c0900d2190543d882c0c1516200344c502c01d020707500014509000c108018900b070f0808060340a06500009009810000820508001d1520 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 988881420 1250 988880170 988880173
    0x503040210090905281802011229090609010609062007060e180f0615070c0311100c020d081309090c14090f010905070e0d150e0a0b0403200f 62
    0x40c1c540d1000e034a004499400b4107900010840455071425143c0486e28001000c0d0411110100c400e400c008594800062130074482e400c1c0aa00200080140340d0480c40f2166070f0142400da0049207250810302e0302c41e8140e585903260b40d0103032402c0100848044171aa00810b0500d02c40440005030318000380040c90103841035a40c0d05a070b1802034000d101300300c1802d00318071100038420070410654601c80d209050700044120f5030405005c41400820281307024020000d0011030708103800208200d159210410b150ba019913400d020154185020303103106035440c4c006500310a0f680300c2038000503000b8004168a0010325818140d01c0d45550125040705c12090b400c40341214460f2090126003a0010202040101200e18402030300d000b203034514140c0c3d0b0600c07880c240d49444401195411740210044840010007800c5207110310440d01f0210001c60600d00400d200311319000c08001c600e00040f8445018903045001074216840da036030221243c040711001080c1034200b206004402e000180220341c14000d0210 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 988882670 1250 988881420 988881451
    0x1031a0603090c03190506010e15121b0a08060f04060212070503040309170c210318100509010215150d050d03050c0a0f0e0315130606050108070503040210090905 71
    0x5042c14a4055000805501174200d052200002600010554151f4091141000f00758480e480e0844100300c90342e000179400100003e9020101c500095298801491804445801180702c0184000b90075140600c495a400c40000200c403d054004441e400074410403005180204020343d4410400d82540e5040001e400001440140b6901560500140c4003404d800003420703960418241d551081c007251079000e400000840344c24912348040010b42e519824007660782d00d1540f00c9503a0004e2040001e1103128462481210307540074452815520b00300c0061b0010000c403821a1010124801c0040901c0d40d603141c407014995131526141c0804009074460b40c002d101c2e4240c0c21802a090300c0d401010402c80c03400c01c0c8404030300340303500c0512229051050304022405138403400120307092060b0507011016000c0070500b444024541c00081c1140203000300420401c0c141ca0300011244030100340c1d03141300081c41c1440880d026107031400d03820540950301d003408e52496a8505c58a000e88070203e401c1080d156401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 988883920 1250 988882670 988882693
    0x601060f020f1506090405010e07090204090f020a080f040f020406270b0a060c1b030503070219050d0b130b10051831060207050106031101030213030201031a060309 72
    0x10402c0400200582c00541440038074001003107030368240244428841d40c0c020012405104081d4020180c491401064612072510343c203141010b0342c45842468001b614090408207004040c0c404c0d546c40c8c00c0d0950355000e00fa191804c15207040c0c030000d001136070195a560950001660b5602c1200c0c01848040090440301017003500f02e58049503004051040e00c0c0c10246841d040c0e64814940101b41c4100b401c24042c10321403406c0c40030130002005201100e45484403804400e2203c00001341903594400c940101d00e5810400d52541000128490315800003105209880046e600c07601060b404000c20030351103e182d416889070b00b40d04000342c4010180c8140018180140c1c200341c5070000b892100a601d0200031f082540f144040150445540c1844c541c0e070340c103d401040e014040403868a50400340554641c40d007803e086000f800e1500c012940d4101c015414005540240262040300e003155030194070007861a001500641820002510070300c00c1d59403c4602031303032620f000e103009503040b40003032140400e00e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 988885170 1250 988883920 988883923
    0x3140d050403081302180c0c0a050a02031e0a080d0e030a17010f050d0605101e0914070c060c1202040308030604050f04120f090b0403030e09070f1202090609030601060f02 75
    0x5030815040310b203004d80010160311104107400e48034414044141036980d4410403000680240d400c0140c1c14055902d0395824040c0025208440750300031020750f103140701c8040807044a14249424007183d500400c0888000c16000390240c200c040c0103030804508580c0184265046038881c1e130440d0040f82807031407a80000701c290081c071805080d054034500081420000040c038000360241c40223103511f40f1000000c40d00c40400104000a01d08000b040811b2910300c004070032540da06010f0b02941502d440c00828031521840c040e01c1c0130340c160f92522010901142c84440141074180c9000040c4101c0d44000d8008000d10b20003400254040c0070081d4483c180344040200780e80d000b0f084829031500031028030000c105401078620703880c00d803401d00054400c8603203c291090000c0c2e5000302c400b10302c0810000241a00007410320901c0300d08a80105da9941c0d440700a44017080014905030013302c1000154841000d95801401140700c010b20070342c103020301f8000203440c002e002d0700072900049202401610445c0c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 988886420 1250 988885170 988885187
    0x1608030f090705042007060908040312030f09030f0f09051005180925090504021201060e0a15031a040e0f240a110c01150f050306150d03140d050403 65
    0x101103d0511601c5e401406481030072103d105c20703480d0540005010010040660300c01d03400158000406520b4a03030381c1c10b00410246400b0031803004241080200c5a58004500c01c04803032980c540c07100407040c80790b440704548142d54440e00d0020700080304400702e8a90b886a0b9500100c4000d075803030344e03580e440070030319903c0c0f00c61140e00755801941900305002144244401a03c40c24040d9100c440c1030014110044440444640c00035400c2840025603600c003102d42c0301c241e81a1501c54a8811500c40400c050140c010351324440e0036210010070188031111032080c3c104500c020212101403d21900110028040b20b4030491112040e03032091200760782e65007041c8100d18801c460114540f200401c00d070417202d58844010601c0c01e078644d54440603c02a6104000d59034a91082d4000304280c02c42c01c42c800c0a1035600e40140300300b004860600180615000402c0b51150701d101c0d2070882140303900e50521100c262031503412030034440e9500940b21900211400341255a459100c00f049a00341400c000d0842070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 988887670 1250 988886420 988886429
    0x105191d060f070306081b04090305070606030809040e0303130b1305030408010203010317130515071b051f1d060f030a0506040c0e0f241b1b090c1608030f0907 70
    0x10802d52800c1c0c00c2403500300380c1d01c1c2c7c198030598021681300440e01d07044925100c1c410009000c00e240030000700074042c1100240c1a030181c00e40b81000403200641c000c60366070100704c41d81502081904044000204d08000d140e4000103c5011891a100183d40303c03400c1d0b0708240c00c09915690b020004000b070001d100e0780e002a04207000c3c0900d1a00d00150000c110120150013060f0280039184502c0c0f03205101c0d8001c07240420341201070700300c65401c42d4055100c0425a44640d5105011700312904588400741407004410200d00e4a070340c07110b007a411200c40a078140e07414481b98081002d020150303005c44682c0040d44100030787d004c002401c0c0b400300100002c6401c024582d0040140480b90b1841d9600e5004458078440d50480383c6072201914411103d0000302c00480784c406a6502040c110303584121110311001c40f2102005584d4034140c01d2180c1c10074071007030b00300030380e403158841000c140d8144d0880f008040c2c03040c003400341c6076080ca00c58998001c25401030303500204100c3c01d1410407020002c02c2c003010003e070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 988888920 1250 988887670 988887673
    0x3110118170319170c070503040b2a0c01210b060310092a050c070306060605070312050f01180e03030114030d02010c0801050f0402190c03110105191d060f07030608 72
    0x5000010044d2549080100054001200010440144071040065400900030352130b00903640d03007604001e1151080b941c044510614001c598814031401c02084c17807414100180e440070146c07118447c40300b680b4141e61449007081c0342c0d5800402095160030004610a052006e006451103241204442c1102c14142c00580a14031500460408400380341c1d03081d407907200500e17102e42c0360900402d03c20b08026643e800207024a00d0326000040c1c1c01e8000020305089406a11958544c50030550080203503001122100b00c0c4200d103074011702000300a111120a641034441c3e0001c2d55122200456241da442a00f15003002c6104845140052808000345601c0d0b200510007840b007101d034503101030403007070041c000c03c4c0c4210703040300000c00340d520bc40d81902c0003079107045480484072000720000741c83d03034611030816400101c10041440545005008041c043c0c259080e0b5080100c0400641000800c00f000c0381c4001d6841243e0034600300d00f01000214042e610952000e6000e040070070300a012154941d010007804d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 988890170 1250 988888920 988888937
    0x506030d1706060901030e2a061603030509030f13232b05011b1103070b0c0a0908010f05070e04060602120307030e030c0303060102150103110118170319 67
    0x4010404519800c030b00d05071043c03a00d070302c1488010380c081c02c555409032a00d0700c180020303241d0b001c3e4011600c44800310002080c2800d0a115001d100f550f12810000c00c840e04050012540003034400e600840d8400c9840301640c0c1410742c481900c6841d98400c28a01d404a1101c0c5424080044540c00001052500f01071002c1d1a04407003020850020f4040360407034501c41c100007030744110b240c902c5074030201c158000001c010203180d03020f00750f9511f140080b100000a8104840c3e600107140001164008e03034000c030b84e010440d0341d41401e854840c0c0c040c6000804000301c1c40000100c05200740142c3d122401341d1580852a850070072401400b4401c4a0015841903091120400c02d681d004541518a1074500d210705a4960303e5120540280203041c0000380c8502c00064070340c3c7c54141c0400910301850090303094480302e010810744d0790711b01c1500b03000c0036054031118818222158082d004e404010709141001545641d6120483d41e100c0d18182d503c1d1103c1d8000090f5a40110250400010300c0080c50400040c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 988891420 1250 988890170 988890197
    0x10c0801030f0b071110051501090501080a0b1306090207061103011203110f15040b0109090b01090e0c1002010c18030507060503040c091506030e0f0309220603060506030d 75
    0x1030115031075805800300c1c02103004913003000d10540b101c0088108000c201ea40100c00418000c0040100b200d100004138401d110f075003850340c4a80d10200403100141d488134071980710790660038001d020307117805d45500c04118501c4400036041c074046c140041042600050301ca07280784c00e00310169100e4100d0b91220b101d040005000400419070b920b400181c2614040d200c00041f08a0300e45000340300c841ea90002d01ca0b0740d280b4640000c8568450780709a20031016490301d0790f40d40300783d04245c4280c400c0040500c01c40c08014000c1100c182d10010003100b809044400d005600c8002c1450000d0042048005075110300c243d50225401c0a043c1046548041d000b041c05880c42e00c0d216204ca483d8003c80c0300300700c40003020409000140d800c038006041a41020000c45030320382080200f8104e5481485e0100342042e0702c111448030041600701e00300a40340c028501e4245202c0030082da003565002c0201501000304880c20241280744112005144103400001e180c2c2007240416280c10b154034440d01c10010202040d00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 988892670 1250 988891420 988891433
    0x150e0105091002071b03081308010b0a03110f12060108011d0601050f01121a0906010c201801090606141c1112150405130812040302010612030f02010c080103 69
    0x80c2d010302d19100140c8031802c41c5441c18500c103007120540c001030014036000c01030003141c2d80244807400d4895006805199070304c5455007030318405008290304c20800c5004101240c003404041100510040c10f030307400c503a140800583c62620b100b14550a6902020040c00303411f030f09105200b86001400c03d1000014400369000c0e50360f2805001d014011a02c4462501d00303640240d50a2248448208081c0440ca240c241500e0406aa141416104503060400b007407095010f440d502c4101600003141400798051000d084450600043e40160042d980c1c800d01c0c6022107540a8940c00303858260703000704205151003001041c904528a1940110600f0820390407a008034503000d90110000c403201080020a01524116a0049031540510b03444051704015007503000007082000300400b107030104107039260035000e101d1040c2c1140005110440400000c0b00700301509850300c0d8014400c0c030010460f152284080c8600d10350b1104210049540552204619030b0280a030140c500d134185040b600c59895500c400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 988893920 1250 988892670 988892683
    0x40b070c2105040f091b0309020d0b0414072c0708150a15120f020f040509091912021b06030a09210525230712150e010509 54
    0x1075501c4580c000020700d049028005030b07401001034145269001d42d0302c1c03900c0740140c001c2c80c458408581c452004180c0007406881103500040e006460010300a00c1035855102c0c030031002d0030035a0b00380050b030080040303c4000c00400000d04850030f010340340c28500b03400c0300e015281c843c950450340300c0d503040c10440c84c2036002030210750014130030491000c00e2001c100405c100000c280c00086061500c0307008a1182d6402160516070009162030410a0600042001c0102d000303900c0c409524050030401001545021000d1640040d11078003640c0c09008030300e4000141004120049032980d0400c40b43c002e190383c041c0804102c5000700d0001e40050384441c0001080743c0310045c40340d004155070700c0ea507000b070090105440640403024901300003004d106500180558204d03201c0340c1c400c0c0d810381038461822440d00400f11000c95100610000c1d100e02e140c00901940d80060841825120f00d8034001071020410306400d00450140e0812014060912404010b6507040c001040103a030401050000d00b80300015507 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 988895170 1250 988893920 988893953
    0x3040506060d110904080a022a0d0809060a0206010e07050403030c0f0602120109051504110a39060605030a03080a0c0509090103080a0816090b0313021305040b070c 72
    0xa288003890350700d86100155800c0c0f00c0240c02c90050000c0004002e01c001c010014048940c007100c1000f142d20585c1e1602d04010b8140f40780d52801c02013480f5090406242c948100c0b84215203a505103c04480070510716044101c000d00164001c00c010000009110300c0c140d0000c4461408a1500d0b04644000d400254407001c020803d507500c1030040207004440e4107954511180c0000c104040d6034400c803200180c0410784040da400d40b00154124010301d0203204070740318140070000203070804080d80002d40b1040b040b00702c0e50419824100d0046107402980c0d034594141480c8882e005d03021941c078140f1508540c1107401140c0a548a4605180440e4200c0c0110b80e00c0050b0300e1003c0303190b500c0c80c0310480c1e09009070100c0c0d54009010400100c01c100e03c40024010b80180307980c5100a640d03504c100c10514182c0d0901d02c10202d4503508007441007030103410007198811105401d50189210b2940403030441e200343d0b610594400e5850f418001002401d944080c3c108403c0e03c2d1240c0d8404298503800e62841a5001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 988896420 1250 988895170 988895179
    0x60114040e1605120709030b06030a0302100906110f040f051e0f0103020d0e0a14030a1e030204050d060f05090321101208070323070b070212030901140c0304050606 72
    0x98002543d00c1007080b21010748141242901d60305190201419006590004550308609000020803a042c0001c009607015055401448804600020745c0000c11031454280d0300e83c3e446441c41c5110800355001800412020504141c1c0d4902d018406101d59425812440c070903600902c210042c8070308c4140c00c10418404490003101c500c00340700168001c1c42103038203812409007410103d074007005010507040749440c011241c46901c0040074591503124441c0311408804a8003074084800640c00380321080107086920700b0014601511040003405140004400b04d9140752100c1034140e1500c814000c06810042d040c004504000102e901d445054400701500c0075001c140c9800280c50324400410a00105103640d801000080a0708150f401a40b00000540100d841021480e600c65520744142e0284d2420340d00440c1868070039a1131002c0008042c00320011441090a00d103d0003500800650042034000000119642d00170030b443e40b2018001d20401184e4000e004100100350045511a4000001c1300d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 988897670 1250 988896420 988896451
    0x6010212031504061a1b0a0203070e2a041701050105060d150302040e16210b04080c0601081e06011a030402031009031701050316032d0b060114040e 65
    0x2141c0203000c5a885113422660000100d11024170a00003001011080303a03a8130512211036410907590745070410001d405a0090401b00300c460b205080c80d40d00701000300c1e0840c40707000b0500a83c18050035403692511296000103020400750740c0b400200301020044100a000342c3d0b141c000026418000c14008004180d1190402c6e141d1035901d600450166030300820070424000c001084a603900b000860710700201c025080c01151818114411008400100c3e002207861205984c2e810003021000c0d104544902003032029206030300c4140900342c042c020f10001040003400d031401c0b144840740c81d0500c0e00c0c07403a08174100500002d80700020020000b00520b00307255507903d851010030301d006400307019200100d14081140d03081503800b0314190040403c0040800a0781d032a00200b40e15400c1c0180c20841c0c6c40130002007000020400301c40440c1d1041522484039001341c424040542e0f44103404d0045900e440d46204010f2a03682003034112094040d4100d4460402d401c00308070702c0c00e840700035001842c03840858 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 988898920 1250 988897670 988897711
    0xd080d141f180e060a05040c1e1a071248030509030709050103060501210609051c1101050f100e04151805010c02161707050a0e0a050601021203 63
    0x280c01400400c206a000c807404c034a02072800800030941500c088480400f00c910010b0030840120700c00c4440305410316016141440d04e031005100541e252080022070740b00340a5100800c00302400a035220300d0580b1051240c100c115945408041d4494017110703514409184543e240020190f01c0c10240d00c000484034500c1d46608050700c99000b48188039034144205a8040f9806030745400003412a0300c5620b05000030303621f90b00c001403107091b248001c0700308149000000700400e030240c0100784490b01407002c1d0b5901c032040700c0705044c1013002620248045100e5910780710344501c0900c5115481446100070310400c1c201203010a00d503140b18070414800300c0244000c5010700111542e104160802c40c072007084545021700f0320200520300d8050036142c952070051040000d90004c00c1011903514030118400842c0d0400442c56400080b03202c1596030ba1040d61400700e1252600180e88001c0c00c1100e013182d0b0b540ca0f01c0ea081d0301c02d6610040010f030454001551101040c0442400d494000c0084244070101080b203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 988900170 1250 988898920 988898969
    0xf0308070c090c260402090a18020303160201080f071704140307060b1e2407053013090c0c061113060810060302090d080d141f 56
    0x1290002c5008501c0e00801640950700045540200003400340c01c140c200014200002030503d0840e00a5007000000f0000340d000821a0300c4503181003000c184014292011340c000c24510b8000c50b94610441329444a10015980c0000001d07910010114880d02c2d213240c03001000340303d803040f20316a80240c030919001c06d041100005229485d84041c9088070b132119841c0c203065000e0110001c1040c0250101086074164207001c00708141150070242c0440b0000c1d042001d1100e025400c0ca03a45000140c042c022400081d405009018009440707082c0c08000c4000e1a00700502002d4902105c4c1c07009034204002034500f422400d071301c8200c2c0c00c12440021100d00a61050b11320045101000f48070614001034940411581c0014082c0f801c03e1072071620384292215010395202800303a5108170909040c410070010503100750000d11424901400700480030074503980300c1059070132110800200c2500c0c1c0040c820841c1e90301242c50b6104245031a88030403010038200e810b82c007010303030301035840c01d01c80c0e0081c41039860b60b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 988901420 1250 988900170 988900193
    0x70537050d18091406040f05060306010501110a15020403020f061204082104030c030e03010902031506010516080c0c0d020d140309150c1219050313120201020901030509070f030807 79
    0x700b0401c2030100307005854203407030703104e804a40c03840c0300700c0c035240400014015500c5614462080038009003000e9080000548110080e117243d00c2c1284100c122041c0000d8400709500395160803100f02584650852040000303020304080914055841800a420303460205100f050308140c1128080c0d80d00e075549060b05a1a9420002040e0b01c49840d206100030164441351489001c4d0107aa1901e221301031400c1014281c0701003000103985940441191032580804040b0141c0103001414124505441c264009168214049013030710581d07400300d042003181c0d800b03000c01e8a0a440403a01000482c009600098500c0381d600b0b409001900c00b9064200d81d140204200e0303a06400092803515401c0ba890300340300380d96000040481443c00748051510700301c07070031a06031440d40c450207401003004d40394800c00b2a6181c00050030781182808070103c56003c40c2c07251501580700c0186031b00150b43c03000c0030000901660000340008105501c40b0000300b200350031140740082604e503c01c0b1150303590201410410304000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 988902670 1250 988901420 988901429
    0x405070509040807021e0d081305031e0114040b0f0a0b040f0204030501060b04080a08031f23010c26120a0903170403050a03050705070537050d18 64
    0x45000705000034803e29070060080a44200e6020b6480070f2020350248100880100e031a400011040342280043d0441c0b0241080c40982c60100c40e1250361100004d02d071440c202c6094049903480e0380070307a050420a015010b61401541c143e1016428995a4070105100c01429509000000e501103090042c0503000300c074403540020000d10501119078400340007988a4801118030b5031900030300050600702201079404540d441c0e00944dd05640e01c1d00c4950042e44010703c0144961224047c0c40d030550071070403400703010b07086c0ca0010040040803d03d0a080e00f2001d010310038144803c40d00901c1c00120180c440d180d14840c010000c8071400c0a074103a81102b801290711000e000d0343d0103400c121800102d50702000545000366100720541c290074159044503401554040c0c0082e0040010342d030283e00079080103800c0b078112314000380781550649a642c20a841200060b410030705001d810f403101c0c8100907440d00038159542c018034404440390740d401d0f0703284001c00025061001150143c0f45044050340540001d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 988903920 1250 988902670 988902679
    0x60f080f041e0c1707080109020603150a12120905040e07090f060905090a02100f051603110a050106181104030204110405061615060503660904080304050705 69
    0x1a034403907440c44540c0c0c5101d004d0388814410a1000942c1c04414040d160415401401c4e051a6803959250510708103406107000da0007038002140010207003000501d82201c01c1c064440b542c0e03c071308909402010555281c2c09103200d50f080040700e800c40d0034040341c0300d01141c548110010344101e014451a025040c1503012251840c9802c2c1007180350740d80812074041541c400c031803080111600300c0065421005160724500000e6081c061000000304010a01d188107000e410501c0c1b0210864014515040c0c50001c104e909035104d01040050010080480301400030310141840001c0755010040124000c0e440064401c584440c44604406406000c0310003070040900340542d00c14540314071040c56081c40c40d04490649070309203c180003981510030b0200b82d940060162101c2c1014015600c80f5807024108802c12007845130000311780400342c842604c60011071a507000700c800181d04c3e1005200d050700c898a03070040d5414500c80d800769200202c1c181d0090303114120640300d8a840c1480c0e0310381079407904400c0c0c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 988905170 1250 988903920 988903943
    0xf1401111c170105040203010308030c130e04081b0304270b0607031106150d02010e1801090b0f1002071505070209040305070b1003030f0309050c04060e01060f080f041e 74
    0x46030301120b00c4442c2c45800e0324140940c0d0b43c54091004074402440094010001400880c40400007100140030031103442e8004515281c9804902090700000c1d142200c04140020f00b40d8114a208000c2560084294001d0b5040ca450f10002400c0480c0d000c4090b041e08940040d200c2c00b40c030041d80001407140d00680025100c2e40c0340e280107402400e22075014115803160900140224409800c107000d60704000e45860f06a07a29130307005440d40e40c3d000d00640d0b0301001c000d1000c2580504074812a0090039204400b00e80c3c03001040600118040404d1b40c18014025030040326015900010240102d4020907c8801070780801078040b0342500403010000e5104c99032000740024154020090b02190340640450b800b036459031144221910b1040c0300c01004940380c44801e014040c0240c1c04400b80b2400b82059400300310144c0c002804a400e103400402c82101d003e001440728541c08007000010342100d0611100e28108011140a40440200002d050603030070024014400c44841c507980b101030b40032401448 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 988906420 1250 988905170 988905223
    0x5061b1e061009060510050f09040e030405100311040e180307060f1d0a02090a060e10080c0109120f0c18090302250302280803030a060f140111 63
    0x441e9030041d9070520050a5034400400c2c1d1040900c680c108452000b054207031001c201d1817058a95401034144490303441028007025143c0d4503540602d9510f020320070b01440e541d41c101020448590002e211010406143c86e1101b964203001d1740490f0f064443d00b5400c100f6a90718030b003207500d0603c54145d560040b0301021404070304109860300400d0003414404011700503420b04440c4d9a8280344141000350840e031000705003c0140c100070741c7c141d802440e210320104605842d100d003001c003200c040c1c6051038400c46000341044200410302104c07070390803403d290103001c1c1c502c4c0500f28140f01c1000c00c006425580b210382d4410400028240c080700402c1000341002140c00030650400042942d0402500540941c0d00742d501644130545001d14583c0c0da030862032034054156001d200c40041c0140110380d08032802c020b152281a003004ac910b008000d248015a82d9141991000d010b691640c0d024040241c0d48038014490110003251070790425800380b0b0042c10130038289403150301d041814490710119003211803d100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 988907670 1250 988906420 988906423
    0x1211150418020c010501140105032415030f060d020915040219020f070501051c020706090605040c060e0a141c0b0108160b0301050a121103060a06090c0905061b1e 71
    0x30443c031810080201e07a0b81c414921000c400090384090005800f040050013a0a401462403d03844184c01e4845c01039a000010800c2d0011200e1803019005020082041050b62505240d80c081c0d070594050521149a602141c0c488a000d030546019186e41503409181d515940d0642c0c01d480000742c54181701c07031840c4030041d441d00b08418040856002d0a400481d040d4022411929020303808807802007030f00c0c0f140a41500a400100080b00c1c6140c4030380c2c03200c02081c2c0c10b0080601a90041c2d162000c240d2401d240030700b14042c003400c51801034036002010402150281c4040803800010345800381055024500c0040500c61420f009020040c02400890503100c00110899041d0000300c510b40030701c1c0c6580589007980000d1240070b41c0402203c90038095030a0034a400c641c5140308180040029101d4400a4100841125400d07080c0d560b486040048100e903014a01c5804268206202c1103828000441c016120340070410fa010419a1711056a801d030420020400b80394441035040e12030f6100c1b2845 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 988908920 1250 988907670 988907677
    0x30215072001081501050315030708070602062e0909080c060414151017070b030a0510090b01090303030b130f020a0806090f04060c2c0a121115041802 66
    0x28001001900001d400c5113202000460356007050f16014150f40d61420241260503c00e0b41c541d81500401800180c910002c0103401c028200640207002e852074040070100e040d4004420f26810542298440c80c580481444960b00b5580205030204280c2c100341400341041c0b05e0601041d03030354483e5504010502c03100e4107580785018030748016a1202d100c800e900c5681e01000303542c2e85071a000d0950f0300b0440a072102c400c001011100d00c080e00c89441d9698408445070304121185001030b5111010400d00c0c41d16801c0510241c01500000c1040403070410000b060301c806404010181030f034426248065a0f10f10507400107000803c1400d101101c0c2440c406030194114500da42c0201d401000422414035050100c41d1003040c00c040480305a5a542d00c0e404043c0440b410410203014007880425400c020940003001012395065000c0d140700c01d02c03814407140b4512a405184403d05030301144001070100306a4482d01d83d811500900380c13a01204c0040f229101d00d61054a0450b465081e800c94401070b0b4000c1d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 988910170 1250 988908920 988908983
    0xb0c0d0306060c051b0f1e1003050c12060f0607050106030b0f0c07060c170711120a05091201020f07230c0d06021b030d0f1a030703021507 61
    0x50081503a00d0105440a100020300100150000e8a00803078034440315000c008500d00003451038012400301d10100d6041d0000250044210f001c40d00104540d0900d4422328407803943e9072500b08840c0c5001d9134944168050b0540d1951200700400100d00d80b40c0e951006818181401070030340340c0d54156864002e000305030a1200301d034070982400000304c1c002011a00700d44540740e40d10603030b46042155503c15004003088503064040c0304100304850781c852000c106071481051070380c681038a0342c00403002c00b501d05003030a03901c00358089040125541365580300f42907e20340b030000d0f202c1a1801244040d001c0c0a802540e000801082d00458440d0138071111b0020788403411168562903000581d031200e465191400104002e40100703a05461100042259001700982c510082c0f243c80c0314942400d1190865200b00c0003243c415032a40c0c181602580184641005c5810748201054600c4203080031030b8903854a03200292180c111641c0c9031381421800c0c01180d0356a0f900c41008441180850502884103044051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 988911420 1250 988910170 988910177
    0x1020c0901090212100b0f07060e030a08011707050109050f04140903220501021b040b090406020a030c0804020f0111070816090605010206040b04080c1e03071b0b07080f040b0c0d 78
    0x21803180c1548400d43d4083d070311b00c602450b1410700c0d210030713a107540d500401c003c44403142d8031443e901002909101034140020740d59a040e1003545800b03002023099280c01c444480c41d80114008111582c1c20a101070300300c6905451a2500003401d20000e001020403a20289201c0d4601c0204904090044003e200452030450034440d2034049030400107602c1094080c0b4ad02582c860994031440e07a44040042400082c01880402c040c0b0f45640400d155039020f5400310381080e00481c00c08400c94141c025142880700b185080c0b0000d140540000328410709140301e0074180440000400c444580520090015126503412140a101400307030300589d22089102d039800481c40c03d240440d0541c0301240d03080c01107030408001505500c0d0780c0c4903c4039070707406030364040214420102668103079210b880d2107021007014003000d5230312a0058241007400758045400f00c13032485031070030051112054900590381210b80106096840b0810707030815100354803a030303080040c12080205602c600c1030310006540c0c1c680701080e038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 988912670 1250 988911420 988911457
    0x9441906060806130b06060f0906070b0f09030f1902190b07020105100b09121c0c150905060a091a0c030405010c03020a02030d0e010204090e0303070e10170601020c09010902 76
    0x1a07619401c0b40d40c44020000445c20000c0f80d40e900d44a8007510007070410b50002442d080360980040e449903c55481241c0d40e8803040300b00302806094007601c1ea4000c20704005940f52041d5003c0101d0180715a0407103080711600f10300130f401114801c02c440b4440c2a07000320400b21012403420203400030a401c507070310700040d030030440003c44400b0150102000c90708100c00b00307030900b480001001080d000e07039070000140d032103030909001e0800c40c2605814111151038490001484981c10820704600e405040041d03603504040301a070018400140d01688100010f100040451881c0b806940740701d40c01c514448010200340170711524a40c00d030010360140d44140001c110000300245c1c00d4050740600381622001da0000e10140407440b440fa0020811107204400042c689616000c41c40111842c00050703241c00d51020041003c2250003200b1103035407207812200b400101a0490004000d00d000c0d54040f40000080004078410340d0003003022a5034140b00506200352581c4510f02c1130025005510982c54040140c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 988913920 1250 988912670 988912681
    0x10501031a24010e0414131703090307141f02030a05090c030c062521080c030112030e09070807230a050901050f0a09441906060806 58
    0x2c80c03118101100000003a000700c015550813041640316a0000d44130100e0b41482240203448500c1103000606001000c02c06040140400d14810050b0303140308810000e204031484004140e0b0303400c80c0d001041084070b190704030001e0708280e144100005641c0103850380104105444d000740d4425281d4000401c80d50703440d40c2c00c8030382d108211803459030150031428401909050400003090078030300003104801d8a200c0130501050035419080c054503d0545224026a0f42c010408114034540c0c8624040d0703010705146014840c20b00c81031042c80b682e60003400c0380b8002c05006448040e8100d200a0009409161019000c1e00c100070031102c0d00001aa0b98084801c455800019100c3c1c10405440315418150300d01c0e0b0030355107907202c041c65a043c0282808200054404040182121600e580c1e540c3d00303481c0307800d90f00411920411345007903840862040040c4d224040d0100301c0485802e6048804100c82d01810482c00d00c194020304030345200c13605c0690018400d05422050403103070400211000c0359900d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 988915170 1250 988913920 988913941
    0x109020a17041703060609121c090806060d144608032203021006060305090c040b06040f08030310050d081902030d09031206051005070201081008010501031a 69
    0x2240c00904002801540d03c0c2c00e2100c1030301850380020050700b41c0786040c028100148904c004d01040a405a11540706041405041c2400e4100c034216404d098100b107091071070700d039141c0200809590050000840303410600c1107904081d070300c408030364080c0c404440841d2045c00c1400d00800425440301000d10510b22901c001207103007403031030005803190030101080b903031240c149078406000c042d00110425001850600b42c055070401d268440c1c1c0043c800d100705402180150303040c0703a10460925282c41c0c1001840080400c94981048044074001201d0180c4000100c0501898100344105d11040c4008548210000001e5010311070203c030109500c0c0d1b89200f0403030031002003440202540014090303a42003c1d00300700e250341780007018015030b424054154000c900710f8080344420380015452010050580b0058424000a0b00050303132540d40468254002401c54820074034001c0c1000000c00009003d01c00014050303001d003140c10002e00c02565a402d04003034a243c1144040d500085003004a400c4000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 988916420 1250 988915170 988915217
    0x615030c031b0a02101e0501061d0a050d03120f050106020c09010b181909020d23013002040e0303040318030c090207020f040e0d02070b1804050712050109020a 70
    0x16a60040c49580114000303170029100c6008080100c102c0000c3e20085e10040380a0a4040c1600d42d81d1881c1034800010380c0d0148401d010b00c6107014210741c1c0c43c103000d103407070350281c0007030f05601420322111301c1c030b00910100000c000540b000ea6a0358507000002c034200b0750104001d20389020807112110780b42d032030b04200c5c00c480c811220302a03000b60800301090814100410700c2c00c1407058544107096050303519145042642d00c00c06102000a43e80e010081712070220f20341281309021440725140580d810960f008000010203002c0c40400341f10880c2d2020a603d00c41d5a904020794082c0c007d120030f51105100765540e40058604501240076882b042181400c06010541242d42008a682009240816a900a41c0460313026604811101c03e090415290341c0680c65400d049a0010410032507545002410301116402c0700304619020440c54001503080080c8004500b800c13500098252104001602d424050040c00c022003410000000f90b5141107074050241e2411030380360105a480ca45000d080c210b01d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 988917670 1250 988916420 988916437
    0x80901201b0a0512040e010e060904080c0c030f03180102030a050d0b0a03060203090f0c01210c0c05060907090f02120412110f010509010e0a020109030b0615030c031b 73
    0x9009002004101610349100d107120300c40041581c900c0ca030641c40d0325040100c00c9448107280400040d040240042000b0090300400c02c040c0c160312103082c84000958401805800039181e080301041d00c11038030700706208003410b051000b002c81c0c407582640040941c80b5085681c0e00e107031030301241040d16119400402210500c03001075403400c0c90700c00302c80c280e0700042080b01c008030341011240e44088002201480114064214080140414084ca00d04a42303442215802c2c6410017100d004030309601da41e00301a01d040321910941c04a4003011002c81120365800401001d03009100f02c4c0c4c03d00c103400307101117090419154120414006400701000075402d83c4106140310f0300440c2400001401300303071b840c485c00401a0302c40c84d06034084410301803098980b0700c0c035040180b4140d55a200303201111009214060b601080d0318045c0c519501140c0000e8000010303440050108034040300002d0166a5400011400404910300c070b82c0c503400d00c020900c0c007540048507007010806486501032074440030351301500d0582 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 988918920 1250 988917670 988917731
    0x140c010e030307030f0216080309090703180f1a040803040b0105011707050a0c20011214040209130c090c0f020109050615060d0603050a1a0603030a0503190507080901 73
    0x4034003550110303040b80e12220340340214014241041f4040c5941d618050080002c10001c6881c0e486100070412584000391100003410b240c51101040c01251401c6007000e103410041400d060001402c140c040070300c440740288441d400f002c0801040103440d5001c2c501842c01070129240d1a03172a00015500c0c00034400038015041095030010328001d1141000701135414981c90248192041580c5644125480016040098070301c00005500d6592000140d2640101074505110400318000d0440c0d040e40d002d40083c1c001c1e15200c000a1564440d6061803c040c0e80c440e074520043c564441044000f40100c1d4400302c000381b030440c0102d920f544140540120107030040080d0255071a0701001d03042d448030444620350008000d0020f2a00020755104503401180607a000d41565034003484c006104c45c4941c495106100364010601000782c034004140c6814200070300700659680c5a02d05100c903039061421041a0640c00d150800c090280c0c000e04c00d034014000c0b54024040c49105641003040e09800d0180e500b0032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 988920170 1250 988918920 988918927
    0x1e0504080702040e01180308180a0f0b07091707061d090a1e0524031c08040201090302040c030c180e0619030c080a3c060b0607140c010e0303 62
    0x9803500d81e0000d00313030004403000040e0008049050000b41d50582c1c0302503012403841820051800c010441445040c5d0840d40540100901903403290100411300201030154900c4100203110743d40940b0030f05010f05100d00e29081202d0400024684d101031601640d0b0000d85806241860790076001004600800003c01d80740b050b58450389004010000402002402c42c54035400344051559440348900075200e0700c00d60b00304180c0c045490b61440b0400903242d8040d0340085600c041e1050b0741071085c0544a190700c2d004081d07031a00d0004032440a020342002e90f01c80c4c9081950480c1540651012080340310365242c0038000d1150915006400042d44030350078400a0388000504503203005d828603610141d000e20030440301a12030f05d507601c0c0005140c02214960f40200c11305400c1c4025105000f5030b4201c001042804038824496440d5801c0c0c0107841d030840407a41001c65020815150403504a044002d445c1c103440300d055007081070708880340c80c480d01e0050207110105581948201d1b0100720140d00500110718 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 988921420 1250 988920170 988920173
    0x121a041a0405010209150301080c0a05150c070512100c0503061c1a090708070e0403051228060906050a2405041e090e0609100c02030f0d1e05040807 65
    0x300d00c00040007168555820001c0c075807a60346413401d0031001038040c07400917100d60420301c0461074107041040d03082c85144030b410100440d130398101100c5000010703010055204e403d8000150314142e81038000c25408420100654001440029050107440300a6810301c0f010300b0502085d2b030381d0b00c0141d510076086103294100710383e1014003440f01300f4064030440c0b103030b1110822101c101024590985840b4010703003084404006243c81044800302500740c1400c0b01c40b25051075900500544603540d4980300c0b04507107100041862110828000808001541e030343c11800303078506004000d10b03090141c1e900340e510302103020900c0d09000c28180e0039500d103542010140c00c41c940c0803044425004980c9410007a04000108081d0b210070b00c6440040d100b600d4614840e81030036400400e0300e80b140622181c56001c581042544500040d90341c001703280444000840c0000340c80304034210700c26940040c115010001c2c0443c5940e080ea407050040701c081011341001d045803c00c94074103443c010354016190080c144070160 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 988922670 1250 988921420 988921463
    0x20d0f0b0106050d0b1e01050c070b07050d021e06070809150108060108161d060a0902040e0f07030203041110050c0f030904110301120b0a0605100c0506060d0b0112110307121a04 78
    0xa5060106010ad507091035543c412484543c3c4001011251078010f84001500320b82c040080b0124411450680301c54100140012651140001d05040811240e180482c83d088414840740310b0044040c86110780941e11841c101e80d0b200420721840700d003441010303c45002e510090701c000082d540f56100309503401900d061031185011000d4542941b12401d0b001c00038029040c0e100810040c020b03141000a42d25041400c80740c0c028006019a0506d401041000005429841c00171140c4d54122100041d80321005001c80e00750040000d0380c1c100b480f4080d481d041495001014243c840030498003480204085003040c0210702081c8104000c540d01d8000c440d000691308181e00f544561841d5000070301d10303540c00010302d00c1c5060031358000104580076884010b2010a00203039074880c009030b0b5080c0d0b0b56051541e50781004281481002e804c2c0000800380e074104030740365003543d0072b040303000f011034142e02c3c1c840d40c9401c1110f103044001ca0b901b0300c4945012030011040e44100d031044c1e8000311414641520f8810301d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 988923920 1250 988922670 988922677
    0xc0221031609050d03120f020c0a022101020d0501050a06020d0512090102091c02040e07050a0b0304022107061706060a0c0f0204110d060803070f020d0f0b0106050d0b1e0105 76
    0xc8091000000003c15162a10000b403280103009a44800c0000609882c1504443c45a172012105138010045044503080010b0010902503040d150035040e80c0c50145010701e1048202c20250701940001099203c28041381c2280307040e42d004449941d03201d6030b00c00003a44c0d00c1400800080228000f44000c17000044030000035607000c450b0340005850511888000b4009802d0a010b01d042080158076070020f5090170302c43c0c070b00e407144000020302445060100080b50b80c8164800c0c7c1003074a40000009085484002c02d41d0320a0845d4042602d080800710041c0b902c6110310b010f92400144417007851820100c0c1c41e90381ca40603d10207040207245c0005484100d031821129241500c590400924460060311030f44070740703140c0302c4c01c0316210741c0c0b2154808070700c500b55a2a80e0000c900f5900c02c0c814080450481e0351058030303541e8115000c880100d44c516012a00700103d00025012a610f030000181403900140103102c920300b900020007581c0e0410b002c101c0d81c42e045842e000882d0702c914059001035405100203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 988925170 1250 988923920 988923961
    0xa021204080a1712130f1506081b03070b1e04120b09011413241a0d0b01060c050703050102030a1b080f07080c090316050103050906010b030a0b011101050405010c022103 74
    0x106c1c0640c0d03c00c0d203030720071681042d400b11804a5a29882049100c805118510100d64035142000c40c280320400041c1d5640624040c0c1c0d903030300c800021b40300700700c00c090300e8081b007140c03070740180c3d540c90301d0740c40c522200240310076882542c006583c107000072640d034010701c540e16198102141c0000300d5250081c411070144103814044448111001031704071340502c404126500b80c004101c020802c105c080b0801c20800780610000c41c000c076400010a000505043c6c40641074841c2490014120091400e08170314114107a03001401c2548004144100e105c91a0480e20079949482106040605100070483d00700c54210341c0c2c010701d11f0191000c640349521444510ba00b19080401d02c40c00c040c0e01900007410221990b010f506204111300040141d1b5030103014190780b04d1034050141c4060761601040e05403512000385801c420965a219011443c1e0084e0031104414050000811451520b8641180281002c401e014007500c20080300d1001c02c3c5c0c0c08100701310410310746145c00d41107440c0c200d080705025055060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 988926420 1250 988925170 988925183
    0x403060b0d1b03260f0304020a0f030803060415060203030609060406090c0c020a0801110d0e0304030f03121a010f1101060e0c040911040b040b0a021204080a171213 72
    0x503410201e42211008001c1c0e0781d400700c0c1c40001900c0c41c60f10f0480d071080300e40e48040fa80080c41c1c00c4d0120f406401c050701d8680308555202a5240e07290f01c0014000d10071758002c1c2454008036038001c0180071202c40507602c10307041642c0c02c101c2c800202c080480b43c45501d00c540c03801680204001001070503e81315003a0004d0000d4000325100c0d4803040700106490b004c0845034002a003403402a0305524000242d440107100d882c000308007a00350010312843c04c0c4208841401159101e5201d010407903420401ca80046030841d04160541c020ba1400401c040c000614a0590070f003010044425031485440310341c00f01505840c2c0500745258010103860f03144030a06d03800350a540c0c40b14001080da03188a52a841400e014407200d80e01d9042413100c000303c0d503104540d03540c0400180410b2040d0b1a0640031a0152150044100c0d02c84102d018202d2a04403a83c003e0a0000742c081000680c900002542c1e240c241e214401910405482c019542203c0c010a1010301f40103c030038000c03c0c604c442c58542c800010740901d2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 988927670 1250 988926420 988926439
    0x2130903120203010b070b1e010b070c21050d02061603110d0603060902030609010b0a05040f0e0a08180d0f06090510020a0903020414070906050c1f06060f08010b0403060b 75
    0x19096002ca0704268050f50105a00054150030080101e0300d180d480560540e200c400c031140094503444072201409996158440010004180304580300d011009115802d040c0300f03a6402440d4000719141102022103051081c0092460b4030ba00108502d0700c94940b08542c07029200d00501e0403005400d4858010354109010054009400d80c17038060200650301850300490b80c4481d0744149031600200030801c0c2c550380d2504080251030341e5041c2c2c01c403084070001c54010840c0001828004014007400c0c8001c000d0b480b03041510300401c4402d401a1000d007070382d80c4190020380c0000d4180225000a0280142921801d540020015030180c1c4000b80c607174010b000321111060440080c00481c3e11040c40000843c10a94007001140b805c0c0c00380e603180d8001c01031900e00c03a040020700a00100300780d002e0312081c00313001701c1c5d0301070301900c10070070303540089584801c501c9003500d101c1078000140054000c180000307142e9404401002d00130f036411412604102e8140d40380c1440c0d520340400038140081059448003114 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 988928920 1250 988927670 988927697
    0x705120d15151404080c130633171308040b0a0c050c0d0203100b012601030b060a03080f301504050c0702010e0f030307050d12060302130903 62
    0x120000300540101802d900381c4001c0c11030060002c028107146203550100401050001081c041580c0a0400003506c4d07000544415200c80c202030700a581141102c0e0b2010107000d0028003540c405100d8070101c80800034107001c0050340c210b42c0361440c04000c081560341003021880780c0c42141003d8108501030b805e4a4101500e4022220b800d038441e0040c00c0c002201054480180407080c032400322184411100d20404901c40d41c082521502c41581080090f40e031880c000f00c04d40d00840754181d8841c01402d1444881c00ea242843c00300e20401c0c00141c80e07101c10000050503508054001e107041e030380c200800c01d040c03e03681c0040140552003c0c0f0180440c445c2580346003811500d1940c00b1210200c200803420592030800400048072000340c61581c403c0b4188401d02001320104011503118540a19122440401900219180c20f20b8001140d8061000180b41d40a1240c00f240e1310043d01d015549202005004440842c00e403482808082c2d80020100001c411003070260307001d00704440c441d0925003100e0684 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 988930170 1250 988928920 988928951
    0x90d0e0d05101e0c0807090b0705071703070501050609010b07140c06030a0609051b040b0a0c15020307180302030312060d050703060e0706090e07030b0310020d0618020705120d 77
    0x3d5014440d414a5040c0c1c0c5400d02c489004002c2d08414914004969250078040140001d2507031007081440c0e00e000030840c0c10700c80148007032000340040080c0405600560450103950364040d44054034254a0321000c50f13240e140210140381280c2c0b200c1d15150800f84562122000b14004000f01c000612409d205e081c41500c483c07014500c80c03c010100054076501e452000c2094610080441c680840c103c44802c03c03042c0030005850079202d0b102805512007083d10801c0d41c00201036a8040c1203c2102e9034411043c5801d600290b10806141da00c0c4003541010301c004003621002808001d5042e00184030076000511481c850350b44c420340c010039144071101070f81c0b2001d0621403260420b80d0002d4072003088403081d440c2005030500802c1c0301d182141c040c0349420180d06403100c004d000441019120f1002c40c8250350b0811064a480c40c80c243c0440d41c0380d15810001d4000c111508c10a094188000c80505691034203109030390311680c104016056902d07011a840d030090b48000140422a030b41d0306e04401500c00e8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 988931420 1250 988930170 988930181
    0x30f0d0f0512070e01091d011802040909061506140a12090b0403020106091d100c0c02150a030b0607030c060903051614011d0a0b130b07080f090d0e0d0510 68
    0x440e292004100461310005084420641001e80d4081c0d01c5016106816070001d40f00b4110390810480c03441c403105003801c1d40040e02c900e44c042c00384241454a0321091007401e03070080541c040300c0e8480c60440d0380c6e600c0c0700746c5880340b2551620440d0f100c20300080300d41601807081c808501b076081600180747d0000f42e0360040940d100785d9042d070050b95141c00512404101d84118101e40c44507518000d000c5071a0ba22403580c5500610442c040305071202e000500c510b00404a00c0740481e4020080c280c2c001540350040e031250403040d0350a000906008607140c1a00308482107805042c2c01da62080003801c0c0603100c05021702105101201000704c100b00b241d001440000d522481c89101e0101d10400990020b8140c2c00d5030781c03500b40131040f401115600c480c0d902e80068284115540450030840300d0713903a00796440d1640d05011000c0c0c501c0110208100c0075a600031a0349101c0c9840c5900c0c0251038941000e050307690011540780303901180c1013103030064152802190082d011840f610854a00000c40d550503400e40c1d2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 988932670 1250 988931420 988931431
    0xc0306110d1a04050a1503080d0f06031401050106180e040c08011d151614040f0605091e030622020607230f0705040b010309021518030f0d0f0512 64
    0xc8200b0202c402c924041c0121a006412a10184001c00c00d14160380c1c1c400001344002001480c0009103d02440c02940100342040d041c0c0108202856580c1880100108044140c980301d51810700041140380c020038590481d40440c500c1740b0451030620810000100d005802968082c02440300059021000d004042c4142c0d440004090031440e00540c05181c102c03e001060000030b151002c00c014000445034015003a0401d00c0c02ca15840c100e454403080328400d0390014000224240c0000c985140c001e0010140c01c0700c292014107050b035010007540c00c110346211510b98590401004224850540b00d48200d000d04860138178515488142d0000320aa407000030229016139042e02e030030803803103020f503005d10300b00d01040701a1045210340001c20f0707201c0c0e04601616110349d50f5400e51070002e9100358008124550301500003800000d1882c400251900840d010440348821100c00032241d0801040307003580e000c60301e0b00500019543c0740040d1901021084108200001400403c82038543d03030b10614002c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 988933920 1250 988932670 988932701
    0x10e0103201b01020304020f060306010c08071a0c071101051321030e01211e02070615050402090102030f160f06230105010e01120e1b03070f030c0306110d 68
    0x51503a00780b280700d00038540c8284051a4410310030040503031212130b84003040b00b0f002ca451035a00d87d40c001c0180e407003800c0420003a00ca554007207502c034101b200321030075468031091940c1c4400855880034848034181c81512402811000c50740e0880310954041d4000d0b0229080c0168bd095940742c45521151400c0501c5006c651201c04100021007415007001d10078610702020310305900d00c400143c074000303035049a440041d5402540d8038006040548200380c0c4101c2c1c1c4c0d00703090081d0b503200030508060014041403e0410482d081b44a4005058030307051017280e007901e40c1a0007440c10540340d4100c94185405c1002c440041030409524100002d80c4c4100030401e50b48104800500b280c0a40040a0749425815108900600384c40042c4500d03070b000700000003070023801d28283c524004040b29446c082e11550405030410320503800e41d1414481c001c00040b21313028003a4100c460300d41e5110180c928800031880007400000010000b0320101d00d182e08000d8000821a072583d1800781141644000c4440611451a02c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 988935170 1250 988933920 988933927
    0x30f11010f2c06270109120203130f050a3312050a05100905040f02120706023a0302040503070603090615031515050d2907080402010e010320 62
    0x12044040a800b0a15403070b00080043c0d1078054450040a484450780350b9040c03290610480c25003034250044080c07030fa801014203161602040020b9902d8114503084840d1038074080740425079000403006203086807802000900d034246440c90b614580480340f5581302c58460054844940d0b8402d06002d0075004903682c0e034054404840c6400d2204483c8007400903c4402c0c2048140308407010340c03a8410381940c01340c0f10002403940b21442d110f205940c0d8154020342122a40c50f4910035040e010506d2803c0b40c0d441d03000e0310080031590708110032603580c41c1000203c69461030b0129581c0e079080c4101e41407088150038014034103034075080024a088074640c02100002e032164044c0e020050540620f54042e204420032201150555440700446260b42c081003126035610310441c00d06c0c1d414002800002c0030081c094188101c61070405148542500c1c410140329004440305504000840301414802e80d604d075a5000c080e2030f6640110b5a006841ca400380c1015200c2d150b00c100134850403a060140c04484c8400da98 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 988936420 1250 988935170 988935221
    0x70b03012904030f0b060d0b1f1707031b0b0c061b0a140d02040b0301090501090e07060e0d1a090d03060801111b0a0b01090b091003030f11010f 63
    0x1003244a4144640030141c00344020000030b14482d410045040c1d1000840c034aa07514900414141030510901924501d02407052020142125045005170420300e0020038000792a80301c004006500d0700043c42c2d05600c181000c002050f08c0e0ba41181c08415050b8404203c1585c0e0351100c640750304035103488405e03504039400b072144c03103496140044c03032089079140c02c0f904080b001d2401601103005902c820028940004001c3e0104200d82e046030007502c1406285512542c40d8910140204400d0050b0f8207440c1c50030740b1100200100240c048121540ca580d00684000c40c0c00501008103407490741290401e2034100c14440d508518291a446040701200429450110400080a4920550200d24543d1405103076442841710f620490f2028402280a81c1c00d50030100222484c111081c60040d02c000110070011841c0070740c503007260f036202100301c950901549415844200303030501c6100080c01f040e803411580c11028028010343c01c99036400300000500c400c0d110400d000381e50700443e895203404484101c17001d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 988937670 1250 988936420 988936469
    0x307050c0a03080a0c080405060f06010e03070920070b160e040c0c03090b0f0d020c07080f0d0e04060e131a011203031b0c171306051c050702061602070b0301 69
    0x40545c81c5e034039041c021802c0644504d034a07054007421340002c4103007041c00901141d018202041703081c24003900715034070150b403442c1c43c400074000d140400c1152a01c50094190100d10402500e03501500701c1d92600007902c8044c040d800004a0b01001400e0003941c0714010aa580c1d64800c1480901007a150700c012108246002003000c145038201660b210781c04d224070680c4011a1098451100d203130440140d43c0d010402d84145003001d0b50f4412200e03885000403410503140d01113800d05181c03116032540714200302010100f000b030f15940d006981d00c0d00b501c0c2e0002003840d40c00409490b01303e0300400b50405d084880f410580d041da90242c210140c03501e642c5c00030008041d071511030003880d06500707404408450040480204030414003100600048958480c2e03100c4101610102c900703040d40d844c4503800159035010080c145400c00b80484d048800520310380803000e1554041d041c407940d0a640a461140e9030fa0006240c2c0c0d031205400318046100340398011031280705c00c1000714041c10181c100130340744140b45140071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 988938920 1250 988937670 988937681
    0x5061b0a060f0b2805040b0f0402041d16020312070c1704080c011106010b0f1b0c010f030e062418180d021f0b030a030e13090201050d020307050c0a03080a 68
    0x1100399807a501484d50b060109039510a0548030200c4020542c0f060007400140c50741e180d962441c0d03000d0710000b800240c055840007403c8280c000076080c5407442e901c050b40c0f1074045100c0d130380c2d040140c1c000b0455424030001c034088042d40181d940c01c3c421511022900d8040d4191041d503503101486400213024402000208031840201809103003218081707405010082d00c8a9041c410300141c440045013040c1280401c4096440704542040034845030b582c1800c981d650707070805801d42070114180d0300701c04002611030b0040440e011a810001c140c81e4840c05103002415018100f0b510031002c1c144503805071a034400c4031002881296445500c0790b801c00760143e444201f03d0180c0c250440d0700c2450401c440e9500070450340303002c448140100401400107205400945492440a50316025500c2c0020405811212040010109580c14041c200c00451018116030300d40030080c1c0400c0d810f1000105041d80782d0001c581c00540380c500a801e24803410402442d1002503041200850000e500700009182d562042 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 988940170 1250 988938920 988938949
    0x60105030613020f0d08091e090a020f12070302090d082101031e1e05030c010e0309030309150903010c0527090604180c080706090503030405061b0a060f0b 68
    0x619001d1122540051000c0704007802c5203001d00c50701301401c800e00c449182910802c0034041c14400041d8a078403451034907d080003291600c5000e469002c03580d08074ac07510a0301e0f45c04000a4025150000c04c0c006042c0c040380c0141541e0801d602088580e50030345496085146a0340324145041d240c0c841101100303a10781c0f064807013031800d203500801080850648140b0a218004020b4001900c101c02d0921001d251001070f50001407440c60002c2004100c000070091074041444402081750202050003d912032080c2e1b24000e601d0f1b4002d00030760086103040312116000c0c2401401c0e8619140300c94001c0780c00d413444804011b0100c2e101042105010b25644206c000004004228541801c01e810004029280140c01c09002d07130756035171613103c0c040561030150040c281c06c892a0540f03255510b08a540c1c03034025001d400b000640200c400034143c01c00000b52020750324002e207124208071205d100302c1079032032054480e0045442804500e1010a1447c40307076408540b038803400072541c504208144542400f401c0c65 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 988941420 1250 988940170 988940191
    0xc09080309030d0c080d02040e04020f01113a2a020a0608090a052505093d030804060e0102060411150708030c0702030106080a0812070504170601050306 67
    0x561103041c1ea002c100021031043d07070300307004003200c0050034400c0ba540101d045d8080940c1c030018011518203001d040c90342c03013248200c40711501c1c44505030045814610004030141e050380b14400b6100c2c01504090712440803030003000c5180240904c10f0f1f080180c42204000b03100456540000945104807a2020900aa0f40043d2400081c038031503003c034128090038400d403400c201c00e000100e00f034030303405001c0c4000c2c1c40d4008048401c07001350a58044828202906401d035183c402090014040c180180260720030781c10385c840a9081e860040f8080507040080103400c400c03130fa81c061040310003003290b0840009503006124103a1600e05004000c4c0268401080c00e50655111600b00800101008a10030380c01100741c600c04200f110070030607004507026919006100c4440401004050b5640034090801c40c0d000b10b0090142c1580d4104060300d07020300c0c140241c007020702000032102c45012008016006401890241c0c50a075035840200000420484021307441d40020f40108120f00d001c124a58110a2001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 988942670 1250 988941420 988941427
    0xc22050f030f10090804081b01030605040e0a02040b03070f0f090507170402120c0402070b09060a020c0a0305030403140a021b2710030209270307110f0d0210030c090803 74
    0x1a0740750340c40403409003900c3c4107a181c095120804c00e0480c2918010401031086450300b0444c001c8450400303940880c1580068501302000507946058018042c000b8110006041c0456058086c403000d008a650785980511846100086640e01c2450280091245002c0d2560755410003d003001964000b9003100b0801c5440341c420507000d045450a640c1140d8121500c0190100201d403c0d4149440d20508980c060b1010607040c06000c0c403c200d161046440d00140c44441e80d034001014124000d00f0b6003009268003e43c001d100003401607000b15000350003410402030b1040c40010384001640600895401070b0030400075414807402031805040c42071021205050040d580b011480c0405000c80380c441c901540784000700f1800c3c50034000740340103984c0140103422146480d03244450720700d0800c0c1c042030000326004c0c0702c4002ca0101100361210203910402e04480d140c122401c0004401035140c0c1c0a61220008085000680d518803210041d0a540d8401103030300c4d1a02500a03040c01e0171540082410781040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 988943920 1250 988942670 988942693
    0x16020f22180b19061e0617100308030903070519060c030603020306070521150108011221020c03010f0b01090506031009022a100f021305090c22050f03 66
    0x851641da4401c4190740420f190030f050503501c1c8080c0004c2c0c0e120380b146840340c1108405405003c5040340540300350f070312510700b86914080340c0240307680211040c0c4000d06000d00c090002a920000843e04800601c0860b42400d410391180d0b410480c07011040d1940d418440104420000c0300e009068240c801170408010036132850300400d4460340014074160411500003080c88078011504c000c0e8448000c54262103000d0700d0140e0b402002c1000d168840350100d40b0040000039106818a481482c896018444030310205034041c0401e41075103800032117429130045450501ea252824880c0000358107a034031010035056400e0002401d042440d420042c010802081000310403048615040200c900346040140c2d5841d01807030781c442202012001c410112455030b84a21507010000703042c00c46105000e0100701116525003200201e12a2031501800c020801c1c00400032031400e0310303502c0c1d40b11040c1042945445080c40c00da8501c403031681c103c41c1042c007002c80309101c2410b1a0b10000058001500242800703c00d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 988945170 1250 988943920 988943933
    0x14030906060f040f1d01051f0303120e0102120f06030d0c0f03031107080a17070c03080603012003100501020307030c120c0c0308030f06060f16020f2218 67
    0x800460181c09a218450201c3c0ca40750310000c4070040d11303c410429215101c0b070030300600d04c9410143d8082d6080c500410101c1d045e01640001039191300d00041403c503e10769054031890300d902d5114107540e0351001c0c80018548280000d1007449011a044a901d10b881c0040007003000f80580154040d0388058414040c0a030031a28010b00305400c01310f00895040c0c1d620303080b005410300c1c921a089074800818018104450315024140e9030303005031684006044a05011120035070b080341c104000425071003010f070100e4001e031510b03904610050004914a0300b0324210035035900540300c0c902d44c8082c0002c02c222200042c441d00001030002480618900781e01620024156081c4180240c1040114800b83c0007040c01601c040c10510361000701c906840d035403070500b10b110780c004580101e1560500e8001a000e40b0303102d42100c409131454142c003414991803c80703403500d01c07594800c01c81c0c0101e2402c4148050380d886240d005000c41e000d0103420a2002500706000a90326040f1800f090481c40300b2042000944 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 988946420 1250 988945170 988945183
    0x73b1614120a0b03070e16080712051e0907030c050a030b0c0f0c1221190c0905040e070618050a05060702062215140a080402120715140309 61
    0x240d00d40940c09442e103401201c002c0502034841581885081c0c03001a10900d03000c0320b50301c1851a0505c180e0704c0c0705200420b0324207007800c440d2840003807511280601100056804190001d00c903500f00031f01200800a1403041e16016222140350390320410081007007141d486908805058180d0b40000c042c1c1c907540e620309200001910007400e210010401e0403031f511816040d03d4400141000302c40c1c070515082c1680c0b000707902c0643c00d000b6002c1e14020804400920740c00190144150107021a12480900315400c01404100c2e1140f0030000710030000140c80d5160300070704801d88034080260180394505807001c1c040700c2d0090700550070144034000800507682c81c2040801254400d80702d060340c0300541d03c001009803259500034041c442c007103210701d46400306500c4d030700c400c1c2e480d2968003914040101c5010364034001a034840d103004003c100300c0340b0041849000402d401c54805040304050982c020071590501400d908801000380040b02a060003580c010651150074003141d40c1e61380b55041090f4260b1f100c90 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 988947670 1250 988946420 988946437
    0x405040c17060f030a1709090601170606030703140c0c0706020a03050910050d050a06050f06091c050304080706020c01080c0403020f09040312110d0b010201050108073b1614 76
    0xc100072000f041a440a2115000d50382c0c4c00441a0b281010a6552040c60740240c54418003c411140006000354052400e054460201300350406850303443c40c0030040d007988010010010103031502d11241580c035800364064001c1000101c0ba46d220a5201030552400d51564800e804640c809020080825048012034801c0103060300c4100b046410114191082e108010b600070810b40350a00b0040088191381c0320f0005e5a00440b50f214110079180d080010754042c40341e2241d4040c0c885050318810a09200c81030120f2440f400c243c90406030781e1810141842c2d21580318a0141c0c0155480100542c8d02540c9070f0b134081d40381c1c2a00c80c00c183c21600401d5030000580c0b00503004c5e452010100c2d05050050092072003040359440d040c069901d00c56400449500300141402409090400e038503455801070141b9410f031000440100207540c6480c410700c0966034280e00d0b051408404905078801d002038801e80303203110860341022881c2400c4c0503a050f1108000340e07007400100242c49401000c80314001d4119032000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 988948920 1250 988947670 988947679
    0xd09050d081e0c0c01020615150304020d05030f0d051317090310061403060609060343030201020c0406060f0e060f0a0e0109120b0a052a0405040c1706 66
    0x142c41c60700184400411101c030315000b40c2c4000c9014030031040000784c202d80c501d50a0f03007a16166201c00101d520340a0040c0300c5507500070046684192440d4154000e15403090000b05054450b030210303141c16007558000d8119402118000840b0080240103004158101541c0340b035100c06e080b66a200c0714540301d44849100c1982e000060803590654042110a858122880b0100038090755110900709042000300b00c2c2b400303802880002001ea1400024052003240301a000c2d002c00001018120808105807004603402c0d003402c114120001d00e0b5003d80340421842d0315105210b5815800064602159518820f00c0b0303a042030400c0c4541c0780e100c4032000581c02203050404800f581c000000307101d4003c0c8020040c1140d8086440121f40f503024030341c03a440200030381340c50030140d403144084880c1c400001005003810440c034000c80c1f6940301a900c40d0b980100d0040c0b10a01809035540080c1700300380c03e074540035283c5101107414800c505d01032040c015801c80600309280b0034110203441e001c2c90305000b44901d104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 988950170 1250 988948920 988948927
    0x51002030402011e021b03010501080705010c15090516090203190b0d1b0603150605031603020d050f0a180c0e04080408060708010617270c0301020703110d09050d08 72
    0x1c590082c4507901460014551368003024043c03000007540c0301b090101e040ca04a188140b00d840ea81811f1043c9810384001202808902c0d0505006480011081c1000c4468807628900d0704066040d900c07440600c1d51240e00070b00901c2e00c900d1030440310701c0200d4201c0d00005204105005116030b50318038280000000c25400700c0c03008002400070f0460900e4142c0580104a020782860303e0f515010111000e07900303242ca080040801044280181142074010300c4003184080003c80c440b5000c9001801420300d080c07901610300709641c28204281d550a0700c10000e414400c01c2842846907130307401140c4017403107180021503420b2942e44640c24400000e200c0c01264400ca01d02240502400346c0c1220003a1030b030b01c0102c030900e0500034401080903e00340b09040000e00c0c1c804201421321140300400d40910440030018201003409855140144c694010908041c0300d03140e506a07040e1028005407048034002e845401818881184a500b0701c2440806241001346802d82403280e0f83c0c41c0a0140900c0b038000d4042c1e500d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 988951420 1250 988950170 988950173
    0x506041103160e120a02240f0d2009030c040e0a021c0503030106020d0e03162102040507021f050108060106050d02070c0b1c05060a1203030906020a0302070507120510020304 76
    0xb07491601800143c0c104d00b450f251444158000164204040d1084da041e00d501d000c0008040d40d04a00100c91400c03444081201a2444510078060700c105c083c0190002030403440044074801c94582848209184032001c00c00c1581c5160034440040c4003007094806001e050507504c60702d80c440070400310007807050380240b58800130702b824000140c02c401d600a080341e0750f9584406020703640e8a10381020300001040c0741400134650501080382054504a103071295005403d000319200d00d9002c03c00d5010034420020036440142c2d03070303902407640520340c1a0040c109403030303040086031156503506402ea07a090307043c180104542907000442071304490051a142d0f8440841301c4550b0b019225020018045903c005e4012030704030080b600401c0000e0103503104040628004031844141c0c0c2046410342d43c0403600020412441c1510345012001d03038403e140001c1e4a135984c0da80d15003240c118010480c00079902080e40c500b002410480007005d44141d10000701e82c807900d503481c169150b00c0c500ba004074550300800402c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 988952670 1250 988951420 988951427
    0x1091716020a1d090d020d08070c05152707090b0a08010903050a1e14131d01060f022e020903010f1e060612091b031203050604110316 59
    0x8503a0041400d880aa941c03520082c000e010303500a10500f072801c03000b0070800c010000c0d40c040c03079916030f8015018160b8000c100350750540d401460720050080035202c00002131002c0c40542008074642040045c2d60074401c2c0210b0a01c00351016402805030000ca018502c13150001f2000122002d016000c0b0724007440c5404a0700f01249980701005039802d02c51040300700354105014104c681006d40d01e0013450110030203000000c124101100e40440e5941400b0840e01c07240c08002c1003c081120500004c0503920701694000e056000070340001044130b1801031140a500c500c0041c920266440101400150401250700307603842d0017103501d8120049064007035042d25030b4042c6c0300303100c400a0007080545184070301100500002642c01940c44000340c8040c0c1c1c10359003845001c1c01c1e0f0f0748030750303941e4682c00c13500e01d900000b00010f000651382140c01e03003426a1500d4803001d4000c0039510030a10707180c001c0e09504025040d10390103040b00d40701b141800c0c00508580c1840702641c1d80a0080101144901c0c541074059 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 988953920 1250 988952670 988952707
    0x5030c0306031c05090f150904050a0209060c1b01050307050f0a020c0406030308040c2301050d020c0105040f170328060830030108030313051c0c030f02010917 70
    0x1101c012200f2003032a0071254002c4080c02d0481000e42d5560b09030070403001002924582c45000c0c100b42d007001c0c05800d0b801e060541c00341d0b07405000100300501c0d0001c41c900184250b041841447c1490b80900102c0e9000041d090750040c50351000e003400780c10340c10302c0403001c5e04a020740c071100340f10403001041c003400552080214a049050160040198680f079040003015103608031026140181c2603000020320311100c80c0c81165461130035a4070001d1900c41d00044456600903c14900c905400344281c2c401110284103140c0a00e100b5030107442c0c0d21007185860045e201c40e00501d41007084040c800c22829102c240b4103e00f80c43c10104002454060302e9448100405250304103200c9481205c1c0c05042529101c05000c08900640c02e101c03d000d1920400140c0c644001d0107564071b00d8100f40301007400301007848004c1400a1140d8281c98040480b40d140c0b9485c050001095400a04010101418103800c07082c1050a105944020b101803003e41d260403294610150700c101c04d4443c00038100c1d00a42140300d01c13 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 988955170 1250 988953920 988953943
    0x304021c151d0a0c050d080d0501060504050319050601030209042604050112020408100221071d040e0616110106080c18041a1b030f10120305030c030603 67
    0xc0708840d40d003690100e00030301040282220403400141c200085100010b007007040d40e903100c0c01c816409401c01044c442c02151040c01111500c1d0140b04a018001c4c4034000d103400381050b07540e92a1524a0507040602d04520040d2038112a200c11107190007260003c900c550540f6015150010961514500a080d000d40010425a007186110021010980c420002c0007120800d0741d900c5003520801513403030f040f40324500c200001980045406c82681c4400d4000d0a800701980841641000c0c039030a011003055422078030034001856030556264950600c2a500220307140568040240010607105941c3e94000646400801100c0710101c060540c031940300c0c1c0e090241d0307500003405800e41d0b500c00507030b9803000c0403c1d1a101328188a2417502454440c1036003441190840c09031000d140c0842d4031401203000c0900b07100e8104400101801100940000039809442c180c2520403903481d14402d803061008458000a071015051107035980466400f0050742c0d04480710503032080c0d03652074040020b4a480020000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 988956420 1250 988955170 988955183
    0x506040605040311070f0e0402030f060106030b150405010f030f0204080d080103021302030723090d14150603030a1223040606051f11010b04180312050c0304021c 71
    0x412080240a03005140100e01c43d07220000ca010f1180c1460b40c84040c0c034000c2c0c40d030758000c9607010450248039120030340d00240003a05903420a561911620f08143d401d070003030f0000c207071100d00c65072032801c050905014411862400c241002d08110009200a44401614041644074120141241c0580d4100d90040c07003200111090034404a001404401c824030080c0d21604040d8901b4020480300d0080700e12030015035030b40304e030400421070b000444002c10184140148105110284582d00c03154041c00c15207008550214100c03071400b8807140703410400581414011041c81c14040c8a0314008150341d90142d250600d606042014103100d0018121441411a130500c840701031140701034810261405507019500c00d02c6142d0301c940500c00c1e8500c14001d40704001816134154002203100710b501030240c03000c90780042540100c90000806039141c199101d154075034140307444810180c004125103a00c044421090200f403a2030f1040448078000140040e0107480c075000081c1004400c080c11100155110b035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 988957670 1250 988956420 988956433
    0x71e0201060518010815040f081c0c0c20120304060c14010509030f070302012406090905010b0d0b01020331120b010315021e0a0e06040f03020904030c05 67
    0x5000a01804092003481d004020705208904541c01c0035003194140c1e040c4e071000b401c0c0355042c3c034207501c980000180709441003003812030704400040e60000241815211703850300c01ca8030102034503543c0c01c071b5100700180c1e001e1041008450000940c0b448105001c50040c48890320140c4626010560b20b07000280e100415020005001c02c1031034014510a80709400b82070400d0b240044605040c0c01c80e8030a60703180a10f0f510038010b00852886610040c104c03e0300c207100120b01e44125244c000c600d503900c564848001440c00f4800d020084d07204020600814200c04280506e5140110540c0e0b9403103110401c10380e090b11801d1840c126402001101c0410011000c202825071810340000405505110750100082d000a00012082d0000c02079006450700100f1030810b80e4616696496045c0c410b041c40e5407026000d116502c00500d0b040c1c040d44001c51034640080e035400302c60a00a00d801c0e56403024034802c10b010b00045c000480503044050070390303034140c0704e102003a03c44c0c4c10165210440550001c142e4407461 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 988958920 1250 988957670 988957727
    0x1d060906040e01060b120f070e0405131208060112020a050906070507050a060801030b0c0f0904050a0b12030315040c0c080903070b030115020f06150108150405040c0e10050a050103020307 82
    0x70740144144014035046008507120035118405d01f00007551250300103081145002090701d0554031136a000460001e00f901c21180d00e94482c0c0e003000010519001142245c0100022560010440d4070115405c0300c0c01c52916a0019024090b4020403514500071480410780004020081041d03a029090003001450450381e108001071054409020464190303c0000c0401c1281500a007616002d404003160b040c1000049020b020041c00001d100010403a1106148603581d00c1d42400c160021003000e0184d960b900c0d2600c4c0003074182101d01a10341c0580d1404240f8940d0399880000348030140d5000001da40d42d01403100000c0c1c40c06405030800c1c00704410000c00080e40e107800c0c03d50b60740c10040311b809443ca42034809103802e031034410031550302a0303846040040610544c03140f02c40580c0020508644c00c2c000914102103021a502140c0c00c032012050a00180080d4811142c0c1a9028103a200300c04955070914020407100b40c6c15100b42c0341403540200200b481c15020701c11124488880b441c503080040c156 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 988960170 1250 988958920 988958939
    0x3050906160e1831030e0d0203120a020109060b12060613060b2a0c060301181113050a080a02010f0e0f0301090b07031401050d02100513030c030c1d060906040e0106 72
    0xa03803070310301c0704130311140c000f0860350188036128480c54143e117842c400103080800303101781c0d82129041280d15018814070012403181a5000c0c0012501503800064083c200745003020448a010740204d102d800c500c804521445000038005a102c902aa9102c2821107010a000f01501300c0750000b946000002c80c6001041101010000e850340c440c480141d03810114405a035204c40c01c010f12550450010801030098031445181900244c0703001d000061200340e5200140c44540004143c0000c1c600021003c02c40b500c1c12050040c043e00140700a403e10500d80d5001030072104d01000c0040900c61400d507251520342c1e5140d9090030f4884082e000380070740f030540d2400c03244030f180456140c40444e180c81e0196410f80001c80f51603060340d00142041c2c00420045c3c00b040070344c1c42c0c01d0001604002c0100469034041105400140c002c6104407101d1081ea0301754545041041d84c1d0750801b260f8448040500c9e0002c07044094800d402103425200607007142c45120224010302030034286401e1541c24142c000486c182e9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 988961420 1250 988960170 988960201
    0x20a0513030318060813030e011b081917070f11030a03050a060902090307050f1c0c06030f0e03120c040b04060e0307060f1d0a0905041203050906160e18 67
    0xc0c03c1900f41a42038a1321015215108190350711000003401d4615180000d014503c1908181c030305040c02681110000d564036007440103139404440171080865001011111641c622013031540781c1c00d01600700303114503c4600d040b5000601900421462071003610780c00e401040a0120f4100341d030300340c80d40d50000e6003001d000380c0415500700c00341034603114000071203a500c1d109540d05003000801401c0c402e85803808000842003140046544038041180c074544846030143c9403038400d48034a614a00c2c1d185001800307412a08142003d0030103a040490105203071002004982c81a007058081c1e403581e496195500340140940e4011000041340098042001a0040c8802035401011003c0b03842058982c101120074032085500d8101107585c0380e2008582c084404080c0b52010000380900000a60b9802c0349415500181c0c2c0544040c1c00301a0031101042d410300600d41c1c49050034008012908080703860750340500185082c0420802d42c12a40d0307004c0d603601c0003d4200c90b0b403190011029400d1100c0680703507101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 988962670 1250 988961420 988961447
    0x20d0c02011b110a082101060f080c04031716050d030f051803120705070f030509100804051e0307081b07080d0504050f030a0c03050c180606040306020a05130303 71
    0xd00802c0e207140c8407403003000c408201003c00c01c007034000b03110355a4804078150002e01445003c0c85c000580300d0204641d080d03260340240754a0303640e90140e0078810070143c40300c80041c0080a0701c6d88100f0040c00071800d00b139044200320070525603943d6035003690b442d440a140040c82005203a0301a1200d001000765042d04002907608810f2810081901d034440c02c0302e0b01003401d1100c3c014a800c280640b050140903004465480881030038568a0003400755a61102a0301d100e500b200404c60104158445003041d0710058409065800c2040319800c05844907656a4050998036112440d0055901da4840e018000d40e2052984640400d0b11a2410400100349801c4000962400d12400703000150b072000010344125040407070307241d80789003909000610010f455000301c5144c0500c03030705d144c010000c3c0b40c04042000a6004001078026100c514042010042d1030840c40700107011410705000c2c1541c2c0b000d080b241101e501103001656412078500c00e5480d8000c00e901400d0200600d24000140750700082d0f07002100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 988963920 1250 988962670 988962701
    0xc0f020f0901030803242b0516060908032b060e04142103070e01050c1e070503031e0a03063602071e06020d0c030b150906070f06020d0c0201 62
    0x515841b4004070118442c801d00784c0c8405150300c440c20741a8045c5031034480200e44c00401c024048651129072402c88514200824014491820090b9a40c804040006842c0040207075140941064600885030312070f074a00340703290300d0f04024403da4460390740c00b40b4010070010b211441c0364130b4581404587c0009040402616004200414010000d418401401a1030b0825681c0c20341e02c03100401c84131804040013041c10700c8400c101040d884c00c42041849003001c22034011000300f11a10036100c0c00c0c03c015034081806903005001003a15070031403082c070f1408050b400054039141c5280342d00850240070f00d03a029405801c1102180211000d0300a490301c844003440c0c20f6400c030000384c6071190040340314000000d480c4a152901c400240c682c070200c0c2c6c4000a0080b4800b60500045940d400d0440703c1c40d0508030702103a070710510403100d41443c0c807a121a11141055440c10000c00c000813a000e8031443c00004e201182d8501c0c0907003000f8041d41a2213009400703034410051041c0e850700284c001e001e440181243c1c0d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 988965170 1250 988963920 988963951
    0x219030c140304230a0e19020a02120c251a0d020708040e1605070b13240b0333100806040b0103031701180e07030539010c0f020f0901030803 62
    0x8040344043c6d4039000b501c2c0756030718241e5800803180c910020b4009585110840c0900c03500c02400050907400b03402036032420005480a212008410344440c0310b1035407140e0070601429010856480704440f1490440114500d01d6038620821025000910809030006c101c1a8041408209914074200300c622500c50818500080c00304240d0a540a000e41b800040401c0c41000000c0c03d01c001e41e446140d009440b070994030034110548026480d0404081d424061402d503507824240191404106041d09480200c8940000c0b0b01410040e03411440220303182600d0003421000315126110954200006101450030307220681014a0000780501007071106400050440c65000c0d8a810b840305214101c40c420441c00d5684604180c010300506112580209a406100d100101141091140452444011036040102e405400d001513045100b101e481d1581c0004820070105640c0040544000c00d802111108900620344002a032b20b40c8582a10b6400034010703800082000710b684007950080101103d8645c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 988966420 1250 988965170 988965179
    0x10e131512060c080f011404020a120f020d0b0f030d0e1f0206060406051906140409020d060e10080c0f060d0c0801030510020c030301031707080f03070219030c140304230a 75
    0x1117034082c005c1402031a41d90b105910149001d40c0288000f84c05405c101d0b000c081c4903004a401c440e01003c580d10501d400242c003c818000740e2182d245810021111041c580640501090b903410010074880203001a1203c2120340d0369525010300d180b110082815007510200c800c0080d04c1e0302c002c1e00c6050245003048404030340e6160901c0c00c10180c2c249000643c0c030483c54003000b219003244024899107008020000424444039500040c1507070720500c40b0100301d03149032a400d000e004c0002040a500240502400e100c504000703e003070a2444012203d2255490f00d00e0b0001d403080c41005409540149490030001105400c50342050480303004100381c440388480c0200f01e500703074070580083c1002600f04000600015540f2135a1680188907004400d050a91035595440345500005042d034070110040108819664100110301c801045032500300106550380d075001d030102c8100b150043c2007031007003000d007000d40700c1c204107907402400803501c045515401c02c210922140390480c1d8281c000c030781c40b41001c41d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 988967670 1250 988966420 988966441
    0x20d03050106050f03070f2006043309022e02100218011808010e0304030b0a203415020a02190609050318040b010e131512060c08 57
    0x144c150150016007441d640d40e90100300c600c00e08282410052203c9488001481844a4021202070100c000101910b00b0301d420300805518851030004c000e00c19500e14100c03440c00441004041040200020420f2101d82c800a44000e400415212424142000c2140b41c1d10046c013481855003419000c0e10701c101d4003003801c074050340b0078a80d04c14007400d5282c2448903a544210101d1401c0d1507151403090031151150740301400c4d244460320441880e400820244144440e000072240c0000160208009140101078201213117001818030842070800400c1e0789610b112803401701010301600301c001c1000c580c881025600102c0c07045d030042e00d03405204810707a0751045251084440f500061303001080c01c802e4241401c1c3c540c645940302100d0407a00c42c0b9561000036010000f0f061300c5101e50940c031200b560200280700c11140c40782c5005040044005415105454242c2d650362801d07051080841c075454000440c4244040076440700503800c2c0b003007403803809220080c0d00c0380610001c070b80d4400049484054004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 988968920 1250 988967670 988967677
    0x90114040f0b0a1401210c030c1e03031e1b03020105011409130b0606070602040905070f180308030621010905010b12060606071110180605120c130b0a020d0305010605 73
    0xc1003036000c000d005004a00b00c06c03c210340e0b100d8828152407051942d541d03c0710b45070780e2079900854450010079000c1c4080403000034402c211200d802903a088980c81c60300c0060807043c0035000302c1142001c0315401030b03895106440740b0700700c00c0f902c00300d1507000c20261400a00a1500740700307800041b0708801b05803c003460308002d11390003440544640c44103181c0c2520340098144014010a41c400070400c850000282d050000d000202140c907000643c2d4071b06001c1c05800241091804001c000900a280914003180c403280001d8a4202a0881d200c1e900c100104180034840500f41421220103c002c82c0700941c150040042036100d60001e000c04c5003605d050103010204420708000c20b8101e03c0010b04c0030304006020b00500f0380038900e132006400c0e5440205d50020001c1000c800050a40b00074820104070303003420000208107500d00f407458081e180b080312902d12805403008440d80e00025641600d81640c034080d602801c001da071101e54805405070701035a40c2a00c14070030f0020a05000000031003d0141c1e0a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 988970170 1250 988968920 988968941
    0x3030f1d07053c190e01030302070603110a08040303060810090c05061306051606140a110f04140307030c180506030a0f060207021807050c120301060203040b03090114040f0b0a 77
    0x240014011040c00316040c44041c003460382d030401e1040d0b10843c100485100000005e103424404641c40d9415424000d00f80505900110181403c040b0035503022a020421501c099456280c444110340380c40ca0118064841d540c4100d52500c00c80d002d0101710001c81c1d000c00c0c5201d2103125280041541d80c014002d0724040c0094920b03103003a0402e030400081d409130005010080c1d140040b247e000a89503542800c40c0c201400c00407116003814100482d01c803161141a00c01c10748041c12900340381408031100c01e140310351f000c0c2e0003c0c00f2110001c6801610100401405150701c404101c02ea1a1501d00d00c120880c074a034a000035040c10b00020468500b004903260860035008480400c00c08950b803200c0b0042d61042c28101d03040b4079050070b54504900ea004c00280144940d50321140d603888403218403482c0c0f20710a0820a4100310030401001070503000404c031421134850015080d16540c6103161030b401800d003800400d2840030004100320802420095a0040500c00d4154a16540398a01c04000701d5003c10385 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 988971420 1250 988970170 988970239
    0x608070e070306050423070e0f010c15060b19230c160b0c0714060702010c03110319080c0304020a0e100503120c0705150703030f1d0705 60
    0x34004942803555940c1c0c4070400d8107002c0b50f2996100d0204040711140d2401380b94484019200c5084104d070400180d0300080035280840c904c02043d40007902403c0c0c044429814030200c012000e003009a11071005084032070b45281084820790314042c44583e40c2c8100711601c0a0401c011070344510601600403210f00c180101070001c0c40c0350796164a000700341d2200741d05219511851284e02220b04091000b90054a688002103440e201e40381125803900c100c541040205006c4203000340d110361225001d80e0b0260341c092074402c207080c90904069030800c0022101403401d020010702444072f52a80c03039100b410007941d5551401150760304034a1a07814081510005d511040e030b100204000c021b00007406410541d5414104199030f40d4030700107490140180b45401132508041080f4843c0071041c44107400502099510961220070701c0c1c112100c41c420500024145a541c0d42854001500755000000064221291403152400d155103299200780320b104051280116080074003000c002d81d400080103020305135 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 988972670 1250 988971420 988971433
    0x1080c03151b030a020d090309090e0109030c020f0105040e0403090315060503030a1d06130504060b0301050105070305130e010e0a0606140f0304110405040f03090801020f1909081b130608 82
    0x4111024036071004d082d40813556020312051501d504103121b01c058641c4203444450130580b07881e07900815201e0210000840d64500355111000c01c3d00300300d92002003607048480c004c81401c0c0c40700599840c02030b40c000074000400b0000b00302c20140c00c014000103680c02200801c01410309010154147d400601500c0d80641040c040210b0150080c02e004c010881c0703140c08190010348400100c2c610703421031400344140c0384501000b00013500702482084081c012480c1c0c80ba26545c10900042c015200f640340080420030002000070310403403007a811101030804200145120b50b034445000b001c0403002e880f00d04009241c80000a44d81d40150b0785180d40d0f5840c0448036040c060304410000560300001c1050f0703240c071030030808080c250340e4612400c0e228900ca210340c4a401c1c4014200141020601c0d00103005607881004004403020340802550030034600c103072628000300030642d070032074a0000307907402240745125451865400c3c1c210714800c410f0360f04d02640c200344490301e840124401e5036500d11483c1c0310b0341c01c001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 988973920 1250 988972670 988972711
    0x6090d090b0307140a030b1201110a051b07030b040312050105010918020d020307030c080907060818010905060702030c2407030b2d01030b090411042301080c0315 71
    0x4a0142d9400300c00c608107200400f2413100400010391044a006000030740c1c804a440d134514002c0c1c0402040c0c50349a00800868040450360281845100811020300002090b032120100390125146c8140c1100819034180c01d640b803400d003900a405a9040300450507441038803040740403c1c85554102c540594481540d10720b0700c0900c0b01d00d41041c010918040f902000701644002d0319000841c0280001c0c0c0e80011020303c0c07458000e121280182098001d504000070401913140e11200d00c58000203c101305034010104100e803280102400300d8010014007500e41003002c5c464003c005400c1d10214001910254083c450601c5400c1c100d000d407100d4000307400000314a07000d00c071307074090006160b020300700220300c0d0500c05020040650000b1050051445030981300350659050082c03490b1604261080000c2c0d082555540d0398150050454038040c5030f607240c0c0030415410007c014004000e02d582c104e901941c4801c90700751a07030034404801e07009215980080d150340f00d03c1c9802074400d000c0703104c41102912a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 988975170 1250 988973920 988973939
    0x60f080f1311040e0610030314031504020d14130b010503071d1f030b011406030c07060f110f0c0601050904050a060c02100c0206070e010905030c060d020412050a0506090d09 76
    0xb41019580c00940d5501c40c11500d410800541c0d01910450945111107465403500600042d4410a14200107400b401407140040d801c1c80c0301c0d1066a0100d078050b84410b440d000707010051003150810450454030406015040c8025140326903400d000b004400c145070388031020f05581d0840c0b031203009002910a82c0180e0304100926000343c0021001100c0d9a5144141c1804941e0102c0d540041e0703400849031004010b00524408c040481da9019100b050451601c242000850302910101070402c0c3e0311190706030300d580015484100e50402844c02641c0321000b900311208240c100300b1054680b032140c60004a1140b40a0b43e003240709580c4000140310281b202e030390f404090610000d101c81503124001d013a00e54840d080c080d42c290502290700078009498140001840040118080f5050100c00103060080da18040341000c0003440664100e0395800c44140024000d109a502c9021a0600305c0b44001c100800403d400003202c1c000c000b102c0d07031501c0f01451181c44a200483c22000f05803440010041c9101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 988976420 1250 988975170 988975193
    0x15030f0206040e040b1e010e01170c0a090b092a0c190f02010e090405070b090a0801140103023c01180e0627060118030507060f080f13 59
    0x80500200d092036603500c000254030f6001d880443e80e01e0020400c0040c11311098408100f54407450345c03501c0655140c5030a135100e9034010301844400c00c141d0956450030350410408800500000743c070611449540d0320f9600300805041d18082d22650444001c16070b4440100406224401c1e0403022007100d0b0304801600d1110350120307042004900a0514113018048400364480070b1600510242c422081d10b8400140075290102900f84200c20079070a200c0418000100700090b9481104555612450440000e807820429800b55103103609011800660b040190b0b1034504032813098628040541c9510708600c07140103c041540c807841c04034a409a000c01141c083c2500f0b519040c1407080358103d0803a0b0040b0010a030342c001000d5a24000d09105036030600110598000c10b803403a010804560b5048900c10b8464064141410007842030140c00e4940a8070700000010760f800400c07100990317500c850140441a00c0c0c9407100208111200148141c0b1140e44100d1040801c074010104680e0b0694602e02c000c2e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 988977670 1250 988976420 988976423
    0x15010f0903050d09052e050c0106030203240708190b0414101a16060515060703110c0d0203061b2101030b0c07030914010c080a0305090d0315030f 64
    0x4201540080815420301ca07142501d1240c3d5501c01500d070801c424400512541c0486d0f4002d22243c11200c090b00c0754804544224285524215541d40c078181c2404d40541840e400203503146c040c0400c030303002c0e45212100800c541c12081901d4080303991002015036440d10102c0313610301012540070b542c0c2400ca606900596a40317000403c0050690100c1742c1c0d14a282104440c204140a030444090040107061001c480e11401e1140000386041c411b802006a038031131940000f0a0300780c0314000301310307210078803100c8164083c4042c0080ea01d42c0c1c65814000c200f1050950014078500600711501040d05001b040d80681e1600a4010503682d140c2c500c0d1600801103000341d11000d00c006200d40d920b41d8003102d07585003503612500794a0a4550450401001c3c24101404000c100700041116a0019410020329000c80d0100519285581c584200581e008102c101e401441c0382c90000b0f0007112150140d00031406950744808690f50012021401e03002c07100d03208581c1358050b0a510301000014103200341401d00c00d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 988978920 1250 988977670 988977677
    0x30804171507020a03080c0405220209030307051c02031e031f080a0c0f05180406020f301909050a0c1512060e06010c26091201020315010f 61
    0x30600e070205892042060381c0140043e0000700f0007805065000100d1600000094800b919061a10000a03000701c3e5507096140014128280d400b5481d00710350650f02c40103230140c2500c0e03031403030b07907180c80d070789480441803d07400201d19180b141c8006840001035480c0741e0003180b100320b85410022a0340003103410081c1081e0034000e0003407001c1101144001c40f20000c00c40f803001804c0403a07091a01810400c09078001804845000d1820001c0c0c0d40c0b030226035800092844615280350b00c9500340701010f4440c0248034501440700061005206410400d41e60580011000415038403088000c1c0b4104410190740038814148200481c0031094460b0380880c904621650445030b81d13200643e5540350030038195102e1a1080e429240d58130803103810046143c08594103110401c1360500b4001003019010000e48141d041114091034078080203070308426420031120b80d0b44010001c0d2280e1034120002c0d03001c2c00c0c0c1c55004106e090300480d8214014020b4030300500e42c403503030a96002140e400460314103880000203002c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 988980170 1250 988978920 988978933
    0x1b03050618011d18070603060602010b1203070201140d0603050c10080f041704090e210f04140409061b0e0f031908041502010b0406060c080d0b130c050309060a050103080417 76
    0x103c0d07010400300c0c0040040d1f8601081c83c078a0000301070308646100300d6042c054045118030600d03c010110890b8403a40d42400d11200100c20001c032903819003d190084c025036480c0030004001d1204c0000d1014541d9000c0321000390140d40000115448881603c0b4186030010b050301280001e82481144e2403a0400303da900e90a05903600140e900b943ca40d8015024a500701080051251022011030a002c10410758907a00d49451700c00c5400039441184140b0001c04c52200c1041120340d11500800106034010700c1c21b0189422004801c4140c0084110304404283c400b104408241018500006001c0c00280580b004854000d04030846088002e02100c1c0d00d0020040840d440c5c1119009801102c540c2d4000103205e00d81c1418031080b00c18681000060001113280304000821003011a180b08414120115400001da0003244889080d0241c9238001c030704046031103c110b648540558424961102211015203400d0880801c42c0c40c2804040c02d01c400c200424420880591400c1c400c00300308208031040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 988981420 1250 988980170 988980211
    0x60905030904020f07110f0a1a0d0617101803110127110409122303071d1002120c0705041407170f1503011b03050618011d 54
    0x80b41c1c06114600030114011850900340454840304011708a0192100c007443c408070070004050b142319110706d092113403400d107440340c0d00040750040d29070400345520184180b0f52140403280808142d50303040700c2a4810100301c0000c8181602031030302400e240c00b0030040c03041403d440880e4a9480b4981080c8a50740b02ca403101d1001c081c40303000f1340003818180702c0031702a00940c1c0703068042c42038801e141502c00d90400b81c0c0c260100c3c01100400380c0c3c8044606120004540e0010591110025101c000d80c07442404010040c12076045031701034260480100c404039061040d0000c000b0102c041c4064200140e01c030441d10304c03401a40400814100c0152400c03190910364550006d016103c0c0a1102415402d04006001500e500800324052010b40000007668504d070182e665000c94800900c1d48692512500d01407403142c40a44c09030040c800e1004184500b2018010302801504043d124140940b2001402c1d0b81c82c2505154030301e060780c050540c035420080b0341100c0d40c11a8800904200341380d1003148207208 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 988982670 1250 988981420 988981429
    0x25120207200117040305121305070308030703060807030f0b0601140a020106180921050d02180a0b0a0804020f0a120506040209180a02150f0a0c060b0d0f0609050309 72
    0x408140407480c091041018900040210a107010b82c2e0180311003540a010000c1e4102c0161074580c0300e40182c546003552403d000c1480020340d8000a89a03000f825008000e00c1008801903100e0300080e00c0500c14940d850b0213907955030746a44805800e09803c9148280056404103006400c948145011022142c2c060700724811540903841940250303541c0e41e010440107080401c0000403061190742001300c3e55142e111080c205100081c614982519000c0c804401c5006409441481d040004115110340740c1030482c200000103103c0d114800d0040590002e0f03011203260071180b0303101460355081c0c0b2a44407582070002000000070200e9125080101c0403400e00040c00b5020b03041c1c1d0080008280e00d06003401402210500501008034890219008240d642c100090f0880761a606440d0800380c20002c040680795806140710b9041c80d040d0010f03448003a280d1180c107030502c0c41d0103050100141034000c02006812402a01e006014040b5200c00e0340c042a401d500c280a680c3c060400c0c0c903d00b030314810000703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 988983920 1250 988982670 988982693
    0x21010b03030414030c0607020d060b12030403030905130504150e07030f110103050a1a06180a180c050405100f0216060c05071211060304211725120207 66
    0x150441006011804584d1604000311480c040064903e20324080342a008589001e9a4000c0509469101d40301c0c06800d03101c0701c01d500c0c00c40e21407105903511603451b031030020881d80b8948030307a902c240c00700c1c0c81d6161450030b00d20455000e5544045a036030141c482d01200307005085141240c1c0c4950040a01c008085808007921110f079621401446800c80c400400150403241e024010201c020b2900c104031460003d4051048569842110156140e82141444401d00c154542e4200c0d00258015800510100303203540b0b40c80380c0d40510b142400f0070084407400b102d590089104d01640155050701c0c0c0c418540c042c03400c0607001c107118070503520003020700c1c0342c0d40c482c0b218036134481d00004000c0c0342d010701403050520000c0c01501640403500c043c0c581988800c404680c0300b24441c2d1264000102050800240d6042020403017400c541c443e8000014450242070700509100010009140780d0000f410600c0c03650020229200d0100c00c10095602140e084505c8040c180081ca20349508204c08004149602400d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 988985170 1250 988983920 988983929
    0x3050702150c100e1b040f02070804030203100e0a080309010f06180e014503030c0306080604020310020c1204030f11032a0609060d0b04060f0521010b030304 69
    0x2403980c2c0707280040b80e09107031020141c42e80c1c019a03c0e202115110b25404030301d10105d04400001c1092a01d02c003030003e4018404600003044007807000400d001009125005002100e000b2400e851802201072080021347d00a0300360000d00d40c010400002c0045c0c44540a0b40d0080b0340d590000500440030301002c1c0850b21590002c0307035000600d061848070400c59004003c18091444000e003e41c07900c0746110020700030750454980382c407000012500070200e0752900f048980000030a586104035882e09000e001000340301586000a410f080d4046111000046c402c0e0143d03601400030075403814607250400007904096030300c4800340074850303075100c80b5103200014101850180071408140400c40c030385500741002c4603107041d000744c1101840035459000c10b1a082220482282e00e1181c0700c126400080d640d200d141d0b000c0e42d000341c011038291000d00842d80a02503910090390308001140d100d011142a00c107107881507a520501c03120b0341c2c0c80340c17101b071642d495021554000040780c000c00d11350010741550000d820 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 988986420 1250 988985170 988985209
    0xa0506060310020c0c0409060b060d15090506281203020f0f010e190c0b0301060c05070608011512090f0f122d09051c03090819020d03050702 62
    0x5006603450240b11110112000507030031443c100b843c12085407598040404507101c0c580d00e050080522420b074121a02010700200b846075501000040c443c0140300b541c440c079104908030803020800021500c140d03406048014540010015202041c0500290383d05c8414100811482c0004911490b0310414a080c0d20a4003e00641ca845859151500000303a042c0f045aa041240110402d0740100390490205000700803c954110176080c0440f81c40011761141040f083c00000000380c0070391020040d65600e104405841103241e1f10401110002820f004105a9000660483e540c582c0558440040c506441002090080302c0d80c9684848501a03031060340e40ca4102060f40382002805454800f643c003060512110745a12041440003150040c0d074544000380381180d41a1405004409842c02440c00030441104886291180361181c0000102240032031001040425096400b00d0b920b4070169041214940c014000d408122844201ea607065040c040308220360005a110300403da10441c160f910f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 988987670 1250 988986420 988986433
    0x8030a050c060c030709060c031701120318030201050423030d0302191805100e0409050d140f180a091814030703300f0c230f030411030a05 61
    0x11245410140c0040c0004030f59001002003184264001001030180c0f901850304441c507400c5403800744c860b40048880404036500328000041e610b400c2d000c40d00a190311954030204846d1100908050384940d0b0300000317000c12000d00090006c20b1540c4a20010411145003182c0103104203408642401c10074802d603000240c00280800040c1841940388411000307a05c0c00c001360300740e403800965085280d80503182c032400040310034030403081c800d800c44680381d0340081c0100882429403070095a50215010450b01240c4119054a002940d02d4150f0749a1460300c1c6032107262000440e070406070700c500381a529900c2a901100824441890f01c5034850118810b40c00740040c0760b10341407100804a11111070700442d442080b444000903808151000751540b03180c0c88455a00e8045e80921a41c000350340e5040d50340e8904034826101c0c0c0402e40004188004a442c1c00344004c0e600c05902c1034541003041c0d1000284010031429009010000040d58001d01404601c04040e880c1d00019080c0004144141c90591001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 988988920 1250 988987670 988987687
    0x905040e010921090603090602120f010e0a020a05070f0c18050615031909020a05030d090f0509010f0e060d08190201060b0a0e01030b0312121816180608030a05 70
    0x8940c110f00c3d0002000c2d4520034494400300100000b000d40034010400d07460703000082c1046902d4054801902c800d508062691500d003d0600004a0921a030410b5103101000300324101d6461089400b411816521585050825140d1040c1d06e00118000c8402462244000400748000341e6000c00c0c01210798400b16007070401e0b000b0028040342c10780301c941d02d040d000c2092003040d81a80900c50f10000114102140360062400040c9400c2c00c2d41e84000d415001d214848030285034400004420350382070108030f95005490301e091004481d000d000342e112103004d20350240203019a00804690140000705200c0e8186103580d207104c840e40020b010700070114004055000020380a00030324024100000980782005c1c40c0c81b400602c451080303008281859a60210b070501901c091142d00c400d40500030743c155882c0c1c09000c0000c08101704440d80c9030810070000700702c14550300100354141c5095480caa20040c103414100180ca04121104236420303800da0700c08000480d950180040d2001000e69110700d07840d044c05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 988990170 1250 988988920 988988933
    0x5030a02060717190e0c040c0210061205030331030306080f0c150c122107050c060a0b061c020324060f0309030c0106030f14031e0a0905040e0109 64
    0x2402c040c03911410f0301c079080048464194200d9001000401c6020170311404411040f030070020b804041ca60001e00700420b040800d6000100f818003501c88800070030043c0d981c0d81004041e41c100307034402440e903041080030506052403000d000603408003458074410031104501c40030700c00c048150821070219454250820407404c05008120312412000041c000000500c80004c0724003040d1205000f03c114041420188504100074503002d00040c0d06405554510b80d000d418441c070000300100c001422a0000034039894400d40550b541148450000d2013607444000d5280f02401c40241a02c1c4c0161003440704400094500c1c0c0501c03980c074a45600184d4905048001c0c4d041c8400414010398418210006860740d911450101d0b400f1540442c00f103526510340b0b0994078114410540306111543c20805c01206108000107079409032441500c00e54441c03000046999168002c031018134030040840c0d40c0d52101d03d825000288005602481c040c24490303120300c0041c085405003209040c07241c5d0b4410204003081071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 988991420 1250 988990170 988990187
    0x60a08010e070504020c03130321021504060f1404030c0b011a04050d0816080406020114040809120f011a0f0a0305101512051f020c072105030a020607 66
    0x461000a2041c200d6448080d82e940e0064801e0314065980001c1115980000340290b0300c00c5020040350561040d41d81c20030403402c2144000c50011100071031103140c4c0741400041e40c4045055946c8000d44136503203036110100100308400c2e0500c40c11b61141e44030303030b842c81d41c03000ca851040b07109494113078009401e8200300151010580200d418140c00e00244a21014104181c0c0d00f182c10480d40e52a840840b8a0700c0b03262030107500300050249140c1c620510811107002c0c007400a03502d42e54001c10a42c030800241501e030035030655010b080108200692105401c00c3c89410300307103540d40e00840742441c1d0040300c0c042c00c4607200045d0f40e40d142c2c040301001d1070500d000c00010010f5001203403000c203802d05603103446032200c07004122100b0b1966219146001e00740c1c100690001030185449401e0180ca0b03d08086840380e5464810098006c210b400c81848199603200780c8a5986030380000700f007421b0501c0d41c0c003055822034401e10300d040c081008071440018030070002400c0d020010f81c090703d1141403644001d0480034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 988992670 1250 988991420 988991429
    0x31a0105010e0d02090c0c121b030703090909060e1f05060306040c061b021c061d072309011d0a0e03160305070c1e1a07060506060c060f060a 62
    0xd1081005410b940d0785019007a0702030301200d90324250b40703580c0c0c2a0741c8244108000c00555004641072001540d042c0c23000b03051000c490f248802c45052140c022662640308020000f0041400f4000070700040c8420750110311164405e5074002001118610514640a000c07141c50f022040c0d00b4480341a80f411310700138260099015801070602d8209692230241c0d40302b80d4000c1a00300041d00102180d000c0000092820440d006032103650064161907640c155802081c1c010f0312060309056074500e401c00310541618403450701d0801b400d15282012f642c2d094001c400160003020f4004089428420350301c0d0034409000300945c0e0368400541816184180c00400024040c2c503030741340390440342901200c0101c111000740410700d800314910180c038a0240c0341405030000241280c020f50502065000c4034404a052048241050785405640c84941502494001500301c0c1c1407034003408220700180070344d0420b90f00014014803441c10030f0000081c142c608001210300700303a0740060406100d03403030030103003c0b020240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 988993920 1250 988992670 988992677
    0x90a020c190f03051e13030c150e240c01061401080f0a0b060d0c03330311210a060b1806100306080102120a06090b03070e040501060f031a010501 64
    0x181681d89400b10481050301000d41070150000d12070000e003210710095118115124241600c4003010550754120b4505400101c94101c903240000c03490240d10400f40c1160300350b6540d61104820070070103102060070344900c6242c46289132401005501950000750105082130000018014603180c00d048108600c010250b05001c0000c09121241582070304e1151300944821010a41040a10209405d4404e14000900051815500da80340b04e5058000406a4120100009103145001140da00701306c1006407003180700300c2408003040000c00281d400308404000400822030f43c10b10820302c084010034108001295004001032400f008100e108080078004203039071001024250110381c00c1c41d0200500300c540704602c81d0000407011031094220340b0240c0100c00007035403982d003a0168144507450540b000c5141d0f0741400e0010902c0c410a103c0c42101d464010010000c1ea4075104500c0d01115000c0d00a444d00c2d52110004100992901c1906004511400c000e0b0f10340c5d074039000c25501c40310041c0c00c00c81c1013 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 988995170 1250 988993920 988993963
    0xf010f0b0d02060f0304020d0b0c03060108070e0d030e0a0801020f0a08151c022b0201120c0512040606051005030618102303010e0303040201021005010e0a0b0d02090a020c 75
    0x5038403110244e841c40008000c10341d9590325680005947c1044a40c2c0c011706405541c6d0400002c0d074455005540211020380703c03c0085c2d180c1d80c43c181c50240c04219855040560040307004042803103031003515840390024106050701074030785401c0f50036070340300480c421068500040c400c400103900c486056400b01c4540d045500d030102c3d100024440d842001b4080c50482030059060b425903440100460b003105020f02c0610315007a001040c0301c1d400d001010140e02050f4003040c10000c0d031145004042e5145150340e0340b5450004500d01c01100001d002d40140c450a070b44000214240e218094041074194035510340c02e031a0302c4e00204005609880c401d074881c40710001d9007130000b000d00550250091700d91070740142d0451851081c010038503001c003455080c3c0c15820403004010011000c00114041e5000317909071448050005010825034000f803042e01c070b0300010300c40021681e1025900c03984040600038461510a07451b40c0014075401025682c8004981d80084c03d0308002c0b00030400d83c01c41d000b001005024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 988996420 1250 988995170 988995173
    0x90c2d0a120c0f0804050313230103020f0a0f090906030b0a06080f120d11120132011214090601050109060c020a05091302060705010f0b0a0e270f010f0b0d 68
    0x104403544100d58003803144c92000320302044000d00556401c0c910443c2c03001c1c3c3e01c594400104d12400700d090880078128a031181f072007040354840d0003140c40c002c9011a8a81c9840c501c20401c607007070703201c540800341045422400402c14406134055400154000c1c90300c01410b04010822204890032030f4854101580148240c8825243c0802c0e00520034070f0380c0c00b505807110f00034000c080c0a01000219a81c18040020340d40c43c1c0646550680c505032003d501036140508880c0101c10345040c07600741d41031074159a03c0441c0c52030b50b01c0303400c00d0320690360b20a00228800802d850300c84855107040c1c03041c2c011500703c50014015560f110860030000c1141d8500780f07a4891158001c04c81c290010300600b801220550b00280a079004858803142d9a940908099910403080c00d04034020010300d4035000e1040d0601d0203420345440e0a9401c90140e034108545940c15403143d80d050442c06152140341c261030311881c05407818102e8140150f800164040300003003450300c3d030503900e1012241c07000d880d184202c00003400c000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 988997670 1250 988996420 988996427
    0x1e04110f0a03030c2a170d030212160203070609140d020706050913020c0d0210060f0b0a0809010608060c0d050c040609030311150114040c0e090c2d0a120c 68
    0x70304c103e4006259206241c00780c2c803d0143c00e90034072000303100101104c5000411142c01071030812144007907825104162800d1104505a02c503001700100d42c01c040001080d11294058a041c00041c440c0c0100d13881c15020340d039520107840104c2020383d201d1114250b03c4040c2a03051107100c010f000588098030609003403000103041030190015841c00758119a03003180030458150304a070381201d2490301711a02d003000200005d59804500d5146540c8509040001500070107841503c0d06407020044031900780410b045048a01c1034008042d00c24664030354030002402c10f03051007091b000c0d80301c208009949481c0381c000c4a0544402030001039070380c0000c03c02042002d5100c1c0c0850705032645498058090424000100c1c54505c491001c2410007040f20300000380e600c42d1140158454500356024441041820000d40b16041c18141e04d42e040304503540080c4000007210010310180b100c00300e400386010b0701001181101c280e074440044d00240002180c48102e44c0000d440500c0b00a4044203010000b1010f1008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 988998920 1250 988997670 988997687
    0xf0c0503241f0e04050705030f0c0102070e224e27090c08060d0311010f02040e0403020f0a170d0b040219090b0f0708031e04110f0a0303 60
    0x40c8612a0403018005042c2c1403072640780014002d0100110b42c6003050304029441c2c1d141446041d21074403502c40700403001000412000b0383c0c260160090b2040364078195110000b03180092010801d1200c031080d8007032060203403c03201348050040050b00c196110300c41a805000101c05192a0451102c8466003407080c0c81c04c2142d00030691030000702c42c1d441c0c5048029125940b4042e4801202c860074404a035154518aa24004403a207414090024132050203040d1341c0450f00350780e101d82000381070009001182c00b4141030300340c14010000009650101100100480c9c0085c0c1108500070795400c10f00c001e060341081008400f061020117414144456076038100c03240c00e5694a1081c0c0000403036024500e15141c0c0c022248014050000e65030340074410b441c0b01540fa0a0131f20003010500c0308201142d284501340a40e281c0d0001d9a000502d01081501e1340452600024940c503000c2d22996900502250710000142c06544100c1303824800309040400c010180350075550030b60042c07504000800201e607100244 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 989000170 1250 988998920 988998931
    0x190b060d020a0e1e031903050d0903110703030801031103010203090a031b1e031403010b090f0303071b0f0803120a0b0a17030d052406160f0c050324 65
    0x41e070b10444a9020780c0c207044515151070307000409113102d21944000d44014290008100d003034580010041d880003504004000024001844c240841003103068075500c2414128000d08211018642d80c5c01c0b01407415180350401c03000a0308000040042050800c0c008100d030000300c2c025802d602d01424119a2517442d180302400700b000702c1d1050620106a846402080340d04480c1c0351107080031101c1c400003036403240b440880001d58071000300404607801c071099a040c0c6000091052824502c2410001c41c80420344400354540000c100490000380d0002c0300d00d210075264010030466901e0b0042d4143c1d41021544498441d410410501c4080419401c41c50380c0310201c2000001d00c0c0e0300d41e20208a6181d0140c0000c0045042180c0c42e8000d400004003602da00440b00a00780000c0c0c1c5c0c7d400600380d2498401c0c20814410420303080c003a0142c03520101600110708140012418000d00e81c6544080c0019038000342c0d21107400184c10b1006040901580c0203800c5854a0120044c1e0007102841a40c90300619 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 989001420 1250 989000170 989000197
    0x30d14130f022101050709060806180c0c0304180b0a08010b0102060f1e0c03062b020904030210240e06010e0603070201060909061d0609120315030d0305190b06 70
    0xd84185003c3c0b84600c4a0f0014059000f00100d1500003000341c101032260007203401060b0a940015040d2034a140d946204106117008102140c4440c580f046c000c6e002162000220300003440085400e070a8520400702031020400f001c038400c0c000b4014880320510503041548640d0500180c0c43c03076039800145854104906c0b4881800340c0d61000c81c0300504806a00c5602009810700c010300050000d0039010350b002d240122108420750789980210021880d80b2220569109442c100000c050720389242501c2d07005004c0e005881412030f22403401000c494003500340d051000c03c640c1c940160107485a4010010f4840c1d0907100c880703424005c0c00a41074280140f1007903c02c010000000c0c18172031003900f0820041104100510100d00d03945001070151225854440180301d00c240c54600005002400f030b0f008801d40c90290142244018040c482980010b10b0104220003602c1e203002a900c0812031028580c416541c001355504060041c07116a0044421009000d42403141c00f10b050342d660303c11640744540210 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 989002670 1250 989001420 989001439
    0x120c09092802120d02370605041a10060201050117030d090206091305040b06011e0302070303060f06081006080106140306040f051e0a18030e0102070305030d14130f02 73
    0x10000f40720b0f6100809844035800342101041c07945800150301d0505003000140b0140703484011003585442c6285920204c00e4455240300403000c20183d078486a0842e0040300380a13100503401c3c4084028100c20380c3c00807121403600d4030400c9016420312034107024120000c0ca0020380000008825a40d00850900c0d6442a070340f040d40b001190785810880b1000600a4000d0000036002e01c00980100411101520001e070010001000c540c800c0031b00c400030241d11681d02f8401c2c07a419004a0080d0420701e13084081c10355425000c2104441003000400400380c5954006540ca080d101140c00211030764041070602c45258018800180c000164810611007804801e4603030b51000002070180c5044402008814606070522409840c0351402458140220301900d4081e210501c4079411a01c2003c00559510710307040344440007900c980341c42031140b10140304842d40c003500c0391601410f43d0b0001502203030b00b942c0c481c480c11a60000b1a01d01e648501c0c0e4040c140c040e20007985546043c038a00e2079000384690f4444 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 989003920 1250 989002670 989002673
    0x12020304031d130e030903010e0d020a17041211120a030f05071502072a03110402090d15020a1413060f20011424041109120c090928 58
    0x9003e02c2e8402803928500740540c010009a45071280e1100c54030f50301a50800080c040c3c003c07000501400055034560041c403072899540c54004d0500c4006071150000101000006044c1c0648030384000c03130318000c3c407800302c1c0c06601000304160040a040210310740e400c440c00c51310200750864030000c0080340d1030820345d40e90840751078194040d02001404940d46403011500e10107000039051020030144034510460a0410481201410310015200c02403107196401d41354005428260040d01026170040c000c1003220465036581c280046144185001999020034040c101a510050040d100103100b09041d207003044030b0080d20820b103014000d071414090401301d00300da42e61055000d56600900c000217100040442503c0c1800b912111a01055203071000b0003140b080a01c10282d0220207a000510305400c1b010b150911001e00b1070050b46030002501480003103007079203400c3d42203d0003211040242007031403c9001000094030000c0c0642c40741c0d0788a18240002c1600d080f00b030304200c1c034a0b803d402000800382d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 989005170 1250 989003920 989003929
    0x227010e011b14061806011206090f050d08091e2814030705010609060602030d0b010210020c06060306010e09060103110f0604060e0906120d051305040204030308010612020304031d 79
    0xa24006048a02d11441d0030785100000c600980681d405c46800c0c030301080502600d50307490b41d0070b000f17841e000170300e801030f440000e2601e40c00226142c1c07141071117940c0c101e402c0c0c8410b07040c240c5400d1107001140c0c0d032504000c5041402e0004e90b90041428826160b1108044019550341c013481103000c0311046001152840545c1d0041c0110341a944020703072038605088420b81c0354498000751411244e56003001d901050301c60850180d4419201c4c680d00444c20000780c10701d041c011740440c070080e44c150f00803004140d404045030300081048800c0e03440204082d01f050f5040c11724000d0140c0c0140c00c01804002404030400012448904494000504004e8401e2000008908040c410340c402d900640c0020b00281c890b0b04022802c5a9070740865070180715644020074018058034103034099107590040380c481c030000ba006074090010702a001030008282511400483d080740d119030001c1c2c0103c1c0d003104c0100300d941e074040490f404881d901002542142040c4da0081d01481000c01000001028a101402035403034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 989006420 1250 989005170 989005217
    0x310030b15030a150e0a080f03151002030703081605031303030b0603040f021011060115050705030d02090a06050c030a08072f0d020a0c1421010227010e01 68
    0x8000b802d8403050301161814280707130103080c03d010706041d007050310003a002000882e031418210740091456240c080018000041540003c0440d0004891003042042d562120880450702c030301203400841c0c0d10310075410040c10300c0c3c400800c072480c50840c0e40d580358000340e400810380350000302100121f010764929160940c00380110325440d0341c005401004100a000482c1021040c0038001e0311404120081410704882c0b0001078450614580d010200412803600414a40304115400c1c0c68090b0804c4201c0d90f420342540c1c4a0310041d641d0a401003809100d84c03a01b41082c1d030041840d818442d151412150b451030310390280156000a11414400141070280a541e0301c00d0800c146a81c0c04150104484403168001d036502c50414061055140031126140001401d402c0c15422206000c0c25a1605824400d04d4003403403d455005840300c01190201c118902c03088000c625900d00241e00c6444030f0326070034003003e002d80f00c0c8090010500541440c0d40d07002004941d4241081c60201d285080d12110002041c9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 989007670 1250 989006420 989006461
    0x31009021210150801090f080d0603020d050d0801061110020d0617060a111330050c091003080d050a0b0310140901020c0d0f02010f0c02010c090b0310030b 68
    0x141c4400b84030540c4032a0b019261156408848490103512a6015801c803882c00394010244400030390341c140800c0d4590003030407190001841c017080c2c040d20399020a030b00c8401d60004841c9035101800c1b6100c2603410580043c00b6000e680f800050350580140c1d0b296560310142802c0031071507070024404029444540000002d8000c1e800e1161035401580b009a5035000300711000300d40d207407624039103920601c003141c01c5030b100000040300b4009080c28160641600401c0c0d000210268095091241e6541d070305180b040c951502480c00f81440c50400c40078400380c81d4004111000554102c07505000080c404000e4a0504620b0f40c0000740d02e0381c03050b441000502810042ca50705100e0010301940c0c080c00c982054082ca545400842520740320500341034281d01880308914203a03001341420450007449900b2200c0054018400400d1550203032040000311059100e618006075100e01c20041c5141c0c020144000810783d5203219450742c030344440b0340040c02c00c40c1d0000074420385050011486041c158001c40521a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 989008920 1250 989007670 989007673
    0x910030f050132010f230402190203040e07170a0b12070b0a14070203070e1b040909050618100216141f0507090b07140f07180b0310090212 61
    0xd050b40088841d06641181e0000c50300c18140c1c0086504020211100111501001d00f0441e60b07030480001c203046d1034079648a9401c60381c01d1107001105a04400010610840da8029560b120b0401040403500c0d00c0c01030001c4103201c0448044000d03c240646041c1d40003076100070000d000002c0ca00000d0942e80103480544e201d100d514000b1481c85a070800801d4000180d0f15447c00301000f16211031900c2c042c440004e545034011280c104071922854002d2503002148009441a50300107d010b5000d41e00650440850b89c0d03070740c807480000c000701007180f9500628150f408203007000046a4403541d8003940c3d00d0b100d200315000708040300700d0402c0c104c822014070b5004030403052018104103640e90b5500511000c400503490301c4d081d95180a91841203501501c0503950b13a980343c0c0d0130090402902d6214101c1140c4d80504030b24507190584c01840000c120790440380180c03048914085220005034080342d40900300301d01c0c03c0715050380c542c0d000403071010541c8441c01c0840d03107a4060000803154900051018400d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 989010170 1250 989008920 989008961
    0x3090203060f15010201050c071e080309030913140114030f0a080d0b06161115270f010206040215071502070606060908030913020d14150910030f0501 66
    0x4580c1a8802c01c2c401e401200000c6400c060f010300490903100281d80c10000080100640d801164841d420380c5450000000c071003090348016590f0030310a40c012514001c10f9000410041840d140000701c13404030300e00b6004103000842e684040e55520030b43c184141101d80042c0050200c450301d050016113074202428007920039400e65801c3c01e0405501808454106034541401c8171040c0c5400d00c1074a50726000141103100c16002d0ba9a802d40c0d950750425016404040010049420030301003005121a16821071440344100148284901700c6980f0312803c3e01c50b03c0f00710450303007007030b45d00050590380b064040300c0030b80301d91210404030300280c86002c00c0900a0804204c4c004c840300341540081c80014030851013040709980c1c0b050220380c21680c50040e100290401c1045041c0c51520a0040309021082c0100514086404907000300f00c0c0e94900d003801d20130000d401044845001030402c0310300040282c5400c1d6a52400d03a200d0b191000c01e501004045100924502e030500100354840951401881c0c078102c407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 989011420 1250 989010170 989010181
    0x60608450639090a08010e0105010e063102040608090d0201051b130503030d06050a090204030c060807030f0501060c12030e0c0d0501020915041701140a09030309020306 74
    0x31490051038105039144119808203560842c0301d0a5403030b602426000e0341210204110081c80a11070b0b07010300444001c014001048159118600a402800044000241d4013800c102c80d0342940d00503070101034400780c220100002520f481946200b42c000b02d020002050030000e01c4000300d010074860355074141d8408030b00031a0250700042c01a01031010315089804060200c0012400d07108211030500303480140f5408a1400c03a9203001600003c40c0210b0341108250b00c90010070304e15000000d070500081d0f250703d0108201d00704074030080081c14404000390310380b500790345070404980814841d403010000103038006003005119510248501c03400a5080c046969a40030080c031640e11a40b064038281048054240704e1402403142e45840c072050400b07401381522510402421a803515016501550200461600703680d031016000c80710145524101e0316981030009528500d59810808510b980c5007541400d0b5207460114810380c8001a10001304407203c1910303045014100005000f50503120b65001d015 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 989012670 1250 989011420 989011531
    0x1d030a0c05072303061f030f1e080310050f0a0605070309030507090f0c1b17130905011707030b01090f06320319060c05120405070612060608 62
    0x503d04500301c040b1050f5480c2d006111115200684080c2d440c0306120b04104001025440001c450794040c0600400341300f45041c800200039856075084600c51800001c002d4410020002a00174103802d95004a840d00c81d8001300c1c100740b003e4096141800008070f411402c26104550303250245621800f5602c500341e031650a030018000f16a0f1400c146418400d510000c01e108800000c0c410010707400f000c400f140d180c0c460000c201900c03e051810b0050400080d45981602c0222000800c081c140010b0258509100301800002414900103175400c400c0081010404201c0743d14103440410600141003070710303080d2080041005500042c801c4449482c010201c0d8181072000e0300c040344400507003da0800740801c1503120814081e041e189020014a40f00c0800d9659111015034181c600b8207a01d002d98009110308a94002c0702c046800380e20180c1c040c8186948200940074200030100140801810b20070094919000100400d4003071050550b51030308611107618801c08810021003020342c1c440410f1108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 989013920 1250 989012670 989012729
    0x6030a0f08040e1e04020f03010b061b161d0903040905040b07181d060a0830040501090314151512031602010828020408011d030a0c0507 60
    0x2c40c442d10f014000128650b860380c004030010102c103a01c1c20312030341c0d8580c00c0012081a04408079090f44d80c80144c490703241c4800005054094111102215100c0d02c2400e00d440e001501091f4110661818010891241c2911003c211248501d905001c0b958501d0503407441d42c0143d5111062407418401848180000180d5103800b07002c0c943d65410340e0200303d00325108241c0304c0d480364040d0340d8261394031078541c8068101c1d000d4100c40000e10300d103000c0780d070f900d0041d01e8501c03011056200d45e0002e00c0841e94400200c1c1d840540450081c078224105481d2500190815005110103404410711008038500301c0014480103044160766051000b0a05140d0104094910b13946400c1380030f0b803266003200355450400000e41310783d500103100c41e842005c299401100c0302d0ba000703030400303a1104030000d16540b000305203031042000d0301081c000140c455142201c5a401d40e43c400102c00382080341102181500c28020003110290002070406112520052500a02d0101298041504c0e048a132030994011000c29400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 989015170 1250 989013920 989013929
    0x715020f0a120e01140a0e0a12050102032401080f06190f0f06090806150d060f0f0b010c0201171b030108100e150a09060219020607020f0d120506030a0f0804 69
    0x102c81c0a080d201d801074621310300c210ba00d542400d40c14050704406c035110300030150081c0780241050003038565501c1d212142070100c500c116203694012003040402080e4081600700d405d141c9c0384651030713901c000002911101d406403c219420000300000f4690340c9400e000600c0c401c59041c0b11801140d41c1e14502e80d00c04112380260240414102c00024505100e0810402030302d0504000d0300581e2a50b00743c8080c2d00b40015009904102c0847e841f1003c201d9030300c51889801c2041c40d001c2170501000204200315840e40407214144031144441d140541d034003c040110700400d400168480d41c03282c101c003100c028041a040609400d000001040c035050101c3d024105110004046c80b001140c600c055866a0b6401c81015195500e400000c0c00308039184c0142142901503a00149044500400249440001c15500c4050f0b4040c2007441140b560421039210b4206500f00a801d2050700f05800420002c1081a94845546c403680460402d0b0b030306225144002c0d80c03180102c3c24202c2203252116298105208 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 989016420 1250 989015170 989015177
    0x30112110612090c0a1d04330612050d08040201021c020a0209011a031303050d02040605070b0604020a12020721080405060705090a0b071a100302031b030715020f0a12 73
    0x82c94030305041c1601c3c45d20956480300c01c0011841c0180c05442d170000300c01003055580c880c2400c003150591a11007401c2c0450030314683c4401c1114110a0424203490300c0354041d4841501045c2001e000c00c40114400c41401c4c0d081c0740802140c0c813135000403464031b03240d400ea6000c000030310030031450100c1d00006c4440c4070a2080d680803985a07607580400484150050144d1031080040000810000c844843c0c50b030301a1103401c0940c1002c0b080701c5054200c0c1c00c00c0c0c1000b030105a000a200b4103220606007120707070210040300c0030752038094480c40040070100302c212810b00b940c3e0040b48500070401000ba000030082e407190450340840702c146600504030315043e40d09a809001d8880800c02446c841d000311140500f001e000310740203500d0b02c103188003940e0080b81d0a4664401036255109140040030300a0b000300b1104080070f90250950040500f80186407903600010400d11035000040d86004c5002030440b84403801400c0c004401d450280d09100382100109003500958081d07004009a07910300a00c102c91540d0f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 989017670 1250 989016420 989016433
    0xd021c0804210e090a180201050d020c2e050123040f0203070201022709070804080d0e0106050301061d040221030703092c04081b070806070e090c03011211061209 71
    0x1100c6000c542001c4001b02091a0494919000d54010001840ca000a100c401031802c60303032002060400d07030803060402c00070a29010444d100101c24074501a2411720031410061540340c034001c0c40400c18603415462800e1b484001801c01c80d07640f0741c8030f035210304080d5800390350341c1c0f410300030080c003d51144000b0598000e9001030074501180740b6400c02d503504006050104242c856620640e910400281304441d0a00100402040d00c00b0b140240f00510034402c0000c200c0c64102402c142c299805600400f143d002d4103014403a142228400d01500319405480d001d840c101120540d1b04034100c14114201e1034800059164105507114042074100e074009965041543d030403012314a01c09080101403c885100ca1010802060780070f00103000d440701419030301c90001880e4903010700780801a0f01403d010b401c001f081041c42c41d004006403056070003c039050b00d164a4828094021800180641030408c14071042203400c00048001800c0540e80041006450390710f682c0c0907011004007110f14440902408 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 989018920 1250 989017670 989017681
    0x90405070608130302060c091c0f0b01081b0f0f0d0b04020901150804021003150305010213060e031f0902042406030e03120c12180d021c0804210e09 65
    0x200b01c80103444d500d90701801003900e4039543d2030700b203400c6031041c05c0c0d0282040c0d41038501c0308224031500307041d90b100e800c01100002042c181807404140503030101c0c0c05500500c8001c2800000544020800902200d802d90003241c108013103240c101e045132240d80c00c1145c440590301402000c41c80103201d02d2003158018020380e2200040071040c0b01c6a090ba0700850340c808080340c014a44400d41c1c550407410341c43c00054081100854004120260f8001d5442c1c3c0d5002502d61480b400312030001c00035000e00e00f0200e20b5030190001080d0b03217005542c07180ea031850320841d00e458003c845804c40024a500200248800c0c0c1d20b01100781400091000c0d003000c1ea030262040000c03150b000340920f1003014101c101541c140446d00c100340046940040600c405e020003003048124151091034407500910107440030002031604075440e1413420044210201c150351003031151003c40d407004507500500404a1401009035241c030300d402c41012081c11600c0d24807952051aa400315a4003181c030030440d2408072503002054503503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 989020170 1250 989018920 989018941
    0x2210405011b14160606060f021005070c140f07090606030507210b120a050a140316080c0c03120c1608100e0a0f0b040b1f0501120902090405070608 65
    0x80400d001288840140040c400441800307414621320005620841c0846a9952406c80704150003103004a40380c0034a040000d50b04000b0648090048802001030b800c1040d4040d012000601c4028201e80b190602d20703201900501030981901008800c80340502e84540006e0094025400780d81c0002c0d1070030340064032092290201819900085051107510441000c0c50300c081c00402d908180c01c2405040c410206080070440b64011a0044000c0d0940090a02d09020b02c54040e03d403519456000307100c0d00c9184807250030a20280c0350300c66081d680d00c05103070f45418141010300d50a540c1c14055025200e810003c01c01c0180480030144054901d03840c13501107000c0d040c81e00741c003800d5459480003c1e9203049030042c0c0e005035200b95080e401c0700d0b00098950381e0684180081c0700119143c0c01c0350400d2008100000c582503412441851003000382c003900744c4c9800303f0500c0c50302c1024100070495018248134082e40c0d210941d455005040c003440c5151a04260b40d450b07100c1c0c4907020008000c000058503d120 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 989021420 1250 989020170 989020211
    0xc090807080a150516050c160e04140a051510030b090d0915120b010e090a09230628020a0504050f030c090c03150604060f020f010b0a030f060221040501 67
    0xb540510152240110b1750840b41c82d005039406000c980300c6d5500881606c250500800001d2512000c0c18815181c6490140300700044406011215405108482c1c0080c0780400c8640d0083e04202c10070141f6500e0100c01c842c031035160703400580040b21800034418447c0011405030005041a10b68040e800e03507806a40070a000300c0d042010004280d0854041c0c101c9042d00070f01d4254105151480900f40d14000045200b501a00d10000e095613484162080100c60901007181c01e40070b1701c084008c030320100c4506440e031000400c40000d85804260240940d061502e64903a40c0c602d40038115210385504a002c0e00691040c0100340c416078010303e400c180f61400040d00c5007082806440c503101c0d6203601c00115078980014015000c6206c074904000079075294140904000c191a17512240d01410220010b0304010300031040d08440d90500607188915225410706100b143d5014860151108003800c0c54002402014408400700c858802c5c0b0300140c02d01092001e00507801003008000d00142481a00200b00313 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 989022670 1250 989021420 989021431
    0xd1107050a0302120114010b04060305071809052a0903060609060315070203040b0a122901110109080d060e07020601030302062403010903080a0e030315040c090807080a1505 76
    0x14805020300040c1402c4480d9103e18581000108011001d00c141c00c1403011b09030030640c4403807004102002032a505000e47c5801c0105420800303007075980b50041142181040c0a0301030303070356112400300300150900710104d45900399024242242c1208141a075007140d06c03502c1460722074441c0b103022131920315004189078040c400080c002d00800300380168000b2a050010012001c1d40014080060340c000500000d001b540e560b80d4880401046010350041214081c6c422011708a00741180000e924203904030b0318580305801d0901c0001800c01310710381805400c04220080c00040f000c40c2c810040d0300d840e00030f00700790745041204001a0b61502c01c202d944040920024005a020801282d00504914580c56450580b011201041406a0046800d49a8111040340002d02c0e00c82006160f103203a110b814400034402024602c0c40c1401c1804198034032903110542e1107143c1d14201c842c0c020b4012540c44008113030190a407002c0907a12010310751644000720040c1c43c0150300d07241102c4440c1d2144210341c444d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 989023920 1250 989022670 989022679
    0x618090c020a0c0609050a27090212030408010903090b03090a02041107061e0606050304030c03360501080903090114091f080906060a05181b1602100f080406020f1201080d110705 78
    0x881c45c0c03164a80103089101404d903084082f603100c2001c800c000740300510241070114008509110791307140c018055035503640b00984d561002c0c002e1000c0c000d0702198454034603404480c00715041320780c240c80884a10401d1070060805e0701d0502c00035a20006c0038668400c0d00501c92080000c1643c0c2c1c002908d89100881d40100001e8170600f51200003802841200540b002150000002000000b00258054000c0412644100c0c1d8050104050f6900211056024044801850610081200283c0303035215003415001607980204042c4095191074400900c0890044003406011540f50806810b000003960000642d0081500042041c107105c015102100c40103450f000c6c0e54296071503440b00a14018001d0b000e10800c0c14195003018a1510241002d005050048000781905104000103c2c07a180d6410090202ca00e40002c00e15400c8001a0f0388250800009640d581c8082c031003030a18422032840705058185500080381400c0c0c0042d21100020040d101c5050781260f42c903143e80d5a42081c4140f40d4013 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 989025170 1250 989023920 989023979
    0x708070b0408120a02030a06060906390807150614010e13061412060108061801060513061e0f06030b1f05070506010618090c020a0c0609050a 62
    0x2504444066034072a000d00c03441814004281e500c10303003d000641d41039400a8010046c001b1411541c4501d1008090608010520b2481c0c00005002100d0b03443d807000c594007111104507501450000c811f071501c050742019581d400d40b140740c000001d801142c1c0907129104000d14182c0c04505d2403160f08240e034130300015812405646c01c011a0220032448190303030840e0351518111501103c6004802c0945810203000300b11708d001a0500110100001c4144031ba58002001080312584c086010f64008040140140360050761040040c05000254401d50700890388140d56882000703194000c40030f5501003290321034054404020b4140790a407074080c400750351019100c100003103402a40000d00b0a880a0300c440001c05104c2d9030202c01c944203904a0010800001e010010080140951409450a810300303500d10607201103200104041d80c0034028450350740d25032800000f40200801c1c02c090742d106424001c0261030b060003c088016030310031580118628240401c42910388100c903681e10b0b8440010050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 989026420 1250 989025170 989025173
    0x32112090515011401020d0804020a093314121c090909050601140109080a0b25030b0f06040311150906121f0b070b0703110c0a17070807 60
    0x2041400001c44003841035641c01880703114201c481c180203246400703103030320900c100c00c0c00a810004c07806500010011207104100041e62040c00b107106a401d00500000c00c1030003149041c900b28103030800714070303c0c0c290b922110210f41090010003058910014a025590f02d5200500c4503041d0100e0402ca0700390403511510071403200d91080c00301191440c0c03618100782d41c0e5a80d468002c4951180d01a245038109038018068408183c640d00c0300c00e070b801e00e00381d840e036440e001e40f9940710020b00c1d130000c2c2213540550100e000240c80e82d8441e03200301c00410350310100c608090310140c000c080104000e40221081c121001c5c00f482d00350155021280c03c0321071000c0c026601d03020003050043d050940942d101040c0724040c19a11080040c1c012250040a0b0441704d08201000119119500d1540604414580c400344813a80c3e036802034a0b00c240d40a40c0c5100a91107041b0184d025000714a090302154002164900d98800d000500340c4915024510342c82070554003400d241403e10a082000e0410b14080143c0310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 989027670 1250 989026420 989026457
    0x405070b0c1f0615020a0210090b0301030f081b0d0f022107080c0105040b041505220302010e0607091707050a0b0d0e030d0212060d020f010f030b06070305040321 71
    0x3003524400440090b0180c0c07900c41c4035a0b0032041118001c01640044010030031412301c0c220030004020360341852611a45803c400e0b506500c0140002804021505108802c20817000240d40b1070780c40e03989590708c21040c04425203984aa405007d0000a04c1c011340c240e0351140081a0805440b192a0052012100503507007a000c65000f82d03012104d0603001c0000c2417a0305803e1103680d0017140300300400902403c1c9400c2a18280640e00203c05000b0719040a100e07446a10301d0038608a001003005450000c9480d0809900505007100010ba40c2d0060008104500d0b038001a86802e80d03080d41400800d110886408941e20703803050044c1900711000715003c0c402c400a20000c0d01c5002c0050402081c040c2040850351b096030404001c0035207480e00421104c01c078a281c1080c09501c000244c1c1d10b900040d2151300010b840004404089050002034103071014502c0c0f183d000300e407100001402c290f50b10605450010042d41c441e00c0165817100c84001d614020b02240000120040001c1d5030303d895144903182d014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 989028776 1106 989027670 989027713
    0x515090a110418021b060711030909010b030912040e0a0c020606010210052208030f060a0303021c17191116060b030c0310050405070b0c 60
    0x886595001e0301a50101d0f80d5070b0f031205a01800b880c805200900c180f810846103450307482d0740d5808201000403424060201c0369a280c0d96110314180342c07a00e9018800d01341e40d001d1076210040005821010140d90400c0448080e42d0f00c84900311402805507004c0c3c0d10006200306580b04228002409215280610034680050400e82c03600b40d00007511003400d000c01d000004d5a89000c01d40b00340130410888040303c40e8480f0010904900d0510120350b400882d089001d01c500780e000a2002d0900321ba083d800c899043d0010f20415812150030407005400c24008010008111500c02c518407440f184140108410004880c2070042c40c600300381901c4600a038409a03420030040c40c9849600554000e144c40c1d040000064110021400203040195151201c0d0745440b854005203210141c13075000900540c4108216142d50360341d2644000d4034041c40b52041c1e007507080300540404030340000921 = true := by decide +kernel

theorem cover : BRFrame.Cov 988848920 989028776 := by
  have h0 := BRFrame.cov_init 988848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 988848920 ≤ n) (h2 : n < 989028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
