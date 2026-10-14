-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2304
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:18:24.815769+00:00
-- url     : https://prove2.me/submissions/fee55dc0-8332-4f2b-87b7-1ee7c89f1212

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 414208633 ≤ n < 414388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 414209883 1250 414208633 414208657
    0x2180103060507260a090c0303030b01020d0e030d0f021e0105090d0807090603020306030a0b0f040c0e07020c0405060a08120406020d0e0d031110050a0905010e0105010825081002 78
    0x810f55440b04211070340d0310a8207140c105001c2c4d00a0004c40031424000895002600070f8001801964540718081c0b1050180e1095000c265030705d61103c0203503818020f01c00d180203181801003030744a0004c0440d07070b1840f0500c4414100201c0c000c64400a82c4280000c3e0030441e10382c480a080e002e110000c5600910307007600c2e42d550600ca4990100c2d1014007603442c0500c1114951a041d5209150500c150080d5100503d0380b9898003d5000c514005969030b101d0a01074110290660250b18103803604030f200d901a038002150301c0703040508000d400c0f64001541c0749048020381e0081600d46a40f0301080c441e034000d8000d05181d0058800f29601d055002c0060411244030758221031281c009810140e445400e49a83c0c02c0e000603111018401090103510440c483d0f032609012511041400b007450400c56030b06488007107250b030303c2c2c11144043c400b09009416407000540000c20a5526003080d403a52861004440904031181c0c5080240b11004c4c42c94940041400d803003070b2030083c00c2c0c010201009501100980c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 414211133 1250 414209883 414209891
    0x307020d0f0f082703010c050a0810030b010e16020c031023010b070302060708090c01080c120a1b020303011415070f0f02040e0c010e060f04050616060c02060408040302060f070218010306 82
    0x140310318050041f02642070b00c0791510b62402c070740410100d41070700e0700600da41c0c94000e08220010005c2e5480d0f0794503000f03000d000f03581903050825a09600040d070346a00314204540c82901c00030010b98011441c1009809882000070302080240c5120720313410f800782c02800312a8001000010100c0203036004007002e520943c25105140d44d0340200b40c074860001e0711010010b03402106503040710750180240e08d400c4002100d03083c0c108181ca03c280c0ca8001412a04056229101c4203100c810940c0b500d02d2400400150026505640c1010200b1401882401c401445415503c000e42c1301d032450002120790041e00400c5824111240b401d11201c80303803042004a000d41d01c4c0200c20b00c180354012509418550059503800000084c178010448150469240014200010417000501d59070b20301c010444010300810b02d00411040381815400c6424503805101550844010000000e0b441c00840d010741c0d0341110341c00e4130703014044034081590040c000000d41010810380d80803151000c10420310f04981c401ca400b88 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 414212383 1250 414211133 414211207
    0x609020408060601090e0903090904140105090d090b04031716020d0b10050402070206120402040213080a0b07030b09190b060f0319061202120109170c010605030307020d0f0f08 77
    0x2280c0a003281d47d143c440d0000d2151565910703241810a400500480e16501000e400c80c15103400c5400560f425015a440078900b1046c07103401031410401000b110780740c103050900d1a110405003c0e50440e60303981200c0000b900482c000d86140780c816533250043c02502415001c0d28100b200e60105076203000d00b40d48043c1001469281600880e240d4941c083c2c1000d0805007803040360324001c80d001d00b04990154003031050000c40c00c0c190800c84001e0134400300800b640d91080c148802c000101802010815060121406e910703101c0f10703081074000680484d034580d050441800d420090003e041c5041d031120000410702c0403415003074081c1d401109081c0702c400080b10104440000c4030380511464041c13903805810035002d071601c840520000190000041303118411651201001d0754401406622440302190660f02400c0920600300a0301050300294600760103500000c0180c1800b00006040070004e884100c10400062880540340b0b501a804d21303115102d201c4052680101007240c400c46003c10400b807 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 414213633 1250 414212383 414212399
    0x120a0311070b04061b150e0705150c1e0102070b0f060319033006090c020f010c0207030204020c011407091401030204050a09020f0c03070302060a050c2b060902040806060109 76
    0x201d04136202c50701d1304500c1500070003001124692074401910034500c480700d00c0b054035019006091555596101500e800f604010400503088003444080c40550002c1c883c0d004043c40c006619100c1800d000c3e15aa070503c80407245601a210b1481d00410f440044010300c610080c40d021942e0141b10201d06603240c030904084284400b9110032005000910015801500060244a203849845c6a40740300b1230740c0116028000280c41d01e036403100c00030315583c1001020107a814060340800c0007582d0000d10981c281040000d6a5580c10702020b440360741d0025050804010941c00320f102a00d040c8008101440d0020740642044001e1080d400a0081c800da20400d80d0303c20710803941a41c0005201c89950703410900450000d400244129852480401501e610b0b1407041010f008500d1003540100344c10701d440120401600c1010342852028402805030f0445181c40c2948100301c0100d00c0d50500107100100000c0000c0d100d164000103911348000307008900c0d00400b062461043d0340030b03201e2104082da42d100b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 414214883 1250 414213633 414213637
    0x9050105030f0f060109081204050109081903030510150f1e0516080408061005310f060b0406030e0c01050918131e03033206120a0311070b 61
    0x281080100b214800100c4100108201c00d030401410f00d0310103040ca0300e4501561511903206066200c540001c10100036079039010a510703001c2c040b60806400c0c402d61380d240f0f00d00d0350840d8200c0242416100c0c800211200c000703003181c0d0000c14007501584402c80540074017405007035031140324100254482c02d62920011012803c00c2e030910a5659441c074003410340400b404104094001100c00c1a03003000006800d04013084882d028008401019203420b223000b0030409d141040f491740e2038a00c00c1000804035021056486412408002000800c070540c1c2c82d4002401000107401018a142000c240882c2c0b4903403651020440c10081d00c1100c0c000ca04200041d03030389009e00c101856000d81264070040c60050f00780c94081d004407507890640000291591018050803089604c1503104440c0950b400034140d141c010207004400c03186044080e0103165031280703102006400303844031413191000410f4076a2038a0000d00203010b404429a04080b04a1a004040c54814404100c0501c906680841c0700901d00301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 414216133 1250 414214883 414214891
    0x10080a050c0a14161a180a02090a3b010f0b0a060507080c010c0c120e0f0402091309050a03090e01080304090c031e0c14180909031c0506010905010503 66
    0x180c10281e00d21814000c4000e610010009400250541c0158009980603e04580d5003244171428640c901c1c00a60784045407220741401e041c141c1c84441e2a030050f0316201d103032035041005281b0200d01c0a5602540803020801040f90048651045040035a591440418030043c0c0f10140c00034011118004004800e81c3d02c855205603201e0030201d41008900c0c0039038010198140300d00001030400c2c4882c440300e82110201006070001c24620070040040000d141b1418039801100d013402142443e604d0041240d0305040c070003890080c0ea000980440030380c0c03007210509519030700c400d0034840c240c1c80b441d010344c41700e801e440101d000c81c210090101d4010b141403410390580c0c00080003103040038600343c1d480000e441240d080d07105040e40c82500e01c50203a651160007000304003903076011a0030046032000500003900588903c401c040203008a0203c4521940c141000000c210380241a5480304c460150640c400c4e505601001d10034220402031950301608490b1061100340c039001c0d4030503521001900c03144000c40d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 414217383 1250 414216133 414216137
    0xe0402090f0d0516080a12031802120307020307030804051002030403172506060303080601113706050708061005191e21090f080904090210080a050c0a 66
    0x941682041c0c140002189220b03400b4070203e41002507a800014182060754001d0030181e08402160024011400e2030440f80074650300d03013000f28442002c94030004608205c0000d1054600c8403016801e40400c209460b01a40c008065444542e640e1809142c154480d10401c0d00404541003111170060001c0300742c40c00c503604005a40030000207040c001c0b030203500c800c0f030758102441d1801c1203038081c1015070300c0320303c00501c41d4034001000e47c15030270054001c0c0801003c041c10803030304000c0c008900ea0080f900c0401e41d001965110340c13000312081584a4007001d4007400902001e08105907003440100d0700854000c1c20075483e250140e0b11654180002010b9030300344074022030010080701d294814000005078080d0b5080c5407c2200a260f004104c01d41c1e50590209800610780d0342c0c03000101d03065a8412508030103091400c1140c40341d0303a46c031021101c02c51280501000b0740401d86c80c00b00e071610f4020b0404503900918031703003507801503610141406400340c41042d291483c3c04006980541c01200700c130850b458076 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 414218633 1250 414217383 414217399
    0x6090b100c0b0603120304050f070e0907030201050304060b0306040807150209150d060b03070e03011a0a0e090a080a0507050610080304090c0302131202031c080604050901140c09010e040209 83
    0xe91101e040d0900e02400c3c440d050302c600001a03040030300005c051406584030b403001e0303c4007a2a01d86041d107001d01030303040030040300d211006000000f600000c0060840c4e60a0030150b840c0c0c0c0d00c40c10444018514880a00d80600400c010082003000302002004160b00c01c1070482c0b54108460b10400072401038000c52030b0020b511b2005038110300000c001402e2040210305011520079180c00f6040c9850f00248c0301080410800c0d02444045c0c5400e0141b4030b6160b441c0e60003071038810410000100540c10303e200318020740c0b03100004039000007424400100c010360401400c40e510060241e004115611a10082d21a0b00030306001c02c8050340418144002c550b0481e00644c105820071444000500b4510000410316a08000011168200c107500c3c5004211904941101500b540145030500700900c0000b003d100c0318018003076515800002554000d002902c00190136522034200c0707401440022412a03018951904201545905c00c0003440210307800e0f6540000d121400d414403007030b800342c402116800401c07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 414219883 1250 414218633 414218657
    0x90c0f03060d050a0501090b0603190b070e030a120c0b090a1502030a1508010e0d0f0503070309030c0609050c01120e0c092a070308070c0b060d140f0106090b10 70
    0x8a0410b0280364015800e6450000742079450302d0840d008480c003101c0007112001000094541070040e480500290710030305004088503075901c000640c004021200b0f0105141c545403642d101045042d6000d03506c41c43c051210004c502c070140140c1e0004004450306004c0300300007154580003291960300e0a6206192600c25550190700318040e4000404984016550744000030303001454860703002c02400790000019491600b40321041c10f00c00c0388007002e014050050843c1d0507255024084952022086c900041c1800b0180b4045600c0605440c1c01351032141001441c00900801040b07084c00b0b11401d0722607050102035450310405903882c1c448500b030303290450240c0c0b50741c9092880c80c4961000c503400c000b039000c40c02210100c07001c1503c0040380b403070003901044100416800c00b01e1250081d18608154003250700540c0c0d90308906000400040c000d8051506d10810000c99280d0140010442c0090303802c001041d40d035990007000c0c40e1245801490034445101c1f10380c00c0400002e030882403955286052850 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 414221133 1250 414219883 414219889
    0xd020412031d010c051507182306031e04050106090c03050708180d18241202090d060b0310180c1211210703060504032006061c021e090c0f0306 63
    0xe401402d150902c440310001d2030323004448009202c050402c42c603282138034060105e0708100561f020307035106016003010414400800b1903403150a594140032000050380f541c851a140e805013916600c4000b282d400d000c14001d003190541c100c1441510309035540e100c2980d81003105441003400020000094110b281a4110140b050041a00003081400d000b4003659403500381c2c4045042c07400d416060a22800da840b038445501200300054111500700541c100300049000910b0401404002403030076903940385449482d01c0030f0180e00603800c9024010405003060401e401c040b110034020031568401d145001180c8410203100d40100e803500468a10088030310078050111001460b640c44107083d211203d4607160710742c1049550f015500c5142e000c0f60608042c075011300b03205403401c41d601490484031108003801100040455106074122040c00c0107070301e6040c160103900d4220768040c1d085040b104080070500c140201c18a0150300c251000682c80d91183e0b914601d5014460401c9102001040864003501d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 414222383 1250 414221133 414221173
    0x40b040911010c0f02030f1e010b03070e06031f050627010501030908070503030c0a0f30020f0313051203100b031b1605010b01230d020412031d010c05 66
    0x40c8034450040e58000a034001071f1401a0b084500c01081d4410760b51110a0070440e0030fa80d540c9078000d0700038441800070000294841c981c6000b041008145240054030380c1d42d00f0003001c084005141a06129403804c2c40e01040500821600a030003a1102c03818640400084007240f6032002455415491603400c1c4801100030300700b014001e070744808ac10711040010480030b000545c01072200c440140d5458040036000b4145502c440e2044040c00281e0480c003034900c1041c200346254041c0d0901c0b0000240341e01c02c2c1003000340030301045032003070300f02c0030041210307581000705480341160041084070400004560024002d11040b1032000d1101050841008802e06503006150040c2100303c40346000311010710310180d0b9802c0300c020b0050480841c06039005002d02842100584442031030401c500c0000c241520200141d0481c1488001d0800150045423090650584000c1c094040000c4d59001841c240280101d5000c0304003640e503a005080180702d90b0140000404e25940310002e0020107144a140100b54 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 414223633 1250 414222383 414222407
    0x714060307030b06030702061b040620030409090c09060f030f0f0f021008040b01050907021216080f0d150f050607050703060615080a0b150a030b040203100302040b04091101 76
    0x2c161201d5114100740c1e2090051407007212281d0081c8543d10300070444001c1030718046112010742c00c04020034840316130306c24401d000c0c550359026058410403003a804c003840e612517a4051400e9510781000801000100e0070000110380c00006c041c0101350300c0c3e400110041445c0d02c00106443e250034107000c00105001221100c0b54020034100014420b00e401040d81c80030360655480025440104000400c0411000e450142200b607d80541c0e52404010280d40c0701a01030500700608800b00360501c00301c4442c3e03441703c0030a60150030075454403850105a400c98022501c05043c0fa41002c900b1400c00905544c0e00c011607001e1030400c0f030a140f0300301c180015a0320440c030035503881c000d44201101242c0b00e030248100901050090103590680c61030700038a00d505c0a0045160a8100400800c2e180d071003804c1003075192070071800d0f00d80e646000e000c10750091608405a07900b040c000b008001c1d82c810510403000c00c40f40203407030600803110604204801ca4928a90017400300814203030b00400c3c0e5100c0c0354801d100d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 414224883 1250 414223633 414223637
    0x5070b1308160320060f0405010206090c1c02030c0301020c01060e090a02150702120d08010503010b01080f0402010f09080106180c021c0e0406120506061009150f1b03020c0a05030714060307 83
    0x1c01503030208600746d02c6600607000b00c07400001c0420642d6170400103507500040c8200071b00303458101000010006414030f40d403001c52198a003943c00665030188100e000700000140210b40e1150311440c4a0701a117441d00c82d40040380045000103e0103c8086601802198014250000000411031440490b040b01c0b10991704110084090800094104107000702c0b100e464a61944d20762401c4109030945405a143c10304000c90038090255402180800d584c20580c24204070803245652001220401c1841e4041d140ba036007008000030341452550740c0c400b2001d40d0340b18240440100948283e95691281301c01001312018400d849810360320820b200005075600801c00f08005955407103c50404148000540b141c1c0c10450074008245408240180701d4101e50030002c1a041c5400e07000d800c6480c010100c4070a10031105140e80c0000c2c03058500c042c903403001001d1089003028a0600030b50b2003001c0c91050380505021703038012459240000c0c40c0812155010b80c1f83c80f030b4091071001c0c06015000a010042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 414226133 1250 414224883 414224933
    0x303040b0f0f1c0911040608100209030c101107060c0b240301090809131116111002031c0e030703120908030117010b060306150c070305070b13081603 66
    0x580c3c81c6104100382d0704046007036404181803240c0d003002e00303240c0034180750301d4803a9182a104200800012404a441c000041001625000900086410302140c560203070743c00f680c0c1c004080030403504a0740e08075030511000c00302e0304031988401040e5882c2c080c5c3e445c00b42240c1500750008402c10381382c154030807c1c617240420072000c0c00504408242581d40074103084401d11710110b13a507034450800d003040401c1e40464030000c2c08075141040e8140000c0c49041502303200e0000b900144e400b8480c81004403a8140b101418814120718a141c3c025160740114102d0740f503100d150710000803402618011000b003000340e10042c40ca0701e0829582550b600c03181002c2000c9450301c030942200850300d6400614000c1a90383c55000e540c0150401b003e08448015075a10300c904801e00912109484114105410440002e000355071000350030030700c501c0c00c14994801811849109804250701c0c103000e0203803d48247c1000a0030000d07843d010065255089a811000c0140e1090410004211140e81c1d510f01c031452203500711 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 414227383 1250 414226133 414226147
    0x1407090c0306080613030804120e090708010312031a190f06030501050a09050f040b19050c1b0a080304080319020c0705100206071e09090218040b0303040b0f0f 70
    0x50540d0404901000826500d102c104600c44013401803a5100d00c80180483c5030f00301e65500500714101c01f8101038911060303c2c00b107480260240001c05d030f407443d00501c0c0142c070b80380041c00101750802c240030445800544c1104030b5074180c024010380c1001401c42d00080a401985010300045542c44403100c40d0005100d0340001b01d8141d400d4140300505090b58002c40c041d07040006110b00c89040d03602105080b0714007010007100c68020004150800d0340013440c09030a494416404010240f07c036a854180c80c903007414400001c1d82031000708840e12203000c00d070f00c10706840f07c0c55a456080c60080509034000800005002558070001168044c880d0004c0030035019503030750b541c01240c1041c04c94642c2c0350701007242403103a8504654415000c0b16144024003541c0340035907006203680d010b0112650042c0d21580b00c2c0000d01c0c044e1a8017000382101d06030842d207600d9009001160520400075084c0038074134013440b9030424240441150155444031000501d0700056684860050b03000c440c481c00e1382c10b0b052000c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 414228633 1250 414227383 414227399
    0x16030509190b01030b0105030f12071703090706081812160b072c0f0f22020306090c25050712030201020307020c030c010f051e19080601031103041407 66
    0x1d01c81c01d40c0a01616942503040d4584000d09642c103070000c07803199100341d83c000143c0600244040c4c1d0200d10103a02038035001c07949008101213041c007180000d0707448040104004040005056030444250b03a13922586501c80001c1c044a0003414180c031003040e04030407207104041080c034000748044203003c030480240300003a4035920000c400c02d0340c00b8400100d022104034000900f021209291500301d000740800d4960150006040c075044190103401124200c00d00c05403541c80713a101080351542c18040300192401100b00c42c1c000e41c01119024030034040c40000c21903040401c001e41d11050281d1042c0200100d03020020500d15600d15000c4546100ea580c1c08250009407107486c3c0b144c641b2035000940c50f401c040501a00303145008605030700a034015991512030380e03440981010702c4c140343e080082da07501c6d2454618490142c0c590b124103c0c24000500213601001800d203908454a1a695074076050b190400114180c54420181d150100d0041c804107020400c060500381c0f0708001c8008850043c0e540d0124 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 414229883 1250 414228633 414228673
    0xb030c062a0604060506010f080612070e0108010f1d0a08070521071110050301060f1704080901080c090d06110c011a0102071d040b180a2916030509 65
    0x41c214590000010f00c41007024901510703400803024201407001218807240145103600040020748074402c808840403844000f4451617002d07082c0404681019a1120f4980e8040c2c1028000c04880c0b0b441c1860401c00c444007151a9820140100c001d05201951a01e98651726041a181603030315028030b8442c480184000e0084941c211058466a915070680e030501103030000444680c1e03030142070b201e54103d40302c5600c181201d065640c10705046910781c2c600d20080b540601d000003600d4071030405074140001e029040d030240c00104001d984800240d61419184400ea0180c0e1410700d4000041c0100000050b4145d048221528010010b2500384503041c6e89250035210448196611040410420f800302d503030500140c2d000e45107001309411016601203005a10348401407029009041d40c1d404544105a00e214008040d031940c5c04903105180541400030301c03240800851004c0c51a40e503400014803103000012446a9100004020180820039082d0064080103001c038056014282c090b180c2d5001080c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 414231133 1250 414229883 414229957
    0x51e0406050103030e04020c0c0103021b060103050c030708070807031509050d1d011103030a0f1808040602010c030504050a0b070e13092d111f020105190b030c06 71
    0x140c0451a07501d1418098112401840c415000301e00402288614100000300d170000104286001643c1e6255080032060343c4801c2056103146004420002090150003d5848400c08040b4161070125139544c2c2e055550300b660f4420b0380480e403c41c8404102140c6402070543d0700c400d904402048500e01ea175110360400c1020340d080fa010442900c1010000140085140c2d050f25003800c124890b0040e801e8030a079680402000f1203040743e00c61100003481700c0d50b500700c045645085180d020744d6503250315000c60260040d01840c0010343ca040b247d1b0888034841c0c000d580c021038019016003030f0884261184118030038020905000c1c0f005c15501c14846464206c40450a5010f602d030000e0001451b1601c02c00c0f045a24542c010051410601016188494407641024540c4080500c03000100321011412300302544001c03100c40d01505950442403a01908441d11800c4c0c3c5845503011200144003210446440049030764156000a04960701c50420b0340003030041800c80d5280802049001e0f03c42d1600380540c60f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 414232383 1250 414231133 414231143
    0x3042123060901140606040306090c09091a0f10030308101e060801080a0309210b07260103080a14070204020f12010e0108060f060607060e1c0309080a03051e04 70
    0x40003000b180a128161801e540d100341c41e60035041000004402c1c6c00b4078000603064541c0d409001040041c4603169000030010381c07000384140780785c40c18a1048155182c1500801134168000120403c040521003886103081182da1a01c0e1811034504481c40c000080a014111510240102d6003008888640c1401c0b91000c09851000e41041c400401c0314006030701c98915a800b4010600009401c0b00e00031003569034034040080311030b0006070030940040361143d0141600b0859002c2c8001954861200d0044c5011046000e116251080d0103180d000c00034800034040c2d010900c0140e003444e2140490108614100241e2030400c003040e00064200d9001c40a0801c1403030001a160181950705032400d8010100c0008914083d032400d03000b152a91070040820041d04000700c00038220f0754a10080c1d40000b60031010400070100d500d1512a0b85051844680d401c2031820040d5911161181c000c007030103181c0c08450749060035a0004103801910000c0d01804500389a101943d500070b1070013043c580701d18013075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 414233633 1250 414232383 414232393
    0x1f23011a0301050603160212030c03040618030c060506033901021f0b060d020c0106090f0b0a03060507050903030d14010b27061b0102120903042123 65
    0x30018146500c1554004041031000600042101c1da640005890348140d0307002c4440e0840c40482801c17030420340c400c2c00316032410b2004403d00c01e1132030303202e000345205d14402d01c1c1c10424031803c001100940c0030354120007000034040c5d0818000003101c540010b60054070203401c4404440c80c070018541c61a41001c6800c400d2440320206654422405103e03640c00d04c0f083c000303400000040800c17a02d118000e050300204880d280e01c8040e03002c0c1ca0340c008803040c03604481811900c0c1d9181c9115140a000244110306103142040705031800ea400d580700340c035040d0800a00000060b4615964000640001050300c410710809001004490b00d0030301c000c10145070080e04c00100c061500c40c0a0502030300681140c001d428040c0711100e41c0c00d520802031200181d1901114403606500310000d03c040c0301d0084054006088901328012250054024000c400607601110303c5955402c4200c0781d40340120b108424400c0c10684498001c2e940c3e07221010203a42c040d5410b0340518000c0b0145a50002460403080341c15400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 414234883 1250 414233633 414233639
    0x120c1008040b060a0b0406110705060d0c11070b0715060b030f010e01360905070906030605010b09180a020d0218030d02010c0504060f1701091401080304081f2301 71
    0x111445031580054100c0d11306500d68101845926980a140245801c0c003190f101c100c401c0c80420400c1d1030080c50010001341e81c4030001035a42d806401e506410f00d01040f141c496100414802103482c105681983c00080d040c9690780e150101c0300101c90003481000c1d6510b04000c1901c8005500031840b62402c3c110000042d4500211141c000005034062842d0100a240b44c0656002c132910100050701220451005010350740c80304001000301280061442c4031b803080c009030700443c50f049002202e004080c200b0850b1780c0c400310380486201c3d101589070702003101500d0210b01920010340315046004007000505200916007c0012a40031094004140d1345400880095290400c503000100c502480288840c5808100181c044c0c06507000f12404d1201c02e004030049180306da0f40e8945804010300c1d8000040d692044414010840580403400700264a0700100e40f50900000716002c98841c08010040c1e884401c20303001181440d085c2c075030340c86900c9080290b038954a6142e0800d88500a810030506545 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 414236133 1250 414234883 414234893
    0x3021c0209010902090d0f05190b010611010902060405060a170c12073b0306011e0b0a020a08091c030306080c041811030a080a0e150c0c120c100804 65
    0x1c0580c016400342e80100300c2c2600c40d48401c3c0701c4191256224800200a2003039140250800512500307a20451103100f1491041c41421401c041c1200c4094031440c810311482004142a5908514065000b5108100170055802c2038030060040984614100000d0030300381c0580280d803003055038880c070507003000314007004001c42082c00140c102065040150362801c0d007091103005c0e0441480340031822304240404010345502c01c003000464600050580301150b0b103407424102c888050b01071a2070108203855010491845200031500c0c284455001003052400554580005501044180e600725000c0815a488455001c881d4040c8034440e0300c000c04d00c1c900300a5103d140205190310300b031080303081c42288a02c2098004070202407940102c0c0408800c09214042842c00620410040201030002018443d640d806200c0729a8004200c0c0e070182840161030040405010302481030000360803113a050b100b9858164860026580c0700019118540e000f1400102d0744000c0400d20ba003c161000c0030081084 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 414237383 1250 414236133 414236149
    0x1e020903070504091109040305160c0305010c0809030d0c0302040504020c0c1e150705010e03190e040501060f1d0306090109060f06030b191b09060f0206090d051303021c02 75
    0x401a43c08011400094a40d0303501c00c1c4d1203960007070160541401040c107251042080300c0d8200b200081c106441001450030140d400300c00d01c020340c0c0719403074110381e202010705c0340c840325004498080003182007181924410000f880c11701100010305500f0040098983c6036400603042090013a400351000304c0d424014040b00d80001c081c5002030f015444504d941568914a071009107841c2d0380003068403071245140450041103c2c0301d001c8014440421005402c41c91858801200d44027941c031b10342e5010900d01400140c030020301440340400c0d405c017403840c1a540305000d50840102c003140d04800814241d00420b00b001001c5e50303202c5640e51600324400a0100502480b0344010350040100070803403940d214141c1d141d0000d800c01c02a440282d80016002041c0d8001c92006d044402c10204015003101c1c000d00300394810702c1020b010450041c034903e60b890020441034400c0c40300d0000307049011152003044a0a501000c422107000c07007032a00c0400540c507490034041c44100d104080c03400c8801a0700401c1581c4c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 414238633 1250 414237383 414237389
    0x613090218221203090201090509040501091403030705090127061211070507030b1806150f09100302120106030c08160506030c090f0411120a0c03060e0c03040302011e02090307 77
    0xb01c440d525400b40040d6101051a0410710f40f031900046174002c920040b00c000c3c8055026a61048003442407100b4410103600080100744031f505075882704004500445d03282d0108481c004003042c001e001c15002540100c008507441006000605514504100e400c229040316030494400655501c0b6080310007101485040070407401d16500500b0b203511551040e0b91140c8500004288403140030108130740521303e8161410300d9100a05903081032408003070244d907020440003090700c5083c1e0803400e12094101481c449000340b6502e0b18543c05d040c1181c00b40030380c1ca100740c0500e0a40b596203c000102141800c21140c000c0c01d051005170203c49100d0181c0e0102e034686800c2180f25410030824440e80300250300481c2e01a54080d90b1403000c00035800001001000001c140c01000080010f0000e402c1c0c00800105101d1000380b02c042040740e0303005500700e00300c1c0c03954000c80295030032841c04120010446000b540d40301e4400d10004c00c0b40c10b01c04101180b0501070b949000f41e03070342c2c01207036110040c1b40500c072882c09 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 414239883 1250 414238633 414238681
    0x90705030718020912030702040f060b030a0504080c0a0506040506070807050406030f020d090305091305090a060906180b040c080c0a03140f120403020f0a0e0613090218 74
    0x4054201000603403950968841ca406801ca080480b0a42032026015540d071180d00500b13100e08a903090580c10345a51040e001203120700c0c500346c0c140c00c100e090f500c52441645c2d15000100c1c00e5564099070300700100b102500540301074406018074141200100001443c503481074001d003d40d4142403030100c3c41c0080207042e00b4244900481000402030f400010740301240c9081c40e012850340d002043c4100281701e40111f004807542090700d54000c1c584c0010080c08100015100701200031300300001801120b00c20b45501003150020000c5101081303098220403011802003c000403c0315003410840548920b0400c12102c045515080100b8041c01106003002081d007500900020404075000ad20380700203500008000708807400001c041100200151a0104861401c45009030700030048034031950003d2204901c600312110300c1c1c1d00e45007080862101107031203c0e0020101a00c442c003c00c03502d00d4119542900c00d5a80b99841c60143c1d46e46140070340b0901401001c0c00807030410086240c0007100440014a03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 414241133 1250 414239883 414239893
    0x70b13090e120910120204090b09090a05100c050d0606030501051801050307060507030c120203030a0f060302240c03030c09010906020d020d14120c0a020106120c090c050c0105040606080609 83
    0x410140c0103c82d4030342c50455041c0c000703c1503000c06a5420500000840c0018808034020503500d0311035000032003050044400b40103554030b40000c0f544d1506444c00061640d006091185152160358214514401050511a06000b0740c0841a02100e10590107400000e0b1508010002810045070641c0c2d04070101820005560410012035a103d0281c485e00c02008000609101407600c200e4801c41c540350300c01c180d101c1c1100040c0c4001e5803900b068907650040e9181c101c40e46010b42c0c1c0340c4652400c603035008d07101c1000f000c0795a142a00d13141e42011004081d2208102603502250140015441400407044158a03041c03000001446500e0750381042d4150f40c00288407001098000030844030070607084c50880c07804446040c21082034002c0b5030382c54050203450402d00c6074491005029003044680c6a000300409a0382c7c55550101c90315401d4041c2030303c40a0041070001150a4001181c130f0f03022800c140d4500f0080000075821944115020f81d0030a540340f100b0700000a052210982000441009003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 414242383 1250 414241133 414241153
    0x120a0b0c1207120b06070c050306090718051314100b0907020a110616032309010903030e01090f23121e0f0a141504031d03070b13090e 59
    0xc1c0e980e01028110205005005a49185810f01038019405804020708919110281481c1070619550280500386c824080c490015144a00c0001c0900464110881c200c01d2056001341c0207004100150205c07041e0030321442841c02003070030144a0381080042c403005210500d29440100121400c0441d400e12519000050066184c2d00080079901c864016000603400726034000081d084e44180c0300c101d00b007811213051540038075400c201e071615503411f80080701d015081c500400c030b942c3c0d121310508280864000a0184013080c840d841e4000c800c0f006040c10442103450320f4480c000366450f03074010b440c0640a16094016602c0031181c242c0b2030101506d0031000d2034181200c0e01c0e22034801c000c144440315884103c03a03884a4003003140410041f082c809903803017280c2e241454000e100034401c0b00701c440d100d4224204070401c404045c0700d200c1c54045c0c0d42c8803085c3c0c040b5107802d1807002d4164144d503414820380c000403070802d8008006010300d660b4201c004038036500c2c4c0b96066040d54005040050103401c00e070004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 414243633 1250 414242383 414242407
    0x409080307030c0c06110702090901150323011506030b01080606030a0b041104080d08090a020102191103060a0605010e06070c0308030601020304180f0b090702150a0902120a0b0c 78
    0x24a410070180e06010410b00c450071021200d6410a1304007030a46030510070000b00b01c0b0001c4008203040340c001c0e00c0c6281d881e9540340080e82a100d01c00000006c108141c072041020031406902c04141072580b0103514401404100a6400e440406071000c428018500341084215007511a000c000c00d004c2c00c1842c0203180200000c1c1050200400034130308162035032100e0761a0382c0d49600a106da9100c494459031a03d4942c02056541c102c94203d050210301004045400d051300007400c2190254141c0c000d2120b10310001c0f0000103162207800488140320030109c42656940c0910209120b00a00000044d55605c0d0800040c0320a8010040500944081080c000415010b01a150640f0f81000b06981e4940322600100e1075441503a2100d00555150b0b00680400074044e0000c14aa030b0611106010080c420010031560b0300003510508090390000501041c503080f4650a9540a00c001c0c0000070305041d2500841c20328011111844004d402c400c080030200300850b140c458220703070503801d00703400c1540c6400c0e2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 414244883 1250 414243633 414243637
    0x102101a131a010318050619150803070f020a120b0601020106170a08071103030708040503010b010815010f230c06010b030702030a03020915040b070c0503010c3005091b040908 77
    0x10b01410151180704407081c0d01041d0021000e80e651110403034205203003100c004030b820018250b040c4406030030050100c0740c15194980300e00640c0d0055010754941402d036610b0308240c100300d000c22138111039000e81c0000c0c0c611448003016030003800741c120420079182c840002421940c84d41c1100540342040044c0140354080025600d0000d13501c625429550415407d20b15039404828410310f61610000270440704024005014000302c0714143c0c002d00140001038015134428104481110a40364580da122000d0741c41444c0400c6e001149041c48403000000742101007815803008611140600c0000d000c00b141c42d0204102c1f40140018683d140c00c40c00d00b960001c0d16407040e14061810190003085c640541d644151140040d045c03002c2c041d40c3d68582c1c60303405a000b6084070030f058030a03400f01040082c8508060060b05030018003a550400100c0000210203a602140c80000030f101c9070406030369184100328801c660089014500034107103800f80450100d150300380030b40c07128015800d1088440010300381b001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 414246133 1250 414244883 414244931
    0x606100f0f050c010f150602010f020315090a0b060c0f15040b01030b070905040c111011031807090c0305011a0715020a0c050d050405010e040504050a020f0102101a13 73
    0xa08503650f107038071000d42c80c090300e094885170708103e160182c0c544406074110301d03140495440b60000d1180415010201040b4081100d0650500060f4120f03098240703000c1030b600f6880340c1d1450b400206000801c011800941001c02d141c500e9130700840b011008041c0402000550120305240c0208510b483c0d51000b113035a2041c84010244007005001c104440d0003000c4d03030b101904014104114011003204001c0c52010442141d5240c0d004620800c420205207024050303916041c1c1c14918071307603114003204d4609080180c6000115001e544c0010444608902421a000304290342c007007119410030707001d40071903100f0b03048107003d0130740c100024400100c0206400b44080740c01c5c04016203404040f03a003034400d41aa840e00924500480a6201e01560402c020703000f503030401e03038035100e0100101e07040c8400c0340c00980e0003812540c00104038000500d021030601c1e0100d44d040c81a5038009490182d900300740e9030081280f0501240c41c800025460a1521403001240d2a40a061041070b500c0a0080c07031405c0760031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 414247383 1250 414246133 414246137
    0x1050706050f1803071502070218090312010602010c091a0c03030a1d0f0d031814010e06090705060f03040c0b040e0106030506010c080a0e0a1203080108010605030d1704021c050606100f0f 82
    0x2080708410b43d82c9000c2c4814ae25451180540317518035281403259165400020402c0c0581302000000c548144144241ca1083c50700ea00c40310350803030402d4a204000140072081c800d90b000200000c5100d420180041c45c010541d944010035210903440707140880c03441c1306101d50480d6000709040071403503a001810074081d004034100041c401103802900b4180c00c44004002c0c00380440c0004070280d21505510840c10030031001c061f00c0058684081d003503103130101441060b40c400020700521888000c87c03801550064411107039142d400307503503010b0310143da0815405610000b001a004001c513079003501030258850000d19012a1301001982e0b15035582c068101030200700f0456450004064407000380ca1406440001e480b0401c1c101c640c60004c00341003003400f803403669500b007003800160f40c1030000c0d4107207120f145521500300c02140f81d22b50b00f0f004540144140c5c0c8c800c103010000e4400f84c15404240d201c444c02172014000500c2c062007030080c02c2c112404400200b145014404454543c01014008000d43e14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 414248633 1250 414247383 414247387
    0x9060a05090705120f06010f050f12070510050409180f08030403030902120c01140a05070813031502030403200601060c03030f06060c051203041104050601050706050f1803071502 78
    0xc0314240c0c90003146401c416041103c150b03031000f10100001785524074207451011540300ea81ca8043c1080501078a00c07850f50003c42030604103100303203048086124040583c504544c40c1e15601c2c40012004c861003004400464400241400f08a20500450780010f0162041303c0c101000c0381c0e1030982102c00d184c0c0240540d07401001141c105442500081c50700c03a001042040c000401410a0fa00c81c21500c0c0c40d035010402d03550b28400004000c10540303070415106d44403e81000c0c0c0c2074a58051a5010b0105000c80350742561020000644000c8082907040c44041c0042c4c0340e1030140380240070994501100da02c5203103d03900c0004958030000b6840d05540e01440c100c2004150f6103001c1d0094000c01c100c42900a0624002040c606d900c465122161070141e01254000ca02c502c00080043c80141d070094548490150354903100d082075080180c00c8401072604520741611034946078110381007a9031281c0c3c2e1030540d04c1402522142e52603600000e020394005580717460b0255580300c0d442e10012498003e02500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 414249883 1250 414248633 414248641
    0x1206020a0324090b01110607030e1501060306030c0902032403070512030d1b0203030609100305010c08010501020f010e060411041503050d12020a080609060303040801020a030b10030509060a05 84
    0x2081c1c005411504210540900009064000c03200030740c0c080c043da00c1600e113010b0f101080c96100d1000301803801d003428050800303929244400c0303000e8903d00c48900c0c0c00f84075011110340c805403050b100034001c00f41c82c1e8000030485d045190000681200b5070100340420700502c2440020f40e54240d82144a520714a5484804180540801d0500510742d028540c0004400c00c1505441c03030100040c603d94a0105080110b0b40040030b5014410600c62100d40051b40184002045400d00380b41207504406881c155041e03055503a80c950342034032601c0e030095001480c143c004203c0303540c0408c24007841c04405802840405c5001c0010b030b0351800c00030809004025100c0d445070b19a1980c1d409001240600036a071642d068413070500a69507000d18060a000407505030040040d802d440c03081e11010071903961284529101c850401046d40030281600e40e06d4001000001340e030510920040c201c010464402240000b51941004030317100848006e41c0c2494144800c0225490001c507103241d02995000c1c0010302512 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 414251133 1250 414249883 414249887
    0x7140d030515091503070803210c03040618172109100b0a0503120403030e040b0f010c05120a09180507020303011206060807140f101d03010b04060e180102041206020a 73
    0x900d800000380c140c0174265012851f210003000501806412540000c0254040c80f44440c005204035003503000b0f00f0003400401c00040c41500308600840110180481c00c65103505c603105424a164600f1006100c009460103c0a0200c8050360a584002603150114070340301900548603400b00f00c00c1c0706265038035801900140d94544031000500001f50803140ca145078a0003154099003c2d00003600820750745034091841d46094052540d4205014104005030940f640c010354500c14111001c5440d0301420002054110050004e02a211003558802200c00c0c03420031640070507030f005c1010400e1203060808001c8410b8000040700e044481a603501c0700d0110340c0341020001091960406080c0d402103040c00180100d8142080301d5202c0200c8880e5001d179000410489640890040e41e000305528034001301c04400401c00d43e807030303a44e005000461820181000201216503903006018101d105005000e8504100920100f401c01e40030000c6250034240f400d544010301c50180003c02c102d40010707442c01c03194 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 414252383 1250 414251133 414251161
    0x30c01050a20070902040f12031407150924050405150612010603081207030209010f0e180a0f1103040f020603061f0917070b0f07050309030307140d03051509 69
    0x1810002c01d0781c001c10345442090001e075100707100342d00d009800140c001c50074030714001c2c0b904842585500c3c3d0100c60301902038421810b030003510040e120307000500001d11709031207103000c0c000c0e185100e6805600003c2c0c04216003c1e00a0141c0f24110b0b03401d04d403508120000340c00080084001c261410b020710256504800100c0101a4900c00100795080c04800400c0000880c045d0403c074103411044607240d550303000c00f00c003240107046003d40052020a07500748520301502c003003400048090003152011500c50420b060443c2c090701c0f080b040c0f0b5903c9840782d582040d41d1050000c00d0340104201c03451810503886c2c904c26401c00703840180c41000000089016580c4022492000508410715482440c2407800b002d060040d41c3e01c145103a594002140364813102c000702c0c1c040159145e20203c5410a10b44080f189081e42128000b10303400d00c01041031b526259020409090058421440241c0c00480500c200f070400c46070303d2810f1700b85802c180074400c07092101c96100780c04074010f45001600350703900d4205800342 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 414253633 1250 414252383 414252437
    0x1150c020d0c0810090c0522050702072705010e09120c1603030c031e050f07051002040b2107080403050901090f0b09150915070f0803070306090b030c01050a 69
    0x207807152800d012190212500103485c0310b0f01498446a0b0580e640c000c2c4260000c4110001c1006c0a40c0c400c0b081d1445110350106400417590310460750241d4840454002e104882c5102d1152402e01000944803d111401014054420084d1014160405960459a90700307c2d400290541d00007042c04c8000f49000c010313031303590b2000150f50701000c02c1d620704020707040c04921507041d00001ca0002011b010030119801c18444140c6c02d60340d491078400780002e507a005800900040b2110b00410304915448641800a0405401a00442a6100034121036107550391401e004c40e920302180c0000b0480e10075002803501364000d402d41061390382c66014200480345a0340319040000d40d982e1003000428940300800260034091030580e610b0380c0914900208403020700480741e4484d4030542d4000c0f040c44280700e0384050301010344a031050380d4240a043c0c3d00c070b48603074008461600010340e03901d0041104007214002c0007142c00c419406010f0005901e00000d10718494403008406020380c0d140d00300c41c1020042446840 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 414254883 1250 414253633 414253649
    0x91a0403030b2e0305040b0711030f0408060610020f0c010507030c0b09030316020304032102100c08040c0b0717030907080303040f05010c0f020601061206260601150c020d0c 76
    0x14100350800e01c400407615a10124141d070810260706503401e010b032141c0e500407070f005001e2814652390050129603d080718454a50903001c140b04000741c1d900000c019001505044014180c80c3c40e0003010302c80f012014415090456004c40700c12100e1400208140324902400e00e8001d551303a80f14201950940d042210040144245104114000700c005c0081c0d40900850038214041c8c001c2c400c0c0490b40c90040f808060203010100c80c05030521000010340054106050059a83d5442811104421154250000702c040760110007044200a0a98090b2000c0d104504c00d0a0900000f80c5a65005403031811240401031400404103021f01e0b000c00000d03000b40180c074110307a5641741a00d040098540d000d481100e25600340b20098004c1c1e401004001f0b4003007495070045c003c036882c1107021103640c5c0341e2400d12040e05544071000b154000c0e1485140c40420404000c000d04081209549441c1000580c426085040c0f00c45c1c654401070303400440000c00d035070112261100c280841c284503105004075072025031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 414256133 1250 414254883 414254899
    0x603110714100f150e070c051614150a0c020402131d01050901060503070302030402060d090302030a0206090f03040501120b040501170709090209040605070309080c160801091a0403030b 81
    0x81245000924100b819607095810b0040000c1c02c0e540c030054034a4280c60102d01004030a043c42002c90b0703c51401d500450794680405c0c52282c0d0349031581402501d242d4200c801e82110310600035010209025000b903030099900ad0b140c203e48040310012801141480d00821580520410543d607a5405482412003c41c800401882d41c074062102500b0b01031380700d441140150400000e1510700201818101c440a494082c550782c4c0d5483c08800952000300101c2e44400180080c024112b8144101c908542c8070340c004641e9110984d4001c0d01d1b01200814944459202c1c0c8080d42c044c1002000342d504440303003801c010100200b030070500c80280941142c00c68103c2c2c41c1000000b2081200000d0502c40141c600c1590345a41e2606000020b850400002035000301c00100803400080720f641c8071070740c89034141c0b40000700c0d5080d80e683c1c64040d5105000c100b0055100880350580d207200d0148003c010a28a0000c1144803800da61300c2c030a0b02ca145001d40580c4100f8400141858005d4118415003a00145900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 414257383 1250 414256133 414256163
    0x903090e0907050108060d020a0302011b17282001020c0f060105190e010513020c0106030b0702151e07050f040b0a090504182405040c05040e1606031107 67
    0x181d942e08540c482d0500182000b4081180d5003001c020b8030200c250050001180c0d035041d0b400541d40c141c10b184140103098a11150f5202160515030745030380741403c0316082503448548540200402c6e000316440441e11140c00050829603070044140700040c0b81c5a0801c40c00074040f18400d40c024090040244004c0c081c039405840d81440c00300c1c065060f11030844400a10303480385a02cbc0c610701d030700602130b240b00c2141c82d4006122626260460308400002c65101601d4041500101400d50760359600c00c031408034020040c403038020b8040c0902111000c4040040c1c0f100d2608041820702c803528041c09d03e00c1d8420590100d51035900c41d4088584104044803030310b51b82c0303640c1c0c0315002c20390740201450b00028440e02c10100e000e05d41030180103609110b0030643c800342641604d655071100000d26611606010504004050140301d000351841140100c1c1c940f513030285004148811f81e90b40c84103032034140c0c104100d01c005900c84124043c003507070900c0c5800500b411841c0c0c600c89162043c1140074248103542d03003c0c0b07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 414258633 1250 414257383 414257401
    0x130b0f090901051e0108152502070e162304380301150e0102072705060d03210603020d140c060c0c010e04020702040504120f140d0903090e 61
    0x4a000320741c1c085200c07031454445040d05540c00806e000e02c000030380003d0401855208000c581d140c101c0079062511041442c424031003c40409199184400b58020b081d00b0004821034030044e13580402411a0141540200400280100e1000800c21031080559100100e1501014207403005080158584002902500c80f141d003640070040a074000d41d0003561191044002c0d62054034101d892201600e903260f0081c0c4d2054961034000080f00b41188a48200000d110280611021a141d0210370760500c03454071501c070109070f460040c8035901a140c082901000260305c9160600c3d0000702c56a182c442a0440d10000040d0920b540040c0d442801c81c3d250100b4025000a0001d0030002a0120741c85140d05005200d018025118021000e070044000d01c1069402007942c0000c460300280014680074080d80094207c410680f0140c0ea0014001c0d05000748980118840c400182c0600b405003045000f81869501d9100d0b54440c1c4540507219a5040c04150007400d007040a4910254149000c2c507200d425 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 414259883 1250 414258633 414258641
    0x903011d0d02030406080f04210c05010e0106120209180703030302180102010509031605070503101b03050105060d0b01020307140d090f0503070e0702070b0d0203040201031a130b0f090901 82
    0x5040e19014014441114500010440f021588103884134400340d99000000c0808040c010000d941d60040744203480d54452527000340280701065500c0d42c10a0340043d0070207508442080c01d4495030f40c2e00d8080c09102206540030700c8414103030304a4110009540d421484202d00000c1302440740a031040744804410182c158001d00400b2900700364500c4021083c40049090700d0082d80c52507501d0300b040081030617500414584030b901d0b17401282112045551803009c00c0c542644421100311160755100b041c900c0c51070303450201d18107101c1490103105550510f000903c0700c0c401c0003141180b8650319544448564020f10555000d1500700c0013051586101901c07007900c41208100b41c0b40003512046011640e030404010704000d03940040d004040071814410b0401c10703443e000d0010003d501c2101000202c00303005100a0040740380c209005078236408d003440050300755442400b00303080b0700d0702d5040d00c203075a901e810504507841030101c180494400032240104a5101c41c903020b4582102c101d5040100207501504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 414261133 1250 414259883 414259931
    0x3305011503051e0c0a022401050102070e09100902040b0616060b0301091e0c2727150b15120c16030810180e0708030406090303050f090301 61
    0x14180401da5640d01c94000303070301c014881c80c906148483c0110710803011101c040e107424091401103c2c10854201c01b40b40c09015441c820b00601800c983c014007280d68140540e100829012407010050f0a0094120b0b48440780e40d001e10b43c45d04e956860700020341d0360b1608000c9080101502d415590b1040940c600307000c69001c0c000b9554030303050110200300e0341414407031501c00c0354100700801401c0c040c0d0a00040841c9038064250341d449a41d110201d4005d541d1080301c0d016a1002c41c1d40c2d918890010f403200c3c1505c4800c602d940c0500d540390201040954a00c80d800340c15070b80304031002c00402840f03403200b0044c03940986803900200c0389441039024021107401046000013001220a03190764885264041d803007100c107810728030008250b40000080c040c02420340c0001001c01d400841c0c0b40c8070102c0080c1884991601e040c01900c3da0b9140d0782d0400d0a101990140c02080e014515003410250041c1000b03000d484010700f0400d000419403000400da100384d44000030020002d108500000561000003c4110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 414262383 1250 414261133 414261137
    0x13020414040b060412080904020c070e1008162601150501080a02030421111006060e030c0105030127320906070305041a07030c170433050115 62
    0x50080c1e9551620000f52011941c8118021741c1038203e99441c201c1d981c00c1074011340e4019409206e5401d4408041c088800500a650b4020143d4500b03c02005281c1840b0b0340b0298060704000405580382281c0309070ba00c20307100c100003682505219100e1790310b6881c0700c08211088039441c0c04111000080c41c2400f85003220381c26610000c181c0c90b17101228040f031009440091150049001440801000e410f180c008005c40381030150a03607503c00105820940e04007107849507950350300710910005400100700c3c0032000c0b0641c02803802c4118200003030618030041c0151502c2d8130b81c88030151900d1090381040d00038080c3c0c80b1828480407141c9041c140c0800300140d8050185501590140c40030b00842269500c0b0f440c0c8507004001b15120480f041e03000300006802a1240100d00c408820640c1c40c101025004d2702c6145c3d00001c21411411000f0f01c4903860785408941c0300a10402d00c00410040041e10b031403031080a80f40721214420030b04100d400341e950403403003003000d0500d0000a0064407d8000b02400c00e056 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 414263633 1250 414262383 414262391
    0x1009050c1305010b07140a1a04021002010c0804030305150d08072105071e0b160f020109051005151806090a0b03100f0609141905040215091302041404 66
    0x1014040945009000700c0130880800d010715000301d010241c4251a10a040341035451084c625107a1348060700e6a89441c0024403040c3c8244402c6040810300343e071900499100070400b208901000400104001c0d0000d41019285c1c03020490381c0180e00700514010500070950302c83c084291921256580080c601502c80c44100320741e00c1d950460703084120350160095640e107881c0400f10350321100004055040c60f03045612002e003c4001034042940a402b540d0198603407000c084250000038054400c41c00040c2c07c59050900400000380001940c440c2c0d0308010b10301040c82d13a00d0904002201c114040455404400c41b80301c40140d1045120381401008155000b14655951400b03100c01e031240c01c040360780c041e170180c01c0c440b4041388142c0c0090541c030016040800c1440e56080c0b21801d0f51070791884007059101c003034240843d409002144030841c40c0d9030281480685066000a00103040c03840e00d007504d0100c001446030300340e55920103040308010250000c5496036203490690300410303030b6007607a00d002e6454 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 414264883 1250 414263633 414263659
    0x4051518150108060d030c060b0409081903060f09051816081903050a0302090f0312210411101b11090f040c0614070204061d0c09211009050c 62
    0x400c0f0b9465218510103449034040c4052984e04548900008109480c0705030740d020b03d010240d64900420f030400e802802501d03210b407060b00118510910a080c030405043c617000c4200291064501c2080c100c035074080c030002c0d45549120182040c5501003400340c4240c001c000c041c00980d031000d041241621101402c0300c11000c5100d070314041820314030310701902081d418890b034508240b03e50010038680700041d018601d500401d0b40420b02d807956107404001d0960300882c080d8201034555403818400d0b10703000c41580e0142401d80302c0f2241c221903008813034010740e9840c0c6140c048600550348400030030a80041c901c0c0c0b412150070040c150085075001c0620680090002c20002585000241c0c0510380180690841510303005056030181440700d4646503205042c0802d00c05a40c9074131a200c0245004034101078000e255204416601c0300041c0007400039030003803002c01c081703840d02d044d03140f10b90710390340312074400740505060007440d0003041c2001101580c2400c0c4aa01002004102401d02c1e400035140c41d2241c6903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 414266133 1250 414264883 414264887
    0x301230907050f0603071e02011e05060d020d17040b0310080307031e090e01140a150c060203040c050418150204060219030512011502070e060906040515181501 70
    0x250a12440c0d500c80380380301c0030499138680807004640080d45410600c501d43c1c0c1100c040c000f03002c402d00d131280150b5519030382c0c20551001341e0719250380305000100c1000fa034500880007c1c0f1600b4211070181c00f0382916818401085a00c1210080c0c900030194040d031030302c4e80c50104141e590700c1102c0c81194500125400640d50f4000000e44061a6254895510702142c400303024181010000c040402c00000b001c00082e4800d07101c0d07203a0301070f0000d580549010f500e1041400704500180c0c0c4825100122032221101107603000148189007a401003000da078030380b16418444644849038224039803051625a080fa070cd00300050310044228810074140d090940a04040002c034040d501c240005038000300900401c0b00808944d40f042907100b414850b091608061003550002d200f40c11801100c1c070300440810025804102d6007000f41400700c1c01c070000307150000103c2d01da400041c01c0e59000d1600d0718041000383ca82d05018010011003e058281604000001041640000d0755040b5680c242c5500100d07080d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 414267383 1250 414266133 414266143
    0x70c061205040b0f1b0f12010605070b011401021f0b0f0109140607050102120108070e0a060b091207030b070f080f04020906131b05120f240301090203012309 69
    0x398114101200c9541d4001146001500003040d850354044210101101c42c0d17484030150a03607081004070540c0340c0a0742044040504010382009090000500031040015105e00005042d6101c4483c14003800e00440c0044c0d21f012034103040010035292002ea8107506910540c0070443c40d90b02225130325008001d00d4019200c0440c0d5002e02020869812040748850405070000e0009a201e80001032070040309102100c45c200c400e0f0010040b941118000300302a40090040540100210f401004614901781313008a0a1044030038280c0142540b070101c3c4504601481048011a040740014a0034589000e005083c1400c0210320008140b5280100d00c032130004680540c421980501907070841d0302c6420402c14442502d400300340c2445d4031407030804548500000f12001a115640300d030f5417039007804951502c60700c0b00282001200c040d01010400c1c40602c02c8400001502081040c0c0b601c10b070410007203070160910704c41c0a90150700305550450640e208040191010342030303c0880c1515150300d040c0d50b80321 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 414268633 1250 414267383 414267391
    0xa0c05190804090c020a02040911120c030d0c15060303090f09140705031305030c060402100e010905060c03130b090a06050703142b14070c0b1303050f070c061205 71
    0x2050601c02400701014951284928051341d004071032035401903600103000d0b18959081210710794450080c00c00c0d64102841080c1006e00c000c1c010b03001007045000840d40d9200e0a00e110001c0001300804042445550098180c0716010528280f120741c0d100e050140010381c0f00e2044818905d1200c4c80098090442c0c0318050058610b81c106a40544503801c00301c45c20307040035002859014555084100080d010070080c020790b00c409002c0e005600c3d01d8010492003900e181032840030300c00f1a440903117003a0b9200003040705a40c808c4681035101c0185104041c914042d041c0781907001401c0b8a8049070500c516000f0b001d6a2104841002c403d5440d40021104c2e030003464001404a000704445100700e107146d80207808400015800d00c0018104450301c0c8002d001c2050719803502668500a0f82d0703450084121480c0c1c8426141040b02561410f0750340c0782c1c00c8460080001c0c0407031410f80c612004140c07140b0103d4205921408016840703040c41d00307140c2d0801e444d074032442010803184820f204130780c02070380070f05403103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 414269883 1250 414268633 414268643
    0x11103030f0c040f0e090114060f010f0e180402030d05040f14011b0b0615030c0a12090b09030d06140d080c010608070902040f0f08060711070b0a0c0519 67
    0x554030741c0c5400e0740303071120003820000a00800384804540c284400600e000204a101d411000a080402c0400e08460a0194000041c0000c40030009503898803622449914020b00c0e22000d50000c01400303d6448161485c5150b01c8408248601c8031030b407010f842d00d0701480c001c400b0f8900031030384080c05545510940c410840d081414101c1044a40e42d000d14000d20352030b040c100000d41e00d0700514507038405601003204603107a006e00828081c441c100341101542c48042d4003030403840c0d07007403400c4005024002c540600e0300f0810310717151a0541d903509030040801c0d07983c0403d5031421810000c40c0c90381c80e07400100568071428a0810b0000c0d502400816810312a8030103040c480401c1a9030311403030b000d40e0010300c18a04d01c3d92282e00004440d02c00704250070042c101c6644c01a280d60a10301c121b42003401982c0840440003c004050000c45404151290041090300b84084061090142141080c00c56845071119034000700d11281e040340c001000001ca5072060040d030306c20850b260484c1400314400100540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 414271133 1250 414269883 414269887
    0x3080117070e07050c0601030b0a0506031f360201080c03010326070c06020f0c04050417070213020a020d0909090b06090901020f07140c0d031202090111100614011103 73
    0x100c031003001100c181e00004030b4545640303868468100c1130300d010400e9000720380d904a49c200300150049a03224664000c40e04130090705030301d40c1180f101000b040d4403a01001000b90340f40210301041101da5140d04a0281c109030541c0c10750f001c5441180c403002c600605038082805280003c41d6014000c0461f4180c07640030000f4201311041800304036424865181000d034405003009040c01281c40188540c00800c010b600500e42c100c8490002070500301d41c0e02d040f600880c00c200501000804510150f16221800c11919841d0848c500000700d0b55403449039070310201031000030000e0060340d01181501043c41c0c00e45404a40f00e9542144a01700c4410b404098004000034000c00d50900e4103622031030f0440d280c8800581884418080c0b00301c0d5601200b0105d1780401c0017240380b00f4408080c850309100110843d018a0a40708688001d000720381509074000600340e002920b580d4a0f80075000d1260b02001000841d03180c2c4040711104401800d2074040c04a0b800f6424210460380c0d07208005111009a044000d58 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 414272383 1250 414271133 414271139
    0x2031e09211b010e0405090f0708030a02031c0b0603040302010501030c23010e06040504150315060b1602180f04021219030c050a05060f04030806090c0f1305040f090308011707 77
    0x2d10782a4849503a5040043c0300e1061060f640c0c40d8051240030380031030740c007405081c3c1901b904146800e905070301000103038100707110000680b5008010398051603ea69811441c480078066844010895100d20303d50000c4084140424194154040c90690707126117010303501140c640c8027814102c01082c0d01c00000d170701d08495100055109a10b0000c00c03501c081c08240c1803c0d1544005003d80b08002d40f8030a009005141c00c0040c006514000c0c5103214003404100a41400d01540e504544110250382e4202010201014210344030b05030210062014403607040500e0a03c03808205c2d9114042c1d03002c0c0d00c40c000711a40d1a59040020850800d010080200d00d04c2d50148d84d901500c451907510016a20350048207280404500140465441803a4080742d0203054030301864003400d00c07040500124003485450042090f503002140c225006800d10300d510795190101406036548103080c5410940c0c020b8100003480161506a81003220b01034803d84401c0d003e0780c1ca802c01ca100c030761001c580607459580401410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 414273633 1250 414272383 414272413
    0x6111b040c030b04180611090a030b040302100507081e0601050a0e04060819051b0105030402041122090b090f010e100e2706042102031e0921 62
    0x111944031401d040c08140858500700113000c4507204054403603140826140300080105600c24004078180403c07000e403c00b14180049103e1403028040202901c1045012030103160081006041c80c102d01d00c010f1001d450076141c000d1007150301303491600d00e56036003a4003120011903681d6100e100d03100603551541400b802400403a4031640b50002c6c02e030056515080454080ea003809043d81c480e41d4446289198405071420518010190b82284401c1c103181500031520b0303a02004482d00b00341c04580c041100b120070302c0f004035580b140142c02115001034500d1074011258001e07111045a46074102049180701003005c4c0300380c910040b142e840d00c00400d100180400d00540004640240d090500c046d8a680c071801070703540f50070040d10780c62401c141c0007100ca5a00490280c06400ca10849405070600c0c2c02c05a407582c1110010a80d850103065002500103400da10800c00c0e0b81d0f14060040d003c0450201d40080498a9800314035480e024440c501c5803841e000210b24203e460208400005140f11030982c001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 414274883 1250 414273633 414273641
    0xa09170f0d031d0a06020a1107150c1103061305010522080705010908040603021206010c0f0f0201020f150a1503030903110f040501090b01020c03120d0b0303040f030c06111b04 77
    0xc600783c1948419819039102400700401d40f5114400c8000582d900c18070302000e40807600254000c801030380300d800280100b03445411081c8401d15582018502c4480c1d600c1c0c00c0c0b040c00c04c079032001901403148030104201c1070032954064003060302800c000c02150b26281e40426899429003040040207246502482c002030a000c01005440d000d000001141041561000317000e034800e0317100340000f036000700d4000340e20b0b41002d0006400c10824248100c0743c0c10945d440000c402d00c00d80000d4104103400c1501c00a40e4001e101d20740350300c04610140c40d400c5000701d00141a0000588610218503d002c2c0c4550114110900304000d07203406803660f001c0c8500e95600c48405080b4424070ba600710a0031a0180f801e600c4501519000e00745060300481c101d00000300092800f000754007803c0c8240d00c00400720184003c95400c444610054080100c0c1104212010a20f0742c4119803001c0c03c8104800000030074400c801891005403907aaa4030307800e41c1d4190000c00d03941ea890710001c0c075800d51a0852001c0091400d940 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 414276133 1250 414274883 414274901
    0x3031a0f0f06040905011e150f030b0d05010501080a0507050a060e1201020903061302040e0a1e05030405120a0c060504051305090118060c02250302240a09170f0d03 72
    0x8420700e06034903041c038075054505c2a48000442c2050100301300309460700c41c0c0c03240c0291004001000481560080040001c0b170441000d40500d60f403100099481c1e114401c4200203644c00c0002072003556511030303016944004d4900e0a807064018110041401d01d803082200080b203500b0703511940c1040c0718004000384491140b6445000390760070845c017190b5031400d01005200d01c0d400001c80c41004854018031082e1503080e040240c490300041e801d90b002800c80d08007155625000c000701c0300b0f075604034070f48946107225039040561301c988600d032201c600b40400035074a81c4581c1715070780d580c002d19510701d81640e4501131801001d074000c00d65030401a8050407580502e40c0441d09400104050442099040099440500a40b50f158880c0c0c0c59222164040005144c2d0760300c5c0c0303c1e0b0300545800e24004050950014000244101c20000e10288072401c0800c410070f0400446580ca95985090100640034504034452454001c015210220030a940031510395046014080905501000319104a0081510741 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 414277383 1250 414276133 414276139
    0x13061107030614160f080106050d090c1404110a0210090c0302131b020c0307050603040614010b030703051b070615090c0503090c030d23041208030403031a0f0f 70
    0x110000040703015402500035624141c0c00f8207045041598000d00c1c08284030380410284103003100a040f01c264404441b0b81143c0640c6400303600d5070002d00811016201142000e88102c2012034041024641841040625002200c00f0889900390422400150041d40000c601680100ba02c1c203e030071b901c036005102d10920030103021781d886450780d00240c81102028410400079990302070f080e2102c190151076240c0122240020301c00c0d244441c0c0001e40d100d091b1300460b80941404808201045200d41101c2c000403c1007500d083c1d150b031034050070109038004559540c00070342000d010403004000306010756104020203503041d2901e0802c1d02d40354060202c0440c03485a102c1d001e140000d020001e8850580f2a070402c1d07980c95640e0605000b0a4984409100350340c4c8650081c07840722002c1d50308101e045840c540f0140240080c0c040900c0b0010349800380d580240d0110403150400030401c004a402140b1072840b03610708200307030b100e010001a140025041082d8010751000030003581c1d403511540c1d03854150402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 414278633 1250 414277383 414277393
    0x240215041b0e0106030c02060114030d1214040f1e0b0f04171b0c150a1809090309030515010807090b2701150f0906080c090a030503090114130611 64
    0x640e050082c0c01c2c0260720101c0004ea541009200302a4103001440c01410300381c00285088c04400d0000e61502e00c0c2d920310406010b149000c020b4034a1980e001000700d00342c2160011410b03d024246810103032101c240031200c440e0049101e410610440220925483e008135008140b9582c0170a90f0310b01c0c05024000303443d030b0000d50b20b107416010003180046c00f200f400c4000c4400a080000784061030650401ca125100d41354103840610588424000c0d142c0c600741914101a041c900e0044d00784035404150002c015842c20000d807942455008061442224450740071590161070040c01c500c8214000e01a03040305410074001001101400e400c02640184d0080c16008806400304000c1e0307801d071140e0b4400000e0f000c04401000264000065114a01d415040c030a51042a01400a160000c9409a40b0030702402c0c00c003040207031103184166802244040c3c405c1184a8030790501c00c1d501d40182c12054005100184282c02c0c880c00d0360140e800c110303030400e000285d0505000c800c0d941e500034041440350394418 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 414279883 1250 414278633 414278639
    0x406120218030703080408010f0e060c0a09030b13030e0405070f1d1801060908060f071b02041a0f01021605040c050702030706030b0108150907110313240215041b 71
    0x3d00000000358410b01c2e142da035440c9802d02d46401e40307000c1c1000b154074900e860a016046000410303104d80c8405c0741590140e507000c100d02d00baa01c450440d0406040642120704104c5440324a032010304400703002c2e4036041070f0b0060b804100000d0300c20403511800050003011140744542d00400080503106d0040340d060f00d901c0d0902c1c0c00b061000501c6941c2c0b56041700d13100b0041052940185014000e40a61406030401d032503c4400b503820b0180191004040000038000c000c0b00c2d40203000350510190740100240310011002402c03120b05140503040703e00c00c8c103c40c09074401c20340c0001900c01d5288032080015280e607203000c080100078640c82c8610018080200000f9005a0b070920a260140c00191030004040b03000a0004145a9000b0011280b030301003c01001c0040c2d495090b050752090403441c009143c1d24480112500b10f01a0300c4119040c1d11088002040321f2071801000c42c0c000c90740022182e21010304c1c1c801281e42d44030240c02c0e00391040b030400c0480d020400320034044000e9035203038440d40ba107555 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 414281133 1250 414279883 414279889
    0x10050f180a062c03040e01061b0b071e02010b0a15140d0e070f08070b13090902010210020d060512010501030803070c110a091e1e0207060b030105010b090a0b0406120218 74
    0x110003003c01c2c1d030300d03003000030180106071200c40b070343d03014224030301c3c123040640c80002000b540c1d40e64040000d01000d8024000510592081c031000112012038800001e9107288400082d020300100c82806110316036000c1f01003041005801c3d0b4141811a0b640d60b28146108010b1507038a55028090700100b982d01da212034070042c42c04101c005c004052075495851046c0c51300c100c49040940a8110002c030901c10081d0300004080070f2101400d8440284001a40f0722848c80140d25007800899043c080c1030010900c0100030200754030000441d00e099803c240500c841003495400c0711800d0100a0040d0710503c01b2500d11131041d941c201c2c2c1a032181102c42c2d0380c0f01d01c0b000092281d2100d42d001300d80141c0c80d40d40352005403800382040c2d200400141406d001c2d8611041450049644003130b00b00606507804036018041c043d4a0f0002007540c0c0000c1c00800003541c58066030070065008500c1c40c3d0003560400c50008200b21514219001c0b50030039a60402c103988411480d00c0603610507901c0b145a2031190343c0607900e541d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 414282383 1250 414281133 414281201
    0x20d0f0522120506072f01020702040f050a0c0305241504140f010e031203151804050622020d03050403081317070b030a05100810050f180a06 62
    0x360102d0141d0701404540b030450f01e4114010118820448240f04110702102c0502101694000403613183c04802042c5050a00900070814061750160504030f488003805869407100f40103826850f01402000e0141c1825030a45805070303110601010760380b45858000704000c10758203a181c001031944031102800007880c58260096003000312b142d164500c2c40d401384d1500c4548507072181400e0070b00c5940110107200194032001031101d1114010310000c00211407100c4108400c0074000020101c40c0400311030f842441e43c500007190101c4162044802148182c00d00804090300b01031b25860000011403a5070a10040111b0000c0131418440203000100006401ca0081d10390070000c219000b010307e203030981d441a60178018101c9131161300500418003e610b440030480350304c546450000b24164591030b442d4114083c40d81e104040c03034000c50603038103580842a00900c2c0614010300c0055080d07112001c1c640840d40c5401d1681485610a0b14101d00160b025006414441411440c0d01c05068a0f108040108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 414283633 1250 414282383 414282389
    0x182d1a0a050d02042a03150501170a020405030102070c1404090807030c1a041208060103053d060215010803040b04060f0c32031812030c0d0e03010507020d0f0522 71
    0xc0340310040e502443c1c4c0b5100300da1284061075040400e091526002a00f00701c0d03100ac80446210f04440041c80e80c80d0744c0e4040380c00904000c0d008664400290801c0c0459100501544c5c503011180c02c9030b01418901402000121904824010319007013032a90259035100451344200c03001c3c2052445540f0301c8841c010050b200b07a004038030284086042003001800010300600342c0d41410300c0c110178407200720341c401c07480340c002c0e240004001500c05804c2c0c4c41030f1000240b2003449091410820020510300c3e808074440001c40504001d0050130390305c8014040d128080c50188480810b028401040800d01c0b4a810041025050820b64624041d5403500b9180a0442518503c800107242200c1e81e6800a014078140115202d400f460804a608805807046150101d000e407050204081e1856461424011580d130100f428080b19843c1713640801c081c11401141084038840d503c0d01e00021030460010400304501401a81c0d200c1000c605030b036058034550030100742c00b802d140c0e00542c610111151311f101b500107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 414284883 1250 414283633 414283691
    0x9020408010f05040b06010c0f02060d02040509070c05150712050403020f0f0703020f0d03020715020105160503042f090a02090405011d01182d1a0a050d0204 69
    0x5124240340c045425160020306001c2864030707050400000c81c900850564000b00b003480d06029080040c01c064a038440d400c6806907024030300046503801c16007641c5c01001280d0040d2071040c1c095850000940d18181425000307007131500f18541e407050f9800304003030140d4800c078207003010b82c14241c0a000301000c80d00c0440d030440142e48015410542c0d20820000180c06800c034000030a00e0794190f6000c2608414000c5185020700c3c401071240742014004e100f084054516030314502c4480e600303800f000707003c4c1c1410f940148500c41c0020310280c038544900116031180380c00c5015869560354a45031102e000018543c64000d5030784a00070b103407440c0e4510510a0003000f8440015031030f4203145082008503901a404501110700c2c66094042011450282504407012142c99448060104420380d01912000140c001c08a0000040c400100c026003407042c02450103400c10069001509000d0707003210704088003503500110070b50040216107480720000c4410b41c07000d4400718162241081c0c001119008410180d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 414286133 1250 414284883 414284887
    0xb0a09120c0209010b0408030403060506060702030f0606090a090803071d03150406110702010c06091a09030c15070c15140721050f04020d0c03080c0706021501080c091f0902 76
    0x420b5103401d181c40d50140000258241c5840d160540303099a0b846144030040c405030715040050a070b0b6a511040d26805038024080e549449002c441c016251202114214840c0c1c4502c030100b05030304400e10550030420b600505152840e101c1d80015200030310032040c510400d00d03095190b180c3e55142444074150101c1d1500c0700d110a814913181036800e43d8508e680b00d2a00000c180301c0807015070381c07150a2841898004c5000940103100f401e02041041c003c180300f482c00600a030074442c8a1000000600d10102200f01f66082d154401c01b40610000301035034410006090b00070340a000c00c602d02c1e03281078444000c01f0001114600d045e042440703010101d90141c00b26020004400c0b410b41084160442080c08800030440740c40d02d150504a21407015001a000d066210940d03400c0001e20001c2d000913640000c00c0b940c55031403400803036a807184280144001130051441e9108842d12a801d054141c0d06e511000d072140003442400e12030800c2000b48034000003407a150802003007541d19039001c006000e014001503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 414287383 1250 414286133 414286157
    0xa080414030f01090f02061b0303010f0302040c0e0f21070f030c0b03190207050c0a0816140303030127020f0d2d1a1302030402040c05040e040b0a0912 66
    0x141820b80714424400d9903410150b0b102c1c00115091720b9480d40c0307039045400c40d0b240e41c09031072085514400322410000c1844000008a5004d088500c0102182d01c211000e010013045810102c441c500440d4569130855a4420400c24510381a030702d1240317140000a6041c40c040d81c41d00202e2805100c2d601030184014525400d00500c521000d00201520f4050796040ca541082c0803041c200c001c0510800318003690100707900080000510a600100e8001040c2c285045e40b1040785548801c0b03a003000700c1c1111045100001c14904031041c0c40ca100c50014040c600b9a86042407a42c0200c9002d40c40c1c19240b0610808414419800d1001e811080b1002e500c6c1e5440700202c0701c604040300d001c070882940140680203074114510280d901d0840781c84420101140346056171203000405072903411440e41c04006040c100d480e101c45540550310a6008032000e10011807140c078140e510f4441d501840100c1c41c40d040019020a40040301c0c2600045821800030340e044d801e403a64600d030000340c1c1c08040000c0303080d00c0c08 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 414288633 1250 414287383 414287389
    0xa06090c0608010807060909090206040504090b07030516020303041719090f06030b09042a0b030402030d0e03060411010905090108100624030509012c1510170a080414 73
    0x1e240501300c40c10052040303908000d406050050a4803500304e80755104ea010702c045407682d000782d5004241c080e106111840b514038280405c11421210180001d24000c001881c40010000c04224106245c0185203941c603541c40d14000c0c18140d0f00002038102e01041103116609281040701103031596540c614495a003480390895501041368094010103040003c08200c9a480024260b000350388050090f0313044003085e2000030f456100484180816101410000f441107940c4000e6114a1003203050b5034103e215010213541c54004500356030b801d544880002400a078000c1d60000103004141810341809070340d4000100119001d0b08500e01c030b5041090001c4000f1114003440020307000d050500d80c40c00303001d9540c1e07024134850300d90150b00300361b114000324107000000c3d4030140b114a885840000302c00d4003507284805012581c1c0b801040f62080b0007592102240751000c0d9805070191429503952503292480d60b131007444500f0b0b0341400500840d07248200041d2558010320003480501d80300151500501c0030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 414289883 1250 414288633 414288647
    0x1323a051b06120f130c08030a02010e03031608091603200102060603030f072a0618031a0405190b0901060f0f0b22030b0109050c120a0e0a06090c06 65
    0x400342c0901003d004940320300402c0844035610140701601c80540b42d852100c2c003c0680301001d4080d240e4613a2160105003460301000a00f10a01960001d0108500b01c03480c0d25070300e01c82100d0094842d1854002c004006104080803034100c0c0c2d02d4000c9072405100c81c030398010280910340c02119101ea00080c0c0644a155400c05141d07010fa00340040d2a8619018000c6500d030311600410800c0d02c000080c400741000000f05044815000707900a502c020208142801604032035030048070042004412005a201145466042500d60180d0781d0015003541000b40c00c0341c100c3c081c200711080e006408600000308504911005040e008541008050034045145401c40b0056000860302d40c115a106012100324000103a0840ba030b951400c036507680307440c0c50140c0be0700c4101d01c3e40101340f00408000418025a62180c0e81a41e10a000402079900c0f04041d40000784200c03080c00300c4071501e40303000511440031a485a00c61852220a07105c1e800940c1d9554803c54403046021140b02600342810301107960300c090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 414291133 1250 414289883 414289933
    0x60414190f0f0f0e0403020c0906030a0f110103050f1312171306060b0f030c0a02010e06190528110d020d14070525030909020301323a05 60
    0x3c0a0340e00702078400945580150f10164025103117400402c104bd10b081290003403850b0090702c00d080e40c011500d01440003441c151203a078002824000400d12000342c00f200540500b41c0e41c0785550460b20103039500c41c000d0020300d49100a212114007441009403850360407030f102da68400602400c50405c1c0c070b8440102d03042134001c1d681400051045500c60609502200c0c0c102500c40707105504c50520440490240c031a803d11032000303024000030701c126481c0b401445007403c84900c40502c51951054001454100c0074032041300e200030f60341c807240002e07015540f1152031a1462003e151601c2031071224041079034003103100140703c265610085210000e41245041c0c0080040c0743c0705213001c05146910a0030035400c0c0341108550340410390741c001c050140212000034000380505545a41e580c4104c2a03000d04400504002502c0042c0814082c01c40312549080e002c10007840c0c2518400011200c086014103c00c030110034035040c0c0c440150340c001e070142071030119200740f0040c100320004000030300008640c65 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 414292383 1250 414291133 414291149
    0x4120606080313170c06070503070303050601020a030507080310090e0d1b0c0515040509040602032502031b030c100b13110405040b011214060a05060414190f0f0f 71
    0x22200c1c40c09514520303500d104440d80f940c04a082840381304401d60608202059460344210700003510310400c44040098007146000307440410240d5a00801a600c44c00300c260018005541000803038000364005001e103070071001c81814500c0464503840e891040342ca8202100c1c14907407040b14010803003130740400169807581c05100050400c800d01c1e0b84a219085041c0101e611650701006070601144025054900070440108500113038202030030701c0b0f8000d500035140d21510f48040342c1c4108401e282e410044001040c44c0d0700441c540307020500144010070340c00000c0b81ca039000c20008007170660700800c2841d40001404038001903030702c01801000402d114544140303a140b410402d41500410000d01034030701721001600d020440b4110f80c001240c0030303c458004040c0143c5006c07862400d80200e884d805112701425074080d42080d464000704410340c0624880c007844901d0034119907080d400d1076000d091103c003c0740702c54036055469542036107aa681640101500300010001081a8400ba03107055000742414 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 414293633 1250 414292383 414292387
    0x2090f07210b03010501080f071d04020d020102030c0a0b0103140102090f0603060315040501020a08062b020402210402010201050705090306061c021f0207060504081b0a0b07030302030906091603030e01050708041206060803 97
    0xc030241c40741c0c10354002c000cc0d1151901e085000c0a59009008484c0d603420200c1c1510030b00480b5240c4134009901c20b0009030f070701d03001640c54020350340414802c441100e00010016061005a501002030700c1c2d02c010710240c0c060045201d0392003003211a03081e03940658810703000982c0381e540c810380050070311200410151080c3c002c1b10051641c0381d0340c44038001411605413010b2032811303c48d00200f006407180f001c90003c05a0346880040c16110700e0b00390f09026034401d034007c2c41252178048048800c1d01440c010154181c000101280491400c52403086031008010a5401e51410b150002a144400003000100300c1607030a10218a4030340c14401100a00500e0a204e41020300f00420390fa81c0711003084c0032101d1980207000c10020f50381c400c038141c40104541103009550720310519004010390011340c2c80c03800d81e03c5000701142c12480085441e5881e40e000f40901400540703582c40c00c603411030307110710f43d0f0b41405001c000ca81c0100307000c000104080c081840c540710405c443c81c907180080f101c030340e84000416001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 414294883 1250 414293633 414293669
    0x1505160c060f021912060803041d060406030602120403020d09030b0c090d0804061d1221070b150f0102120d0b040608160302090f07210b03010501080f07 67
    0x100a1552607811031800109441440802d40091062101c0700e510400f0480d040550306900c200d0004540c80d407035405110b043c0c0c5d110300c0c15590303000e9800b400c511900303400907480d40c503284c4c50916235000300c000700045178040e6a0b80f034080803a4454241c04e4220000c582c1040245030301080103c0c5094414074042c0e88062864544034180000901a144800400a20f41c1015034a4044c2080d455403c4200c1950b940e5640351302412090b8800e1590208150405411081e450b003411200500202040684038201401c003440c1c0031107052003018212000c09001000c04600002003461213a00104440e0000c2e404003c20040d07201294040e00c0d045602058141e5016070420040d03800780b040c0040c3c00710708202caa900103000340109070002c0302c55206800c603210b10b11415408000440340256440c03215500c07441002e80c084e9404036002400b141030300f820080c0100420699019a20120070300154969622000030700790f41080e0720840e500c0d44020340d03591030300d0307024020b400044c85d6812800b0580c0302c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 414296133 1250 414294883 414294887
    0xc03090a0206070201180b031918060b0d080c0304030231050709031401020a1b032c10020105010509060a0e06210d020106032001020c040905030c010207150516 70
    0x400090000d0290b50b001c02c0318400c59000d80245121456aaa62808840d40350403101009030812110480300e0031400610684005003445824211109007a0003110445d11303803526400b918500d810590462107007035015010800c1e80000d00311204400703001c0c61313950b481c50041004200b4501c1d5200c4824503a1300315040c0200c40038810340e40f03450301a140490b056880c540192036046c0154005848001c441c040e08491110640c01072210b9040d58480d81078505000000e0451520490170040225041208001c003001c282480220703002c80c520307030f405c2c01e411044020a860414001603000584e44880040c086494007000d6a540440251303622104240360031500090f800c030241c4894001d105034911640c4031004501d68150040380c21046640719440c2c0382c030090007417503188002e4451034000d1014000603c1040207032610802c05a00400d0002d00b00e40400000304075090084419120401c09810320358020f0018200392401007580c656001074a40404085e1030b0000d0070a5554406072400745900c0b9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 414297383 1250 414296133 414296143
    0x2062403060a020409110f071101110d0305160e01020303151302070321020c030d1806020c150f01230a03120f09050f030a030503131b03021e03030405040b0a050907030501030203060c0309 82
    0x5404c0440c80380009d8a80f40140d0300c1c11103920b521448c60082c06014201c10303070540c0025000b20001d40d0b014581c00340b4200c00325080740c0700c440d00380e00581007003010030322407000000c15a0b20810024500d00300840400440000c0317921100c0100c0126450844011002814800903900340b03404440075450036004040f81900c0c4c1c0b0414085d00308880c2e541c08002001e1203503400e1fa0100c3c5500417803c41d601c03084042500c0e591b008120003410b206440e94001081600e0146034207040303030389006180400c40c0300c444a6103c074100c1c0a940b40d810402859002022070028440d14180a4050b10341044485203038100800854454100e603014000b02d13400190a500c0000d510840300d074040c036040d612a150600d51090b4003a81207800b401d100e096a035a8100b4100503c0c0800803684200c0c0c072003040e03c1c550b20301020010345031365132a0341c15003041c0400c00482c203113500504ca003850000c06440d4120386400001c1c50701907066490070006070b40c640042c0304500303003006030b550080d00c182003044c00c515102c0c00484e656 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 414298633 1250 414297383 414297397
    0x806010e011d1501050c10150806130206121510030e0f07030b04080723010b090702160312051c0603061404080a031109090f0907140102062403060a020409110f 70
    0x101c000340a06c42281d0038404c3c012040b041c1030040c407507020f005107401440c400b140295185c501543e80800c2d03170245501c2c0c00c0e05005601074001c80c18400d003210b00c0380001c0e00007882d000309101c0031181449640c0d10391886070f41c1148640c034001001e90203441d003540760940380100701c14a40c1c4010000c0c8046130b036000c0c0440e84288e01160960ba2006a45840424903d0030b0001500748811005d030644c0b40e00044d00a480c49046c2a9403510140e41c03210700490780ca40d00031503410703041e500c1041d092020410240c04241c0402050805620701507101078107409010640d11454801643c40c8070034403c00143d409140c0700050850a0382082c2c2c100381e126512180700e0641e4a106050755410034030ac0d00801d00c030948941e24002003108545140064221381044812526450035008071a008249403411140c40c50a00070107900604550756261296840c502e20f6112101d81c1c402c004d1071500165a00300500c0b4030400c030244000d0703111440c1601d00307800c1e1503641802180320300c410320103040b090980c00141c40302 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 414299883 1250 414298633 414298637
    0x402060f0a030c1d1e060c16060e0607021807021f050f0f07050406050901021c03021305040507090611030702030f030d0515011209060b09070e0f0a03080703050a03060806010e011d1501 81
    0x2d8484241700103042807150414140b06130090a41944030408010344003000c80b91192100ca14078401d100400040d4404c0c008000d6004412142003645c620000c10001da0003440d9004961710748900d100e07682552001015800411901e80d0300b0170810349800544150800c60350104030086080c0402c001e03001d40554040d80041001c045800c1c03034161300c01c014800d0030450722030948401c0d55004100a0203584a040300c40c0305500284400211400d25100709803013114079666800c1510700f07114080300d00c41e18902d03102645100901c01d4102680d8144000081c210011008643d203007404010003042d107900800003007561103000b6407032515907000242d601029074007843c0040e5080d650b10300310004007030080c02c05030403048100c20011500d411011611101038100c4810480c1c1e00c0c40310410064400a000003485003805011301000a4010320203000040030a080105400340c484040a141031401d0740801c0741111b602c00108641103203000d8000340c180a5140c62034240c41d01e074140005078211b5004540c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 414301133 1250 414299883 414299929
    0x216060f0b0337150515010203030c070c0906060207170d0801050d15050c0d1d0703030302030c04030807080706050603011b050d020412050c0909031804050402060f0a030c1d 76
    0x3c8049200d20340c0d00c00a400e2000d107103035145850b0030241d600d9900480341c5039802d46004089600340100d5030030342e940500168002c0d0315590f24000350452540140c1804c5034510b00080b80031a030188240210030140003103a004011845c43d1085003c00f04012090a4405405c043d41100300e807540f15945505560381550104031011042c039103080240b03151022001c0361403801e1306000000c810600144003a81095105020f682101a040110031021004201c42544840300410020380aa00a540c0c00704e03110580c14181a540c0d100d071074250b40218000c50f008100001e1800c10000a4031920703410220503402002000040c414010300060040c40c00d50034010081a00c02c0048055011903018007904950612005c21f240b4010781c3d956800d0203924450004007000995081001041d500c18076940d100c80960710020b00103010040c00d000e841a81c01a1080024071b03080a0b59100070610307506c590340d0000d281003d10382d004010002c190440384200d6610801e40c40740ea541d2020b0541e43c8608103030005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 414302383 1250 414301133 414301183
    0x160315021e031e161707050408060c130b0a0c021e040c020601050315071d042007060507020606011d0d0203190c050604050625060216060f0b03 63
    0x451408689042045038035400400c004180c501250640c201e0f020a064041154494104580c3c2c4480d4402d0300300c002848290180d1002440703440c66642003a45814070500d0030b52a100b0300d0342045812070340c0c40c41c0d450b000601c0702040c00207800000000c041c1d099110781440501d02c0018003482a100000e449801305400140989001c0b09503204503100090081010f5048040083d4442c2c800740b20703072442801410ba0a0700d031804e040700380920400783d542d600311003444a154144680388075906490b4000e9900c14007003080c40c0500c1c81c3c006110710b980940903142c6401d440d101c0c040d0340313000f45128210741180c820310880340d80018041c82030307403000040c41e0081403020003c10300d040520701d0041c1d818811000442035000400b8034051782a40a41e902d4100c41e0f880390140135162055100f810381041c4200613000c080e00c0c202c09224022890000e000340060a552a4041660003206044046441d050142000c03c100b40c490807440001e100000c0c40950712103030019440c0c110f0301003500e841e04000a010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 414303633 1250 414302383 414302407
    0x20c0105030a09020f1e030c030d0e0d14060709051c0b010513020706050114011106100603050c0910030c121107060e190b0f070215011403030d0e0102070516031502 72
    0x46243d81c1c4080c1403000c4894610711120b509140c0506c02ea40680a00d081c041700600b030110744c001107907040d901d40301711510840d03050056080c40c003c8c090703c3d40c034490181018020b900744074060149816694440780386042c6810841041d00001842800314100404540007607400c5103081d04542003110400008181254014040d00c5461801010285490300105031500d8514811030705942c00c1cad07607a0745441c6148220303036a12102602c0540d814042d49100f0041c00340302c0c0d00903a5101c48400c1c05e42c0d044c2100384000c560088903c650b81e1001c241c4400210320b01c290311001c2000e0b1054000010b11101d0040700b5245140d02ca901406009951200c0544544900030045102c455002100000001c0441e040900041e00156001c2c4180307141c4402103030310b842c030008030080301542c05881c55405034a4414595601424041070b1909400140000301d1800f01c64804c60030b200c0c0c0703a4000941e4841e42850400c0c01e101c840314881d51890442503090010900c496480070b610003000c50010790b90160a200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 414304883 1250 414303633 414303649
    0x507031a25091710151404020a03020403051506090a0c050f0702010e03070b0408010b061c15051c0b06010203030c0f0a0c20041407050d270c060906020c0105030a0902 73
    0x460b15100002e20903001d0340303070005684602200d5a0302c00304402c17071400f034001c04c40c0c00452142c0c540490b0f89003c54141880e0650092400003c1800c005141c20765135611141412810100e48510300381000401000b400c00903803190f44290345c00c074200400500da141c0079107136004107200390403411004100f1108590144003405040030008048581d00f40d5601d0202c503a5501a0280090390b500700100c1c0035440c1410300a4440903408641d16900104100c1d0b00c800003040b00840c50792001d000b40c0320010300354691540a550035030030000c041900c000d043c1801701e10041c2c05800241194020402c004d06088000181c41031f0210300c800050341c54007034a504403140300070350314007420489403810501039110b408080244440740c181c80a10001d81c1c007049004005000300d4144000c40c404110101c81d4820561020941c000c984807130041da07039422140000340c01d070000701c02c545515221106118458102039001c00400c0944020b04080340b0b0310700001c041c1d01000d82002e040c1da4070743c103e41e01150341e1124 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 414306133 1250 414304883 414304889
    0xd08090a0b0c0408010c020c130e011415010809060412050a0e03010203010909050105150a0510030e010c11120c0a0308090a061a04060f0f14011107030507031a2509 72
    0x3502030a81080780030040c1a5101344280c0e6403c3d86010b4003281c40600105003007009440040144445642c400e0301031001e0b00342041040481d560b03401c1c600001d2022246068042c10b242c0641c06215054a0005012403c2c0030f40041c0d80d03940a80c0c10040007428460840d03060f1010b0b45007058480e0000d41058410300220300c4803030740c50f500120010400e2841c6910890100340142c0081c0b0080c2c036040b00240c40e40d41040c02541c1c0000c44c0c11002d2201b420170340b070b820801c00111702e00081c1520a91081608484e025003d010028500760011164480308020184801c503c0c292014980b42c00c40c070105039105c400341c0e0005c0034070150340001144040180852040c880d0004001d107c9e13102c03d5007102180070428516581b0a030f2410002084c040c5002c645003007521011301005040a080940c1700c41301201a9078160304000030050b400055100c140b224400951180006001041c214a00300308118140340304039030740b0341d490f00c10060b00e0f018240d0303008814031110400b420840b0420724103c9801010750 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 414307383 1250 414306133 414306143
    0xc0307050706170a051006140f030118110a020d031a030a0506040606060c020a0e0c1b060103022d040905120c0601090b0d051c0509090a09060e06090d08090a 69
    0x71200088203500404024a14070b80350f200031810340d54809040f01103d0007a150020181612402848068002d501b9000011030500c81d070341c200400c40b0341c4190203038804d8101c50380c1d070034406038403140c5440e1a0103109004000b43c0d42c400e04001d05000300030360b111240c076079203002c041d141d04202071441e402e080304103885600a03095035481a49801d08030750707c240548080714803e10344000000c0b10340c070030b00a480030140d00902d214592464904409940c003c05064103030000d20400c01c81c7e4440c0c4984c48440c0031904020f0151429601d10300400420a202426550f940c0410341034400304078000b82207502019108440c00240040d2a0520b60b18045041d0b01441c40a40002112012044006002ca0491320071907800d1040405040900034130018114000744140d00c40c00b5005c01307050007100300f600309010f0f6250241c10b0818040008044c2c0c00140d601c5a0496030f07030100c440901401e40520904d9000003802409641001410310b0396807091542c140d4200280500031590307118050126408454000d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 414308633 1250 414307383 414307393
    0x6270503100f0204050d0b06011106010f0b031909230d0c02060a170a0204030606150504031e080d0915110a0f110102071407080a0b070806120d030f0e0c0603010b0c030705 75
    0x1b40c0f0784044a204240e544c50b0202e40c0309181500c1c05500040d416041c2d03881c0c8640c00c0c902034606402c1d4050382c2c00240c158000002500d81c0014005400d10591360441d0240400c4040645030702d404c843c0040b08001c0c0007042d608880011143c0940000503400403d5050b1441552400810421150295480811480c0c181c0080a100310340706c0c04c0e0042d005a0f03008060812406507113138900041131a880703160f000815400e10080000c13035004100c80007500302d03d4840f140710024543d40c00700310303030301c2800003020742c41d83c5540d010240700c0d4046801c0c0d0407030780c003103407c1008a0a0024400b4135000d4a2102c03401c0110b0b601c4804000c511901c905600880141c000f503440b0105c0f440c000042d00e00700b2170000c00c01e2003140e000040100000820010725500700714009200d0b161840100c0d04d084000349140c3d00300c01c1014050b10b0f007003402c21140c080805599000a803201ba403400141c1602e006c0d40c0c0c000120b031b000c030802e0b480716901c075412641180c1e800e1117003030b0b680d681c01200c403820750148a0b0007408078028 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 414309883 1250 414308633 414308659
    0x203070906080d050403050d0e0a03080c06150d02150a03021b0705121203010e10050904050610050105090307051c0b090303190c08040f0c080706270503100f020405 72
    0x1103030006002d5881107030694110300c0c9440300032a05801070344000b621551001d805112000d014840b41c12414401921800c441a140c0d115610941d201240150866101c0020054054a060603002416404445810b1038500365000211500006c06880003902000038000e25054002c4d412190070746031a03110302c507035420030040030703519102540f0607240a040c2c1412404040480428205400c0e041d10f40307005d003140d00300222110401e100a00c0900d070604545400704156072050000d03071086209030024000c5160443d0094056460b5511150501409000500580e64080307000400d5071410b4031079485410780001000030702024010068060710724401800408403000c40258850b00c20302403481c400005885205003114950780410f0005030800000c1b500180c140003400800350301456008040321f49810b18141050803590103540402d900803080b450316000c0c1e02189070120342c46001560007624007030101e41c03200d525901030410982c4d18240680d4604c0740e03606880c0907040141032142e247d0a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 414311133 1250 414309883 414309899
    0x7090c0207050405010b041809020d0f05160812040303050f090a0e100b070816050c0406060309110a030308061002150a020307031811130209040c0507020916020307140307020307 78
    0x25042c042c2038000c3d03090500201d2000c2c0d4070b508030b600310340f001c084081115000b8510500100107514040f0703404180036012802242c0120b502429550243c805020403100406070405500c1055108800c10340200f41c09034054600c1c003045d01d04598160400381d5840f88040c1d02c42005100d01c0d0803c1e0b6100c444903c0108454026201081c03041225408010250b034843c02c0c0034150303026407032006008841c10081400745c0e8074401070034075090344110202c0302070209100000f01a038500d5000400001d60b100402402e12000010140380b1103019110080c5090450314018101c480080c0b4440c01400a0755103081801d1007080708400c032001c1041d001844d41800c0340e03400065401a6441000a07040032800c10110001320010301005a000c0b128440c540c40b9801484980b1580c000d41203511a42849200819282ca002c0c40d507402d115941c80e955110568070401a408001411603001481c2c150b1410714820b400100301c4214541142001c0c40d03100007842e0540c65841003120094041c0100040010004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 414312383 1250 414311133 414311143
    0x11b0b0702070905010810024009090b01090c050f1315030b1014070b04050105040605130308070507080d0f0f0b040b06030411042a0f0e0d1407090c02 66
    0x5a15070940d9040da0f07480c0b0b840310649100b07029100c1650070045603103030005501c0d0f000b000c1d41c42d900d00c100200e14101400c4140c2606030310340e5184142c0c144014403500b61410740111405840c403010100801d90301c2d600c48100e0240305020340000b40d13075620740901c2603e0144060350380c041c00c4101842d40d60b40180120a00c2130b8140d20402045003e60001e0565541c040e006900d42c0c0f11000d040038100c41c620380c000703c4155207080048801c2d80c90401c9902d0202c1c04e0b504080f071165019000206180c286880c00300b0031964001d14200301c0c1c03900c6e0b640c2d4200003039200508503000107061401c2c3e601c0d210b4170b090180c0c0300e1064004030b441544c500800c216007002e403900010750540340c425003006642d1000b420700080c3c40301002001d42c46071040001a0000e15840440072010390094000135421a0b141a00809d40959101c0341c0810501e641d0161075583e4005070881741d1012501c2c0001c0124000004508000c0c0e150000501c400f40944e5002c0e8841c10800040004104400e8140070000e00c0c610702030348072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 414313633 1250 414312383 414312391
    0x70507150c080c0301030302100b21012003060907030e010f0903080415020a020c061c020f03190b0109050919061d15030c2701030309082b0e011b0b 65
    0x100300c002c000120502114401d0b0790499802d600984000c80e00c0921410091902101030b0303600140461603c2804280c161740e14880b041f004000042c18003907400145111440c090b5944c804200130030400ca65512118480b42d00b1030000d0401041c00d00505034602c1c003500a04070b682038205d00e40440601030507800740e051405180100ea600503000304035403074001a0311600010b103015070f11047c040142030030003600500e40060403046031080d00d000405200300740ea10041000c02c0d41440441440381d80c0d200310303401d043d105003a214100142810140060200d038894800c8030310076040c1600080144d0414601c41c0c03650b554007807040112036290400800c180d44501020403803070380da080c00501480a0240f551b2b070040d80042c02420210821410046060540d6011400c0d514101000b140d100e0541e0389042e0285102c1e80380c0391442e6060803130b91413400e031001c1d6043c01e1142c04043e0183d2095202162010020414035162908200800050714014080c2e90070792074000c660040a800c0c01640c3d4254ce000b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 414314883 1250 414313633 414313637
    0x1b0c040f0504030e19170a080304050102040608150a030b0c070b0106260f040f020a030b07030507030c3605031209030c010c050d1224051903030e0603070507150c 71
    0x400071001c2c3c05d026203e003814001a155402d0800203020b6010580403404400c0400d00846a20b003020303644440e8150001d980440d01c603900420140111600520314a510003035181c0302540050b1f901d000922007400342d12016042c0c1d09604081182c0f0310100742280c081c507800c2100d000b01540e481c50002e00f05003c0c0d40e88000c44507449c1c142d4042d17041c40c021300c450013410302d80e466480e9030b01c031516141c807111000101240c0c0408290000400904c0e007207050343c41a403042d02c00181d24602001c0190554109032281d4007041800e030050941e43d550b4101c4402c42c3d02c0c415103011800c6804503c0154403200c10b8010aa05126103101510800d00060061000e0102501582e100668034001507455100219004045800042021888034881c07404039084160111008c030340e58006401c0c00d924101c2d0180e54a0440ca28400c0a00a5007001c0240c003594904900d21458401d00d55103000340041d0038071400a10451002001c150705034420800d130b845260b0084142019403600d03181c03642c0282041d103400c1700 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 414316133 1250 414314883 414314897
    0x60513030507031427010201180b042009040614010b030919152c070b040b03040510060e0f0c0412021309020a120b01050406050625081c05090102030c1b0c040f050403 73
    0x2c41000c1c07c1d2228180a0383c000e101140e250bd89607100d858031b44d403000d802d8010700c0250280b0040e030f42d503400755a4000d60040c500024182c401d640081c01040058021481c030341410018400e140c4800503901703910341c1600f0000e070703c0ca040d51f19000d404004020007103040a41418810005029103caa40320310740804e03101100d444825210707164503540716114001100e10107000800c00c40c0518002180d01c107100c2c006072080980b00e0711242044130400d0308080030000f500c03400c00a030a007030100c503183c001003450901420070307140c800d6030b45000c0d5035500028010340c00701003031020000c12604000c5d07000703134001c0605614585903204840f0444910308140c5044100c800001030300c0c1414410f4030141c0e58050202c602d44807502440522500c079443c01400101130306806c01c0003186609001d040c0480251411448943c010710120083d104003034400701450340304100b40070004621800303c172480c0308a0a207003000400003007841800d046801c01c080b9085800c04e44006814100740e440148501d102e601e980f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 414317383 1250 414316133 414316151
    0x102091207060c02010c110402070b01060e120d0f1206080616171b190e12010b0307050405070210050c0a080f071409061e07060513030507031427010201 67
    0x140e03030710580c0c4600b0700801d03580c040344005548070b52032020704540680340c107100d4420040d02003022603004510903100d0100d0710005105413503016502515a9000301e40050540e050440c80c0d9803581c1b070768002c6009100e005c440f40d242040c02200120303034100b044a810010180d40c2e000641d11400c0484090005d0461100400c44050007100090101040000c107012103a65041100c410001070448030300c50040d042c00780340e01d00c110361400c01c1a90805961501d01c0d01c3c17001e10500503032500c05550311901c0e9042402c64112070714005405400c66408075800b00c3e15441c0c0071300503814412514184540c05080c18208142c2e41900c1004141603c0c1d00e079030307540c21030307035100c82c8550700081c103542d40d0780000c404040000030040614080e240140700105620314010413070445114181c010840110702290124411051100c070b07210f0181d00c049020742c1c0d0340841c20b6594008200d4440d24000030184180019818007103014072040e07500b40c50144150307041c140090740c050f90803250403410140c019801c1074209 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 414318633 1250 414317383 414317419
    0x1c111e0d020a0b0105100909020c0c0108090c060f0708220f0b0f2706040603050f0a23070e060301091b14070311030d05040b01060207060206060d0b0621010209 70
    0x110b0712080e0441c0f00303001941d00b4401000030050b503074405002040804500400c11004610050040300104001402401414000500078620003040d1399116000440ba450103900e5000c1107542852183e54110b0703880045140c1750395030303005440c40d00000d43c03001095201101082d80e0444203480380300400344030203551400a850303288075500d2140c0c403180081c03004140300348039004820315000700340c04036001d003606000201da031681103988103000180d2614144100101c80101c1b842d0031503c1c1400c24000c460b104003090720700044090800c4400388401001071030240c460002c405104d00020487e9540396501c00c205c20141074000c829100e03000d0044030704850f280c001d1444a04c500c0c00411000d050940340d407410f981d00500f1904c00c080d90f000400c8421031070841403085500c218031400302c80c400c030f5040034802031800299402800540d072001d001c0c400d5540d0790b81181d07844185d0109001299954900c0410201460b241043c2c08028124501080100d01074026040410041d01c11180d0318010b41e000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 414319883 1250 414318633 414318643
    0x41b020f01141b07140f010606030e0d05090d0c030204060306020a0e0906090a1d0106030602130803090609061809070f030c09030b0412020a21030501060503091c111e0d02 75
    0xf000d000c9100f04628968a442000d082014014a98842c111158030801d0341040b84a107043d450a0f5500c41040c8109030701881101c0b200c0328820000c0001c2c07481b80001400754440c1c400014402e07181c03401ca000c2008882400007014590192050150326540d241040180d0407a40c4843c000c2003541010b5502420202d001034400c1c0e00081c000703e40c50300da184081d00100058071030141c4024841c284201b000100b402483d0007103104010040e0b690344010207007a4105555000715289805c10081c0729259904c0c502a00c2c1c417004c00f240c0e10350382d80b60058601005003100250140d04160880100a58560090074080300c0f910329480c240528140d520045500c0da400d4003006000080c0d01002c04c010840380d4614052800690044804902c0c043d119030300000c002003064070703c50841c1e00c01034169560600400303004020608226003941403072285941c4500041e0b0551241c488494403007001517102d0034018559080c54410303100381c0401c10800b00c0b00060702820701c59607031080701c20b84103125100041c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 414321133 1250 414319883 414319891
    0x70c0b030712050901021e030609010b04060804060b0a2c01090606080f0709050d0b0103170406120504051002071a060616330b090a180201030b041b020f0114 69
    0x1440000414540c1c495500903e4041c00e000c00d1990f09000c0d18103000c1d100081901a00404082c0e035131245002410050200700c142c01180b00c400c2c050008004264000c4041500140d20840114130f24140e000400c48101c0c25a0041c40440141c0c400c0d4091401011300c801400340c1c00f00c0034403100381c0c0c840082030240e600703a1042c03030001855480054041c034034190b0440d07088042440e141c50500ea440000030b54010710b104090765482c040c40010420060050040714401c9000810641850b2030103a014251a0012070083c80c0c09803503100007000c004042c8810980c1c1c01014200315141c68050074001181c1a5115451241e10050307800b283c500d02c1d100c0e068500c111441c1c07030403040c6002d050351aa090007280c3d14880384903070007080105084207455144414405100600000c440441000b00910341c1c0000d030007031940501d08400143c4000c41c0c00d00c900c22960702800e007c44c01d0000b10000c01d0017842c0c1d11001320202004090240411980030454110250f05440207101c6c100848a4010300d2030f0046d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 414322383 1250 414321133 414321137
    0x121104021312021e0f0415030c0602030a030b09040807120306090e16050409020a0510111c0e1203030106110a080c160e060303071502120a0c09061112130812070c0b0307 74
    0x160700760446e140641102d8103000340004150b011641d00e40c0c985c071040748030340c20440140c0c20200310028090360521680702d208000310782101c0d0a00305911603040521610402802c803c0b0020a007003122030007500500020201c0c50010007141003500610780c2c4500d01284005140d06620a001885207418005d017800690000d100740d0a50b4500b50400580b10b00009495060003100c1c0c0f420245c46078284040105298001200700c0840a4000014420010030310740a104401072680c5c401e80b850b00005590654510742008505040c046265500d09101c40c17034004c2c2800300020700500307006004a40001c501b4035404240c01865210503080b6100c00c011104560154400e00c443d8000c9006403c0f001c070142d0b1503d20052604016130540110f01804460146132151031b40074024401d0390100e40c1d50000d0a00d454840a00100394000039201c20741410018a01c441c08520350708031a50a148403001003034050308488801da48000301218540080d0001d841851065200041d803800c042d080328030a00301d036 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 414323633 1250 414322383 414322399
    0x51f0e010609091b031d100f06120b160306080303040c060f081e04061107050c03060702030705150414030c01050718030b0f0403050c0f0322121104021312021e 70
    0x1013108a00909030800840311081d00c640c0e1300c500c0484140950f48080c2c041d0700c1c1c041503003c0300320605070944030b182d80011560111410810042101001200e0300009030300c824144c0c0b40c0040c6411005401d180d0030900f602d02000003440200078141000a0485211381c0b81c0c2c0d24200042c000507980428102d4407004048118510041c881c0e42181c0c0e1940d000388110f070f000400b4281341d42c82c0c2c40c40760440742c000c4a0503444050a000640303420440b050b80a040c40c40154a49561a501e081e1140081800d044111390480041810441c005000617803800380d440032640c455180070302081c041c05099896401007082552380201e645598580303003003960b800141804140c0c0354042820718410300144168101301051002c5c0092001c148003024034000b4180c020b5031906000e100185151417503031314508009110440c01c00c4008a04c0078088282900028803064001c200408100030344200411086902600c18020810300030440c808a1124001d88a50800b049181c13071101100d006200526801510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 414324883 1250 414323633 414323681
    0xe010302010c1b180e010b0a14120a02031204031a071d150a0504030501060f150c030e03160329010b0f0d0f2702010e04051f0e01060909 60
    0x11610181d90508030b241d1034a440d500d00c8003503401c0b260313a18001111034030303030340751a80c0300c0b10074000d101c1480310032180c00100c0c618111820380714102d0402c078107008001203103d218056009114920102d07401406450314001c50b4840c01440342c2c01740c017048428400a0328842000d04201140a01c18a40d070f44035203450f012100352000f042d500300d000b041d52214201d001c1e1242c0c5110080035260780e00d2183c1301c0e151914110315001d400d441490300002c0340f22055030401c000c40e082407403000300c8110321403c080a80040c282803c8503003001101c1d0013605031003401c60480240c080949202c0c2201c0c000c0400402c40d0503022400c4a446500e03c003000b030ba0514040040c08501e114900600440501460844c0b40c42e0204401d2825181160000030301c40361f81d90744040f075020010200c0000e94030b98279920f0030074a9030756001a000001e41c400180c007459403600020441906650074842103900b18031171788841c0e07540707048080c3d29600900600340020030041000800402c14003441031b001c10400f031515038100e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 414326133 1250 414324883 414324893
    0x8070308061c05030438091816030e0c03070e060a0806041203050612030301060e0a090e0109111207140121051501080f04060e0325020a0e010302010c 66
    0x4001d009150311200030505070301c0541c6199581d03034249115101035a1038910340104c000045444014075640c52036005002210044880d41d40104842da01e640300303441d03080d6000890329144a4520034030240252000340719801480207504070030000641c1d030610484101000068456001d42e83d141c0c0c26038010001071100c080200c01c01c0764031100c0035103001c0926035240c00d9545041015074007a40c1d19200703455045003144e814040c080c0d0000c01615400380200301035040603030701d00c4144180010801c0d2030040b0191540c13200c25840c028041310754140144884100014007c14549034121660701010510040d9424044040140d2212280140800c186840c030000c1d402c424200e04141045003e08588445d00390000a840c0c0e000c0f00300b4800a214a807803901140b45850302c1c41d496041c403030301c00208002c18580b4944198010f0740300f4004150b0427000d6000900d14012100c8003001540b440240046911b00f42406080c000e000329080700d00290780f01d5450004020a00001c1c3c0007c450301d04040c00f1a03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 414327383 1250 414326133 414326147
    0x90b0d0210050c1501080d0e060406030f021c0f0c0905060702010804290118020322050f0304120611040e0619030b011413050105030c010f0306030210050403050f0109080703 76
    0x4055030408074034015209943c5820402c14055402d00380120600602001504000d02d2004d40f14a0821002d130340c440400080b41130140b8442c1408140d1100c07107150039030800c0d0301604d081c094442081d0400e175545d4140c000103003416031000c0707503400d21f4500c0317500409104108000403500e0162a15242200325001107600900c000e00517110302c01401404600407240e881508005103103800900d806504140c40507100f10f054591060489006005100b04800001c00c4a80480e841c2c0154075100401454028182428031611000500004c03400140e095001030110a07900d225136070800034544841c1c8903600d580501c0c058050b410b916840000c00c0f0b17050040c1c801c08040703442c141108110365039076550000480d00360095001080c1005600030341d4102038290600b00104000103001540c140008680d84010710207101e410080c25030030084d0031070302030b0340850003454018081c010800d403240c1c0040d10990152004035494800d6071104010b550062140001c07803540401800c1c0b52480303d8030708941e24 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 414328633 1250 414327383 414327409
    0x90e1609090c0e01030605061819090312060e06010207170601120819030209010e2e050c0f010203010614070510050c09120c1c0209010e09070f0909020a090b0d02 71
    0x48005401d000c1030310303c3d051071000c0c025403045801081c42d1401101380400e007050500680c022200003810300c0110314440b1004035000000320000940c070725460a085600700c8041d0701c4d5039070451038100c001c2800400150000d21400c3c01782c00301d5011946e503803802c0c004520b5115490341e154000d580140180702280240103145c600030302a00381040b06100e0082d203c002d5100c40c090100380d00288040715560410280c0203100c0084035051200340c41001c0d140716540c0c40000d92502c81a10300902c1c084ca038080c5003505e50101c055021a640c0240b000c03480c600030340c028001e440c00324000c0d1109410040c041c6007107034900e55111029024000c00c41c1c0e4568050200540030074803a12050001a06540f2614141401d041d9a5002419182c08030814400000005500450320403140d421000140e1104503100d811200d00e0b41103a40b441da40c0c040c00701d0800c0740a82200e0800780160341c001910300d07440d8000e0304606000315510f040096a0340001c00403030300708020b43c542040c101404c070009072a05201c11810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 414329883 1250 414328633 414328643
    0xc11030d0e0c060a02061b0301051003051803070f0c05060c030d02090a05090702210301060f1220030405070617060409020102070305060c1e03070c0f03020109020d0309090e160909 79
    0xb44600741030029010360400101180180c1c0600d04000100c600d540800254040d01e8441c5442c41d410080802c08a842080c00f4038107141d120f5003c1150030560290120400302001d082c0c075241ca85500d81004105e900201c00d84604040040100d00340c07800f20304540c4194003c4c4011458019040f41d1300000e5041803014684c007400b080c10004150300c0d44020316100b82055409020b801c000c131282507c0300043ea844507640080309000601c00c044d001030801e01d960803903042031a04091000600c10180810741c06a00e1a07940060004000380c0c101c0b8081d5014501c0740081c0c40906454a204544030f0b0f0120708600007403030b03107600428650f040541c03221601a0040c0305865110b41c490711003919109095078000303007152000a0802800500f1f2000380722aa4a25140601c1e50070400c82c02032a59020b01d00150150080080040c10103000350700c00203109501030480e01c000b12140c10042d08080d0300348180c4203090706050149a01c0480411590080c0811000264905060800c00d00080562107400c0310 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 414331133 1250 414329883 414329893
    0x90303220c03020a151b0203030a0e0d0606030320010b031527030910080f06010509031c05031009181203060504050a020c0c060a0801030f0204060308070501060503010c11030d0e 78
    0x3026072540d0030940098100661040c5d000c94a181004200300035120b15070b0b50480d642a00c0c00010394001c4201c2c0d803058080d00d0004000f02c0000c00240100002ca44000d1085280c05000010141c1083c0d4051102e4103590380e010001080e00185801d95002060182e41a044000c50b110076414030300000d40c10800001c1d030922500c0f003400300e400040035440448e04055001046400c150b262090251b12513004038940100181008050b4107805400904014140540462941e0701610108403088542513204020404c03520729030341c050010384c0140d40802d100800d049021030040740300d024003002003a10441802496a4580340d494030310b00840c10803420142c803120001110f640318042d19000f0324100f00016660440e90340703042d1900703d00e6288140203090501c40b6a40080d00000c00c01e04403034000342103c00ca60010f2000800408040e04000d03c6580089030140030310038158080c4040d02d5040d00200310110316004c040e20b000c526110902540c1d8001c020410700641e494010000900d04103040311 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 414332383 1250 414331133 414331139
    0x70603090807080c0a1707150b1507030543060e2508060106120e0c09010e090615150c0c0a0b0a03050109091205070c030c1d090303220c 60
    0x403103951310004048900c0d0b440b400301d010503c10150703044403100812188451800c1d803a80e81c4d442054284600504505580e1034035042d2035200c054001d091802c0d40c0a91580c0c409042c0f9015100360400a444115542c1500011801d602c2404505110003012808014107090340c00c128405600040403c84030f2a48078202c1303001da4042001609844544848003034a158020351a801d040e40c05940581301c3e960051004010701500048020258107803e030021a400d150590250b150a070003009081d00001a040001480a0681e9400e03004522500c15504140c4902503400b201d6100c145d80c841d031000d001024048907110300300090514404440a841800040768009040380c003007903020404013000050341102c100d40c50700c03400c1e016101c1050204401ca0094580c0e880512940c074810060200001d000c005001c140300d2024000c55100103d0078016445003400c450b080c00100104d201ca002440101d00307071400c003000f507a11a82a00102c105000b06180406513044c1592030180c9202001034008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 414333633 1250 414332383 414332393
    0x60702060a0e040204090c020c06030114010f030212151e010818070302060711090a0603030c0311011d0f070609031a10030512090f011b120909020412030801060809070603090807 78
    0x504010008941e0004510005507c068140b020380750803507108e8a820801072007804600d10031b200e0055020302c0c2000c41c50040032029402032050039201d031103024a40c000c118160342618501c42c0584030907035100c1c00000450300251202c0c206220207501142d040b03030008810850000140040d94409001c48000a5076500800c080d075000d07400640344c0c4004000f003980c0342d06061888540048121000f046000c1c03a684005010750107008000f01003100340324104802200940084d0300110000701d51760300c800d8225940f03517560714402540030518042c9440004955010310081d20490b034120210101004445d250004070040003000a040303060048000b00100388100814840b00d051014041d62754901c280c200022510001d032003a0401105a51011328210b03952024041030750300050025540b01c44200c10b0755200c0141d00008910f034400710300003074095000344400303d1880c001d8039804026600c2d01d50071124035070304032452510795101d28000c000203442548907001440c050f501d82824403c5940d01c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 414334883 1250 414333633 414333637
    0x2031e2e0311090c160f1202070f06111b04090b0a0203101203120509010b1302121305070b090604030f0501020d0606030209010207030b060d12170c09060702060a0e0402 74
    0x3120a03903610440600070407108620609655404964454052821030002400380c814403050400441c4a052440100701042d440b02100640c03040c16041510b031601f000941d550310510604050704040e40f4002030190103400c0300301c0e003030040d07801600300b5402425032002004004a030864119550342c2803a000325041d190528050a5200781c0507130b03603040c5040c8810041c0e80ca600082d901c000d9150344840065005022808401600140410a662065003132801080c00003c526085410380d4000070340d13501c60354002c0c00400251410900d07541c440c203426488050389410f0041160b0310a4500f13004010703950005d851541c800803c0345180503100c0c0d4610149241c8410129456034011400303000c0903005001e0880500003615045080c1608100000d503100c44621000d405c4030304000204825440305101ca41d0740a0700000c01000003441000020800c04c20b070b54103c070b0110700007804100132a07040750898403912002011a41070624503020004140c0c0404001e405000c21648240d00c00d1321070f800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 414336133 1250 414334883 414334951
    0x7080909250c3f0f0c0b06041e0e061602030a0c0c0503030f0403021e060d0b0109090507050c0607180b0903100617070f0e010e13080c0a0c080102031e 66
    0x8001402d1404070510f00340c9001c00400040140895003911010b030170781c40b80302c1070502034100101c4042c50700ea80700850001d2100780601c0032a11054071030b840c5602056009601d001d0324610880d155a540c0040f640801b18580014100582041101d81075452045050b24155409003014403120369990000030300e0366210240391241c030003011a0030410b6160003100c1c1303940040300c40e00600041c10440d0019401e881095903904182d50b56803010809a4030407100c1c00c0140c41b100504004030f0411040240c455001101c1d0f19440e840b5103000250344a104200074242c00d40c0465016038685d0801041072802d0704100101c9805210700d40010070004041d00446004140e640c80040000820b001100d0034412141c020140101f1106820404003c0c1303424003d044644c0b101d042200d0307484003c440d5130034004810002c1d0051202089154600002103100c0154601c04c003240c5ca841a81c45a60130300380c0c002140d4803000e40900214210001088203c1580e000e071101e0032494040b144006004107083c0c001c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 414337383 1250 414336133 414336203
    0x4030c14070806061e01080415060302090f0a06050114120711060f01061b020310020d180c0509130203060402041a130e0d09050901120c090207080909250c 68
    0x481030000b50304004140d1821581c010480441c4045c034013002804c130640182c0300401c00c44880d00740b0f200c0c0c040d0700d502c1032010b103070700502050541c2000402038410003019548800c8152600100003000d6010f1a50880f002c1000030125041412110000801741c10084c50282880441403858450820500c4014840d44103803900840950600100800b005210b11a00b4400c0c1c15642c000350240c0d07000900c1040c40c1c4500b0780c0142c1d9500d41c80000c0e0001c0c001c41200e813040c40a00400401c20003c1200004040e2181951003103082c2c0d035441f107a4035500d58a0340b800f03509500030030041001342c01d0641103542c1540c1c41402230050216032a020a600c002c1a4440c8a0384503500c10403040300354001d00003c00c0c00022490300042c134030704100016841340f03018820040b0700b001c0441020208140700003070200505400104644807549410f01101941c00300d106903102d612000002240135a8406004400100d048000039004d044088107440c0107110000944424403044d4800c030743c000740080b01c500381c06a25 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 414338633 1250 414337383 414337393
    0x100e0405032808061504091a10090312030606140304170c010c2304330302040315110a030e030c060106020705190b0a0311070209010303021e06040b04030c140708 71
    0x1400d008080340000b4204500c5160044003170300f110000d44c0d05440640748128030008600000c0c1c0d8450302d250600381d5a540e0400d00040300d5841040e04601e81c84203ca002d19441141880031120450884496004040c041903405c1041c2c1e1076803002038003441d4041d10a907490744034204c01c0b800e600c0c41904500b03e980400e84d1990308a443d03c81e07021248a0f4112100e03a014030308400c00a80d5406240240c1c02901011500303101d491441ca0210880141c40101d1007803015081c2140350b00c0200a944180010782d03801c46d05454400c00e510262048014400f4112440e41c20119195804c502609030080c04040e103110500285e20950424030000e0b0007454903030020321000e440c0c50240700c401141c0201d1b80282e0036604404110310f00c0341c1021030304c105209241c00224200340c1d4440c51240d0203a0200a074101c0c00b00000030041680024030480c0d110725400c680030b02c0103111080c2e96911501218024640b24005022a001038000c2d400c02c84036600c1b0f03140100514a48140702171610340564003100c036175441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 414339883 1250 414338633 414338707
    0xc0c061a040c080405060f0405070f080a031d22290a0b07030c02091b030a0e100b0105160606080604031d0d11010806060c150406060806100e040503 65
    0x1c94424140000c481d401c001d4000c0c585610342a8072154010901e0303001810b0503000034104541032000d080075045103890104140e884a0050355601d203200011004606840020340c42c9074924190001c20a1009095425004140f031110544800040348400301e40d40300e400000780f84a80b00a04c0d000621440294400700c8000020804410700c030f039202d016908010072600d00880e13403040410341081d03010383c0c840390381e80c665074004c0e03101240d80108503a0984007c020b1105d501800d42282800d41c0c04c580071500240c40c40307060017003140e00040410340414410400164007800705c41101c00d01c18043d20001490342c1d0744466443c1041d03c1224124009075048184034002403002c1290b490f6454181e030070400d010525a21480c413040c0400ca054103011800c00026501e036a00412984015841e41c20740d448040c1c0382e000d010300c7c2c0c04107860880b486400d240300403030b0700c1400184c4944600f0380031104220080c1341c00c40c8100060800760083e2040d0008104005500c000c40081320b81340c1200444400c00390070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 414341133 1250 414339883 414339889
    0x9050c060d1b081b030403021504030c0212070b1218010606020706031103060906040f110412020120120307050702040203011d0a0b09010b0a03020c1207050f0c0102100c0c061a 77
    0x2d1810701501070284010a01648419002d03051090a200300c04096498560b4201a850000045045c0d460300220500f000101540074003031109141c400d8844140031880700d008291142d0090089000c004001c1c403070803c020008401d85504100c0e034032500744014100525060039103146403c01005a48452030402050f42d0503c55000d05050400120381941013140003e040c03d00c0107044075225607291100507a40315803503404850380e40054002e855540e507a9110030f02c86042c185409a0100d90207000c4030101608801c5c0c3e030561640a40090442203c1428a00d0724039000904400c007040414424200181c44902c02140649164681d05028110000e060306080f0300041008000c0da00b4200003e055482c3c40d203400d41074039401404140c4440307090008400030300407481d050a42307100300c02008440500f100000c100300f50182d01501d0031118090400da984150482c0da150040e03000646112111290f5071005200c9251803614041211558076001e085e9a0030950232904104a00a0006249 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 414342383 1250 414341133 414341171
    0x3160210060302010e090603160e010f0b070f170d0606050d1a0a0905130602070c03050c03031201060e01090803131502160e04060905030a02030c010605011d0409050c060d 75
    0x901042814000e071400c5900003441c1100141125014110240103c2c59a41d010f2115840040a440000c0d15036036880b010152115020f125107a0103230907410780400c0441190003218200c2e60840780380030401c200e03030350780c0d801b42c0c296031010301a1b00000b40442448017a0340d008043c01000d2681e54aa214680b065406045070501ca41d120a2940c1d9070074014450748072081e1020444050840004a5558021000c4501c140c21600140803502c0001c0031000c22104002040981e4090400c03190618000424503680c0c3c42000030007080004008010403c2c18880c030f6841c40c0390481850400c080795624450f0b2855a04800e10842611000f80030a0010300100d142000c05031500c0e100034055a101d05040c000003050740e009000d01c421303124002509014050f007044070fa142c0d0010441ea5079207000e041c000d403a90803501e1403864035400d200c0300080e0b13580300d1170b440c0c800010501145030425211400b08801008440b0044540b4003c07a03507403011656602028011b2505040d1001ca40503603400d0b40603001d0703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 414343633 1250 414342383 414342403
    0xf0213020403061112150a08100f0501050405040b0103060b13020a110606150a0e120708100e0102030709050f0d1b03020a0902040b071506122109031203090611031602 73
    0x41300144100c1c4800d920080b078954001409100c0c2c078800342866404281c03044202d4110803c0d520900c1e081006400641e400203022002d200c00400a0b6600c1d0000c00081e200f05840142c560001311005001003141940045000b50005100e1010728041c0f506000c2a60410b60126000c0742d040364514100150a01c409640700c401202d001c4514402e4449403402c41c02501806810441d005005d002079441c0d000324210058100f0781140c80065136801c2d141d941710080c2c60414007031400c202c407002e04480c0c14003d60780220110f131a1141d03a14100f40034016400c0c0d20040d01d41e8400000d6406201190015403030081b994041104620083d0550045c001030940030b03400207a45920400c800c110b0107a1860030f540c0c60590100040752001101c803803140c064030750390f080404840c0004000c030003009114241d6600741070715408c0021f14046c0082042d18a4141444050803030300d8000a41520a03110740d010425091180c400050f00e01d110409111064008840810303034469003c0c4490511a0104000801b13 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 414344883 1250 414343633 414343661
    0x40b0103110d0503030112050f01090b070f03140105060a120f0c0e092217030a060603060801050411240f0d0509060705070b0c04090504210302120c070f021302040306 73
    0x80089a80c3c1e50356928030051150611010b50420200d04210701405658421036510000f0b1001c1c00a07030070f1040159000340c031030750042400700c001106140d00902996940150401c1040e910b42c2c0313400d00b4842958040c4440c081048621008171301040c12501c1600c0d0f19030344501d00051100742074071015110720745ca02e6002d40305d2100f52080221022801603401e407070000c5012201d50740d0000703107071031003039204101000e50301c000c0c000c42004000d010130380c080e1045031540d58083c0300207a9100f4002d0b00303c0d00142d4000c0d06002004440005504280702010806681e182000702680100c0d025252030343c224148409806a00251140c2d81381154010240c020041d44041e140301d0410140c0036105205a000050079001c92200080122034031506841c02002c0c045402c3c00a840d09181032011403045444130160030030261305030781030745200b8425506c1d17419110045902c00c0d01c03841864000340d003000c50200c0c1c000c0260082000107072503006660a08a842460140e1101d0951500380c00340d504840510394 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 414346133 1250 414344883 414344899
    0x9060902010e0a0e0c091c030809060a0603120e030709060602010504060b151b0316031707020f0709090203030f07260910030506031c110610080a021002070e040b010311 74
    0xa00000054280d000000100010742c0d51b4104000b2404100701c69030104049002c1c098580c040c5600060100e200d00715034420744540f5510502e901e002c8483e94003020f022010301041e654003c90240c0115959908000d0890316280c0d5a0540c45003a646543c11400041c1d440d103080c071040000c1806015800c080c11508211692030300003e202d017900852169640c00700000d40f0301d04c40c5102c2842114030f826685880203254415604002e090031001c03d04100c003040c0700e10700040600f80302160b00107102e80844040d000c02c5e45880030701c01c041c10341c1440603640360004104440d02c00440600030701d030b8144a440c12413413451101082c45030540e100b004450721050b04000320440741d600e015040c0e5882c080c509000429868400c0400e280c120b4407000c41145a04094150341c40c0e5420440d1101a10507050071a41250385d1a250451091814480e820155000e0801100145458082c51180ba5142c0c4103c034196503503001e41014024050320705a421440e020014001c0c04020441d0305030104050b01c40b26 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 414347383 1250 414346133 414346139
    0x4020a050a0f0509090c03010806160206061201141317030405030912010b0d2001140307051b0a060606030e06060d060f020433020d02030a030f0b0409060902010e0a 72
    0x60518481c002100003082100d41d04091610300400130381d80322a2000e082c0200902c1c0088208090ba4020b016880309403240e2000242481d80306540145400d0341a80a0603050f1502d80c2442031040060314050038554036401c20545940030b050b101c500c42c3c1d203003011280500d500750902d0360b20140403c108c081c0924040040202149000046030320343c031815142c4002c5014480f0500b4010880c401ca000d03400b42a03030141c241440250b09515043c1072618000c0c41c14412001c0c0107680c51040c0ba004800d840d031091001610301030045001d0004a10702c540d5260306018130b506690700f845544441181c000faa00c0c5410301940364184540c11901e02510001c0c9040d0a18400003150050320100003841c0544541c10303840202c0c9c2a4041e540109180702d1040880c83c01020056110309061070702344030040d4415142191588009003031812005e043d00618680103003040110042c01c2c144021030000d644401c440220758555204034195180140c1c00090f21910358400141080d107507180e094070610400c0e1041c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 414348633 1250 414347383 414347387
    0xe070f050d0507060c02040f020a230a1e110609030408120301050603041506180b10050a12051b04060206040c060302090303041e1706010e250c0f020306150a0504020a 73
    0x190f0180d0b011801d0080c10141c4c0c1d0310005000e028017481041c209400442d07002c499075013002420f452005c4246050b400d0282c80828000140101035128000813607102c40301000d0101c1e02d1144ca1503c2d19441c041c1098444050001c0c985030702a101e81400d0343c0001380400592005220840c941036080d201a80b4552600e0b0000f1994000508050f02050300003e840c0d1610203141d008a0007401440b156500106000c94071030014281c100d40903000e00821025000e07001c0c0b094007201c20740031158440349103025000c80e000000380002031085602d0301c4e010ba0154005d44100026000900884d03004243c2c0345018917010300c0c8a00c06501c9082410300521011007561303400304c00d86041c0d6900186510030705092408441040f4140e41c8034480c503e07095404d503245458007180041c183d40700002c01005603202c0b078008000362200507103d40041300301000701c1a0300301e12400440e0061801a008050310645c9a000603040c00d400b52802c0308840c103213902e91000790411a0155004200440d0300714200400c0b0040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 414349883 1250 414348633 414348643
    0x40620010507140d0609050a0e0f0f0d11012a031407080105060a2c01090e0c070807030e131a090934060503040b340507060e070f050d05 60
    0x1102d1030320880404d08039003070300d0319034048401443c0c00e04081c0024140600040024150340b0928040b6002d0010915111789000032840340a100d4840100000101e00c070b0704454500c80c3c26002c041e203540360400d00403907141d05091411052000f074034880500c0c4074010301808031415052200c01d400104003c10070b003d0b0700000c04904580096a801e40c0c4c1740e0703041000300d4101560707015610030400784003030034140c00d8441c000041c600c2c102030301c0b624036213a1030742d16012103100c045400c5141c40008001c00c0000070301880281c02d141c2c0c401d00b0645c090740c0e03032100094409000c8070715801e602c540c3c620060310140903c41c10070b5803104040d0784504a5061124040b0b032504e000d58030003e0f030340c40c80d100750380105003503000605212640b80ea0550344240c1c070b403000103116905c10f4030b090340d064440801007410204000e1004440750b008410302402030101d80380c20040c4098280188003071000500160340810400d0103000001c4c11101d0180c801e41c0e0a000c9141410f84441c0c000b18041c07041000044001400090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 414351133 1250 414349883 414349907
    0x70e120a06022d04050907090f03110103141e1b070609050a0206030708040302101a0103090203011d0c130b0607061a0a0602010b0406080f0c09041106040620010507 72
    0x107005642c515400301c42d07100182480070b9100c2220f03001507012880e20400301c050320954008440c2680715480c0d0380700c100c0d0075051034000d1010214031400c080000620b003c020903010310040c140171900002070002c4d9840e00408448425091094100822400150b42d0038140c0c8030881340704582075401c0e171540a040d03500030f50340c0080c0030940c0d8080303107028404200803064801c1e41c020705050303991a01c2d81000340504001e5408a000d4821600e01c050303450b00d503020b03054541d035001c0008401c6010107401100645954541681c05550b20401d4099a002020071080e42c070710b5580081410307170b507080d0501c0500440e1490880e9640c2c030703200b0005190782c3c884046800c21341d00200b0111b202d4140e0303056044516192281c1d194004481c15000500f150190888140c1c002d040703400b00f101580c0c0703039022a03c130035450710300c81104e4100030306460361480d00380c0b59a0340290088000f40724010040d004194580d11942020003c203001c90221064140d11640c14030395010410000c1c4035908103400d0280c06400982 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 414352383 1250 414351133 414351143
    0x10021303031808010207200a0b0316030e010e01270201080f0a060b030703270c060f020c0a0b0919081209130911010f1706040504030207080a03020303070e120a 70
    0x2904420003116a610010043d01d1040c0c000c558801840c0b82800c550210841100704c0c802c04680403091514103c03a03602c04494000e81100d280d0b607144240000c035400750100c21400d041c2c1e00d199103980e1003000d00c1100703500c1548030000200102d6804020000001901001303e04109816032100141d900c0254150040009499000b094403440c0101025100d03980000295a0003c4100840e10358580c121183d07603103095042c052060005041c0d000045102c3c0c6000e4406061200300708580c0d4070410b8405146001403041c0d6680c0510755001031001180c0f0b51201d908008041a0030066140c02020003011005038548048c0e1907151a0702e035900c550000607443c0c2240d0000c00c460606850f4400303200821100910f08200da207089103040c0c03450107800c1d4103560001e124100141181801641c0802c03813020000548a015a81c0a0411000d003c008108400314011283c1c002904d541c1003040050b4180301c0c0d00915140d181c032000080c08419a4600c85214040c1e100c0c5e400303010b01e00443c07003a00c499000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 414353633 1250 414352383 414352397
    0x21e0309100504030501181e1a100b030a09140601080a0201050d0f0f060e0c071e020a080706020607020120071b0807030602030a11030108120c01060b030f0601021002130303 76
    0x40e0000b51164080c0382e001034010750824000904145500c0a00480e10b841940c10b484400040c1c43c040102100030324004040d140000c881103c03520008061562198644036034580711034a8071005e00d017580060355081103480c1c403034030b03500d0802040381100c0d0016019100101501c1d032420199a03900c640c011070181c140240018150341d0032400741c010380300c1c101c2900400e1107586c00c1c101c0e001009200a01c1000700340414000420320394840a82100c81e00750300611286440e03040403440a41c441c2e5014802c0364007000a01e8005450b00c410301c40c1c50020003d9801034200d9141c2080041e0940d82c00720100c00341c01c1d02c1103e02c4031401c0a00c6003a920415001007135002c40036000030074801d620325903420a41c150320405c00004104541070300294403a44248138140100032010400703503894002030088905a400c2441c3c6401000a92009000a142c40d8800411080d076108003e80580d4010384441428000440800800c1e580402500e1803a440c0c00004620700720b49a20079040d00685808020204848 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 414354883 1250 414353633 414353659
    0xc0d020a0510090809060711090c0f0904182906030c09190605060c0a050709060b03070c0501021c0b0f09010803090f01020a050f010b0a080105090d0e0111070e0106021e0309 76
    0x74004c02c0d109841300117003810390359004504000d85094800030840d0722030400f0301d0004420b020403006840d00b00ca170b089030103420301141e60708100113000114240c11500d00860400070128100040700d40030034042c41c0046204400a22420400142c02440b80b4080c0e80084a01e10841e20f450310069031150781600e600c54021602c0030904007802c003036889a50b0102010416091a4a000c90700004207403280003241c480950320f10094040d05d2091084206001d070030300006403d00c0c0659140c1c11751b40c0c8550001850144081000e460900811190401156848a0700985420090f200100c40d030390449405100e036141c0110f141c0d1342e1041520441c06001d00e121660314036402008440c10490382714064520b9004030741006802026441c14084c858107042d14006241401031040c9400f420340317540030f040921200c42d0306803180ba0202d0001030400c413402d1003030402c2480134028800541601e07850120254503000c1c0c028030746091040c00c007800e600b00c1e500501030380c0c2d0008111051400e003a9000740103902 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 414356133 1250 414354883 414354893
    0x4020706150303020f0c040b030309100c0f05010209010914090402010f02070906080c0306070c0506070822030f0201050c04050a0e1e0f0709060903080315040209030703080c0d020a051009 82
    0x2040795400c903049904080084105500495040001c0d0044002c54418041c01000c200585650340350050b01a08100000500c500b80440c03414944e55040c02c1c4a2030304580c0340ea031840b651401c00da05850607503000c0340d40109503074031645400084c185c011007d8084940c040c006602c440e0b000c4c0c4003c0c14403100040d400541c0b030081c02450000c1c110801c04001a90b52030140b503460742c0559008038800c0c0540400226918003e606002845030050001c125961b640041914103150280100610443c410004003096003108100355a40c0d2017a0740e00548502120806402e50704d018202405480c001d1000384099291441640211406125000d01c81d40320604c00c0201e1410018070001501c00f0541008403681500785541e01039206a07a518088540c1d540049a50440c14000103100e014104003091b0300e180422082d101010004000601e4501c42c0d030700007440c00d00c0c0c551044502150200d41c11903015000d03c51102d00350040c1c0090709000017a07039a0640c031140c090351008500e07a030316003180b400e0103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 414357383 1250 414356133 414356141
    0x11401080f1b0705010b0a080d0801091a0619080109110702090a0e070618050102030418020a120c030f0f02090117130f0c030203160609060f0c0b010e0f0c0301080c04020706 76
    0x8894101c41c255601d600c0d0420705e010741189562a40948450300c000a9090400101c030041c0f240c4503610003019074200405c9001030301203400090706944e61085400259610383c402000600200c0102c83d0a4a08004001c2c3c46a00141e000100541c40d002c1444084490b200440d0300721a4103c40084040d0340d00e116010042440712002c000f1449110004924160032007082d8400c164194840034005d642e440049035684624040c2c030480b403505d0346000c401380701c164015080750300d12410500d4403c0c00104519084808010601c0006901d444a9000c5521984038a0642c41c20300f8a00354501444440040e040304200301044541c2101c10000880c0994846814000c0c0756018510410301c0040e418034850181090200b40e10a01410400d50001c854014114086898640702c1c070200c42d1130001c06844140c1307000074403000d0050002c0710800140c4c401044501030941e0f507003c251181022a0b1151084d40014000400c0342c1c001c00c010702c80008005100703a8040000c49000d82c0e5005503181540140c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 414358633 1250 414357383 414357421
    0x51522151701050108070b030606041a070b09070f0f030b0f040305071509061404031e180b0403050c0306040f0209132103050702011103040602030a0e0601060c0b011401080f 76
    0x100000103914640d07210107401c414122140d480c02c0320200768a8891100851200340c0da01036000000308001c111041c07a054914580401003c160780c1444440c1d29500c0328030300e084a000c98103420000044c0165a19011040081d0081c80b40c0f03c148181599500d008400e409041c114026550b0000102058402e90890380740c1540003c000502c3c041a00c40200604081801141c100d8144669034807401803001e070f03a0b84555050741c0c52040070303d1b1389140084540c216552160400c03201c4c100341c0b1030040100e0341d0a0300030160740b055255128a1400e203d406c5c00c01018029200c0e030085000c0c040070a140c45009441550101c1d14084152031b00b901e10803692002c40001448428541e585070340c0c4821070070713403102040c101d502e05200c9940c07070070800c900322142c2c00d8090b4103003401403000c034004c90303010f40c0075580c4503081100000d040d808081783c55182c03030405d92011000a1604d402c41c0100b2030700030741842c014403005040b1010011510006480e50000800000000103032100007403165100c90525214 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 414359883 1250 414358633 414358649
    0xc0a0b1807033008040210080c090d050c060403140c01020a0b01092c010203190c0c0303050a02071e15060e01050402090d020a1e0b030402010f230a0305152215 70
    0x583d040290070510202c07026486000c29030358074200a2301072849103200350840c0350064900140c40b02040a0030041d4101a1010320034000340c8a2983c65250041002d180240b2040f11810403541a940c0b521443c0820981107410015500c800101c4882e8406e040d00e00d0f0070004552202e44da1072500398010174160040c4182480c148002058006500542c02203498103100400c0c201031140ca0815599420b60190018042c512007201192090b40000e411000300c2502500e000d03802e0300c0d08074001850626400c000c58080c88580b0400408c2d107000000f0602d02d40042c40010300d800d071180a070742c205110b8540929000604244941d9604030300c0c8858079070040010600e030b41c44800c0c3c0c0d0b035403003211110440703a94038414001c0384005450055a1149a050b915401c408000c9203048403505082d6100c4400a68641d81c480c18800210000d413840b24102d5400043c0b80c80c0074821a0300304602801058040e41c2040c3d882c960514801d8401c80150f154000045444030162803000f80003071042c2d0042d51 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 414361133 1250 414359883 414359963
    0xc0304030224031503101b0e061306021e0c0306010509041412030711012007082710080702120a02100e01060303090e0705070f020f04020c0a0b180703 66
    0x3c0c0403800707004c5562482100f83d0480d41c2c881c80d24814641299509403244600400f140c038800312840c45401001c100c2c440c050421814000c010041d10018104c40d00503401581128440000c1d2a940035421081414803d00405890400801003921043c06024450203040d01e40300180134092204507010030441c0c0001141c10980c41041d0b2000c8682003983c0c0280050703544591140d50a07814060000d20b0a603003655100c07441131040204581d64400e2100302c0c0c4410080c0300c8455074800c49101a0b03400901d5002c000c2041a507603041002c000c50404040f42808000c40a00c0341031940010060118081400213640e250800501039180c240743d0412018aa4149600800c040c01c041d08520704480c03003900d42c8803885071500c0e00421100821501200080d0013404120081003154130444010b50015040e4001380d0300d800d010400303aa001030340490b1158003a01560041112341980b003540000c2001d401401c0c0020b1101e50313900d4200340d20020303000f54002e0f070f03120b0021802010a19100d10404c41802 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 414362383 1250 414361133 414361141
    0x813020d0f02030f0a0b070212030c0702040b0d0602040321210b100e04380d0b040b041209140d140d0c030305011212030507020c0909070306060801020c030403022403 73
    0x980d170301809135045501c3c0d152100031468150000030020030110203503400504540c1c07506001111a0005070f02660302680b00d81034548682c498908040086000e44405070341d032421400c040c0303942c2e840180b07a0300c00c001195803d420a07550049490000440000005910942a03441107001e04520175102d644480c82c0c0c402110070a4000c4500c011407141640c09001c5a00e0707203d0030101e821900c210201842120440c2509a10807241c0d603042c0e03070b080040225000c2800703902d0f844040703001203d08541034101a820700007844150140d510f00d040c0c44c1d01e800240304c1d0405450078460000c04202900640a8550400410074071078407200c2c4070010141201e0a901040134000c100902e1942c0940100f4900000814514103c40d110581160402450728175807078100000c500900c8020031500850140c2250200d099444415460190750300d840201000c900318100300c805c60b9101e620000c6581e10400000011080c04419a012640c040711800301003150b1401d0700e540b141d03c00c2030301e0651801c000300b04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 414363633 1250 414362383 414362413
    0x309031403070311010c09060503040510050c0d0b040c0e010309020a090507031b030e03120a180302010605180f011202130c03020304200a030b150303040b04060f0813020d0f0203 78
    0xe846443d000341d603130920000c8180e03040d41c00c0301e0060034804c00160201d1401c1c0200f80c0540000c6401a200d00110b5071010005503100e02295016100c9912000e000151013400c0461402054071132001101e04200a40d031450b000743c00b140e0000115414952240c025409650301c003c05080100380c03011050200c2d113040b8000500800203800740c4003070344074542c102505a610901c500021403284034001c0d40340854000d0310055920000305043d090f00e4035103a90182a04500c020907a916210381c001003007031810300c4200700c5141e0000003c00c0200d8043c1040010100e041410303d811039160580d2881802c02c9400031400700035855a403181d245042c80904541540c0c150f0080d80301e180105205801843d500003243c030720303504110047d5032100c0312404c1440801c03203000b1001d41000c00c00e17459580c08002000402d0445d01720380d01100382400d0104040024a40000c12200003100e079141c10000b07460300c007a01c031100248112000e4011543e68103180200200034101101854000702250050854a100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 414364883 1250 414363633 414363637
    0x102070507060315031505040602161406090c011b080c150402030c0105070503070b0601090f030b0f090303040302030414060d0e010f0e06090d0c0f02060c070f0b070f030305040309031403 82
    0x1400d00002e04c0d1a0600716000c0c04004e075001540d5220007100d0103015028409405498042d00136a4000c0d03082103807030b10090f014000c1803078944c801c0405000b80303840c14002c1800c2510041203050507820044001200f41c0c4d00030a0181022442180d00342e140215050076946401341e0b64800e40148181030a0f5010780118440d440d1003540f086085855001f20600110390130b0003078040040c0b40c8d81c014030a000014a541c01526031150701031420300300f030036030b00c0c0c001c061b004000c3c2c3c1c001e4170360500040c2030011280d007000280d503002f0035441c015461030070300d90b600940c2c3c1d105500c69542e542d000c19468240c1da546650440b03014003003580f4140708400c41800c40f076000b004c01c01200110b141c0361030103928001c1c0c400300d4264400c0213100301401c940c0300d50000940d10700400c4801220440000c007181d10041e501c1074041d01c0d80411400003004424146461200507001c0c0e904020001c200c140201e01c005005103920000090345444c6c00b1034192102c0c070b0190380441c0342da00010600d0005815408030300c0c3c00040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 414366133 1250 414364883 414364889
    0xc2404080303011a070804060c210509040e0613080d0b030303100510020106060816030608060c070b0c04050904080c010b0d0501022205060405120f151006050a021005060a03050102070507 82
    0xb1501c1c142100300c4001303000c107125940c001818800280420407000303006640114502d401261a119245844040b95540040840d01440864404244107040c1d00b080c0c4120401d4680b60802080c55040000c44076100011544c0003c0c1011000034150b40b060394150001030b10140064100c980b80c0c2451040c0c42100166405018052080095840c80c07244c414000d0ba011941c06859034500ba481c0e0040854600c03440d0304007542815161080050110001c10480e4032446404640a80707030b8005140031203080e980a06000c080c43c50070310040c050383e501c40d02041d400c5907000b080b4554440c0003400c4107004d45808400f40e9480382040140c28180001900249491011008042c2040c0d4a40c03030810410f10481c0100c540018090005010318200b0060740f0031071140c51012030b15880741d100003d601e041414506188101410001d0080407116405100040e1580d030805500700505500700a66403800d030813203c0e19194903080440c2440d183c0c0c40c0740a003d9a08400259902c1e102801c00c29500e0404d0f00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 414367383 1250 414366133 414366149
    0x1052716110d0e040e030c0a060b0306010f060215061807020a030e060a0c02090a020f130501090911071b0b040902091311180604090204080109060b120c240408030301 73
    0x110020010900115502c0c081000c1c40d2141d9826908410a02000342040304485000741310400c44410494010004643c1d5244905400f003410802c0034181410302d441a4407200c01464500000d00149402040c814061000001d00041c030340e0f6035100080c18040e0ba104c15209a0700260b05001b0815404540e08088501a0f12090380b8a07082d84107100303c1f4440c2c06130620006000e00000d4005140105095070020010382003d8144519000c003001300d50b000c03144403a03070800d8004041040e540c01c460f2100081c800107404000300010100004564800d4020092088142c01070b0301d522011090a484041c20224100688450701c80001400940c024183c0c1c3d803207525649101c00145e20180070350502100800415801c100c00700b04491070407200b9010107548000d0034400400c5d0310495201410040403031034008140c000b000d04100003101e07020514180101203c602d8848403610001d200d68070040c00b50f94112948c18065a89100c0076449141c5c00900c0100280005003544000013941c1a55111 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 414368633 1250 414367383 414367397
    0x61b010b120c090c0c160608070c081812060a09020102010605091611010b0618180405060c0a11060f010602070f03050705040207060213180b060c0601052716 69
    0x200d020000440010032848070141d2000c40b20b0000d0f402d0420440750480190b41000f0700306503c08801c81d05240044612208105925504210140c2d0044600360020300c00c1c14001c1c01440f2588644c0110310440924200c00f64411105403855285d6490b124841410b40301554694145041480040e11104209a00643c02c0007400b082034039155001c1c902926801406032045203d068080d20450403140a110f2139559030300507810076880d001c00130114101410506900480310b503082203a904842c40e4500c040c0f1401a0411000800010398150420310700c0095588605401d00d04a80030000700c40aa4458054402072143d4030500c9950320341601d105400f50b400c403d443d12200424a202c078807002d001c076030001800700021f0a1690003028154014a0090300d480c900d5141380300711512952080181c40711040c0950007030482442509900c0b40c0c200d036002d141048410400e541ea200c10300900d4455207207111082000040003840e55000302d070b5110000d8103460841d03030550200380500d081002051030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 414369883 1250 414368633 414368651
    0x20c041104180e0a020906010917010c200c0919060b03040b060d05060f15040911012012031e0f0118020408210c01290306040c030f02030309061b01 65
    0x1240100d0030403d00003001061240c0f010380030815240005003400d410b0081c0d903000810a06250305104020011807000407540d00781324640200711480201c0300030480c4034441002c6030717041c0012a007101e00f203008070307844401c03520303694980c0040f203200e107001607071903840c05800203540b200c07070b01c055441140184200e40607036940e041840100164030320010001d8104500107854a1a01d6100c030750071010f245030780151100e1050128045546503101230702c83c1090210600195a031108020310f4800b100528080c9810b000e0701c25580d04c2071140741d15143c1e20b0003c030004140032110810f042030401c0007502d426060a003880c2040380600d0a01410011200b014001c80380d01d0101c1c0225812200464020900ca80c0250b424007950b010314000d04045070020010f0312030f004024001c01c8611784103d5040840850201b414107031519000c0741d89400390300316500300008078040206000843e504503491000820080c0b000909621a143e890341c3e0144004c900415056a205a09002c0c400704800030007100704 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 414371133 1250 414369883 414369929
    0x3021903060812250f0b040501090b150d0b0903070c0608070e060f090603041a090d0e0d12080c0f040e040b06031b0f010504030f35030115020c041104 66
    0x42941003244203003440e1185820000100d581140c3e503070703001c5e12000114400540d25840301c0071050300d05556076911500c1007024000d042c151140c104240c042c2c4150300170402d0010030343c07040441c0005000121007a000503060603050003260701156210070a5400c0c00d071075080107070102106030348001c0065540c0074220218141441210400c9010b0800c00b81016420010041242d200400888074001200c20710042c0006104030715002c1c10740075010780404100700b00000d10243c2c131a0020f40c4030f040d4035007910010409104111491003040d02e400e083d41c0da0380c004491118800e84083c40f40741c09000400040c40716001d02d407a40100d21420107074600f600d50004150303031500d035218a10b41480d56074180c4807141c600100240701c00001030412600307140d901d0301c030700032100c80000013a509105020325003100007981000e611588181301c10f09050300b62038040c000714240814060f10300c2c540306040800d15054002c000740d908408009000303200e601c1034041724060542107032190301041b40d4541d04074481c00c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 414372383 1250 414371133 414371137
    0x4061514060403080a020a020a08030408011410060309051c02070e0105061c0c03060503061003050d1107030b061219050c03030f0d0b0d050601171009020f1003021903060812 76
    0x10001e0200c0e05141c00d54603401000e500c1490020150f2007110046801620340250f0b110041044a02542c4c40c1d6140c90203150039500031030384c04034108040604014251000081c62800e550161400048040301072030312526203e44182d60300c41403c07803094000100e5500207000419100d000c0124001660f1741c1044c002c5500a190071401c1003c450310788031800c03806035070020024072100e15000c50841da40300042810034905554070b800181c800d03101403082c00400c00428060070701518001420400560b4a1a114000e9001c01088819540d01041013981c4094110390b104203c607066812aa04200c0340c000040c800c04002c88050058041c81407140c600402940c0801c2c410310011494407c02c403c1c404000c050b1502210340c0300744c0310002c40c0c000c100c04000c400c3c06402d0070b0f442c040707410b4000e1aa1505d014024130203080b00300d081424001c010f0720b4138016030a0100c3c050341c0030030303044000b01c20540c06409001040c4024a4000310481c00c131980c550044011240044180d6058030310b100007811440c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 414373633 1250 414372383 414372419
    0x6040c1d01120b0a1b02100605011b0b070e0a060f0f020d140306031014041a190c11010509070303390507030609080c0105130b0a0f0e0303040615 64
    0x1400c0c4103041d40740800c3c0140c400a912021036040010313078400030580300940341080020400140e2080c00380208042d041c0c8650130262109081803200c3c0150328400688903d4411002415600010702244007540550100c420507400206201802c64079407900800c80d10a901043c40095001d440c0b0070461800400c881e00f20302c4042c2d079442c01344190344100e0040c0350f00107080c02c0c2e014403800440d04143e0210788150000007580c2c080d0107885007001e051000040d41c0400c1e080c0809c110031030501c08054402e21610300a101000b6022680042c0d030341e0f055590070002e440c80c203015400c0c0401c1103031070000442c1c603400f580e209031920706040c140800c40b4040d04041c046400c0041c14410100840c01021742c4925004a1044044403440c45d01e0365644002d40c1e009501c1100d2011012409400740c05007070044540c0610b144144c000003400c0d607181d8515414001d00414105035980d9070f03e07c1c06400c40c0d004040e0070340c450001c50340d1301d080c9881d0020081240c01c8000d04800d400c9000401d585001c5003410b048 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 414374883 1250 414373633 414373649
    0xb03150403020309010e061e0909090c010c030c03030b030706020d1b020906060f0c01020a050703110d1409181302040e060f07050f0d051302030601050d031d04020c06040c1d01 77
    0x80080e14401914906c803140700035980050148015a18200d401165a80b550140c400e03090b1186008070078041048000780000c0e5264000c4c00781098180d138040c3c143c01145800d450840203004039424198001c1c0202c028170f94150203924400700398103400040c031618051045e40c6141c0311021007401c4007003400446600a52003096407020070740618008015000c1c61509a070f00a10301001010303400d00f241d111036001700c0811808103006042c1a0042060401d0340d803445d006c0c0c200365641000040c000f032690040c0b01652200450980320540700e80000703011200003070404041700d050403407483d2004001e0800891055081903d0015409808624240038481c000c41030f400302c3d1111242940c5641110000c0c4d003e51505001c026282941405a607008000341414a45075007858010700d800c10380140c010a00900b42d56a04000290b480301003204010b80340245007c0a0b02e114001901a00c20f402d10a50280f040300d0601050007502c801120032640b001091032221090a0002e41d07007150244600c140c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 414376133 1250 414374883 414374887
    0x2404020a171e0406021b1006050108060915010f050d02120f09010e07030f0501090b0c030402040c020106050307260105041a070906080415060b03010801060f09110f0c150103060b031504030203 84
    0x44c103c0c0d0050b1000104000300d07030f0485178194450918000107034200b070310340c186c507884100141c0d41c220b02d52a80045064078541d03910b140c0401c0d40c1c0010040018054104141010b01d10209807052040d58000b94040a0a568a080f02000c02038041010744585424150700780214180240500c030b258070040005000e0f11450f131a58481224000580134262410754a83c0c8101d000101c14004192052801c080016200d081c035005000454081030700b40c5055a16021082c003041c2d400282c480c007114801c640b44003444c544a506502c054401c141136041560a0105104c20844880c035102880803414401ea02c4e00d580d01c020454000015101321800b007001500400c0128450f07070413051a00a08820106900e9070380e00c0045640d90007640504201e940d1104140310460703c9006060041c40600c500b404242004043c004007882070440424079030307000003514010301e0018440b0800c040d030745d00c0d02c0c400e903581d4038140900075106500006109015a550f190301141820700c4a0b8019505640294 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 414377383 1250 414376133 414376141
    0x305060106120204090501060503190c0e0f0411030903070203160302100c140d1e020106030b06061e0a02030a0905010206070903150204031509110a0602062404020a171e 74
    0x1864401001e40344402e5280c0810000c83c18041c28012a4001c03c0c0036989e0b6907a034a842000b0144074060252a01d80c95401d080f1412001540007042d018a01d5049a65510642071000003e006140070160648c035601e0101c02c100003410040050030249000750195008000101c40500314050140002584a10040c2d8130607007007481600b051100c02e100304001c80502542c001d5640c40d00240b00366100005003240070000384054103c504041074031050000b407081c681142c4e034080c14040001d080342d00400d40030510000c500000d80307903142103a07150780e140c50340e80d54840c100940b20b600041c100d4000c1603040c140011954030001c1c0702441420720340e5402d0045800d503941d403031034050030064039004903409100210208070102c00c200499040000001a110350b03c0c600040b1488079183d5151041e95034080402c506500452b48661040b558019040466401004092002c81c0d0402c203075001440892014402500301100080003420525044036030f940f1840c0c06016154184214601440b0ba00081 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 414378633 1250 414377383 414377387
    0x60c11060c0a030908273d021e030c011a030d0e040b130203040611031b07030201090f06021305030106080c0418061415030a020604030b0405100c0f030b0a0305060106 73
    0x9031321042c4110b401c01c0c03410721540d500c503101c0305048529214840ca00035450883c0d10340b50642c2282400541a503500402e0400c0c28030200084034503001c0c401c1c510303030034007846160720901c8080c110b0b840030f514200b071045c00680d180c0e6994004000c43c4880b58a40546015503040c1c0d00c180c207a1505000b4010604c6c0840301d802228514900c0c445a6041500c0d807070303225a01d64800c0070075410003c005400680768034090034102d007518101a000315410321b04105000d542e031540741c3c0f100144440117082e640d6441461a00f2801002551806400401000c44400422031a50004c0000c01c0d024441c1c01c00064982c402c0500b00e61036032140e044c40350320031606002c140c101030f0070460240812840701300c4041215219081a245c1490181082800d62020401c1d40c00101c10901d02c001c000b030b8020240840d95a000c036420380316501014285041400010b02000810000c1a043c0c01114a0520454141240141a654101041401090800b2791004890800341803800c00c0381c0c0c002000b0040c5918110003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 414379883 1250 414378633 414378641
    0x304110102031201350c0307090204050d0b04140303010905190c0504050114190f08010e06061c020702100f1116030318090c020330040627060c11060c0a03 68
    0xc8104041c5c148441c114030341802d084c15017401080c4801418888803440105820201c1c1c507000144110310501c8288800d413184131254001c1a8400c000b02400c0c0c0312810107681500b02d650712103126100003c00411403023101d4101a001d5810b0110300314603c001c0160a80560b140241c14800240040c00700704603640c4903000c1c90b031a820050006c5c030f16103004031251903d00700c0060600c9000c60085010305078959402104280181041410200340e03050150026500b485a83d484184d081c01d210741107114444a80c0c11100c0140c1e009142150041c0b000001031700030858542c48801213050400e40c07502d40c80307000c99500c0490003000405440c10f0b0459909554598070f1125a07100321480a2000c2041c000324422912240c6868006607159080549955403180380c480210381c132802070f01d54a400c1e6880c480340342c50308280d0164010601c1001c883e1510076455501084030140ea004803503e60034010260b1100454820560703d48d500340390720901c01c5582c1c41050b981199140320402c044104240f00e0f0340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 414381133 1250 414379883 414379919
    0x60f060405060f0909070e07050a1e0504081605091003050618010e0f0114010605090d0201081504060b0306090c030421120606081005040b030a080d0e060c0304110102031201 76
    0x700c0c0307480710040c0004c500745000840313001105a01641c0b0521603085024101a0302403d646402d41c601503240600800120603000502c0c145500d6000e4110124010802d071000b1304040f90441e0141d040d486982e42501019103e104e000b1202070780032400c803241e500c0142e02600d81250003018243c5a07034550446c44502c6101c03440981d540c60001000806050120700c0360550b0040c00030450600d00401d1102140069204405100c000c106481003a141c01c003e2021403602400d1002465407a0410f2081c1c44d01c00c268101d41c810720707192002c02c6013816070000e140a060140c031300e80411b6880b82240c814a12003590050f110400d044482d44560020700501c0d40e40b01445c1c500402e48100f651009410307202a40c00450109081100300300c4800100c00c1440001c001c11542400a181c01c6804651030302c2040748013802c5103600040007111801107401c803600c40034021007140c8081c50b02520403d16900142e400700c507052004240c0c00704540c0f0000070f4030007024000c0354a0015034600030b200200d002d034040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 414382383 1250 414381133 414381139
    0x70807020a03021c0b01051c0813050402160c08060121030201060b0706092001090b0a03111801080a1109010509030c042a14180a0f0303050403060e060f06040506 71
    0xc200400140c8903042c20b1418404c0e080210000740e0703201c1c500109202c2c0140c00c07080c02216aa440c00c01c2036001613400301d078410b0704100003035a19130500280c0c008101594102d540c01c1400021402c0641a0f0141c150700c149004001e2508641c0c0c4480446803501002e128052200fa1000400740c00c1c01050007055151b18402e000000d00e0300c1e5500f90712905038111600940d03149554015200c01e10802c00303400e840803110280c904401011200018003a00428010718080e4040403411400707190003944154141d90320740d09215190030682d401c944005410116980c0050440741c04a00e1601c11401102c0d900740c1d210180c1360030441c0d031000442c1e181c0c21158499034148140c4106540c1ca03140d900c100407421382c1034040055260381d0b042c69500510010000307141001b459146031904010840156020040310b0703a40780124424020005442a03d5a04545582c07500c241000081540080c0200100c9100f083e060015a4880b0061501d0350800c40d080c40c040c00066002460078607007030b0b22282e4040001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 414383633 1250 414382383 414382399
    0x130b060304111201110403020a05040e1f060509010e0403090509070c08070f020909010b011d01020726030c010204060906050a050d0b1309030507140303010f0e090a3504080307080702 80
    0x14030f60040c2034405001d44207045400024080c0700707600b0a00a40005071a042e101405903102d4010a166101c001c201d40d04c0d0a5440100300500321586900720000501c4014101062945c5501810007070410a9074120049881e02c0d10001b01403c10b05401d0703110b41540c0d181e900d441c003003688840b02240c0c0205412900812a416410010390398096400d01031071004000150340d141c01000034041044001d0460301440d01e01c64000740aa074000380360001d41c0c250134002d040d822940c0f111031a0000c80030021140310302003c900d0400e2400154043c20490745035940e014251070341c840e001d4036688240c030983d41c0001c100b0002c050310f1704040c4d00014400f0384042c00380c1c082038000c048400c00311110070208800003080050100103000300d04140c80c01c119a41c07405545107515102490351004c800e03100b11840c141400d00001c120f09814000843c09075000340d01c0303401102d811203c7e0a1001c0b410424044050088203440180300c2501e000d840c2a905807000851405040341c0312040d9940203000c080b60b1091030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 414384883 1250 414383633 414383659
    0x30309030f0312060b0c06100b07020d260d0501050a0501082206150e0f010e040b070e0612091606020712080c0703050105010e0a15050105070614070806130b06030411 73
    0x60700c50300b070060040d1000c0340c1d22000b41c0520b1a0801e11f000c1e102076125128180e0a00460340c01e00119143d5590480d94001c0780801850200100c1808103504200f144000044c20305e001c181034020201c1807620082000b041c1c0e01c51082080450440c0220ba0009203160f000a0a1050f5400380101c0c1241c100c402820070300496a440c0295030007088041009048081c0401010081100042c0c0142d885202800c143d030518010a001100040000d0302030110303036011030034060094261544004000c0c014030341e10281a43c91190041d0191000003e601c41d000390383e0108038008859100380d611560240c550f5515049101541400281041d202d121041103408210b590401140c0011845400045850361500c2600c0e9071140c1e0080c50b8050860609850848203c01040180140d60302424542e03110394950034000c0c02814031128500c5201c031640f050210a68016031210300c100c00858614180384101d07010303081511140080f031a00310b030b001c0c03022a00140101883d640050005003c058103524 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 414386133 1250 414384883 414384917
    0x2100e09070201020d0b030708190c030803012309040201020d0e0307080a0c0e071103040e0703060506030403080a05090a02031c020102120c040524090f0420030f060a030309030f03 79
    0x1801d4800c0c0c4050703940025240e014201500405251100403405030241780d00d0031031034640300c413440c0017050a080c148071035031800c001801c100b42d40615002000640c40c8e41e10780307a00f0042888400500d4144811b61600c40c1102d00d041c0e0350080c459a41a8040e00203000348041c1a502225619102541401841404110040f08020740d8098a0080d60002401407501124810450f4090300140400c941c003250400325003c00000c40b402c42d13890315240d0000356650b4408030020301c01c82e00302541c4008000300b40402d04d9807188640f0301400f11064200140e0f15041152075036030343c0791b410094140d00300340074010412072203250740c501a0056000142c502048071640411152089656a4030500042424422070901110300031240040101c0c2c4406a03a030769800c801940100c60003c0c0c82407016000da10249e8840d07030828246400d0580c9895141c0e00d189010021070f8000b200ca00c408003103120005092031034800d0351241280d82544036080c0c1e06040d911b035010075030351401c2c06a00303020448510200d031030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 414387383 1250 414386133 414386149
    0x6031a311a0406050f0a0b1e2d04050a052101020a0f1205070518040e061311030105270109051c030c0809030a1808010c08090d110a02100e 61
    0x710841e1050038010700d625080104854594000380c1c00b030502ca040e401c002d40c40700c089903c241c942000007240ca9004100c064088440b503107108451b480400306200d242d07200e042c0e00038416900e1204014129109103030b403440e214000e81c03040e11b0344004105400c02044c2840070078407000c010b1401d13624903101c0a904007142682c0c8604a00702c000380c04090f1000d000b42e485003c0005407090f16000f404141800c0c02d00410500a10444c01c046404501801d0807995690b40b2181200017180169059460a001181800e1031640800d541103610860394606a24042c45401c1c46000848481c001c00b040091a10041c00402c4002d808250358403414080422020406c2d050325088480304801c0501c3c1c5c541c4000c00340c0b4088040c1c0000e0103803010a00a003100c01205039207055109291036685500f102084074002443d55000b00019440c01c52101e2415500c618403a00c1001e091b000c541c90001e080c242204c4840b000c151400c01500302082840042c030340010342c090000e00c80e190500584c3c801c040056801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 414388489 1106 414387383 414387401
    0xf0d0201050f1501022d0f0c030d05070812090a06180c032402040909021f0e01051309051503060a0603050a060203040309180606031a31 60
    0x2130303482000400c481a0380d4428410300030b14a49a000b5640e80014400c03100340c0164a00e41d00001d000280d1801c3c2140058010410b918414400b02c0e4150800c110445950804200100b02c441003c26818000c641e494007400500103146040422181d02c201c1c80d0700c859244405c65004140000030f0b0b9002c40340c21521510b01103900a0654030200c41e1003800c03941d010b1000c200403400a5031a4401a1a98400d50f15809000d058140c94441c2c03031983c48503140050140a03103800c41d54820340c0035103031503009070005001103921800c482007039604c11101d440103034205400c4030340715240c10010740e6000035070341394200301050848d1940c91326901031070009000582c0000101741018445e007118401041c0710300e61a4290390b02c1c144518081c1680f403103081d00080c10191000e044e0500e0500c561040e42006084092070702c01c5c100a0086460b01c42c02c000304041c02034483d0014000540510b01d40 = true := by decide +kernel

theorem cover : BRFrame.Cov 414208633 414388489 := by
  have h0 := BRFrame.cov_init 414208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 414208633 ≤ n) (h2 : n < 414388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
