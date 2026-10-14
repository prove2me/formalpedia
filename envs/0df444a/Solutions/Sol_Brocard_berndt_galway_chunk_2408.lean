-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2408
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:37:31.934794+00:00
-- url     : https://prove2.me/submissions/8c4a4330-7917-4ad1-a968-ab0e0fc33bbf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 432913669 ≤ n < 433093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 432914919 1250 432913669 432913681
    0x605271515130305060126120904090f1b15052104020d08041d0702061e090a0f140606011e0c2f0102060a020423061c05040512070308 59
    0x480140344070350300b8620030000180c5a441e41c1d45014002e0f400300c4100c407002040f0344c40e10458500014602c01e18a0081d01046075441d41c0310300c040c043e51600c0d521456603100c16600304143e02c0c861070644c0382d016484014414600076410f840200c20310900342c0c1c00d94101c910303a88081c4201d080b2661007500001d136aa4140724001601e0340580020001c907044020b0b41c041e074006c40c0802c0054401000042d030784070105200c5000406a040c40588000c0541d4404001d000c00f08039050081003216203e43d0b101ca1070b80e41c5031a540f500d03140d09000c010f40b00d070340030b80310400521103207000310744211520f1001c880d0161076107001196814103400458400b42c00c5581800c403030600c40c3c1074801207140100716844060a1080a0301058420011480181180100030340110b58040c801c003544620080021824585400f00c901440c020300035229490440e404a00c0070300f5039581c011381e03c0558085e03040e9807500d440741c0180c600400040ea800c4e00d0130311507101802e036036a41c40d40031186181d0345a640c4403070b5500d0321 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 432916169 1250 432914919 432914959
    0xf041b080f0105042c01110706060f0609140d060f020a02010f0c021504110316060201050403120e12030406112b090c0501180320040506030a050604020603070306052715 74
    0x31542006255403150020b47d190702c0204080c00c4064041e00e03001942901d00b05151407200344a9100c08248040c094080280d10002c0899803000801503442c0b2040c0e6841b4035110b401844e40d181500c4041d031000c140311041a0b415400712242c1d11424008206c0c541241c00c09a070344a0b00d520100b00b84001090009000600c90715040d8030b1120040c0485202400c010044151881c56410200050795913000704001d040d4003410b1840440c4600c101000191300301d1582d01e480d518120000c4581e490000081003c00485d80d200c80003410004060a807502d4119501c4944030b042d0f11404401248020400e203030071849845035184e0305030300c074034013100080c54a8010340340c0c5040450581c071400414140000410218001902000b20412240300141003140c208400c0b5034016000d0b60103a401041e4a10004600049580c0c21640444445403240d0320428110301511540d08071a8103d910180b50440d10200030540c1801442080010403250b07480c0d01940c50b22003600300709582d0084d401e003811000c590032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 432917419 1250 432916169 432916241
    0x1302030703021e09100f0e0303040605030406290409030e04020408150a0b10030506030a0203120a090b160b131b0501120b0306010e1905090a02010306170a020f041b080f010504 77
    0x220f05121401fa400c4e080000c5c2075403c90b81c80400403810001c01c010400072103204550320b100d400c0820002c000c2e01070354840b2a800c88080414021076a4220036000e243c00382d0040b2603404c40090040d591a52900d050544400780c03058451144140079010606500b02401191502c203000f902c1e40c000f04c850500203c01900700504000c1e00740c01580c6051016071001d21a4102e80104070842680d11601d20303100414174910340d444615083e5040c88640d94004042c0c4242e00d0050f003206a00e0869100c0741c4230318120040701c25009050445142074001151245019002250b00c00d0301c4641048a85e08c1a007020340d190055040d030315410110040c00002c0310203c59030381010045417000e501d20007018500c012280141ca403c425940320411110171580e140c02458060312800118020f03030110103142c80d558200001e00284207055040b601e00e0940c40310b0f0b0129610004124001780041c4004101400e508801d54002e050310011500200c2e01d410103000b0315401800c40c21980400c0810000c00443c1941 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 432918669 1250 432917419 432917447
    0xf0b030a0f09050313030201080610020733080a05060a050303030f0408090d0303060f1205060c09010210050c1c0209011b020a2417070c060b1302030703021e0910 71
    0x282d42d036000b0307010600400142c401c5404000c480c500b06420340c0009444a5801484030b4800c4040045011180e540400d6100865004001111500031200e5010703000c509140803120f147c041d5211030a00a9078040e4039a03000d118881d10030000e0f5104d080c14840005028003807213415500410105809000134143d241d0300c82d0103110710304d04190350319002694182200304140c0020307449041c02d0107100b0b543c00390701e0b00400c0030300004400101640d5446441c0e5400900b01c91110701c010600d0001c40c0d000b88002c1c0d1b00c500443d9020820743c80d001d03010221540080c40321100f021b06081c405415030300e0034803c40f03250f40c10586840280c00c01003040c101802e801448106d0b0018a840e40c0000c0074104408021a903842c055201004442c41c003100030520f80c030700413827030300001c080c030041c028a03d400022001140341c01c414007069468545020446030b10f021841c00a04600c000204200a50305a0207412600340310040d10010005c44070f18030b0742902498460990100c6004134014082d801004c400c00305007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 432919919 1250 432918669 432918671
    0x18050f1003270203060603010b010813030504031514070c031407080c071413050403090315150e15030105010f090228030c1e090905070905030f070504060f0b030a0f 72
    0xa00d20241e1489502d92216020341a080754001910440c50244401c0354841c00643c02044001290030000f03050300400340c9003c0351140ea402c82001818882da040b500134507006044c010007402e10b206007100802c0c0400c00c1074100c01b103000c04500d259101e081950a4107416650329200c1c4010403c0c84c00c400d5020460484840a00b080b0322800710b0810700c00d52009080b05800c5c2c06491021a0611445804150381c0141e828500410000000c0d0070840c0305050320781240700c501d122400200740900a040c8482c581c5880000c28500081101365510759511a10034080c540d044c05860350241801da030003c0c02000340308420101309104610b450303409031500140084220304202001e108142000702c8803107400c1c0000c1d40b070309020350340340e500100011021140c2c0c01030070040e11741d4020000c00240050141c180302c20780b500c021828441c030400e10207010301002025280303640c10780b1000b0742c0d83e24014460540603074202000041c101c50754100540488440102c510318642c0c490440d04002c00310400388040301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 432921169 1250 432919919 432919931
    0x601090203191404021504081504020414271516030908070305130510050a080a02130609090608070e0114010c0b01030f0b2202060304050106031406010618050f1003 72
    0x12a50314011022451041808a620fa0405006000c407003242c0c0410801e00a1041004002d840400119084202c0003c0800c1c07405848500c00200548140c840e10300e80300c21840c2c1440480f805040030f85010103500b072240100c9040003140152203084040032041522180d0000541742c00c01d1410034550315600d0302d80003840c0d07805a6a400c1d4130b07800607002030300005c00201712803842562600800020704070450300c182812100e4800202588101c0075120304011440c80400d2a40d001a015a82c0103030325040700d00b0354681c5420f40144803074450310a134001d5500f1b0080c000f0b500d00010503c601a110103007001a200e0f0b00b00b540e01c2545105401d051410003048100c0940401e44010300540a54402e03040c10505002c1340c28040307116100a824a074100e5041c3c401006c6044501c4080629603a0547c1d0050b100c0c3c4e071f54100180107000321f13403000e0080161461100c007156000301d1400d050798610707221b54004601c6032003100003100c0c4a00070315420404d40c0c241c0325010b01c1d141a900050003d986804030328 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 432922419 1250 432921169 432921211
    0xe0111030d0e031e07080906070201140408280507060c0c030c0f03122f0a02060d0903021e03030712180302010204051305060a0b072109050405180601090203 69
    0x45038800104100c0c40e40000c00c00c84a244c4905011160241d0101940d03410003442e501e4003403540c41014003161050030000f44c01401c590103248080016000010255240ea030380c1d03074200d9241c0c0080242c02c404c5400310841208141448940c60400c5500000203089031410480103481400c89041d0a0300c0c0084141c0f80040010b8604100102038490012072401c80c514608d00201240596114a824455100c68904800000c03c946000d0110700d80c5c0a02c0c0d04140ac84241404c20841160194100e83c000074441e918403110307000101c209101e90300700e0b1560803001440c1c00c50424494018001d030f03041040850340243c403034070b00886903a90900c40068889843c005450400018802c1200581d4010508004516184121900c1c7d0b8107034a0050141c1e140043c0090303e640303085e001e000c4c5000800700b8000140140303119041c810032400c1320040125000640c1c0076008940601c2614030807824400000e802c900ca0740b842c0c1070500f210350010b1a15034204040303d0065080205281c030442030309948459 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 432923669 1250 432922419 432922421
    0x305070218011d070309050c090c0c030f0315030d020c01080a061707080115060203031308120c04081b100c240912050a3f05100e070e0111030d 63
    0xb00a00810300c03000160003801081c000070010081444040c140782940f0800030920210305c4010101e401c44201d045a920050048124041c0990588040c4000300d500b1303680103000710003940a0050080c0c02c15241c200c5100b0950f582d1948e851010058100310361b9144154020b51005412203010500803407207030380b00c001520900050100040c25540282300400511000380708010034449405091b00ca030310704050b000ba540380f001800e405030318410a54074201744410803083e5248655241010034803410440c4000b0341c290041e0251002d58005e1421024158810051300d20128102078560103840d03075400c80982d8480c6001005032001c0100c0c450f10800007020303903240140080311400000e0302010b641031090f510f02d00102e50030f0900604100700b82c44180c2102e4448900f405e1a03440200101840e400a00d00c04445008000c2e0100040d100c00c1c8001a0703600028815a005100149016541c0710520811901680c0300004a28141c03e6145103501c90301903a40c01d038005404503841e003400101948 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 432924919 1250 432923669 432923671
    0x100e0a0e070c1202190f0f050d051801020303040213050a061502010e07121e06020c010908210601080105060f071401060302090f040c090507020c1e03010c17040305070218 75
    0x400102040d100c1801c0080d11084003941c043d1510042186807652030082c400e1140316003028124441e0240400f04114404280d110507036405001e0311001445084044e080b0303040000c440fa402d25034506002541d510001c1a83d2043e5001058800203000d8200318200401010b842054215240e03400410b21902030300f00401da51090750700000f00f045c800702506040c410103412404402280302c2807100803824200c100103c010b40c2904551078203940340f034500005e04c5074042801e501d5003041d005100b80100d0300040d004c01d01088d041d03022020000c0c1c41e84050080c1c1211400d000c0750143d8010301890030814060500301c4000c020852a10b80f030740d2a03000c00e500d07400702441860381d1a01828011824194201a040f0045422168460825949400d003c1d04140224881241d40f040002c01e00c510030070a010150401411001c494482d41400c154141041e03801c19010350708121110180a1051103060b60022554440443c56140c03903400320341681c0311801c183c0e4800d1112442c010580d070704000b82 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 432926169 1250 432924919 432924931
    0xc03120408090a230423130f230d20070e011418010305060408072a080c371d07031a030307030e060c070902091e100e0a0e 54
    0x5403081d04600301440004c0381e0240c0c2c049008900f41421102d59241403901400c49118096941c082c0741d55824112840300c40702000600540c08a048050503c4008103420b1001581c0071107000060b031454402990f9620300d5001400062503020f1050a9141084070304915100520269000c0d075a0301c40480c50700710002c1e0000311141c088004088410b18103800f07180f49000780c02c401001550b16589480e40c64800c001c0028143c400002071600811088480c40341006271031110140491011414014202455000b004520320840140003850700d4900c00c490070315184020034400081c041064440c40e1100398080601030b5501510201e00401c4150140704d000c078030f8032050321441c40c00d08402000d96240061311400c50911640e0001d0a032400320450300d01c11b415090106d09402d0300d0020922900c9583c050340505c0c080c0740800300300d00c2d049400070000d140048039106040088507245805041c0441d030695404206c0d1201c04801502660104010400040c548031205640e44044c024110040b208 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 432927419 1250 432926169 432926189
    0x4030e010c02130e1c08040c0608150402070302010c0e03070f09110c0a0302160e011a1b1603062304140a02042d14010b0d0f0e0619020c03120408090a 66
    0x505c01e600c248518032414450080c0c640940c56040689a40e40c00c0c40c0f01e03000b031104100c0d0310710026500c0e194a1050054802024104650b502c080f818000d00901203120b504001130301c46042010740b440e001550f4025150345002602540b498440c02c00c0c024203059488040c0c80c20305114441d015201400080407213406900a084444004e440400b004006034016400007442d000040c4107400040e100341080d04003170707500d0702c1c1d90310307500c00400d60701001c0842c248103280702e1902108188034015403000c4c102c900c280c005014850741d4080220048540940300c000500c181000180400c8040100000501c0c58105880e8842403640102c4c09807540710703429258002c0d06031655029420038048140b45148440c4042151810180c0403000e9202c06100d640c0c0c0030080840ca121030f400c035940c40002c1002c01070344108941d010504c0c629131180300c00c441e174403845d942d903880000c50203015000303d9170700b96013a0000c1e62808818090407076082401038001c2e50404800d02a1100c1c0d500d132514420050aa1003030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 432928669 1250 432927419 432927433
    0x10207050406060f11150403030b030109050a060b1c02090402010807140703090f0b0901021c020114011202040c05070f03031107021207080c0a050f0f0418060603050c040504030e010c02130e 83
    0x3402800c4400360070811440313a400b2018000061b04880c00480e007181e40b600c0c0100303581c542840000d0241c10300c00405030150103920421410020241c1c008090594196410407107020b440c240e2000c103000c400c80c040d400c00c0780740d00040e00540c4146205680300c0d090b07040c21403031070010100349045900261021004030300f5580b4180890503e00346031750010b202050300076251041c800700003134407101d8000491586000c2c9080e00070070b40d4000c1d00a2101d2118888000b01b0710340c1e41c0c1e520f100104d003108030180e01591420b103501e0540751055003105c00d1349811002000c04121680d800300d004010340e0094450989040c41814016a41da0340001125010600101000c506194040f404c14014044091003800004010401c6890b200090701c540401100d0f010f0f842d083c84000300b4080c00c4c2d070703130a0f81d0740c00351590007000c0400c001c40c0d002809680c02442201e10980b0f101040c401101c6003600c028010803500515802c0b1588100900062944050200c0342021840f0180304195000e00e114206030f5000302c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 432929919 1250 432928669 432928697
    0x3020603250806010e0a0506070b10090f060f09020901141e070f03030506030c030a030e190b070c0b2803090b0109060608060a060e010f05040e0a090b101503020901020705040606 78
    0x10700c5c00303001641100c103210803a2812000500c98854940000c12062441d000201c0010a00d1f62007001002d820809101d20070351409250014000e9000d20421000c0380000494400c4561003500d00141c0e040c0c545d8030100405040210050b0801000c02817190144000d4a603841d480b50080c013882c03803084d1014250780c5d055240180540710028a018000c0e4083e03030302e0000325500084c1c41001c1c5601410024066501c07240400e407911400c2c03001c201c43c41080800002c40c541c3c1da400401d03841c2d008802036100302c0c0c0c0310401c0500c07511480609083d04902d030302d0480001911581c003c1c1c84284103040006050a540d40d40100c1c92000f68030103002140c7d110420451282c000405580c400c604445466100f0b0516101904480f1841c08031410002c85c0d80300c5c0984a80550221400307050800d624003558a040080e00001d0045082d00300c0e44c564002000c1506c0341c000c0300e0f1100c280c403418860b07401d004414072003c400030f4010301035240c1141320300301000546407940c1c401e51005d01281c6c1c0d02d51005103001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 432931169 1250 432929919 432929927
    0x31e05100504110d03140c0c0312191107050f0d0b040503030a110c100e070b1909141f03060902030c03040b061903080f0f0c010b03010c03060f0302060325080601 71
    0x40b03c1e9001d840404034590009030702003100b00e081011010301c0f9450310240ba28036460300c10080c5c9203940500c034950602c44200d415101500090041aa200782d580c01e09450868061140105018480d8000c907018001071810064004076007402802c41a040203041e241c0c940d0058050310165401d0700004140301208000380500030500b00344405003850410305010165448000305181848560340e0300052600201c14003121000f0203800d076000e03403140304013618203c26501a10b80034010880c412800206001c40b40c0542140c0f030b100900d884080411181c24110f80c1c075440a660040503039410022403040340b13901c090b502a40305034a0981d101e18040c60200e05201000c1c0c0003c1c4036a0b15030b01c1108546404020682c01d1300e03800113890341c40380b0320200c0301e9031140180000c0a115081c04503402e82c040c00154020b041c20003003100213105a440c1082c003941102c0c41d0703004070030501e00600c40600150821100440c1c03c040303074032160180d4550800096224001820788440041c400009001d02c030340e40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 432932419 1250 432931169 432931193
    0x41209090908070b04050f0a05030901030501060e060d0c02010204050a0306090519050d0c030e09010603051501090605091203040f030c0608092d0f01051008071e031e05100504 77
    0x1000c080200e4412074607211000d0195a40003401e81d46004001800c000e02400201c00c141141021144200064908117442e6003140703804900007880c050000506500c50008141da0783c0c40a44820b107407000344542d6402404400c00120190344d000c01c00043c0d103032262809000114001c5500040003482498030504010408120103450b19040346120003154010400b1400ca03041c5d41410140c000d0340b46025a2004c6582441d03d607c5501c1000000302c1ca42c250300018414000b400c2c900001e4a06c0e1801551115800c4c02101c001a00900c10704156041c00c039400f01014400c04210f0b4281540c4035152100509190011103048003615010000309411a10701c5070010021005044126031840545c144035503480207181000700d2040e4021120721081c400c1e9100b4000840003400140741469040800e00510302c210100c41c42084030010b0044030700c0784041075a0000f904105509071a41e2110105c0401c22000c02201890071032115001440800840195014081011510b46450b0502e1002a86 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 432933669 1250 432932419 432932429
    0x6030e0601090b03070b0c100603140105090607050316050903070602070f0902040e0a05150406290c1e070e0f190504020a060516060e0a14071202131103041209 70
    0x1051043c1039425503000314250081d5040c000e82c0d240c031581000f2281c0c0ca0721250305180700341c00d450010701006000c5001d0001c031910140000034066a203511400d01d42e64241128001d00003003090001c229140750115a0718001c0780545811f500f0003c01f8000641406440c1d030000016900000040042c0c24440ca00b41e030046c80012021401d0603d0194441e2100200a00c2264925030710800030f40700c484249842c61200802910070030549484040080986ea0819004482c6403115544c041e00c1034803101c00c0b50114160800134111310f515100d140061715442c000400b00300e008462010034569102501644203810944240c40941004e500007100800c1c1c080744070b80030a080000300001758540b1383c2c00c00c04988942c90842e030354500801d0000e424419000e4000c214908000f031802880e00001004030586008510b84030030183e404d4100c0d40d1342c010750300c590100034124000350401f510706414a190061003c0310080303400c40c200041d9115940c4111000c0366279918000c1d8810040c2e90052900b000b0788 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 432934919 1250 432933669 432933671
    0x41e0b0906070215012d0b1603090506160b040f120903030f03050408030624130e13050604060c0903170c0706020723040b0901180507030606080a05070e030706030e060109 75
    0xd410044140310034081c0e0001c1c034035004d81b1000250101040340340c03000c1c0100000c401d9070303442d2010741c2c0d0029082e02c0c003102d05030001812000d002c034413032402e00101e80f038138100101c4089104100d07a5a038507107040010800c0e24032050711039061011aa1011010441407500e90740c8910550540c076024103031080c42660102058585010840000d0919049a070003590445074808005284100c400f18078404500300309441c2c00100705001c2c410301012040313095482040001c1500d64942d00824401d01c5201c0014202e0741c0054003107408902558000c55000c60545001a8019141e03220141085138408000300b500c2400a0304020400d4248a0400030303054601c06031002c145020241f081140c4900302001411540070061000340d662580320f111244400390900085603910700c1c00f44070030201200701c91421414040003920803480b0f40305420581c0c0154075141c0c0c96031a00039039140200401481030301444402000e4400d41c0d41c04000801c021300350340e1b9000c200e01c449213040706c0c100b1006910501e28a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 432936169 1250 432934919 432934921
    0x40314010212070c170a0e030712051c0c120504170c1005160c0602060403120504030507140a020d060510060206010506070303050c0d0207060b0f09040b041e0b0906070215 75
    0x804201ea4503039000307052450f1200c40d03080e603820302081085e0f032420f2014a0003000640c1c400c42035080801c260301644100d00396408256625a41010030b00003410040142d00070303c3d9100b400d94800b0030281c89286035072400940a42403a0b503018141010200c0b40000f1a002090030000c0650658922810031032640207040c0f840755520204915416145802c02402800310301d48080e040481e03100c50340700340c00604402149954410203915404191802d8002411128002a544000d400350600560b4156109450034070030b901c81010007107040c905851907015940c68040580d60305502d40784c40e0b5004000014450501003400d01301e00403da404501590000c100400060b41c40c5015166066014100401c00d07a98141250440348110314039000303140e101207184030501290342e000c0307100d000003680c01a29915078501003001c0d03040110340080c503c506a00000d0300040404003085403036150103002c010600000d50f40d5580d41402290302d04103980c0300c8010004a581d0411103103200c01c140c90100562 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 432937419 1250 432936169 432936187
    0x20a0b120c0306010c060516020f07030c180603081c0b1009140607020d03050310090501051c050705060a0c02100f020607030203041e05031e0309031e0706050c0403140102 75
    0x1020030003041250145070100009142da4003640c0b008080c5e0307030301c894108281d00e015920314441c5046007070300200600c910f600c80360300201c001407002c0a6a8206101118061821a14105100c0b000b07502d0400343d80c483e03900200007002c00e0080c0c02c0c0f0208000b038188210440c21512411a4903c4048a01c0385000c0c0c2814285d07250070011080c2691015994071711a420880e0100f0f41500c10708100039000b400303040c0d041080c1644100910301540034003c440e008140d40380d00d03010944100303005140d800b10700145c0c1c1e00103811100c107083d0201c03445201660303c001d54800001d0303260341091041c00041621851000c04510302440f0300d1811700d516040c421181c0c0c110040081d80d6280c0144004141a0300002090a00558041441d040c000100ca0015880e02d0f03440e01a48903000f407603040240061076400003019071103039030a480c032035070440c030041d81031031120302c10308011098038040b50309180030801048000c40c0583c01410301c80c10b0b003408425625451407a101c002600c4481010f03403541d02c10300c21a40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 432938669 1250 432937419 432937447
    0xc030b0a060e1e06031306050606070c0b0307020f010e0c0301060803040e0414070f0312030c02070e0c070c0f0621060f0312020f0a0c05011701050603010b13090e0703020a0b 76
    0x410b4000564042c40044014100443d0b031007144120950710000c048108480701d10313504400c1501b640308110500a540ba44824001140910710008215100302502800524420b0024550040d4144102c8034041c00c080310403800c484c50325500c40303d10b801021440c84181000d00440c001016004002e51403d403819003a0b200b480070181005001c5020034540e01c81c00c0d042000340030013034160001e46107a0a03542c0d16250f03452340581080000482c1c20314044041040c0042013101c00c0303442d11040155030340e60b40540c0101652143c1c0080742d00381e4072a800455007001d110b1141010f444240c03510212068941d000d50040c1003004c0a480507581032140c14001048036000e600f044035401003102c4c48900317080784140c0c282034180e1440200303407081c244201c00f840064155a02100c01c207803a034160f80d003150b1901c807104160901030503820120420040100481d1030004044034426050b04e00c114170b458460b00c0b0f06481c030501190381c01d075101034024000e620300b0540c0b030300042968020240c503141600340000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 432939919 1250 432938669 432938687
    0xb04050103020c1002030a1d01050f060907051b0d2a03051803190c050a08030708030901090c090509060f091009060609090605011706040309090908040f08010c030b0a06 74
    0x6410950003003043c0045401c104001103d594a800040d5140d00e0044a000020102c0d0420090180114491100d05060604c6414000d1039806490a1660344170002e01400301000b070081d5040000412000600b40d040440c248a448800c00140002c40c41c500b000929200100c81c07065800c2160b0004000d605405129800000da8076041150300d40c0361082c095070481c0106079410b0b80600036541c4000411544510000c1c2d214440d2040780c1045495800f0701515208034010003026600800086000c203001001031584218260000703d46401c1580d2009120307440d40d485490841c0d21141440080f01082c01000d900100569560405142c88110147e40e408006441c19085a80b40181000d12081e5000500034002c645424000e5110b945060310080c9001d1241000741140b074030400503420008a149805203809d9590200241d081c6101e0400800f05c0d04411994031008110000d44454901010301c0208400c40000403075900200c0c001c0e00381e03421014024400c26088905005494201d1001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 432941169 1250 432939919 432939929
    0x8010e010608060105041a0705100e070b07060204080f06240a030318350610030813090507050a030c09030b01091814070312030e0309040c0c15050105010e01090b04 72
    0x30b0011034440790010303191803081d0341084111248410a04950910f450001c04c0041c0c81801211040d86181c0d0010044411662445419420102040160b103070306001070030009002c5c600061400d075035000210310304844e0504d001c0c09500100c040094000c40a0750b50b240b230501c00e0001325050810000016032481103400010107110880014510300030031540414003420740c0801880003410a0a855a180351030000400c14a902c00d001c00715440c00041560b40c00340c4841181006043d003180d4440143d43c00c42c01741c2c200f074880000400140c0ea203c500500d4020a040c2c2c0b03526a40f00000e150003015942800700300c0c1c0c1407085410702000043d40d01f030241c1c2d0440705123640000d42040341060303040b00c2141c5a10301038440030a404c0380c4588a60b0120ba21000c0303c2c40385800c030594440c50070064003950100b251000043d00b061240c1400c90604ea005261445050300c0e204d02c072490075a640d132083d401d011510102e074940d140d0040c015035800039202c2c1e00780002402d181c1905c524049814109104030700031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 432942419 1250 432941169 432941177
    0xe04020a171009031806050c0a060c110111030f0c070f1202010603051203071808151e040f020f12250b030103050303160c03021b01051603020105011508010e0106 71
    0x2024000d01c60038403040518146001090100c21041d08000b0403900c4019900703107001285101c00603046000c1e9040382c83e20b8007080064500c00d00c00c5c1d00c82d10000c1c9030198009003403086407035a002c82c0210030300c54041c89150440c0c80039201c0c00d0000010310344460041000e02400c200f007194030041007a18480c2000e26a00240300490b0400c0c96004038090400c0ba0310007407003446016000703940c44040d140035500c02d034000d5417041406040807a13444174160b070314416000950072481040114098042809500c10410040810005840c60b199500080201c5080c2c1d070304122142d0b544110700c0c26004c85080d00200710350040400684040f40d036242c0070000d1a40e20341c2c50036031010407103040c0b11341c11260042c4800309000d0340301d40e52410040e07141c0d40300704c1c1e48680251107980b0034165240a00e250b0519250181d000b00b02e00c03020b45141e004140042d00070a410f001d0b00340100c0d026400d002c2c003c10f485030b1199002141e00e5262281105005415110300c10502441400520482c050850303000d0441d882c51070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 432943669 1250 432942419 432942449
    0xd0513050405010311311d072601021903020d0b01020606181009090312051003080f0a0c02061309060e01380304060501080f120a120b03010c180e04020a 67
    0x40311820b04441b0000c407000401142041d500c10301640c840a41002030101680316080404106502c0300d0702809849441a0160070751002000320304284102e40715228001841d0203001040c0c00500c400d6542c05100181d0000303400d01d41e06d400b6000f0804120020300041c00c5c64206200000d00e510181d04a0b02082581040010441c440369034400700106803100f020802e040c4a41802020403d4828030340c14081e041001294001075040740810890390000503c0c7d05125084443c0ba88a80c000366528080200c1040b00d000540d58460050402941c8007100180c803520385114901a0b8101d42d000e84000c40c08800108540c1c0d40c2f18641100344040c01400c00c5841400410110a609002032102144507000c001c1008011a6600c06816100800d04954410341c1c40e0b00b84595401c921641e04400100910100b51414042c0c1c0303010341581240c2d85c001c680103040074046400c542c3c1380b41caa10002000385014501004410352154090206590250035602d400c3c1c0200e507501d0118030074805001c182603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 432944919 1250 432943669 432943699
    0x80715141b130e101a030402090601020c0a08060907091505090c0412051f0e15090c04090b2d1f08060f010303030f0902091b0c0d0513050405010311 65
    0x10215a00c0c8040c001c0c4125545440e641240c034400011a000100d182d8039441c04621701003007184800509807000c40d028a1a51680e0078003810303100140c0400d042d445074902c045202e9a0b00c000c40005409440c0081100b440c010803024544001607006a441e1450305811881640b6200031031703802e55900707680c2884e02c0d4840100318400b503c83c5500900c0c8c0514600000c0b020800040780c405112001d6403a6150041403903170341101110061007080307800ba4400c0d000e0140814103007204650141d4903009848001440f940031900782c80c0a98421180a0045410004070041e201621100350448040b08139400c000950140c44151000c1d04040c1681c0c080ea00b246c102c1003402040708050691241030b02e52900b80810800c10801080c00100c1c0403900300724050581841901c1044503480c1c0091410925407282c80c240350002d1070307075180c2d018503140c20405500340c140d041001c0c0503135505a42c0c138603a4036519062014410380c01078000342c2c07241c0d04180c010400f00700d510400c9501c03030000312000c1c00c01201c0d503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 432946169 1250 432944919 432944971
    0x100c091e051504090c030204120f02040e100b1005041805090c1003020c01050615070204090615061112030c03071b0c080d2304060503091908071514 65
    0x650189034005100c2c0c40811a00c034014000d801260180702060103603607100a0264260301032802031200652a40c0702c02e0700800d400603d83e01c58640058400100030007042200760515540d0302002d8031240d201d9001301b020341842e0200c1c00900e403052030214102405c004400100000307069042c441c40d03071502e000c175416803800d0003181001c0e50014100845000e50805c00360103500405842c02c8954071701000106182400989031010380b003580c44e5285083c1095003000000d000d810340c241e40c0c142e52140f0320043d840c00c03915848064070581c0c8507414000c81c10307541d40b860302c01d0320030085162500602c05d10031009450001d680e004030722401c4c95940d205807160f00b00010941504040e000b001500400229124003085c0c020400d1125502d41d586030703145a900412024100f100c0c420740010811080281902c5280510f802004802c10349480c0c40000c03076408440b118450041c0c1b2100f00004042c01007048174008000c10608004c809e1042c0c0d0034207003161080020003401c0c0d408040c103040c0000c0b500b5800c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 432947419 1250 432946169 432946229
    0xa1a060f0a08041a07080f06010305010303050d02130906121205070c03061d060709140109030b06010f11030c0c0f030c0315060102010e12040302010f0516060209120d080405100c09 79
    0x800c071504440d21784520020038921094840419280304000814010b51181c000d00b8113903900f60b21074500d0002c15505440096100f150680c0c519040c1d0280814502d5050007110003d01c9400c541224484440c10700b041c0c5844008001024003108000004c0068400020071003140c1d001000000d1200d07108515030266110700b0042d0b0094092a8204103285800a1410302a19200c055030384c1a03405040c015900e00c01729007c05011001c0c840300040c0d20303600c2074580309400c10242c40c02c401e6440301844143d241d07402844c01e82c030480d040320101f4a21424040341301c510405080300100840000440480d44603400001c400c41800082e10010308941d0003500328048900002e42100c02e5000f00400d1784010340c1142c00101e001030100801300344014440c400740c4090003c900c030080c11140081d92a00d000750f0140c0080b580200e121140c2020300031f010300841c442c8100545482205181900c2c0c40d600742a10040c3c0d8207541c500c0e02d540700080d51b510044100030f65520441200710003801c0204907401440c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 432948669 1250 432947419 432947453
    0x170f1515130c030e190b0a0e0f0d05040302010206070309150515030f1c11030406030e16060215010e0108070509090c090c0d0606080601140d0609050a1a060f0a0804 72
    0x10410442d041c1a641c5030b8400050201c090301a5516680c1c245111485c56200d03600103040e44407044082001c4d0b40c1242d20229210042c0d904031840d22102481490030064948500f0b0003182000c80d040080d560140042c5501200524003000b1208055581c3c00001e0a10f40e2103c0250781d80c1d01c0050503d00386020346890402000301181c0850401d03d1402d80c0d9805024269119982003504005c065406846841d0203c95084082c42c20721b0304001040b4020203400e40076000074032441c00d00d04010003842803140b01030251603000c2c1109050940c0325200c000e8060303204404900202c2d004000c80d203030108514058520454a65996032103000d00baa02d02220810502d91100c170301c8040c0111001158001d00500e100d55009202075030365a030381a120b03035038102c8409005c60724007c000c0060040920080120613003105000500d42d448010080450300100c5900d00790315603442c1045660714030090540f4401c1c604507803003840c124903041640c0c0d01d4000c400040307090000c8074001c01c041150655103416041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 432949919 1250 432948669 432948671
    0x1008090a0b10030309090b06070b040f080a05030a1d0706050702060909070f02330414010f06050a080c06040e061507050d030617060c031f170f151513 66
    0x108091a80c142c01000a11088003c10b0b800e01e0000b810345828002e4260801c001010182480e00c10307100c0302040c00c0300400c201c4420031340b0240440003c0100d4040c0c070400d40140e4409460f458540b203041c0c11500c01d100b0003940d00000100030342140800042da5820794403203107403e0761644030601c0890001c3c090b0404081d0700440340340c104410242d2007150341d68644242e608407407a107034400080c0341510108168150078070030f00900c2c03107869241131003400ba0018031401e8801049440c0182c2c203800c442c41c2c0301c04c0d03031480c6444d52400c200380e140070390042e00905110805880e5001c0c0e080001007a600c1644030340b01c2065030410001d042a5601291440355016a1084607590452464200c2c2c4481d031000c00718010901c0c00300e02003880702c10710f04e02c0070841b0940c20041c100c41d1121a00c841c0c40e5000180200b0440142d021541c0d105d0364180240070082415071340408040841e40c04a0342000c0914800c410a40d12015008040340428072030740c1c0c0c001d03814000080d50700243c41d002c41d074861880384203030b0501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 432951169 1250 432949919 432949921
    0x15140c280e04020c0a020f010903150c0c0f050a0b06011d09040302150408040518010b0901111c0203030a110c0703060f060306050f0603011d121b070602030d0b0a051008090a0b 77
    0x40804941c0d1017500e407088440203002418000199a00c0d1818040a03200030824640002c40c0400c0c2c0d4000580c08115052529116030f080c1c2d9488010810bd040c11500354000c0b642c1d500801080b1104a43c0085090170140072040b19100204070030724683c1d240ca40b0911131000400d040c58001c2c0441031101a00180c0c4080c14500f90900700a66409071103218002d001c10564100c0ba003001d0f00626050700c505000e01131030800302400448a0009800001b2a02d010310f40701500d00040050404000b1200ca070003640c0c6034a0038003500c0c0222209581021041c0e01d04001480c0700380004952042a00ea1100d000a03003040030040b500000c2c00c0c644c000401e40d500d04018441403d48030158140700300c104030000c0c030842003003100b02d806032404642e50355a2030f4850101c2000154009001d8141f102040e840c0386900c030640650f041c6011200d6000502507000040c0069182016006400301014140d9983d0210741c503001c08226024100c062041c10810b80c0e4020400c0c1030000d102e184113294100d0360804003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 432952419 1250 432951169 432951187
    0x20f060c070f14011407020f150406020a03080a0b010f230a0302041517010b0d140a1506030c080a0504110a0807060327120c15140c280e0402 62
    0x1800d00600912402008903810040d044d0700c2000c00164200c402c010450031708a140e07003408035500500c103805a2192034540382100d842c500801a00c02403a1980c001c0c10380c904035003405444071a0285c01180003604040301040240d030825401400d07401103190290703101480c111001c0302c1840c80400020300c603400080a41216503d900941300fa1140d044010658000210003a140d0b0880b0303001d8079000f4011500100b005143c21405030510100814010034200b4292070403000d84c00b001c0310b82c40400e503a2400796021003807c8005490240c08281020404203110320006400511300074031101c01e440c0c540c0d0015007003010000c00080c481e0409450103840caa20b42400c0c903180d0f01c540c0520000a850482030740391710944640480030b00f441d007821a86160070720740c0b141e22407104501100000c2c0100703941a400080c0c00c80201c0384138001d00c200b00040307901669810991020028080c00420300c020b008840d1003076501c00c80400303800c40140c584622030340994070585104400110701e0703603c40d1000c00c0c1810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 432953669 1250 432952419 432952439
    0x1b031501080c0a1d07030c1403040c0f0803180d0c0519051f2f0a110312040302100e031e01020d050907030c1401180305010b09010b0a0507020f060c07 66
    0x207950300b412950f126603140c603080c0094004202404502c1c3c01400e02d400320740300500940c805401c00d1140d280c029031203620503112445540c019202260080b04081c410071802801400c050040d000e8040a1864079003444140014a413500b2417191181d20f00500c0c1400300504031003050700400300a003c50010009404a04034034001c24031425014403400c05060400000b40401c1c3e042c00400b03901c40003030015080307070710344410f0310748005561201c4080314031440c02180801060045078800c085890390040b928040c9400d100d50f5400e00a0220414403040c070050703680003000c0c80700010364640740c44044280b41c006490443c008003d2034028400d20070401c0c09800c1900140340c0300480e800300303001c1b0741c0f40c0d8080141c0c1c5240511000e045e0130b9001205000c0740e03000804c0d40d4020380c414503004a2000c1b101510041150059004032007503035403050010400d00b40160340a0040451a10a0f800c101c0c0842d0064a6481803020091143d0442c02c61030002e596010241c400240c85201160241038817400a10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 432954919 1250 432953669 432953683
    0x9030705010b030c011d12030c070303020c0105121909170703020105130201140c030c010216031205010608060d0203210a020f0307030f030f2306010f0504081b03150108 74
    0x30310a03500701440c2d1040c0c1e003030000d0b080e001004181e413144514030803019030400c80841039280c154040c1444c445800c0740c0750200042c21030300b12130002a007840b03031131131034064540580c0c80c2c0480d040c808240f04900d1b00900c11100b0b00d51040441890484400030401413000510030304030300818181c00d10810340c4060a080340508080340c03290f0002c020589031103d4031841c1c4a0300c0c03400240011003032440044040b1040d8054241c03514154100c5e81041100030f001030998011410110085400c94150000c0c0342d800034421008144094041201e541004001070403008000c01060240e10071907011411910100142540010802002c0c0f08590480074810015409400a4070040c40307801a20f100d50880030086403601541507c1d01403440641c1c100039005444104400142260b84201031040034038284240700c003013009090503040b43c4c9414000580311401480044040120600003408540f0f03000900c880b01c3d5503814000c00a5242c56800240707000c410380c42c20780d468004440006002d1400141030313 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 432956169 1250 432954919 432954923
    0xd080406030e060c07030c0503040f030f03030c030203090606040b0303040929010f020c010f03061206051f23040213120203060604090f140708030c1c050a090b090a0509090307 77
    0x80c803002e0181904a039aa04040d030710480d03150010465940003e00484000407510722074010740742000e41d5442c02600100300741d40305942140c4100090402c150307051150006580740c5040450071804d101c2203159071410002d010901596a89000c5140c559041054a00812140c2c905100d000c0008031986c0200e84610b07600c2c0545110406514803640c010003180b074240c00b1a0b402010003c0d001401100c0740500b802c103100603d0364690010564040700b540e400316140c018040401c1c64140140380f884070b422202e0094210040d46042401150b4143c0b11040ca81204910122510f0a003403001a00a1103100c030104901c0c1101c43c0c0c002054188c039841001400d00880c190b503443c0d41d0300d10610013613412004004180c0078254056a00040860070162807502c04502100c2001e03846090181c41c41d88070340315200b050f9000a60310007108511680c6007030785080c1c81c0b50540c2420644034018101c4c0c11240103009800e03101203145d04003620380b00c02c03041c020040202041500e080829209443c1d91102c030003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 432957419 1250 432956169 432956171
    0x302071a0c070e1605070f02060d0b12060601120504110a0f080105070c030e130f0c051e09060417010e0d17060a030507091d030c0c09090d2a020d08040603 68
    0x4181510402e0a4810b1300a43d650a1449110807070803116540030035000c40310b08180001d428003684815020309145d588000001506c0e00300c00080140d1420b01c1d69400c0c8180c0d005d50104481a40d01040288440030810740104058969281c0240302d800e40103e413a801201c11103001400341001400c81c802c8904410081000303864504d0212a40c280c5c03454081c01103802c0d0b09150f001414070105038140000020300004040300101c0d02a015030360640c140d50300140d804681c104160b0042d40c900440c80d00e800e403101d4608000f64000c20500c1c080c0b803007669800d030300001007106480c10079000344440394010030a80340d040d850200b000d08581ca44180040503245040002402424100e01c2c90050f81c0d0030000030003000703140c0081500a8900c0049051026410008110040c80100041c194400815000e4401c1c1d0b50080140320700c61a0080141030b8580c02501004940c40d0801040564145160b080902c07609540585c400c0507505218004d400001c2852440c040c440b030003000e0002e039102560 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 432958669 1250 432957419 432957433
    0x705011b17030618090a030c0f0228060503010e04260c071401020610090203130807150b1f0305070c051c1b0c14010c02030609030301030302011404030f0c0302071a0c 73
    0x11131200400c004441890495010048400100340102c1980700407910501c1401840480c07603010611034140321810082d00070b03000d5038a0707000801081545014006901e00715066614003010a0703140c42c00500301414500041000503070440c104034250741c00490796040b0035520428648039581e154050312450943d4805a0882e1030b466102040301400340340d413488005030140c102101e4a0080d40041c14410b44401c4440744a00001c01a10250000314065001040c80107a000a1101a14080c0c44650301c206810f540c0c41042c0299130820003090744151500095540d1200402d40b2403801064010700184a01c2d40015105102c1d44084050b0700d246507500c0d20b841c52034059141c0d002070034540c010004104658184950f0124906540724507005242c1300c810740d40c031900401e041890958124205400c000014024540c09004007035403501c0e580100c3c00245041d45004142d01840144c220400040b913000d40d041c540b00f00b112001508800700140001c44003640d958104d5406030240f262180a000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 432959919 1250 432958669 432958699
    0x308091011090918010c020c040f050103081e07021e0f010f0c1401021b070f06140d0e011e0c110a0503030c03040503040b070309090b0906030705011b170306 69
    0x20003609075840c0d0112070182000001c0e0100545014000c0ca0f203090a08500c000040d4450709000d080f000c0d0280b40c0190a007a0006000d00058419034480310408a080034010030000726648101c80c02d25010000f8010880d0000480302d040c1d102e40c10010750f0bc44601032141400d82010800c21200c050209c4594811030fa0f028015158660300200c0180818140da01c1c4502155403a4214125050b40748001071806548090000854488110f40502940401d1003802100b2040351260064801420b0151011000001c55a120700c06c541811118546855294020000075000f803581c20340c40180c0742e5001898500b1882c002c01c2c1e00031458000400030b41c0103184e18500810603c500c5500000910f1455944611091003580083e00441d2076120801c0001201d013192700140c801e040c031a40e00d86060740d25100c01c0310242c92440780c1861051242c00203006203682c00041000031688203007065080800780b0346503030768548151600500790b210016400e04050b0f000700029885800d040f5480700c1104001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 432961169 1250 432959919 432959921
    0x9061701090506060f030c0909060f071d28080c1806060304030c051203010609060806030c030601090b0a03020303040f03020910031a0402120d1d03190204110c0a03080910 75
    0x800b03800ea42042011034060300b48401030414030000502121000c94142d00440ea0201d001c50701d148482d00a1002e2111034084440d405030040d10318134003422032901d0030200008010307100501c184602c45920700a030046040844010321008002d415040712a5100f4100381c0724031200d9103580c0b10b00c03600f21200800020016030503004000141c034181c11075940c0c0e0360a8540250000d070691b001c0c400c024841c00002002c80083d406016980c3c1e911042c18039000c0c0c09001840040c0c051b9220380c001c00c02100c20f85d100054801d04503900c1d180c000c1001c840c1c50380800c1481d500c64001035018000000d000c140e1840d03101c80f00044920a0f20b1448141d034480030000c000301c645000041c40040448114402c0c105011750070354100303000412880482990401040c40c00c030908010070081682075010b0113064003504400011050258007800d1000a46201c4040403030040174000d118a50301c0e0120100140341c0000c0e105150b95007000c582c402d030600d040240100ca4225100b107068442d10103c0550344400f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 432962419 1250 432961169 432961181
    0x1810050a120203061c08090a1409040b220602120109140a0507031112040c0602060907060c0519080304060f0603030f03091a10031a0c0316050408060109061701 70
    0x103564940e910298210901c60103548064000e0b80e1001d1103254000c1d441c0c4014160322007003803082000658402d075001c04c0c080c4000d0580d1041c0994001200c081c9011749912072500d520940c4050b80946036034501440d0303d0340502c1ca58031001702a0340c200c80c4d0f4042003081c0d401440700c880d00c0083d80480360380c0d07400684203448034429400c9403691258041103038000b00341c2115800040c0342c140401d5a641c0d031010384207290070003100114039610b00018041404910f0507207602400d604d1001c0c25007450100306080d80c0300c3d0144182c07000c2201482180c03080c00014000c0d5148200151409507182c41c0e40e08103021260000e031400d031200b600c0d008642d41310a90900c640021603615894440450501110903001801a1400bd031034440301d5410101908a440c42030324420034030f1005c040c402e18214109080503000340761540350060703074440074400c03841c2d1084d0a5075444034444410194000722024111004c1c0200e0b40003a183e80304000000c1001c00300c5030082020707540368804840d0f84444c45a40c0c1808c1c0d8030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 432963669 1250 432962419 432962437
    0x60a0204140f102a080307030e010504081e07080703020c10050a1202091f0207090f05010302030703170706020c01020d24030303020c1207050d020f0f03040b07140102181005 76
    0x108001250741d401d40a003a40711400d25040b8001c4100f01c00350350034850613030300301001158240303800401c101310160140310781000e800790000201312625050392a86002d1086624000400f64888186c0890030342c010704542036558412140380d1a2185890f0281d40c85c40504103042c854820045910461403182d4190f0300c403110190b440d00c1009410408140096004c00c003101c1e0040300078219000c050300e1118020340149919801024114a0512103004440c8546021000c0c2e500341401000175913400142007040c1d0790080300e003a07900140320801490358419070302d0040c030032800032034075911085045d4064090003000f8501801407520420919003001402484a05c0100c00b2a40c00d0012a210358040c0c09035100c150100c0c0c699050840b20300f00260080281150300c0c0d0b0042c0c0402403004da06100728100c3e002e10360001c2c070151403a0190340d0f859002d2800b450703000c081301144c4402401803648800c8501e042900c02155510422311411109085401c40e90707000e0500031034400100e40c461822103040307075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 432964919 1250 432963669 432963679
    0x150307110d0207090f06030203150a0506010c020904020906010302221d01030b070315050415031403090303070339030914010516081e040e07081303030b040e060a0204140f 75
    0x58208004913004004d495010140c1944d6540040016103003008980100b0b035000d044900b56203422004a020f072103000f011a4100310350400c07481c0051710784407180f540069040b280c403405580d50a0040b002070082000e50500090201e400140d50704100c03c44c0c0c01541c8070be40c2c50113490030314900340140e168800c0c0300081400c0040300014400c0c034803a90082034882e03031604032581d400390f0703440c00030b030613038104000c29104150464010010000d03c2c05030b00300c010360088081d44c200b200000000c2d44900843c0d802800780880b5107550108052164031500d024101041c00400701d46000c0d59900e280c0c001440d00b140130840c0301c0380218011200c840168440c0c401655018904480329040d10003415028000711441c032014004a81e003125481400503441502ca46066202c3d803074041c4c400014440941060207206040f07080c0030072042c0761008a41425014100410103440d4900454010400c00c1c0121201d4081c5800748445181036400400482e41c805901304002e1400104025890740902c001603808 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 432966169 1250 432964919 432964933
    0xc030c0105040e1810020904271e0503040b0409051003020a141207060c210e04110c1b0301060602010b03071203050409061805070503060f1c02150307110d02 69
    0x307000034849207500104130030003020313990045103a4900d404074600c00c642e155a00030a07103d1441c10144a40510b0b0703442507901d03a00c1610440c0030b6401c006400c0001915281c043c0311060349826080b400121101c0d40306040300d1b56590ba03582600c046801c030f030142004150901c400701e0002c103010840c15007503a80050900c013480d40742504482241441040340b5800c00d030f0403c0607154503032003442103000038401074540594101061400c036071200011a603110101030802910400d10fa070042214102d0001030364000340f01400500d03000e40c075008030717041340744584217400e0030110300c0c9130400745000044800d400074040543c5a0f032040c1c0c02e981b07048031425015401400c00300303c19600080d551150300e0203424890310303003a2141454019103480d90000340300d141c40603080c0c0c80444624401d99502c030801c1d14040e411030600d2070019040d6113242e2400361241d18001041c90b4040700304c0c8844082ca59000704103001030012042c0b03908040c1c00442d03010010443d22404143c0ea0480400d02c0207003d0a198050244 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 432967419 1250 432966169 432966179
    0x2e0b071b06180e060f090a090209070f0f0e04140703061802120a09140d020f150c07020f0303130303080a0b01091508130f0b09160f030b0c1612020c030c010504 70
    0x196190044c10b041c0c0c4140300152101031034130b035905118028203204002082900707660060042c1c800740509024100080e100640c1d091a40c45154044440f4062074044a6443c0510026000e4260004140704d003c00d1503080c050006d070140c4c0304604480c842e0361000c690710f0100441d5003c0303002d00841583e01600010018100d400079900c140f41240c410982c03e008402d81140c920b02d84100d600810000d44d2114400301d200c84810401c00318403440f280b807420010b25100d00b40710740300c1c02200d40007401004d140c444400a46d80a00c16145109010488120096030320b00f0010b00d081d030b082d60341058080c942680c1001651040030101c080d20100c5c004201c00d03e4209030100d621020040c41c0c90702800741c10840000207688070303142c800c0d00350198070f2505007030a010b858107040c40c0700c1d0b220310b1949d920342e0b0000b001502140c024620849822641e07a58499513080e803814118441d65048000005045410030200138410060001d11303000c80d0308554a10f02450107040d550b00000748100d012481c240001c01c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 432968669 1250 432967419 432967439
    0x120309010e0406060509010e0d050604050d120603020a1701061503060315021317120d020a030b0901030b0a0f060b030a02070b100e04110f090a06080c03062e0b071b0618 74
    0x880301070302404030503401d8a0b90728ac0d03d09041068404641a130082e0006030b80980d8480113a1024008a4104009842c44d6a0024100401c4d502c80d5503000b152503000e210200000394803141c002c1c1180c5443c04007403495000c0c01401440c04e4002103446440d4042d20785002100f510030303583e180030418501c41400d0704110806014214049401000e413180d0840e104a240b034150241210f0391103e80b025072580540c68025042e60148503115024089440041000c18800c51070b00360014514580020303000300050181d4040c002030380040b01084000428401e00d041c1c2a130042c22503038002c2c903903c08240c42c0e2103030240015410707101b1460891460004030300802c003c00c01e02040050014100d142160344880424070891003120034200700d594a1004100350320081c085500241e0301100500640c2c41d104241e1007000c0c10099400740100720041c0b9041c54206283d20078805411310200d902c0e15034a040c41c2c0001700011403018204902c4026100150780c40c014105070f01521a403120700344000c0d052187c400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 432969919 1250 432968669 432968687
    0x403050d03150803070602030708090c0904030807020a0c0f050a1a0f0f0c151801023402120d0906090b090d030302160501020702030106080c0616030e120309010e040606050901 77
    0x8091034040342e1001800710810001056041e00c25040961030340303020324002c1d08406000300200340342e802442d08882540d59000750154044d5140c100f403034581e141c61604a162041180d4001c0482c417003e50085020ec10141c419000c0358400c8600f00d43d000d4940c805131507010f0100d8490303000400706002106100c50010064051056104511801c00011b00c12075494090040c0c4a80e4140e8804000d0101203011802840c440e4080840258038121488451400f11028040e0680507440036010160003504030386007040009400801c0302d4061030010966640300c400750640140402c4100000040460203115583c0846505200d45c43c10400d00d4014050b80f076400040031030802d03500304118800d00500301d040782c0c00c450041d4001070301d6031107620506003100c0c1e85412055066120403032803102651882c040304d08507844010200ca0a40d4540b4040e9403c0d014540400c0d4014404d00d01601c2070b0314004090302c3d200c4000d0340c0c0d0201c0b84c2c24030070600c802c44a4501514000131420080c1031b241e135000c0d0180c0707 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 432971169 1250 432969919 432969941
    0x17010b1f0f020307120c02030d02010e19140102030c030a0608070e010308030403110f0109050709112d0f251716061d12040e01180207022808030403050d03 68
    0x1e0780c030306413095540105540c2e100c01c1c07980104d03e00740c3e222400e50070f04000740c0e800609036000800420807540d03640b035982d465140c484180c40d4203d0411408220042e0302401500070300c40025900d13070600c50a6041260811030f075000401e880c0c040009802c03a00083c40343d04403003c0100b0f06050740d080d0f8548540b9076000900c19018000800c21042c0c02d0a030422144080100d40c400010f004107540c9041d45c20314140b540012045070a0640c0d00f84030868403012a010301c0c026401c42c421651100103400141c6000301d288080011001c94440c00844044004120101140b58202c8620300c03116010300c01480d0484004d81606510181da10b21241018020003004080782e12220071600b440d940d090581e84801c1600d05802214031080803850001c01c130780001c009503000180e090a0400120a80302041403203079240d003403506450248440600d038100c410300c0790041c00481440380a543c28541c1007000c003242c401103c022980010b41a035000c01924180c3e5441400350035540c2d00b412089003e80828101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 432972419 1250 432971169 432971173
    0x3010626010b0a170c1801020f01140f0604181509050f07090c05040803271e091506070209150a0801060602060109060b0703180f17010b1f0f02 63
    0x1058600c1052000d445000304000d078100c0340d580d16454001880c1501d400c00d14809400c11405102001c1541e00c141c92800120400400d00342d800e010040740790004142c4e141c1015407070500c59001380d60702c0c5c0d85400d12400c03d404255a0903101c00d070a00c0100da40d42224001c0c440003900445c0c00180002c17903589102840204003050b40340340c40d100c003405c0c0303010365002201a51249a04204059141c00361084c10649400c2042c1090300d000070198880c4036910b982c030f1041600300200100000300c8244074010b000701030000e42c08001d91b80d80440c0f04155000300c00c0d11882030302d800074650180c2e402c400e8804900151105040056940c01e00000381400b820389a4056901e10751980300ea00d5008204000b047c4e0703400046089403405034064140101a000604800c0c10311006024101c880c0782100c102c01d60520744000110048007540203a00c2558100b80b43c40350040070b0006186262004030402c0c880910001c00c9003172451010000311100c0741100c0c0e14200d181c65000c04840d80981c81400a803556401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 432973669 1250 432972419 432972467
    0x2031803030f0a02030d0e0a05030406181203181401050702041e020f0301030b070c03080c0310090e0f010f0905060601200d03050414011505040b060c070324060b030106 74
    0x101e010300340e822600410005900110343c1b08140b24403802019080790b950009024420ba031500da1a0b00c038461402040c003803210400340c10302c102400203540c03030040006142014500000d444c004011080e480c8901d0002e80d81e8000219002c002a445a059004140c6400340350480603400e00c000341032014502d42c51502e02c40d805038281d031106d000400301d9107041c400741c559130341c11481c100944040140c035103000c100c080f5454500298001030903d801c220f8111a0039217998850f10301c07240d80309131a0032540707119042030707413042031601e000a8480119644034024000d180405a0307030340c00c613402c101000c2c10503071007440031410390350181717910388000300e407061580504030b014500031454070502506400c00039940340304000902094030310041d0f07419030784030003403040c44030420310240c2c0c5085034086d8a104a42c0ea5282503181c0da525002c68000040380d00544080c0c40c0d5030708090105498140090382c004281c0c03040384060240340d205900c00e50302c0940125045900700202140c0c8070072191000444500420323 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 432974919 1250 432973669 432973687
    0x1603050f0406091d0c030a05130f060c090b16081c090c15110606010311220e0105180406020f040816051009060801030b0606130e06030c060304030203180303 69
    0xc0180301405030380c1c80e2042103d29118403100040030b83c502000044801a042c8400f0710780300b408032500011541000314081d240d141c104c0c20b01048400c1c0050140c0e00e4050090100034103600a680c107035005c3d40707446800c181d450181540c80d1094901700c03203207480e28040b110005000030000c3c18405100726138030b100c00d001122661b000c0741e00b980c8096a6100480702c041241c001b0780300c1440e586220510300300340310007903e40c2c055944501c00b81545d0305154580301010030f84041d110603501c840750703800201c0b5038841ca1000703001820380145c0241401c40c02d014001248504203406030900f440c4440801e108140ea8035182c4400a410444641820381d40402c0f0000f901c800070460b00044140c04c1c60791144c1e680c81c25003005401200e400b180800e10590705010811903070004c075001d0440c1d03082144500c240e42e601c000600710384110311a0041414010078003107150a1361201e5944131700c0007941254016103c0c8810481c0c2d03800200e5004005034010001c0c6480c0c040c1004071801c0b240301c0641228207011080c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 432976169 1250 432974919 432974947
    0x70503010e060a230a0b040b010e091b0c0d080603010e03030f07050313150f0c0305060607020d050a0b09060103110102010501270e01240519030206160f0c031a0903160305 75
    0x9a550403012511008000e5540c1f502d4815144410801d08282442e424500d012604e06040205900403200d106000b0350048564402102e1383c0740e01c04000d580102108640140c808001565500d00139032a00c2d094001c0124004200c90291481c0c171401ca00d540e551503012969980010024203d04100f0007856000520b41d21102c00b40382441480851000400c3c00050104d5070444004001c06003402c00384103858039220101c0d80d5480e0180c40700c030038410007402e00710701d0200d0308000140501843c0701004002c88020403028141c0e8440d40c081600c121f20000124241c600c2030140414289507030006065403244941c40505410500101048019550310003a0864035041801400c04140324801c09026600a10f15000b8001c110b80c011750300100302e105030242c80300c03e00000b40540780004d4061000c0610001103c0c2103940904440c00500c19441e0080740d20280c2e10040350000c3e034801600e60941d00e560010361140500400443c1401c01e441c0c1c04a0901c03100c50029001e1007010046001c0701c2030b43c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 432977419 1250 432976169 432976171
    0x70317010b191e03090f02060f040303020d0e060d1e050103051b01090803092e03020712050a140d06030b0906090f0303010303080105010c060b060c0f070503010e060a23 74
    0xc0c1001490b00d0350400040210000010000001009000248030300408040c95944008004525002803414954909000c0c0190303d140c010758000c07400300382ca010302d00b0070354010b00682e486542a11880250b881041d1880590312071a00c2d031054050020803150091a070100011940d811254080a14040c110001b120401c0c0c105a50503008040c0841c80d03c3c0150340e000358900000c2c0303030090100c0d2500082c0c60b101e00a20307505034810b0b0507080c8501d41043c220040366050f00802c0c01c214425198a0302e0107030082d401620200c030644512810440d0b003034010419035448481c9910b8682071501c0c100d0403010164002d00030030300f00039a1132030701101040908246602c220300d02c0000304150b0801104540c9021507220126003154020001030001a9002c1ca031117044901c2070904025400803440d0410181c0300d00b90b5490740001c00440e01c455582400510a003802641209030303803440e91900140741c2641c40d80002d1020030f9002c01c001c2402840030b50f000a014614107003d24000400e03904481c45c59240c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 432978669 1250 432977419 432977429
    0x4090905070501031506052208030c011b080402030a020111010e030412020f0d150209030705040e031209030a1b0501020c0a0b07020708031c1505210f0a030e0607031701 74
    0x101802042c001941c044c42041c14141c3d40b0340506a0107868250002d140d4800d0101071407001c80100480e40102024640a00140140100340c0f500c038165140228002e02c190303806c072602c52546401c48110309000b00703802801a03802401822081e40702e500191801c50707a0400c1d5a91565075403200c0c8410340d0081c8050805071038582c41180c082100360042011200d014603041303201d408000d0000300051200c1c10421403123300980003684907082c50300000d081c5121a400141c00c9800c0030780402d82d0000c04001450004c100c500c20511640ba005031542e80c900801e10f1820228021401e4018500300d00104245a28810300000d444e002c4440300050511036000400c40f0201803400c1805102501807140c0350107011607600560600218000b180402403440400880d031a0351140343d01f04107103410b14a1f078068003003d1b050414034401801d100441e14865104d20110b4000c902180000441c0401c4a224039a01542d4003409080d00a040007500c0e84418801c80910100c040c1120010100b0400d940c0284 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 432979919 1250 432978669 432978673
    0xb0312042405130e15220e06250c0602120a0e0d02100213380705150408130f180e07050120010e060403110c03071707170102071a0f010504050c04090905 67
    0x18031704018a030549038010420b1810b40c109404000400c1c4102412275001002c0345c0800c80381035456807003a82d0003c180341c0050b003203e00010b00b0301c0042503250340840c054462454100504c07040030080365166080602001c0060304040400b40b030f8900e151b00501060345440c403440701c095964007841800440c0854182501c016030311084443c0d141c0c05c410b00801c1c0c0103008074003031814466a03600d5441c0c01901e851404908601030114052100b481c00303807019010301481090055490300359040162034944100541c0c01c080c40c8018415031454080c2d4541810310500414615050200560714085850b0058400e440d805c944001046070900070350200300e4181c0d000d02201e0419040003041c1c410448030f4040d980c3e20800c1030321180e0310001402c4040368042d80180242d03069242da05030400710300d40e21440710962440d4000c03a0064041d8000c013610f81c8100942898110b68010180207140d08641c000b03680d54400740108840d0809800056001c500000060f1502e6110f46071032045460481090701c090f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 432981169 1250 432979919 432979969
    0x3060f130509060f0f010510260f060103111209011b0804021906050304020906061905030f010e01060507080708090406060509040b010801080a02040b0312042405130e15 74
    0x158001c3c000d081c1c0241035141000314516081101044201c41846020b000d40c1641400090483c0300c2e628014070801d403a600c5036800080e20b00405040300c01505e5010300f60100d800800d50035806442090303c1409041510707400d1000804200048800080840c21955290308650003480203080e070380c40e002c4849440f4142ca904060040c06941041c0d14030500d82c20110f07000c20301c02c540c1c100054a031f0090b412519400c3d95503902c404181c080c0952690035024449051100d43c40640040213148248a0084071180030b0f030f65040d4421800340f0a01c142004030b6010444000400c640000404816004e030213010701c1d02c851036011401721540341e41b00200140010607502003d01d030a010f0310080710805d02c0c0c076504a505098055880d802d407041c00038800c42e40c40603101c8a68506104404007020070f05d040c0e41e00c0f40e03a0750385d4060900100c25210401c5a038003c00d00f091403070244040c1c48891020034070405485081c030100c0341600f0009402d843c83e024a11010300c0c196555030729604111618100c2c00900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 432982419 1250 432981169 432981181
    0x2072601020a120c0c0c03110a0806011401080f0601080412090b0406030605030f0c2b020405010303080609161704050c040504030f031811060a140304032d0c030503060f1305 76
    0x101c0700c6200c4e0400410503a416080c01060108005034140d075081303111055150081000162a1800da511902503401128000501030751214a030b0300c1250001e80342d504450b07640c0b44420408a400b21b6010380807620500100740422801c40101c1c840b544d0310f0a2000150761280d001c21540c1e00140c0c40240080e40b5144c0610882c2424489800d281180000500b005224180043c2c01c071000085100144200329107201ea000d40001414070100f0303005003003080b00b940c4901b8000c1c50b101040360b60354082c1c0064000310f00203401c2c1c0d41d11605140040e59400c810116100c80c150358006018205031010702c00c240c9200180e984a01c41c1901451081d01d0341040170500107405401c0d507c02090440d180c02c10b1340464070200b440d5480002c4030301030031220789030764140c0b1203820749003001581480540008040100010150401203100b05d01690000b4101d207103104481c03000305849101401c1d0300081c0d041f01c000340064080d90246811981c01806010500d040c0008544895030982082655603241c10611103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 432983669 1250 432982419 432982421
    0x1809050712140c0a020c04050901090b1b0906070f1a06040c050903030d020a0315060e090c0a1b030e060c0610060f0516030c0602040801090c090c02072601020a12 71
    0x1040040c0700000d000c0120080c0400318250001042003022043c00241c0d02156071003403268500340300c03000f442000b0030b00b8403800c024004d0450001c1241d02d0600c2102080380c610a110451240081c01c0c070040740f608443c1028419103401c10b0000302e0300c2900d00c95600002501c94514110300031580182902e0705d28201d010032003a1043c0426140074030004200c04501610080112000000c0c03420001d669420070401c1100144064440c11090050001000c180030340c0c0102c3d802400401110f40d50308640340c10b00020700324421094914086402d07000302ca0301000420351409161030082c03c02d2010100203a012440540c00f140c1d01c156550090303000c0000f215015003080c8054952841c000160303100e82100a08248904c2113001051740044601f80d003014407584910740d22940c095425902d46940301c0c40b8074080c02d010b000445d000c4640000105004003c2d104145d18180140d00800c0482d24000412089014401d07503601001c044002030581410240014480c144141e07070b0749a001e05485000714 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 432984919 1250 432983669 432983687
    0x90b0a09051615050702030f0106080319080c03040b130b07200c0f1e0406140103050604090b3103050301050a060c0201020703120e0a0303032019030504020118090507 73
    0x140030b80e010740c80144440d20700300a50030724481290810365900c41e4503000003464030001c3c003100c4c02c0540c24400e02042d00c80001c4090241e16400c1c0f40180b07610b110768403040ea0342c22012101c0c03125042003400005d010440d80309006410403060090200401001c0e10b450098400496545001c2800e8441320001d203080e140e2104030100b00e040152030258501e0001441034071444c14154070440951500c00b5110081390b250389942c1000801c10801d05540e0102042885014810309010030f00d000d000584c0390078a40a100702e110f41c000e0003a6410340d100d0150582c1c040d880408610b01c64001c880c948980b4044080070300a10303019840b034a88940c5090100510404940c00071001c01542d80122070050360001111010f5960003001506000c664100841e101018481115400301c02d0250002c00c2c07580681c022000c0c0004105566903009103c900042c15101c2c84080070060a6281d40d14558248240d01003034119205151071035a02e80f01c07125900f070b20310641d04003401c86540c40e4140401d07150080074403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 432986169 1250 432984919 432984943
    0x30f150d0c1e1e05040b01120c0905130b0d1e060f0e060601020f030a23070f11120a02040b030c130c1205061c110a091b11070308070204090b0a0905 65
    0x203020021145950495503c140d00c035136401180c40c1c0795003034503985c0100c1300610300118414042103c0001020700404028003071041d0b900850000a007102904d40754050420b03103010140c5054a144425a161421004030340000003600400405410020b0140e0040c0c03400c0d0108504082546074110150782d041031130203402503055600c01c041c081850135010045d0b6071400041d003000074841c14010380f4070a4101e8050f015491486002a040c410400d006000b080300c90300906400e001c3d41000f8083c000181241d142c8444640c1c00142d00d84014500743c2c0000f1310032500501520b003004c403c0000f0408071100d00c80e14145003030310303400c1001400d17030300111050203000e90840034882404c1403008903503200b1409800d0007030f081c2d030344000c0c1e01030103032680394500582400f8209400d5143d503114880000c0000048800c031040500918031040341c46100710007404000381c0c010b40095031440ea160005503104440c00c030780213510340e081c903c007182408490500c2a500c0902c041400303080c81c82c04500b08030341503000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 432987419 1250 432986169 432986189
    0x2040605010801061704110402030c12011a070b100b1b010f020f070b180f01020d0e0705010503010e090a080a050d0b09190e19060c0f05030f150d0c1e 66
    0x1008981d500219107000003000b11707070b420526101c0c3d007010403040003080c0c00240c0150000041c40440c9a07100000c100c4083d81109842140c2d0321030510402e0b1034100f107030300362039680d01344110804500781001994220705540c10ba810b2059544141c00c5890b007080c14580c0e04107401014400b4030000c21b001d2106100380e129411803910380400003503900b60003203440140c0321840c00342c00074000702503002c82504074445d510201c41300302101c039040c0c44c0030798051190f003059941805840f440d0300300b00003264415588141c541d1070550b82421282e124100d4000c00e8108544a40c6d4240000b1502d400014040000140d45895032421000140302c1076070700d03444041d409110b034102000b198401000c0e04269191a6010215400d0000c0842ca4035042051511025414480b14004100841a4010b0000400d40c1c0c540c10301403620800d065655000445440b41d05100c210000f409d5889176000700703820000d000308074565049980d15000c0b031003415900318004608006108041402890741954018800e41030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 432988669 1250 432987419 432987421
    0x3020f061b0a050706110405030c040917070f0f030216060203033315180303070b040318030b070806090a090503040e130b0c19090602190201020106090e0703020406050108 75
    0x1078440846100c11140d240d02500c08200c84a59038807031400c0f2a00190440001d00034600030080f03c410a0303101d031040b40c4c424422101b1004d1242024042c107d104c40c1c200d4840c501c001a005040d011541c4480e2003200c4921540380c00740006048036540594484c060b074010aa1900c030040007030040c244a0300701d40b05540c0103000b009209200c0c41d07122640780304000b6200c10400b0f50500301e15800d03400d00c0300095201c100b40001c2c0c407001079210080c040d44150880c481000140e08414036440f4407603000c0281c00c0a40e491300041c0400d0282443c42d09407002038000f079040e0355580d200e40d02c0703c40c0284c03441d0002540c440140a0300d0f1400201c0f81e030308840140010819803032075070b4915a880c865031240880151809000600c960322180500c1c0074030383c120702000b00394a0b100074070419540c003105003000e801c1c00030280c62003070501c1820500b040d150640c0003002c034160480032500500d02c1d10070003241150340b44c107408610380031035005402100c500c0f40c0c02031240504510401058071415004a810001000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 432989919 1250 432988669 432988681
    0x17010c0e04050f16050d020f0d0501140a03060c090e07030b030f070510031a0a030f030305071b030503040f0203030c0706111c050d09061e0533030f010c0c03020f06 72
    0x82e5080c0d82007100c04d01455148401d41a09890350b0051400039004a88040391050303601d084403005281c0e080700c81004005503a200c403000c1c0880c4851085840d00606156801e10014000e580922901046400d00d180807541d42d000300b540b281c90403645040040d8030b42c0d40109050804100c00845a440000900380090403e07010800207001c10b031300c2a01305521075011038420401c150300342091041c0940581402500c0e400c0069400b00e001604070f0000b4508030020302d8851080001c2180e00c100005104140340c0c1c640c40855440d08013410941e60701c43e00300007140042c0c1e0100001e1004904900142245a00e001409004507a814107060595080400140b1070380c0100941c04505041e0317410b10a407258140490403000749100c5070018078141c0340012041800d1801700c42400c24110804d03043c845595140c082c2022003101080205000394500e004040541b4248881907100e2405001c0f511000312002e5031034203442d4a80c003035501081c805614001850b41c14400c421191003441c0082507682000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 432991169 1250 432989919 432989941
    0x1150f0509130201120f0605101115060f01031e060e07021203060927070806100801202d09010e0a03030806090403090e070918060803180a17010c0e0405 67
    0x2c41161140e1b078440c29071200e440755901110223484003900c1c1a171280e00d901c4002c3c1180401051030350305442414080e0302c000900c44c0714548600700240c01c1644107000800190050040c0410880c248034925041a00c12001807140c01c00500c51000300c100d5a041c50240a4100b080074881e190003c40b040040201548503841c5542d00110040340c0b4800704040c1c80b03c440840101d19035503440368012030600103a07200000400c113009401d8032000c03c1000d6680e2034000d003200c1302800f0743c1c0e11813000b00310340300c08501681029000e02da600e06c2c1c0e10016400c1c904021801582c60501c40c00030710f20003044034045075a001d40c000704294400c4d5039051700f01d81140c0b4060040403000304204d1081c1c83c56000a0304240c0700d0341f0240011712820107580158100814082c0c4001e010707021303a001085410640000035116405544d048900c804059481e000600860408000003040d030103030081380c80c00c00024801c048112601070060100c0000400300e00840c1d00810400a40010500c00d50400c02440302c10205 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 432992419 1250 432991169 432991187
    0xf010309020a0e04060216080703030501050f030d230406020105011d01050607121b030f08100f0e09070510080414010917030a0902040c0c032c060c01150f0509130201 73
    0x100c40041010f40d556450300700060f115108a502c1e401915458660810000901408000344030392401e224907030305c6200b482403410224400035419402036415044040c0100048841c0300140a061004018610070300b00070343c1e12680c800c10041c0c1d9190010489002e0f007241d960410030a481d9a00e0565252800150304d5000b80039000d0b01e000541c900852081e0700541c07100c0c608810721901e048618140c0e060140008000c114000045103060300028144441200c81c1d806461202c51020020703030401c8400d0340e41e0b20000300000001e100d10b01000c1815524288915140409030307a070030603103203040d1405003091450750640f032000da8100b0f82d11000140600307082403a1700c8807490f20680c5075500e5640603c090901c437800a50018030304040c031032002e0f82c000d0080f01d10710f00036100e4860010f404e41e07580320f0392480041c010040340c4d90710703002c0781d15403034000020007021010f0400492003140c00c0070841617039620341d80480d4450a41c1181008a4106801c9140d40000444001055508640c002034000e03c5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 432993669 1250 432992419 432992429
    0xa14070c0506220f0b270409060b0906040912140904022d090f010f030f09080c0f0a0f03080c251101021501060e03031c050907081c1d0409110f010309020a 68
    0x1b0200b16420b00080300b19079042148000c206120942c660701f000c1001f07145240c00d260260608400080d80b50030f0901a0300001c9030b0101205041341e81144045031700762481c854400180c1001c0104018550f9030b0f0005d00250035080d0510a0722020480107401d80d110307001101041c200c010300c135560445d502c282c1c0c0600910400e0030820350004040344cbc110300824103411030301c0c4118030b4002e024003804000c0c2c020741940c507240c40c00c407403200060384102ca0b42c0d03000e170810050840c01001480e5000078800d009403030b00300c106841c0040c20b200c507021010030181c5040303c050f282480300e54140d0050041e06060354840e80303020b001500300960311440001001e03005005640c103000306820741113040e0700d0400807a00030307091420b81d051b2521501130040000d40f17020350b080c180070f00c03c0160119a0300808502d002c40d92005211a40b034613042d803201661400c00340b031519442030300d40d120281455100e5000740d0164520585d2099400310780402046a40743c081d046103410985010a08401616010841402d0720 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 432994919 1250 432993669 432993697
    0x3120d0b03011b02060a02090a080d02010c1d0306010504020702180703091505010b0d050709050d0b1e0f011202010c0b040503070201201213050d21050a14070c0506220f0b 75
    0x11071a0b2300845d1030303c0440e501c200c403240b28030010029555410350101c40c0754442952800280030200022442240800001982c5500b003e001042a40742a0f4000e01c410b5201030400c81c171260303014640003080c2e2400c50f000750104e901c0c1d45940c020000c00d840c0e036203014141294100459414510010510b0085c0c030542c0544175a1140400c402d90301890910004200044c00b050460200f494403842c030002c00d644e201042c455000d151038a00010100f030500c508450700d01000d19a280041080030716080c0c0c24144e0520103031000d960007164001c6502c07882140954015562040240300042019a00d000541c110162002114000110125080c40d5480041c45101e0704e440092106904051040c0d01c0320354080c202d15910410800030422840e0740142c03000241c0070405034100140c2d4079104101c0706500048031a44c0c0300c180c55903507201410119008682200d07420b6120701c0840c14a5218400100c030b0070420750008500c01c40d0303461405003d048a951042600c80c40c00324428454040c0d9610440c100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 432996169 1250 432994919 432994927
    0x7050a05040e060f040c1d030705010f0c060b0d0627050712080c071535091006030321090b07050c160315050702060411090603120d0b03011b02060a02 66
    0x2030b039840d088444d032003030300030070400c80318100c240003500580014242d00d200150844080d0072501e401b0401c681100d5042c0c50740480301e1a5590115120000d01804803501591000110510380703070b001ca822103c1d441284d002a400511740c031a611b500e89210301c06143d9240d101041800500d0200f00380e01101c69a04660015604501d8041414060051554000d2084c0303a00080c4805140f62030b20200105070703c50b240301c07121000100d560240c409030004d10200b181c80d905d0a50000d41401a40d00240030015203411011018407042555010b610540008180840501e0f0343c9000754450405c0d03500c03021082151004998900d4055100248004140310002ca000c0121310300a1000601612102401e19000d81d10703880c104d1182d000b20312601181070324080000702d0142c00060b20a001d29007011203002140e04040030007000d51801000306e50107000c0c010340e540e1a058800064070b4202c0003540701084101c2d0303081c241130031a0210f41c0c000059a01d0342d0040100c203034002c00c09680010f943c25015170350f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 432997419 1250 432996169 432996181
    0x91107020a2702071a071706010c03031107050a0314040315231303080c1c1109030a150e010b06030a0c03060515130503010e10020c0a0b100e07050a05040e 68
    0xd00b894100b0701644207000198080c00c10001095424004036102143c448a8907418811241c0c0744062500e402e001c03d4043c0860220b6002d98400010244a454003041181000f0b25605d0719802c5018111440c2d0300c25030385141019005a205640c0380190300364281084c1c51034403010286041442c0c1c0046095907a0300340002a00e5200c428142100c00005250550074101d0888800010a070000c1d40011401c501160070b00d80c9000807200f400e0310b61032020200000c8100880010480a0703080e10030307000d040040740c0460305c0030700c2081280d070b004081000003150229090b0040d0f42c41001c4088507a49001c0c40008a6a14407081e25000b2685400c000784440441405030010300880d040a40e010b1030564807039084c40b0300ca10040c03c10f642082071111907540d9880c145420307500d42e01c80040e690340110b015a416050158007070038117103e803c3c1c110346804500d0340350703d116504c090700c485201103d007080621400124840c015002681c902c0e200d0300d08036410100824900a50150500c155041004620 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 432998669 1250 432997419 432997469
    0x60f060a0c0809061201080c01030c0c02060a02010608011113090501080a0b041e0f1e020619020705040c0908070e040b040b0402010c02100302090f03070b0304060b0a03050d0801091107020a 83
    0x202038000645010b550311114205c10b4605042441143c5a5100f00d90461209520a001d40000c2009540301c0200c1002103600300141178011841180456603030342000101003009010310084065112680c65640b407a40c40300e45645800b42c0c02c444962030806004001e5494001010940207030800703072040454455251049008030b1000c0c004926007412078882043c0300447d00300e505801e00c0345d951284801c000380100340f401c034409180a50b01035018400420701e00c2013804980460140391054900e0030f920b0b0000901158a01c014040004117808800e000b4520304008640150070155000c0300103180694415000d05d00003000100807540e9213000c5011a40145150000c4542c02800d05040030440c86e8014001e41000488900c81e015020f50002642804900b14050b902d14041940c034584c1d40f901e0300e0300500190309140341c0040c40428000085030f0300b4000001e07000f001e50380380d40003940b40c680c5940566000a144003090f09040116000681c1d07100c0340c0004880410001c1c00d0710000d811640d803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 432999919 1250 432998669 432998677
    0x503070f1d2e050f0414130309030803070e01030b0d020d140c0306010f0312020f030f0a05040909030c05062a0c0f03040807080c0901050d03180f080a05010e01020708030f060d021017060f060a0c08 86
    0xc0c02c0702000300a2000c00d80e0442c101019858ec00c1c0d9081050000358000c2100e0701034000da0181d0025032210201c0b0205e000444207203501440c010860300084494008a460103d02740e11003845481421414420440d01d02d014032180b414900c01403440d1200031121680f01c1c0b040c2402c11030008000652442e401d4015002e480045c04952002c01601c8201d09000d80955103e02c412101801003000042c424100f07a00c50050110b20b642400d40780498119801020780e001503d00300081c4111011009032060401c0140f0240444001902140740342440c980d250007040c2c15105c1c8507095460040c031076900c0d2035040f98080d40d05480c0102c012010020840400300340768000207030040e0508000b00701c2c0c02e00004e4642440d03120308001c10a07440350105503401c034018060001c15400c410804a884500064803280d04644000c00c5c2e44d5101d261a80015410901603580101084181105205101c128601d05901810540d240900b1054040c00a4810b206100e40e51040c4194010410103101484c0c0581d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 433001169 1250 432999919 432999923
    0x306010c06020c060a0f050115030e031b0f0705040c12020a0e120a0309080303010605030c0a020106090f09050f120409270c0503070f1d2e050f041413030903 69
    0xc42d550300fa802803054482038100c80f158025410000500000640d9219042c100c4009010054402d610118210060008011540d140d80b000703009111300404000c0100a54444100092031509805980d1604100c010342c015446186002110100560003120b1480c1410340384030700507a1510901c206907058211040c0140e084858500c01d50050f440008440900a01944420810903620b2a98960368402400340754000303807050000c2441e2110301c00281103010201d00003c81e140d030712071841d0812200d070304003200c019545403803554041c40f0381445441040b44000380a051170340c540742d81441c00c0d0300c1180314000c41c00c2e654202070000c3d920340e140144901e10f5520a02510810141401d808006890140358424014100002600655030421074200d96100300452204900200c81030b8030454018882c03058840300100d00c0011560b00760300d100701c0c0411114030901c0e81c1d0501080c40081d401490076207002d43d1421400f07003201d0a000e41c040350300400859100c0d80000992a04032060606a400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 433002419 1250 433001169 433001171
    0xb0c1506031009050d031a030d030b2404172103071b0803010609240c1a040c150c0201020a0f0302070810020301051504060c15060b1b0d0807090b0306010c06 69
    0x140d40c100031380410000c400d440c103507509101100c40f11480101c8003103040000303685644400c80e9890410b00940140c000084000c2c88042100b1110303094100894480301695200345000405102450030313544105074400201d8002c1c1480c2d128400641840d40946949480c840c40c044002800c4030301c00c0c0c140400032a5451424400041c5600c0c00d0001078000380948400304807461000304410706c0d070703009103524100344040500c01c20380c01c05029100c20000600c1550694040701501d0041460407103004d00503442040305400c00c502e040c004500c2c105505003100c040000001903140543c1c0d00003203444149410403481500811181303002d0b403410005501405140c06002d00000441ca00c1ea4055812500300f906d0507800e03900c83c0311038030300240714600520012402441410002c100f00b18441d10031010b41c280c00282164803078096a40c1504030722030006013000700b407128407001002404001e644100d03a04141c1c0789820010f00151282510380030300c10031040044005000340c1c0c41004042407454000d10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 433003669 1250 433002419 433002431
    0x2090a110a020c0f09090607030507200c12120403110a031b0e160909020a02070807080d020c0603040f0f03030908120717040b0a0e010209030708160b0c15060310 71
    0xd002e500e6007400c1d4040752107131000d41d4204070a03003080f0000034465281c4c1e00141503130f03903600d000c150300810000e4403443c02c00031080648a0740e010020010600000203000030824075681c0740c1080040408102000a40d13040301c0032241010650000780c0d02500e03400a051018000c1d0a00030503010700b0140e0000c0c00076542d01403030b07040c15440c22141d10117603404844c002ca12a0707103030b80d82500701030201403040c03000a00e80b00c0704020142080d40903218010492040c0d4103500c3c1e4950b0b090303181c2501e50700809000d4000115005405404000d4004008000c0c1e4510703085183c01d07101e030151304828103c040c0030a400d2143c920201880780d4003240f041035002144940b80d0904642801e071400301201d050001c84e0311090303401e120046030980e2174411039000484806581d03076154008042d01900203940b41e159000d1080900303035a01030001c0710243c40303110010140482c0c02d0b0004504948594410304900a00f000790301c0d052080420200180d035040802217000740c40e02e0003c00c0c0740c4080207034003c01e058a004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 433004919 1250 433003669 433003687
    0x513090606031a0a0b0102100518070b030a1503022110060807181e0b06070512090405160e010c020d020621150a050d0807140109030f0c0f02090a11 65
    0x6143c80841034018410303003070256105442c4c0d9040f2000d03c0304490150340061035030240130590303030040c9a00260304100c00e10702100706409549000b0f070743e03080541064008820090508a10321030f41d962040f00640040a036859500458140c8a6071801113080148079803541d643e04004004019035201d0410042103480d541c0c91809880f05e030103000c0c048110b194103040c010410054028002c15070390328484100c0d2180c2e909081e0004000340400c0350340001080c0241c4005c2031051080000d540141d40343c2e07e585961100800c0700f1108020440b00c0d4101c244504212603036488503026901880c2821b21010300c4040340000341421200f004000d601000004e40032481a1840c01800c80030304030b0000e40484c41d1100000d51300540c0100d1306181d0400200d040800103071400c038080407040740c0558000c51800c0084e032244014880c41d00d4242c030300d40e911000d24108240e0700150030458a0306e00d141560074403c4a5641402241201e900a442061240c000c108203500651204008070303101c0c82801e03551362582c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 433006169 1250 433004919 433004933
    0x60617070927050106080f15010e121c080405060103080f16060b03062d0c0706090b041b0b0d0e0c0603010909020901050f03030702100e0301051504051f051309060603 73
    0x5140200c0b105040200001c1c032180540511070144281410010382d5640c3c0e007540314058401814400c0c1080500240310300c8546030184043c100da41d140b0040d140f080c05001001501c407041c050800c1c1000070303043c10840418001b0400a064039842254559608908003c24201e401418810440d101150751803008114040c1d204120004040d400d440c0a03136107442900302c580400070700030744400d0000120002d00042e003078002503028004100041c141006500d4900860303000d01c1007162000400c500340300030300052145218420380014012007100381800c0810340107019160340b000c500c039150324441800c0715081c0007149580d000075001d66101d6941da4001d0014220300313a4243c0c09034031041d00100741c90031b004030b0381d80c2c58810140007540b408469500340401002004400c00800680b204c01030450ba0b030a0013a14020105a144544060b0312081000126000a021442d489464600407005c50905502070000c0701c40031109d05040d000541d13600d0300a00043e0310010f22a516000c4007101f00084 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 433007419 1250 433006169 433006229
    0x509010806060907140a1e0801080309010c170304051e010e100b030f100501180216022403010906151b0b191508010606091406180603190b040606170709 67
    0x400c1808035500d00345c1d50095071232203028000c03540103401c204555000d55010302e600641c4240302e00115000441202c18a410355041550f08031580c1d0071580c81d0b44225000d4411900c44040d034800200140d00703014800550b201c110205107660680c03544401c03201568107102c410040d00451007a034004420640b000c20090000740244a80707103582c12540101e0810328420303508942c0c00030031048a143c585401300854880c402100280080031880e07100070624110010390b0080c8144d84010945c0342c02c3c071840000c462075820440c0208a0207004a078074601404041c02d55072500304241202c0c0391600d2a4052441c4102c1407911001383c00e10100c0b03505051a9402c050441e420440200031040d181c010403112506103229032411712841d40c0c1070806034030342080240710107041c0c081e03200003516008000c548240c100f1540c0081c0183e0002071341c2c0d103104141c0110681300204403405c10415081c043d001d0701c604602000070101182c1c090026034601c6c082e00c00d110161801810183c0e144880d5071984600c489 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 433008669 1250 433007419 433007447
    0x2060a05070e0612100302060a0e0a060c150911060703020c1216090f02070f1217060d080c03041e06031a0a090b0103090204060b040f0509010806060907140a 69
    0x46824002800c4030722411104002c080d004100034501009a03a81c903401180242008220000c0803030b0001c0141e0b9a04c4c010b000c110b826840d54440c540d2480300f000790809583e4041c0e414400024180c00004102418444c0f41d2041ea000020314044681440460b0442d88190740350805c100081410a0580008086000b8442103130030104103840b0505103600c8103c5601600e06812000205226145881c5c002400200780020014241195901d03101c04100b8120300c01e840d10b030a030500458016034400e403056407040000b00c0503861820318001281d14110b460b40701070710700c200110f01c0c680c904c0b4003030003141c4c0180b010500d5a681030300001d1500700a40c0c4240f051002103803030038000340e1545070850801c1a81400003440700c82d80700d2805030074401800716007254504142c1c0c0c0398a40d5005036950f2099901030017010558541b100d05103440a2661502900a18802c80000c4010491404001016680007405960500300f0b9102e00c0002c2d209505a401028813001004c00c5400c0d10720f500c001d0702d00d0810 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 433009919 1250 433008669 433008671
    0x302060c0a0206360a17030c10020901020f01060b1801050702040c0323090703020d02130516030e0312010303030b06041a03190903140a020f0703060e0705100e21010c02060a 76
    0x1c0c00e604d00504060381c03520301c00d07041907100804020f02020b81c260111000c40c0314090341d00d400d81d017448030340c00c01c4526a50440419404998161a540d04004036540007200c000208126418100700716100d0003a40d0361245a10150302114896910501c00e6442e001d5002d04244034111024034090050122680030301c0c003001c0d00c0000e103003c031100350f901a8040c0400c00040c200c460b0440d000c2c05421400c0741c030280c0c0c02842410404069030b285104080c0700c0d4082075009403e0a02d40c0c0700060984a4600346141d00d80c3c02842900600340900808604696040c140050704500c6c24003c1089405294046411700c001284014000e1090384015881840f01c8012442603c58514014080310000e5030302070300007039a101090780c0d030b02c0d0b420009140c1a405801180c2880c110340034250710b8a03005803c01c0f50381c41d80f9804181e080d4042040b0100c0501000c5400107441050010010841c075030040c3d0b120312580c82382e01c41090071001c1211031b9a03244d44040080c4440c41850034042d61303844068880003909 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 433011169 1250 433009919 433009987
    0x412030f0608060a150f091107020d050f100207170c0c1003020703140c060a090305130f0807060806010203030c0703030f09110f04020f07030305181f050907050a0302060c0a0206 78
    0x42d094100c04c64050700d46c4924500182c9041c69400c40003440ca00e480c210b90381c401042240d000d0303581c184c02504031a20500007008500900c0c801c29081a500c1360072210014014050300d00002c012482e00c03407005410910050703c0305204940d040c5006040325045801103a840c5411041e1a41a0014075540e402a1100120240e140213071000510458600c1c03c065003180340814511245504280f00c0d05001e847e102e0300382410b104d120340a141007580700b04220740c01002d041006840a00c4400002d14803804c1014031840c1500002c1e441c0d01c801003040c01001f00004024023058005d92000400700c188140c104424a0213142c105202c444400a1030710070441c99a00c0050b926140c0210345540015448041c04c001155030150090310000d4481d2819407a044d440070400d501c00c2100d514204501e40a590281c050041400104c1ea0b002d080b54155070800b103420700c42c540303900420b0001c0301e41c1035628a41d5030140110070350500303941410081d1712000004114100c0140301081e500c481c2c502e10442644 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 433012419 1250 433011169 433011191
    0x6030305120c070f03180b1803010e07050a05101202190e030105010807052b030206041406060f01211b110a0f0215040e13060501060f080412030f0608060a 68
    0x30501a41c0c0f0014000e10703810312450b0009104400440700d91100300c5142001c01c1c0c8500c810070303042e00718120102c4901101102c8020504d003d02401c641d6944250151045500f030501150426184d402040c1c00760800d400400100c2c0d00c1580b21840d180e4032100115101d1801d000ac1ca464074040005c443e0005062000602c0d5901c0c0607c40c0604899018005085036480c0c502030003a40303050400c0441e03201001c1c0049400750f10082c00d1200103507100381d011780940e02d804d14003824481d6500c00f50665680c000402c000941c0ca900004111058090a02440d160104104030a5003800744107202d1400313003000c400f8641000c904610043d50000c94407200101d10440404d2036071600308140242088025456185c00340c1445206000180b8001054902e481d4031002202444030055480c08450201e504c0d0a5040c40b036240b2416014124034500504c450480d11401000f14001400140440590a034040b00d403034041e92140c0e0701030304800000d1001c2595500400e40301ca108841c0006228100405140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 433013669 1250 433012419 433012441
    0xa0201270312200601141c080307110706050306042703020f0601061418190605040306050f010509040b06032d1204060f0f0507150e0705030115090515040603030512 72
    0x1048200000300f80b240c1c40c0990b40c4c1030806d8844407464018948000c18080d11145058695420b070140509550385c0c10010350041008030018240f030001c2d000103c2c00e110147d070050440742c20640880303000c074410200c0000076040440541500c070402c03022458103c00c150700400c0c03000c0e48046010035208160390310081502d100c41000440081d1150802250310a5510120300040c1280701038003c01d00b940b00c2c030003070107980152904a5000f094012900300204041400b070683d01000f208100003982d40b61a01149500d000900003c0081510200048443d00c0c200080f986114080d60b281100d50306207454400d51940303100c0000002d00654680401d00c1c9000c00886040f60030554403a207003c640d92204581d615a051103900801a041200c1e8020880c0d40c032203001e03940c210350300002e202c2e0f5010012618101050380b0440c040d904100450b014403140394030003c12140d00c0c02010406640f0100c4140d910400b5403042075010345404804001d01d07620002900b0080d079441c40b40724072030300d9100c100c003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 433014919 1250 433013669 433013717
    0xf0e06090a0801050a0c02030a140c160b040f2103112109130e0c190e07090501080a110417030705061515030f04080a030f0627020c0a0201270312 64
    0x740100e10104c5110031018030500c010541442d02c42f007581c105408040110044808a5000050036200400c0502107243c0c041c25103001082c1300050004150510b1304180960000248050140207031458a80709004040c8001c1c03d140100c9510300903a2400c0244001443e0003d8401c0b501900203c80f404003203071258403462441500020042000c202000100141913100c0108040c1610304a400003440354810321541e4002e1355240c854014041c2804001410900020b14104103941040304451040c5080c00c02c0310142c9428215a4a0000c18885624518400c0c440000e02601c41e041c10070cc00d61502621040d030005080707855603280310700d0281001250200350340c01d0031080d1f288070100d070009408800a04a50b111400c000c505680c0c0c04103244101c1794070b80e0042e0521942260100c41014050302440020381c2880001c50601168de801701380d56103a20040241406006022110803501c05140c58079000d1035601036405454884c40c14803007001d1341028100c0411031038a006410001ca1010705 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 433016169 1250 433014919 433014937
    0x5090606041511151e0f0105011211030c130f1401050304030c0b0a09110d08070f06090f06020a120e060f041103030a050306100507030f0e06090a0801050a0c0203 71
    0x6a0406081002c20540520141034480520034449004111807405220000c1400303900411000140740c0141c1c2c192004091101e04401d00b092201004190442c3c8081681034a07028a03191201e6140400490000c00800e0656035049c0404410003141441450081617082100200d4507103040e80c40c2c241414182960040700c82ca510030a401d8421035105501860380a802490610008010303901c0700e01c07500038284c802c520b416031654001c609000c03e004245041004c2960b151940c10303500c0d280d07180d00c0d02030754400400d050f20b0719481f070043c485260000c0b4002070b002207080f55216103d161110080d4003425014001c9541e0485003a6100f4503842840c12820b91440603010b0f0342d80d20f41d00d030141c55030014400c40700544134102545454a003000500302c1c3e0181a1102a640d0030140204050481c00c0c0325101c1c01c0000410078a40000d40c451024590845103041c151080013030000041d040e4020a150640c00c0565654001924181500141d0050720300c40401c1080c40790030034089803288100d00003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 433017419 1250 433016169 433016179
    0x204060b1608091f03050405010b100f030207150e0d022107080c07090f06030506011712030c0418020702010e01090e060d06150608040203060a09050c0405090a0f0516050906 76
    0xa4000402c0e5010020a030454004208002070000c2c820f85284401c00300b48550000307a6180104401c101003403150561203601150b94950203e4202d500500c14a10401c91004054000c9001020070607100722980180c9407001050010740101c2c0007482c0c3d80c416400c0c07614018803c1208003240b04032400c103515a00c1c044c0300d1840d131130800d1507200c64446920041840505103e41c100000365a02103100d0400c0f07180c110300c0d022034841d146003005403810390180c000ca041070003940d0013010740e208000b54207903514000c041456240c0d500c0f01174823070740c902665004515403900c6404c6101c050781c0b00d60051203500d200341ca0752480700200000440c0d0074403040c0111031a164090300401c6152500101112481e40300741300200d807481e40002c03495040c0c0e240717611400100c1e044009120031032905000c001d911290800081001c043d0644500d691200114807442c0500d07500c40126031111818040c401e959900168082008422440d0103541c56090110b01e180d540c480d608049000c1c50800d1a0720b001d054020a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 433018669 1250 433017419 433017457
    0xe011401051b01150504200703181805010f0b0a090603050604022a010b1c0b0c07060c09080607020d090b090a0e040c090b0405040210080403140d090204060b 69
    0x40d00c541d840b04589041e140e085040744090b96078240240c10405110f0200711008503d08030503c019a02a501243c10b18403600941c00b0302d46220b0f0b01a12240340c2c042c9030600342c0040c0ba600c2c44d020170b0810b0b0020384100788061124107442d4125008036040b20220727040400440e030707654008003a6000346407400c0006810114208010b9109404c80380d006171006100520341f1007041e59046c00c00030003051a5a410704140c04c02c821402c42032040b4a0108400d5a5101d60142c000c542100c01c0c141c1c0c0030006220038a031501042c4c0c851607100035078000e02e5010301c0404c84031540c002d000d0500e02803813088030100d205031400a100c052010418000d00c442c80d4032081c026505140300040103402c03400140e0307004460b82c071000403001e0301000580e0069005840181400d0b062002110a40341c403103034400d00650415062000507198141208221215441c15051540700c914040300c2804da24004195425404185507032060300691055100c1072088904120b02640c4000314200d5014845501400b101150 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 433019919 1250 433018669 433018709
    0x40905030307110127140106031502030405070902160c05010e0328061112011a03010506031e150913320106060f0e030a050601051201020c070806040c0e01 68
    0xc0c02c0b0344801d0040f0400860801e098441a10807060000203001c40d01880c029010240008414900d14440e280c1009010702410f54407100b090000118810310000d60000004040c440140410800b50840300030540d92000e104845007841449030074140d030325200e0002c6c001450f6020704180d01038000080c0190411101d40da41c44808640041c4d4549044130b4031910b0302c070024004d8880e14091503824084e880d11070304500030181480805810040c2d1080c40c03010091255440c1c05c0680e4115541111010740d03d070b507088180c4100164440c01a540101c00a00340040c54400350400e801c02d96066504500c0c0343c2d10040000c45140742044041c001c41070300d00501480914845648a441c0c191800703c2d5040b0145910b40d03801c45035158030550016a0005124104941c80010020a40c8089004200715845512015140c10040c441c5600c0f40700c098072442080301c400e4041c0e07584201b440065440030707540d0380c002a03101c030403c450445c1d810428660105080035001d80396030590f03203c580d480c403c4025030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 433021169 1250 433019919 433019927
    0xb04051005061e0f03060106030204170d022a1305070f1706010e030a0f03020303060406050d0209010524070807140706090b130806100303030c02071206090611070602120105040905030307 82
    0x560f90344c2c2000c0b010002a010351000c0000900801c10707680e00503a0340c1d1800c200f0031070000e1020b008520b5904440c8040050b070790b0000d410606240c0414031307206005103805881c0c0a1320b51080c0025008482c2141004d903585150340000c1c8100625181c244e003025030382070102c52121101d07040505011140700481c5a551042c48501403841c2c02408480b011030f220380710707482c2c00d6025200840069200004221441c10540503c00061009a07200e5800c1039a0f540001c001030710501600d402a1a80c199100f0607a03c5600d00b9001007210200407a5580514100000d40340d200e8007041d10b0b0f0010a5200980b68540041d0b600c0440c1d41701e40c0d030400c0b894102013500513a90b1000382140e41303500c4412008200715009000c00f9008071003041c80e2800d0a4610714020b82501d203010a0102550807866082000c03540718201d0f840c8070b90340725000088a100c50300e0104010034000c42c03212001e40d40494403a0401c0015030003040c0304c0b0000380c1c00009580c0d0703507020001541d41c0c0034030050103504184041407105000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 433022419 1250 433021169 433021219
    0x1b03110f01061a07050a0f1b0611100c031d07050f09061c050a021206070207061e0e18070c0303050a020f0f07050703020909030a110106050120070e01030b0405100506 73
    0x20800c1030340c4d40c00b1447e856035000a02645401d85450f0b0129041442c4205641a10703c006d29180c00e01036400c204404c025038403001c01001d0140c05540b00c1843e1a40725109610016002c0c4a0a140c00105241d05841c1540c03100240540342c007803118904038075054540600c04074800c22000b8880550340042e0640405001000001210284207801070000180d80e800d052401d900c2081d001000d1502d0b055074020329146c03803035010b2000d1000740700e1440c81c030602207a64003018060a041104800300e013140417880c041803221440c000314003030f0b001303000c0104d5101540b4a00746000342c0c1c0c180b0080e06d5050012040340300f40312640314184010015540210340030b01c05014110300030340650390351035503d4000c1070015200b11045e03500c0d60000501c00ca07040e500000c822403220b1750f1200810411707041c800007800c0d0200c09030850f1b420b01d20000305040c5514003003142c02c0242c400714100d00801e596a252000f504d6001342d90407103045c050311940034103070f141c544150b9208101c000d0013143c00ea0500c01400d040042 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 433023669 1250 433022419 433022423
    0x23010e0601121e06060b0a0e040c020c040e150406020901110d080f22062003060a0b0306030f0706030506120a021e04060e010e1608010e0a0c1b03110f01061a07 70
    0x60200f00c8041040d501c24200204107a440d01640d40d4014080200003028584200303114601d0450360100c0c0d50390000c0d04118081040ea000100100e0500c4098a00350540306850b4110708003004020400030380b034000c0c1c5440c600030303242c1c1d0a82c0350700b40c4480d0b42c40d04181e214860000c0c08600000d2294251000c030316400110041c1d0178042030300c0882c041d00320110244800d44d2102d40b948400d0f18101c003421441d911042e01c0c42e40003404c5050100028002a48030710515402540100101341150703003c0c03020021901612040743c10899031500c014010f01011031305144640c481c081120030450021840d5040613500406289c4046180301c201c00d1140354200890f41c010344e868102086018600e00014040d003100c070190341451501d0302250610030701c0006180c04001c04a00104106502c2c0c403003041e0450720545010440703412108040f2001e050514501081030b860513158818503130025499540304007140144e80426881f102d21038240d8229200302c0300807c44104070210035410400c05096114 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 433024919 1250 433023669 433023713
    0x10b180103090f05010605010906210f0209031506010801050a0b1c020c010c081f030b0a02091c0f03031401060e01030e030705032709070c0308070c23010e060112 71
    0xc40d103a01609805100c0c080351646e5480e0000e04c03a542e0000c00707410003024545000c4011120b290703910080304500c4503031300124035161b050005110400307406031010846e000e4121204c01045803e01900c0300401e640c1c0d980419803800003c6040e08040c2c110809441b15001486d00e051040703003a0340740300f001030812214902e5080c050309030801001c2c0a400700722040e1369100d55081c100095140214030001030b2046141c429104200300140c3c40000c0e980e40440750380001a104c10b0740201040c1104605100100a201c0021060b410002c14103c015071041c0a81d80c100b2041c8400c40003840e240e2420f004120203e003849000c8015588a5006180060b2070350303080e031781403240546d075551030742e000a14101050038150781d800c9108802c3c4269070100720b2085500d0889800c00c22405040034021040c0034080010000005810900070030202106030b0388800d8145c0802e403501140c10b801100e034101000e407542002e462b4416680300160060580340340c40c1003c1d19050362079407282d000740c0458601c14085 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 433026169 1250 433024919 433024931
    0xb01150804020d020a081605011b0201020c09070e0409080c0f0114060f0d0b01120311030702090a0207050a050d0809010e1b1915021506031908031503010218011403010b180103 77
    0x401b42c10300c07000c11082c441c0036144654a05085c00907080b440524010703102040001c24490141c0c0e80040e01e2107181d07074242c48800a0380c0728101c080704c840c00f9040e840c2d074005092050013020080e08100900f40d043d64001610030850203804504d007602c01c181d6032004c0d04a042c0000c80d01030f142c400482030603400c0c000c18812001d09103a0341c0c028210002d134400e01102c080001540c0030b15421241328005000c02c10085d6141140c141d000400d0104c000c0d04000004d41c0c007040c0801002400c001c100300c819006000c41c2c0d00e100e90389030014440041140c4501042d4200102d1820700345c4002400603920300e04c51034a03280c0d554490140088814030010754081d095545100107402034070810384150704081c96000d410000c0651555610060002e004c40b4044d600240d40c1620b8030b2041001020302d55842003d659598071800d411070b030100c00150419515502c0065100742c1980210000900b49000ba211200b40702c0c65282c8250283c0802d00c00d00b460075500f0080044441440310070086d170488141070001d51 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 433027419 1250 433026169 433026179
    0xf050702120714100503010e0604060302060c0604110f0f0f03011506020c032b0f11010204060302040801060509010305061f033203030106053004050303040b01150804020d020a 77
    0x40703401004450140c0110105200510500441005001d826140440056100f07400140140300501c42d06103080d00c403801080043d40c0b5030300b00c8002160001c081c25201c0c0790031026240c480c881034804454114040c4180b0318542450f012484008400403c0000d02e6110710060103c0d580c001d0000c19455580c40b64402c0b1180088180c51014101a6000786005400081030500c0e002c0340c1d07444605007440c041540d04026111010080d030140041c50f14480788500c40e8000d4540d01c11040d0020400c2d4004200400d005074598050022108544002e200712070b40d4030140301c50103c0a01000d07040f9000000044c604c2540703e110101c155080b6010b04401507582c1d1034528201c0d2158081054a00c16141007280da441c0500981d101d84428001642ca1540f500e074000c1c19a2203024a13038011265280d18025210b10410401c90403003600c800001a107240c00d20b8203d40700da004071011544c0c8004040081076030b00340b0740062a581c0c2e035140c5420001c0d481307580802103500a0ac0d042240e00208020700420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 433028669 1250 433027419 433027429
    0xa0302031f0308070506060103060f060513170a03020c0f010e01110c060d09030f0905211204090b0108011418040f12030506120a211e0903030906110d0f050702 70
    0x1c000c50180b50b04645030000ba280079801c140001e4009410141000390600c580f8280a580004a0f241c41c02c120740d460b11039039840c64400c880c42e48071044040940380881e03902880843c1042c0111b10036802c0e585003011103c00c00ca4114110008140010b40041010400e5401000d203900350600e142c04030350141c80701000140403940451400c81c000b94407150740c9010141c101000070070107a82e40c1000c4c0c510604240100d240007581e601c02c000030103a08094444441003d001400f040c804188107203986980340d0080c031024000700c440c810f0000311000d00000f1400c1922601035040000103101c00d130a00342e880e11241007018083c0040e01e4080096480d14002081142003c50940c0651008542403805100700944111244d0300315165400c001840d80001e090076a0110382c010004103242d0b40b86880782ea00700c8401c1c802d103c02034030503001251510900b54021641c002101d01ca0342d02c2c061101d4a40d0f10850ba020b680f9050541e0301d0340180711070344909000c0d031100c0900b1001440c0240c107081785e070340001d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 433029919 1250 433028669 433028731
    0x7030b1902040b09301005220818090f070f0504060f23031f0503030c030d020703091d0103060b060f090f0105250c0602120301090e0304030803041505090c060a030203 73
    0x401c950300c514a10b006d211070314080c2c40c3d400290140b508002400c04410440801541c42c4001e08010740004c491a69024250600256540203440c0304031902c0c0041040b0f00090003901d820f00803a40c581c0c481401644141c00b2501a0303419517841703425100703005609230344107400e5000c02c11080041c40301c0207045900e440d0145200342820380030b003201c110b20040750001c0800359403c41c60017600300700414403800100101b241c515024070350005940d0032581c18110307040615900301c1c1d01c030400b41d822252507d502c0e42010300c3c10b80c0d0140307034200324004500b020002d840c45069800070300c1c00d0051008608034036100143c0d560000040c14410f1070710200752220101003217081d14002910104840740c82c1408030014065000d0482d9000038413120b510100c000b031003804148500640710740c1316403a414402100f030003a10001e581c00b0040030703120b00701482c01220070400b42c180d900741e0a00c0c240000741f241000040121742d503100900ba940c60f100518400701c01a6200400803018002c49113854206405852011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 433031169 1250 433029919 433030009
    0x3e0a0c0f03050f0a1206050a06020307080c1005010e09190b01120c0504020c010213120b0c0a0207090c1d0f010906110c06070602040513050903040501030e0a0507030b1902040b09 78
    0x5038035811700c0624660444085030031090050105140a01c0b08a8001085803003050b009412261281000100b05103810f034950505c6034170501f440000550100f00072200da004541c4032050314103142e0004038900a402c210000a03040302180c2004014a0700d01502034180350f402580391041d8503403104082003d0741e1140001c10341d80c4e0350008914040482c034020740e03c007808940328101300003c919218509080005019203100080005884201c00c2c020800070004110550003440521441c0002808500a0b2005480c0110982d000454a8509003400f4400050140c486e01041d50030302004558610f025180b059107031080d090704009540c2c642014040d00340c4580c0000d03990780c2c140818454401c0750303030b010040300358100814810218008030655095900c03c0c03800240002e801c0c2c2d2002d11b481c00c581e10140446c000c0002c040280182a4003491140e00000508c443c00c2400c0d4280390124401d900c20000c1c0508184800b41c05440c0c11000d1100c44046e10400800101c042401e0500f103150403544 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 433032419 1250 433031169 433031177
    0x102120424020309121308010603030306090614031509010e15070f0503090304302f0a050405040206041703030105030d0f0804060903033e0a0c0f03050f0a 68
    0x5120100c18814500e0120754600180a504604021440c140e4441d002c60051030340500c04517070b0340c040d0f04800d0003101c010050100203020195603810003030001c0c2054010320307201b1030803d48c02050340d03680796505001011004d002004000f560b003000101c051070242c0b800311a0754079155803254940c170030044408415507207805444c407400e0410000c1e108020200c0b40d0000d000d41801000038142000c400d850441d1310310403100c40344100e041c0804130b6027681481120703141b0b01209070301818401c40050904a442c1c0c520081c5075500b4541c1280c44801a91066076035100c0040b01c02030100d41003541149070000d00c05003d5501741a1070f072031028540000e00020400ea45d0005c001004685020000b606214400c2e0800705903151940100a245031001040641001d40f00c0035050700b0188603a1290f070710072004046001c9001003511070841c3c50061080105000c0c42d9000c030700340b843c100344c4007101c83c2da80c0c0903129030b407400304a81e484d10f025115449042e02131200a10200850b02c46500091180e50f0301d59903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 433033669 1250 433032419 433032443
    0x4090603080904060f05030a03110c060301060c0308010b041404091505041407062102130b0f0c0709020c0a030804031101020712080a0c05090d020604051201020703090902090a0608060301021204 85
    0x80c0001c42c2c810780e05c40c01941254010410450b00c02194886207035803d49011031300071181070312080ca02424001c0b01d03a0801c20000000525a40c00b00e5191300720380c0709558109683e60384070101f9406005d00e018030204140002c0354402a440c2c103038071802d5064400c181410002056000b51703400c0390412a4243c0d600308680300b0310304805606000c03c01c0a0049824440090b1051b0b201491a030801c45039100d40e540c1d0300298500d50486898803c070002c1c0341c3c0080a59403800707a880000d07440d4001403c805c103d031240702c00210740c0725818001c3d1a0806088401051000c0d0540c80440e4a0900a84180d040c440004002c400012080c0001c102090141880c1540e05c0c1e07418000505200340100820200c6140c43c1c42818443e40c0f100848026000c1106c0240c1c0185071400012414403c9600290340102c0b60b21408105050640103045002d0080d2500e8404a0ba9240700700d0685c411013101c140d22006002007845450702610400340c10250141c0014201083c4002d06540841c0a440c1600c4008181b4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 433034919 1250 433033669 433033687
    0x18090b0703050f0a180f051c110f0f10090218090303063c03151504050610052505011425020606120111040905100b03060102060a110409060308 63
    0x54003181c4c0250400320100400382005001a5005200c2000108001c0c0e650b5140c60a012080080580091401d0707100c50035440f121501400e2025000180b00c55030141e807007203403281100821508008043c1d00090600d2000c51405c1c0f01c01804850000c9a00142400003e607201e00741060301480b80a840c0e00565990030700c8070400c0200801c1207080c8074402074000c6000c40a010a0320307216a0343c0b40c0800300d24400100580001d041c802030741203040202c8000c40411050400300c1100c074089000685040015803105018048014560501030b004920200001d180107400001d40406803060307921a013100308210b9490074250382000e01400300c90203020041c040c04201e0360803841039070301c50842900005140300c00040d4076070800403d00d1b07214080c65100072605407004e4000070409100c40c01c016607299201e140004c020718040e1100441c48940d08404503007840b4000c1144e00481c41600100103d50318003c2c1c40d030203003680701541621311605000c000760360402c80c01040c01451107442e034280c44265131 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 433036169 1250 433034919 433034941
    0x303010f03050c04021810120c09090501050102030903030f030a020702130f0c03050115050304050a0827042a02160b09011713290411032518090b070305 67
    0xb503400d144143d10410940960711045000f04020100c240c9450038000a424019220804a0b48412a948d8103002e440e100711075011400900391034449004202d2030340c803400120798074054108a1505940f041014400d2184020301035039100310b0b0050003500c1d0613003c0c0c1c00311300d5582c00d031054a140079440e0501c0300d881ca0454091610111100c0c90100000d616007000f1072611022840403030184500000410b041c400f0600c114079040d60400c81c3c2d280e49010302640b90100324201c0b0107a52a060b448080c0050602d018050f181005005503203040280400240001503006010a000150700c117104440b007540e14600c1da040c0080000d14400d40c0c940304440c00240800010400c404844002c0c0000c00c251416200e0401085c20b0f0031007001c816030890815594900c1280b0b0160000c031003c003504100400014803100455810142c0c240c1d1000b52112060b040c03107902200c41031a0029120302d09215407088081d11090704943e000000c00c0010641d1a01042e09109540040000c0c1d100c0e0200941c800c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 433037419 1250 433036169 433036183
    0x12070308100506210a0b0604090b01030f061d070c0308060f0f041b0306140306040809010c211101202109030a020c090112081621120b090112080c0303010f0305 70
    0x521782c0203000610508002507400d20590140c2414280c0d50400a49a6407090340011900c0504507020060540c8540d4405400a025106014030550f10400078120031320810405403203a901d80c495080c1e64449808000032074803044001500140201d100084ca6521809071101030007690340569160301c94005c0060031340d0440d1308000484944002c0f59106514001031256011340c10501c2181c88001100c012140004100000382022f0004100d04081c40f0222080120410711a11981c80401619042a00f038038034151120211880901000710b11003000d01c0100502d8140221a00361b01400c0c044080b00d80303400380d480d85026400407800001c00c03a010011069031407000c032801c001941c0750115148013845842d00040802c8008904408214841d001d03100340c6680c0140f0b50591100c02d600807000005019450f10b000404007059101350200510440c40d00d0720010b450700c5860381c04c1c0310360b98407010762503403040743c004004018070741318040305101440c041d01411290b00075032460740c2000b0f403400e0300c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 433038669 1250 433037419 433037431
    0x11041404061515140a0e060706020a02070f0506070b0a0f090f02031501080712020a1205030a0314010807050415030c080304060315180b040e01150e091207030810050621 74
    0x420400641c155800413551003481880041207550b90300912000c4401c0c1c1072041400c0c0e0401d0700410100c04000b4650003500c002c070071660031a011243d50f1641d22410710714511030f0716017005040020740081010740e0303100359104010305000300709102128054002c440f81d0034808d03552800d200901c841145018440d2280341d40400214001075414115619106c0e84580b0800b6026000209444210f4441446070343c000c00315504244c40d800d07101c0c20b090fa100e51152030303004002440c004208410404401d40d241c140e42c1140c0061040c6820403061000410281c0c1044400d260140070010003c0e41c180d020001a203400c0000d941c81c0c504c0c0c40006001e45005000c6140d541086c3d080520106481d100c034401a40c806032030115444404101140003030507001d101e00e2441d420801c042c194401d614850400b1500780c103103500c0f500c0d500d102031540c84038200c07090481c16520801050300482c4c4190455500b0450110b00d01e01c01503940c4000806a6015203040301603400c0200d40c04003ca1107024070550311503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 433039919 1250 433038669 433038689
    0x405150a08070c03090503100204080d171f0b030c070308130210260a1506050c031803120412020a05040b01020d081005030604060b0405130f110414040615 68
    0x4611000094580c07080141140104030040350110149441018640e00410f03010f006c0d520809050b03510b20001e036000c1c1c003c0d0b100e80d20030000000075451089038003800f86c0d42440071004890315148800e400c41340300c808401c01c1c00105084080352140380341c40210701664544040751b54070542c61a016040074001000341c0d12854130881c0340c0d405078a03015000e11041c45640382941c1200070305c43c00e000103064070011040202c1842d8042099500040c2c0c000c0c55a05a0404021843ca581e20f1040b00c00d8414403407a049690014401b500c04110705030240d00481d0002003d0f9a2696801700380001140c02640c0104d198041e080400f07003d600300038030008003030082038405015015501c40003035911034600280c002003107111400a100100c0d5400d118002c0c01008042d02c1c80c50925042c400d024050804445214620300b00c08610115001c800c101071103607020380c07045a420410b032110801c58403041039003a040740c0c0351280d0113841c1558041c260b108500c2680001010229010804070305091600140111 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 433041169 1250 433039919 433039927
    0x6110f190906080408030a09080c100501030b10060509092a0a120e0c30030d0609051311060f0a03091104020901140d0b090103050304060212030114010c0f080f040515 73
    0x800c920904587d840030350040d010403405903a1038001d409200b4a511179156008a2991481004407608014100c078019843c0400755140c18008035041100b0340301e01c030f004c03a40820a0001c0c42c00c081c07070503a6110940300c08038407082c516000700c82031805104c0e020441611000803907038172042d003008043d800c1d601d42c110100006003441c0451640c03410003041c01c9114141040d440d9000c2a40c80c400000b681500800700c08038540d0003404141c2c1c03500102e415429460034808081020a40e522415101300501843c2c000c410802c0c1e251150050030031280c1e250821000c1114214407000100203000380d403001d0740c0008900d41c4508041452120801115100300d00402021a4580e8411400219410160306003955807018103090402494008417417a0001103820000050020100152040703038056001d0792080100d0105d901310500c0240900310000c2e041c034180d030285521030741241100710721480c01c422070b04005032030b600a103800040340c1810f1000c0004051043c1d0410245003510258609e19103420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 433042419 1250 433041169 433041173
    0x22080f0313091d030a0201060306050609040201080c070501200c010e0615120106050d110a0f060909020a180902190507020603040809030304090203040503070611120406110f1909060804 81
    0x44004510030300c1c0c44107480f001c280c1e0320100891640003d4450b028102c03962541d41c0180a03001c0d120600c426900f081c034000010700303241040000580b05650580d180e0b48603940e81010762085400441082c0e4003596524040c00210103c440b0594500c00a42c451a4075001d00300312003801e440c194000740c00f041d04441d0601044500742c85c0c3c00f4204660881c0d20390035040c00e0790111401884550f10807079201c10000e03039480c1400841c03550007071540000c0d10001e04654842030b0402c448000c40c0319030303000100610000c012042c0c00e41c0c081c00c01c00056142010fa41c401182d440100344000390040040140d00044120307803075108000c0c25204c0419030411a00f800803580001d52103000040c40a02001d0f00003400c090399039401e004441c003a1988940c115240d05003070506540c3c9400c044011561030345041500343c0b0302d020200c207580310031001541c91242551242e603020058040071074410702c801700c244000d650300940c54000d811101c0c00400408540181e8203001002484d0540c4010b0503c046070081c000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 433043669 1250 433042419 433042447
    0x1030f0b0601050c151e0a0f050907150e0609100906020d020106060801151e0302090a0509010302031f0626100c0906030c0905090f180f071a22080f03 66
    0x14940016103100c05ca01d5580c802d141c2400303070640022180f500b40360010440d541c1081d5118942c0007041c031100704095611081420796412103401440c1044150501d41004203104015400f80d09002406d00345c00c007070300d00c000704200e482031162040225000c41c03828031260b03604015141e40250030744000d2010034900b141c084c00040041c05083d10810800110701c160780c2c010389600030b07050074028038018000c13240c3c0d0380140207400055100d4864103041d800050146484009941600e030020090b0090721a0381d1000d0001c500040075410040f91600d200050100001808082c0903040311240401034050f22005030400c10030350305506805240a01c02d10f06a039201d00c514069540701c1c203001440c0740d4113440075203080046900c2a640b00c01400e04000809078a08007250003024110b0220003503040c0300c0704040e128400754003600700d554024101013001c26035010005101900d070701c40241c60020500820f070b40c403140d1b1000716404000348e03410810094070100000c0104414002c080c40c200351402d02e10031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 433044919 1250 433043669 433043683
    0x5070201022a070f121b050f0f0a030507120b2d07020c0303180108090c0f060d18030e0102070b070c14190e011e1d13050601030f0b0601050c 62
    0x18011030b5070034030312200d0500100100d40140880b000c02502c12552142401c400c000742083c1141c0c0b1104030101d003000c0000d07460000307050321030040c803640a2003140d00500040c1c2e40d001c040d5543c081380342d00002010810620402014000d08501413910410f1030400c84040940644800c8410b440f540c00b014080c0181c82000001c101e00050440b05230310f406004918010b40c030381d0160303454000050003003c115044082c403880c140007a02c40d518560740d4904015111902c5035141a00003400512071102403400c80010080c0310740c0171000041400e11070358242c0c80c3d01f523000300c1100440c1101984950781d680400c04100140960b440c2c1910b041d12a5660010350380390341c46103104c846181c0e0101482541d41d407028100d2100184a10340c10390381ea8929400710342600788180c1c5003031b0420300300701440c103a4112141019102903514883d00300340b03484500d1422400080082e0500ca82e202482000500d081c44094000d5002d242a00740009007428074140d5800054885418000200940403a4103030125030b0b2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 433046169 1250 433044919 433044967
    0xd06060617040b0606090d0b0f07030c0e030a060e10022d03040f020f0f030d08040605010909021f0207120b1b0309100c110d120f09051005040602120408070201030507020102 76
    0x20707030f12690741d500424061940900c0c0281340d000080b082000e10f289c40291203200300c089580c01d011040d00c41c0d00036a50b02c2c0107107124540581080110102042041d0000e002c612034070400c580348041d0a40c1104124ac105d81d080340c03040e04070f042d401e4202e45002c080e258440c03104060a01d140d1b007402c0d910800d0804100e003000b40a2141d48410f88416074588154419a44000d015508105040640104005402c540032202246802c002049000705071151980195000d024507040001024146202d01c2c07140340520b04610400c8000f04646041c035200b50f01c1103200c0c00041100d401c2030340001f100700e0742d00c580700004103500307108210039105c00041520011008480000b010802d80d00200c40b02ca0305050300d0404c0b88a03041720400340ca036100208820081c0f081008114500801d03070381c0d8068401c8607001911035408a007028a8a6419620241d00140f1031800189450281c000102d00e404c42240d080e140c5c5140400d400c0290358050107070136071210030b92008511b040452051a140382c0c84416035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 433047419 1250 433046169 433046179
    0x90d381608070516050307020d030507231f060b0f0d060602010227010e042f09010c030807030e01110301060314060604090c020a0b1f060206070206010b0702030a020d06060617040b06 80
    0x51381080c80350038422218020340140001805000da820090311650100500302c90b0500f50000481d180709810255000324034000340a00310b00c1e1080b110350b2262076600111000b040e0340e20080017414845000061001084c10400e254a032000c0208580484030319500142c2964010002e00c458050104104d141d40900030080c16a40041c080040720480003051405403c01e242064503951440a4074140190342c14107564904031010362200780c0c0d8140030f00c00304113021400c2c0074541c0001900404001e68003c0484c50300080d00407540000741e00351230300104181e810042c0000103025260740342c0200b040081c1e00b806131000034100800402d660b071003148120004942d4440c0c1e001d6400b482801000c500b0394001c0001d4805080000c841d880280d2180f036200c92240c82284002403050000c0b40491040600e0f4004e00340681ca826407013411a4000e09017260f00d40207040d030503001a501d070800034074402e029150001b42603003005400f42101d011008004070b52810b102c100800103d4440c242a405001661 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 433048669 1250 433047419 433047457
    0x21207060b04051f0918020108091606080f01051207060e0307030f0c052704020d11030d0315080111160c0807080607030b06090d3816080705 62
    0x20150020110078107080d9110b410b140510018006024107070200704203100e83e50105582d50900d1004031126402c41c0903030307892400113004c090340c0203428280d071000e40322069075114140c0c1822039242403d0f682164011a60100c24440d1215102d02c07520301600b400e45084401c000b5080800341d441a81e0310451007040300010a031052a10144440300065078040c002c003a403881e861400c0e892036000e5000b0140180501544c1182c0007002806171152040b1400c030030622500c46400f480000c007040e440585039521080e0b25111581c9080020b07003103c00b00c2d81d400240300d209a850070894080281c0c45054180e042c8500c1640d0b070022141100c8210301d02042c1e1200d2480c203840c0007041102c640d8841e100d60701440700d00282c25080400d82c280308003113070741d41040f400c0c07098400c101003402200d042c950006040380001001039011042c404514400710f803603002d500741c030780c4010b0009418606100070400464007032080300102904103070628082414104070034641008000c01074082ca280040003008510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 433049919 1250 433048669 433048673
    0x19030f0f051e0c0f071d040c090203060103060b12060102060906100b1b07120519120f0215010602010b13140c0d02070503040902071407180b03100510051002070501021207 75
    0x1004854083c0c02150a0714402c00482140345e84a500501c2070200115074941d01081c280c504005480c4142d620400b8030813402d0800b0581d900035000207090505040d070b1a80c01140d1002000d01070b1180c025a00c0110b00300d890208002810a036020300100c4c03150344031a00740306000243e49581c105541c0455841521001d10f40c0211400078507441d490890b500610501180000c001c081032920300b4003950444914141c01c0507100c1500703038101d00190814400d4030011040c24402d1407082a9408180704a030f0f0b9110701180048680207080e030160b40983c0d540d510601c1c0c1c900b01900d2012220307031034050401003c0400306500000c44030080461542640004035407041c0718440d41980d85207500401141d0311503445424150083d805964140d40f503243c1d2040c3c1051054001692609448040b138895407400000c4d02441c015050408490380d150003001d040d00600c100c1031103050700c5020711100b064896440c1c2014444c140034542c45003000c54110001c140480d9800288800d00760140c088900e0f5078992034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 433051169 1250 433049919 433049977
    0x31b02010903020603040f050f030301030206040905071701080601050f0108061f0c0f083c090112020c011b080919020103061e1a070203060105040207021219030f0f05 73
    0x35000290f04c0742001c03041c03009001011100c14143c2d80b140f4100d8091512490500350740340070911000b58030900810081c0581c45540d041b2030340101c91810711400342d0b090811084001e0109810018895220710010041803610030f402400303041085c24440c03014200304012400b00c42c05010003844482461164503c5640300d00c9050113400c1c0c000c200058544042c0c582142c0030390140303100420558401040c511341e030101000e45e01560166901109011400e0341c1d071845d036038002e079008505000500b0100b00e01d42c0b1080c00100403508000d0b0001640d03601043e107a1200c072840400e0380c802c010038075080010411001601007444600400403458190040c80128050b00c1e45400c02c40110b083c4402060000c0c800010365000d40b40c14816281d80c5158448410445000301000a90303d0b61124004014505090340100300040c0060300c44214002c046490f680341060120070401c03844d281c264000c0c01d1660040c000c1c50301c0350492410070003040c6900c10040950148042d48440380c883d46003025003c0c0c0d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 433052419 1250 433051169 433051187
    0xb010b0906190804120f051803030d020d0b100315301a06030f1203040503160318120b0403030515041e05100510050a090f1202040e010603031b0201 65
    0x300c01c12802441c0d00c2c0c454024407014003940c0440319040c00b85421004a4042d070907020600c009586c4040c140014503405031928014000c5076501400b0070000035820405600060000c6042d944012480914130403d0040340d520b003c0c500d07000c2619081700020070860b4107040c40c0803501d00b2007a00041c28030340f55000b1070090143e00c0602060004034817210410800c1d05c0000003504e20108820345a95505043c90f4580036522102c60b004c1d0404400e019003000100b01454001d40982c04403800c0005240c8a4000e07211150003d0700811400000c6403410b034000c0000702e000c0d20b402c0100d00301c0311141c1e5451194140d80038100605142d1540005600300c0600b0348011000d020003042400110020006c03050b80d00c03100e00341c0003815414400001d003e44660354031441110380244c101300b00403540441c00c44213900720030042c0040208005000807403400054050000e803644c0980b42680c41024410001100c00c0003c0e0001c0c96410000d040001c030b5006081500441003001c501e020441a500c0126110b208c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 433053669 1250 433052419 433052437
    0xd0e1c030c0804090204090e010e010c021c0905030706180902090307090c0302160606050f06031311011202030705032205070302012102040806060a12080a0507030915030903030b0d0b010b0906 84
    0x110200e0002418826900004041c00c07580008000000a91681c2b0342640e1604040d140540d20950381c038280311000c00c1000248072454035020743c02c940c840d00080d042c0a122b0b4070080015086a000008840c0300c50f010000400740c2c40c004514090104000c251030304924860841b80c07640d81e0042c600d82d43e00a40484070f034400342029100000c1d82c10310309503000f0b00e254001c8901580720a01248090308043d02103901a40d10f40400308840c00e080d9555600320004182403e04000ba5082c010185942c030b0b0014600034080d0b611082c2e142d00d81140188100800d01500300c6c00900040c0c695000700d240070410b1020380350203190401410b0b01d480403021565903c44404400d2903c0050000340f4901c0110b0710a000344401c89010400eaa42d0754000500740242c000042d01c0080100114026940100c004100240c4030b401d00d40d0031f2554581308809081d020002140110752560400c900f01540751080481355801210401440c403055190800744400501415000d0500000c4103081d6980e560140c030f00707480c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 433054919 1250 433053669 433053671
    0x7170a0903060f141302030a020418020d0f1a010303051b011b0806040f0509250302040515090106031509020d0e012a0302030f060f1f020d0e1c030c080409 68
    0x1001c3d603084801803220000088014036028041000c8030302c1c02055001094008006003180c202c10740800c0001c0ca0750865030f42e415041d40f8212070068664803203030344150703004040300c031002c01d5903081c08bc0c034400075034002c6020900740d1001400066004825900340e150f150000c10000e00790881058014441160052003044603228030307800c125400702d03000e07100300820386044c0502c440ca400c100099910540d200d0302241c00c24800014150017a4610f080420707030f8062240728441d03a80c0c0100d02226402c4d40c1822031440030428192207400d10540407030050416180412000680c0f0003c0c0a0b110300314001d0b0340740c00c0d4002840440a4003d0b40101502d900e5890007006507500c02c1441c09076110010310150482c22030340c0c00c1c0510b40340c000d100b6a4458610a1480100c6a543d001049880c0b8000315000e944201c5910140910301e0300d841500445e40c0581e00140010401040007420003843c142d2020300c500b0b5055806010350014002442d10b86906013050040c0f40101d1400c680c1c1c41c00b458111040c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 433056169 1250 433054919 433054931
    0xf090a0204060906090b0a0b0301120305131815060806060708131e060302041811071428050a06090320030409050a20031e04060e060c07170a090306 65
    0x62016580881d084605d40402000113403220360034483c140702c1900c0348992031501440104441206c4601c595040303480382c034095185c5840e00030b00030400301903508001c640c054003d8000e0f00440300f9100d40d440040300c44050341803207482c0c01c5009180301c00040c895405800f020810804001080c01981d85440c0f105600d0045681ca408c624041e200f0300c51411600c03400341032400200039010348200c0d8140e448058419002c840c907214110050110003035152680f080800070800420011001101c40740c0041001e0701281c0702c801601482c0780449074000c44241c080400700c2c000290009030402c9011340c0140041404691030600784d44410b501e000e00040503020031201b51844601100501c280c41d1030900410003600c590441d07200711400c5403201d03070360485500280e0070000009401f455120110400f4064084d9421145165441007aa4100c0f190358581c2c40d1650420b005104040d404400781918038104200d5450300203454046007602001c104c0001100180e8600c64a501c601868000c8014008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 433057419 1250 433056169 433056179
    0x1b0f03040609020a051e01050a2c0406050301140f060402071407030c0902030f06040b03030d0204030b011a0901021203040201021e06100501020601061403060607020d0b0103050606030d05030f090a020406 89
    0x242c421150220710407006a40c0200301403a01c0b8502070301c8941181c0d040f4031000c50800041d078095008520005c2480411071001840709140313840c401c00c6c1078249503403034014001d840c10b1006a9075640c000324800c0c0d042c502070050f107180040340700b58040c40c0c00e00301d05119101e031000b04000344180040030304000c0704c45201442038800007448104a81c410b004220b206036503030000c4012400195401490507241c000450724a14042c0c21003030001500409403441c242c1090005001c0b82d0080c0d00440e0304043c6c2800402111440c8135403c4640000c1d1070601d882d04102c940003d4848240650f0b022400c400440801c0c150391003006240482002031254400c040301644050350398803000c582007461b4040d01c40d0089060352012039aa812682c940e110715200c1e8821502c4035910350001829282c101105008079005a034aa5080e0001140504046c401c80e50540c1001401d01c0300040c4040d001e54840c4803030040071039001302101c0c0c1c0b020075401c0c00400d0340c503662021070900d40e05410103541700c0d0800b400807074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 433058669 1250 433057419 433057421
    0x23120301060f0f0917070906080c01180605041809080f0702100c020306190e03070f0506150f040905101121010e0423120a120e061b0f030406 62
    0x2068512540300c002c454482e95070115040442803102200042c4500c00c10004003150b40c14a03003049840e14190f4130441d1711303100203408881850f03000c030803d42d10240d005401c95800c80c540c1a503400d0b00744a0310320a1070915001500e00e10840c13040041e1191703400006070040d600342c1d0001ca903d56215800c282e0780d0440301e00e40a05600444010f91003040d001c2d0b250350312140146051090306d030340940a03000c03681e40c5132645d0120300d081d5120003071040d0b290342c410004010240020807810f0311898506400380c6050510300c0c9404001440286082208900c1c55145e0b074400c9400390381c00c002140c0110b85080a4074206003029901103401ca2901d003090312041080315108058540d000c00554241e161815054103000e000382c5c03e20441619540324070108011603c0840c248030342c0c0a104018601015001d90103520b040050321141440f03600226140d002cbc1944a0701031848414004814803160100c0502c039070700d03a500a0070400c441c201040d114001e407121034064520014002c1c0340903480b4601070500c84 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 433059919 1250 433058669 433058671
    0xa050604030e0a08010b0f10051b0f0609150a150510030506120c0105033d140604060e0f030127050c04050705220509070e031006060c231203 62
    0x5110340f68111000c1000c1c00d0510400c00e00150003402a0560304905040c4500c06148610143c100300040003440295018000c0041e104031002d4000c21000c80c441c0c203800d08121015207c001d503a0441606200301009031803080ba040110110005050001440100c4820341c0e02c0c0e200c1c40d00040981c020350029a056800644104030076510549070074004622980c031440d48940c401d0200e182400800d00d0715404212081c000b50b1602c070b00c081a03070b40001c2c8100b446100188452080b034510401400400c501d0b0a40c4101240261066418642045006001c3c4005170390b02601440301841000201d940035041070615400d20085051003000042c1d5861140300c81d804160741d40d1103030b05001442800c19100346481400b4a55070b41f81484000341c004613801039100d000c248048040f4901044e40d503944c0c2c13030090150700143c42e100a04d40e580800d05050ad1aa01840e03001140307041010807581da0032680030034005510002000c0300c1030407000c0c1001d64804c10740226101e445580c040c10340940c0204029 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 433061169 1250 433059919 433059947
    0x12090f06070314090a091b1413090504080906280806090115030f020319150b031b04030213091208040b070e2206030203070e06030a0807060b10091e1401110a05060403 73
    0x1300c0c548d1a14441003441344540008185031041c5e0714800c004411a641c409500148291021807400c0804e02c00100d03247c1150084070210465004201c1c07038103440340d8181c0c070700e0003060a0068080c80e000000804901c01440ad150b001c0c801d1628000c01e2521a600041c00741c1542c00e8115124144000300318900c6190504100328545000c03401c1010101410420701200d10b0022078a1450340c43d0890989288402a941042543c06020100041e1340314074107d0704800d1a6500006ca8403e5400c140c00390041c80b00111082c8160300d008e02012801c0c286044d0340c00034039420b240b146070900d0004111015445036211180c0500d16515981d510032980201c001c480c000c400b201c0f041511400003803030f480c1c0b040c0c40e01941070707224a003401c0010f48100050311440340500400101b003900c10380850311192881c1400000a0350880042c8186510215030700c01d07041400a10165044c2000107a80a6900e101865414090a600b0111140e141002504421079200c030076182d407401c10b490081c1080c8000104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 433062419 1250 433061169 433061177
    0x70f05031b030601050105071e060f18020904080c120f0309010e0313030f060f020c01051b0c15090a021005191416110312090f06070314090a091b 64
    0x1210241040010740d010407400081c05003807280d180074010f48623a4003004040b00c091b4078007448040060103e04043c034009006610104065000b0f279440403c88441c5c00c00d48102202c86003400d800740e00c0e25064103500c0b6a01100d81c1d5551406000f41c1443c144440c0f540310000c100009882d1300e80e003221405140200310084c020b1080c50400725499461707000c1e41ca180d441100c9101d000b00301060b607503079820b00300d07a000d0200040c581c0c1c40c1121703d0090703a0200802c1d00407691250240402c1c0984c800b52031241c00b10300440c003810144003582c00e54450442c16a9000302d481c2e440c0100704084170612020a200b54001c002d000044000c4a0150141c0c002000380050301c0d988404c0041e005000310005a602e030b00c8001040d140c205196000b4044210000e425240f4000c040d00d80304403074030200103400c902c2803140d09850f151032041c0200308a6a008040707642c0030784000e1043d1000280c205200c0450300c01c02c8100c9645412a903004640c1c4d1500c540d00922505090403842c0342c41c600244a8007581001d1955 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 433063669 1250 433062419 433062433
    0x70605090f0d0c051b180a0b0a0602030901090e0c22090c080406051f060f0905130905060619030b0916170d020703050d140c060c030117060c0307050703050c070f0503 73
    0x1111451100d203640950041b103004114154000e2a2400503880358503900c0c000791800010010a200b11315035003004002da440020750034041e68000540400a0078442030b090303d00d1400550158007070041400d510f0300034014050192003060340e10707002d1025000300c0f1410400c4d00c6040e000241341c103034240c4066070064500408602410318030fa2040a05042e951052074a481c5880d404540c04265200240100302941e0703000701e01c90343c50900302200c0140c140e8011607020142c0c02c046007031400217019107114040c80e0b0481e40c800904c00149104480d000000500c003070386d0740051141000c2040139402e02c0100307a80004504116610000d440041510084070710280907040141c2c1d84600c0c602000c1c000703602403003900003441d205140c900c2040c41e82014903410080c1d442449481d00b01d09032101071120740c000c8010300108403003422280c19800c6407401403160f8146125041c12602c00600150108400021440e0038540104101ca084065200442c2c1e24035541b00755030310502c82e4a007d07160cc00d0041c29 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 433064919 1250 433063669 433063693
    0x708030612150402060d1410090b01051c0509210d060603140a0e03040905090309091609090f0e030a02070501030b06280c05030f0403020a150203070605090f0d0c05 72
    0x1682c10070b2142000500701151180c1e0204a484d40000c007248608a80364006440c944180314010f5024001c0c2c41c0480001a040842000694850030440e0741000420302c90400e80046000344e146001e52041d200080300d0326401405420003860350711156800c4a0740003070b811040c1401008007089028118100b08040d01c1c1c039000c4042d0f034100314549076641603410104005506c5603101c410002d400e401182d10300f0355102002c209492080f12207090a400103d1340c44514106042102c0d03202e4000303241c81c1503954810301c015000040034000c02015580c0c9403540045521254480281254200d080340e440d4505600000d5540966014250000341030694405045c246101519070306018030301c420280c803586c00c110420003410100c80b4400c200c4140d10f2100441c10a000800074101d07000c00305039882d41540140001c04495038000488801400504070a1725404000c0e50401ca03030010010620351900031100b0301d0000301080c41080c2d4003503010442c8104e030300280100c003800c3c402c10548508034210 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 433066169 1250 433064919 433064923
    0x3021b0a03020612060105162d02090c090114040e160503010f441207080301140109090c02030414120705060705101b0314160c080705030708030612 65
    0x40c40001e4001c04203100c03401d41c0e2501820b003260b10085c1803425900f0011444120485848810800d5408600400050a0b480510100c290280424801c3c510080407503034040b910a42008203c0c41880b4000700386290141c0c8146207440b009505084400d0316180c56060b00420b80b0010b680008a0014914081003018010002d90b4103c9280e1012800b5161424801b441c50b4100d20103000c01d200b4241e501d60300d102c0d417401901c00d00c014a540400c03800960362a0982c2ca4600c3c000c2e680980c884d001e10285001a4690b000c990641c0e00e00a214400303c3e44210050350307103a80c02d410084140341000030002005030f00001900481d1581c5000e151310141850500c64110601003a5031055040200180325908040e401440014490011104010762415480003110700b51144c076007840c42c2c00c1c0c2179111030b03c1d0f0501803801814140320807620142002941070306d08200301005e0740c06011708490340350184120f06c4256a070840c0c0044c1030303990b9843c1516018050358411103030715100d0b041c0c0c488402d12034000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 433067419 1250 433066169 433066189
    0x90c030b03010605150f0d11040e010b03043305012d0b0d050606070819030f0e07270501080109140d0c030e1f030902030c0103111911060403021b 64
    0x40a04010010400c1071005c0c00181d0094400e040610b600f0004502403040c140309540701c0c24070040810742c445081a00400001c1c0c1d06900500030500d091050101161443c020841d0030002a9040d485403425440401c1c40030303800d500b104034190b1038213000003421030411600f41c89070504140c1c00c0407800c0d10f02c00100c14003000c0380070b03902c0c602105000d4012210bd07690f00407600841d0003400b503410002da596030b0f805c10358800e400800c545c50040440b040801e0701401107460307900600506002264140d00320079038448440c42003980c40042520104c009051248450070f803c60070003800c3c08650b0f100c80406004e050241402c0760810004c09240b07001c0100400d0003112855240e603052440245510100c1c5c3d42401c1d8080c65a000c2581102c440314404001a1511806580e407070100e903605240c010581404200808c05041c507003041000c2640c00211002c484810101a2444000900380e020441d20000c042c800141c0034802e4074184810b06d60005526141c042441424079a1880d80005010384844 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 433068669 1250 433067419 433067429
    0x90a060f091203092103031b1d01030e1b0f0103090b041214040617070503071209060b06070615050603100317070c0f09050108031201060302070f05100e0f0f0a12020c0307090c030b030106 82
    0x65080856555062001c0716409c0f8805250208075a40d03031103486402c01081a01654141ca0380244414003030030183d000c801c1c400400d0908028111151325008111200140028013a804101100e00300031b00854030a401203001e50780f12ba4071181c071072038041c00107140480401d41c0481d40c40c0004a03024800c0c1c0850b88144400d58500c002c5807408034244c07001e002520421100103403259181c041d03507100c0d8006410070300c0c05010049aa0501c0e406070100d2001e960300b105003d40c104000b0803003043d00d107030321001c1213030782c42402e049403035190100c440c00d28090140020600490f00c0c90004a948a80c1014401c6d035400410400c04d0340d07a120f00c89a502c1c070030f60b50040310000d003c0e80108051030080c0c0c06805950b019540500f1030f88030300c0d600e01e420b182080803031101c015501c10420328030101c01c01003172000d0b0200d00001d00f000c61130444241d5451100d801d0080c48840f0b05010300c02c900c2e10038000c501440302d02038100d800c0191a80c614101510f40c0b69aa540000c4c6400c01403e514a014061241110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 433069919 1250 433068669 433068677
    0x6120b010c35250b06060a050712230c0d080606071209170109050601142d0906030a032c030a0602090a060f091203092103031b 56
    0x141c0582e81c2d80c290400c02c0910300c0b2580780b030405840803407240042c502002d00840954a5664200c40e070710b400240401d1814040c21192994060001501000115401c103004842154513032140e240d089800740710342030000f851081c18551603544a90003c4008007800a600304202c440c69a036036501055024040c1012000e51201400143c01c0e4002c030032071030300504064840fa10b84030460301c45003140e003001c800361030000e40c0303003a000c000110801c162024280000d03002803000b140140c44003a42ea08042c09070580b81481562800709a60760310f4418a00c8101c4205410f060811080302808e4440000318170358014500b1030001515803401141d0441c41c2075040c3c0301c000421104000e884805e0078814209901100c2d551152581980d0400400c2000792003841c01681da00c0b505400d00c030310b000155215000380468600c8180000b6005000307a8240d505100382d12184d090903041c119000a0300c2c2e03204882440d16a10100e03820700d5400c15800b01e182c0203403401d00086d42400d0300000842d001891010001d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 433071169 1250 433069919 433069937
    0x50a020f01030f050414070906081209031603030801051c02030d080406180c09061a03150a1203031505061c020723060108011401060e010809010f020408030406120b01 73
    0x52800105644080406140000716101d180355083c0841e44151415258078070f500c0010003550748108110700240030091340c14400c00707250a146950760800c0202d8000c424001080c907136131720380301003095015500c0b04c0300810a0b0981e807402e02900039502801110b010340d02c45401c01e0820b1001c4669101e4456000d07005000307961400508844645010784200e5440e81c9030034550303159110040113041194006d901410242d840c5c6145001250100d9105081d422004141c06110941c5c4005403544018442e082e041c0c1c403040c0c1c42c001803c441040e00f10364404400c0c128104241a40f40c2c1c02a05200012520021507a48031400c00516008070301c171000c410001082c1e8100300103000d401030141d03140b0540c690f09011160a110360f411145003680148c144c0d20805c01041003c00c240210054a940358460804950501c00004c0080c0188004103041c4900300b030115254143c00d60250a0042c03d00804645076600c42c600d80e901c03540140b01d40c60000d1a46640d4408035074180c0318290766040161602d542c2e03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 433072419 1250 433071169 433071173
    0x19060b0a180b25060509070806060d0b04023c10030b0604060e030c0909010504030807080403020c010804140a03030605281a041a0a110c01020a06110f070f1a04050a 72
    0x340903030f501c0d40c9620001104078100c0024045001c2c0f9401a103060002d800c2540c24105c001b441c241006010a105100c90042e140c0418180c2c444c2c0c942254040c1e40c2c910b865890240d040e001e4a0503403400c00c90f14888021981d0b1860340c031039510503101c00100c3d41e0481503500745030100d0980300da984a40b60702030341c03c0104205090240f8040004404003a060f1500000d403000054982d10040301c03039590a0351110b041004240d80280d003168029154200011141030546000b55506c40600f00345050200c10380c041000c0c0000300003d50340e4101d0721400c1b24a8503005160050250900744920340c010300c85400184402c0e0540311186801107247c04450280c0e03440c2244d052980344043e00020300b40601000042422540d1640501c03800e450105816560f40c00e003c80100b9170001c003000c10308190800ca080c80c1c1182e81c00310ba84d0030401d8102002041004c0038080c654090302c55141e881d040f561001031920100b007082010341e403000b40159000d018858a403050f295520004540040003038100d5451703000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 433073669 1250 433072419 433072447
    0x6070302060727030b06040605030a0c03170c011815060b0708070602041d1006030207050d0f091205010e011103010614030703060302040203270102130e19060b0a180b 73
    0xa401c040c43c0c0c0c0c1c542e610320283c1030b10003501c800316003060394002c641404102031030401703020300b600410b0194020911440c16480f60407090710b1a00006016103813199003105041e40032020b4401c081e441e40300800000031614100b460f0785035114021a505982e4584058541030a449104204e6103c0703a4040e02c0d044071a610b24140d80d000c00811a40139909010214145c1d00d2910302150188012948245a09200f02040550b0300fa9503c142e0805004000800c009400800d1a40c4000014107190081d51400b200990386110260000308880c240340a800f0140701e015007042080083e000000c1210341011405240b003444240114000b24840813400941c518050004607400301d014540090b60769105c0e400101030344c0c0705482081040c180702000c0d80304280703200030032100300e03c1a200031840c0c0b5100121140303203515248140c5400c0d15500300042c0f441400301c00f05030907880c20100c080040a0b2a0383e18650941c10503480800060800302c0c143c8419603c040d809401d1743c20f15800075042901c0440694 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 433074919 1250 433073669 433073687
    0xa020427110c07090f1e0b0d170d0501051207060c060f1802011722060b09090708120703090e090a12051c110d090f0c060f0e060703020607 61
    0x8561159122161403404a980002e040d440a000000d00300492801e003184003950001c280d42c9103010720304418110b8454854100350b0382804110008156002410700082e400c222104014050300c101190042c00c0c0140c4034003c0c91000800b02c0c00300116603c0f8000c0c01440da00303518110005a001d140f0030300c4a2030086410f01d0380b480c4200340115504c0580d448850985501d43c0c60350b070300251050f201d0320031507800003003002d1480780b0404034021a244c0003040f070f4460409004018041c00e400c1c1000c5080c0400764000040034440034120f2180c90804c0d1080c82e42c2c3c0c1c03444e032240d010140116018169a103211a00b11440150503a4400c0788407403e14016003000080601140f81c1c0f40f0070400e45100207040c0b210400381c075040030f844184d02c0d151000324602003020000c01a12000b45400c1e5210314401c000819034040f0302100800040c5580c40f4030781400c17060107403040070308449542000003030000d40c041481171540015030384050306683c000c0c003400007500850710f005001d41c02403c000740314035208600c0d41e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 433076169 1250 433074919 433074989
    0x1101121406190807080a030914090a1805151806130b0a0b0d0b010f060201020c030f0703090b0c1006051503151c03180807031e0c090e0c090a0204 64
    0x1000e0143c2d81d6180b903502e020f00303030b901c5510180c003c40102014142c101103042c3c0184042c141d000b40e003110b03140018a403500010b040c1e400d40c40d0b403199000c000b80005a01401500c0d440000c0307540e1111186290310741140200ea0520220710b100100c040861004a41e075402080b0000b2590900030752235a541c0c5001138004c01402600d030f81c50b951007409986903009816424003440c5a01c0349035043c00c103034500b00d8515400ca18203580c010000c0c8030503000c00104640c2241404c0c45d42c00c1c1c40344803a18013151080c1841c0d111902c80480400c00008010010074100d50396881d044080042c03d07034030f800b03002c0c01030811240c1c260068001e00c00540c0900205070350001280005040d0449100b003c2d1015180c8900e01000347d000071180c0400040c402501020b01d0054089440102551440c40e030310507425440540141c0c204c0000100c8000030030007098640300143c82500801c0c004540f500c038225540c1c06c0c119a07114422418140401d0b2185000e20854050300c03001c120070061000c0e0030103010958001d0f0f84507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 433077419 1250 433076169 433076209
    0x50103020a05041419060512060a08030403061e05040507140409030909050711030a200c10050d0f020d0b030d18050126070e2715010309050106031101121406 69
    0x220040c420b17100c003c01c0c0f02a16950307d0322501c0320400302c205070f90a64010b00a9000d03031a5407005118a020000944d000c50b64804404110311b1002c829241c140761030016501031140c00d250910040100c0465001c05a900740c8986562090762042044184c07085d9110103400f19015940c140001e0381642c1000b54001003504200f50046412040145160721407580940000c00380081d6000220308020010140340c5844d004104000c0c403d00000c0c80d410038240c0351414800c00042c5050658400c1e041101c404807485811525400340e0b560007406001400c1409101c1e00500c280b4044c010700890034018100d5a1495040c0800d0408006480003504950007403a8100f4010000b4000a07081035818030407821b6646020442c0200000d11502c0c1c00c000c503100c0c0a0001502c01d05809032126080030341d2018040075540e045107500d10041c5c0083c403421a01514550070818040103102ca18407400d1848082a40d802d2840079000000d842114402c83c1c2001c1903000703c00120798540381500c1048000821510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 433078669 1250 433077419 433077439
    0x50f0f090a02041d0603030a0315180501060905060a0e010305090a1707030824010c03110303100807080a03020c091f150806041a0904170d0b0406050103020a050414 72
    0x4104800450792401440c0d00040c003408081c583c004000c94a01001c10300d0b602c1403c0c1480065260700038014a00109960b4841d10061210740007030040051941d146130001250414070f07620301800782400340300f0202c0e444440001ea18100101220720507900e0b81c0e10740d5240501100110054140a040082e5622460b040e45001c00e1201c102040a44003c80401d6035840791494090100f110041040b80d1022910003944c40308102c0300c60032010840309181c0314486142070328056074001400c17400051580300c00f00c200012541d1120303881081e40c010408884d81195508a21640c6410102c402401600000c043d1010307070030000c1c80030303400028a8005403044c0120303420680754441541d00c6406280c05a04008000d550021040c0341c01101c280c80c1407200c0b106584515282d0540b040020340100030583c0090280180840b81401c282002d105990740e0340b0b9145030a402420150643c184942e10302a0001050b41c00b0b4402c80f001075101d5101d00d400e082c5041040d0a41740301c0d840d00c95030040c21045c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 433079919 1250 433078669 433078699
    0x807110d050904060501020109080d11161b17030a051b0d020601090522202701090c0905060d020403061104031a010b04180f090b0702060709050a050f 66
    0x220805420811995079291225050400c00090b0395180e8041419645490b0100300440c4801c1e00715091416600000304140111800c1c0140c41e01c903c0b10b40f08441c1ea41000d940e4204a22090240c1414441c2c850b441c00f482e0301d8020b03400c0c00310351200751480345034010805010a140a0400f03408424100500e030811103859011513030404030507c9600c070040c1c201e00010312641c09c00d445040c1d0002c0c20050f403281c1c00c0b801e407144017142d0315003010081d00b420301c0c1000104010725503101c80101c0480180803c04c0c0c080301c174070300d03030a4a42100314400d100c20013100c00403c04029611407059411241d9031a80c1402c1d1421083c0011603100540315220355400304000300102d1418082e0300301e0745a640b036056580d603146081000e440235402820b07480c0c91501000420541c401c5505980660b1020905d44604842044042000b48615200c0d4a02c49080070344260902c00704902981c8140c0e40d507000d84c0c91607034400404884610260088541c0a8041c2c03009200c682400c68035203034500f0f03000e803150108900784 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 433081169 1250 433079919 433079923
    0x7030905010608070b03010e2409060613030b160203070209310b070f020f06060405181212061804030509040e0102130317041217040b0f0c16060c03080711 68
    0x207074220718910744001004002440a541c22950b204555060004042707042088104000b4001a8060722070140000400c1c80c60761400c0440e1009403c0040d111201035607407400d50800718007140d43c1001a1200c1450b04903881c0040300300e66800c0d5005000500300d075146003103240b01000100c900e0842c031303d810705200340c6428030340898254640180e80a40d01854011030003060000825261811500110908200e000000460b0b0750402d800f20342c045003a030396002d042c0d00c0d80b2848512240f240d10549202c0618030f050760b0b00030032407a502c052140405644907000d106549038642610714005a8400001e000706c2e01c50740150003810401800459540700365a0440c0c2a42c12810081703454a030300900030800c101c0c40703040c948500641d50441604142c030b0300160b064941c850540180240a07007441005000c0c3d030100417200a40900d18405803609405280d4040c540c1188550404510401084101d083c3c1840c5609044030303281e40d218114010340d0f603401c42d0b0040e80540f45005000310051000c15030401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 433082419 1250 433081169 433081183
    0x5120a0f050120040806161413080706090b07060e01150e070206011514180607032307022d09010b0705011a010824190e0f01060807030905010608 64
    0x181c00124511030540c0e106043c0032603081d030345210503200300020449280082900d5900c0310881a040850840603442651410750780d080c03503080c0600002c3d0000101c82c00c0d4000d0020340c5c00c200212049580c0b2103100707a950024a00070300e205400144034020000e040f07a00080c1340c0442ca5030010a1a44144140c100c801c445500240c041050b0a41042280f9034100b0016005141206050008001c258405410803900d4002c00b07540c1c02e00040c0d0051503001a000409410380c018000e1a038070300c6e860400401c00048101c08083e41c00d0341000c000d200b10900c1007540d401c15001419071003200514040000005940e403205802ea400c00c980e20069540c5c3c02c514140248160026280d4580b820710701a400c4801080c01001c0480044c403408800346d9201d40c000d94812032105a900107505820907040810922680d0164041d00700000b0440705e03070b084000d03602102c0b42c510000a041c0c0300c000048807418002d00070f060000c0c1140740010302d080d05c82c0e0040004540240c0000403020303101c602540c20098 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 433083669 1250 433082419 433082423
    0x14010b03070201140c031f08060114010f110309040902040f0c08070e120c01140408030309100612170f0f1809070c0c090f021209010614030d0905120a0f 67
    0x160100c10070209a40a000f001c054a1141030f91042902c0c1c030b50001c004601000d0640546d41c020340c2d00c4241c01c03690f03280f1110060640002298480e40c2e441c102c0c80d60342c07429124114005107100420607440c0f401844d00303d8207a840c003000341d0b00704803040302800000d001d000c00030fa90145d15050583c60280c4184168641c41c0007071703500e0102915101c140a803107585490760060003140000c0c0362100ca81070200310300d00c000c04240b030302e4001a4000e031403058040c01a071700400000c1c000002402003121f0b00242411500210040501c86c2c02c0e99201c544032816031401300904018011000d00745204400c100804960400024880c10704c4482241d01030305400038510070344c882c401070184c8286445c0105071030340c1c0400e441c0f8080c1c2400c1015520920342c1d081074401ca10a06442c5c603c1c84080960396013f48120032100100030105282c004200f0740078190307501c07036904002035600302d400140c03c0215000800c20ec203620b461040c24900020b22204c41c0340409562860300403082d0120000d454000c0f2034a07a14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 433084919 1250 433083669 433083689
    0x32010050a1b0f02060c070b04150b0a0f050307170c1210060305030304060e0712060e0712050c0109080c03030403110d062d0605130c171003060515061207031401 71
    0xc0c403203d02030f14040003e0420303602d040303041c0f05401c0000c00e80b854080c2d015501c01c6c040348034085030a500501030038003003101c1d0f588400c0116000c120060756003205001c8a104904580215a0b246126010381070152041c0c00e0680001c0b12040301810203a00040806884030205c450f54500c2041c6907003150030700e0708100c0e8a50800400e001c148038040c0a0084d050400c103000d000300f28a044403a41c401d00b10f40100030100e50f00d0703172400c0352140e0092010800078904565031079400300e510b1402c41c0c0c07600b804102c800c0c0810b1026038081100e010004240703040100180046151900355202d6105445c052200250300070300c180f40c2d07100091054020782035004070b1807004045940a003a42410f00b45540101c5003d42458080d04000907554494000700c81c42e111040064191000c090440e05602040030a0030006140030a200390041e00c20000e030122401490100400c1e00d40004040c3d140d40d6195000f580188103020200003404170300300140c1c115589040000c1e00350011181031007a8082640105606 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 433086169 1250 433084919 433084937
    0x91002152406040608040215071e0201080a290406080f03091e01080106032403200d020303030a050709080106060e0103111314040209060c01020304032010050a1b 71
    0x4800010407401d45004102c62040c01d040c1040c1d03005150081c02040130b803082c01c801d620b014050900c1c0301154119600460b920458000400c0024050f04d454001207002500340e800196102030716118448012806840c11100f0303074800d0202190001504a9003944181d9034640065030071010010711030300601c5107020f180c40341c10b1081003101c0700e4031101e441344100a076015825405da92090b0507506640c000d0400049111840402c9196040e11101d50551000304481c04000d20914a600402401d900030f540300110500c0800d0088a40310070100070b415038014000318480102d01c0d00300d10762001c039030b1030103c0c09182c3d02c11031039095940c907600020206482d41c4540096590500814803115040d110b40c0c0d2401801000008240105204924030b01e80320311201032850703035260122040c008000700400d4403041040b01c2039000758000e440c2207010070340701007407928558000c0c03007445004007054003d45025010810000080c000080c020032540f5901d020500c0c1c5a0135850040d60075105503078811000e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 433087419 1250 433086169 433086211
    0xf030b06030a0b19060e010804060204180605090a11070821072d05071b0503030d1b11060a090303150605030709081b1210051f05010f0509100215 64
    0x1001c103d801d800c0c03060703c4130300d21309005094024490040c22402864018002c4c0e595003402e00003400b44e604509981d101c4494182c030302204540000c030a50760101d07076011050300c0e1050900201c03086000c0600c41c106d000c0c0300701000f240407000500003c02d801d0044500c40b40d41c0c0c031480304004008440c02d00c041030041c0781001c6140c280755605100c0700260f07078030308180d0039240c0d4010b040c40c02000e0006199000e00d80f0503242926244c845003008010142c1241e031155121035a030b202800d1104880c0041c6020f0704041440c0c1c52090404190f01ea02c4000178108030707240d540182019001c0c0c140160141a00d52600d017554110502028000704038581d14152203080c08080101451404c0d440b0980c20390000811201001080c0030619070701c0801c44021668a19602d0007904264525040180340d6103810b0401c000c04082c20752400c0e0403554070419940060316007006440380500b0108520000d842848610914145828030f20302999440c01181d40c3c0810491f90300c85014411141400140d8038024040c00c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 433088669 1250 433087419 433087429
    0xa0507020c0a17150114011103030103020901030f0c0f060e030c01031506050711100c03081014090c070b040312060605071703180d090e13050c010f030b06030a0b 71
    0x24114405101400c902801c04000842c14a03160280c01c403014100300602900d60b02c104400c039460001d19014070450b6a50306100000322048582c0c0502143d82141480c15440c000700440b07040c0c0e54014a00d24550b4210f44450b0f051003c4004101d50b41400f030040031807015140c6042c0301c000c080c1d9980d10403003131000704241800c00141c4204c4078141801d103805000301c4000d0101d080140c2d071040c03a02030f446018a046c0440c225985600058104520140fa003030302c941d02141d1342d20f03500e009495552803a01c0e03a03a100c0303c01c0403a40c822207900c0d00841c50010128034010040b15040302150f4841c0741400015100d200c0c0e112802c0e44d0441c0410301c10f003100c0400301000e011303403c020b00e010704109007020800d44480310b0b820301c07032020307c0300030700000001900d8100c2d9000d1000100d000007084564030407841a000d40701800501800400031800c0001801c04480c2034a08a60254448040c14401c0c1c2c51750010740d449c03150a41c80c541810340302c00f0804400c1d116200a076100750a4420b021540a0840081c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 433089919 1250 433088669 433088671
    0x70903050102030c04031a042607061409241504020405032409070305030f071a190621060b0a050d050105010906140102061b070606060806010212041a1812060a05 71
    0x48021000e030040001040500300940006817090030381020784030f0702d00341200d036a104418ac000c2a5034075018030040e88110110700c140c0310302c3c0d170303101100c052000c240c20071030080740c514468400041072500011091080c4da440803218200162000d81030540700c9000038140702c6c031f0b036104d80c50504040e20240381c840180c41d601c0d45c002d5460b1018220b1603085454854487c403e0000c0c0129064001546008003c0c40d400300c800c48504c006642c511a0420404600e150038602084016035424002d0102d000404010210603100c0f10110109a0707140c20358031500603201c030781c1d042d5609c204401000100c688810021008984c426000001d256051030045000c4407260340104c4040c041c584055030160340c0010b2071903000407020820210491325280c14a503148a0b03164000c0c029810500c000900540044209000d590709800741c40e030210803075600d95114050fa02c034010520f0f0003200c41d214013100480003000d400500703243e81170506400c400810110b03030103540c255003654060340400c440c42034103108113 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 433091169 1250 433089919 433089953
    0x60a15080615030703120201230c0f030613060e090607080c0909100f080706081506040324020a110c030c130b010315060203071b080c0907171014180f070903050102030c0403 76
    0x9009c00d42000b0604040034021040703904040701c00000451850703070b80c1151000e41e100c00d01c4818802561a89240422414103840c0002248141c002003101c030340c0281030444c441d00340401e9440c28000402d04128801401400914204039043d80108828000042c1c0002400210004188040c5829002803d020005002036101c5190303407103030703039450b2ba590048408881e040f000c00c44240c0c8032043c03000b222120792518483c00710f100060466409400480101e54000400c0566101000240a00d070301e8141a004565001091080900003040e05901c200c903c01d9041c540042d02e01103103904c603071400e9999040500560300100d4202c0400a14001d5845c0c0c05651400c0c14507100d29014a45598940d44011503228014140005124034422001424600341e10740c40030310706040603503030b040712461680140f080741c401000080c401030811240120750800c64481c004c0d01907071600d6180c0d800076006000030041244040002002c140240083d40c00b9902c1e41c444196520300c0c5143c500180c61004604d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 433092419 1250 433091169 433091231
    0x61814071a190504080d03060f0e0601080708270109140d0c0312091b0608130b060d26030106080a0e0a03120f0e060a15080615030703120201 62
    0x207564154400005032482810529404544600306030401d50362400b940d08048039502c01da1951201b07096140d00602d00311100c10f00103940c021340700c0d03424690a034422541540410030b1007001c54044c0c2d22a1522941c410b107150010f0043d060841e40784451340914803032845041c0e45981010080c811a0082701aa03c6604002040954400f45015280c900400710250902000074a0f0040c5d07200141c010b0260383e9031018051403142115031202d42403900e10b01a00d03000407000c00c006010600251012000560082480035560b56a00c040080c0c40000c900c044440101007a01894000c2c0b5078140b580907039440300303956a220743c10702c80010001e200090020944030309108030350b48215030100b00c9002d0380341c1515000d441104610b13014030140c0820307805040105c3c0f0340050340300c1800000c10120700891405c07000707001c8010b5908000c502603c0a02030003807182c21220120307801a0751804815060b11018040da00c0155880c3c0702d0315030080303210741c1c0345015135151100148625030071503100707014100c1201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 433093525 1106 433092419 433092449
    0x106120609030909060b0f070804170303091501050603190e0f031e0702090105060a120603030c031106160e0102070512012f0a05030406181407 63
    0x81d080d000520302c12004661100c02c0d02844089410170070b01c042c100b010a0400c661290f00c0f08108880141c0c003000001fa0f60070500d00e1424000811030040d684a1408041c42030520303000703a42d802d000c240c0b050018001556200e041e17a03040104080da41480180031348246004003041c401ca81c0051080501c600c180c0000000180320700382d030000c1060604104a002c0d81001d00903040c00030b40c410071850052065041500250200600c0e03480c180480c80410a001011030b012900700341c3c002800319025000381034200d003100d114011540010720342407a102002c05006c000c070740c400708c081000903400c584040e0f208010000141400605a510042010a50031f00904004079441c803503550081418580203011801028444108411289410a071b180115010b0307200800881d50181e403070b45803140000d140440c0790209489414040085101d00881a1030400c0b5079219640da00008a = true := by decide +kernel

theorem cover : BRFrame.Cov 432913669 433093525 := by
  have h0 := BRFrame.cov_init 432913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 432913669 ≤ n) (h2 : n < 433093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
