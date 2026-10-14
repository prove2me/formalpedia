-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1790
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:41:02.239882+00:00
-- url     : https://prove2.me/submissions/5d5d91ba-56fa-462a-bf18-0a5c2340295c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 321762589 ≤ n < 321942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 321763839 1250 321762589 321762601
    0x606091e010315060305011802100311090603130c030b100e160c080f0c03041a07030f080a0212150114030106020309010c021201150f090c08040219030b1303020f06 72
    0x41202030549502494009540d010f0765900b100034142038100800075864044d030709421070618264010418400c07a4070203d0210701d000114262400480c24038400071003030102480300e01d8148083c5921400d2240b8802c0844410b0300e034681040c01e03075441524104500f40c00c0c44507000c00f0945801c042c203042410400603050050549103030f4583c80b101c031802c0100c03610001c410840781904071400d281d89058001e4540440e14011354030f80e801445801e0050064000694405002005030782c0d41680640721800e052040050035203d5240003082c442c0919403c00c009640c6819022070795014298000c00300460b5001c0310005400034103204031006084030148010000310b0340c00400c54004100a10300713419504601d01c041028059120b4401c3c8003542031012025451321070340e2082c4200c441910440205641d20000a000c031040c030207802001418420008016090140c400d4242e81e007520201141d90760390b0707100c40502c182d0a88841254424043d0541c050542c100008030814910348064207042c1850 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 321765089 1250 321763839 321763891
    0x120c0f030c020a0501110a180e04120e030a0c060305060301140c0903070b030a0b0a0603020901020a111908061503010e190c09020a092301091a041205060609 69
    0x1400964040548941550850368402e120401209521000900044801600e8a10940c20030504a40028803001e0700c2d02d800804803603c02d085034030020000d6144d444644480c00c5141200c00c842e000d00c4442c28003801d00b510200704048003a4050307102810044c2c2003400003800e80d00c0c05000c441c840c0c4c1c10329500d1120340c040707012680d0b007010b540e900e001c0d0350b00840c0b000b00e0b0030043c070380d403100008040210411020740030a400007101500c00711030512000e9220603054049000d0700b0008c83c0140e1020b50b8450001c0d103006901d15400e0b0000b000d00400c0200f0f0200d10019501c140c011140301c0d0840c0c1c050240311041e0011064410204400900c02c3e50701a01e040c6031782d070380052500d010b21400740c0c4418003805a421461400b0307045046065584c2e89400d00c0c040c00d243c056211761410385131034840b45003103001841540f83c5520320580d42c03101035510b0255144402010152003088400341044000ba1b607500c1c40e0030300440548100d014086603c0c04000700700319102c00924a0070212000e00e042200c00c519 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 321766339 1250 321765089 321765107
    0x80f0f0703050601020c04090b010608010b070506011406090d031809020c121303021f0f050306100c050106180501030506010e041703100b0307020604050d0e03070303030207060b041407120c 83
    0x51881d00180c03a641e9040103d24000584c1461a000303494203401e48244413109220505842c059220b05c1400d9aa0303903000e8600348102c0c10040e0050b00312a00500070741044001c4c0f4481a003005052034108a16040080c820107141d0000310040750280a0801d0806502d620400062403800c00031424910705001491b01d50103c02400181c82d2000a0030b41d02c02c008401c0903002964016141c0c400d40b18403114283c8070b841da14503000f00403810040e030301c110315449401100c0c41140042c2c501550310f0a0010142c801110311041150035549406010840c0058038107101c070070a101c0c00e0042140e51550405a042410680150603441c40d6402004081000a0441c00705000000d040c680d903560760007440175071810076804c041c0802c90000140055160300007045402640180140c8161b00c20050003651864000900c0f950190000d143c1000464000d0f4040c02046019000102d0b20303090003030025080303030380d8405130100341c50407281400398155201003160652182c0c203a04220013401001c0260180030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 321767589 1250 321766339 321766351
    0xb0604052b06060e0901050f0417130b180a050a12200402040b0d0f09030816030e010501120c1401170c07050f060a0b01020309060f090a030c06090303080f0f 69
    0x14a40d0300e254031403103624292031201d40d001602000f81946490072500400015a0001c00540c2403401149034070540740b840d540030f1584001603950f0720040c00000f50943d0801c0c45503480e01d90001400290fa1000100100f9000340880d400b800d44618560400c0410b58003074015034081d15400d082400508486000005042e400a1010300504085000403d4680b0b10001c900d0300f0900120b00040c0010301d0328094414405011024800c840b054080e40c1c0840700040c401400084030400401c014990510300354101c04900d20b4045404001c141503d42558070a030b200707400c02c440041d130321814402d0703e00905c0f000e49603184992800001080c0000c014003200410008101070410104d00348105440c21078908950080c00c8e070300c000008a04090301c800040b101d40482d01d040c5030380c40005600c0030046903041d120041240381880c281c9030100035144c00c100c500070f070800801c0102002045d5603030150300040035650b8840007000d05600d0300806200c00900940d01030380410f400e000300040700f00100c9034408 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 321768839 1250 321767589 321767629
    0x615060912030a050310050f0108060114130308030603120f040312090e2a0901120b030118050709180201020a240e060f16120e03090a14040b060405 65
    0x1a0340500010078004940e01805070038407000465543c8940c0100103548102c0528101c102d444e81d840d81480810400a001980060039600003e540d56006003180e201409003800420705012202c40182502c2850f03030002d546220001c001c01005150800100300419200268035041c0302898402e11510b01450000502c0e400401c1080c407401441038564100414004c6507070507841c10509050380c0500c032561001902192188201041c0d02520400c80700c80308410f079a00d03001e40d90452401401402ca81c040c4036419503c442c03507802502c0d012500c05040c6030081d409407050031314101610007212000350076140ca4209400c82d17039015030380114919480076000300c0560855003050480c01c0032542c2d00c246000c040c41c54481220500c0c2800a49207104550440b021030a90321110040c251459104130640000381150249204016081d001460440180c000b1241400c9208002070314107051a04500c25001d1030b482003410a1a250090113013840d001d0303d02e40d00d402e08180100d41c0902e010307a8100310503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 321770089 1250 321768839 321768847
    0x130302040f36080d1a060309070303030518010504050d020105060904020a050130020403050609061b0a0309240b1906050a09120c06080106030501050d0204051e0702071502061506 78
    0xa2241058214540e004200658070241d001110001700503050710078406102034000c16140382044411a0b00601d00b0500806031103145540c12405440020414039901c00c45903000e015202d0240241801144110003a203803050032000020b0071504020411407044600d075050101584590360500c0076581e0030310740345407201091aa4a080003202d80920180e81c481c1544125000c482a409002070300d12a5060ba0855110a1006942e174041941c0400304045000f40c0380b07185034000b5006040042083c100403405001c59203905030390143c2040070554a80900c00d0540301018a0311540341a40405c81385c604400c9141000318050350701d18040c00782130101c001100e82c0f13000d0180c048400284100300f1000722119072403400c403040c800b072841883d0100f1151030000c90140d0103405060b05a40d0041c200190384140360302040040d00014154030503407100d0301c0107042142c0d0941d44803403090340640c0081c8900e42ca8040001d400502c0740840404641020040c401000943e52504100e43c40440b601925 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 321771339 1250 321770089 321770171
    0xc120506100e0d0f0b091014150d0602040308041503050702060403110c0901031b050102030f0d02070602070f120e01050c03120903040e0f01090c110c090a0b06130302040f 75
    0x2a066103980d000d05103101c2e52020300304111794030107030522030040130040c0c17110030098060140c04d0f5410345402c0d1103107140f841e00042c004070504041d042101c5004141090290b1076490303100407640030f40c0054414000002d8280700201e803103035010101007500d290401c00c80c580110029111200500000d08000e83e00b0303000340c0b5202c0d0400c80c02480200040c80441f141d6981e15044500103079a040f0203208441000d0700103169030010042d640c000c00314844142c6004041c000c1f0500035444079004a44040c0d0038408000499580007031340c40321610490021608a10311400034004446014145040280400c240c0c181d81c0b0b008019603014001d80285a440c0380c848141c1c050940c00740750800710840c9024000c01141400243d680e0b812520700f01d10400c5048562401151007501d410005002548045803580003403e0554507a5400b80d81034400041c1c0301c9010300011041d50241d80d181030b51545001061003540750a1060f00c424050a8604000c2e420040d980444801280f0440d080e180f0000315080341 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 321772589 1250 321771339 321771349
    0x2190804030f0c0602040503070b0909130c090203041502040803130506091e1522121703151c0302060f01030b0402010c0609020a030606081614040e1507030c120506100e 74
    0x3501f40202507482e115111903018480e42c000352038081c0315a25a8002c0741b91f9181078070407200d0103a00545280600d50408202070f02950024000b00e4044041c29048010404184080c20142000001856132007400703000c850440c0805d0340089108200800c000c5a191340e46101141d418031700030f00c0301c015100c0f0020004500c4060140b0141c0b100388000303074440034084540ca08403087e1010a81c800e1400380c4800020226005120f0010b281070000041072003550709030341c0a15805503034100000c0103070301c81da0045900d0358180e480c0800d40b2242e114410007056014042c46a02c8070041c1c1100c4419859501d80e81e401040280002c0e0500c120b2000d01014448181c2221090b00d401900d1500c0c45030ba2842e145005025510950380c0e680500c80d8610b00700d8112401007404c80d00d540b121215819801c0701000020030701d1402e8500c00c0e02c5081c020705106480311a0240c0300702c081d031b140091000e2503098080e00e04002202d04580e400d2904042007642ea4442d4241d40d40211039140000316010f40c580450 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 321773839 1250 321772589 321772597
    0x20d120207050a0c170304080615042301080705060715050c0d0e03041a030f010e100302030619050105010512040605071b0f02010e060723071802190804030f0c0602 72
    0x241440c0248005103051019144101007100d035013920298402c82420903030b507241e000c7da01610005400000215140180481415004000003400000c4413030112140505446a105c2c0e002d440744100701c01080104020b0114800400c025540d641c508201c950311003820b02c00d40c3c0700c510b40c3c203170b610804108002e0032502a5009103100c020100031549601c12000d5030b0380c0080c8510540da00c001e100501540b46804180c074091620740d02c0103041350342030440c030450701d290081c03046031648502400000540c1d03040044c103000c0e0303d44000c3d20032a030040c040c0c444280c0b50142c0045042c840c04006000103200b00010040d40700d0340003500080c554807154800c861601400303448080410f047d96052091144407064a84498400d880b00c01d03401c83c07590188030780c5018241004c1c00f50410841d000002d501c2c052031098010082c4800e4882244d2107081040b4064464400741420581c0810740d00118260a00310f002d420426042014030f615150368014440a514a860700800501080315010082c51b9011341d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 321775089 1250 321773839 321773843
    0x40204050a1404080403121b11012106031b0806041202010213061206090605030d0e030109020303040806091009110d03030908030a02090a12031709030c011418010606020d120207 78
    0xa0350a810103007030a072851781242c041901ca5101541c10361041900500500d0340a60034101e01c407a4880c01500c1c0c501c1c00d5070842d440c2c1030500910702004c0d030311200004103c0380e5440c010107000501c6421410f004c1d03402485085c0440c071500030b0380001e102803a0002100e030b90240e403106581003a0010075000328003a000f45105d04000041107000490070703a0304008094001011410200242a900c0c10741c7c005803020b0744030f0184c05801c58600058014840d6449510401010380086035020305607000c24034581c0310707912143c405d800481c180312070010107100701c440c03000500c101480340403010380700c0000180741030840e10320414190a0441c201350280d040f503010702c0d4014003501d03207138500417910b8001380d8000743d0001e200d8103c11340003203000340403503289194258040d550502700e000e800741300caa00c00101401c2c0070710910040c004454510800d0081d40448500d4900c01c0e50682802c800003540080001022001a4102007040c00b90710303400200390510403500d180040c5084081d0702214000d100710800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 321776339 1250 321775089 321775121
    0x1030303020c0f0d1d03120d0603021f08060d1407180609110a05160609150f023901050c0717030412050708250b0114010503040204050a 60
    0x1890341581c00342014404000a60348800c80c00940d89454070f003810b0086010444c10046000519194421090280000b41c01c40d211015106494149034114884046460b03468401c14403c5060181c60425070200c45001c000741c0c3c1400b200080c04440c8014003c4e0b00070f517154030704503050040141c58080482c603100159441c0c0d5407106440101002482020b080003810803600040b6108a0711443d22f50b00c0008159908064034200215025888401ea0143e010010402d001c0030606a10403103106a1150400708041c0c25a6004e000a465100303d05049452050165030891081c9418014000c0303148105a040c0001e04151510140d2045c04d94504d075610b043c08000046124170b00500500740142c44204802d40c03560700da00d50a102c03c44004244003480300640742d90071302403800750070824032441c00e59040043c68806000c20040c4617003d14610b091242008090010802c1264090070240c07841d0004040d007500082c01c14031018000a0040f540c45000480102c000c0d0321140c070405207071039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 321777589 1250 321776339 321776341
    0x1110090e0f2401080a0509010905030d15090e03092e090e060406081b01120207030e0405010803130e1906062313031101032705060c0a020307080a090b03 67
    0x40075107200700c81100c9101c02e41c03503038903811072880002c1d154880c859501607640401a6503100640006408050b01c140038a41d290501d090000c1c1e000d1024200c00c92900c2c41c00640c903034000c1e0490710120491303404068060f1a00302201011900801101c805440a44d035513502245064031038102003086143d0300409441c047c0e40900c4555010003100200c0d400001c0c50520380c0c686004210417550360340b0581480b03a2080a0030759102210b0380b904e055810050501c1d21000c41c10040f085e0903039014040480019104c2c0d90310409515261051034007402240000f14205241c101000c0103001890181720000344401c0001500d1020002480d041301898800502c21581d64010151000010710f0b5030303030450b00510f40c030f25114a4201041d110b20201c2c142e11940b24a00d1a201e1206d0300b805605924101500c8281000c014880c065500120800301c10400030b0740842828150700b000740180c00060280e0041211804166002045e00c82546c3c1000440e03942c0c100c284026a44111a0390041404143c044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 321778839 1250 321777589 321777601
    0x506030a061a040f330e0403030b1306030b070c140313051f23071202030a030f020c03070b10080a0b04020906121c050d0e0c01020115031110090e 64
    0x103031004400720b0161014000f06046000c10300540e1040b4002041d95501000c1e40214a05980240c84e0b0141903c0c0c030020101d03846034646c020b45a02290150b0200307456900303000050514030143c80c0700c440380076800c0010a045584001d4a407201400c03400030842014980c406101d50600c0340784c04803600e0b07000c581e5560351004811030603c2d600d103d140d1080700c0c83c1d504d090380c0c03115a0310805000ea0150752000034810201c0d80104c0300c2407180c038186182c40001d0008100080424490240700501c42d00115100c0a005c0303001403d403054541340a0340640144038203001d80b0030000640b0902d5034008045529640c1d41d103002405a581507121030392900c5548004014050750200030380c0118002c2d64200040c2d594481400f1310f6468412103003009900208e880d485810510b0b41d50502d810326860014507080c410102c503000e94161038101d0341341e038001070001081c40da0248901d0b0400001504202c9000d4074640300d40703400c1c00b41c0c188a180100003a1610500061040340043d000d010f4441d402c070100c1c1015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 321780089 1250 321778839 321778871
    0x50d0506010509011a0403020103020d0902060a0c0b09010c1209030224011e050306071110060618080706081609050a0b120a02180607050a020a080a03030f1802040506030a06 76
    0x82c818a8016030a41d030011446651031201264088601804185800e00d194011002580841058a030050369841c007400140e94040c000d007056205982c442c109007075203041c031444c44503014002c0300070740c4c0c0742031890225990000414044448402c0000400441c20b040030790070b0109640d0707591801080001006154101c3c981c01c0c0d4103991651011603540810102081b48911850240540c15804a00000c40d114444c00402120083c60426941e00034403a90041342509e405802003404100d101544e0742045000c19040401481c480d4002c144261424902800104006d410106074018504c1030910311409008540010b040103016105901e0b5039132011902a04103010795044c0c103d4840125952001c18000c1d81c5980080340e0507072010441c13410400020398820700d01141c180c01401041400740c0d0b140800d00000b0b00520000e807010610700d2500030304654540750920940c916064481740d108424a490302c803001e50580300000c41e0344407180064500f0050002c000d03c101d060504111400c580 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 321781339 1250 321780089 321780091
    0x2030307030b010f080a0507120c1d060a0f0513081504110102060103031b0f06110c1e0a02010309081c0c020c04050c030a020708070807050705090f1003030f09050d0506 74
    0x300e90340c1048410003040044440c8588100108000361620001c40c0318000c0c0341d84410b400c0105410260880461914548151b40c0c1070f00c0c0301c03804506a80d042c030400c070750404068490b2000848203d40f9080488a02600d03000c0e100d00214100071380480d1340303000100710805010161404504072034030300c0d9482c1184144000122021a004130300000108440d5000007005c0741a00e50541707841480c5500f040000f00740080e01c0307000ba18005d0040d081440401d038a0703c20086070702c2200c2c2e20b07a070380d405540c081d00d46030402d0a000380e00c0703030071162054108245000c117229190950910b13002c01c070141c2138102001c2030f004030714107904000328150302407080403804d44c0550241c0400b40c0a036501c1541401c1000b0403240300700d8a01e45555801c1000811010b03481c2d00905406225481071403c209650322070b044280c0054030115680c1c1d02807a4144480d10705551000d620400601c030102003440c061040b081030054910004082c05a01a8560300b9540100c9080c409010041c2820501300c0040c1807090395164 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 321782589 1250 321781339 321781351
    0x7080105070e041b1b17040f170c270907030219060917010905030a0507020406050f01050d05070e12012007020109140409020a120c0b0a0c0b04020a0b0307020303 71
    0x92000041000d0b041c03600920100c841e202410740d03403007802190191201030385001208600c40381e405c44600050500d1400790b0b0612101c500d40c0f03407500e0410305007860b290696041014100c40842030050000c0000440b510800070a454605889561280042c540850001044002d081d120204800c404001035480c003242c0c000c80302c0c400c03600da9031500c282400c409400f907000003440514007030146d42400381404080c90034683c000101e11603a600ca450440c0c10134000f55000075800a2101c066240600840c8040c100450310503c1072403624001030802e01c1028945038005880c3e100042c0c200e030250791921a200b41c054040d14007480e412014034001d01c2c50200c00184010412032507448410070b24191558075034103031222030140c0c0c03d02120103540d0000f058419802a03d0305180401a03c401054a001300491080804941160300c0c040703154501603005a908040d06014501165034840720800031260440b100710601e46942c0080b0700801e506801c013103000c40d000001d00c0300d0a6030004c000c1d44212 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 321783839 1250 321782589 321782597
    0x303030902090a2c030714061b1801081503060a1d010c0509060309010e030406032315060f09031c09080d09090b03010f06060504050a050121020703020f0708010507 72
    0x1503103008419007101c900111800c4404c40500d0540705460700b21080480710400c80045a05081640da2408440c1491003100205900a0010f200d0002c0c691003c4001041c40b01e014181000040b4032050044e0301d44189150402140c1c00205d07840d0303a640c2091600c6424083d050381c074245442042a4007400e002e0002c0d51003000c1d5003c0105d603030340c1c042c400c415003140c03140c0c0c4c0d031403802d001c00042000e02d82001c1c00300e6644e551380303078001509200104000c1c070080440e610b0120308401c0e499902c81c0d005a445121007a603c80310303010040340300702500d5002c40c2c0000c1200c15a44401c649442450325020b10a801a054070480d10440840110b00c000100350600c03941d0f0704201c0c15155004a501c501101000a02060b4070304002e000e070102c150015000000c001d400058079140e200000300035500154810404a04002014012030074885000d0000d41020700749140c2005014020141d2010b81c600003502d455030114820041500c02d008644980f60070004942e0311a4540002a009040a43d5054042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 321785089 1250 321783839 321783841
    0x50a09051509040b0a08010510030201030f0e06240d1506080f2d1c0807020304180905070b0f0309010b12030d090309090c0e4015030303090209 63
    0x191a04290444400460005507401e00d0380ba4420b01c0701512602c40c60030b130300000c81100411011000d2003039030310900005d00c680458628600002d0b0445004482248850303040031181120807500041d2150800380095040b01c010000c0600003198400c90a543c40d8407258a400741010f10481c00b2001e40351407c40001000100d03920b03401c41e0f03034440f5010b118014a4110032051800c40c20946c0340812591101451124a0304c20300c1c1820741040340580300108944512404010401d40c4003d03a95440a800e000851901d42402c21907000c000c407910802400035184d22411017040420320a03d0300410201c8030182d2035445040c040401500b04460340303000d942c42c200110301c2615220a186114900220141d4a0140c1408481e4041d00383d80070140d09025109600044004103803080f41950701241e41d1b60440802984200b0082a0404143c454240c04444c03662003964601407038540a64005a910346448110804e000c0203010001d030003110740141d8503c00000c0c5501074211407003c600c225615086 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 321786339 1250 321785089 321785099
    0x30d020c0c130905120f091f11070f030b04050705061315090b040311041b090e1b0415030603060606080f0f1501032003160215070819140403050a09 65
    0x12901d0100740642241e00400c00c0101905000c00185803009000051b14903001c00c40780802c51000d03000003045121402c0f40080401154010420301d14002808050314840e4030b0710040c800880501d0102801a41d4074102090410608001d888014880030303082030b03250f600354252111503070700ca0710903103190010b02c90300d540043c0d100b0b0b1070ba48151929070003050704240c2141c542e89851280c4014540c0c109a45000325524140c00c10307541e03ca0f02030182c1c0c40000fa61f04000000c0d85034100a4000f030454505403040c100707540f40200640b026180c3d43d000d00c40e0380c409023f070101c020f0074050b4800341c40c00b85802000b041880c1e002c20030030f1040c80c80b0070381c00405403908817002e03544080483c5c90f0301c100761100071010020b40c403a800c005110781c403220098006200070035607050786a0041c4c0d03d103a5027540e021a0640174a8040c42460803401c16050080c1003803414041c050b250f13460091400c064070304184a82c40f00708450f98007450b41d074071792050780404501d042d10700078090307620621030301011405415000032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 321787589 1250 321786339 321786341
    0x1210b07201c1107050a0b07030e040603210e10030c140a03140f07020c060f040902160b0105010203030705070201031d102004051c081e0403021c0b0402010c0302030d020c0c13 77
    0x304550014000f01c0d4003e2800c7d0007054641c02010f4110108440700504c003003030355100d00918019502034040344a03101440d000020340f40e5400748405003889102c01c0a61485d13034500b01e09600c40542810045820000002e0032038880c1c001d41e00650a021b404118645c640f6030540c08004e0200c1c40540805886e01d0f000c040f800c0c091021600800141d01c1801c02d00a41c0c10300c200506000c03005200036905142d20b03074034080182c3c0c015001c00000e01d01c00030309102c20301840103c04c5006140a00181d451030038042c800402500c0f664201a06054803004040d6440c4900841c0c00e20810f01402603c3c40c05e0302511600300500b10b08014000a0906951080c1c944130903401110304885005041c40c4c01d2103019550415000220403007641c001d0018444d03181ca64010f81030350a81c0103030040c9001c0e40ca505500c108160088441201c00e0902e010748140000149210007041d00312b42c09003885020180039140803842c502c0b0f8182902034050004c00c46103184607000030b034800c030003070115160180309115888603c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 321788839 1250 321787589 321787603
    0x30711090f010e131121060705090109091a100305090d08070249091410050d0b03010e0d080c03070504051c05060f01210b07201c11 58
    0x14103c0d001040403c6411040c07083d44030740b40f4407890490914910000004030b101c050040c480100282a1011108084040c003d06030710500783d003407450416070345c42d0000f801c4042500070b00304501d070b5071580590301903d4036050031015a00140700f4480c58140040080240000355144c80d064450f144031240414012100240304105540c000d005221801118241d40c00350100100e0055150603291100c440140c80c20a5a81280c0e8001704120800200010142c0c40301c0d6124030307094012518840d040c0d540307100c0050140c4103286413807521030425885000003081403005da158550b1900d15a0010300b440800d06422019840c0c8030070381e0556406442160502c401c4070390a0005d241080140400d00e0106400804151171102c0d600302005c1d19500d0328504401621402c8940c52210300400100742004080072100c840c20301d800780848003039500c00b41c440802070002d100780034101c03550004050a15a10040d007aa600080300c62039444112100c140362125010f201c001100c000949014440004540c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 321790089 1250 321788839 321788849
    0xc090e0601210201090b070501020408060106080103050307031d0a0305060a0b060f0306011b060204091d030a02060a020f0c1e0c0102160501200303150406050d0201020c04050402040e030711090f01 86
    0x1c400e2101082c955800d03502c68140220b0500a007604040707210380c014000307442c40501c21400160348034203212026241040580c0800e08004d254030040c0300040020003502e01c42641418145240b0031100c09154950709481042900940321040000074043d0005880d4081e1040e91700400000c0d841c202403088511850849078003855041020034000d503c00d214109903461500c0b0a14040303085035681c030040e0392066104840e40e50301c402c20440c0748080c182100d400c01d414200110714010854802a456840003800303c0c0c100c03a80410640c8010202004030340003440584180c0d41c055017000c103824420b8841e074412040510a02101015a5000080c1b142c5d14103094a030114025240200464102d44411180e40542c10302101e0480303121420001f6501070b00201c1c0c800c0420301c001c01c06001c00c903010b6a00152140300300c04110700142c1d802041d84e060741c24003981c002c1415078407070003c140903100d01e8103449414880014200184841401c3c164944070040340e000015440724194000710038428024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 321791339 1250 321790089 321790109
    0x90b06040312020c030a05070501090e060d0b0c0c070303030608010b0f130c170103031d0306160302132d09020711010e120609070603150e06011412040c090e0601 71
    0x107001040d800c1c12428030080da07500c100c540d40104036022a08040c0c103401d0440743d6520580040c49290f81120200000c0c29907910000d45600c2c0c80c800046800f440c01d50007800f541003d80104450021500c102d07080c1404040c21030768415920703d40240206590700c00d070441540b82071031140032490f2140034100744074402001c142d500c500c200c12803001810350f0050f02d02070210f000d0300b03030340721219029080d40203501a03100c1403500858000500000c900c0c151103103121750440c904021048006084aa00490301803800580340c0b03000000b0440e050115070401d00054240e402c07020f020881c50440c0c06025010303810300c40c80d0f642d556141d203401d038040c01100401c05914000c141065510401020b0301c520002401c4522000c42108041d043c61000d54801215401c100018016981c043c052244e1040743c820340300c02c045103071403050b06548002400da24100994140d01b2003080442d1030590303128840030656602642003d24290f00c590303c4030700c5452005820003862251039030700418047d040f01e558100c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 321792589 1250 321791339 321791347
    0x40f0b03130b0a02130b25080316020c04050c0903070b04060203040b0a0e1206070311030405070e040c08010509060403030e0303040b0a0b0303040801090605060a120c060c03050c0d0315090b06 84
    0x41c81558102004203180ca91660a0146044001c00b2040d1880140f4403280100e13031b10941e610280c145034421110030f003d50110b201040c000508c294040381d6100c008504046030400103135104a0030300511044040c2c0c01401d02062201100103807008050501048003100c2c01c0715650004c41d4124081d07481a0401768005001c00c201c00c03a100002000e008001d4581489407014070000580d404030580044c1c0d642da4011030070484401d4151040d12000020002c00a084d07203401c0d59599606c8201d8040d80c03a900c000000410204401c00d004403000d410060024045450700d030099a41c0c03040c003221b0a0740083e003407000c0c008550901000310b900403a00714102292941d81d51305084003500041d051550984410040024007140a10072049818414030b8081100d082c801c0c1000f000c107800d504001d030480890810307140003804115442c41210503d0402c24a03010043c101030340d4501401d50903070204d0081007100c0c0c02140d45503018028840544040103401768640c60404100c41d003040c412504040108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 321793839 1250 321792589 321792593
    0x6061d04150c051c0f05150a0b0a03090206040e0709060f02030a030b1f02031e090d03030e0a1a040204111c020d110a1e020d0e0d020a050a0b040f0b0313 67
    0x240016401d9210b90070420b1901d103040d84159000034441c4215001d042e0b955203148045c1140d8024a904035050300c4040501c070301070750005000d140d0305115585500e400040d440b220743d800390b0451007101b500100750380e450700c1e40d1741285c0c0120310b011101600080c0040101080d04c0d4041d100115281241d80c1c010350030400001400c1d00200b2400d0700301c03540709001a0410341d00d209085081f0540d6480755015507111708041c502c200b80c681d00c860001c10b00311814001e0b500241c484804030b440868044c42c01003400d14000c00824102150003002405221468411003c1500340f0110240034074420355041121074000031580307802e4000c144800e101e00304411008480620b840d0041c0c034103901c5d03240c0000707070308000300109800075840307200d8803004500710708020103140e451340224041e400f9080c005405000003240c4000d00366a4040c05c514800c5440b0100d03401551902c078441c0d405044007a103001d08a586400580d4126001442a400c91804010000c0340c0080741c441034900070411015002d07205001d603 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 321795089 1250 321793839 321793841
    0x10e070c1e0203070f090204170106060e0d03030f05040309030b090f120a02120c0a030215130b04050a0b01271817160f0240020405030a06061d0415 65
    0x915416a49440360300b00210300c10040c00003420091031b40c0d2600581d120b180100780460340d9804001d0382443d0f4508002001003a410000c160304001c000c480d030241840031864241c0041281e080240c90151034441000200350704400c0041c1a60b01681112140750340748040380da55a412640d0407039041d0440744108441681c0d100150800001a005842c104543c840085100e80c000c0d4040500b80c3e400b5454210515806100c901441c94480351040d60920300011040c203451072a500050a103040c0306c0014040c0f080c180f00c00e0700c210798040f4944146503590980203080c1307101c940b00800f0851380241d0043c69120680706110aa4402a4034441300d07140585602c0210142040000501c0d0000c1000c081c02030103645169003240d114001d0000020168014800b49906d020000307000f40800550000d41380404c0003c14085100703a540100614080822100190160754840c1e81c142c880c00d6104001c018143e0060800c0d120315102e103211041d080420b102c184181643e015100100c2c56800800341419 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 321796339 1250 321795089 321795143
    0x309052b0b19050906041b080319050d02070b060103050a1503082206050706060905060306060d02130204230307030803130309120506090601060203091503061512010e070c 75
    0x8690b190344001460310390060252841110318105640040040104004005080c085150807038603910080b603050102d02da03682d21502e4001e44800e2001c048045217544200107e03542e010540f241951039241038608400d400c08151582d43c0800d08150004454400d0b030700c07072000c0300350001005030b0f403040c0755881c0c04020360b10070030074101a803159100111002048400c02002000995103c50f601da8090911030304543c002c0d0070030740741d60b0f080605000703213940c000402a4000e101158070741d0010829100041940d200c224039480c00e5400450009511440c41000b4410f00030005c10401c0c00600280400d9150000c81c040184001c2d07090001c901c85400d850b808404080c401e0800c104241d8032983c01d44001000800219003e0b03004404200d801e071400c1c41030074010304e07040c0000c50410b640c110020f148046100b40842400d81e01000080080c0c1c0c600c810034091414001149a0350f1540341800da103281e00c01d02400ba10382403158086030403107206403040a001504550a070541e4880c85030804d0381000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 321797589 1250 321796339 321796351
    0xa0c03050706020903060106080403140316050c0f01050108070315061a030907050d080306030d080106020607210e0c010215060d0f020f130509010e0f0601090c110a0309052b0b 77
    0x250901010030a51401c0049501810300342e00d407400312b460300c1d2400408407080c8002e255281d9100b84140621540e038540029040c1103582003190721400d203601d15501d4442c441c441c4200303d608200000800c02c1000c64044180c034080c4218410076480d03214040240d5101d481080c0d143d0742c51035054040c12103000040c0d42c01040010940d07806a503100c0004550700840241036449020001c2400100c1c50204030203916250a41030000043d854414044e4682200800700300c00d2000b400302d80d8401540c201d900781e9051004001c104040c103541078034195240c0800f0061805442029000f40150b150340c0c0d9014030495006200c482e40300c6003551900c4404282980498001e80c040d08542d0b030a13a0340c0c00c9042401c07100000001924504a45030600b50b40708201984441d402001c03902e0780448000c91a00d054452500c0040303418003901e00c0885202000040008503409078905100415621600d5401215030480355495500711491142c80001c42042050401200e103802e0303440011004410107074848 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 321798839 1250 321797589 321797591
    0x80d08060d0b010b03060f18011a0702090f0a0e1504060b0a05101d01140706020a020a080703050408120a17070e0a08010b1c0c06030b0a052e02030a0c03050706 70
    0x1581c0d9544503101c0c8032080e04110080c443c040100181800c3c85100e4016080045554800482d44003401c904c2400c0103000301090300410366411351002611008403610680c0c060002e2102d4500324415541307684050351002c07107103420108207103010503002403068407506442d681002641c4543d0b461200a1149900c3c130354000c613144400040a40d02d80d00040d09840b030030744400410940840441c0c2428001000c00c605015120f12808051120703541030701c070007650010005075540b2442d1000d034a00001c001009000d041e002800c4010503034483c01400031162001d0486508040c0090807804c50300a40742c0d40d0000450f180a801e0780300181e00105034002040d401d0400e00011000e0200c1c00288003600801016916103001c1c0700c0c642003c45c0c8900040e441111103c0450074155980c0c4103040d0a40b184504058551005030345c0f82e958501d014004244c014241c040c0007160140c00c020b12403403074000c2465a0140002c1169840c000310403030340410b585958400d40c013000e81e138040e170f40d5801c1031000f83d41e01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 321800089 1250 321798839 321798859
    0x1020c06011e0b0c010b1002012906041203020f01060603061206020d140108210414061b01050a1d0d0816050d020705011e0603082a0604031d01020304080d0806 70
    0x1415021000f0b11308010030f00000f25082940b00180701600104041090440e8500700c480496400f1507000751b9039404031846503c01c1080791100082982c021600507a1000d144180303c50304041d000101040041c041d003000b400000d580e42d400f0340407503030a84107040c2849280640d00e80018095402081a2045c007400040c45041806020340900f00980200c5000d6201c03070b0301245c40c44403422184203040060b084141c40d290414406650030350b40224641e0284501080031103061540120910010307184000030080c2e45030001152015068088105c2001c201300342004291700c10110701c40c1d518200c19145c261542d2200c0c0c002d100d080040c000380c0001c0210038480140b0181460004100b07450044001103036801204801108488900030208000d5180c81c90170400200341109960800e4299203030741c11a4060400c2e8000845c04002c6803d000f40102c034100001c15801c4281c1c4503887c00100a51360b40e0440c49801a40d41c0e2165001d03a04c020340c04150341c0800345104191440c0d221401400700446 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 321801339 1250 321800089 321800099
    0x5040923070504050a080f2d011e111e031b0c030a0305060913080304020103230906161704030509031501050f040902090a050c04051801080c0301020c06011e 69
    0x200c0c16a05600003403400501080103242001c011009882604080c0080003840d10341290b4811400c2e080803c059154807484072105250805100010711a00081c80004039000c02c1c070460300d12118215030b240b46412200c0842c081000c007501c0c01c07415000d610710200180105048003613007000709030301c00d40c07140210f100a4000b0381c1c4018001541030100113603245c98220b030000e029140014400c81c0240c04090810403040038007042d85585580041c80700d0fa072900c0b503000403409003d8a12819048406040c0100440803031080943e12518550003969000e4840c89401c08291103002c0124000580943e02d00c011060121145a0414802d0420525141020700840e0070f240010340742410502e120001003086041030b0140704010381c01214200000086580042c0b441c80c40079191000c443e64410000703083c0d0303418800703c0f07020b04401441070022003074400ca2404000f43c2400703221910300640c0c0200041d4101402500c12000104000d404582e0030724101903200790005a01414810001e403000803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 321802589 1250 321801339 321801401
    0x10081510020f0c0909250e09150a1a13060504050c070606080703080316140c010b040b0402040302030a0816021e0f01022a010306080709060321050409 66
    0x40159640c0141c8803035848008020305001d400d038522030140e032400041240121006c03840f10a00f08110b85680f01060b8035003007004c07040040e074101c00c0c0082061024400c03c0700c0005507254041e0010341e082032455980190901c1901c0079404c1c40300c190882881502120728102011402014403150001074843c0d03a50009410f03074074240c60070f000131400040e041003880820701403e000340100070000c2c00340c1c51551b61400d1481c880182124290780c400011701181d98402c403030340b40c07019a400044648070584440300038003d0104000f00303440341d850b013a0411142d00b054002d540c1220380042c040c0003c6020345e206c001145d80300744021100c0360a00000361006a40e030815000d517894242e008500140030450501c0307110401b000c0b909040d0b50248031603541c2c0100c2e801412044201c0500e90310003d44660005034090300098101103018007501e01c0201b118100741d8003110480c0d014106589900c0318901c1085d00c003000100c0f2507c0001c004200500000c5510382000d182c03000c820314220501c0e80a00d411302 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 321803839 1250 321802589 321802609
    0x20f0906030109060302031911010f0216080d020c03120406260103060b0a0506030610030c170f060307060c050307032303090c040b12070317071401060504060e06100815 74
    0x28003c1aa520030500543c1410056102c41d0741c0e0940d0440c10100c80ea85640c800001d140801324100620260100e100c14400e002c4554100b5418215044454492409039140c80102105000503c91401e82c00740c00d243c0040d09020718000d0480b440d1900e424510112101007032400080c81025514102c8081407103980301641c001c600541c00000c0340200e10080000e13403440c55001d04c0c13083d0801d2060019607542d00d0031550000003a8140000d90f4060700000303036908c14100e9100c501f4004207404101042c04000002441480d045081d1203001c1c5d2078003c01d5a503000703c51805400ca40c01403000b440000e014940400100d0a00740b20401c10078030704030126005074011208903460307400851820510b0b003004d004003154440201d405c0304228080b0156555144070600c8017403c034000303032410303100c0b00a4090200c40c54103030050680d0050180e540e4480e07000c1c0840b07200b910700491402500254003140000014000c01c40200100038034105400c0440318964090020000e044440c5141d0610f0380d5071040c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 321805089 1250 321803839 321803849
    0xc0e090a0213170c010306051e040b03070815100806040309090213050a0b191d01080c1315080f040b010b180a060c02130216081b061005041d030a03020f09060301 71
    0x9000f030340d44e200c00050581c0c62603445075005480d6185000e0341e4010300c1c2200810140b00b642c001607c0d03103400700083d160010301d40c01040075002d0014000d1048100c0441c0324843d90320000014800c540da03d1075290f660004450150005440c00400d1001c461281c00812006a1101000d96065101c50010712480c0301e5500110020500065480780c0d2030201e44540d00e540e90b2414980c5966160b4131204122100d00824581002051000944e00c55200d0701500c00040b420301000c03144540318040e0612142d03d006a000104044038001852122001162485164003c00e04d0381564030300516141c05806c903420034a1b9951030040034200e151075003140c2c80d000340a603030789094194082d401405a0480c595280700700c220700400407900955040c0f0501d113081d981c0541e6459950f0404070b110801e4107012520051240542030500c80140c500710309440903524215400c1006241c140700361100010070301c0d19403140b6003060128145542c081e50161070102900c8011515281c180c90014010354800d800c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 321806339 1250 321805089 321805093
    0x2061204150911040c020a0f08040806090a1101110f01050f01090f06050a1509030803091b0409020906090c07050312011401050c2d0609010e010c0e090a021317 70
    0x40106000c0d50080c80000048906030401002e109622002c040c40a41002580131300d031141981481d491080050542e200e4000e0710307202403e2014074114406511a2080007007508c0b94802003108030030003140c2a1800d96004200d00869802540199100c0740500700350449409203004614240310b081c003e02d4401c590551800c01c02e5810b00c2880c400300d92003203c0c042e8a4900d031003402e118984840884e03600b5203c4c01c0165170b0b0199104c10045410003032a402c010864940070061000762040000c51182d907240481c1c0c40c0d0000d05444050004465a062010350300040d01c501141050601401198000240150072860704c0c005071219071840e48103140386980384010304010045c4140c00c02d254a160300007443d0561800c440d8040407940c50b074282c1c040c122225060724803100e112150000e0541c41e034a40038280d0b01c0307505c2c2c2901e0003402042c11154021895003440790103d4814495424200c0c5041c004010201c41d46600c00b0036070094201000411407400550000326820420040c203152701d03814200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 321807589 1250 321806339 321806341
    0x52805070e031603060c05070b1b1626070f0b06061603023a121b0302181002070608090f1c09081204060c060b061c11031b070c03020612 60
    0x40d100089076291b8100c081004030900c01c42c00001c5900c01100e40110440003020b410700f0034640e0a6510788a0880c16901000c501c0c4040000c1021070400420040c03540583c43c002110114910525885180e034010440d185000f05440020b0340403000c0743d08810b003e40308500740a18184001040c5114078400d038003681c000b042d05481d00c607070003164005e070901041010040826026500845108240380381007400b4014000c00c00c5000c0b643c1c00340c00c0340140403070b1101d03011400e00c40240c003d510261001810802000d116402d40c203040e0700c00c0c40c40850b40ea0041400914020080701c0003c00981080c001c1c1c040c8010b10320400030104920900c0e0303a5107004149500403a414050003140d002d0b4040c12160b0014030f80d0010001c070381000d85086a410b070030150390b00d01840c03401c200144205902541c2c0800085a42c0400d00010000c0c480c6441030000104169000764100038640e0008035892850b0320300c03043c00005020b1000010708400c51081607241d04241c1c60f6030000f51140c12510f5031101c040c0d1040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 321808839 1250 321807589 321807593
    0x9020a0c060e03130b0c030730030515010e150f070804030317070801050a030305070312050c04060e220e0f0105040302060609060f0a03170d020408030c01052805070e031603 76
    0x513950900400000c2e840f10302d80010700300c010303403240200c41e070150a00894400003452180c29180d103000c0040200d012000c24814100c024000306000d6907240700d540d41d030b800c010105501070501307004c0035000140450010350710104c0c8040d16603c080c2400765800350170700040000441a0015201840c803076290904510040800300700015001000d1404111071200108025241c050303a210039a90507280c015581c0b40241019502a078040d0692104607241c00c0c1004510b02024014006a44903540c60124140403001040380601c904541c00410741c41006400780540e4156010754440543d020a40d654007003200102401c441040360280d015070841820000e203460100e60f07490380100100c0320344424540020209443c001d40d400000c0c24088241e640301c101c040400180c600100e5124401d658494688840315200e4006400720540e0f5800d150100d51049500b81250340c44030310040c0049440b034034442c071203c09007201402c0b00003440a0140c1d00340031a2010310620300a80715802c40d044d8154a18 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 321810089 1250 321808839 321808867
    0x608060906070516020f041113031103030a1418030610051503010b090d02010302160f061d030d110403060606081b2718071d0a03020a09020a0c060e03 66
    0xa0100302041000c01489041603c1036010300c5138039030140d80c10301006103100b001c14002c2601443c00308106002241c440300c00e0004103d02002d1b00c1c0300707607035400003801c0e00c20905030341c2d01030340d544040131400040200d900800840003400103550100c0307108880c0c078000c4000c41c1c1002015070741010b21010030f88080c452410400700911312108000303e9240f8541c50500d018003907003d0a0742c15842140010811030940e8401c3d0140c4580c8a85134508060b83e048038948444944030501017150840c0c2825180440c004c03210886608512480014600d0403040403039000040c10b0f13001180009040a0002201081c0c281c0700e801d01901030303910388078698100b41103104074032240801c07040505d40080000c2000d03048880721070282c020840720120f199403414000a4000d035400408101c0f43c076104d204003c0d01d194022541880c44016001040c0c3c5107640304240308031142035020194100e1107202d010010048071354010044580ea615182c14100443d58400080c0c0316004011801544041030000740160a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 321811339 1250 321810089 321810091
    0x3060e030d0b03030a050f03060d0606060f020606091515070804060306051903021e0301090b04081c0605010c0f0311120c01150f030204020304140d17161709100608060906 75
    0x803c4006600781544044020428814013060700b000c0e0300007001107420f82e120000394030f1405a00c400e09001c556252440181004101c0c640840148925000b0031002d05241c40760310300520344818040b50000c4810300740000c0c6c94502510480461081001d04042800400079102070b000d56a40030400300d00c2d01081001c110850000b140c4045510712003000103030f550303c0304000080600306442802026880000e40105410540039003c0c00790842048104080c04000702440d4002541d6050840e08550301d0714100e450314020140850058120200420309000c111980c0601c2803920400c807a16201d603550800110500001c582540410a03003652030f4280508004090494280114946401c1c554100c2250620010f406107a000011800307111180c01401c0d04500c03810308603140136420070300040183c10303440300d840c00101c260404034441300e00c22112210801700603039540707180340003a020204e6004000b8003415080e210b03915036120180400d00803d002000e408021300014034200380c1560901d50 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 321812589 1250 321811339 321811361
    0x621150102160e0603100204030c030303051f23120604150e190305130b0301031e030c0b0709080a0c09060f060f0c020d0b16032406081003060e030d 65
    0x514000040d02030810300d41011a0740002c1d0383c80854803a100845e0a00e20001d04640039070b400090003109100d0561601c03c202e83c801d50b0100040e654042c2115084c0b14072030142c0d80f2843c020b002c100850022045917000c5041d14807255400300450000040120a80090f82d5013281c011104000078000301e4044c090115509071f20a100d000c403e41012500d500080207811840a007200c1c0384002d00d071040c415910450019440010f0700e0740c8410400c2d074190800d2008494030706122200042680240151100c03d680c1915540301810841c0d80305040c1c4a0300420345c40411501c5000014009010042030900b0f90003108890442d500b4011440d003a0390858200600c1c036450040100000b550041460074038905501d880b215640c524800a101d22031b00260162030404c4490030b1100102c049441040300c0409518100164910302d100200380802e052a000c0f03880014007410400c150180350320903800260640242c07a016120303a540c4040720460301402040e41d101252580c40ca052a2164200c1e0071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 321813839 1250 321812589 321812593
    0x3031d07080a081303060c08090c0406030201120513081603020c100e0622060e010e0406061b060f0e01200309100b041b050309010b040b09150621150102 67
    0x60400710500da503000100700040000b83d0000303818801241080200c006154804021700100c80006402041c02d00e0940d9545003c2c01520520801d524003880f42000700ea43c180c4078100c00c60a8048024001d12004186140c01c0c00000103850004582e4002800141c20b20100d01d100e18070b04d404c00034036041701c40c130050317005590b4601c000b001d16800142c03094101508590389981c031105049c6a51084c002d003441d0440b03100450350081001038100300c1402c0c000c0400e0341c07901c10040030582040290f51851061b64085240c4944030540f00250990705012280101c001184e5100c482080718101c601c514400c140995449621245540240303550100b118101d2460358150700b0b207000502c4d281c01d070300883e0300426279692141c01065101c90f040785d40505140312445609440d07120380600164401c9aa07907101c1c2d403074156030003e46c2c500741c4075540780b0034400340c000c109035174840144100c412203070701c50b640d8407440c1400483c1c5d40b86251024400d0504040031202d00354140500c0b5120300d5003413540c0080c155 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 321815089 1250 321813839 321813853
    0x20702030d08101d010b03040804090921020303100302041107050a0804091401080c042d0912021204032913020102190809040c0e0604030b010807060f02030418020d020703031d 77
    0xc14881303198603056444841082da603e407254507010348548600d9102001c2c0e0b40c24094000306200c010307107030400e1007a601054032140c080140c0d822a01c921007181c280510042d4000180090700f881c1d032003008150a401240c1c0c0c5405005d031075142c5096100001104e030410005001d00030352140380108000c010300090010081d505210303040b5100e4107030041c6640210f540e8801c41d98105100400414a0f07180011200a500989035860000c0c180081080d90040d801c913500302c440b1440090225140140f8074032060a080c2140d40c0c0c0e460220907a540d9000083d01c100340040e00ca07541c0444907015214021020007521340e0fa100190402c00c84800022121040c00100342c08a480001110380c9107a0440707000500740c03090701d01501e403025040041c40e0480d8010902204000701040158144c4030320b00c0854010643d124070451b820410307224940c0c0140c0062000b00b11408001640c10396071410703824090b0811001c00014070803070b0071400d415000281c031050324000c0008a21460b07051400700101a2500c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 321816339 1250 321815089 321815129
    0x8060705040311030c0402030906070908160513020c071d0601031103040602090a1e031a070c231903081803040b1c09030e03071d010603090303020702030d0810 70
    0x3180100d2002800394900180c0c048030559060014182d040001801191282005c407000781c1c0d503c0d801c40d045404a1021703d0045500e900c0003926048001e0020b620301086410f00781070040303090b01c0e0f01c80309001f0754081c407010001e1001400300401525901d000b000c50901190704956600b80007501032814180fa06619201040d1031100b200e9116400000140c1d441006001040034000c10b940603d09034a0303440d0108142c0040242400c00707c078020742d401c0c0c1d122400e02507d08044142500c100d4041880001c1e03800005421202007072440160003c01d2000400020040c0c0c00c1a01d00c00e6031000c1c46a241425108041e0442c0e42030740c010081d90409084022101222035030381c130a40c010407001c0b50010070000d8580d40c0400300e4001581c403c580605c500d103d80e1030b01620a00941c2e4040d8480c1c020754202242d07c8600c8100f10300d07070081c00070302192180d1804030b00340e00a104080050301003580810039035015850810803070002821643d01c500407413030302200b160510b64160300440d0042c0c04007400300b20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 321817589 1250 321816339 321816347
    0x2303060603010b0c0c1801091a030d0e120d05031803090d150902060705010501030c0e0c04150c080309060a050108070b1e090d0624150f0207090204090213080607 71
    0x1043d030703c24240b40e60392078404618140c80d1180c1110f000b03034000c0111159000300c00c0b00c030400318100e41e601c0707006002c2e80f58800c034a40800f2552001245d0154005034541d08128421808507420704005420898150403003c00075091002809448002c501e00000703000b0313201068900c104c1400c03c03220145003003010010004200c0f40d0b40350300c0a440e03158202001c10000d803540d8404001d030f6038024441c0350784d0300c05441c1c403a01810091109440c682c940160029046400c0424940305240c0d41c90b40038038050800f00e0010300c142050440c00100300080e040280061300c1c840082d405003100a00400503803620001c01419164160010140b43c0c0040c1c004001000e208819030300d40392207070b003454284210848091102c5004180100d5031013460003400b402800306036448510307100d002108180403000449880c1c45008402c0c8035204030300300008215015648035044005101d461481920011b9540d600c0040590b0043e0b000504100d07400102c03a4036001200c06407a0080c840c080c06800c051401c0d0340060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 321818839 1250 321817589 321817591
    0x201080610030209100c0b09010501030f0f050123090c01090b0a141306050304060b0d120c0614070e190305070605030903040801020a1706090c0f0a0306080a032303060603 75
    0x40c001c162614403140c00038002d405403041034001520740010036440030002003401003107520a50b000300000c00030420280040c002e4a06a0f43c201c5646031280086a035071000902c004241034503a135503103400350b460b02100300174049065a031310642d021560a00d03e0505042094440589060150000c0c0411a500d4001c0540d1410865810404140021880c00f00c1c3d10744100c8502c1000040032010100e611900040654011400f41c4800c0005c00d50f46014048000c80d032010141109040c1c0e6200c9500328422410340c1c21840c41841c004c00c85050340c01c0351800d510802c0da01403011a140c840c207080c1e5400d00e04068840380510445600c81c4034079584446403104014003071003042101c00030001e2514841001110000e041c4480215a1020b403404024141401c0040c0120008440d80c0842c0045c6003040c0100d003c1d204618100f031800f1a00d8804404d91350003200b8060a040d201d08000442c130409000c0c1c3d024440c025150312003070a00032848450b072400c0640c0c4000380b03800c0a0062040684420040da = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 321820089 1250 321818839 321818851
    0x2091009050a1e0b0a051f1b020102070306050c1b06071106130201030c0c170415050a02120a09030c1403010506010503100b0307030f0c0905100507020609040203150a0b090f0a03020108 81
    0x944804c001c021903d0700100c0e400654001d054809140d4030415601c90801c6a41c6240d40c9034442002c0d103100021502c011300c0e4019006a002c604244081200c59112079001801c0d148041c2c0703480400d56282681321010b40c214003281e0418400c00601d42d13007000345420b9042404001c2c0001d49400910031804072180ca9000c2d04056644c981c2030602c0c1c1c0504007540800350030004003103c00d44c41061562a550141c0254460f008217040c100c8003a81c007035070070f84030b6018031600605168920700403191103d40180c08038604001610500001103841c000d101000f8000742c01596003610b801005050949038041d0016042000800420820170002c40d803071001c3e00d00521520350b40b500c0303003841100039101d01b0b0701060b45103181580d00e000f01500004034404581043c1c4003a0003098081d5001d4800e400340010182d0072603c20009018a0704d40f41e0f000319844107240301649483c40300761010a02c42030305508220607811000075045210302d0b0100c0c3d150701515080307030000328003825640001c01080d400b8280b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 321821339 1250 321820089 321820091
    0xd09053004090b0a080f0f070f150e03010b1e03011505100f021005070806031e03120a020d0212071814190317120a06081c02030702091009050a1e 64
    0x407a01958858844c031380240400f8013110142e0900082e420388a80304401046001d100b12080056640c2d482018901150202c0401000d8240c0017801912400c01c00d01005625540e50009400e00303a8400d400141a03000d08181d500b1104c010100349821076041c1c0d1104040060a08800c000944d11038001e0303121201c05190050911101500607464494106e00880003d8248400c2000040d4401031061040d141102124140310414034034481240c8050480c0c0d100e030300301300881c000d8882562502500000b1800340149000080c1d41480101d81100d0454a07150f003108083c0b190040e0310440488104480788a81c1101e20300c1c181090301410b28500005004000400c8a6110510280ca014008641080c904407198602a100e41426070202071203100807080007011076887c4a540c400c0b02d0595192900074100c0304403080e446004900018140380851000304101001600d60b464181c0c000c0d400500f01c4c483c55800c1980e4503080d1070000f45451015480c0140d010400e0010781c1074548407a0003540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 321822589 1250 321821339 321821351
    0xe09070909060e090c190f0b0306011b0c051c0b0a06061d0609090606090a06021e0703120507080421060b100c140a0c120212070e16050d0905300409 65
    0x41052130710246c541c4440407668001c040000c0300d03400c40c001140b107940e01f665888a206c02c4100102d020303404446000c1e0003450201402d04c8141400304039287c0d0307040010f040140460040d071f603501d1514070440c0c515200e075494400c01c000243d0042142d600100111920007031205051000c01c240b805030300e1441e807040300d104cc0820500c1e203c4a0444007440b40142c03c00034003e4903108007070750701c1c0d8241c1308078a03810000c980c002804102c08110201600c0d4802500ca1b010072a511040710361b234005070400e8270168002c020009080c47c080943d401003042c0f00351210b4083c0404d007842ca0845038159403250080c160310301005600365200703039515000e07944011f43c44a0302181e809032500c0c011130740d180200278603030412001c2005154680e0311128144212101c01c0d4a90b0741801440d2121410320039000002d00c0304010800030060812507592000c890710b00103007410f90030b2002d50140e40c1c1d0810195415002140b1421491503a2888502100b600816050b04c40c00c0101011400b8480ca108260300580d80303003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 321823839 1250 321822589 321822619
    0xd031d0402040b190f03060305120c030906030a0e10020c030a080403050417010506040f09020607030f020a020405180f010203010b0d090c05030619050f060904120e09070909060e090c 80
    0x1d419100544200c3c6103950300c1e114a070810381d2500300c071000c100f030114210340030080c5c480c0d20901918042c3e0b40d000303010305881604400c05881c941c120094400c0103020501140c0665215800a90300c50182d01d400825020010701e549400e017021030610800041c010011103e29880010484500c00032600c0c1c003550740e60712414225000c0c0100d0304140d070080c08107070710034030230800540100b801a1411141088081070160714a0119800f200c40207402000c10300c00b010100c5e0064195136641e0809005031b038280d00440e0f0010703003110003c031107003109900b40b481500c01104080101d100e086140030000c61075941007844e403039214054210407030420307515070f0089000c1001c1070b61a600146005411a80641040c0400d50101002c0d541c10803522440c050000314400c0340c1240e403e000d0100544400c0700c07a00c50342c03142c0d000021024115402e009900e420751140d0707290404a035100c1c41150fa507200180d42131203580010344141e58010340d02c0a002c6d90a01c01740700300210301800b20031004c58201e018000b5071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 321825089 1250 321823839 321823841
    0x102712020a0b0a0e16030c0e0703060f0b032509050609040908190f0801030b070818060f0a0b040b03070b07140f010603020a05030102070b182b09050d031d04 69
    0x40c10700410000891081c0548102e0b16008184484c140c0c0098449000311440900d40c5044540f0018210582006042207010841d95009412001c0c901c3d010515913151040017101e4062540007076a105030020400104901c415498034a000c0d40169070300b0060100c48000305544101e0007014803458000a601d40b03559038640c80707686c05a51215460751250340c80d0180c00107002520f4644e10101d40c4d4000034a240d580724590040c140c2e41d00424458290325060011511740000420301c08034231503c0b0180064600040101c00e02c1403440007519400d0b4940300000c0e034142d42c05440303000d0041c4d0a0440440c0745548c0461038005403100880301544507040ba0400804110003202000441d0285000c0d01a0502c0c0c113400c0107080c3c038001d40350ba5074200e40d41d41c03d00d8203d220301c02014010321038010216642d005007002003d40c0700d620a0807251b0380d41c20f000540303801030794034045a640c06124803070302c4032120713001030081008140c110b80380240e0342d0840d1000b070f01450307207118070040300c1182045c64400ca41c2d44d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 321826339 1250 321825089 321825103
    0xf0103020a1214070f1e030207030e06070b0403092c0a0912050306030714010c121e11120f03040b070c0c090c03110421050106030f0510271202 63
    0x10a20890a6103070b0042c16281040c1c410b90005400121000300040c0110342c6c4d81d803a0385c501006400c14090800d012002900030001c21410800600c132020460350f1004090040e880c003c0085a1450a040ca40500880c0c242e80c882040c1ea02ca070003900756961240c20a03405024084010080c1a60714007000f5001400401401040e076882034138888076132036118010718869007068048642040c2c45030400a42c0d203ca04140c2800144031001c07050016010145800d0750310b1040c208078005500041901610b4051071580311300013100080da4040041e000c01486030142c17008501c46107440c90500c1c01e04480e02c401040031f070140390044040303820140f003118200302480d0403401c1c6002994442a400028110b100c1c0250b0000e4200b049280e0340310008c00450381203840e10840c1c01d01c204848101c0485401080c10140c807107541e140e10000100f1b00c4cc0b690003640c3c5100d100a030104511840c07801d01215212500080000d1400d201c071617800402d41002050603800c4014055090349140e8100d141a41c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 321827589 1250 321826339 321826367
    0xa12060b0d050a021b0307060b01090321030e011a0f09040f0320010501090e0d020c01050d0f0e0f010b0a06020105060a050405041e1506051801030b0903070c060903110f0f0103020a 79
    0x1a8440c172800300b01030040003401c1c0c19441040244803c5440c10f004465800c0623000203006101c0e0803030f417001e401118043c00c00c8901c0040c240410320380900b401042c219915030400d0070101c18003408409203441c01d1491900a0302c2c089804600d64103050701d0744c400300350301c0250090500c000c60000d50900c2c90000708600074011586c000388019038507040b2110203005048189807032849010f540038a40380c008500c480240c1d01c1a9202414480291440c0d07000e0700100e0000b032141952000b201203d82c2080c0304070be581805010001c2201d0b2400c2043c0042c0510962204045900d480b05001d8280d440407040f0044840c2168040307625280e608105c194a21080101802c4088010101082045c00b10008840300007524081000320768440504c100694000c0513007845040c00001800000c07003c0ca0750903080745500303003100d00341103960f40d408c070000d5030540151012410b45481041040b030100078a000d00d100c155642451900180f000c2030440711001d440300c0c14540c0219030355000c1d0744543d0720a001c82c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 321828839 1250 321827589 321827617
    0x20309070e0403020d090504090201171003170306031e0715030b130b03070b070803040b13120201021201240c030201150e040c0b07020108011202010e04020408030a12060b0d050a02 79
    0x2040603c0d0184d500c0d0b070801a9140401d45200c0001283c0c03405e8400d5212464040e184e80f1081c190311009a240000003c108990051180c032010002c61841c0780316240f5240300d4500250340341040c80806203401c1c0200c00c203c1d400201d02c51417074500f86001c112402142e80d8151710180c01c40c1103140c1540074103140c1300801c0d00164669000d00900980340c01c1030041840c1501034400040c1c4440074030700e03680718084000c0c04c025402c2010400055030011483e07848030450302c55201c2195980d0741d003440400361149142c0181e402140220825203031540d50340c010840800c1350b10b144002a010f03940c070308400d0f1240702d00784031480d800300c01814002e40108115044030001d00d4021900c40100b440c0724541136078103482d103c0040b0801b207a1800140100c0c2c041da90142c6611450741c0c0307030821003c00380350041007c0b03040050003118503145403114000b07000a001464042d40c1c42d0320b66502d00030603000003c203400c03640e2030422008101a07a481002c85546860701070340410550785008900010f403142111007ca0700b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 321830089 1250 321828839 321828841
    0x14130b04390512030703180509010b18030705180a0f020a20030313020d150c030e0609060402100e0411071209091104090504151a010f030504050c04020309070e 70
    0x990070000c2040d25101d0800066480c01d602e400611201035040ca51185240c0e00411108000c24000c1da44a1695001a0298901079031200041007200000303030b000807040e03200407070000f012441640b00011181d50580c01031502e2361405000890107004449042c00510998020403900c9610390032811030a10302003070540d5103110300c480060590200601c00c0e840130701306001c138020340c031000f0007280e001d4045800456110340480d020803401c11200318017250b0740c0303a1040c0740903414003243c007401d14402d0035901c0009102110b40c44050400c04000c20300d24550b0411020000181d80750410304a1444c3e45241c02b0024200d40d0002c20002e0000b80c00d0503100c018041030520801c41c403100c0b05e403c0022181e070ba0045080c0d991140030300f9220003510f0545040400c0c0710030b10000140740d01a43d4040d001d00402c0c0762044418208804840f00031008803070b1a800265a09915600b1084198034581c4c1440c0800651030107840c0c60351103c0207d0706980c4a9070b0000003281c81c82200f040054080c1c14203414a00003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 321831339 1250 321830089 321830153
    0x60b0a06021f0203010f05150d060b120906040f06021b1903030b0604080d0e152106030a02060301150e060307110106120809010e0111030c0307020414130b04 69
    0x70742c8201c08400c60305003441c50640d2040607664001d0324122200302507251001401d0000b00680210342481c0c49143c10014001c5070400a2640a01801003101041256582942d0004c0903803d040c002d010210552194040c0000107454102d50303103143d600002e00507111028240b500070f920b4039041610807680715030900e80c000c0c140c3d5600c180540d14443d0710100250b55002050003114090391159440503009200d02c008643d00030304400d841c071603004003c041d1800b40d0000004540d0044901071000441c8001000b0700e01001c135800d5a082242100200300e90078043c0e00061b0b052005020309005402c0c5c240500302c0741c5c3e014141901c16004001d02c002d440e443c011200400305055052040c03030307c2d82070001c00a1100c1000512006154001090a1800c0b9003074005480c40c64041300c50504128121494140c0034005001500b0f40c03034000303070203560742e80054010401500d020b09511540b80310b80301d00740007240741d65007a42c101566225030004070701da075203042180813820410700005124440b07460303c0c44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 321832589 1250 321831339 321831343
    0x503070f1509061d070509010603090804051011010609061a0c1002071a101503020a020f030c070905010902030c0a0c03050f040e0115090f1710140f1501020316060b0a0602 75
    0xc60702013030004030880d0014000a2a6604418816280c003c00c000c2c0040c03000520a8000c642290700544889281543c8c0b234021907240302c1c41035048000a0481043c400c403081d0280079460051610380c80c00d211840c208000303001070040c0c1c40380302e094011000815805155080c443c103030180040c15070440d160b5140382030642a440480c00800814820781c1d000902042d15810313094251545403041c0440385028640a070000d511802210007540b04135202510203210420041c00c0e48a4078001501101e40352648040564006810480301c2c140144104a440c070980c1c401c1d0780388906ca925000881c0c440311304041d1a1881a040104050b00c00010003084a0300c15034005ca040300d40038110501000d40c0c50700115407c00c1c00d0300400d460440600c00411141181d0303c00800c030290400150b40c0100071151403441100e800208107425105102d040244184400780101e501030750307848a064180300d41c140001e4a81c810141d4070781c115016000e200d000c2c030410b45d02804a010019000044168403480c001e5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 321833839 1250 321832589 321832601
    0x61a0903280203060f07140904140a1e09170307050d050103061406030d022104080106030c060207060915050315030a240209090f04080c16080c0402070503070f150906 73
    0x2030302034890b400110351210b500d5a9110302c61b03500f90f85c400c1c40ba441d02850b00480c0e9072000424647c13058684550100c11034902c45040d00a03083c4003800940702010b91060801d48401081c40c3d00c0c128680040701000c60061500e004802c01600b070090340d66910014141c4090287d05d00e800842e074500b90000c0304100180d48503000344444d1180300354040d03a42000305603442da0707140007000041e00448100130344a4646407000e03442e181050195030a082d00e41205d03508442c40c640c01600d2340d100040342008490780503c0240007030501031409020356800d041086801c00510b68207001040000000100ba142401c407401c0341c0b03064000c003910b006005900b040e01403100c9824518400faa00880c4001540072103200321980e44102406080440d41c4181003445281d500078030070340326200208000400100e060028442d8442c0b0359441d04c0d440d0341001507103403424039403400c400e00462040111030040b8400005541c5915804550340d86c07529510301d06200b03100c68800583c0c0403503052000d40b0341040085d40201c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 321835089 1250 321833839 321833843
    0xc080f0c09010906030f0609020411070f020a050102030a02150a090614040201030b09090a08030915100f0e010b0d0b010c05060c21070c02010f0c0b0f04031101061a090328 75
    0x30307907890762150b550f003084600c00d1200501404a110410340020101d420140030a0700044c000680b00040e41c216614541c41700000f20340b0080c4d00380c0310300c0451821484602c05800280b009504000551501a5031080b480e641000780c82c0401c070000d0002481074101c21041680b010044c81168401c44440ea060030090720200c0c01b007400e1a20980060611058642c86240c58800400a200b9291541e18903035001070220740041c001c0c40e10605101320a0b4520701c1c000d490301603800c0c0100346001205502e10740c007908904501c01104004005085200040d00c045120340480000c0c4013500c1c2c40142e9006015103c000e0450007031004120b5a0003078a8054003034401e4074104500d12180900708481c594004445090104503071000d071a016500c40d500070010800a0f04000341440300a84031407001c090102d1b00800343d00c034044100410540e1040b080404404000d000303100c200e04108408004924150b0509800500441e40d103d160f5810005002c6220700941c0e222640e484150501c83d11000e22201 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 321836339 1250 321835089 321835099
    0xf05031b0114070f0f0203040905010b2a0604030e2404080c041401030321050a050115080402010c15061d0103020a050111280209090c010f1701120c080f0c 68
    0x2c0c0c0e000c0080c210003a140714003003075030380e60304004091642a900ea00c0c039551703070204511080c07101041c00c40b068410f040c00b810007580b019031a050f03c0750380c0700d00000d0b010703c80316031000540300d42d010102d500041194000c1c0d4142415445d04a040700450b2100541e01d110325041030803a94414a0581007400a106a4032104151010725072040244001e8401038041000f02140c0000100301003845400c40d0f030a10080b160301028041050040c4405a03441601c19440d11540c82d00100440056400c0d404554100c508100e101460f1613000070b4204c2d0701001d00034002c02c01201040560025030f922030006000c1c004500c0d11108010070300003103009003d0000705c3c012450400c005c0b03043e41c0034210a50040d28500010714006041000c80340e04144107001080d01c000c4445440001039455840c0144203c03412001040d0442039540014610041458500c061000321010b030882000b00c07401042c1910200410800d0805551400604445490f808100d035806003500e06a043c46002c1003440100000301c903 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 321837589 1250 321836339 321836351
    0xb0411100207050315090307080f0a030b01080c0a0305041e030c05150f010b0a0e0d03031a0415090504021305040803010906080304140f0102010b10051b0303070c020d0f05031b01 78
    0x100680c2da40c0040c2c0501a4107a005600d0040b4070150615606d034010800c2e800c0e03e05100303581d03903005600c0d013010101e80b1004802003080440543d251184800150003442c1512480c2042019035000b07220760060001095141d00c0050700340300c44080c4440d402c4903400303000c03504030b1050300f002491a100140c04991038040c2c0942c1b4200044901d110502401c030340c00c1c094583d64038101000c50a50b1003449020140075205030141019a1542030742d4000038080c0d00c0c003180012416210420700280c12010768811071900c1d400001102c04035801d08151030810900103040d444a000091200801611002a4904000c00c0004101c8101301444c103d41520900707000d0151034000540e1a07001e940242011408041449403403450000c9035440e43c41e60600000564030515404070340440c0607021881c001c070310b000800544500205200725402c1c111800a5421410f05807001006e1510103100640f00d0081d40341c090b414040c19040c180d0040b503026040ba40c2e106001001866810100784420595520b011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 321838839 1250 321837589 321837619
    0xd0b03071401021507020a120f0e0d0506010b0a1b08070210030203060f15122e0b0702010c020a12150605031504290c0706060f031505060105070b0411 66
    0x4146071104074816001380c04510720f40040794441c0725006048408512800701c001c404100490280440c07045140da540c03500000300c043c06080742c410b8030020740c01100c0015031440480d80106200d03041d00d0800d030b01e481d60b40f42e410f1070854000b01001c810107450f15001e40d0110400180c00020080c0b07603c290f0711040b4041c00740308185e0480c042201c44940003400141030321280d1030405803901300d90500c81807036402c01204d000404043d1b88100d8030081c03100c080070002c400010100c100c81596084a200d201440340c00c1c015840142c4c020820004d05008450000c0c108550b20704c01000c0148c1750f00c0783e00c40714800040c10020706400c882141207101a01c2d0402c013140307a0801040e1400c005009a0240070343d0748071035584000440c2800c9401e418602d03440001d041c2c0300e240b40e001900031800c1050300f0391201000d08051044407a80e500113401000120000c000207125100703c0c00810800c001d00080c00d940c2d0b0700060b1540e12400b540105031440c0401004200025034243d40302e00d82c426107072925201555 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 321840089 1250 321838839 321838859
    0x60402090f240103021b011505030f0304050d020f0907030501050405100b03040b04060b120c120c130c09030b0403030e0606030601050d0803130512030916060c0b13080d0b0307 77
    0x191100715030321001a908901a04a004802c0e91114042c50014908004502e0710003419210503d8030b9084e1751180c0ca00d454a400c1249000e01800c0100c019102c02480c400300540d6030302c03a91103440e0181c07801809590135990340082100c2100c0c400303090400c4074904450018000e001c24001e00340b02e14a0b00d00402c00c50845c0341059801d40b54000401469902c66450304054040000c00440d2003503180d020307494094907110f01c07888407402102c00604000d40c00a041000d4004000e561107404d501c6000b034602f10386c6d29940400030240c0c9080000450840c400422203520481c2d40010384038618580512007090341c50361110507101c0003082a5542d903241c940816440700030078810340c0d03481009451800041080c2800650300440800708010b0040480e0343c070304e410710207140d010804985000c0108050030006003c1c4009418900b1040c2c0b100d00d00301800a0004211035102420000d42c43c000185803610080c01c02101981011507240c40d54460314410019000010003d4043d00640d04006071001d1a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 321841339 1250 321840089 321840091
    0xe0f030a050c0f12220b0c0c011d0f01051e16062a03020f07050d08040c1409040b04031803061d0307020d0b07050f07060504060e0319050a02030705030408060402090f 73
    0x3d41d01c40e1504c0d0484440078000c1072036204140700c05c1c801074104005445944c0100404800340403070040c3c110701a00300c0001d80220101103c006141c2102040c00c22141d0b50020102038070542402c00b281c03500074011403024071a80041c1c040f10007000028042490404c1c1c8209e08110601c208000c0c03190324a41d8803641142281c05c601c1c0030306610a081d1442184d1300a801a08084030782101b01c6003004010345602d03261160040c2c4c400049030f407040900040c08000613070b5101500c000c181410200382030b6808504034010041025051102d40c10100c0c040600c1104094901d101104d400300c0060349034104840140102001c8000244001e043c940529002109a440603a00100003084014481e02c0d5464403110080c0804104041040704000f03078a041030150400c6401200005850310f058a09081100c4074102140c034035510074003040302410403a00240d40b400440b80b415607164000540240c2c50f5001c2c03d84010110b01000c1400f2030301303900011700c0f584158001c8406200c0c50700d4000041c1c01400d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 321842589 1250 321841339 321841363
    0xe01080727090b010333022d030f01080f0d050d0b0907020d32070309050a030818011134080307170a02030711060d0204090b01030b06130303030e0f030a050c0f 70
    0x211042030300d00e1b1800650140a00c030b00c14400050314a100c510a154070402c800d00310300400d66010042c009082e4001c081a4058180240140081021025110b654800400102c410408001010b42c0a4245a0080e078409000030f09468924144801c0c081d445051021000f00000d020300c80007150071441d070524040f0210441c02e450300c131108020006685600030b035410340030301414120004050719000a41c83c02035000750302c11504d035458011065a0b40c942180c0203410403c0c0c04801000010001c101c445058802d80c0014007203006511640403144a0340d51543c40aa480380300c001210403004c802007492170721a8142021540c8004000380303c500a100c072510045c1d00c20304c40040040c50621284502c0313000249078909002240d80c0040c16a40640c00268003262a020703001e00c2e03560180580308802104443c85401e226002110340603008840c4030207400c05840e4041e00000003014400365103812240e8040d65030b02c440050000c0d0407540200e040703144038450300c0141002c9450100f8203410f030003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 321843839 1250 321842589 321842663
    0xa0b090102010c0f090b03180601120302160f06050306030f1e100c090b0703050c0105010b0c010c030903080615040e04051e070602030a1101020c01091101090e01080727090b0103 78
    0x1400c01c0150f8820347c00041c40c03d180308d13000d0f14140c44000f8040098a00030034005110f605030a015250081c00e2403210740f40c1800c064041e41041c096000200c0011003550400e141c030580b240d50343c40c002494007601100c81c10550181c019503000b00b81805416503c41c52402d0101c1d103500c2088001c88045505007405180002c80704c96060011049200050024a0280c074245007459000d202241c2126420fa000d15007080000a4101c000030b020b0140c1d5144540c181000c01c6030003a1034038040c048030f4004021038819103480313000c1030081c6440c1c0251409040b10142200701850b00d40b603e01d03964030400d03400394134082c00e54000f21003110f00080c200c001e45034243c4c069030804410038002e4411820416481025540a015400000fa001d01c07454140c280200b84580c150400f038000500b200541d034019a10302020540140081d50b000541e407011201994034a1080040f0a07101a00c03402c6401d040d1450b05007080100418030281c3e410b214142e901a0a43c6600000008040860b219034003144021f00d07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 321845089 1250 321843839 321843857
    0x5070614061e060a2006091606030e06071110020f03090c0d0510050411061c0e0c1e0427050705120607080411040f050f130305040902090f0a0b090102010c0f 69
    0xc0348512070a21790400f009000310507203c001d8629906040f012620f014140e0b0007402500c0c2d49100f4100d03000d004204d1400c003080802d2001d1045512641c0041c0780c401131112465803040c412004210034130300c3c0b10595404540310466240c08031142e50003070741c01e00c169210305d8216851900e08500b44c0682154090b009220703220607010401c0240a00600554030000100512100342d2242e4004040804540d01001a80b04000c0070302000c5445420400405074024600075246840d600180229807810380c101002161902000601422141c42d0041d408d6080114000d1603c2c9181c00ca18240307441074040d1215030f03807184280310b00741d000d500300f403a2968410004070f06458092448241c00038000e00c070100b40d403c1120701050546500d4001d10707002c56074a8003000800c0108a2315140c009510405c5421a601c06071002006401680a42c400c0c075a80059103010542e50034940708203a000c0a00b80817101a40c1e40c41141c0c10360060003036103002d5400c101620705c900d80b260304407101c00b22554945000b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 321846339 1250 321845089 321845107
    0x50301051918080a020f060a0b01020c04020c1c21050c0403080a032c06011a0715020d06030b010801140103240207050303040c080f030c0c010f05070614061e06 70
    0x80c2080c4603181186000480b110700100301c0705001400c001340140c00030140035401c84101407500398020003510303240d0700d0301d600c96039180c5e4003040c40408680300f102e02688460b502d0074542d0421503403541405050b51003031031040d1940e40010074000c503036039000416481220a8400381c0140c64040714001d840060070441440040d491306c014040d0b03c3e84034a0002030800c7c50005c1c46010180c000c08141c00c0840d40103810800150402541340500412540c0805090360207444c00542d008000c1c00900c0070900f49580010140c566043daa0051180300702809415946e0400ca0f00c41502030040c00450b50a02d01000400586ca0180a040340e40c0100d030003c002110900c1d4065040703000b0907000380d880e000c1182e030011400810207103004a00640c001c4188511300120310380780074080414030841c0d41003441094240301021804000c1000d00303017400000c00f80c0400f8100c0e114418004010602c503c1e010008800c042e44000f02032146d02c00382e504008100d159018500d10b012000c9255038003000030009240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 321847589 1250 321846339 321846341
    0x5090303040611101d161d072a06060b03161202040504090501061d0c04090902060d2c0109020906240c010b04051e061207170601050a0503010519 64
    0x1d032403c0c580c000e64016140201a0130b0030340303030514160080d50f8550003920790f0043d024409003650710310580040607038a2814061044d44403446100d940100e60741e90000302e849001c3c0b14600400c44a2813184080c3c1e44c0c585040d0301e850300a510054a1682c2340c4807000c64810140c4048902030003864014a03560520341c0030403030f10529244141e05001c0e40a002c00100c2e42c8560103400d500c54170030f00000c0b410714204041f5803130a180d040c004107a944074540910021410100032501550740c550302c0850340c0c0403140003141c05481148140100280782026100240129400240c2105800120021240325460201e030907160740032001303548100c421007c1421803034500201c854594041c3c60700c4210501c800b0541d41d458025545410181c0d4503000d2214441c0b0b0180b048030740c4282c071307043c0015114040f000007241003040144500c0c00f40f850b4900c2d0400d0078400700004001002ca9005d144080c940d0302400544621f400e1055501415030030402268914041c0165449000951600f004115050705d03164 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 321848839 1250 321847589 321847607
    0x2d1c090f0e2a1309050c0703050304060b240d1b1d0301090204020f0a03060e1e040311061003150e031e090d061a0f150a030204080105010f15050903030406 68
    0x1201c51242c0d40c0c003251003840e410141c80ca048100641c0c5494a1074007440300280c807001003826130581c1c42040b0b0b510009400c0010f40c0e400c242c000d02c00180380c42050002c1400c210080d103034454a03000d2152481071214071800181603015156400344942d0000c0d0340e8500c804001e2007088004103541e2035000400032842d061802c40441c001380086820303d03076074000c20100d0b4014820402980c0f070008803100c00c04d41500a03c00240000c2003850302c5840c2840c0303012a0703010031000003201a09000081403d1502c548216034207030403100305540081c100300000c44840c010500c81100e01c658080304000f1504068452490b00044800242d80340191180404100f602034009041030810309001110b00c5850b00303c14000228440c50b000560000326809000d0312500c0601490301c6150403c1d40e66403c1c0d142c40d085a2180318003440d280c1c0c2c894076006400e9000c0c0c091074100f40c0803036203000c0000030600d8031402001d04484402c0c10171030006c400d8420458031807080d55012a0558010081002004e104858070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 321850089 1250 321848839 321848881
    0x1104110f090315010b0c070e04030207140409061a030c010e030312060102030f0a02010507200705010e13020d0f050907060c080a0c120905010f0201020406022d1c090f0e 74
    0x2a45121010f4110300c80b43d030200381c00c5038503120408182c40c040c03010704000080140940550250f01d23441c050382d00039a950454080c1e5100406810100922926950044944181d20042c01d1210000c20b1040c0b1107203240300200c1e107100341b00e0710304940b00c0365005510364013030f800303000c1c000d18603010303000741c0010f0343c0000504040d045100030000f0031510300c3c101024010f04d5145500100d07480c00e14080c002c00b0043c50708240201c0503441006401c031040c000480b030007212000c0c2001510200b0110004034052002e092a0807060300000e02c00e51070781c1d80c40d8400148032528080070051602d41d460450307a04d10060058002251449455001041040d0b01034115200d032442c01c08203030380075555846608180f08070030700702042610030305001941e0404070181e407001c100c0c4000c6080c41c0c034082c1d0081d655035480c0c0142003a40d10a550301d129180202920036244450101201c003030502011105021070300100d11030307000802030440414450010f591074030842e001c000c004401910b840c65994010024000c403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 321851339 1250 321850089 321850093
    0x12070903120503073e030d090b06031b030604080d0b0a090c141305041107060212040308010905070503040201030216050f030901030e19200402040b04031104110f0903 73
    0x40000080c0305402100c4840c1c00c1e81c0d85040d120304180034050040c00519060300d400d518040841040c0380400c0701c01441e82958524a00710f03032100018290f06621416501416180c20082c00000b8009400c80e0340b03014801c2a01102e004050b004174210a600310603e4a1307500d0b411040128002c900c039100070706440c01325810000356507040e950014440708402d03031002d16059200c0f030340800d58980210302c3c0341c07401040c060a50714040c401038001c1a404450300401d445260707941c0c001e220040c1403d0540342907941c0480210742e81c0c1903c8020b0840c4070000c803803c03000030f02507000114032041940a42400ba003825200c460035070f180c40e40154040c0d001603451441400c104a04440400d0040081c102c01410742c4000e10b070750b41d074084001002d95107100158001988410140c11140c91301c200c800f010036422841140c101e083e0085c03512202206500450b51050000c5030100c0c1c2241c03203000410460b41f0555090001d01e46401c01c0c442034926004011300d01420030b01541d2030a0580e1070050200610043c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 321852589 1250 321851339 321851357
    0x207170304271e0f05071b0f05011518060302060f1c0f020a02010b040204050d0f020612161704050c0405060a0906090e0f15070518120c010f0c081207 66
    0xe4100b0858010148280100300c0a041c03038020581d8034450150003414074030040c0954941440054442810250030310041c00742555030320188503072844148844e0742c2c080000d1000000302148284078800900800710720401050f003444580047e03100700300440e90b02078925401c3c0200c1c2d444001c56608024181490080c1c0c3e0440d0700040407040c410504100441c2c0b400685a20035800c00908685102d00002d02441c810002031140340c4d1081c0401c414680d014100300000500381c40802d00a018501115070f24244d601c050000c850800c0202c0d00040c400c80e610480c0003000070307420254900055a02505c103800950a000d91820305800150348201c0140c08032121580d02c1000d00221042c9502c603180c1c441c0d03100741e40400000d0900101c50750310700480041181813001c1840c200040c0002d4184000d01c640025100c2040c0079414580c044160000c0c2241c000301c0d00310f90184d45450038505450300188950a841d001c0c00e001c0c60020001a4114188904040b1100000c0b112050003034005000c0c00b20100b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 321853839 1250 321852589 321852659
    0x20402120115110304050f0411040303030504050d03060311100e1201051014090a1509060806100f080c06070f0203030a1e05210a06080613030207170304 67
    0x200040c6105012921038410359031609840c440402500355400c0c042010281000e42e0307150000090340c0a44d1002c030340ca45002000400001e0043c10314804e080003051000c1000818150075502c200e22841c018070940300d0054a034802201121481d00006107051a00d000a19850408446046540b1900c0c2171002800b43c81c01c00007244030301222140034a41e0b4555080040d07140e404a00c2c0341c010305601e5002850390482c4e00c0045d0f595840281110a4242d46085184e0100051143c540040448050810500c1e0321005603984510049500c51860b0203481c10019072403a800d084481140c00c1d610203042c51203c2c04c5d0400401d40d101c040d064440c40ea40405120143c0d8007407000b81030100c0340c0c0d140d0390380295a2192114121070300c0d411600522400f40002c420028860060a8000354a4440c0c80340c5580c0e8000e0040003083d082e0000d03002d9220701d0301005000c40340d650000701c1c2c0b00d02079000c90b80c580d580c1d48020b00e86121100d000074049e400621081181120050081c800c0710085e00465130025044 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 321855089 1250 321853839 321853841
    0x70605040212101a1e061602090a0f1424040f0e010203070f080601090e0c0c0601140117220c1a130602061e1e0408090f06070b0408160204 61
    0x80419002c2c0f95101104c0702c1109202c0c1d038541031004203513008504420102103c0b8201c500e0300341100d0082c4d1000402c403042c0005100c5071100d0310341c0144146c0e0942801d000d03c80040c00181d503030300a00c0d40782c07807408038005480f42c5d049031103100007001d481004180b01929207400001c50003441e80080e11900c0f00c05600e400c07805183c1d00c1c10084000181c5034038001000600c1032080c0308428091040c0d840c1071003526640009008181c0b0581060310842d9160841075044a1064641020281c047e050010940b01e6845120b61011a026655201b040207595400021084103507104400ea41c03105005020480404182c0028a4010440450007a075143c10040e00710300290a00b81c0000d00020f000d890103024812128064000c91004001c540303060080105030010f80140b55811000c000001b074210441504101107030b42a00e01c2d101203a090902d0301d9502e40d044000e4503882880002c8007c2002c0c2030000c16204056044480740f41243c80c1c80d19082035683c0030039220001060b0380b04030071000da112 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 321856339 1250 321855089 321855103
    0x13150f0e060a0b0a05122107020303120a111602100302041e050117281e060806070305041212060e0903120105120d0e03190f030f0201020a05070605040212 68
    0x144040816680f50441c10030411680b41e0304014401e070900c810380003d801000030070718101c9140050440146070a00087c0d604c40c0075040009500d0310001507442414151804031702d000b11000e1b6418800b0320000d0728020511b0003000341880740c2d001e460342807401505c0c0a10070344008090500f401858141c8880902114a80c040000e003000040864104080d5034040000b0080f06c07010069205d250414040c06080c000d120f01c03c140040e202c2c2900f0440302244e6034498284d00b0944401c01861440040e030703034000351010344501c05680c0034810000b044a802409076078451680202800d113a442110340650304040c6e000314884c3d0441c0c0d222404191001c49503502409881040025512005d128150314000703403058001c40e0003410200207411201c00001840314000d0170b02e081203c02c0908000200e441d15440540c03d1900e124400115002d01c02d4030317a4179a04c65402680c1d0251400032004040e400c1c1d01c40c80307446d0000680100000b0740440c6050b4000c5812074030040468120b804681c0c1c030360b840c10301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 321857589 1250 321856339 321856351
    0x90e210d050f091203010302010e010c06060e0a06140d05370b04150c020c01050c0c1504050307060302031317120907080106060206061509031002040902030f13150f0e06 74
    0x80d1401d211036104100140d40b00c0415201504c1d24543c11640020001d00d80c44071150305003c1c42c140520208203990b040b01c07010700206c41a5820070302d030070082080905994030420135030b0028005004183c1c10030416400d0101d804c0030080c5485049110507002c6c46142d039025076800e55801d42c00700e5217000410301e04d0300e41d140542c0321202c003414035052101c2505440300304100054507100e0b90221551300812480b1070a5002d080030303a200c0030b42c610304908141c15010303417550040b800c04501002d4070fa001c0141c0b0540300d040e82150745150720703000107408912080d5a481c0e0390311000c0d402140000c81d0700c0d84fc600446851180c5a05001c25810040101d4005403a40702641d0401c92092122075024442c0c0e80051040340b0052125080290224498104000e81d00018103c0001d18644540703081010412107090750000315a40d43c0c1e9000650025001a692a0760965584000c90084108041e804030016040b03000341100441e40c9039240300401c110f4141e29802d6883d11078440d4101414080319100310 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 321858839 1250 321857589 321857611
    0x1050702012c0601030303050a02121e0903030c03060402070f020616060c0302041a0a21090b0123010c060b210708121602010c121701090e210d05 64
    0x10303180d040e0120072044091800c54882d103454080941010002071060440780c040c00d001034a600c0f01d04c0000083d2003079101c01c1c849000000d091104250413210b03808462074003020640c80c16100d503680c154507840140c564070035800040c4045901031a0540c001c00030184a0402070b00c80c45a60760106516403c5071110f1f0319035851605105c024882c56014040c66401113184c110303c0e10b420207156407846c680d45442010421000b06007000b000d4000c0105510102d80c400c8185a98000d0429950181c0049603040340d00314204000003a0450021700c03c1c40000c09a102d80b415010b21802c011500903805003800c3d0742042e107402d001402c03612400f4119407101c3c00e00744082814a021203100f480c1203c7da60080c003160303200060400500c2418410b46510200035040d9982e100f0681c00121518814044050074803d2100d100100540c0c100403581301440c50383c00d030a40783e0707a40e07400010700721a40f01068089170341150a440c104180c40440d0507038030614140c5614109849280000c00300da6017110080282 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 321860089 1250 321858839 321858851
    0xb010b0703020c030105010503120d021608071e02090601081e090a0b0114091902070b100303110a030503011406190206040308010b03010b0a030507030b040e06010510020105090d08060a080105070201 87
    0x701d941448481c02106058000340015454400070a665040784260b40c400341380042007080a001d5070350100c40f212010144505542030940c20f000d15260720031402262034030b640c030803500114040480354803030407500245004040d44d10100150b41084004042031000d09080030140c01c2440c1c00f4008a005001c44c03002040c403480c841ca0070110945c0d042c0c100c07076400d03515030040310b009903941089035510131811000c90240c0c00038003610304084d00a00b40001c010b15240010007583c40300c04006901200e00075a900c101d16200440c6140d00c9100700c0401a002400400052110044c0d040c0285924000500814541640f210b8121891181c0124200060700804140024540c0c00600c960260550080710761079949800700080c2640310f10300c0000d00741901e0b0740008841324002d91001c221028040c0082c442503810103001500e80300c09000d003074460304010100c016018030500c01c6a2264103001d0040480845564040d980d44c1d40060401d0780c06801100040b815002c2030040d98020000c540000c505 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 321861339 1250 321860089 321860093
    0x12061b020d0306171e1603080306040f0b01020d030209030a0b100609051002030405010f03020409050f10060314061513080c1e0d020d0c0503010207030503090f07030c0e060d0b010b07 80
    0x545515030312400550b82900101c2184141c04510300e0a0038603500c05e02d05001d0540c103481400c100c04544082c1152603946d800105001910740190321607042120300300421061600814120382c4030090035030059016011007145c0c0c5001c2c6c1c1c01800440e10040c119450301c0c504d90380303200c019902240c00400306049101d00708041c5400c00414030240078201c404c1c027038410554100039a2801188500360401c140b01040004840c040c1d811280500b1024034288420315002d000c209103e13805940303125600108240002d0341c2442807141c904540d98401034440b0300d8454800b003044800d041100d40c2d90040d82000765196101c0030001060007018110003400913000410100014071403d9659154404004a441000c0e9038803c409140e4241d81150180107c246906183c66440901d80181d40c040d0f100003202010b040c0c00c003010b1480742a99604880850310000c1d01192101e41d10f200c000c018415030f2600303002820202c43e425500071f5000d000d03802030001c6e644607014102020303403100399980000120182 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 321862589 1250 321861339 321861341
    0xc011a09060a08150403090e0703020a090f0f0909170a1d0d02010c15090615050406090204080d050703050c100e0f0d021f0b03030309061f0f12061b020d03 68
    0x41d0049048a4001c050362401440c2a00e50510060075090200340d0000103042500858004025100c002c2c0810503600e401d42000d0000c0d80b088001c00301003404480000b4111744400305000c207907040440b4001130503140401200c083c2601d181c04071540b450701c07502d00c810750700c5580c003030701c402c226556503640342c082c0c4c2849480e19a00410036207805501c001d9401740141c1d030800c0100008552000b09240000381c0c821512000f4816070900824050812203000c0c84402800c2e218405e80f042214200402c50740d0f021b00504920451046e44e0141d0054075078090071600138406030800b20301a00381246480790480c411814031a0415001030055a2129101d401079030400418124802d580000c00300211001000b03590f815402c124246040c0303401d0b130700300e20407083c94008080d200c0e00542181d8880c2024004152501e8013160840b41d0304030680e603880c50180c88458810212404403000c4000c1600340306030713a154510444800e41c1c82588656100840c4905001004c10740615640a880c80c4141e60714010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 321863839 1250 321862589 321862591
    0x507030605120c060f09120a050102030a060602190204090201260a060501020d09150203070b090606010e0d110f0604051c030e042c0a12020a030e0603010602030a080402060c011a09 79
    0x15080e07880b40d0312543c01a20f40104036010051006412070b15a040c2c1800240c911480c112000d00c40d0142050f040100301c07054000e1405840081024841651101d400300e80d58410826110007111150550b0000360510b54004c036401070041c034000f1401400300e014107400000c1d4180712644500d5110402861590520428000d4030007480a012003400c854401000c01c00140142da601e0b00c40c920301940c03558000c00840702d96941c0041c0602d014500003410f19160b0305d08841a0f03011030003440401038107140c23019510844a1f407105902e50305028509c148443c1d840c40c80d0701603410030380820010800d55240380c3c1c1c003c0000c10040140c0181005460002d1100c0d0300c0c40d5500d40650304024108860817440032030f8031020070001e0351344140354001c10ba8240c070f00000180c010f0088217030940041255036001c030b151181c5d5402a11103815031980141400131600c02481400c1c0160030500c0b43c6401c0c188201c08681e007160004241d1420b01700441e01c02401c40b1121b2503030030300d16603169202000302d0800450903 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 321865089 1250 321863839 321863869
    0x703020111120f09071503050108120301060801033509040f060f05060708070602040f0602070501021614011112120f161b05070308120f24040f0507030605 68
    0x9a00b00390b10a561240a0039002d428000805a002c0005031200c2042042e00020301c04810118804800c01c40042c2c014031081c01032050314000d40c0b4007240f45120312411a4121002ca0340c0c1c001842c0e20319114072002c40d0018442030340310240b80341c1482e500c1c07140302800301c0308400030041079546d41d6603141040304a41c2003d0030980d40c3c0341007000c20070003070046210010840b0340c159506955000f55240205480c1301c0c103031009260910100f000314840d05000b50342416200b29400703c0f400f1a4540005a0765054549150311007590249028490032007001c0e0001a561010304004074000d0741c80d2005400c05082e44110742c1c49003000300c0c400302c00c400442c04a6030001c840c95612486030502c10a01405c44c03000380c5c0300c9002d02900c408480c00e590100031410020710340080c10b0741c010a07100c0c07400b05416032050710200c4841c2640300118005000f55040140074000c500031000000065503038015081d1040c0b58000d900a40d202e0050350f081e24a40141807007011240e900161044c2081e0410030300c001ea26080c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 321866339 1250 321865089 321865121
    0x3090f0a150b030a02120d021902090a0e0307141b0103020f070f03050c1005011a16020f04060f0905160c0804050f06210906011d0f070e0a080307030201 67
    0x840101c0c400c0780c8001105030101001042094011003c64900040154001d4008038040d003514980c0101003110a070041c213035425590560315011031030321100c030b0000000c1c3d131099008010442c0264554004810b110000c2c0561741441c00316220701c072244a100391140669000f240e40740f0392010074051288491482420214100310221a074050300340181c000082c00c072105071a40000b494041e509840c0008603000898400361907111600010300f50038801c101c00c010802103814800140c2074151899484021100d5061020603000c00010080040e420340d002982c0312404100104580107190150103011004962410107030210038202c6048142c060400c0742d881c1020780081c0303200003150102c950881e44210300003070200000f904c5100e0060b2104060a182c00700070115070700880e202c3d1282c89110184d8400e60307642c5005002c284204410038180742e005070001031030076910340101900403820303142c040000b070210008038503c500f09070010301c800d60000c03c604007056424055403030003240b5521 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 321867589 1250 321866339 321866353
    0x1103011803020318150f0d0f0e030909060f0a140a0504230a110a081005030f07050d0c030c030c030611090108060d17130306050c0309030a1d060d0203090f 68
    0x14025220f00031300d41e0502c1c0a60b40b1a06a441556400d444508040c4c528403035995a5400500300c40e00951141916500c45400c028207654034110522808201100800180d441d26580808010800c81c0080c82290300000c801c0e87d000d1583c903808918405480242c20040203203602e10b00f0006d5080e503c5d0300680c4240d0400100051030003107109801003001042903080e466031500c030190005400e803040c0504540c1d001040c0341c240b6a43c40300919000300c508188100d846038a41041c551030315a641c1441c3e2a940c4102010011410f210a00d200d540d13000b800d1422090b922070740c030382d810200d5130f52007522070104024051043c4121481810b0b600703c2c00c0c0c19214074050742040060522400107103014410001903a02c0300900c0301e403a200740c100480e46105e0f1030707481291500391400005135001c15a2418608030004260442100440f806101e0440080d0704001ca860400c0b074401d410800014460316841151010030b0712044c01a0034170800c1d454025880e45010507281e0310340291901c01c4561a44030740 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 321868839 1250 321867589 321867593
    0x1006080c07020102070e09100507080609100b031504090512030f0a1a060a11010f0c0e0301110706020c070b0723010c0f05130803031806060108150603040f0602030411030118 76
    0x5d00004455405040e0b1500c1d54400d8950740c00c104c2c40d030444036055400d0234100301d40d86500c404a02d100350300c116901c2d2925240d030108207425402d20302581204440030008501c1402c1001e01030465004020000304040e41141d85050401002e24114159503201100f4402c12450700291950b1100d0380c440100488078242d0721030070b405140d501106000b02000941c80c020207103d0240ca0000648020090080f0f040400d800c10040c1144126980000d85084140c9554901802015528106042804c1c201809030b200e0030000d50040f2002c100320320450000180044e0030001404469009440c540319420032405e224140d03030140403280899034074040110951340d4015800000203541450102d49600b44010b0003540340c039950b0404000d510001c410070201e103120024680c030031040c802c141d81c43da0b114040191032080f003d503040004241c144d207501c0194200300020b150b010380521041c0707110903030700c3e2603100490b40700761000e0b2540407030040030300300c681003d004044030400301c0406015040c0c860703 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 321870089 1250 321868839 321868843
    0x10501170610030209040c02071703070503040e0901090f0c0915350118062a0e041806090c0503061512210a110105010506040902070510051006080c07020102 69
    0x24003451049070b00d0500c0600310351180e8150f801103003004e882080b0068500c0d030040c1d40c40405208540c02262458001d2824003008426640d040303030703c034004508043c108190a018001c00034048030f400d641e52038804020920134207056078141e00802524002d14100791010040d01c6602c01d40c0e449403110314508024003800840310000e44200070111981c0c1c64040012002080c181244801c090741c20a9114031590210400c2d0384102807140304204103045104040112070702c2080910079241c4048001c0c01100340c003c500080a185004000083d401c281c400c402c40d00d00441c4005440556855542000704851a043c80700a418110000c00c21460150004119150741021150082c1c0c400300c0c2c0c3d805030000801c0340d03001c140801001001da4040b1045202c815410030885100058104400c000d036602040c0302e035505980000c0c103a20b1815013013400707030f90195010a0301151725204400e040709040000748501c0307002d118950115100c00c3d1030b1010042c17034030034050325078048410100001c00040c0e1300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 321871339 1250 321870089 321870091
    0xc06160906050310080d020102091c020d02010f030908040e090f1203070507020f0a0303020f070608040c03061109041e0c14090d03110d05041d0405060a050a060302180f01050117 78
    0x80d03403512590f0f80d9500e180801680d119640140c0a900c070b800c805440c020703019005821200c1040d100c03030720700c0038403041460076003410b410002c0e4011400b82c07a0800994416410184084d426080200304030905540e80c0440398030651210010b4102d000510550349018803641e1000310b5000006d2800000c10040304c0360700d2001822102c00d000001907000d0440d25244e18514490000800d040d40d000c2c1d03079041c0691103030401607007400301e401900d10109401e409124407038041c0341c0001c0c1d8401624190360b40c550040002109000d1150b00501240b001039449014208009843c990046040c4000c41503090584410080d141c0034401d0b548001495468000306036884207000312050300b102c040f5400d05460345207841000041501900e1100c02c400c5801200400446600c402c900441d9140001c0040c0f0080c0c040d240100103801c90360115141b82c100f40c0009810420020000a00f1a0399500046064040e01a11050b801003101040703070340003002e802280103081c2030a003695104081408074803aa10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 321872589 1250 321871339 321871349
    0x3090a120f090902031e070201110418050108030c070302100512040f0312020a1e230702090f07020606040b0f0a031a07080c0708030c0d0e0a061a0d0204050612120c061609 75
    0xc06d0001645243c401d400403842042c0b11b00740302d9940da480e440705180c2c1d0002404018401800c160000480301d900004440510702840d010740101d9040d90300308424041210a0b50b4208030042c0090108440d064042500036842501c85154802e400c2c075004c0e05804040d5150a41a4030500c00800e0040c0c000400c49510680595401c2c9400b01100080d51812108080c4201711916466401c1c0e4884203800240007240c000c41d00000640e513198030003081240125181801a00301030081040713400c0541145001c041c0090244404405480100385c48020681c4160307038030044240c021111184010505802583c03e00c1e100c0f130a03141c044a4000103104005004141c02800000127045044100c169084c54045030028440c04108002c810382d2025070007002c0e19514a003100015541182c8445414004401341070b41d6006841c036000c00005020043c0b80340d400071019044042000800e20009180c418018122600d4880366aa09031074030b00001c0c0100380000343d1b450351003030880d084000720003103035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 321873839 1250 321872589 321872641
    0x603010e0d0516050303010b0417071511330a050c040e0a0608030a120c0e0a14010903150204150203090105040308280207050102120909070503090a120f09090203 71
    0x79444052061020043c1c50003e01a40008000841c1101e0200c0c010000ca48038480d020703914410300001c0c2034a582d0f080c8501541100c51004501130140218807024000d080d544c02d841c0ba8010940d00785d080ca40711515a0075031000308048240501d6010048650403000000042140345804c03545a0040c1c840d80c000d00644074501c0c8001540d086980c0c001202030030f6948162a10b4612400001d0180c48203108000345040c24107810b02c08041c41180b10b12141d03100208510201840c1566420f9080e088444140c10024903980103c00f0501d80c07001c03000c42c038880c0480160796a01d044071885442c250450324104540040042d201c21b81e9020060b10107490b017082c80140d903460460910320405a0580302884c00103500407051811980101d9420110348003078080e01e0030540364030f07480710552140c10302c511780c0b005465000c41d82c050321400c0a140d05c01c8500e401c48002c0d144503100e400d51a0143c8903120001407801c425100c54950007000c6000501030801c0550a6040141a6650002030789001030820 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 321875089 1250 321873839 321873847
    0xe0402040e07080a0305030610030c0f110102040504020f0702030c100e0f0f12010f050709032a0b0f07050d05090321040b040803090307060224040303110307170603010e0d05 76
    0x4020a0145030000e00f41c400407100760030316038503002c1c0850300704442179440f9400014140204030300038000c40a44003132a9030f41c2c0340d801c3c0104105940001c000200e244441d9800d02c0301181c02d444520040005d926555442034132220320f441050318240e00701d10400e000380c1e901080001090380001c80d004650320101e07980020442458003044251903258a5135520494099900003810707810340c412442200c5100e001e00031a91034440640f0008054480244400d440e1100008100300e0b100c000c40c11410001511224a9919035a0311065001001003c599020000302542001000c002c4030b100c0154608080d4100a45540040c1d1204940c030403201c02018914001441003a1807400c031000303007c03003105550f1030b551030ba2403040c0c2d25008060303050300907c5415070100389680005000007400ca414003011000302520024007100c0c003400340046050548901141513042c1045000d940325910b0340d91602c030072106c401c00c0d6001042d0090724a50090340343c09214916014042100302103602c450420030740e5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 321876339 1250 321875089 321875111
    0x60c02060d0c05030603010f230c040503070815092109040e10061703031b0a0e040c030b011808060c09060706090f290f0a0b0a030303020307180e040204 67
    0x34920408881501d842c0c5401851030074030b500400030f98003d0200350020060080c0401e042c3e42101c0a081c182c00d421208000307121490400580760642c01000300614900b811b80c2d40d00070a180100a400c00300d281d03000907000703800d030408020b40035600c0003060740103200043c41d00c50781c0e1940322440001c032283c6000010300342d005a161a041000078205c1d04d41203c0450a04814000050045000d0780700d00d33244540540081c1280007090700d0145880c8014020081e5030094888101d6000106050074815070a0420ba000e50fa28455446200c1c001c0d100403a10007000000101918a00002c84143e04d0a00d20103002c41d010004241d5031218401001c40d643d2460800095118011650000c03d13990501801c4070802950400002c0000d100b82c001403000003050802c003000e02e007044000c420744030b00000004c15201d040484641c000ca0054000104442d400c0d010685032035154000380c010940000a01c00800d501240325480700c0c50010b0380170b4800b07042c8103280079119000b4101034400c1c0d8079035140c228 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 321877589 1250 321876339 321876349
    0xb0f0417090a1a12010f170105060310150b0c0d03060605031b0904140109021b19031b06140f0601030908030c09040e2406040b030a0b0703110a09170a020901060c02 72
    0x11030319032944130f0000150707500c5c2004c2079141c085010b802192102086102031444050042c980650340c018040c000c62030fa9140103c000b08920194818070b0800c0441c0080c803154100c0c01411070001000152020710a12076001c0d0644885030300010400208008100e64201d501c60550490b000404215603586200d45c009000341c242c514605845e140040f0000860025035402031810030a940c007008440070300c10642680b1440580000072200201c803215000081c465680441c1040c0f20221080c10400e6a456180440e140c541e8002e84020989091101d04c0c5080f6418541c402c2003403034248144400e903590b186c4540400382506440f001c0109001c01540c0e01c51b008010819042012203100c40d0f0800d0204070001030a00d4050300070300120010036003a040c03c3c041c42c0100c00d806001030000c4081c59070303a940380d0f4000400c50b0003010b60b0740c01c413041c030004a01c0c0145945000c42d0b6481080c207080003c1900a0b001c56691801c865110905038401603c1c0e0603c1981100c4690808207420f821a002180e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 321878839 1250 321877589 321877597
    0x3020d320f12040b19051905070308061c03030e011803020709050105013e0f1501080d0f0f0306051c1103060103031b0206070b0f0417090a1a 62
    0x125181009521010051000041158200701c400c011100c00c01410503004819208500070040007032800c1007000c1401c200344403407036042e001c01d2400c14a0000c0628131a01214034410401c0005000016914141a44480501e40001c4111032290155803c4507180310306003075030710b001000d15480d5450f1030030910f002c0d031040170b0599640e00c58030000c0c40240b60003034951085000b210030540c9040008103c2d0f5201e00c20b2960685803020f01094034658120048071403581880714a000c00000700da02c0107121000f40922035104050900811140740240c8504000900507001040c0301d90280096000140c0d21900304540070a040c200400601d0240310210040d1190f5042a138203d90100324000380844141071101c0b400307000301c1a8a19403d02e14080581300c2d4420701c40640003401c9240e0240814869180c1318807002d100501d09450100503a031440302106046640310822400360081100b480349041501c0b4004d0142c010840c5130000c0d1a00150494440307000340802d01c0307514650b00c0c00100e01d100c115 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 321880089 1250 321878839 321878903
    0x6061d120d020105090f011109040f180c0f060201050c04030611120c03070f020a0f0209061c0b040302120a0915050c01180203010e0a0f080c030912010912080103020d 73
    0x25030144001d941019020380400e0301c92118034400d0440f1203404000620490110198030110796181511550030400030f0159040c40e405400d41c4c5107840d040140da20700308000790503c903190500f080e0380303031a001d003030042c140e42e001c1d4056904040400c00107200d00d204035001e0f240e0102c03001034000b81d0410852154002d40e228807500c0d0700014248580200020065842007140c0c0c0c1c0c49107254405240101e032210061f42000b059403060101584c0146050745000d03602c004040c02c9a06074604540480c110000d0901003903c1c0c894a100501c0289941404040c01d800078000c00e1a252186140d80105581d00301e02c1004040201110ba0b642c005111b0340480d5440da100780c00920028844034880145034100c0c441c124070030b610300300b0550b0380c20714041141142c994020380c84009040a40d203400c0425440102c030000180010004801143d58000e01d800300c0300002000000d4500d034918004501491000c928000e200d00c450041006036640881856490b0303210070a0b404e4281c4500e903480c011503950b420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 321881339 1250 321880089 321880093
    0x4030215120a1b0519080a0b0d031101060524030402030a08030a1b09140607020303040306110d0e0105100909030e0432061c0c03050307060b120106061d12 68
    0x42c815400321a07044080040d0b441010100c41c1007050f481501c0510a000611500c13824000102c104140501e00503940728451500101e000d002040c0000c00081c041801100485c1c400d810800849609106801c080e0409850140c10140980c1c008400400e01c141040b40740c4000000103400c54800f03108404940e03034803d04a44c0c03241014001e0384040c1101a40d200000d02c8100400c0b07841900c291052401c4517003464004410201401c00c2c002c40381c2c000003041c0c0c1c06210030000000060354034420b0607803845880318016101c0300a50904400d8616214a120044c0c0c100014040c2404000c044881180c1c03595a0000c0e83c3c0d07207140b45c1a03034050985204243c0c00792411002e03800003d82410218003d4800040380b4500780015442208900015180244c10601e400d00d449004020b8030800b02d000d070f01642d020816a036581c0d42d040e1640c0d1000710100e481d1600d0b65001c000d2401d02c07134846868024918024000e481c10706100400401c03010f03004100804200761054a103442e4410b2501c01100c02c001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 321882589 1250 321881339 321881341
    0xb041a01090f0506030607050301050111031b071a0702030d320306270f040515070201020d0b0d0b06060d0902040f1d0a03210b0d050d030507020703080403021512 71
    0x15094010680081650b1515040400044031454042281e0f44644c0c00750b101c045c00e40c5d00381001150b043d443c4021804541c407041000c000820342e0701c03019a88250000c80204402420f000fa1902455640000c0c000ca540d4140600b80051f13401103000808500750346401e01080502800c03800848082c1c80c04a820311000943c001c00a400d000029480b507401903440070603203030181103244550703c00da4806200e250491000f080f02c4000345840150005d01030380c11103001810740c140440c0d403488150761002c00350f0340c00500042210041e000d040306010040b616640c88144640316034099150040110317200e070100045034001f005e13403035110703440036900600108859104901d00340001e2490113601c101c50503450404d0390130004000b0b0380401c0700754181d1745c003080e2141d150706103d014000001070076012034440c4c000d543d59888540030060600d000760000c00710840d0000c000340450790050401c000710f411810301480411190011101100d605940c102c83c41290345e40d0210b0030307020743c0442c0090295900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 321883839 1250 321882589 321882599
    0x31201180621030917060a020d0b091602120a02060a0903021906020d050a0b130b040609090f0b070e0d0f020d05030310030c051008070507051c02010c1b0f0b041a01 72
    0x480b44001e428869241c100c0705940701e501c0c602d050111058003103500d5101d00001106041580c015007008031140e10003040740781c0f4000003e22404811150000c1c41080d4110056150354104503507458004c485403154503000041d0300003904d684000340081c00061700e4910543c1010300c20850740c400c4460200c5c90541028185c07406001a500008144180d1420710003c15a120b6580c0300e044a80d001c02004e030701d242d44c500720b2a4030162000440507640141d03960340008481c4c400d8000c644d00148100d2000d401d9441c14508403400c0351020f80100200080d00080740d400e030300e034a02d41c00429a041000580301035003e2000400d60040107000409502020052199011482203464107070792007001000842e0b1b172240e0a02c02000c0c030704001030300043d81e0103001c110f43e940540010300744603001d4010f8070301c0e810b1020200d480aa00505600e070060b03650300c014880c0d82d03034411704c03040d104100221590212140b64840c3c002150780060090503400394400410100068213842c08003c610307600d00c80150f503a40d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 321885089 1250 321883839 321883889
    0xc160201090b0a03022701020a020d0c0902071103100c080612070914010f0e07050d0216170a090501080f070302131503020d06060234030204090602030402120312011806 74
    0x30508411a03031301c03510340c1e4100540b64046c803a80044042c3c0c01000b000301c00b5000c001c002c00305a94282d590410f810804910400d0030b000402013107000d11b45401401d95002c007810314080d0014443d0468900c0c18540010095021454541008044031510f9400c403c0a03100c0f03082c21140e0b84000105807401d4451940f081e04109014101d400c0189800040f964801c205082c200b0103e40310700004404020100c001c043c00d9011f001814000303069191088181d40e03500700d0910110120941d488001310381c4a03001c55121402e035028100a02e840c1002d810702c1c019041c01d00c078002d0440c40905401241e00680302c0c1003104000001e00b101041d096000d4004100074000b51b0042141c03220b40341c14218085040c03030001a4138070b6403400500c401c1070302500402100b001000100c4032540a9814050004003582e0356010320600580100001a84c80c00c1610400007110301c0310440c0502a041800850316852820020741d044400e40c0e404800b03a8442002038000501407508011540c1a11b20314020102c00c603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 321886339 1250 321885089 321885097
    0xc030712020706051809070c0212010902090603070b300708010302030616050a140408070902091806010c14150702061603050114010e0312030405160605030c160201090b0a0302 77
    0x1003902030b034101a85403d400c0f116803003007180071380300e0048040b0100c0d5503090104009620032001e01d0140f05510381036000901403d9543d98000e001c2e91a500180103500c0c120603007d03000740d8100d00130140a46800340380181d41c05907407500b21144020340c0302080a0f020520201c0300141540000903003514002501a050070004c1c00164040d200d50000111a4405038500c0041d000460705d0349401c2c070803464411500f642d4035103090109d104080c0400504580c013044104054026806c01584800c005000e0180401306400101452000301d418011140d030003008424030305420000400b58903000351103091803d08540d05a480304425072017007101450703001c94080e014002d840b10003140c5c2180e4200c1201078901c203000c0d40180440c42440740c8810340c000e0841c60404070f0040c00703172480c401000d0202411030f002110705890356002140404920706144040c04090f0200307042107800c5d800c020321030f121140600075014084a01e1a036000003568000d032080b000820022035103550355102140c0080c00307908 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 321887589 1250 321886339 321886373
    0x307080901050a180f0f0b09010b040b0a050907080406090b040b09010f050c09190b030a021c020a0914040f0504030207060927110c0a24050411090c0c0307 68
    0x440c2c0004103100680078010494030803000c00e43c1000380144c1d130300c44e9414400e0404044480c0d02c510424a400201e90150132403280752240c00010301400410280030640e010361a04a02c1420310190a20040d6248a140743e08a001454203081030fa840d441c020008021420340039002041c1007040200b0000301e800e00602c0381030000020311080c031002d40c81000742c9209503610841c010060000f420503040940340368040e0700d584040b000d00585d075041070355015030082e110502c00f2a00012400241c00315040034071401074440d0b900314500440c003175000b030901c0300c030f4010100c2210219030061250f94a5070004041640702100030007160a0a150103540d0303880d544030f00720118084480015102c14419074000c07916403050320740000910302c0c8044400034410341804070030b510801d000c2d1b106c1c00b21040228080c003a1044046010914001008500b545a01c0c1420b050300da08210400000038a5512405104107050b2041d44550321074003040005030042090803401444081a640103220a859070b42c0c10310700f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 321888839 1250 321887589 321887591
    0xa0501020c10061706040b070201090c031208090d0509040b010c12030f0f0c0215100f030b150913140c0d0605060f0306060d030c081b1c02010c0e010c080c030307080901 74
    0x355841054203803502c4560751000140d0450400038000c152040b0947c2d41c0100c3c6440009080360296a404210f82410703007003034481e0b61030b19240001d40c542194005401940f000c00030001d810110000520390710400d024103000304d80b202c2002c0d9543e40102c4880b0481c50384018205d4100110364402001805851826506e0608000c1030803c00b840c80d01c0b039040104411382c040c0c65001c90f614800740000c0d0029200c1c468110b940c0100041c5076901c088880301840c402c00364450981000e45940300510005501a8807584111082c0003c0e810840440380c1c195901090110340301440f1194241081c12900d1241d07003103560702c6101d800f044442c0d40821f1180b01d089070045036480440c010f1565482c81180d00b030b0b800c05e40c401c0c0b250001c203000f506620101c40c422098585040c01d40d10540b00d603209002440c02940e4841c1d41c41c01c99500b003c100926018241d8030081009810081000f030801000b00f0000d41030050f04020041800882411110782440d104e003201c2e52401c004000405500040354201c10035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 321890089 1250 321888839 321888851
    0x50f041418060d03080c0d0905030a02060106080c030402090907050a17191a0a0209061602010806010c0203070605090103091e1a0402060406030518072411120304050a0501020c10 78
    0x144460680e12401080c0c00703405020122844e90703044d1802c01d8050841c2946c00d20600280b82214030600501081903c00e201031030315400561800b038580700041c0c125034203000400081040b0441b0305400e895010380c04507100d4819071150001c031424400607030000ad4102c0d0020380003103442e1440c1c0c43e04002d80c10191084030503105982c0c41e40d1480c00e0960000400d00296982c544200c1c49221544580010811100501c0e060ba4900020410b40c0100045060480350002200a42da0407142a0394043e0081c00c0c0066295890350000703881380f0403401200c0504c000840e003254540d2180c0c1c006401c0981c00781d401c0640003c1c00c95550a081035100e0206c07250044101e811091208040c3d20500480d809848181014103001c03040e0060980100407d140b003052400d040c1d0151400c10a1400400b40d01c0c201c1c40d01d0b07030902d1103e0071660324a482084240051042c40c5091040002440c68402d80034036105074030b907216480c10608040d10a18007070065800401c5107401c1180c0420003407070652801da410421 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 321891339 1250 321890089 321890119
    0xc050717040f090b0916211a030a150c090308030108071a13181103130302010515091b090d0b06010801141003150b07150b010c0b041101050f0414 64
    0x181d83c01441c0f0744c0d80013400034001c15a501c034a00d40c50300c00d00c0c000f400d00e4a024603c80a01d40c0540e00003024041d0007944440004e0200c01210b04a68024402540504503144040c2c80307840c03003d00c0001d80b540e0416941d1000c0300481e440703a1081e43c080d584c00550240d881d60344a5035107954100c02d00070790200006001200300061035030401c580140203d40300f01340741c40d403410050036040000000c8620300b00340c4400c0c140420080c0000110300c1100034800000810f822814000d003101c00041103800030b8140700105080540c3c5128100390f209400c01100300d040c2040c68180c101902034101034642080845d4091810001440301240c42010213a0f01c1c140ca40c0e90381d141d260b0300c01c0b00c00707680c10750003821406c3d103e14618031980222401c00c481102002e44182d80d000b5811150f0b01000040e00c000c0181079562405481034020100003050074a007800020940c0d407144103882d20b01410042034101211840d40d100e902403001d41c2e480c40520542c198503140e50b080c00703d42e036110030307844280b064140e40f901328a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 321892589 1250 321891339 321891341
    0x30b06040c0318080706020f04170105010b130513061d090f06040206071b0302100302040501170126190b01170a12030f06080304030c1a030108060a0c050717040f09 72
    0x31900c5103003d00e0302118955034031680c0d0707160f1021a0a44042e80c08101c0744103400c1c034960041000302403e060902c54184584551400c40d54103070000840c2e04402c104481ca4400d9032440f00d000e55000319286072101c000440324500500d0303180d0103580042c00d00b07042e08582c45800034469205408803015200018000c0e0340c403030780320541220000c1d0b01c8071042c003070714020031002140580c80160000c00620826120b4001400151651902c200081e800040520055900c61a16000a00d4032440d0342c41a5052004041407018181c0900303180c040c13060302c130841418080040010301950400700000d160f0081c02c20240d00f11090083c004000500310000300030380c07000540d400b036240d00021010000140a081200682800024400d2a42d260b41000c11080302c140010401581f0403c00780000300d03d0039125184009020950098001c2c1c00c1c40100310048011883e0391780074103010070000707060b25111401d559074007810501070002c0c804061981601c041e03040c010000d0769030a14480032a40e59840280c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 321893839 1250 321892589 321892601
    0x5040c03020307170a0f050a021206090c0901121101020a06090f060b0306090c040e03070203101407020a0b010302040b0d0605040b1504020a140a03060b37021506120304030b06040c03 80
    0x4405174801c1090001043c4036042c0f4800b02c520031410b0359034442d125000600340c00c02004c0b8140e03154028030184034070f07000300304450003181000790340b80000c0d036250000f00e855030f151101300600b1a90f040d4181c1c900b1603200703002840c001580040c2c200080d0703005007440031040e010b12800703e603d5480d002c0c00f038285250000701c041c4102510001003400d10044818000580031101c135294407840284031307500040c0c1d41849112900461040b00058480508001c1040400e01402000c250b4100c9404140032960401c0c016056980503940442c2c0020081c004c9805940d602a0152216103020309000c104562042240d009200b9503d91143e050080c3c01040100d02c00c201c00d000100d4413208158a0020500e0080c04c0846d00504000034442d907242c0380c0c1d00583c0d000320440004501134005030f440c21200e4820507860b4010043c0341902e0001c1035a006584e924100041c0080a40d8000000d40d41da540c41c079000c109041008103903a02ca03981d03031520705590320f0240e6041d4800d80c14001142c3d5801d00c24800c0e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 321895089 1250 321893839 321893879
    0x3040c080a08090a06050f07020f0f0616050705060403021e0d02060d02091302130303080406090203060106020d090603141f0b19030b03060408071704090606080702010c0801060f11010f05040c03020307 88
    0x307d031a0404690800003000190004140c01104090103008142d80e400f000d04400380258000d44000c420030702c0c00c6424213100303400003885010144800d0015807910300d82d14041c0c1d5006032440106031070711400a040d500e2502d81c000d51144000524503c507100c50340103070040340006d4800b944500382c0101070740181c1c01042e480c9480e0000700e410401c08a03100c2d07901c1a80007030140200060202550300828205402600402c0c050b92001c0e0344020300301d41c4000c0000c000d001c1c91404005800402c9007a0701205409460501d03250340d11034880c440444481e1026004200e001c3e0929554070b89094681403071149070b41410b005c28504950700215040128038644150ba00c40500c0e85801e64603504c41e801905260040c0150800070301010400308128460100a80115141e0050320301d4981c0e00242500c1c40c0d00045000c00041d50010403e09401405915510903c2e050401c241200c40c1241c0d40100141c440016000f42420284002e11140c501d444054074025400e640c5101c0e1103c52000015200082c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 321896339 1250 321895089 321895117
    0xf0109051b01030209090f06100f051204020f040608070923010618080613020f18010510180f03020307080f030301061d061b01062903040c080a08090a0605 68
    0x180010745481075000d108403901c141030040c20050303240f010030b6488501300d81603007030500c09800344070481ca001c3c00f81945c100081c1c03801600c2540252401030050180c203142407103442841d0045400c541e2403500b0300714162405481044019036070400345039280d00b00d01c03403007100c94503101c43e101010b00716200c108031401c940098403090f40d18003901191320880c0c00360040110540764202192048080c00903074021000101c00403400d40c85401007090100500c00b10611034410b20004050b100b80c150082c0d41141c50403180620410f00d01d00e01921032641c51032824502501c2c0781303804501901400342d8403003540e00a03421503035000c4d2100c040c55584c0566118004441c3e0090004000041c855440c8250b00c3c1113501c7c801b03041400c0800403848030b80120105c0326142c60041d0849041040c24071500c0c1c010840c81000d80f00040da08100c0328510707584020380c000c124000100040a00501c8445000280f003004100c0700414180c0c10194101d400011030284a4103c1550008440d4421015a6010500504 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 321897589 1250 321896339 321896353
    0x60a050f0120070b120103020f1807030b150703021501050d0309090f18050a062406030504110306040803010602060f0613200a1706060f03040b09010608100e0f010905 73
    0x42d2500321940d0a8090350030612500e2400304103104040090400f810840f030040309194154410801e00d0310000302101c2c000d00701c119100b070940010030460b45c1c00180b1414005480c3c5807001c04100c0b0314114081e40c000700310001641004041d030000b80c81b020080c80c0e00b1108110b989610411000b850031000c080c00203441294240800700295003c842c13000791038040002c3c4a1605844103501d54202030b4240c0d00da40200040c0c0e0103203c0395004400303000c0000b009502c039a0300c408408802c840114003c903002c00d552903000408000218448400c0508000d040b9840c2d0320382884c003812540c2c82406100b006025001c007103401d503114445403a005110003400305458201c100020402415590a50b40d20741c0780b1040b0200b41c948a44000300ba24802c1540d44c5000c000c0c44200362070520030050281c5018003010001304034000c18de60103880d0402c1c0c1c49100d00c1000e44515807014090035040d0841903190160003141c0c00c4c580241e40c00100c284e001da0040e01d4590a40c0c2d80751030700300d9003400406407041d00310b00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 321898839 1250 321897589 321897617
    0xc03070b0a0e1e03040e040c05010f1404140114030a050103030f0305010807030210022b020c03030906070f020d06060803120612100c1403100f05030a030905060706020405040203040b060a050f01 85
    0x30568404a041c43d0b001c036070a0590b40c4183c41d40198041d50b050301c06580b00d640510065034804481c4002c1c007441e041807060402401160181441144071702401032079141c1385a10903a100d0040c00c180b50001002c5180c4030b05100b50041c000741b0007844102c02003184040c100c1c0e1000c0c060702440381207074000c40180c00440c1c5503401b401610b04010b14030400310f0242e84c02d08542e0b203042000d01c184a03441411000011659040064640030344661384910a50040c451b45201d9074401048401c01a80442d1600031b0400500c04a5011200201c00402c401e04052001c24182800005040145d20403035580360f69441c0c00c2e082c4400362554018541d0a030300400c504099003d400d42014080300e2032403a0103412070720703a006080899041603851942d020b01070b41003080b020b09030702d40300c4e001740800304c0292020183c1c59038060140301c0b01344201401410701223806001d0103803a40c1a0703130040102410a65503461320b80792000c44a403084454034480d5907110b0010402d03050940c0241081790060b1a80b03803110583c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 321900089 1250 321898839 321898873
    0xe0406020906070f03032c06010b0711030f10060e070203310f26030a0c0614130203060703060810150302030a030f021c0906050715020c03070b0a0e 65
    0xc01c455800c01d20400070400080e000090140c07541d40683e400081c460b0041c80c000d07140c900300c0130a41040702d07501d0045003105000494400c0c1140e68144d10140d84004030b1800c00f00f0750020754080781e894060428580c090010210b00c07034442941c000300420455032180142d8001d050180c80000c016441840548040d5081d804000101801c001e060700400d00c41d1b210b104c24594081d0415583d02c21500320400078516001d03591458030300300d1958180440040c02600743d0301c0c003c0c862100200311040300c507101030241039400703000034080e400300002c0245428101017520b940d10300001ca00034403c04000a2606100e1300c42c040c00c0d1401c01028180301c0440301601005062417419103000c0740c1103100c0c0040140c0d000c21002a0080c4039444016140c020700b1030190501c42051059492030a10760280100c45620004220039100c4604059441e041d250800640d8040000d05103049544002a12822494004050002103110f00c11415540da9030b09180400c0e500c200007501d0540e408508610905080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 321901339 1250 321900089 321900097
    0x4030c1a071502130306060b0403051507020d3002071b06020d050d11180316030206030601031d07170f030708090603190903080f0c070507210602130509010f0e040602 73
    0x1c4900503251654513519504c04884560f031280b010023000260410410800b80080c2060038601c2036006418a825030b000ba44030064900001c0402450043c5850a00b10508003c10106d8000300130701900900407100000032750224000b6190a40024000d0a655084a01d41d60580e00d240d4080d000c000301614003035901da0006180513030041d49031410351a084140c00040c11582504400d00c1e0205207140b1300b8142450340d0005c031070070040d04003001032000d81c54400803a90000c2c0e086c61300041c042820780048210058604a107003560007070540000b59054042103c44444112174182e60703410003103203a050390701c0c071400500034480c00b002d100190091500360061548130303035401d11a117200c0d0800302100003140d80304142103000c40c14640600c20605104620740394050b0354034030000d01c0d1a5443c2c0743e03240c0d89c01275445000c1f40a18506000341c0081e81242c1440e4680340e000c0819034071444140313444a4802c819008842c00f59003020000503c08091811920444490415075000d42e00d90780c5801e400381d84 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 321902589 1250 321901339 321901357
    0x30a05100c0309140c0a08120a08040827011214010515070b010e01030b0a06120b250504090e0106031707030302070c03150540050304030c1a071502 65
    0x1595503c2d40000c1980f181034040011110405040c0001c80441046092011600b0601c000e0380300821851501c0841c501b140c10803482401d0844540d0746510303061107030b031080c1070540400b003190b8505004440020808a5074880098845502007414480c9000c00c44d0a010407071844044a0001000203040004c03521341110955034049140142d41d40340c154200300d00fa804080c000c1d00c800010030512040001890b007002001d90300384403944c07900c1c01502e5000040103024084500c0b540200d000c503c003080300003402c415015070f0361402103520700c00509039400c54424503690600b419004281e500040c4200010f5940c40381111005ca01d03070042c0c1c65000e4010045c01c40525508000e92408202d0000000d0003c5115000030301560241e00000401e844000e4220f428a02e031980702440342038810b0303030746c03142080f80012241a95068007140da4084040c000c8050141d000015020050141c0c1c8280c0c801619070301441ca145070f41c00392102100d11310032042c0c0907100051050403c0c80c3e880050300104070f062 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 321903839 1250 321902589 321902591
    0x7020c190b040b030103030e040b090705030a1401080f060906330a0f03123f111e040b07230106060503070f05030402030a0b060607120f0e030a05100c03 67
    0x7500d590306180039501c035030045025020080010010190b00c514800751012058900f408040710101c00300750484009445027003030007804400180a000c0951080c9042c1c12110f4000200e03582d0341c544540c950550291b54491030094100040e00e0346800106a0b00525100080c41040d001e181d9415010481d500308001c03640041e640c0c1c1503881d40d10348030480e01034908611740c032079018510303d400c15031030402641b40b00c1801300305c0000311099034400d40c180040c18140500302d0b04281c0d01c0b030b5240c03945007e11a503e0b010b144c0740101d00403456054001034502c7d0300d0008121603100d02018013601603802948200a24104200700182c0040c010003c1c00032070121103190304540210201ea8603003503580c0d50700a03000007000402000642d40c0e02c02d00207001010241021b40c0756040030780219407200d0760302c0409451003500d800840c1403500c82d1412190301d29040701a071203601c030306000d0041482d0708d514100c1001440102108116150100d4100c403070356400402808001c001c3c00c2840b01400c00d42550308245 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 321905089 1250 321903839 321903889
    0x304020109080d020705010f110c010e030f0102070b040605010e15210d121a010e040e0c0a09050603012904091b090203090f0d08071d0d050109170307020c 68
    0xa5408200e000d00014058014201d010b00f00000109548c81403c0b42e08104250600301400c0c1c1d0300d01180ca0b4a4950007032030581d126001e0b480210340340240d5059441c1941d03100040980910903c0c500040c02140708542c241b000c1e90ba1099000240c40d42519500380c400d090141c00c40c014a03201000001e5034040c0c0b4412001080da1a00d0303a802d1008400c1d10b0000300f428181d620a240705248030341440341d900d00c00b09480c440010000280385c1d41c4004007584c0200ea40700c01803d030001041100d40c10312000200122481901d40005c200908025600c4c18040d41c2080b1030f01c00400943c003858a04010620449030049201c02d00300700240001031426942c00c01e00d03540e00011010346d00f00d2000a8a0526005640c0782008a68a490041a01e08010b159040544088803242d8450955a040700843c9400a00341401c501c03007103804c1201a03002640020803103081020810123401914007203005030303400f500340d8614403501107603480200c90510050f08001d104008031320b010f20300e41603502c812a40032400c13 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 321906339 1250 321905089 321905099
    0x5041e0f0209040303020904060f080c0105070501020c011d070f061205040c090e1506060304030f2d03090501050a0b0a0512030d020a0306080607050f030a020c012a090b0f0403080304020109 83
    0x85007082c3d4040c0e0020390001003000e0182440d001d00401030141440e44420649000e6070310b074035003a400c4001810441d0015240c014002c003501a0b6102d060540000c009111300d0305512442c060a5407d103030124050604002070108904c610b4000710342e203940b10405404442e4881d04001e220003007003200c1d5900c07011000b10b4440181e00ca4100c41d1020000140803500e0a4240300941c00001841039204a07420410400000c0e440810405540300504051040b01103038104000704a2030400d041e5030090406200091107a495000300b070665001e140200116100c02e0074071001e072106661301e29041134450f501000f160400c003100d001558460320980f82000c0104000c1c84c00c0c4c2e440b0f542c296000988458081c048601c0c10b11049820244a04081d03241104e50b12404216002c010144170140b0f81c04229030310120380c04c0d0040c041840020b801490b040d01e1103075400c02c01c1b40c2d807900003c0000b8506100031078032469100032500190703011446507040500c0d50703454505590000300103c0c10003103a20000a2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 321907589 1250 321906339 321906349
    0x5150d1a040b06120c100507020307030b04080301031211120306180112020a0815010e13050604031d010504030302060c090613030302010b011205040201081501110d1d0405041e0f02 79
    0x401030340b00d0050884603081480c10842070f1107002007141c59a401400592003582c3d03c11a1a0300000340d0b81c10110345594050000a0516116910180450021700108802c006401c8001d43c1a00e00c25a091a900085100c003203803050002040714607da4071042402d4000b60304030001c1c0d9884030005000130170044003c04100700300003003a84603052541c5c1e20f0180508500d052020b14010b482c8200040100c00800503040202c0c0e241131084140040101003c1007440e00381c7d0260400c61604407041368031034200351400603c3e000c2d81c02c4034580d450110a9200da0150b12a400700d800312070301a40107002a4840e11200340003540507807030302540000b040080b020446524030034070b00214080d80002502e54480030024203554502d00b00305007242d20701030410006030381212907036421041d40060411140c0000340140c0380090758421100940c4115141061b825034001c2c01d40385080350138002d02e605400b1240522041d140b09940080414001724803030f00141d040e5002c0e00540c0790003041c15801c0c0303440540101d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 321908839 1250 321907589 321907591
    0xf0b060a03020d050a0b010804060504050307141606181a070c150f03061208030916120c08030316050a170c090405060904080a05070804170d02070905150d1a 69
    0x408650041824008210f080c8100da92200a103c003d002075503e00c000244401c0004000505a59980001c00c062150130401d40d102c1743da22150f40d4401c1192211155994110488000400103994401007807007841401c4144260000c09101c04215062052080c000c07412100301498522007405040045000801840014038110103003140c0c0b50b44901005000c2800d00360740d04245801c19008010b44a1440d030610f0f14035412291964403622448080c50404042d0b0481080ca00b15100000c14107804803010501c00302e12441000030716075903410b05181c9900003103a030303021301030354079152504070310f019500070021807003186018840c080540f151034181c00e405a81541c609400480e0404140c2014800c0c0d03500940d0448440032249419070380d5501c50310a03400910b04104022501c8000c000310036041d60003034008211180c025800c450022691803540d9803003c2c0051041142c0080e41c148540b0410b8007900d82c28200c0d0300408080383c1800b02d12401c0348000c9070481a0488194440710300e40040b2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 321910089 1250 321908839 321908857
    0x30d1e05070524040b101a250503040602010c020f030306090408070b0106050409050106020a0f03030f020c071d160e060708070503120a110a0c06090f1203050928060f0b06 75
    0xd5650344c00e150410120680c4001c28044040d00d00390b80c00c2c040d044981c8224100880074848440d0340e982e080c00000455204074080004400c1d240d0b0744103040260100140c8240d5003194000c010300707102240304aa50700c403400c2e07031000305070400c00208009007040b806140d885030141c0c03090b510304220f6a80d4910038100036031110000602c0414144a2400c01d40211801041c071803005011010381c82c1c0b200308040203d441c0060905070389501000c0a82155016686600000001e03607000656848500519950b0300302c00c41c0c040422040012282200a400d12210b060280e8499111945030b40621850b9032202c40e003503070001014401080080e404000806403410100901d00c41410044071101c1510301d03500c07902e10441c000744004c1840a6000741300c050150382000001c80c9204071420003c900034007006000d07000186c01615041d51503019041140079820403070031200a141f11091001d00241058100705c1981602c048074004500300d0780000045070700c0000c0005d21882803000080d02c0364058000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 321911339 1250 321910089 321910153
    0x302161202010510320307080c15160f08070c090c0e060c120f0d060305031809130201080a291806030c0d030905060d0b030d1e050705 59
    0x2120322603080c01010b03000481001812181c038140f100803519102d554641c0b076040002103000051070a00e035419215000c5018043e55003d40e180c10303c003921020a80d26950290300c16070707003044541e000f5608440075403202e0002c10401c000c1c1540c1c0c040c90f400c2c208005070350104090150002007644056440000c12480c440041c805a0460000d46081c02600744c6912800c001d12810603d81c40214000e10644000c98a556072940ca800726194140603101e410600c4c1894884007004214000000308640240f441403041032440404c1082501c900031a401d0010980b5940c94200550183c6078035500510484c3c404141c44080d9034213516150300f0b00810011403a000d00c20b000c40c078104041d196850601e09011320585107840004a0350314194240064054500c900e9840281886036052101421004180c41d590300d092000580141412210f03940c0b03c0d005010324044202d0041344107242c2020044001d60019010007029a980c0e004820162030f42d00412079109c540c03d80031900a40c40c5d07221103071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 321912589 1250 321911339 321911363
    0x80f030f04020405130503160312060816090213030b070e0904060515030307122001050a09021201090c060e040605220513050c060d110703030b090a021c050601030216 73
    0x401054420180807031010540301c0005d10007091021040f0303411114070044409102e8004d140c100c03450f26124841e43c00d10341c54078502180d0304001040c00c0880c070000705110b1211644401030b100491150006568407804480310400004280341c2c2c501d41e12900c9800d00116081c488408511b1204c1c0844084490503903500420401002c4481c02c1c0d03400c214190000c600780b080503a940e40014050340112020700034001c58203605004000320b0a20f0901e140c0000b8070850030000001000b400ca1040100d1007164220300b100e101210512910982c6500309420150880c600720040e40e9010000480d140c1203078440304081003070344400345c4c20751000c924400d8600016685c041da8104844002d040c02e001003110b00b00150100b880000c0031980390800301c400907594840b10707036244000e2078013030502d582c1c03404041011411b0517050740c45580e4a60058661240540c0c0c0d0b081e882c4100d204001803c00a10308190307a80e04031500952000340e00100604005281c1380d00c007941d140d200d80e11b5880484115481d41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 321913839 1250 321912589 321912593
    0x210020c011202040b0405120c060a020a050601060518040b120f0a1506060f0f02071a030403080705191412190c0201020315130b091006090e040807020d080f030f04 72
    0x410b080001d038030b42d074218101401c180f1200c00d580710b03e10038580304500b0012001c4a03040180720301010a04014249643c5024554010307481c0c00152a095800e409000000119203000310121361030001c4c419034210070301c010381e010080106079110940743c116005501c1021515000c01c1044020b2600714028200d017040b038a0440e214100201051041c1ca042034020860250040c1e605170015566041104455550030022441c0040304c2c3d00c00700365042e071444101e0100c00315500031030140380217540d40d643c1560340701707019070311403140211001c54200072a84043e0010b102c1e180204228000b080d8480c9805405482500c420000380c59903840c1c14a06500c00b55103094a20801000030f140d8002903040d8a4104181050b0100d803488c501d000c0d107018050b011844807668090b01546000a0100581c0d0900071259070290741c007801030f01d01148248101240f005500041541308035441880d0a280c08850703130030300403545104801140c10701828498480e03c42d2000000d0b61181c03a0307049800006203054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 321915089 1250 321913839 321913847
    0xa092103021201140f2803031e02060103121815020f0f0f03031506120a1e060f150512040f030f08100b0307020f030f0409050f09031903090210020c01 66
    0x11380c0119042d404190340c008054445104040805008481c80035601034000002c54404008003103021120050005c00700815810a1072191002800074041c950340d144040c041e0b035a90b000303000107080d00440d0441c04825502c00c600c600c16500118180765030319075456041c0c540c0044580c8000004d0b810180091000ea03508012812003003500c0c0004013042005d403d020b946038440074001c5020603401c1581140380d038540344115980030160403a4601e10740342000700f1b18001d2451121144150003504005106012140031300c9003078a500c0500c101c10b00d490050301e4102603412030103010510200740300c40614480c006540d5441103018a501c454043c0c11403034010404d60741c0303070704410900071054140801032150030020403d80d501184050741e240c5038450264075000e80c420348843c1e280310000344005a000c401d0050000c4a5081d00188460f07101d00390000f0b16040c0886000000d46d00078000350202c6403413015241c030100004e080c001a40c014a801042e10f42d07540791080c0015a000303c0d240050340d40c0c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 321916339 1250 321915089 321915091
    0xa020a060204230d0b06011d1c2a0909050c030f030403020301060e0f18010213091b0503060d12030b09070f0809030c0a030507060f0905060709050d03080a0921030212 73
    0x41203031508600c001a45c0c80d02500c210103007025042116000c000360400d8842514404002c1004109a1001100740604c411060103101308951101038012400381c04e80640300001001c07204503c80c801c2c550f0400c0e025074028101040c7c00c1d1480d204444000c070032918140302d00c10680101d00d014694450660051509440056200418488000d002c0004030100700c00b40302e82040500350300098100c0241d5101d40603000f84c05644c01c00001c807100000d401c403850341c4510001d03150556802e0070701150102c02c0c1c4043c041100c00580094031414014006603079082d180d84488040c1c03d0000301c180685000c29100c0d581222800045884a100c48903000e80012009a004c41240011441c107100301c2030141d201d0604c200c00409001000ca840b030108034403500107800e00b401080e000c00590082d81480e56031200c0540d80d850100385000d0000c102824009003244030b0301c1d010b0301c9203042c648405548800a02c8281c006680565010904510725040c0c038125008200081d076025880b01303d09421032a41c124 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 321917589 1250 321916339 321916409
    0x4060f080c0108060109030b060111010c020d02210307050c0f0709240503030405060711060a091523160b0702030301090b01050426100e0303010603111309020a020a060204 75
    0x88007a0130000395030703880103201003920b03407280c50b544868035007000584000e2a84c6102105035401c1a40c005101c96000928003111110360f42140c08412600a820410015106540070344100410004500900401c002c0113000b18040c02ca4070500d602c0d02d541814500c89821143d01540c481500c0201060780009842080c13502c00e044c15920303480c20000a03030702e01c60341c032a140c00f5101c02700d42803040c40740c942100d03100c04030b004c3c081503a2070300d00c010001c0042d041c0d4003031016417210019260442ca8440d401641984190b0840d04640301019004c0740100d030049080800081c01102c5000c2c000341d8204030882c0035146a400a640740c0d41001240c8064030a6401e0b014100241440104030f0651000300100a0307624040d900160240e900c1743d82e038109504404030004003824a020203840400000055040310300617a01042014000a084c0c1218815000d04141008410b170f030505c07684440750300810a4031114011202c1c140b4959403114242c0e082940b202c80000c0e00802c1c00b0542580042004040300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 321918839 1250 321917589 321917597
    0x150e090601020a0b13020301050c04050301060e0709060e06160b160c030c060510050333060303120924010905090c0105030411060d0204080105060a0f122004060f080c01 74
    0x8544000000d5581d8900840507000d201c44c90003190318190401032041903190003800134806460441e48a1819502512480d4004c0d864a4030005a2500c0e08240038000c5003241d446060b40707860100112070300141c844003035522440070002c03002c0082c8440c00c04140c81e446450454101e2030a8100900e09402c4c18518505000021a04500096002c00d007248030a900a20000305034a8044c04102048003c3e0040d541510418440c441c0c800c20441525212100403d4000140c5001900c4e075042c00b801561515095070003071050720582c08281e1303822039004225101300c8080c44401a200201101c2484010281d003410b180180182606401a03903444a41078005207145200b1400091440c0b00060001e40000e4420106003055036440c012500c80c088a03007425500c80361101e0700c0600800041e281d8511450300b130b4000003520a240c550307510807101d02c50030350100300d00f0549443c071820b2039000003001c5032404d011000446c0d6445d84143d030090305034424820180d600306031645103481c0c2400c005c18144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 321920089 1250 321918839 321918841
    0x160207080d052a060a05060a030c05120c030102031f0b03060a0510050403020409030521090303070f0c0515070207090e07060507080c1b030d050301030c090504080c07150e09 76
    0x203400180700c107040006440c1669903501c4401075070030185010320390520003109118241101c141e00003403060045c0d40b40c2c42c00b0462900d0b03481c1001170861151100801d0032045403020803051074850403c503992050242a64004d9000000181c22079104941511401e540d0401c40421080b09845c40c801600040c418203180d81452030000d81c280c0028401d962042c1500540010020b100f0030640707006503030280c0305005500341440c02070a61b402c03444803d042400b01211041d2120500d105d054015036541c0301840c510303110901c088404001c1003502c1030501c4025941d982c001807080003c42d040c80d019840185590a048070003d003000101e0b03224020003402e0280c42140024041000c20843d1000d041c1940c1da8002c80c600100d0724028110b100d6114050380d840c00f103106800c001002c1d031a5104500742c40b840c0c1c09032403058555000a00000d46403c41d48541880303092400e61141d50818001c1e1303e068140803007904440e00d0301110340c0290b14615141d0321000d207820b800c940c1001d5110030480300c05ca42 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 321921339 1250 321920089 321920099
    0x51512012c0c030402061b100f2702010f02011409010608070e0c090f01030603020616110613030605041403030c13062a030905030109051e010b010219030512010905160207 75
    0x403800f010304068425031001440c07040d10340300070310810405800f0600b40c400e14100721514034010010503124a121a05000b0408a03d9032045190092135481070300030644c84469400443d010240c0354805029590307201c18244515458007801840781c1c1ca9080003160660400482c0b81c1003181c02c0d80601c401001e20300c1880340020900080c0e54000b13500b50790441401208030300490203011103030300c065000031002401030143c0c400c60b0104507460b0702130030030000054040b1040c8002c5100d84050054407850202c42030000070070940080d9081030040804103034540c1130f181050f0a503401691284038070240050060007403944003502000611036424406101d030a0024015120100001c0d514102035a40c20303c5002c00d40a5403441020b068060020002c050070381c0b800607511400c2c0250404c40d804040001c40e00c2070780502521994202c1a8054040038416601c40800d00c060501c0890500a0920841000c0c00c030690076580244564400803c403820028140d0a140384c91030140c0c021504000c100b03010b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 321922589 1250 321921339 321921361
    0xd0207050307090f2a09050a14040f0e0303091b03070f0608190f0f0f0504170f070b0403030b420403020405070c02190609051512012c 59
    0x883e048400f01140e41103034441d81c00020019035612460849010f040c14030760100451a080800350b05031107404000351540c0c200304c4c49030640c0c403418000a800c043c14101030305141d0803104e80800c00340030105105210200300303411600100c030303103080702c0c1e10030f00b20b51200485201c401303c8038aa040d000307000200d0400030b0000c00c0c0c8280740203c005104610303022820580381040c0300c40300040c15a4042001502d42845480503204903001000894100384000e1b000480034810b05008552003516210701c18106002d603902c0d034004400a5222040134002c41c1c01041182c12001e108910907074001407212860810844c0d960441d0486d41c043c89030a0b0510190b40142012031a42c00041080c440c942d403580d010303800c03000d20031743e08000d40203401c000912503080c2d049404020030500c00c40d008500040008407118503054188645000600911310400140c00d0031440241c040840c0c103c81403030100c000501e1498181c0aa002e071802d001a9a03030010b21564440c00340d40701200100f400500344c1003000d8820 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 321923839 1250 321922589 321922603
    0xf070b01350c010546020115090b0d0c09020a030e030702010905120f0f0115050d051209010507020319060b0a23041b0c0309050103050906040605040203032a0d02070503 74
    0x250500c080020740e850b000110b40c00180c45045c41d007090f000c0c013951440441e400c820702440090128132480d910101c070300e401809190640c000922592003110310b03040200006d01030219049800910700e91300c00740071800900b80384000c7d00e98000007695910340c0713a070014100c84481030600c415401c20700880006071782c0030000008035001254240445004404540d040c031803490005017107442041d003144800c1d141134200010000c442c1d1440c04c00030f40c0c0d80c0306200101c081c0001c020190b8112082c0052204214005042c02c034034180340031803c15006a001c2494041111031103e21150700085c80703000c10039a40251200c290054880c1303806249410316100c440e10060000c061020a65800506940c807960b04c83c140c0d01264641c114010700130084007601c01400d41c6400c0d00055541103000c1040e5009004490141100c10020700c5d0030742c1e0741d80b1000300800003d003003241c1c54003040100c140c0d441213480b100700e90660310422200b565844401e41c41c0c6000d005041c000c0554101171820003842d60041045 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 321925089 1250 321923839 321923863
    0x13050f06070b07120903020a0c1e03200d03030209090c040f140607050a1208010b070812040f060c031a030a050a021309021801031b08060106050f070b0135 68
    0x3440b00f920b441d0810f50305040700180300a040c901c0d05c0c1c908000c0c190b001078600100ca014892040000341c880c2d001d20b4650711260f1102d428240703400b0040001a04074181107081d448012640c1c002c080744c40001481010f8103560640020340c003c1014030b803c0c98a0340380309412001d4101224500b074900340d481d030f10010242c441d101c10611004010b02c40394441c0011110720540c0a402d039400e0004524000521240b03100c000000200c0c07000000c602c030b020340d0b0103d8104a0704003840d0350030280901c0110a10f0103000740205c8548903a0121071000841c103020b9803141000a84000c100c82440c864030020398040040440e1003544440c1075180440d202050070181c0b42d805850441200382054103a01c0501683e8100030740119400c039205000d04c040f9810a8142c034032070440100300030f60407454008084020300441c1d0050700010010000c26000350020003c100511000703600b040e1040c0c94010364080240e01080c0c4140c540380d8040442d401d0f5008000040b003080b20341001c4510500281c5558029564503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 321926339 1250 321925089 321925103
    0x9020a0b0d140c0a080a02070f02300f0d0e0d060513080301080d11160b0a09030519060c0801121b0503010e15060a060507060908190513050f0607 64
    0x581e0021195400880c0800980ca072418140d0400c081d00400703d511403080c060001d0b4100b030204112130000c0c001c8800d03068000d00d00611030303049a020400c000881100f00c0302d084546400310007108440108442c90002900050924a4602c3d0802801d00c40c0c0400d4450410241000e600560341d207901200b030589800240015031a0341321040700000900d0b0f4500903103402400300000644440018982c400c0175450340ea481441112604008d1b9920901d07120311411604540c001c0c84200c01110203842c7d40d405514004403040c0e41c1c0d484003400c141e11556842d03009c50341450200c003803020394050381c4911001850a45210341c9000340100307070b921184034000c00c4c8003019000100c21001c07100007a400313010014002c000c11020200d8650b0350f8104c0709801100d203482170340003074010300e45017407607c049820365101c00c2d2421580d03585030b000904000d0360403107800074140450002c205006603491442141e0383c80d8a65a04003011000307182c04069800103110341500544400903032292405e98041503030140b8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 321927589 1250 321926339 321926347
    0xd0e0a0501060f050141042c04050604021020060f06010c0c150e100c060501140f12030d110c160b0a123b070e1314100f05070309020a0b 60
    0x603101c00e41d50b006e00c101e114160f0082000314020118042c90405014400101d01c0001c251200c001001e29040f00e0203840380c0c0181c03000a001d401e00708200d00c82d6039541d14140030024000c8051041c2c0d050b88244811680c0e01410811550440300741c2c5583d00103209007000009031003640d4035203005400500820444801a2500000c058015100d00f0010704000b8030400181c0d034004402841e00701c1d0035a040d90900d08040000502e05026400400604405040c2c40424084801444044003828220115500c01000000d44010451040c0300180703200e2046030b0359a54854003142d18103040b00c0b542c5840c400160008001a20f00001182c401281608040a40302c6000c81d5890003440c14407120030070400c8080c1c01411030a13248030381e0352500002e442000252900c04c0c035003d690703003220b010303440204074400e000c80c4903045444111184140329091442c00840d111100714180080d000020714419242c6121807005a51405040c3e80000a490308120003800d41c1c001407654000c5100e0315060040c002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 321928839 1250 321927589 321927677
    0x9060901052205071e11030d0b01051306051917040b0a020c1f1103061003020c03070f06020a08090c03120307020c030619060b12040204020d0e0a0501060f0501 70
    0x60300c507030940420042d08005900c0c200d80060640009039889112170500c40302d14140031400781c5041b0420075503050042d424100101300310320040c080c2254030b13418414140a0010192541d030302901c098034443e641c807925449907044000c021211b2031b12010601020007140d44800f2000074400798055000482c003007050300c41e481298000d03c25079195003182c2c01122038442c201c0181c1b85002e03104424845082001050000303401e50039000642e0420340c00a445450003402030312179005803042030f40f1a401d8034a090043d40d1140001d07041d03d2412035071079401244800b85550032080032513024006030081e0102c1e1241d500000d444119041d120308000741d021001c1221140308000303844c0240005401c880090900c1e010540329003c85010802d0414182040464021a03100980e00b5880301c02d100061030b9183c43d804c0101a4004c1c080805905a5924a0b0f1075145400c100440c0c07498041c0d800000e925052014030700c0480c5441d04004d06100181c4071031811103403400781c401010405032071a00a00c0c0300714 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 321930089 1250 321928839 321928879
    0x9031606021b010501080c04091104020304061515090504060617070e04060602101a030d0f05090402030a090b100b0a030e12040e01062304142b02040b0906090105 71
    0x68100030b06040c21160400c000481540110b041c2c6409404030340400c80c641003004245c03890b800000301a0040251001c00e40d0a154001e1600716111b60400700359009402d0041c90260841d41c00b00b1307000007014850f000081d800c0341011010f40010303101408640c1c1401c40107407010150b02d8110b4160320020b030004290510a043c203e02400c0001e2050047d2a50303007900a60741e21102e40302d8110540307002c0b903082c11101e40355080d0f080c2a002901901107034202c0901501c080900d58601000c0c000100300458956a461004512130b140005c00001c18a100303041c00c408402e8014401105001041c0d000e2000c0490b00c015100c0f40304083c030b00440c501e003144111500b004001e90845001d0381c008240490036142408450307042e00d081e0764594224040d104c0384c40207040100d041d1078110304410030081c01785448081c90501583d0000d13080e03a001134001c2d00c1c045413041504005421400050344807034110300e01401015240d2404503a080d40c0343c00c21400040d0301070717018450107100314080f1a0030700f84602c0b4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 321931339 1250 321930089 321930097
    0xf10060504032a0902040503010e0703020102150406020706060605190903020603060409060902040e010b09090c0d060f1b0306080d0c08042c0702030901030c0203070b0103140c06070f060605090903160602 89
    0x20b4980c1903d2200e544400c860060f41150081c14481d5080c0070a1700250400000d03031100301ca8050b03004255104210f602160001c10150060307503090703000c0100501091090107900010400c07079541d20b58907111601455213000b80280344508008100d4810409a5202d4058030741010b01128000740702075061514000422118800a400074207007408148820f5065003c80d1042c40156065081940d9140304e06441700c02e800700309503107c000c94540c2408038101d0340c80115415911000003aa40600f044d00e07186180840c28800000303500c0304400d004802d010b0007020307580c0010741455500c030744c1d1550b24a09a0b00690049410350550b0003400c001000c0d8208102071550050410f1904a00701b1480080d04d076400900c01034003190810712094402c51001080799081a04055980000e90959407940c0e414500079101c4081885101080f40c0d86a982600500781280700345804100b084603840c151003079a007a81d04c054840c154640800100d2603001c82114603009880001c28408079291401da002802 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 321932589 1250 321931339 321931403
    0xc0320070306061203110a0503040e04020604120b090f0c0109140114040e090606090601120911270c030907060f03020f07050f060c0c0703030806270f1006050403 71
    0x810f103980003402c03260400311414003501950750244e0848400b08420f51f40e0f8a65038000701160700c10403007006420b624090b4a9005072008005520f060381d142000558101c0142081d500e051f1020184000003408005950071040300308040c3c070025a8000010301b2840301c41c419003245101ca0720035282c1982c803a069022004030b0400105840ba516030704101d071a00d60484005074a4840d10300410818680030715014800c217016910b2601002344890000040c0ca841c050807920702d51741200c02c0000b80d440001d1284d401540e8900c01e4648641102040f18040000e00446d508500030818000c184801140c46c80035681c8a051400000804000881c02886119144a00c0140128101c0208040032980c0d6011444003022140d254035040000070280c8180b917002d0174079901c001400c10002c2d0081340220f501080040180b4042140d401034402d000030801c4582140351000020014080103190f2070b00d82009848403420101030410703001030090310440c000901065203c41c2101e000108071540340133100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 321933839 1250 321932589 321932591
    0x607020409061107120513170114070e03070e070905061b030304140c010905220b030607080915010806040b06060702130f0f0510140d200901060c0320070306 69
    0x541440107101540c201840840701800f0410074040403c0c4298260741130f10b0382a40009154514055a201500c800c440d2300c07020075500c0b400d401c0c90100e401e8061500c18200d40d120f1009804080c030030503007000100d411010041288200303010809911020300c10540d042994034a80d03a80f1006c100d80c3c99801d44072602092440000104070402a004020b9a011400c42080f5100b89440b40d005580f0340301640a2150000c01c1003080d800d21042000c0c540c00e144281040015640c00b5506c00300e0300b000310403101000441c40d02c10a001c2003003010085841e0784510f05200c4100c030750400d03940d240c031034101070030140110380101b002c20f002e1b0351350350102c0e82032a900403e2407416441075603e52001c0c1c80c818480d0356019180c802020707021207c03801290b120321303940c4410b0b034105424040c15000340b140c800e01d12504040004000400600204075901e204001120002d81c0141c08904100b500c0d00c05030088420403440081c0ca0000a07040070250041c1d5450f80c01e80ea882c1a40100c0303451038500705d0b50028000c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 321935089 1250 321933839 321933851
    0x140c0c19090e0307030f050a120f02090607060506150307170417031003050c031f090314030a0504111c02151306051305010203091c0f123902060702040906 68
    0x442e0001000b40941442502c03107115140c0004c50959180c003c8031141b10204014240c08001182641d101c00720b00d5500010040c18200c420001c10b50703603000310b01c007104c05c40d580b441403019618200c400c18510802040400c0e141d0300d00f01000401168403407500c0ca9840405c100890200007256070300c1c45090310500c42158076854412240d80074140584421f42c1d4a0059154003000c43c200480d0340711100c0444036040c1120002c0880c200d000301112802a404c02c4190b600c0d4003e603003048401180206440c0c10f0201d0303c0d0800d804c15010440d0b00c0071260f803180d5010071000c0b2103100304041c00484c3c2501100c00c620703800c04107031f0016002d100b840850900c0810141c40460825000b2014240021410101e1001c1c81e4950300103a80d28030689242c147d101c840c070301306100c0b04003046000c00c03420707072152040e00300000b201d540c0c000508246140e00e101148010300c07400049144184031038402d1008a0a6255440c80381110032080700380444040d0181c880014400150741f1513400207058154072403010015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 321936339 1250 321935089 321935111
    0x30c12080f0d0c080601020106081510092309010207020a21020405100602010b0a05060415121103060f180105010c0614011e090501180207240c140c0c1909 68
    0x62420300e540f980820f4000c8041460b40d407051013603209444106000b8080080800744007509081c004090020100d201540400e403420b8074011060401440d10002c1070485156039000003541000740903e6203a0701c103200d0301c0056611b90041508407181d40480c1042021485460000020003c40c06904141490306111110600c006e00d103085801a60081208009000c10401070480a00c80c440d40300a040c00248101c90413440c000903446c90508010710311101c00784c540810b07208240c6481c0c410500c040f003005040d04003d00145186a002c50340014482c03441e1580007400c580c18010340703042000707001d528001c0150552100c500c01e28041d5585046607541c4039198001e1188100c8445102d4107040c00090401881c00f48905844440030803040d0580c04022130402500300031400c1e100b4480705810313106454100100751007506002000450810360100e000f40515541030700300d81000b28100400380d02501c000c102146001c40498040c2c080c02e0f5500d2909540d40303034a810005da494944030318826 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 321937589 1250 321936339 321936341
    0x305190e10020f0d05091819051501170709050d05010c030c0203130303030b0604030219050f1203042c0a060501030b0a060c030e0103020f0a02030403050f07030c12080f0d 75
    0x895400c212030340e200e41240c0703000803602d42c82c06980c031548941c4101180a1002e000318090300903480d0190203001c01e400c5151140c0b11454064901ba101d07000c00b41c0c40d561a05d075050150a5211198004c1c05040722403c50000b030800340000e001000c0ea108201c040380c1e6440c0309160441c020174009007468004400b500b8a5402824080303805004031b4500701c07c1111050010050750741030340303008140811452454a06401414211054980c407110801001c0010b0340c45030744821118002c0340c07044031810309080a0210400c40304070781c0c0e0312601c501b803651034110500004990999404405603444404d140050340e030051020590400c000d5040d02c204000c1c11201c1c1c3c042011910240d906000301d41c201001c2c8181d0700b080740549000101c1c620340d0750300031134051444441030343c3d0180750041c84c0480c8500d801e00d13540c004489103001a0000030b42041844004c10010203010f40c2d80002d0241c8514580e541c0d40d00341c1192103503a00d040e101c500000c0c00d200c20141582d4000d0b001d10521a550f540980181c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 321938839 1250 321937589 321937607
    0x408120903040f06020721170702131d010e0606222d060905060604060c050f0d020c0a080f15070c0b0f071704030f03020c030702100206011701140112030519 69
    0x4a80c1c10040060039204c0c0740d1031180b2103922303030404510f0114214000c40d9108980c040c0400f0380c0c1208070001803070703940c040d14400e080201300b00385990009481c020504500752082884001c45681c46070041c00b486036a2150000d0514529a0058000b8030300203072042c0291071400203103100980c0901d80d0b00c418840381e0403078484034102001e041002c0c03070321020400300304d400540d40907410600c2030105103c020b0140301400e0f4010300840c210f901d04540d1640c4c9a00d0b24a814084c03030010381154400c004103080194403070340645880800381c041403800a02c41a500d07106280e00c100550140f2000c01c149a008801f402e04c0b00741c00c203007070300b08919210503441a045400d0320400005003201444000e5001c0981e880c07801543d05a0f61010b50640d0080120b0180d007100141c2d12260008004040042c2c0e5a03413a00080705c10903802600c02c56241c0000c0344030388801f120051100ba410091586c1d191032120280c2c605498034142c0a005808150404070b0315801940340405181401d00c06260140303420940e90 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 321940089 1250 321938839 321938849
    0x7030804030c1a2502040f0b01090806251803080a080a0221150405010e09011b020606060f0f0c0106050f010903020310230406090501140408120903040f060207 70
    0x4492543e500745401c840303034444240d0445003400344500031400036007003030300c00d000c0c8484407612003480c40c580c00090454202e200c00205680d82d0745a184120750704058190020810040900b0640c40d11014410342890004203400441c1c00c001500e5020380c0c001c40e4001d0b000302e800b846501b100b503202d2401007980da0103000d000e0007290903000000d124540600071503010a02d040c0414050003502a03045100303000140c06514503c8421701d8410f40c81c2c490b84696402040d101241c5881804c1000121303003150400140a2000e07910b140780c610103139400080c0f080c1c00c87d000766102a90b4250709512441140a80302d121403940e08005090b00c0364904c15003050003075032030031078100c2c0d2021460390056074101c20603c4000c1d05078000041c0000b4900941e03000300c1841d41e0920a10240402c0f181d2181c50810b030444089810b2a0f0f1106210140082449409405010b04c0c40403c202d043c40d498052a43c02841041c1c0100804c0e600001c011900a0040d21300800809030104140783d00d40c007010351281920b02030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 321941339 1250 321940089 321940103
    0x70e0a090b13020d140f030f0403060506090c03010e060d12030b18011508040507031b1d1308161e02150307051b070b070b0105030c0a0e0c07020409050703080403 71
    0x41194101d0901850042070ba0040c082c403903014140e41d91001c40f161240905d00c0e203026120100d03200c90010310050800c1190b00020300c0c0ea5504615140080f030340040c2105e8011403042040021300380c07546086a040d6a0396403000200b03a992078001480f41f4200000c02444000e5008550f41c281d074041d0492095514121201c180c40b000c0d841d541c00e81020244281c50740036002d10002440310b8011070714075070064090015510201d48948920402c0b003410441c00c20f070524080010002c18271040d145803041e4040d095660702078145170415840d4517078503c1001e444a800054000e810f1040003d600452540c00700a8600c031501500c051345140351411000da0040000ba1004401c14800d40c081313920076411303a1102814001a018103441600441c072031071025104080011038a100b0381d90103880d0a0f84140c000b00740c550304120502d41402580a40079005201c000b009020f400d01c182241a0300071003010500752698414000580a0078401c6006803141c06001c40120602c480c01d0020700030b032401195 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 321942446 1107 321941339 321941341
    0xf010203042105070b220b0103030305070f05040806010e100905010f0311030105090d030e0304050405090307030905030a110105030703060b030907030c08030405060708090102070e0a090b 82
    0x100d060714010090428044041c0020041c2240900300f850114101401d0341d45102a075440074082696442c84000c00724070002c64190030859143d080a40c038205942d403400d0190080c5802d42c2d0200004545507101d010090003202210300b10bd030140c0007030007280c0c40c190845040490280c110428031310700c1e940c00620007095001e228060f21340c184000d41c03031500c1e620b4122801c1c2000a0460f0081e41008200081c0032000700d0941400300c958100401d501a071604200d0840c801d54109940c001e1800c402e210010324000b014000c0c040c8a2303110300d544a83c4507420160340310300901c001814080c140c0c9080d96154440c0000d103401000d14200800c0795901c85010440035001214841030030340c401c01d002c105100414600400400c01b01000c0d5140900740008035016202d4524091320b020000200310380305074420801600108507003078200c10107081401c0090084c041900f016121031039014 = true := by decide +kernel

theorem cover : BRFrame.Cov 321762589 321942446 := by
  have h0 := BRFrame.cov_init 321762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 321762589 ≤ n) (h2 : n < 321942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
