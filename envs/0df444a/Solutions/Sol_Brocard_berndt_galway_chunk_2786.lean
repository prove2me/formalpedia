-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2786
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:44:28.134261+00:00
-- url     : https://prove2.me/submissions/5b244e52-655e-452d-882f-a76770ee1902

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 500899280 ≤ n < 501079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 500900530 1250 500899280 500899309
    0x702160e01120804090606020c130c020a0209063d0509090402040e101a211020070b090705030601080705040b0a0506031f0501180306050405030c16090f0605 69
    0x2010002042d0b0070607090a0141d40c00440d00380e0309140300002c034954005a1070082c0c142c01c491103d100103c0700202001c98000b03004c0c00b40542c001c06215005072924a02c000c0d8010f801402620b4410011003825901c00a4180380c14007068403240b0b034280b00d50028414030031107071117400d1052071301d00441d000420390200144004e12442d19408100d204a4091210200c0354209090501c40d000761910103091850007490320a008140d605e074401c0c00c000d600e860103880402c2c42da0141c40da4608846012000c0d0003040038104a41c525142002148050400100b00f810300464025800b801c0410b0001d080111641c0010701c01c2d03101d900180228038012903c5412501d0407580018440350100c0800c9054080d50300c000d0703204001004100c4a803080040b692591600004040d007010380b240010740c0d0280010b000d004a403101102c060000600310382c407454105000780b085900b00b2000c0d01c0014506845e009200841341070b00031003005144894015030100d548128800d00803d401c020120b035020045c0d80c0c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 500901780 1250 500900530 500900549
    0x105090901031e12020d021506210c06040803071a0712050406060f031a010902030c0f07080d020703050d0c262e080c0f030a020d110303070303050702160e01 69
    0x810307844061810968603140313980046000380401d510700c0007075103d800e144642005401800c04186001e0800e450003446940c0c0100a4403000c81003130503002c00c40e07485c0540203490b44100505282c0583d42c03500030b84014900c80317005640d282f4003450720451414182107801803024211040c0701640b50005a22502c0c10302d0900000382c550740d5800d004024002c0c99001c5015481d106401105004ca06d40f402c0400c40e1542c4180d24041e66940030420491004403000881d1650610002064000c000018507402e801110150b0801e40b010000a080760300030320084012036030001c0d00421001c110b008500701c01c00b484c10205003000641070046c034240f0000c042c074100c0d00039800029030440c2000e00c04480349005d10780340840600302d07000401580b02d00780c015401c151242c000a2805464282d0f100d2000030f20241c080e0000c4800d5a0a00c04480001d2400310307100c640c941d06101140c0c130100040d01602c2e010343d5010409003042c0704040d0401c070f00c1c18040790920000003010b00c6111081d0092504440c000712 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 500903030 1250 500901780 500901803
    0xf07050706060521011d120c010905100203180a031d0103090506240a0b04120804091407081312080c07020406030c14120601031e05101a010509090103 66
    0x1500070024a140c0d044207a001c007500d11180110025001d101a403114400002c10007196207465009010005082e1411070b58411300d09030407102040d10203010708404000010440d4042569043d0a003d0580100001c00341d0100400110321030100c0003c05614035140034100c0e00030580c500030500c00200300003052416840c49010166440303540040c3d0f00507044420b035141c42c1021104108071622004607643c0998200c4038010261616035802c004a40d0101c010510f41494041d0400e240c3e142840d041d01e8001c01031000048200b183d0140c0d040f80b80c0400e00124051505070ba004e024180050614200b4014140d0302c40c0c00140c544048a06500c00342c28110903941e281c03070203400940304400e402900142012000000c10040e10070000a4039040913030481380486080512005000c061041c80c456400500108085803c070304e401086048010403000008215498603850560180c00c245801680c0e85601c1086840c00c210b6400601c4003460414500744d80080068150030040c00044c24806410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 500904280 1250 500903030 500903033
    0xd0201062408060d080d090201181409101710060f030305031308090301140a0506060c2505060f120a0e15190c0207061701270605030316060b06030f070507 68
    0x180301e00c42c000c55024805c036640704d00c0e00e00d054000d0302449804038082405098242041c442e0021a0016500340c0c0d45400c1204503150700f00440150080c080750044194071102041549010140741c00d10885000142010107a88008008440c2c295010344d80a4006220500009612804503070700465407083e000349040c65402c00784c0c5540703c0d000855615610f80080c10310045000c640c924880c10003c00d042181742e40f6001030101c18803071070110100c240c0110f03c5040003000b030049801940036070f6031001002252070b80c0101d2816448041040703a00700700440c0300001642d108004650110b07034030310107226032444404140c0d52400360816807910840058002007d5010868204e000f00c501c012052240c024149000794950034240070b003500103003a00681d00c0602e602c26944504940d49000c1e00250100400c0c100c1000340991405194030300d886100010f075603901000904a858031010700c4031a80070b80c0b464140c048407450041c507405010103208011044000344800e541c041014100715580f01450f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 500905530 1250 500904280 500904289
    0x1501030c090905100801050a09030512151017060d0818010201021c0b090106140703030b1207151d100c15050a140919120512090d020106240806 63
    0x1d40e0480d4400d14500410840c070f480b000003000d4104c5045600821094840c0900d8905413414035402074086401004855000c8041041d110392000142800400c4030200000241e801c58040044000140140342100e61100901e25055080704080b2035450811800769140705142c012900c41c05000c490134030500b0b0b1140d0003901166140000c0940e03050205002200c140d0040c10303003d6590780100102c50001c10410300411007500da4882c02e210b0241803120543d8220084c1100c0a1a960003400c602d58444004004000c540054001c410301200c00b4469100e000f0301413011464011449048001d80040e00d4407000314a2107a0103191030700c4071204002d0f06082d030200d129000503180b02c0385098200198821983d0040c0c4940b1045c88051205031640c1c403a05030385a20501500301c0e500161014100000d8128401800d00a020709120307046c1080da040030406003c0442d910710407504520010411694280300300c6000e012041d285420300c1c00c0ca0030641421201c001c3c40c8005002011000c543d05644 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 500906780 1250 500905530 500905547
    0x37021504050a0b04030b130b220210111903050304260c0a031706061c2c07050405010305030a1d0916030b0a05031f060e0c071a1501030c 60
    0x4054001d2204503922021143c566025220980d0440200700214125000324640f100600b41c11080315856a2548002000d00b60744018805c1c030000007008400700141c55841600d001c0c41020b0326284200300100c1d0074581130a50664050020498160500300002e40001c20703a604907401201140204403a0b41c41340c81c40c41202501024100c0c8085503154080344002074184445102c4c1d604e802c4a01d80c1c1c0402c0320f90300301040e26004c2c2e220005000f000000c5000301c0414840c581265000b0640c0850b074140c00c0c1c080703095071b00b8554802003080030403441c440080103c00d00030318040d541000030f907246490321900e030b015005135a4104410000014540c0d00001e04000c010780c0300804205a50a100d50703422071001014180c07401007824001100181e00d0020007d50423144054050050305d6101c00d541c0300e070301c2c01940d588075903903540303042c0030070800c4480c019148142c100144481d969030030740c1000c020203035100307400c0d40a1030a41d80412240707041402028400000c2030802040e00407120509490b00c50 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 500908030 1250 500906780 500906789
    0x30d05040204200a0e060901170403120608031209030a1b1403040e010918030206070e060705070b0901120204050d030e0315071808030f03152137021504 67
    0x106840070740311420b400d24024828000103032141d400507175140c001e03c4094026042a00c0c041040c0580700c603418003244030071603440391080c039080842c0001541e0706000c0b43d2060300540803640c00030601c2d640b5208810005500018054011400c2414041e40104106188010445134030320120041c01040003054030304030060040419a5110303500c0c2d89580d010710b482446840846c50070b21120164101c0d800e4078084d1070035010b038040c10f61a910311800b0b4503c41401000260031540811042c030100b10140564400f401080001c0c55490329180700041240040c03802850005104000c02c02c0266a0050100070701581418560480448100007a04000084a104000c0401c1e5800c210782e0540c061451217482c4024148020026144d8030325543d00d00822030100e002040420105070203070071400d01407100b00c400909440071822402074031942804c07400e005c2c40095022101c40340d00291840042c030009101503111400e82480030844081005481d00064011101104441001821041114080c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 500909280 1250 500908030 500908061
    0x21f050403080309280c03110a0902121b04080304060f1707020a14010e060a0f151203140c0a0f05010e0a050610060201110403031b0209070509041a0102030d05040204 73
    0x2440e0010300203484465401980b92007482d00340d081178a660342043d038880b410b50403440401d149815036494200001e0050074081c3e100710800000a4621613030b000a00c0543e00800101c4024103107062008061110095001e0b003c01041c002400342040c0001914100d44007481c140032142c030000c40a40301004014010044c40b80f10208000829400003000b0041c035101d001c10804161141515500b25070504410050540007440171510703000d40380d008066140c0c0f40d96400511030003d50600d0840c900554042da161030702140303c0005054114071040004620400c01c03078604a00190b4460311110b01d5000108402c46903805076052110075030008004004210407124214110b04050359142000c40e0844080381d0140c074040f900c6407060092065403c00ca4241604040c110340d4242e0701c4d201003030031080100031014841c0c1c001d690790780c0c25a400ba10068907411356803400b6000303100c00d80d0303c040302c86407110003143e10b01081070741e00204a03216602003e030000303115121480043c01600107001e040154 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 500910530 1250 500909280 500909287
    0x30406140a050714030315040c090905090f010507091806030b0703090c08070f1707050901291c0f200d14090c010906170a1a1f1b021f05040308 63
    0x40900000003140620b00084080c88040c41f28001c0006881c00722032020b0025004910800620240f9000079070800e90f0306080d6403001c001030080310308407541260f40c4400124690005c05c11120b2089012000e80304442c800d07c4142e00b107480303a000012018040100300341e500c03002e071b409104043e06040c000d45025410740e880707070350b40b200d0b07503c80f8040ca0301072400183c1c00c10703200c64042c03c4d0000f103074011251701900c00b40b001d038a030104151100d00c02e0000c140c03c0700211031401a03c034121034010000200c4444046d0313070b12404001c0800c1201c031511110400c2c607103001404480480818100002484010503440d614019030744241e000d4040d8450078014040a4400d008031010701080360310355410280d0310127250559842041340c04036035185520081610740340124240386102e801c908031040d041c028280c10b050701580400c1c030f80300a034004441240d9400f0101444540d1011000d440c07010414403050850040c0d8001a260280d8120340c0c00040c081c1400c240d0400b80903206640046811a00700742d103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 500911780 1250 500910530 500910563
    0x3010c0306060906030605180912031317030708010902030c0903030414120a0b04150209030d020a0210020d05091e0a030803040209101805060f060d06030605010602030406140a0507 79
    0x1d0940c600903540450244600801c540d0302c64070940080340c00041030030b80d200002509596100b040901444498012103100400c0e5104840096001e51340c8401c03045100c3c200d038207080e020780701118141c4040c10020800c0c00b0140e40d02c0f0b402c1d14152010b006006a40b900d8400750507003e413241c07031282078142c0000f142c0082c0c0d030f00010003921303900f880c107460030010107440341520790b255450700380c00525141c40135000ca004103801910520045100802c014079045134540001d1a01c180c2202040069010b0b60800007141403920541e448aa9680004c3c411205003107005002da0041880c2da40c094a5100c0030141400000700314281142c20241a02503015102e09052030103a0040700d0980c02070710021b020400811109040301d080310b009c1d801e000c041c0003c407001c00f030242c0700282056500584080b849001d0707640c0d00d001492045520035001500501d1032901c0416100140e008109541040c00700b04000c6e0780150205c6008010f8503503280e81c81d480320600b85c0c2d03103010325407001d01440070403652000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 500913030 1250 500911780 500911787
    0x90e03091020030c010e0c100e0d060f0c031406030d050d060b0406080406060b070c03021306030b090318040b06040302060a0908011d151b090a2117070b0f0603030903010c 75
    0x8035100c8004002d004011180006e039556002000d1110f4003c0040c0c40c039850107a12811880f40d8895005081c0c407a50202c5484039000d80306d1041003061229501ca241c480741c4c540500c0703a40c1c150403c420708485030346032540029031100403c4105500384100050107034407455990703210f0f002900b0254202074403540c41d04c01c010010341c000c80e001c895161400002040d04004c8070240c0d040a940000c00e009040d05613424080b42ea6036807106084840c0e1140710100c0000c80d004170240c0300d5604039009549030405980c0502e1240030000c0c0a6003d10728243c2402c0c2c440e25424102c45c15130b030301602c0070755807007020740400c480c5051590b2000c00c09518009101d5038085054810600c2122410100e480c18000307020900384062003aa0030715100d10b103080003860b400840070040d05568100800840c0301e039a0352808031650301455010041c0501d4040110300402500344a08070800d181d10f6811800c1102c0743e0f94680d100040136088682010072000090483da50810803905c8490b005402440103494040015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 500914280 1250 500913030 500913037
    0x5070206120f04030909090b1b0d0f0b0f090c0a0f0225051807020a1b0b0403110306090f150a0603150f0e0c011d0a0f080a0c090e0309102003 62
    0x2100060f65410380006c103c035040c010001c040f600060002450340b6034048001010340e5038650940041014010321aa0b081c880c49011039440000b000402d403d802c9030100800084090545172003403070050284030303000c500c0d9030540c0c40d40802030400b4480c01c201c1160a901c0c00c600c0704a00c01d961070602030105981203484010000300c48040d54100038035845c81d90894a010b908079000390069110120f03080c0480c85181c03405c15005c100001c80300c40c150722083c0110440d0f01581081c4c51030000e0003418030281c01c0c01c201281c4d1150022019001c0c5458100001c0c1d110240407010400449120f00405e10040c80781c0e0103000116032212080c01c8219651101e00d0260a652030401011494507d21852802c8041060950844141c3d110740221000c4191010010034041d03103213401c4010860041884904603090303402800040008055030b0700c141c641002000c3c81d03504403441d46401d0450392100c41700f0005c281c0d00030341d00c116500341060803008000c0391004610404d80d0562442d5603444980304030080000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 500915530 1250 500914280 500914283
    0x907090302041d06070c0c15031508012d0b040f050a0b010206150607140a0f051b060f03041113150506072a0906090b03010b010c020603010605070206120f04 69
    0x40c01603e90300714a40c0781d40140340c03000100c1904944005100c25120760700704907950b4400c51901250540b0b60750540c001c49815607015001c299184c020315209c25040718001e00a10996000f4003c010141c81e211043c40e6070603000925000810100c12400c0d4400d401c500a5480c01500030414800d004000c3d801030300007500c0c81c00a2a10740401c8054a502c00b1a12a2140c500070540c801750469020501607954031110003514a6540e0840030321a0030001e202040001340907090400729a40326003000c9017000b18500380c4ca050031180207560b0700907450324819a8944a45002d6564403565079041104c41110520b20499002071a40b48080c40520b09503c581002001010407509490b100c07400d121081c4aa014080c000034280c03500803c1c401c40c0d000d4404829080c144c101002030356540f6101041c2c0e001d54000080941d19a641c00c58613040902c03c1d840350380ba0901c0e2220310006207402081f514401070050004005001808038155221102141d40030711880b084040f183c0381038451174400f04401e0302c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 500916780 1250 500915530 500915539
    0xa030207052d0607020705060a02100e061f0e07050706090b010320010e0d060207031710030308060402210601090e040f060e0303040b150f0d030f02010b01030608070e0a0603020907090302 82
    0x802480b00076001601920440309600240011400d140801555400502004085201d1070b1050001da220a000d04400e03c200800104a1030400300c1040614000f407401d1010700f0199044100032482102d0300803600300c111400d110f56125840e0501c1c0002c0c281303550024050351103880002040007903a0f6503940921101c0b0b80e4105411258100441700f00c28500c42c1668442d082c80840004900b4a50081000034801e0030074030315501300d010100480e200b003219207a01c0d0340c405041c20424103030001081903100700c040710708615040c0c2c050281c50a2241040201c040c140302070b0001007450740140000405040420b006605510b014035002da000c501a03003040780e01608080044000702c13000000d40380510340c823a85000440c0e8a6600c00640c6000034510f981c0d10179030400c142008c507259802000902c81c000d9440482c107541d0300c04083d0070f5401314000141010318100040050a8001c2240c0d019942191071008058850071030400c050901500080c5d03011812030148404a90401c1e022412603100742d6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 500918030 1250 500916780 500916853
    0xf06010521071e03021c11070b010e040b01050a0e0f18030403050703050709090221010f020c01051e060d0b0a0b04020a08011d040f0b07030f0524120c060a03020705 72
    0x160b0850690042c040d80e2141c0107100070002500201b0394106221481d190460b0b203003011200d841d0800c80540c00c0c2e01204420200d50107200078032020084ca02d001d00002d8548000c1070746018005002d00310014451040d0b1045140464842c015820b600c40150342407000301d0351076680341d05005071101000c0c48111414494080c2c0068010242d001c0e107510150024089108030000702420b40303400f1800d0090311a9956282e00f0794104440d144003030204480040000221890550310000c10400148a0203030316015040800c103180d960801ca003808550f0012202115451b01242c040241285e5482958041c0c000709600d03143c42d0384681c1850403140703801420080341ca500403140503500c2c42543c02500c4ea000109481000c110403524107600000545800142c00280d1440c1104a48007941d1841540c80600c52500001100012103070b486003007200c6840e888842103181d6603541c154030800e5800796001213495090740e07000c0d505880c000d41d081000d8403801c0041d010f014039101405001c042000c251007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 500919280 1250 500918030 500918087
    0x705090109090c090614120a050405011d031c060510030c08100303020703080a1701080f0705010e03100e030c0105040302011424062a06060f03060f0601052107 70
    0x9003d035445030025611841040d608005085034500c100302112046800104001c00350444004040c500ca0854240b0025040c03c013480c0a90035189000c41060110040742411a424200402150100c4990006c00310000c40e4042204019200e15806564032003142d1100400e2240c041d0440782a58100780c0c0c030201165a1071a40c1c1c44452661b001c0600181e00c0054180000750a180c000c20381d4404900300101c10207084004104e1046090300140030542100000540700001008003d0140000b42413006d00c6650403004a552030049280d185401c0ea19050344000b000c03414130031111140ba0b040001d0240e4038103820068041e0030b03d12001e5107204080030008500b016015980011382c1080a5405003c1c5084000c02000350800350380490b071105540a895000c0c074809440120044498001c0d12507417409a00700074400e02034001550103038005000700000c2410a04d99983d1000007401c1407900c0d001c040e88071609100352045181c61079209902842b66098008140419145541c0b01644150301d14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 500920530 1250 500919280 500919299
    0x90114010311040c050d0911011409180a1d030903060c04080615210a1a0402030717030d0e0f0c19170a0b07050304031106010e01061809050705090109 66
    0x7403002514184910300900e81d145400d40201d12148241d160141c20024600d07801c2c412035061820854044a58800800b03655811214113070240b0015408581401c08510100b42c940301c0420341064600f03440c0d00003512048550740030810f00360000c0c6155401d09590880d003503072030784030500651080c803650002540445840c8211815101e003000504003a4883c01d500517a4800102015030b4041c0203c200d0050907401c0c940d00c40307458a030002c001e041d4940103081051800c80088100b110103200d1804000141c3c0340011000101c4000545604030b59115444503401c1d4050300300349001b181e003044604c5107c80000a02001029110001e65140c6c049544c2000740112400120104100203840b08201c0703154070f010004c0700c010181c4148ca00141007a0366500c19200308850140100b000403042c03005240c0d0105850703e012a9540040c03440d9414043c0a6140b0801445003c0800c950407545822070514072401c0b8004000104082c40300341000070001e4000d4210044190000c0c101003c001088501c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 500921780 1250 500920530 500920571
    0xf01050301110f3a110403110919140421020c1c0602030c031801090c05060a110111221a0f1c0507030e0a0210200304030503030901 58
    0x50484030300345045900201d483e482e400030f80340030070040030f0369500744603c0c00e8460b10701c00c1141052400c207101070b4490000204071142e11510340b007000010f03c0103000080c8100440c0149807002c5680400380d03920b4400c6040100e03000380071540b181e4106a22101074440d203030900340c0a544200894503440303420002d900106c1070300600c80801a0300c00b0321003038503e0500c0c91180003115100b1540c000b1041d05a1117078026a401502d030088506000000c1106d41e14070652900c1043d20000020300c0008a01c2e110410a0039582c064a0710801c000148840038500550b0300e903c0c0c42000b400240a000c0e0030003035126860304901d24070070171440c441010754031405180d0500d4043c0d880c40e4a02c03001480da030351760b580c5803604549802d44c0d00d00410000c1010041c0f64124451503805603440202e600d00e080540201610901405650702d075000d10079600046e03407003400004206102e807814035080701001c04400d60a44480c858080325001c0080d012040c8900800203510071482c4100a02071030310501c20701da26076074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 500923030 1250 500921780 500921801
    0x80708041a060105090915040c02070b0336010e070b1309020708120115021006060f0c0510060e040b1005101d1507020901240c0f1a0f01050301 63
    0x88048018a040c0750306062103401980600d0309605040751301d0041001c29078142ca030641c0380e0f145d111060313140749032900803844440324500c05004014079185044416020261505c9007074402e24180c0c0d5000b0414030351180c8070802c0581840344400010900c40c0c001c6c140904200d085004400d408207510341c620044076940482c0148410300246002c1c4800300940110a0480d6140020030003015121007814102d4042d104200e5001443c110007080a803602000840d2011158241303101041050b400c01c042140d000c40509207010f6200d920702e0302d2420107000030b011a02181c03078041c02058415128881e24411842245000d10607203c04600e540000c0c440e100740766012044194200c0d45504c2449a01a0140c05403540100210601c0c000b0b150900001090006100301080003020340ca8002902801440c002c0d54047c440c074601c8844001c884201c40e0740c0382c00d1000d540c4001c004c20458030302d0081e1098010b80203103981403441800c8611a0300907503c00a12506800000c905483d041c450070780100c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 500924280 1250 500923030 500923043
    0x1e01170d0203090d02010e0f043905090d0f05061023151303050102041815050906060a05040801060b1309020f031b07020a08010c1b050607210e07030308070804 70
    0x110317401107618040c030400e9690401c2c1e440c0c40c1031130070352924099042855213a40f00880091542800344411844a40c550485108040205118260440c0c100c60720740800751180e41e044003040c241198100c8100340014884c1c0300f00000c0111001403003204400355801c000301807442410b18800800c203501c1144186038080c001c8032902344200c1d41d9100605054030032030703e01c498559598913500c0c00c98000f1b40c0719070030001855841041c2d945082c40b0b02c804110020780d0200e615414640424110880180100c1c000c20000031510202c80c000c0c01603800400e0b41100900040351100c55078010f41d04000c1c001d4205411580000c680841940203071048451a0f001027419603550340c42c0c601e2142102048649002000c01c8104050b0311440c0483c00580503003c00840e04079000140146207403030403051440b003a005400036200143d8003280c1c50303030000f5003482e044003414482405504000c1558085041203898150000c8081101103908000c0320b010f512420190740c2c4103603041c0e802a20844008120 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 500925530 1250 500924280 500924299
    0x8030703051b040e07030b042306010c020405010305150c03070503060607060204030f0f0b1f090c05040e090d020d090501050d0c020709060e01091107030206040b1e01170d020309 78
    0x18034481e9100d950720280c1044403402d00091075a040020303900c950049000e0007912030801680341e4060051142c4800140c03010801c01260f00e40450403c0120b00203501070460044c04103015a128600060302c0031f1300100304004e07650b92072800b265a1021817003035130040a00329000a0000101c2020b41344200c0b410f45507c0d00c0c50f1340c0c600822103d90300005044524960034840440880c1050705030101140c0708400c0c1603110f2009080c000801e800040403040740100c0215030b109881c1c1c00e00e144508460255401103281081103c05075554011a0060225404180100f1098800c00603021001209076020b640b1410702c06001150b60030f1113405071a010881c02c11813800103158941c03180c00ca007034051042d03400385501e44400341e0540350b40758850580703589800014010060a0301c035a10f83e404600440d00c0c540040d9a138080e4881100500142c5118599000506401e40c0074403400009401c440c82000c1030368594041c0a2800c0c070280780c180e0b4904c02d2005140c07480c1d0001080b80c50360038000303243c01e00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 500926780 1250 500925530 500925541
    0xc060201021603032715151a090f090c0a030f05010f1401090b0c07080f0303060a0501051b060109020a020105090606130905100c17090c0a120302030c0a08040f080a0803 74
    0x25145101c0a490030707508880024640c541d851891045c2280f140309840c12000c00c1d1400c3c081550a14102c41c0500c00740118104010200b003801c0b4070702e08c084050229210380312040000c500c42d550761801c075081090202009040c08400000307084109240c2c608101132a2694908030484001b4040c900100205410070702542c0301020f90300007201d0052502d4044241c4071048400705d038002e01e20320041c03a4080c20050041d1042806650100805000110704500c1c1c01d0000840248051090368103000000810009615504203103c078008920000c0b0b500307650752100014002d60102225100552802d80810101a0042412409940010013400740c80c903180c0b04c1c0b1401040c030600126080d203e05102003000407210300900d2081c0d070303460f01d0382031400c2100d004030f598010000b00120380300d80114283d0714403031b9102d28000702510480104540c2090742407500f40d155200302c00e070190061154006500420450200030300942d000146401c8030f459035030b00825071b150f541142c01440ea03942400020b6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 500928030 1250 500926780 500926787
    0x1905070e09030d060609081e0c0d03090803070305030712020a09030b0606070203070f1d010e010b0715050f190b210c1201020a1b050d121509090c060201021603 70
    0x50300101c0d00c0c01a0b0746004100311510045070010f80c003500c08641c40e10401c210020060001c4560840105540c11100410440042e02c4226840456124458011035082407521860120001d84100c0382201c4e034407245400c000d8015002150310800244140d158191454031900035200300c1200b81d1514001a400c6a4484e10842c200410703d80d0403510034080503025170380422082c40103001c03900360800090300b88402084281e40002400c101ca91101d401003295011010103181111071500040d5107030300d501d1811103032881c01a9101e4400031300380400d0040c0030040b0700000d030140c034180007404000e03c0c41521b40d50948032812180c0d507205c610400c8165040c42900410710350204081d0503283c001d051100000d1005442c0340784030410341c2d0b0100e101005503810100741d81d68684004c421612b01c1e486075031031035a00c480c1341c2d0824040149441e4009403140e4560000210443c0e100c0c1c068074107030344601101d80107207009030090364014003103a80050b1850042c42100c00c048200c41510302d01c00b495490a5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 500929280 1250 500928030 500928059
    0x12022e0b1c0201030c030b15070b060907090608040f0c0602010b0a0501081905131a09010c0201060302060406050d0b100203130b040b040e070219030507050c010206060604060e040905030a030509190507 88
    0x117000d03d510741c580c2032459500c00d400b2821980083e01c92548a03001410802c0b14504010005400399072120107100c2c0341500325840008071662864240865940c40c03500824554150400602d11080c00c940410240e4042d042180301000680b001140a6681c800441d0050303015507410400411040146004407090340015038030590120080400c1d659a0707684540c24525100c1070340c1c000c00c4480a01100002c280160200710010744020301c02c003401c64000034514800e910402d03062110000c0d0180c4001c0464211000f03540004107000842402805d010b5101e40c05008100f03207013517103000b01091610703000342624141d4601183c101d041c60f082c5103800807a02030207003020055103d48100e007403860740b85800c500d420511030365940c4e8030740310f0900e059403604020043d40360554000c1c0c0c04001c0a40c075880c040d07400f2a4290f140c08400843c079040840c008001052028245000001d81c556072140c143c2c002c42c2c007034080002150400354201c4000840071100031001407140d00202e004026842d08085c1c0c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 500930530 1250 500929280 500929301
    0x31a010e060c060705030f090703120e0f030a0c050a08010203090a060e070e0c070b060108160e011106040506010312050310030b0a0209061801020c0f030a12022e0b1c020103 76
    0x149490b280480c04101d18002044442d07000164000040100043e80880c030550449210402410502c0c1540e4541c80703000041d001d00c42c03c000d510816002907503140c41d01e40c081c2c808040c2c01e45001c070216040c60042003159006150064603c2940007410007014803c407441a0014400380c9208090b960310070028000614001c03106103c2c0c1000400d01121201e5040e02441c00c0103415a07a0782c0040c82c004000c618020110f6040c00810341c20003c481c800b4402071701c001c110383c3c501085481100d9006941c111760111440d243d600c1503404000800c4400141e69059901410b155032011401c010100c42602c0100e0b1450080185000b00300b001802c03890b40b0a410100d01c0901504141c4000081030b0745400485600394038440c1020300d0402560180484a0340d40c0e030a860f0070302250303070380c10200707a4804c03003800c0040a0107880d141404246100703200c0400d42810308040201c5004050005000c641141c4c8800c8006030301c0c00203400050301d840303185490303400c005e802e015424a09540054000b013514821 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 500931780 1250 500930530 500930539
    0x915010912080f0c0c1008010510230703050d1802180423100f0203130f020604090c0c210f051602030706050d050a11120c1213030f031a010e 62
    0x84070080c0711003c0c0513024018a40c0014078848a8100c100040c01d103580c003000e000e0020031001400f207521384c00762100803024141020103401d10307100034914051140803440c042174403001c6440741c10941c1c090000c007071000003032005000c08103007c0c8204001c2801500003e40c4000c240a0a03561003c0f0744402541c0a40511481900280140300800e80c6035510380007000c940d001030f2940520191140308030500081c0c4040110300f10324000e00440719450742010f005d0510400445a6002c41d6640401c640281400003014000c90790720207405021309405100c12200440000d060050980c0c0d20f89046c40c0c0c1d62406d40d20700c0028225140281c5031036104103e0b840c15200035003200c5001d03840800c0150028075190341c60581c0ca43d8a20301200c1283c4010b0a6552106d051507600c1d6414207403003040e5500c4070309000c4000015140c0a40c02000382c81903c4040402840d42d07010400d1940c214100c00d080c06009444940f10704424480460071108040e0b404541840c0c2c1c042c1c00b01065104d4403045004241c00740 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 500933030 1250 500931780 500931787
    0x1060905010c1406150301240501030f020d36031403070e1815030307150b030a06090f03110303060d03180b0f0903010b0d0c0311040204090c08010302091501091208 72
    0x40c443c078101300c000c448031070201c0e83d00001041141024030503080001c50b003515040c1c95064020303010340d8041441c41210b04250300d4824a54020280354101c41804008250030842900c00342d214184990220758818440c50300c500c1c0301c078500c401d0440c803800c266500d0364804150320340310342050910703800252446041101c4040d002c6510b8880030302e01b11850652294031800c1c2d1030038004401001c003806120030b00a400600c0f0440000703c865400400c60780414002098080154005c41c1c0b0340400c4c0100a40014100302c0d108050242e01c407403009045029640b0f901d502c08650313008664901c400d41c0d40c140c00c8100c1c00070701c0c2d0200e48500c0d00c0c594103a020714102503000d07680701407840344c0350820352046d840310301c1c0020005040e02e424460020018410740c0d00001c403403170b0350315144d80f105c1c4140300c060107420110802c80701580e00d55049401500c01c1c01410495404810b000a005505c01d0104a0060381014082090701503400402c400b94036059446021850802c1400c00d4914010384080b070b003401050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 500934280 1250 500933030 500933063
    0x1119081e040506040c170723030709060f14060d110f070302061509010b0301061b2a0509061c0f0b01080622110415030605010b040303110601060905010c 67
    0x40c51014001c034002e80007014541007500b4140380c50b00003503001410704109504426485040841c0c01e0342190604410141e86d80c40540c0514074140400c080c0c280c1c940100b0401084101c40e40e8401d109440c010181303010655282c01428074411008600140c1c803000601840c0d200941641003034220f0001404c0460510455028110342d54120650403070141c0c005104220740105400483e018120b411200c0f0700d6254540b203240c044510060080f003081028900020540c01102d050031a02d003640a02940001d0010101603e42c1e401c03070f103402042081aa000000e10741c58814001070003210000d142d04d040c4007007404c2c500f10140d000042200d041480222540c0030401500c20103000380200000340009d483c01112400c1038481001c0710111148883c0c075240081010780e08002e6504106a40024041c0f60038200714268064a50000b4042c900303020020940c280968050011681b0944540c41070494010145480e402c0900036040026280081085150301c9080c580030340318014120100003040c078 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 500935530 1250 500934280 500934331
    0x15130b091e01020106152d08161404030317100602030405130f0905010212010b03042d0204060b0a2307020904030c0c030c03110d05121b070810111908 66
    0x405103214040707400200003443e4101c1d940303490100b400c40003842c2d41c405c1fa000400a000c03240d000d4440140b4405288043c030100e40140c002c450f10b4607030007844a456a6a07440c0060003141c44003002d035503440c422404600c001c86542160015500c02d900a10300b00390604c9c0070700110501001c0202841501e804c10141004407030b00c80e20b035606002e0000980e4a01c41d40c64410b4209030117034044015a013040003040040b485c45840e840344401c0e8010201031541d00030f9007251592040c00c9020398840e140c4076001070301c440d40b00018020000240c445c0110024040c040a8007044000f0201c0c0442c1001c00030000145481c40100d50b0007846818102034540076030710b440e08850fa180d00112101c100c4d48a050040c0041144d150350318580440c0c040503010190b03900c071030325050b42202c2c0074481140400d01c030f082c002046031921100031000c1c0884002550302c25600e0350700c0c0166401000f40510307051610700a8600c100490300040d100988000070310084100807074070f204c0002c0440c186058081d2151902511 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 500936780 1250 500935530 500935559
    0x60c023a060e010c0c03050711061207030c080c040602060a0507020f0f010605180606070f030e03101a2b03121407120b0a1a0915130b091e01020106 65
    0xa40300010b01c480c0b0358002c00c0c01c46070100712a5080c0a07044a4a5001a900c48111820b090f4030010280c15078981c0f001043c0346000c1d82041d000ca08400108105455605034440c100000c89992890080d03118881701c1c074190b104d903015000058100f403000803400c08150700016041b040520494000000000f1002e0074080b0200006040b6510b072402000980790400307803200c0000401c6000d98a604021000a00d18480c017240103250303680d44030044040c5405403004001c03000004d03064501441032242d078800100303112220701011314040001c91140e820080540342200c018070f81000c407602c0d6123925002d82c904444104a0811994203041a41d2248034001d0396504a4111090203076410241d9001e080f800f0201d9458080c0352420014000684c3da40d540c880c00c070380309140d40488070703050001d40002502c40c000700c0c56040103080804000b05008900107000b0405410790314240b02e926000e651340c4601c180ca80d059403048026100c020810380c404045040c6034070500000480e1917449e200c2454625 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 500938030 1250 500936780 500936783
    0xa0804050a05120a08010509130b070c080301080a1e022407050313080c010c02031b0607020319122c010512010b0406030c020f070b031e1f060c023a 65
    0x1020413070f400025000360880d0f014201c100c4851b48549013005030980000c0c480000902102180404a00d689014030018040130340c02800a40d942e41e1200b4299550740102c2e00202d03428400410b0307200c00001c03413800b1306402d0ba80c0100480c51106100e603481c0c0410b03034100c12800741140100486000981c04200a0044440302202d4240040c41e04010a040c26003101c8401d06020300d4042c804016540410907009465a40c0600bc02414810021405600500c2c00c001d41500c60b8100c480c0740090904501c0c000c0c40d02c1602d0540f101110300104503034807101445594201b41040d010606141c401602e882c40050042c034095080c20b45901010300200400e0f0b201c0b81a0359000502407000d564980601550a545400108810710038480c80079a1403100e1302c1080320f03e010110205140d1f40d8034141c494099010040c034030072107003070041c1801c002c103004020710121031a14090016a003400f0b82041c030b80b01c58004203496000b40b8800610307100c0310700d4504001d03140c01d81000e1004410040d80c2c404900345 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 500939280 1250 500938030 500938063
    0x708120f0414030c0d050c01060f0806390901032702031002040305070506030702030408060a05060103050117030318070f2702030c040308071509030c02240a0804050a05 74
    0x5080a051000e0b64140b010b040d110540c2040140e00031000c0001000c4c0b00c407805524205903a0b00e051554540102500c1e080001c5c950011240011401e10020780340e8069005160550320810791444c0c0792060404001900c09040003100e9402014240d0001500031140d0606007c0f40e070407903080e0480d9104503544920005024046208420750038200b11401c4400c040c00c80851600b415601c0b201d5852021b48100340c4510400400100303e14400c0c01940c00500b1041d00301d40c0306003807001e246005820200c5000703001a10f08070001507010b03042e000380c942c40080f440c003451075602c5201c4082d440c031190020344500c078401e2076400540300f41c0203e0407030000d005030008030a842d2540741c180c5141040c07580b80039842034018418490102584c4080b9002c4a5000400e95a64007003481e00300c03940c3d440c081030803480c94034201c0c200b42419080240340302e400d84216044000c2088089880030b180c006070a841c246da680912040b201c80c1e015429035500180510204c03902c6c54640c3d540d561030b1801451030507041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 500940530 1250 500939280 500939311
    0x60307031505150f0d1b050d0c0801110a0c110a080f010f0b12070e04151104050102010e0d080a0e030738070c03080c090d060c020c0906060708070812 66
    0x8440034140d0344007201d5041311118404505040043c04145a900000d0036130a0140156007052200300c80010080c4000380059101c54507900300321680036010703c070300000ea5007032032180e10f011624681218a0411240c844e40808074460720b40c5100024004121a0004012500454a100c08200180703440c0742c140004039900c070203c01c2c0c201c10703035000000041c080c00c0321401d007160640b004079581d03040c3d46903110b000c00c81d0340e1941407400b40c65441c800015141e80c50040041c2e082c850b42c6000f401900c40a800074488007400259a640c1ca80011303860b400041c100b04013103010041a0740082c001d540211007224184010b90b140c4580e003500408440307846016412507418150a1aa0a501480c001d04600000c502e0308100150544c580d02d500142000001c20001c1c452419060641d2000e4602070008824084546403c00051000d1814040948514010a8107c3c90030880e014400c03c0c000d4401070800a20342d581c0c41d1203400440301100c0d504010703c208144d07034510215062058550340600d125 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 500941780 1250 500940530 500940541
    0xc070f1505040e0106080903070f1a071d0105030703060315050a0506120309060a051227072d050915090106050f1b010b0604060201290d0308060307031505 68
    0x9014144018402032001c180800c011204840d00800c0c1161040d00b851450303981d403001c0f05400e52007401c000402540900f81d001d0140400101803070818220a01c002046440c1e804095801040581d01c04021804c00c0e00050304551140b0082e41d0488035504020030368030340780d075101d28080301e1480b000141c1d40c2c2d5800411640c100940601c90f00204161054074109800341c0b881a01c078412800d172107001e400002469009203105900702d440442d000542c410050038242c10810550301d504210840c04400c0356180858141c0102c0e074402103176080d03c420047c00c401520406240c038264071041407030603030141000034140c0740e08102500c280340c8459800b001c0340300c030001c0011031141038010ba01008024041c0039601c42280c01140c100c0412884090740c10305258200d10b02400d070400c60740c3d030840c601040015a0980540002104201c4000c652101d2903601d1101110449894027203030f0702501210103040428050344655400480180582d81080c5c0c88c8d8413400008184080181c032015900c03800c006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 500943030 1250 500941780 500941799
    0x101205102414130b0303030106050304150507031b03061d0a02040306060f24120e0f07080114130b01170c03011505090709030804141c11010206070504060c06050604020c070f 76
    0x140d40da540201c20401c101613100031a03a21700050040c407060190000c003040a02c112458003501e48107561600b031080f403a04560090181903103040540031104c100d44020b44840c02801040103541e011900881c1c05111130300c1001300300101811030f00c0602d50802010010a8560082c00e01500c4211006054285005698080d40d403070b000122405078107401035038586036031281a80046541c116004981c01f08070900301400d001d60007007190680d10038607000003030441c01904103680c1c1c180d81c041100d285030307500118502d0000e540400100b060f00c0500051005200000ea9101c0c00001002100c482c902041c001c00d0031521140752048414141000400c12841d00c03030b80c11030740b200300740c58191903145c07030740c1d489003160f0003036000f120b20300c01040100300c050b0f444001814903010540c031204409080c1e1414400c0c3c07210000024203005002d00740005010340d000380d080314100c45e05030351000c40322429030315024010040038184913071051f0208502d0429000403c0030310b0140c02410860b4968a281c0008070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 500944280 1250 500943030 500943049
    0xa0605030d140415110a110a0905090601030b04140601060804060507020313050f032409010e0f0d1b150606030f1118010e0a0e101205102414 62
    0x44042100150881002c2840c02d01510104e07124080074030040303442030005551041c109069042e5900c50603140201b8084016503e00c846075040d0b4550700d14580f102581000c1d98400c48468000b540006c00400014144685680d4868020900502c403a850500020708100080c1c0c00301000803411300c24403060040d40e20850381c105d03450f400110303d860354010511202c1a524800c00384204501da68034602900c3c1408103488402e5120b1400b190070b64401c564070708076082503c2000447d8644041c0d52940800051500c1c0c0c80ca0f2524001d1841460380c0908031460f034031481224920400004241e4001020b400700c4001c8405240008211541000001021650a00620310307440341814030304507480c5001001c07252407032080d40204072138200510058641c401013400103030b04200c4400340005d18105e0b2030191030180d1025449007001d140d88044040c00030b80101000b800580101c41c0c0b41c2e4120302c1907402039546050260309050040d441c6410400e001005501083c50f04600480700981d44c5813031002c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 500945530 1250 500944280 500944303
    0x602010f050c070f12050408030c01020d0b0a05130906110f180102011112040c17070905060f0105040506090d0519060b0603010609030b07050c0a0602070b1e060f04090b0a060503 78
    0x2141d00341240303502c4c0c8482201d1520000762421011102401c0c100b44140121000340014004a039030700c030b00308116603000f54031610b01c070741440d807a15000300201d03c1c1c00c54940044800040102043c0c03d010700c042d80040540d14412204030fa42c07006003000850840c400b60070081206200141c440c105162a040c1d40070041c00403c2c116490185407150b0203201c1416241c11500c40c10302c2800c561303120310703002ca440340c40c5810208840040b04a07105003070700300092031002e8072038900c0b0900440d01c94400b40085150740010007804104144024491402e18001400c090360008220100082c42e0b80c50321424002d00d0341d900e410074074200c4144030a02000e40100801110141e618510310740c0f600d4402800061113020042c2664249008034404a10038015621240411410358000c803089182c864003d50103110300b1554051044000703003100603a100006d03400d00c0c074103503281000c0e940d0104115640390084c004940c090360310794280380441c0302640d45620545811000140d07150410003050b11b080510b152 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 500946780 1250 500945530 500945551
    0xc030305091c150b21060405101b0e0f0a06080a06121203021b030c030a080a0b01120b0d080d0207021507150c051209150703020a05040b07110a0602010f05 68
    0x200140028030f0111050740940c42d90b0b50000340c04840000044003404428407040c1c2c0b450124144000d42040810a140118070600464003942d080703421038003d503402d0400401070401c03800b012145081c01030020007886800284800e1303091481400007241060590800000242c160041104002d554400d000103001020803a00d1f03018080d41d03525840c1200e410000e42016008143c9540c0c600e0b081c0d121a041320107100649443d5144192007a50300c0d0410f04c502400141024040b99030311209200c0c20800179010796607403c00c2203100d110400980405050290400c4603210100041100400503001c2e80009040142e81e4000c1d40c01001240900c160405000ca541040400000b030440740c8501044691410040f4030340503140ca06076014052030ba030004082103280e0070070010031340108500b44540e591b0b0104070403070345031000b00b2403c034081e0450040110300f00700300038808000d0310340c007502c86c0c1c601c2851220b5075118a2004038030a49401c0d403200c005030b1b443c0e070295100c1d1501401800e038824400c0c407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 500948030 1250 500946780 500946829
    0x60c090302090a020d0e120a0206011d0a05090f070303030e07080303251209150501060e0a060e060c070803030406140f0c0d0b03030408071a2b090c03030509 69
    0x800069010a016211501c1c3d240d0018071500ca1044c1ca8202d80340b001072070750944001901d503402d0740d03005600041c1f13104010300401001040c40d48407200740c000e0a0301034111a0f64a581c40c000d40000401028200604500c21030314580c180f802d0030000c0d4070280d4825680070036241240340e0007e02c2c024258100085507042031003081458409521642c2c00342d8500b8035400707002d031440c110548954000f94000d40c412404e00101500340052410901140708001c0d400f0030a0b6070381c82c0c1b822244078104420056000f01d03104d10400030140f0580402c0c5440304014040c0386012044200305150408076881201345800100c01c120a0044030b2080b40f071302030035282c0f00a0340c0307207404000c0803031030000280003c01c1c20501146510281c45554009032900ca030103802c582d075075a1104c44c007550340d08852164010759192164a1030301d002c4c0e41030680d00c1c65200005400240d4010181d10485a10220a010003856a4220000208103400341d2040154041e48410380d0300c04030a030600c04903180d03880f2000c030280c1100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 500949280 1250 500948030 500948033
    0x340e1f1e1e180902272523070812100e0c2208060108070902071502181e030c010c02060901030506030a0515070f020a0309061407020301060e090c19060e0d1b03060c0903 74
    0x1004814100c00741f8a403501d082a020006200d4004052281c11246900450824104459000180510603401800d181e49685501c0e03190480d441600032100d0b0000c40320003107107a4104070809000c0740710400000317915181c2c1c034000804495019500041040c3d00400042101b42c1d01400101c0103492101c0c0c0079403801c2e0f51a01c0314100b0140322000c40062a46c0003441e01d01599660341080801d15000740810300044000394058600d141000049103c1e0041c52010301c61507004403504c004c4964003605240c145030340070005400405005102a4060240d002d401000885c148082d0b107443c01400900142c9003400100205414070082c03040d01550700c00248400400d4100341c00c0c0040f01c0d0140750a5081c0d00b06481441c02e10300480800035015800c2110100e40c02500c00e0034103204200c00ca0496400607200c4c400c101001c44541840d0f004d000ca11601884010b1140988826050010301100141e181c66a14000050381f0f100340c003643d1008000c800e1003080014011101054040c1c60a41d0245055 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 500950530 1250 500949280 500949331
    0xd050306010507300810120f0201050702030d0201091e030210200c030403110103060b07060b0315010305340e1f1e1e18090227 56
    0x2a0040d0305020340030489104010084880383e0300310003001c40d070000b18050181562030030085403000c1804510044001502c01d054034201c00c1c05c403001c000f816209000592100e5413102d000720401e0741041010802c0c180541c0b002c0045506c142040c0e80001a030030380b00d04000c844605a64070550071170034002c1c08040460b6000130405400c800d59080042d01d24044060141440392501800540c40e4001c29010f080c28804005481142e00804426480c01d86080044048954900440c04590428000030380443c600b0b60020700c1d07007a00a0210381c600c401c01c450340c4c001c641c402d03402107a499108044191071503407020082c504220040780c0e4500b00209900c42049114544d000c1c44c06d4085441001508000360401410501d00000fa00c8910450700c400075a114007400c0b103800c043c3c0b20303411075002815042c1c026003407000c4201c5c040e009030032a00704808040001c0e0440c040e400341c0d54441c00302801503a1910592091001d400041404402d041c411012420300020840407080c02001c0700380194180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 500951780 1250 500950530 500950537
    0x170306060912011b031401050904050706050c030702041d0d08090d0e060f0a020d02070812040603023a11070c0b0703050c0102030a05101203210207050307050105060a080d05 76
    0x81c216480010740c1c0003100b0700ca00402c003600340c105940112100f82e00005030140c1c00501c101000e81d10340e00582c0c0c0c075101400350043d016a401440c1d83c2c00040c041240314071800103841c001c100c1c04c0a072490300140d60005420b842e505510811180208000e4410745081040b020024050380d04104001c2d113440050340351200d00380010304051200a916245013955508122544085103c00c9192584030801e0020f50303801045c6280c1c0b02500c143c3c0c1000c10800c2000039030300d0303040e81c04000305840d190600000318040d41041c4c0a01c03082008030202014480b0345065041204d00088920a12010550110300140c51030b1000350107601404005103404640081c4d04441078a011381d031601d81d140e2951404031850301c45c00c04c40040551020050094110386d60300090301410b2170356220203c10380c46001104500e0b02c0003000602207a0407649e00e00300200d00c0c500000901c4029a00103050101c42d031aa0b03802c6a2003520212107595480007001501c0c070301000042c0c054811038005007000d007004c0c1000780240c1f2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 500953030 1250 500951780 500951797
    0xa0b041220030d0f181101020f061008070b030112110a270c0914040506120303070c170a050d090507050411040513060506070b0402030106120f03090905070f11010f1817030606 77
    0x201a1b8000807074a9000700090458041842d040341d5042c541070000800c9151a40503811981c001c0340c000090006080e400d03241610021583c20600f0307000d9995404c0ba0186a210311134007c010900005540400344030030303002c42900d69100300088403a142c07030b280803070721111170310410b20070707000b4003032040504c174444070000481c05503000941611113600141c8014505603049074544800001c00480c554840c00c1400300c0c40c030901365600208100d0340c07060684c2c0600405140003601c00d11800d00801c08030b4001003c803a01035803c0d241d815840313001040544040029511390b421001030204000e080c55514020107015521003046500c0c2804002a5540b01d60400035241c1c0d40184040b9003555006c0d48010014801e003225107510341083c0c42c05288810014200f50007040c03142100140629281c00b4052144103150394401d500847c50005a400c0400790003c0031842d0b6983c60407505041c9203110f00f80141810f400515540c560a25006505400701e11111200b0305040c814420940c9900080d590603c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 500954280 1250 500953030 500953043
    0x1081c030905010f05041a010e060603040b150a0b040501020606150a0c031b0b0a0b0102072106090b07030509070b090a0b0f0c0105070513080a0b041220030d0f18 71
    0x12074250401902415103c09100d00c07551074242804100048040520789042d00d01407490a1680d0300c1c034031246031600840c2d8454026104000040025040b03a00d2168081c0d0b0340300814659020000101d0f1b8580b800b80c0110080d07407070019051081d90380411140b64042c000b2150024031182240300c0340310710301400c0c0d200d805108101c2541c004150003103c0c058410325072480361031110030310703410900500241624180e94440c40c02e203242c0195440816004156540031042c408071000d083c0c1c5014181964400c207480243d51240d0803400612101100342c081c04e000da0380442c3d54140036455038200455071740240c4180f001041544d0080e281c850480080b00d48003002c10b07071650086814100140b1130840080a0b651a110802012603049005804552142c5200c1888540c031555030f19611101a02d024141d400c002c400100041d01d03101001350002c100c2e1500f0b0205030f50316600303001c40c244c20361034080782c42c0c00c04155802d02106a208011598800b0032042c401e4140c0ca01c2c051128282e5140c015219 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 500955530 1250 500954280 500954291
    0x1e090f0910060e01050408010227041b110a0503030412080105120705040902010905032d160b0307110f070302090c0a0e040e030913090510020a021b030705100201090b01081c03 77
    0x244da000e00180e40092602d903000b17540d28a1040300018146641c0c0c0700e01501910782039502c0501e4206480790000700b000c115110020894000b02c165404090302090703480078807a0700b4420001680038009940550300c1100750042450010501902c4c165051304a9801080b0713100a100540340b002032aa8100c84080e107001802c04228001221004090340201d601031040040c84a40d0050b1106a01c8a038400c0c50b08440241402c0c200341915601050051070721000340c14000d01525498900840d0002007500b411080403403000380e0241401c0c05000c0014140d00018410815400e00c090043d0740a016544094039025050f24080c2c901e0208944d031501503070380d5129864505004100304e130311380140100312940d071820300c1c0c2e40c1e20007030200c482c82181d481c040c0b0041c007d0f055a42c0d0084e5004042d182c0c000d01005141c1c94071074050540d6922403141e0500c81c0510000c1d1507242c906d007030300010642da070001c9200009404c2200003150181d000c04005e43c0006c030ba0a12003501c1041c40c1302c600511b454040364 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 500956780 1250 500955530 500955557
    0x4020102103209100204050102100f020706090302070602060c0a1e091710140c0f1e030408090f0a03020f0d0501060e091e030403020f040905031e090f091006 69
    0x102c91640e42000d08040e5201101e03803800d0056607030418403d04401c0b044400d59420314030058140d002c2c5100ba039000d68020301e000101c4403040c1d08180100c00c0d022400606085040c3c40d00010b58071406c0c010b8015801035031051010640c1400403e90010100c3d081500c0c200e21218018940c1d004414042000b0a80c8140075a00f03503c02d94400c001805103194120440e46076121054507813200712102c201280c81c00003089240c100b40c3d0411480317121580c9000741442848201c0100e80d5005035810200071034480251425a440741b80550b0103140100300fa16281c00120003031200100c0001030f65403150b55200c904000580e41e80e020a0740f076003800c0c0c0c1c010290015526000b805070005410260702007a4000410841e45d1000404a012462032400c603049101c020b11034a840e80725502002c1d4101032001c2a280141c02c2c150406500c60780308404803840c00d4503c100c07401c1c1500c004030749a05500d000245031256450084201507601030202c0c0c00501a040ca0240e005019502d071062500340034100c41d6404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 500958030 1250 500956780 500956811
    0x80c01110f07080c10090335030108070f05030109170a0302090a030f0605180a12110613020f01090803071e08040f030605010f0305030a082208040302090901050402010210 75
    0x10040800001102c80b1075488a81c0b0688410945000c43d00407203080407807196103407040400307408503500710102e040c0c86c80c48420041500401c0e200105090081c2030241d9141a415000940c001c285520151a0160400d040e0000b20390301a400345202c0d038103021a10b40030410a00300d000760801d0081c45140d81e80712103007040c0c010b400390451603988800d680ca000001e000444140d841e074248034400422099403092501204107040d00c04c2e0030b200d40d1242504400141d4410000c0d1068442401e109000c8040480554903004080b00c1c44101403000100003011420121810b00d0003040908100340218201301d000d40ea03070702a03204094075082c000d4009841c604060000295040c1d004100f2540e1a40c54401b20146072495200c1220102e140000001f80319128002c41d02c296a40400510b1415084110442d0143c01c09024090003060160209902d651201e00705500c451040954907141da1031801044214030f00100608080d906001c00c0200503a07012803040c03030004401c500018400c814041d40d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 500959280 1250 500958030 500958043
    0x203180a090609020306130212010b0a0210110a0201060905220f06090320070b09010507030e0a0801060f080102042702040312080a0c0f050a110c13020a0f0801080c0111 74
    0x28101a10380b1038041191075040d001035105010580f1440e0b404804000c4100803031007160818203010f80071500500810585100800302d01c595441107804103c180a094000c03a0070920102e01c0c0349000184080c03a181d0280601e000400d80900200468a07000c0d10301095204208210482c0320030074600d100030000c1c600d010f1800c2c55040a0100000001403034041c1c130302c20380c0f101ba1003d019006075080895442c0054040151501c03c2031490408000340015919500041e508406110500600c0038158030342d4001000240f4074040003241e814a00304ca000c0c50012a130f0007a1170240d004002c2031100d0b10349082a0218410940702d040543d10020407900028012a04014102c0e610400e04041e21a03006852070700520f5030340d10420040000c194266020340500c1a91400708200744a03604840e4050003081d030b0000248820380301c020075002c00180800c082c9a0800910741e601042c2901000d5004001144000070350504541079410b009180c1c0d960079881c00c5075810030040d4240155224401d0100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 500960530 1250 500959280 500959289
    0x4030606060203120f04020112050c090405150a090204080a02010e01020709141006112808040b0309060105031b061303060f060501030b0d0b01090903020a0503070b0603010b100203180a 81
    0x4201941d2200c01c001d40b00c1d84110612121000c15401141d14440303032800c1c4501843d4141c651003074031481c800b020409414024800b48148509000520103508c8a0149901c03852a40c0980b00d284c011200c20050040c005401030307001c0d43d20500003407040365000500c1c00ba0f55602401c0214130314007850300407407030f00082d900a903401c542030071040320041e42c0d0002d6040c018440d0070340e9803100503204c0c0005c642d0b004401e40010710641c00580c4000c50050603549081c001c5401c092540000b8206880e050405c0d40030354401803a640000081000c000020700415026017400c50240c000c01005a0085000d24460346010340704075400156400da104842c0c00f407000030740d0700c000140402c0210340b0f642002419503104403070201c1d041c0346022a07949421801c0c1d110480c0c2c00104a0700c01d0342030031a41c000504030140d0031419442202040e10114400308040c04d5054410314030700400d0301d0030303100303041c2503c1600000d14040d099080460310010b401106980107102c0d14410071481000990016415040680c003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 500961780 1250 500960530 500960543
    0x150f0909031c0606090504110a0c080c03070308150f0d1403091c03030501050a061215030212031e030708180c100c05060c03010305210904020d0b030f0a050c13020403 73
    0x2560310060034503030030603c1200e0303407515166880c2c1d5136a814003042c0c40700858225100402001030410707940c068000f4803c414003c4941c1428049014141031540e4041d40d01038001c02c0d100070410840c03002201c90030300302a17000e0710203525080064020490750302070000c0081c1a1052001d40441c00b0350100f040d50b10f1201c3c01412903450480310301e000350011000040079000241070a00208607400d02840c0c1d0803c841c21035541804890700c018040c0000e040c4c0c2c0100700c0c7c3c4c000007101c1c0003001d44e80382180c005004030014040c42c2e841500d0380a41c7d80c1d0301e10204620781c03880c00c24010008255003001c1c001c0d922801d040288030502814020050034021021120307540441245440c4003607030b5020b50748039016840b4000326140c6071964085250140424070004000740d102800a9010100c0a040b0f0035111242d80c43c05401c01ca00a030001c1d003603030002038480403115a56820b0b41c14600d807c100c00680c404511014001c0c840b03054407916160f110400000e401144c0e00c1c00c5000e0442d4440e411100103642008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 500963030 1250 500961780 500961817
    0x112140a05030433090303030507030506150a03021e0912070506030402041802150316140a030b030a140a03031a0937020a0f051c0b0a12060f05150f090903 68
    0x603000d03004178031301d0005038000b0b85420000340320340d40240f06140c002c060080c02c003420b810b440c0680e03c42c10f42c043c1026400305a000d200f201c2c3c1c10041512190700c1c170740406015507128007040d81170105d40700c3d401c02409a02d50000b0001c001ca611001c00302c0fa0001c1d0103407004100400201030a03004c0d41c0382180000c3d00500e441c0048501258104083c1d030003801030b00c0e10000d0101d107800045030140400242204411010050703505183d000e540005201e20001d4107696002645413510300300c03030341d0a420b01c40c207940050041004056144c40384410100c00b0407504041c5420368400700341c03051030041c02d1008010411820b101c4c5d0000d200c800d948200351019010000a16003401000a50410f00702c950224903681c001e100000e0181c416180c25145041000800e60303204110100645400c0142c150003c1c2c00768404a20004d00c094545056802100c0216030180c1c0d12580c0404c4400c024100620300c8480622900c0681c0c030401d070544468002c58400d0301d2510348000f035a007144209038280c1000c843c1107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 500964280 1250 500963030 500963129
    0x504120c150e0f03120f0a0201060b03071706040c05070219210209061203071e080403061b030e07180f0c0c031b03050409230112140a050304 62
    0x582d51980c400800d440031889000d5030801d03d41d40300e0709050802002403050208424420480026203640380e42031002085859882e400380310780e980141c541c80002100b42c04d45d9034590500e07010b140d80082003502d0401000100281c0180f240c0251900244130700302c03004803000401084007124000d020081c0601005032010f040c41c80c44040c1090080740030b904148002003907890031503840b08030540d5510255151000300d50740e0348030000740c010000050000c1c1034141c201041c42e51001c4c0024603c50306000402c01140f40150101e4400581c2e580704150038a003000c0c03002c810200300d090488a5140c0c0f4140e04404102c252005002000e411045e0707249890400c04159a0001e1403201050090f1103c0040031f03c3c50b074030444c04c206070101c0540421801c0004101006840c0c1c021018501004046100010349042ca411a018203900803001e9225546108061000c01410f40c2803040703c0800400002c04c55580702501ca000d14070606000ca01c48015040b520300c0d0780d000d2030001e041c94024101c02d44148 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 500965530 1250 500964280 500964287
    0xb030a0207060b031e060c0309030a080702070b0a08010e150f04021806030a06050a0e0405062d0705042d2601020a0c140102072003030c01060b030a0c0903030504120c15 74
    0x38200445c0e1262501050342949a54106c9004441500266260040310071302544c4c01c4030301402c0768086200c0e0b001d0000c0c44005040180c0100f888956031190349500d0008561000000540600c030340c00140f403031070900e0799034000c81600005d130151005a11448010700c0e24050a1a9503006504080d00000304400b8100d554400001c1d201c088428450680d00c40030403040482d01114000c0050b80700101181409000303048a1280c40c1202042a04050350703501c050441060680341da20100d040400d0034007100110380704203000308520090307403d00c0704134000c0740c4a1030040078481c500140210b441c405d84202e01e10502c00750300300c0c1c5d0725000f5940d41041200040960f5048001a140170401c3c260504034002c06000700c82ca1150004e115a4149400b18082c2080d000d04001e401d40c10b11081044007007500c428011800180404001d664036854030a600da025200200740342400c00005010500000750004107440c01d5682c00c03c90300501c49481c3c13405100c03c60003034100c902c2101800c2c00001c0ca0380c1e030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 500966780 1250 500965530 500965573
    0x20f030c0705010e0604080306150408010e0703030207061418030a2405070905060901030b0102100e070807090507021504020307050d0f031404050f0909010b0d08120702070b030a0207060b03 83
    0x10540003080701913000503895850342800e440c010491001003020891501e001c800032028036110703401452501d66a01f00d450f00311801d003841c908880d04516420014140c040c841c8900401e46801c00710300c007000c0048466914490380180d14100010104618a1514108016076895038081314a0308c00002c280710008004c14149244030b0110b0800300011149407040f0310200803543c0c00f6001d1410414864015000750507100f0308507045105100c0e03104c01004440c0900b0b1070101c401c80c007621000b414803204608044103608a003d2550920003408600c0c3d60010741034a40c004460a040d4a545891001a080601a5009980c043c8411b8607001c14040f2034284005013901c01d80350021204035400c5410654019480f030243d010881c04c1580c00142004500564499048000080c2007100c0c1d9001400313002d424041503c1414020698020180411441c0ca401c581540002c3c1030580c40e114401b81c007480010041e601e03054010444004000d11600081c4507000300505840341003a031080d0908452a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 500968030 1250 500966780 500966783
    0xb0907020d050315120312060a0f060e0d0b010b04080705101e140403060509060a0b090105041a0d03051e04080a0f0f060f020c0106120c361a01030b090406050a020f030c07 75
    0xb104140448c6281c030b001c01009048401c1d401101d0600380c603046040e01c1250f204110300782c100c0d031400889400505990481800307410219043d50b1514282101c030303441e01401d5007081c0c0c050701c206c20712850104d800c08131111003d005413030b01c8031074a04080012160350341c103865052006100458044200305d4940c00461203000100308494141e17964028480c1908c0d440300300e03241c100080e02d0041c8410304081c0c102c4460300e049600040c261024031408601d64000b82d80c0d05400003003010444a0014600b400d00e42100100e5135131040c01d1500b000400d9413a007039803107001054190074030075850030001788064280c480313608507070100120b14001d034208000e5030048588440039442c0c80c01c003050041d51841d18155a6400c04000301c0c1e0907041039208881040c035602d4015424100880034040f4144581840710041481c1c0000705032190314007161410403030314080b91418142842c040104ca500d461442da94829040071012405403511002c0c0f20080c802c008100d16105400020081e08105c10030041c900e00703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 500969280 1250 500968030 500968057
    0x20307051212094c05060103060e0408040b0313050109030305040b07051317010222030b25030b0f0301060825150f03110414040b0907020d0503151203 66
    0x20360355a4003140c1ca401040801c0c0c410703540c4020b01d400404806031000031401d85031154242c4507140c813407400050503034800d18400d9030700c0d190801c0020a5038180105001095105c1c460071190070705617210010b0340100d010300b140790800800000c171810041c055007041a6004402000032540e5410014054103085034181e070b51800c040701240d0054030031002c0721000000d12402040c1c0074140b180c0f00741d618001501050041d9024403480380c000050042804d5400c14501c29400e12a15500d042502410021301020140708c0a0106400041c1003500d009030014840c900024910700c1c04000515507400c8421031a015807a0400100361120005050030b00c440d42003402012200802d090b1740c501414078095204d202c41e6084c100345980d806000c14a05010302400c0100341d1003100c03500c0418940140c0c0c800b01704440c1da07030347c008030380d00740f900c25039240c8038099541a14034541030360041d54400402c0c000400f0072800100103800c10b91602100c0c541d07060300400c14030f05180351101e070035543d42200c120344103c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 500970530 1250 500969280 500969317
    0x909070203130e040c03060c0f030b0a060e04090c030618150203090c0d06020708032509080c011209060c1e091212031407230702090105100203070512 66
    0xa1500010555100c80030141030b003059581090259a507401001d40704580042040c540440007074a28010250070540503551035901003c175800c01000d0b502031580c01806065400d0003030008580c40112540404000d580210700007800346000c1c2d0f82c8610661000e0300051905840414000400f80c3d2414543e000e0390004616403100e1401108034071058a0341c4009038400750811510b410004402c000c82d80c0614001410500c1a880e50105a8011103d41c15a03010070003406c2510040308070010b003843e0141c07078800d00ba01d00b4050842d81d1032080448040c14004a441d03110001550b40d00f1020105030700c84010300001d8a400000f80c0503520002043d500c90907160040c03119503102d546070100311648400910040c0d80c41e92140d0161440c4103441c1e50816443c1c008952210090070b4407940249410b549060709046070703c2c000b2a08481104e4640f949000410031040940c0d6100b1841c3e040d600c04030703410210015625400e034078610407880018554001c0509082d114500c0c02c1c041c044004c252040c9800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 500971780 1250 500970530 500970541
    0x8131a06030c0a0b0d0c0c140c13020307080a1a1903111c032118020933030f060408030103060b0f0603070c0c1e08010e0601060207150311030901020909 67
    0x50003c00384c05088000d9400b4810a210f0b00c0403030b0803910302c0342501e0a0a030f40c0050f1039200c00594024540391548190301c0b480c4501c40314181040780307207950b5081031400c5086003003070b000040010401800918040c0c0c0c590014910200e03546140c2c01c0030381001001761a5070400d80780d680c0c20040d280e00c400c0d5428103480e000005141804c911588240301200c50410415100369070581d003040884200e40281c054610544085004070320400081480f0440385491070305041c4102314800c1d00040419206004803100c00d2094992000c080750921103451350044408484c0f40800d2800702607030100c5000388910780c1440240030502c00203506a80c00b0704003e006520b443c405001c118800003154541006c0e080002030f2049210340058100c00b88228105a00980c0c1e070016400381c0311450080709800c0855001c02c01003440c0074841c1608880c2100043c040540c9010301c0039443c5c0c04503114880d201c042007018440c405100741d02011000f020409580e07203074100050064000d400070313039400d4051201c2c1d0300401c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 500973030 1250 500971780 500971789
    0x151002010e0f0a1a1510050c0d0318030809033a09080301050105090406081023070e01110f01050406020c0d020615060705100c0804020312091008131a06030c 69
    0x50340613400101024050078101088510f4410003000c0c80103ca05051203050075075a1401d800703400d0b000d01e5845035107410030302d14100d007007001d841c00348000e0500d0041803035a52820f64407160502c2d90582040b01459440203e440d085208100d00030a44607000020503550a1004c0010072440c100c1c40da03c0f40c103400521321100c08540969902a11500c01070004210540c41003005100c00440584042074207076030380c1d0309189800c190840d45400d1946a540c850311710250100c444c039045d00403110101207030804c00d401408911400d04014100b002690502d21b031082d080088186406016000700a04c0c07902d0300b4400000d401981c0010401e01804007040005d501c0050700700c1c0545030806a04103946607040070040c9541c09103904039080c0c069031000040f001020b00c51030302c2e0702c0ca0b03a4507050182d190a10400d42411a0b141c034440402206000040d12a10340d840089410085420111581e407281d48070108040e012210051040828401800140040030369913802000241d04035800f05d20000c0411 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 500974280 1250 500973030 500973043
    0x70906090605040b03040f020a0608060f0a0e01090504020a031209060906030209101b050a0c0e0c041d0711190b0c04030213113f04050604020108151002010e0f 70
    0x1d400045003844240000c440c0403000350f4002d031043c40301a51000c841d40c04186010030650141010441d020100405400c00c41c84000c81c41404490514030f075070904280d281400b00c18040c2c0c00c1d0140d940c2000400b15200d505801020b560000c0c03000500920a4100510000840c050340c40040d000c0c2200082d890300034000c1d00c1e22200700400c140101500e00500700c41e4040300e400c00044401021107102c01080c0e051003900c02e064064142c40c415541080c008185a140180200c015100e042004000c00c084207518a460314885a00103241500c032400202c0303290403a104a44080d002c0e11260741c00c0c2010214000c01d101d44960182c2c82142c3e1510504400ca01031480007035040000d800740888014a1640a42c00415030003034490b0801414135003000e03c02100e40c3d03a0040c16814001030112005240f1f02400e403003008050100305034038050303642031f48820002d4402410f00204801080c45a003800580051103440030b80b40706c08034501c3e8071000340a1305400d040c6107018040e4500e4030769a2000415078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 500975530 1250 500974280 500974289
    0x30e0307090f0f09031d130204180606080108100905100f0902031015030f0501061a1215010909020310030b0a090201170c040303110c0a0b090f0f0f0607020409050a0b07090609 77
    0x911b1044d40c4030010710340517101c90440a80e800130003004e540da090780451002d84051301400c110141c10030003008a050456441e500110240301603a0010081c020b00012100d01c8840640030102c0d0812440c0341c030314600b100d169801414542400481d00d542505035111b28909070089040f64042605508c115040710050b201c1b00c000110201800c0c4041600da00021100c94071520002982031396408843ca1303102c584045080c07030319a000614184000e910461107411084001440950581600001c1c142d603086224141003a60084006043e8900c1e00c02c4120081da0000b11803506840c1190040c8014400c0f81d07001ca0108160302c0c02c0710148002550064801c107484100c0d07134685800d5403803e4444c25200c0d40303a400f49100c1c80d50504569118600004010325511920b680c44511b01d004210703000c0c503400d003801e00030301020101c0c0641e5950368140342990b40c0c00755101d6965441034000304014210030003014000f8450b80c41c07a0300030001806445c4d84a07030142d503112078402d27032a4102110020098400c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 500976780 1250 500975530 500975537
    0x50d140106120c090e070809160b030103060902060706240803030f18120d0614010e030a110f060712020d0503190c120c0810060504030c090504030e0307090f0f0903 72
    0x206841c45064a600205403407029044c00c07024a0340d60000c203078800c001110140700242c020740600512400c100b02070100e0741d04217540b010415040c11060000f5000c1444090000e640f540e6903c003e40d1164400c0710001c1c0d4100c1024400d410050361803200e00711508460000d252558000010948008402d9a000e040860001207507925606401d41805410303401540d128002c040040795070700690001031030b14158030305020031040d11786481d401c0401c80e4140c4941c14000e1201c40c800d10b5a03800704118100d540d00101e0b180c3d0806803000420100d2190400d0b50342c21500c0020580d050022040e030381d0b0030440c002d6084640301d42c640381003281c981c0016281c41308070000c0b030b090b4002512380c40c1e003000e00031070814940b2000c0f0900402d900d0301500c3c28403440c503010800040900c11032156009498010304114140346250600d56624401080228480d00300c0c100d50361808201054440d0034100c030940340080444071800d80315400c150007030041c2c01841c0720f91450911500700f00540c0707000300c00b03440d505a02c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 500978030 1250 500976780 500976797
    0xc03030a0902040608060406270305090907030e0a080d050c13090926070201030c080c25020301020a090f05091306020702031e0d080a090809010c170a050d140106 71
    0x100c0e03102610003548202c0c0d110703403101c03030218411a007080a81e10441c0203600200c0e5010405804420a0403c2020391080b00c1c62500d240d000310b03420004581d207122064504418964078071400b100207041044810f0003034041d41884800303000255000e007a0704031824008000070344450750507110a1040c103101d00c88903040d00038100041011a8050b003442c901810b0060000500c13031941964130000c2c004d0100d2040da0216221045d0350b850b10a11094190300c0c1000f500394200000684094000c81211481c1610f14546900740074101450300d80d203841c4c5c050001d54039800746690280403030099001d071148441a980b000141e81c5403038250700d0700405903403065800105458540310041c1d8800e0106a1b0184104d204903c40c00d003040008003912007505010704040e1079100f200a00214000e08040003050402c0407403808a0b01c01000c58002e80024286a151046145041c403050b216000c01c03481005004110a03a10f01e0b001001052240781c501420442600004c01c200c005910038080d5100081d50f01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 500979280 1250 500978030 500978041
    0x100608100f1a090a030602041d0f062404080a0311032805070c08010605010f170a05190207060b0103230a0221011203021c0c030c0c03080c1c050c0303 66
    0x1014042c0500c100d05280d203007194800105110034020b40c011520300e13600007000c01070131044400b28051411260751a458a04002c0c580c1005004041e21302e600c0384410380b10402c500e90941990384070003107103540d5140e1181d13500c0038916203a242c009016008034500c60401d4280d00800b0049a1200c0c46680c2001c54420502400b003003519007450b21507003400000c01031070b00070030600c9149800070240b0700000b040145c1410001004140d500f8951001d205c4109011125020030b1443c1641c070810003440001d9554448039040e5119071042c006000052000429105011f010380062407608400e80b0305011040181e5040f00d1b034654280303070710000141c5000101d0754442e071540080c1a070b2001503501220445d62200740c0301d60f29000381c0c48404500c8455800004241c0c060040381080c0c014003072505031800c4580c070b001e440a0f5002c0801130402c00102c035801c00300408410903202460300840810307101e0416642d0031390b8410140e4401d9500803240304a0b400150b11500444012200101c055801c42d25034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 500980530 1250 500979280 500979299
    0x40b0a0f09151e1401021518030405060f030403020115270f0f060e06091009020a020a08040602060f0a0203101e08120d0f02090d0308090f0105100608100f 68
    0x401c1e082c070109080b0b8010001c1c40301e01250722005407941e03030480c0741681c0380341003444800e642c0d4100103141035401c00000d44030b81208007a40c0561000404880c80304914180740c0d014114869070300081d40c444404592a502099a800a140305500c04c1d0000c2140000f65221032074046410b203d0700c030f1250041092904007910801c00880301001303250001c50305c201803008040554902400b01c4a0751a42c5180800401201d00650f6800c01030984a0f0482c40c1800084040b111841d030095040060300060b5030701410344208072130a50075800480740c5031500d40f11040291601c0c0305840300700306500c1c010b010801c0c5612500c00c503805150884900145149090240b80f6201507450320341d2041090704c2d07800030303003408140005604000706035030b51561602d0400c0640100c4018402e9203c4840c814056085561071750081d5140641d05400c0c64407050340c1d206241441c090a840d82d00200c3c0d42000b05003c2140650040d440c11350b81d068403426a50f940c0e100001d1106600741c4643c110341c0707450303020403c0300c86032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 500981780 1250 500980530 500980541
    0x50405060f120a02031f15060c0f08070b10060f1d0d030207030204020d020c07090b180a021c050603010b06120f070c08161101022a0301150311040b0a0f09 68
    0x84009440003c06980c0000342400c0e050f10346036809004403100340350400494800c144840c1d4908049450007070602000401c0d90101100091480011020036130600a540007a201e540f030340040214500c1ca48100311111001080c170800c40410f15035004101c400c0d02404c2100c14070002040c3e407030b1810400b0810040480b6040d041030302980150b03c0084056103560000b842c41041e46000983d64034251004185001c075190701c8200034de49007100f0002c9580e208513409040000c40861081e55446030200c1500910500c842c1c0480c1c0420183d4546244d11150001482048101d008111801c002000d0044511070b003031f0201180c1e6120720000f40a00c012052043d080f0902b4613002402c03040c6581c0d00d01859000d503c1e62080109440c0b102c50811250b00c0f154042441c082c07003d80603078810710340c1c01d02c40056013100f065070084088401c003441e52000d40c040d0002c0c2c1a00d194903030f40c0c1a641c1c101088003201d680a00382c00380381011449184c03030500f88050f10440d14070000c83c4038201d16010040000b0301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 500983030 1250 500981780 500981809
    0x261810050417060403020601082e0e013303210509030a1b0603020720060c070612110f07080904090209041a010f05030d1110060303090e01050405060f 66
    0x942071201191220b51080d0514118102e88001c02c55030a141c10042d01d8000c1c141c4c0407040c03a9020b42200106512120400480780c41190f0600001d07074001803407800131301189031f4143c20541c40c145ca00d01070300d0002c060098040303500c1d40c0c420031142035404160407804410b01000d0300e01c240303000d900111001c0500c00a008045036140050400e115100000e0400341c480e030082e02e8040c00b865400198202000b4904010b10140c1411454216599104108440c0410340352100740001507108056032950400c84845009010590744029122140036140b10a440c50b480901072402c0c0c0c0c00921035906100300ca03001100b5a80e0a400c100f0030360344203c4c8580c0411041074102d52603040010040e142c0c850840d0140f4800e0400300c181d9601d400312400c620605911105503103540000411103520b02040542c40308a5034544452400b03100b002c0c03c1d140c41d4040d050034807540e180540010070305603c1800ca600b515a41c040c0d10b100d5913680c50401003918410b546a5034402d099000c982d5507890107062490500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 500984280 1250 500983030 500983037
    0x803040809150414090f010302010c02030a0501020a090f051e0d03030204080610090e0604110613170d0f0e03060114030a02101206080f060106050703020712261810 72
    0x1c40c1c501c021900c84000c402016200000214041c0152503a02c55400e980c1310068400310502c0c5810700c14921855010711000e41401030400503c0c066403024041c0d01c1030a03402c0f80c002e40d41c2b00441d080041850201c0c4c860110320411103500451245070012040504888962405100038080d9040001c05c00d03503048214240759080100203100c08083c0f01d01c7d4492203800351203c00b11442c3c580d101094034079011a142c0f2507003000040000064030318030104141c44003611102d072501c10034188040c103800c05400007803010b030844070300c050300c0080021540d05014081d610009a5044100103807006100c20710415411341100005002c880d00c2c0d60501d400201006003260039203105600421041106014003400060700ba401c010060543c2d4015000140440c80051034184031409800b920b0790010f009207010854006101d909041c400c100246c00703404000314a404042d8145840c1428031091000030070340d0110f400c0c81c98100087c0d002034036010301440b04040350541c80e0904100d206200a0400e0090 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 500985530 1250 500984280 500984287
    0x12061215050c0c070807210b0423030c0601050f1206071803140c01090b040b03011502070e070c05160b1c230405011109130c03060b1606050c04080a08030408 69
    0x107240f010000c41c40209507450140844905241c10f000340f1034030340100003000b6110600c1c8200054000745c5020381c85a004152030300b61200c403070001c40800c20960b102400e588400304a100720302401040c00e5040b2082250313000d00640c0344c8004e00108100600020140d43c00100000e440e150081c1d0790f190301c3d602511110b4501c44e46a5891100c9103603c5004403a2560100c1340740382036960855046c46c080d140e041039440c1410720f403032007200700352105026032403440c1084502198810700822074840a04000208034800d45480c4c038004154158042d0180ca052045800d2200326030400c2c8021020f423610303003030850f190000c130819541070742a00d8024404003a07a2880030f511004420800170800d503803800601c0c00c150909080c06802c0d80d44440b800c01170b81c58200708481d280d603501c03140c802d69000703a94070218142e141341c1026801803001c5d502080c01c02c08009541c00c606043e4800012204c0e1052508014546448201c0340c4940a5130058001641c0034510701c80c00b040c0c08002455002d882220703d00d15 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 500986780 1250 500985530 500985547
    0x170a051015050a030308062805040b121f0513020a141906030b0a090204060806011421040b1605030c0c0304080f03040302011205040308061c0b040312061215050c 71
    0x994145603030094000406c44000d01a5a2030441e00c0840954400d0007007909044e84000c00002540e10341c4070703440c1f28036a1100d0f14005620790301030340d01c14180c1e044142c981c032140d180228a88103401505c02e901461402001403010010401c101c4c07006600a03001100150800c0c05012820449001d01a44451070048074031085070078050103400b41c00e242c0e0b03011a046110300c0c103015043c59079801c0403004600520050021607071115089a2003002407070662101160b2542c01c0445116691100303d034900c4080c2264128203a0b400b009000c1c51080c172411000f030392004c1c448041103200009002c0001d0302040850020b003107641c00b40c80a01c3e08003041d00d103800d80d102005407400300b031a0035251460700007040800a5607040b40d5285440540c503041401140b03442d0340c00030300d0383e04018092442003818004ca03013150103006401c819080c0c0e02030111910b0342031600300a4020716644d40000c4100303007401e00200b00c81c50102c4d5209612075110000d058008050709200000d440000c24140358200184000c41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 500988030 1250 500986780 500986789
    0x70210092105030910020a090b070b04150b0901051e18010905010e01060e2e18050406030f060513050d030e070b091c0206040f030b01170a05101505 65
    0x400144150445220340c0a030510703459203000911110401e00405001308840c800000c594503010840300440141c1e40c9044003025201000795401080743c203003000c03c1c0361781000550020140514041d5910039151160f0441520540c1c81e22643c4982001120004015500b04524180a03082e100d42840f03149500000100d80e00c441404805120b91000c3e800402c2464020320915002d05001c00f00204158140b0102030030100003030b10050b0203900d46981d104044424020441400c40c06861100d2195117042401020540164011120305d003044030001540c1c5007920031a400c503940720111440f0b07407181e40c442e0402020000c21050110700072001c201e000440501c500b80e103407031041d10005840f05010002c0f500c0c0c40003c0c0c01903509000104900310055035604510b6502a011107502c5041c5000c610115089001f06d622149a8810009000c000c1100040f80035041c1c49408001100840003403054039508c925000b4060702982000064005a0805030420680082410b00d0142c4c010707511800f00e0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 500989280 1250 500988030 500988041
    0x41a010c0204061a1c060602121606050901020304020f10020a0308060d0b010308031f180e0f0f0705043b0118060c02010b01020a050304230a030b0717090303010b03070210 75
    0x203034074100300020170000c0f407078140c00e03c4885145a280108041410a00007965030780b1428122403400740c0126409200d00200031304001810344c004018011814161081400b030740040c0d8049108480800011040e420140000e617040166980100b10b040d00c2070300e00342c8002101500b500d0300021a40c01c05c402152760446558001d52107404d85030b035680341001000f00c945159000d0b440c5d990401c0300003000024010a101024040c4508002501418044055250481704d0f0341c955001d015602040400c60340201f400d80880e90190350078094440503107003480c000c24162106880150100075810500302c01850708a48586c400717400050038a08200248111200c0d01b04116842521a920362603081e1303083c000d80052240078002842c40344220340e0b03500d0b200d0283e80640000c40741088a452104500100e0f01c400010001d4402c061050300c9040c0601144011141d43e008156101c0594490310301a403045803049012340701450840e400d220841185a00207800801180305444440e48640c4142c1b044 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 500990530 1250 500989280 500989319
    0x1805030f07031709010806220c05031608100303051c150f082a031203040501090615231302160b07140d0c1b080d0506041a010c020406 59
    0x9060842c030718680301e41c0344250154050101c9405010300d00c01a42c0180000b0380050b03003110b40300b54004480d0306081c8002d4002c0d80480f01c1d40e0400c2c1018507200e4001c00218040e01d103440d0141032a0110b12403d403141d090903030b413071400702c0144c801c2000030030300c9100a8140d40d40e4245e0343c20030444c0361102820a0360304c0c1e1850001401c082120030400181107014070340090881501400310048202d840c44401e04130074041031300e554240c001d407407a15582400103003500c4180a80803601d07820a8100306000344402c007030481e4024034045841540001c00000001119a5034143c008080240304031510320501000304240c000c042040d10464001050000d014042c24522050840c5205424030903501400a00344000740306130080e6414200303e41004649291b144102d01080d03440050100301e4075a5091171020f003101c00c1d4040004200b2641074000c01941c0107586041c0401c0d2151400c220803100000c00c00052140324000078070655000300415090540024030014006a8030702200381503000303e904 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 500991780 1250 500990530 500990533
    0x60c0f1a091605011103090409050c040e10060e06030a2402041508010501030204210213020c030c060c0301230111030c030403020a090b150f250311060c04061805030f 73
    0x11681c8062261050000f04424603251a000d00c80040c060f459100706010343e40510340750084442400401c0100b0140200e0241c810043c0b20300b99661681c403000e500005520f024109440003c1c4107914030645400348000802904070340c0403e82d10501506048c0440c100f1212522501c80b0500c800c52000d84018501d008002e46003210781440203015580580003541418410702c018008201501c01e1080c00c000e44403002c0148031002d000007400b120207800300903005400000d00710800e01004c0090a40103072008103c54864640c40703003401c00f6000134041c02528104008440c07001c8010b250000760422010305000011441800b0350506690003018221aa584000760400450400300e87d90340041031286d07000c22070300c24140c00003501e0900051840c07843e1140410011013141103c0f044800500c0a07a01035903010a1013031046420540d00502680400d00040050503041d05c0864000c3c807510003130308407610749403d10070309441e4800c3c10010446010250040402d854400b0050310255080150 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 500993030 1250 500991780 500991793
    0x60a0905040c0c06050709260106030b07030e100605060708160b07021c0801030f0f080f040f030b0f0403120515060c06180d09180905060f09011104060c0f1a09 70
    0x103120045d180c015015070200302c3c8000080007502c00300d006400701e80743c1d104d80d525100901c00187d103002d0800c40e0070140060940d002030140064141d8405244461a802520b10bd0016800d011080f6496445200c0d00000c042103110001078415006040075299051011002c103007545440c41e48034811540840542d103e20540f05905800010349060b810181c50850350941c11580c820365082ea1401300204005440d94003c81044101d10a0f9103a42e8080e0f004c0c19190f41e81c0ea03c69944100fa1440191410035140740802c8400c40b0800c42c032031240340c1540740c01e003907042490f030b4100c01040300825185d040d45d94240d2400140e910000100450001000104294148607620090342c0c608103880701c20580c0f1004441d05003507003001c40e2100312800ca0031140900880c01000901410780700c0703002041406883c04012881d179011006500410395400200302e00d000ca2403001c60217104038015000171441154840d000615180c0008187c40d200318a80300e05a040412280380090341610065203d800c0075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 500994280 1250 500993030 500993033
    0x806130c12051b0f0a0e10050d1a162c040c0c0204050c0403020d03030e030f040902071b050f0904110d0b01140301060f050d0f05031606061a09060a0905040c0c 70
    0x101e07103c10400e10100c1d080411040c86100286070740101c2e11400030f90541480000d03110707103282c808a0703008200203414000445503130300c4c0c14072000c50340d0215461051407440214038021806168401d00c03280e82e03103400c0d0800610182c400380962101d003c20700211304282c00841c507620340b806154501403564540000440746881000700340e440003000c2445408040c8410400b41c0e6458401d600003580500380001c001e21800386c0603041d0700c00e02600c001e0041d030003c0c001409c2115a130062415500900049404950400b4521100c1d00300e071080c681c0c01110507984011515082003e030780c01605c1200c4100b0200c51010200c3c091103418102a0307440f000c0c46004101c034000701018200b4442c002c40c02088030714140a40d02881d82e0035805000e00a1400c20040c7c0c04016400d2641c0038a00d8014003141d031170700700c1e0740d00c022017010540074120f0340c960900303500080d01c2c02a030301610080001030480074201020351040c03100c0782e0403030310600042041072100010141c560b0b2040511080050340c0d0141808420f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 500995530 1250 500994280 500994313
    0xf06140901050d0308042315011503050c0435070e010902030433050f010f060201020702090408090a031a070314130b090106090e0606030c03070806130c1205 69
    0x581c8510f0090041050f1103002a42c000380c2c0c40c2c3d0103039100c3d950300422500401c208844040003040d2105a03c20312618070445240704191f181210034543e104000b15425660072002d0b0ba0050301c13030f441f2089060000380040700744607441003020105600d24100d84810007900a40b151803004504031035822618007804030201c104000340c050102218158514145586c030f1040c100190342004035114070461508822018101a090035990544414440307820b0140a85c008030300b0a10458950785910100000c00314018001d5400941e0001d2840d0030b56515034407048107031380c0600340141e0b20544083c2d011001801c1004e88191007040740e02101110310780420040d00b110720020f10100710340020810000c80d02803650106c46815800b0210403030782d0302c1c0c5411440c00b400c030316000001d80f1410964868a500030000743d0758461402202121005802c80040c907807a000c5d14000c11105400c0395000540c103881107164948420b200d421071202c241d03615100c07501d01c0d9440090403901500f2080c40031140c00352 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 500996780 1250 500995530 500995549
    0xc14121606110a0c0209180a050f0607020a0b0c09030712030c2003100c261611030324090429070e01030b04022802010501140f12010f0614 61
    0x3000884a0302e80703400350b40050501c00c4c50110003485400580005401c1032000141c400b03500c1c50900031694000b440f0304d0410303114801600c007540c861103401d00107202144001884a0704039000400c029071a01c481c0c040981a03480034003890340510032220001002000c0078068803403d4001d544805106071685800c00c0b1300d613200180c65468240c0101490f0403981e000c1000045440d000034001031000801c5825178010322882015a4006118010403105c600c001d04183c1c42507910002c81c003c5030307010040c243c8011200c0c000e228a04d038803c0c0009120000009040c074501211081800703003110481307000891000c412141100d038a0500c0da8651810703686032500825010446090a000d483c080310700034155800352003814100354580d480d0000030f4542d03504440e107034131401010101c41603030303a01c4c504404c03148031100d440103610349400054082b111100003141c0120040c592007521135910300308200c1c003444084001080d540c03164061b40c002c1e054810b680007015804039116a0703d600b601004808031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 500998030 1250 500996780 500996801
    0x11407060e01090b100f08031809040c170706170c030121020901091a01030c02031c0608060c070b09011a0d021305190b0a030b1b0d050a02070b160c14121606 69
    0x18828080008100144040c0040b140404e8403101c2b900e680302d003090518040c1551094039a401e10b612526444880480c010090784d2150b00d44500c540500090f41e0302020b07088910b00c100240034801440244544600041103800d0f40c80884801d01058002400c0d04100b070340700445499070f84100c403851110918050308800000d0908111180c401500a520392182e00e2122611b11901c0360361480706889980a10060541c10003103c0c034501e0220396040c2140d11185050f903403c1181c80000d140320805000303000030801400000c5982d0700d20041800040c0c65091412a4400c407421548101001644140b92250415040e01603412110100402c2210030700080240107007a2000c0601c04140130f44400e54018442000051034188009040130150040310400340030039080a0038409460201d40160240754001c18100b400c940f14040032061041c488030f00c88001c00c455103545000304070081c4400031200c0550702680e6809480404c0d902071540300741c80510030548070401003410300120348210130210 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 500999280 1250 500998030 500998033
    0xc120f0f02060609010b0313080f0d11040b0d0908190e0f15040b07030c120c020a21060522211119030504050a090e0c011407060e01090b100f08 63
    0xb03041c80f0020a01964050241841d619000030220310322100c042005664641c11081250300c0c0c060500042c0c0d919440b050710205041e08001e000c0245950b00d0003124202c0d440510303468a4038161740d0012000e4440114266100b1308207210b042d00f9904000d000030207041c41655941500d00741c1e2000c103c080100013850301d0190350b0000905121000040454095a103040007090300d4100501d0121101550440010030302841c0d0005090900e80065140340860302c03c6980b4100c8a032500c000520748002d00081c010140034030f40c04000450142d0344407507041a2000302c080c0701c0ca0200e1081951407045103000320b5010040b094854804059004509080f141d145030846501040c0c50040740d84402020b441010500c058410300209030164003154000e12014000c40f02c2240e0750450312008182280c41040755010307045032048158400c000241c00141504020341c00c01000e83c64000007090010500040e075942c580c01c05000c41c1d19104818444d440e62240c240c0c50908009600403400791540c00010715 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 501000530 1250 500999280 500999293
    0xb0f0a050a0c1706030313080304060306051806010c0f020a0b0403060f020a02070e0a0603120503220210180e040b041a15151909080c0a120204020a0c120f0f02 70
    0x2c141e40842c043d4040050341d0911802c40e2070b0714000908500c9100340e4010384407014a0001480000440540202c0352140c40c10040c1c10fa950083c08401e41c0c0380c040d800103402d0301c440062441d6004400c82c44549006400080402045601203600c000441d0800090b500300418200108155800b0700561164920002d6081c10487c60000e5030f03d1030310f40180301c810344c200b500040b03541505500c05c2c001150800716103001001e12050180069005031918000040740c002c0744006075400712580910913901a06020021000d0310007114840301503800c1c1c3d40030940000c4c0000d4884410800940960301074911809241440e00c1c0c80f6850440400d42031903420729050410041c03c0824208150001080d901042c42d0340e030b813801c00011449820701130000355410554882080358498218010303210410112409145a03d08109226296115881001301c2f640112401414260040d0404040c181082d101c4440b0680d41c0c62106840d140721340002580b26000005041d038001c140c00040242c90028104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 501001780 1250 501000530 501000551
    0x90609060611030403021c060c0e0907050705120a020f07030606171c0f0c0218010920071502070c0e0a060609031a09190602030108010c0f09170102070b0f0a050a 71
    0x11213000b213110180c032864800ca4048041d1108041700b145403540158100a800c59a01015101551140707189011b01051000100c0311800366044889468200004250381d02c021070f0351007059801b4410760380450003038801507568a101003101001551040502180c001c0c10b08440c0110404000700d0364240760b00800b80034214405003071400c030311400c02e03280c126462034052000b5202c80d115424025003003005000420712400d04400b034181a01c000240600003400c003068410399101600c41c00c0c1000100c08c0189c2c80018481c0c0c06480c0303008030154800750401c8115221a400404907511034038141c0d00c2c0c8410050070898070312a41c0301602e114105440318601715103d030750703407100600014000d400ca190b011a0160b00c081200785190091b04407985018189450804081c1d0400e2065044642c01d28041d011014001e554520058505980c2e425040345060501b043c0c161a0407113030f41d10b80d5400c11403403020554040640d0311440c40040b070052981013071000b11040741d000800404885251020140e07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 501003030 1250 501001780 501001783
    0x2e1103010605070204110309030909090105071706040e070b1b060f04060515060f0903010e07030b0708040606090603030c030206060306071e05090613050a0803070c090e0a0507090609060611 83
    0x241568260302e056a101c45051000c1801130032503a4a040e90a04003008010700a0000402000405019183d828850f01c0f04048282610710907107070302010444821042008110440845500c10001400454032001480b0200d08012190f0404011840009103464168074400206404045400c00405c4549482c00d00000c05140180000b002c1a03200c00c0400c040220f003214000b087c0d880140401c1e03940041c400800000d40c44416228002c0d402d00b003c18a0200300440e4003c203c07a000b1043e40321981e50340c582151140750003002204e070181c1d64071010a00d0019445410b028521a4540304500c44003030501030b2511100411951013584500204142180d0060701c8250043c01f00d62a09441b0009990a851500451140b075030800000701d00309a9001c411031004080300c0c400e0710900b00c050f451b0445c603a140d12403104007904c030b038034140c1040148200f180c2c4081c1020484070140c815990aa541d01c40c00d10005d503000120701a101c4c1001d100300c0c0114450200284120f003821500d0240008840b03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 501004280 1250 501003030 501003037
    0xf121d040b03010e01051005040e010203060906040b03190b010306141b091c0804090e0a0f0b280e0706050702150c12030a15050904020105160c05032e11 67
    0x5809951550721006071500d094201c0441000950000c1c0158070f0a40e8001d400b100700e80c801c851269081440c00d0074210b00c18802c82e8040e20001d00444140e41d41d420504c0f001d8026942100d030188510300140c0140f00b11030320031104c010b1080b07428a0917540f55081c50030a40d0000004804016031b65002e02104a110909040c4181000a1400e4641c8000c00002d00200c00c0d00101039030390004c4003082c0080014540c02042600da40120030000300c841d48058903642ca903c0b50b801840081c15940c1400071a81003066164004400c5c0300060301140c0c03d0640310024800941c5044186031141d0407030380d4004003480940060074031440c081d410480f2940000701040038403180241c0020340014208080603050203280e0303040b02c2000c6506d54a0500f44482c00090030082040000c8880844c0c010509141070803015010b607030141d590f1401d0000390400809160f04444044a0344040314800084640713040c010900e481000b0344a4a250440040000202d5104880c1c0340040d586800d40c244500304500094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 501005530 1250 501004280 501004337
    0x11030105030a1b15020102040812090a0314120c0a0201020c03060603210d020318010605040507080f0603070e070c11060a0c231504050c0d170c010f0204030f12 70
    0x10303002c0ba807080c001460f0304603583d00440c40c4845205550710384c65405400500c1201d0340c0e102201e440f101d0603032851a86000c1d02803400e03484124800304101240d24078104800740c543c4242540c0100340c2905142d40341e54015083c01d203240d001400000305540e01400001505141070700a071100e0716050300025150142d0750740c4201701c40d05da034040843d82d003424015220a07620a020440d074034104808060f00c488902000d014117903081020104060405014640c055541d64a0b00912a221480b400c1014400113280503014420480009590007000d5000c902a0016851300040c25105003040c055641500c02c1c001d0003100e00b0801c0c0f540e229030041e0400c135050707000030003000001414007140710304800b50200d00c0d20b180f01743c00c6d0001e10304460590307aa01030b9100d202160103103811641130004150710042d0140c924080f0090340e2551900c100700406c41704160000024940c201134200710f0498105800a03100b0008101e606420080701c150b5602842e0b0b00c0b820041e40341d003050040c15201c81c0030040c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 501006780 1250 501005530 501005543
    0x1030207060f0903080603060106031b0c02040f24060e1503040c0e160306080d0c0618140a030f05180103090812070e01080a270f0c090b0411030105030a 67
    0x21403006120490380507035905840001c041c48071141c1d50400601600d41561401c1c42030040900001c1d10b41d0107841405012907074070a41e43c900090003c41034840c0c643ca070405903001503da641284103c800c0c1c2c4140b100c0c002c801c0ca51150444e02003d0000c00f021201e402c01d13010701c0315081c0c0c0c00c000c0780d44216155010540003400a03a583d6101e142c0290802403580c0205c001c5452101480000400c0c1110385120105035901002065507440c4d48646d00c102d00607124020070207003810300011030303003030341000d1000c0310204100843e000c01640e0340d402008203540d41c100e080d00f1200c2080201940045806400505803919a06100f4400c58000c00d603800030800505266440e2034500030031441009a0704c00d0000340b100e00700d0f1888d11a10181c407800d0120070550000320307410009000055244642c464a516541c0c0541325207a403071a0490034160b140d0b40950740b1010307402c40e00001420303012030070020300301580c00072612268207003d000070303190310703500811420380b040c00140000e0310b0004140c200b0580021 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 501008030 1250 501006780 501006787
    0x3052203140d0c060902031509060402040b100c0b0703020f040b0c060a0501031a04060615051201051f390528110d0c0815010b07380703270809010302 66
    0x1b000a141c07042052403850380703511100800421100c0450400c2c841c600a44090110400e040c0400c0040001c0c103448101040b01d14020001050344250340e29400381c0d2904005140000048014400350010b0380410302da04000203c1c0d0045040a02080380c22040c000402c0c8403d5055a94a01d490030b120703000075041007024000a4140800e03500950300518000d2744001d10940340403001041d90303000255028044008400000315410000708000e010266a00b00d001e0f01d9109030301c00c4482a4034580da080b40006100d500c1070122420040b4162031402014213a5110303000c910784942050542c4415030844203404000e01c1982000030304410340a035010485411132041c000c0080c2040d00a244080d110300302d03210010907560380c0040d2200b0107003007070100040c0c503031b0342e076185101c1c24483c0400041c14210310102021012112041d405e000c0c40031010f0007c072605404480291040044959030000780c1c46140e246580351240351003480b5518501c0a400219400e900c803415a40b00703400b0240e0402d0340c0003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 501009280 1250 501008030 501008033
    0x50f120102040906140f03060613020901031d0a1a100302091e04050303090f010207051e1002070302011a18010b03100308040905070f0c05060408030403052203140d0c0609 75
    0x294110780c054503080e2410031606440d9130b00c0f4002043e003017094900400c03038920b19580d00d241c00100c1a1040714020031841c5600c0389825124003a41000f10400e042c03640352424000c148440b00f4100803494820b0006204010341818501d00041c00080c140e8041e007415018001c4803003a201c05841035940590381c1a5040d241c0140c064400c81600e08038101c0c40c03181b201840104070001c801140100600d104843d0350100b04145c042c200d00c5000301c0209282c1c046000d14401980500c0c84d0711241d203650040d5060805103002040684e03020722405ca00503503603110f40c2c01c1d5200d04000c10300e0300c03090150b61541c0b56003140c480138000035206006000460101000240b003040c0b4020b000006140e000c41103d8031a0742c3d8902c1c4070007810064036424081000e41007150b01c540e2240c01e203020020740200c000c16407900c1d240c58613880c1e0382c4050b20aa042207400c00140c8401403418040700000900380c168242e0301071445c10802007410910646c204141c21000401da0800d83c0301e080c04038040e400100c0041c10340d850313 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 501010530 1250 501009280 501009283
    0xc0504020a110f010903110d091e1505031f030b041106090d050705031009020306040f02041413050607080106050405090a02120106021006051f05030a061703071704050f12 75
    0x40b80803409041c480c56a0300300e052a011341005044d01d10a0700c40900e8850740c14900394452094552003c0000c50250042000c4400d00d03500082a894000007401070f65100c00b0f400e0556030300c2070365070400b1540c00000c0c0129418000c1c2900b1451003aa0f0042440a045548121502201400142091454020007017080e9950400c40d034060100602d54041c145862901c070752a003030b00e4407500f4800d0080c1c40c502c0421481074060383c000305500501500c03043d40c079aa52007044100e0403d040c0d03000390f59009000080382d60784540d540103a005c00e0764150220100c0c9001441c10200a22032002c00007008010800c2ea0381010644098403400c44030011165550840d0000a000d265031090024a0000c000030398a500441c1d901c2503110101d40512101d51249d0038400c9800210304901603a07041c0d13204000d0305511650195400050f10324010a9041c0e9800d40d44440e482c4900c03c0214940000130340e0820005a510107810308042044a941014901000130704031411502d14140036003505003103403650040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 501011780 1250 501010530 501010547
    0xc02070806070c030e090603120c01150f05041a100e1302030a0b150a050403120e0415090e1c0f170703020910020c15130906030602090103180c0504020a 67
    0x3408200c0700c01d441d10760002444052181d5080d804250003043d2201c4904180c92810710900001e0002e164210300d003651100346511203116280709544c0c461030000911440c050b01c0c0300038104601c43c201e0170303800c050800080390786121a043e940008401d0008407a2503115900c41c4215803820f02c0c0d40752101e0700b0b011500c0c0824194114145070310010800c18110034582c030903000840107940e0380b50b500400c0e4a101c03803607218195021001c541309000c100000344141c1c1142030f55080501d018070a24070003502080c190ba00e2a460850250398110f0140709011075846588241000100140340382c00c805024810b4a00d8400215400c00490004003a1840d02401410030344005103500140c0f1403910b400c00030f00941218011500c1203400035030140c0054400204081c4940006044014128803080341c810399a120300e0000310003250071000001e5400552042000660046e032016039a01c03030703201c0010100e030010f0000d8031102c40c0f108a00d50100d41c903017040f6000c0e51419078005985481d1001e00781e07032446 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 501013030 1250 501011780 501011789
    0x30706020c0d030b0a0e1f0306090605011a0f04170307140708060c03010305102c0109060501171e0a2a170d0507020d05030a080f06090403120c0207 65
    0x10300001d1918000394000400205204103030350204120251007080090141c540c0c42909400800200807901456a95140030324a840211480303003400c0d904d80d42c2100791009030400340c900301c0d84d980040090301d1055008088560b0308034000c070300d4903002d00b0014042d40128003408018505070350315804030f20420030403601001d42101031640c04040c9c00c0f0b1419540c15036405040404e0003180b010805503018001528180d0340c1c440080c0582080360506100200034031807154030610203003203203004020508048070f427498003100000704d401000c6040500a40310103900c0082c014680500c030440051010840211a001c0c1d0b0940040c41583e0840c414030f40f106031074001c3c1c05070a410310340280300e400e0b09410f100542c5444901c1c45131291780311200100b9403003040c1403e0054000f04005510248035074000d0001350710041656440c3c00103602c0c0c41d855130b0011480c910119500006200202216800a03a4041021038110b10a8606a600140b6024101c8030080c440e40d1a079207000611070003408024040e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 501014280 1250 501013030 501013043
    0x406030f140c01020a0c030308060109090507030e0705031908030a0906020f041d0402030c0d020303130f0614070c120f051f0617030f0310090203010f0f0608070e060c0307 75
    0x4029414a03807244244400740d62914815416400b00b60350004c10419010382d0001c030034028280c65034030159009203006107800d0410850174008038160416116403401040280e03400509200b80e000c41519000740f030b40000c1c1c440d42c0a52800d68800180e010080001c17648103801039201c1e2202031016001d40030b50b000c0100301c1d0b8000705403400d00709074200181045900300d42e081201204004818900301106480c007a4150b04250451802c034181040b400b4411407000e4212480c3c4031090821440c0c00c001c5030040c4e03804007400c120070000c141e486011600071a9884141038501000d81e40d03003040700c14041c40343c0c166040d00d00b04031034184008a5a22021560000c058428024092540140303817000320035040700052a000c00410400d284420059814a0000045140848920f02e0005075080103141e2003506c42c043d01c021900412070f00143d402041d005410864007820100020580c032655005041000817800810009960211b0314034010f00007594800d554a203048021811403007035400c06403c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 501015530 1250 501014280 501014303
    0x9060d020f040f030b070e010521190912020c01090f15270905090307020901140303192312060409170a18060201050f0f130b0f0405010b0102161202040603 68
    0x5e00180b40720451248000c0d55507800442001c3d8010f4440303000d540790000d03d203e081e105030803c0c00e40725102c260300400e541c243e04402c0c89100341054240d0b1034481c0119a0540e8512140340b005030100003000701c0080900346443d0603802c1c40740b0002d00c41180d00c074106280100c02062903800d07014105404007a066900d4010400c504480d00d03156990301c600c103540c446407620380000c0d1000301c0031041d6035625a0003020555140d280100041d00c1644101e05698135010400c03201d140100c0d0304034001c011760b0454681c00452013440780c0300380c0c1c808201d440d1264546010080f501c080840702c03242030303031010007101c0000302100c20b82081518961003012480030b000c000180d180045801015040c1d0b150500ba41000d607150302e50804034281c40044d10007010718800100070034040c050031040302d0380c002028480314540c4c500716101c2d40d02c100f0090710700391443c403848030600c0103203d028018144244020300051100c1d4000d5054480d2441691181e240b0803c1c07070000010840d0f1b41d0750000001540c11414a168 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 501016780 1250 501015530 501015533
    0x210302091002011a150c0601061e0e1012060306020f13050f0d0206280c060c0806010509040c140a050a090618090507030905060c0c010b010509060d020f040f03 70
    0x39030002884521030180c140c030128190b032050048411495a0b04071041c1e01d044544240032441010409090106005001020070072004100301802000313aa501c07403402044040b89805101c4800c000e040800880c104000e0650321098114070b4503842c0e41c50031030701546407082c0b40c000030110341d08018080b50002030000d100d2090764020f011027140d048444103071140da0b141000b80003104020b419420803800f10030348000d8640300010b0001c00000403007141d6941401c80300800481000159a00800c070480c2d005030500c0300d64445c421110140e402c003030105040072000030b0254020049040d105a07220f180792000c581c840c00d04c003241031103041301c0c081d1151040f510150282e0003000307281e0b0008a000800050040c40b0720b2402c020850385081c8140540d081c001c0c010003a040c0106100103054840114400003a0104a030610500c00c02c0030840d02c515900c0c490034291042070035010304100701030220300801c0d6528400c9880741e603034140c001a625a4a00c2d000081c2d4044c07a80401c1039003904580000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 501018030 1250 501016780 501016787
    0x1051b060717090d0c021c0f060614010e040c110a050304062d1b080304060608060a020918041a0106050c060a0c020307030c0501111804062c0421 64
    0x81c02048942c0b0b076040c100700d0b0441d440078103450466a642c0254004030381c110300c4a004440211240d400906000e06020461000c400c814900d40030440d10f60307102500e8201884080d00c15800601643c4503096614880c00d40000c10300442c41801d1446142e90b0070543e02c41c1400f0350301d03800303070718068070b00f9a100381c505400d00c65240c1e01319120705404103c4921901e4107203401c4070301c0c00d201c20403840002e2121055800701251001000c11041144001440040303000ca04603501a5204a101c0c0704041801ca00700b400582c188000030f001121224014000e410329070307131190740100c1e84050503804200a1b0780c890800704130030b0b408042e12216803884d0000118200360f11000900904032010115450358032110307072100881c0d418800318001a04107208250000f07119803802c0540038016000807600540c982071601c5c003980160808005001155130003034840c1014000e1900800000c0321241030790700f6011200803840d402c01550310325484040c0c009020041142d482480061301c454019026441070000503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 501019280 1250 501018030 501018043
    0x30f0b0a03150b090921120f150306060a0501030e2b030b0f0d0f0c091505190f17010e0a08030901051609060311041703092e050901051b 60
    0x100c1c182c28540c550500741054404c1900416080e0010043c19080100254000c00050060243c85104010040340090454039541c01905400f2040b08281031440e8078503442c1148a20450194004e28100283d40c0d88109550301110030a00b00860540117032102c45040445091040c0c040541001d040c41d60045001d001d5098903070381d500c00b04200c005000800c02d0011134640c4203680034100c81d8040d00002c54004601c4000c0380303d884407011941d140d12001041e02c200c0b100d0003004045640781080507191000501e242c0311200b02e00808039900f412441901c9042602684140e40020b035603138042058254801c8098990350350540d007079801285072080e01c0b40e10540c0d040c541d560900c004241028440190032882040503203510304020310b0100150b000c0c1c0316600004002500900c0001a0303040c00c140c4511440a0721400340d6910707500320040009108200000c508000c04c104510340e4041c100c0030499418400c10700f0240d445400d140300485440c400c2d40420104800d08900d824401100062003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 501020530 1250 501019280 501019313
    0x80102030114090c030622230a1d06060111070803030c031503010b0f010318080f1e0703120f021b0706110c0a050d02060c0d050a09050a03050d030f0b0a03 68
    0x61129120455030040c45d0105664141d80030165036403000d02c1e09050292107002015000b000709030000200c04090308102004c0324640b002290b0810480c0002540c840c0c1100310862203420074066105000442d034903c4010821411300000300d502000c42d09040207140000c0450a0440380da80c40c165100c0e040e00d4200303480082903084003c0c0b141c40d0f00c0c901806188000a0040c00681c0f0001002c0c0044010f0054140c56085401040445c0408950810010110424150a01da58403003022180c01311123003e000c901404082d00b403141600082e0f1042240d420120090b00115001c40348003100e000902c507580b0100480102c0080c00325403000701240c0b0b40100d0b0307400e4139080103081003500c0144e155a032460090780c5c440040d4000b80702c81d01c0d1441809081d240050f01031030400d6184550203180c6070005003541c0c04150040341a800965220300140040d181c140e420400342071859503401d540ea01c0781c3c9289400d064031011f0450b9001c1c0503a11a0008070001000080050380d0307810091185002c4918 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 501021780 1250 501020530 501020539
    0x201020c040c020309010e0f0409050604110a0302130e2d060702162106180b090a0b0a05311104050c04060f0e101707090f0618080102030114 62
    0x944210500c1e040c07003036844056250700514a085005401119241d582100d41544081c001c1c560766001c3e1502e10403e01160300c190002c04441c182401c0240e10010710f20a01c61041c01c0752081800103864000b007410100014080108078a10501c10583c100b03102e07c82c803c100700c0d03032124503194521003842c016100d070360f81d420035607072507845014040b03071550307101c0707035601d0850040701010004d001d0010303420a08820003514400103405e0540c0c0d1041a40d4000c112100a031083c014184140145180c0300351704114034030010264240b0395074038a100d10000425004003a5035440000f010313141807a90800b010052450941ca018007800200a108c8114200545481c82035900b030f905182003d01c42c580c0a0f240c80c1c14010305092a14a044400c619440441c004209041d5245045916585030010504a8540724494038502e1240320100d0144011328100c00c0240c5943c0c1000f2401503044010309a8006192400c40e107414014250400c185640c0703d54115807000000182c96010714141c0c0411860486 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 501023030 1250 501021780 501021793
    0x10302090f0f01061d1e090702060708070c140a031808010218060703300e030703091401053001050618040b120105071112070b011707030c060507020102 67
    0x2400611000c0c821182d2000d45002e0700c006002007400380b00200300c03180075480e01c440c40000c01d40200300110440424960f42200740c002d51401c2d840c080c0d411951180ea1440200b801d0b2400b000007c200d01006070403102408122580d032800d000844d05a85019001a01140c90065941c50000c0071400050745200c2c4400c040030f03010442e910107001b01c5502902c0480d0514101400d6070070001151311106045050002083d9000307040c50380d100082d02074050b010400b49981d017840e96401c05850840102c2c2c0045d03001002120000b94004a4900645420161030384000c3d10520050700c00b445041d10048240000d4204411503400c050f0100c61070300103c0c1c0000364280d0f41d4409100c494041e1a41e10a02c4d40b03401c0400c1d209900b400d90101c80510303402015903040c03d40c80841740d421210291200300008408070301c2e0255510341003004501c40c50200e6200382c500012900c681ca01d03e201130042550480700d41003181080c4034100014400b46400c842c1740c0010f01e03600c0304068055480300004901602845 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 501024280 1250 501023030 501023041
    0x305032110060203091002070e010605070326040b061314060a0506040501080c0313060207080307090b1c110c010e0601060e0a03030905131e02040f08011104032904080301030209 78
    0x300c0c01c04403442034005508101030b0808100802016010341000c40c0b0400c140096203071107401c1518000c080300d840301c2e55500024207000b4802d898200305241043d440c0c2010301031242c042110741d0ba1094100d455a02c03191203c0c1d00203070310101400402400c1a0400301029401c0c07402c6e018080c06142c0803103980c14241c0c1d940301800800e00907485403902041c22a400612040c02c3c6030011a4010050b2840f83c0c540c800941d1040102d801080094541003004070030010703011340045060010b08054046103041c500789034000c1027407051541e000c0100644591540143c02c0c0c1c000c09072141154054004c2c05201401c03001c032030fa60702c400d00c583c00001e51011103409450600c1e9a000d0143c0780c241d6290001c03103040206000802e0244035072505074aa50792480a030503000d0314000040c1d800c0111015a0307507440e040d00e01c52400c00c0ca07000850a030741350144018003480c400040f2805c0701e51000000d000c0f95400c4040040342c2c520070104c0600e200d5248104410048a40000c44c1624800ca80081294441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 501025530 1250 501024280 501024301
    0x10f14090c090c0d0b0303280309200607060e0c180c12150a0801201206240a0201020306100309120809070b0c1b0d030203030a02070c03050321 63
    0x1144469004441c0b18003040f4610f140c04002c0c01c1103c09000301080410390500802c3c599030045841002c0544010124400c0301e40c07000c21441c801c0001d180610a071600b6468102e0008100c440300805050451a040484d40f200003c2c3e400564000404100381840300010300d840314140d624807441500d0a074032080c4581d070006141401103848103103442c107202c2c1c600c000107a075800142603400700713186801d108182581c07090310a1015002c0b00002260b50b001210340b50707661f14040711060b0000d14080c0062018404084c07511030340041c04540da0200e0b407024039075072141d031042c3d00c064a0203030b00000384000050742c05400460194106449403c0409494503040301160450380004004102451600006910405600750810b80c03a40549560a40d00c50002210341c0c0703c000c56211035040210340c44602440325001c81c809070810b0b51848003d000564000351a0701c0300a1000c9020396001c0303041802d010050204001035903100c03044981c0d403400d84802000e0b440309100090404c000c00400145103240c0e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 501026780 1250 501025530 501025543
    0x40e07080105010e100909020109050603040c0f08030408280c080f0c010302120a05070e1002010506030f0607080109240326040b0d2708071406010e01150c05010f1409 73
    0x501c40c61840305d042c18a00030601070803a00c6016410016440e01c00300303007a99030000440c0103034810504508e0700d43ca01036001c042401d49a10695007a04184802c00c28090042a4403481503a912031503000e01c20300e0580c0c0c00c8140813840300902804000350000c60034400014000301048a90003c1f10b914940c100011021380c0319040d254995030200700007060a00c90290440768100c2401e00313066092004440c08204850074001c3c030303000140e4482c024807441e41070900c0820070301c21101c3c003d041d40340780125001d00b412006214040c040e50342d8901d602040140500710009d80a0213002c1c0010b440e507203062903102c2c4079003030540041c142c02c0c0306024200c3c407401504503021106c0d19002c80d401d1200144040c402803103000c0c1c80001514017000820360a400104070001ca0034031950907191a5002800c0c000b0b040f46610603044c0e072a0f4409001485550703e88402181181d00c04813003400607114240c8110b64036800807200030920742c00c00350540846481e82e08040507004402030f02215941d25586070301da4551 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 501028030 1250 501026780 501026791
    0xc04020310060302210a02040905011d061c0501020708030601030c0201060f1512020c0d11010204051c06020c011d0f030f0a03020304080c070306020a031406030706120b040e07080105010e 82
    0x4820010400150f4029009014145540400410300085503c0081c0420100b00d4203000380d00d40c005414030902c00b0340d118070f9014012400c107022210040d601c00b10f0022001500c91441807800652081e045064450007103080d50b8040000c1d51903401d40d00d010034003030f007003a20b16502184c1404000840584144503210488050349041901c0f00d2038074104031401c034510640f45082105d072034459401030300e490000b40000c501450003000320400440e0002e19010110a50075150f07401084100301315565186c180400510040c2c1c134040030707003d03031800c0d800a00c02d2401e450f13142c0d420002c14103801e828122112640801032400d41f114242c0f0001e42680702d1280b410044115001800840c0301d20b4420b81c00356a1092050300c2981c50304011200d07561030302c200b6a20450310190002030341c52480c0c3d0b250044e010b905c0c100f500d02182904120700025166291400b4040c00c00003051140031500c411600401013140313010300704100341040c1d8641e060701c400d60350045d13003030540c200030001408100c1c1c080c10a01c902c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 501029280 1250 501028030 501028051
    0x2b06020301050901120f0611071b0e0f160e06090d0c030b07020f12030907080a200d0f020f190602070306110a0f1101020f03130c0501080903250c08060103050c040203 73
    0x6c0382c150340d80c00020003e1a4544207007840521540002a02081c07468503480650781804400b40e02c0c150030000c80e140c1c0200000b014076011000c0c0300701080a41602e441d02644c0d8104030070548280710114030680191040780740d011401803c0202406001414502680d004606105495581e042c050740d94a40b1000080007a40c4511141140e1144010195400c110200c00380d8030030301d43c1c510845140c11100130b0182c1e40c54521511031080045078203080100400140c80d412245280d645410410510000340a4042c09410003812140d94a010500001101c12581c0803400c07a16018000c3d40c1d11114001210114a415005020031966400341c641e001c4955aa0441c11a41c801084400b2400e4107820419590207103c1319a10260540c00b031842504086481280c114240c240241650700f140d010b40d0602644200380800e5140c00700c121040030b60180042c10084540c03116510300880d0520015044c00300ca0302c13021521860226002c1e040768010f00840d940030034000c0400040b4442070311081c140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 501030530 1250 501029280 501029303
    0x30e030901021b0f041103070f0e010503060f01090905090f0c09040c150207030503180f04060602060c0702060f07030f0809060f01090e0c040c03060920092b0602030105090112 77
    0xf02d094441000c045501e028101030f41e008076200200307040d100520710035100d05101208010400760710030300100c40c0c24018078100c030a0030454030000c3c2951101400c0c0c6030240ca03604002c1255a40111902401054012810400c07894484251030302c5032080340707140c0098042c114202c4005d184c03261119010f5030704251485580340c0340000e5241c5e06100302d4144420b600445c0800404a141800030740501c1040042440460804d2002c0200070a40d824204d84103d00e0301c88103001d01d643c005040d50f4030240c000380a5079940c04078000207841c4c4c05102240c0f1503182000440f0010164001c42c0c130003450815445400c200c1c1c07070b11041c180c0c8842c0200c8055402400c01d45c010404203038541c100c0c928080c80314055404107610080814151284405100c0c0441c3d01e850701000101c0640c407512100340800b80007250514081c1030850814850324015038030509501c111a050040641070030002140c2070141c01c03c2040151500c030001c3c3d00f0074824284648a110000600e01c40c04070b2501c0406584101c00c03020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 501031780 1250 501030530 501030553
    0x9010305060111070e0f011508010b090102100e150c03040b07200607080610030c02030706020717030f011805010b03130302210c01060801021903050403050d060e07030e03090102 78
    0xd04008050307a0400c1014241c0969410742072120704080c09000e4000b070903603c0d0054a500e0400411303402816407000301d0780480c2d0000d03840070000e41520b5054036160b595001da400101d180960910021290707500c1c004090700c00c0e8034001034540c0c0c0048007203101d8001c1d80d910351401000f8002190050b0011904400040fa01c80c0f00e00407103455010944006401c0c03440b06100d89141102c02c45480010450440034042c162520031400d602a507110700c0c0c20301075884081402074032400b65039001051560049400c0b020440c060348007608650040c001039449180c909210340c3c10a90070702c1002c180390702450801c00e140e60f0314000c2034143c404e14044a032071525000b02c03101c81c585c000301059045001c0c0d8004600d007950101030688150007424403d030703220128201202e003112403030360200400b603104000702483c121142d0303001021440c103410001b58550b91400c0903599442200c016868541c900b0ae0040f8446184007605070040250750780412415050020b09030b074a103e15a030150242e03204417a50003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 501033030 1250 501031780 501031787
    0x90f0305030c13030b04020108101a0706092a080a1a0901060302121f0905150c0405100906030b0306040312020708090d0501020403120e0a0b0a03390309080901 70
    0x58109240b10b6050f4580a80c038829040c19200e1900103c46103400c0300c4c280419036920215003078000324500720076101240380035010715103511841402094440c020072842c05100c039590140950300e40140c1080031616001c24545070740043c11220502803081c601022070f800d0030000304c20004544c480140c40c2040b05070a0090070161006202c01c44541d21510f002c001038589000903450200850010008804154030f81a0144079001c0c903500441d2a043d40403011650014428040a141c41203c082e15101c80486240d1481260042508820a24480515a51f0000c14203040b03464690703081020704800c00030180c40d5501610040c00142e10030700085c0305101c480c0d0040030164030131801c02c0e2800c909040411040060720106881076540030508200b44010b510700c088500703215291160100c02c4e9880001c18401306030107000640a008542c440b02c143c040d5215030494004140308084d540b11a42205450540980f441e03007428560544003220b05000380265064244d01024003414a1410070045 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 501034280 1250 501033030 501033037
    0xc0624090204030312090602090d060507090806060901050415030c0e0f0a0209030c040b040b0d0c050319081213080310060f0e0a09180c090b0301060b070503030714040f0b0306040b010201090f0305 86
    0x7e80b40f46a01b08640412aa00d07041c410312064070541d00400c05151038800500501115442801640c0001e010010075a4988040314107543d03040b60f00003098211814801c0c900401500001d2200d16804400b2503000f100c500b90910540700d50004510b1650f03020b04070341c01d074000c1042c03035070700360744020440d00062070700e5040303500320085c041c01c0081d400e006900041c0c00e44d04038240641c1d41c00090b5000344620304040c00301403e9650340c00310107801007516544652180c0b00d0f48000d0842900d10301e0215201ca800217944004554100d1005600c03810500004030003995a8440e203808130f45152020f1641c240194052072800100400f540012850001a9001750420a1003140030070992580140020302010f0352601400c03003c48002041006d900a050840c1c1194200740ea141d2024000000012000030881e60700c60700a140c41b4410030008076a660300c50003181c1000b00800c6112402080100306903015603c0313048115018400b60390a100107900302d505280016007000f1402541301e0100340904001e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 501035530 1250 501034280 501034283
    0x6070c02220e030d0b0a080706021b03030403080a0e040c091203050304170309250f1206060506190e090705071e061d010c09080c010f0c062409020403031209 69
    0x1140c480b00c1c1c020600d0031030340300912000480d90b403005044502d08105c03d07004040d1000350000c2140c141013079400703552040100c3c00d400130403c0c1c602101c413040d00c050003174400443d030107040240c40d910071190107843d62641c460f50501940c50006040401d9108000050840d44030315810f641a0001e030310211000d520080094440c8190341c4403c10b030b17005c1c42074001c5101340450006000c54002482240c0d840d148000d6403101084500354050083d4801c04030300c84202e0395840c001c2440c2030500e2030200041c000d143d021a500481c007060900f400c0c03100e0100340c409103980e0b03035480d1b8040d00ca250070001d0103c01030796481e00041040c000c3d000003d2030080c000c4c0480034101004040420581d80780029104444440788240030790070507210b14040c003401215500c0c0ea050a08600881c01c2008840e83d81120303e040c3c604105142d40280030740c0d409140c2e40c4008942166090104002e035021041a039880003065615074038100320005041500b91080d41c0560760704d46d0712011a4048d0b482060007410030f5150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 501036780 1250 501035530 501035599
    0x3030e032b020f060103080702150c0318030f0607120b1c08070201020f03040305030703031107030f08150a15020706050c03031f090c09081e0309040207081909030506070c02 76
    0x1d8480e00203c1040040c2c002c612800c1c14a0761070301c140c818401000c41448040c1c2d020b0400380041140e054010081d14049840e10302c8010030102107100103490410100d400f451540903c034188a90b007540994a114014a41e00c2c023408108600c10a10200c0311302d006002401c3d02c0a0071260002840000c024141c680c01481215080040f1060090440c2c1c015401142c05a000050b402c3c10503403d805401d122007005600942400d030f540c0c8000e00440c80703141448081102540000d9440c03500c1f0801c240c600c0c0009021160780c1d0752100703150f400d02034408800706e02521a6150016490b44280101ca03071000b1300001450031502c0302403a0200450007141d46c072004041a1002041c20040da01c98402c1c5070b559503850030412032401101c01d04203200d8207006031034408600c42c4458035010020403030b03054403c10713503006940d2069818402101c0c0100e040030303440c0315030300c6c8020070000b5030080610741500c0c01241039491540741c221060714003c4040000a42200680c00e032981c0f00c14000c01000f81c2c80c00030740ca = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 501038030 1250 501036780 501036793
    0x4030201082212080402010905010804082d040b0405040f06030305160201030207060f05070e09060d0b0a0e250b03061c05010905010c03090b101d070302070c03030903030e032b02 78
    0xc0d1699083d00407090072000281d8003000b000705540e800f05203400180003c1c205100541000d45485885105054040400002e81188035001e140300708224904d01c0140c801060315a07441e02c05907031881c0d01c00d208851055081a00780d5071044030f948204402c4941c1074403140d14140b800c40c0300c1ca95100d50041c040e81499030a02c8018045091405440c18480034024000b407070340341800d000780c0480c402c80030050203840703602d040110700c0c2c03514640b0750706464200756400c58958402e0b4600024040300409408540500c0303550707030b040c1400710044007548002e040c841041180c86071008a410b0100b00e846640c805005502e0514110341210100c400300d004a00100c3c4100c116110b00382529012006440003030303695040f0303806100c030408030150880001c0100e80c227001e140081d0156500c0004a003e0641c1c211440031030000d42c000e90403504d8080e800000000601e40d6810b003e040d0045a10040c1c01144074079004640e1440c01103005110303006c0300442c5111501b40f071289104080b101c0d401c2141940f10b0300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 501039280 1250 501038030 501038033
    0x5030a031d090c19091a1b160305100506031c020c0a03080306041d0d031121061219033506031911090c1213020307060203040302010822 60
    0x2c80100d48110102450142d0300e900035903107052140c02e09070540040000780345c41801103584400780f40003103910913002c43e515070700f01c001203080040d216291070103e885001c05003035040e0030210711602102e000340d060ba0840d82540d9155410b984003100d07465415008041c400201c444409803810185e241803044880986101c004601c281c0c007070781c2050b50a5400401002180e00d8a03003c2d4044103540d400f00134040440e061880c6075204030341c0011a040c940c071204802580402103050b1455403e46100d400c4401084610591003a40c0c01d4603100d004408981c0346214a030390000718440c0345070100c141d210b0f00c803145450480c0c0001c1e07405a0f11143c01c03620724004c60054840f41c11001900c1142408001c2800d03d501050f180031589071a8401043d0345054001c04030307480c030502d0318000006844184850351020040d07100c51291010814040c0f40440511003695200c0d00c5400102e4030a908481380c0c0e0317455100680c1d60b80103507c40240000c5a02002401500034000030115100b9204134501120649 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 501040530 1250 501039280 501039289
    0x51c03120b0d0f061817030601030b0d060203041716230106090e01140f0f34171012080f07050d0806040c08040b0907030606080705041505030a031d 65
    0x20701205884011008000700c0c10701260707100c3e5440301e001050989016044071751b01c14140f02c1003240030f031000400c08000240143d00030b4008102100c0c004115041d030f0519490000000c2d007094505a50508007000c10b0610001000201c610f41042c078012144d0001d5503507102c4c036031000d0001000d21124604483d80040c807109004460142401d01d8020070241c0c844000701d82118503140c0c40c5900c00801905014840d07001d010916040000e18840c80c02075610301742941e89100081e180010342210310b501101d0b50815001560071000140c4d55141c000c5408810745034143d950642ea0400d01d00840c10040101d100071140d01d002e254480c007246414511115101c80e040e403c15107060f1800d8000e0320314000025481703231b00b042d400a4111410007028144220041170801e00800003001400c41e4004152505400c202c00c00055174411001e000440d11a00429120485881894040d90400c100d0180c40746a01060304241c035809001400c8003080d40e14101c5070243d9410783c402040034007180c1040540c44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 501041780 1250 501040530 501040549
    0x6020106060e0f04060312020304090e07030c150e0a0e0105090f0408090d0c0e10060807020f0a02211e1006150f09090c0507020117151e03010e0115051c03120b 70
    0x51fa070050740c0c84601d850303040760503a0041ca00d900c245801c40c601c1400018240186001582c0800601c00961920401d0a80c0d943c80740f040055401140d41d17000249103c6d645100c02d06850701510b0006003031301c13984c402d140d000109580060030b60780c0074803c0c0c00c072a0500411140c00d55003c1c105050362142c0c1d0740c280b441c0e0301d070342070350904040740d41e0400501080b5000700d0880c3e04404540b00405101071002041038a88030301d204002d110f950407440b21407044842c00c00e010f1508401105642403d041aa043c1051002c0c4006114403402510200220380c0e62520480007103440d0080ea85450000040c421565402c40399500380c01d01c10303c0040450700c901c6078464050405199116140d80d600240000341c2140000c402662461445004108108072105280d209011041d035802040006400c2d01c02042d02c001d2103403e070190303e400c40400000005401000c10628114000114113485006102443c405107039010f105012000c00781e400070f8414039814020029440c000516260080c001038210312 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 501043030 1250 501041780 501041813
    0x32d0d050c0304030818060c0d110c15070c110f0402120106111905150702030903100203190908180604030b161202161b09090308040b0106020106060e0f040603 70
    0x10740100401c0b08054005100c50b802007000c840c01800c41c2c040c41034250307444a00a184144922001c5100608052103411040061a081c80c4490300e031501e81d15013644e10000f0a07040300c0e20409020120350120b000e079081c401d1003a0801c0b440e040e41e85c010418015511301d00940e00f80c0040e400c000c07018822180401d09800b030f168aa40360010211800c045078903113240c0107006100031581081c41c0001030300020f04080309442e8403107030711015070b03c0050076401c5004510700c054240c0102444000c614540742d0041d449a1180d0760300300540c0c036a8044a10484c0c1594a006244050400c004100c06801c0c1d6000b510130301006258610f0a0344030b035582078281c8002d0710802440e20f140740d10211b28581001c1c15046401c4401c40840c20b10700b000004418241c2e00c032401421156000c80d5030703102d104208007800d014140c107271001c1c0628845490004c2c0613020484050300c0f40d504940002c078516106010750f804565465076103007500c1d0003680420200c0c0722808030441e40b0070743d2088000300050fa030343c12012111 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 501044280 1250 501043030 501043051
    0x60d090f050105011a040306090507050307092909060603041e03080403080619060f02030f18180108060408180409060c020f0a02090c0c100f1b02032d0d05 68
    0x103046516010342501c8040c2c0001e1680d02207209088890b00b0307444140e0f8111b0ba003001b40444c100180c2d041040c10006280c200c66054051400081411013058004035240c0da5100c0f02c0c8100140301c002401c0e040307180b69104c5a8850700c07000116006290882c043e58100c0d00a061048100d1007103450451a85030100c011408680a0820881815004141c155211805a035116000440c038000b900745069540100c170107100c803141c1c0c14075640e4800c00c10354030702606401c00340e07a440c0b1003092900100340c0c0c82040c880c0705088100300c6003c4801c1e0302103600d0488844400030040394480d40e07a514901d4115440200300380068a00743c07022580c403400b51810603401500d0000703519208072802401d0000c440a1045c055002c441c010006032030320301d100ca5114a40401301398032511400112414600300b1040013003100d0604044903030380d40440c1d210301180070000804003d4204505004c1ea240d0048610403030701c0e4071488a40d824880c420404c8000005409581e561500c1807013210300b001c6135015130381000704 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 501045530 1250 501044280 501044303
    0x915130e011e02030402030a02150c16050a05030f0d120e010c08061c0809040207331422020a0504020a120509030f0703180b03070320030606041202060d09 68
    0x5080050307801610b5216031400358514074043e000311750b0b10248540000c0c0900d88548807000c0480c1604180c404400f262000c2e520503a040c20701c1e45254010381e014680c070411041100095910300000c510001e588041c1c01340545000840003900c0c8403551399001010075807503044081c100740c0288980480408035407210341250508005000d1001050800e060600001050120100e150881601d21064044a0151343c58065103042010458064450210714a58100c00351502207281044100c0a0143d181080450107200c541554004152142c02c802d50018a01521030304200190390364660020340056451565a00460101ea002e0f0302d0b07040001e1510903009860301c0c00c50040a0700035005400450505942a04004c0f0a205428008040c040c000440c45d000074401507043c4018544001e2243d10707407524505c007074040c0c4580300c4001202400c52075900c0003e148102541d0051070302511a0f400c1500380000b91781041c2c00140140e030f001d042400034500c40300d224080d00c0c0400e403182101564 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 501046780 1250 501045530 501045551
    0x905090d050a02070b070807060e0616050421050a080412110a06080621060f0415050103030e0103110d020c03190c1e060b090403180b0304020915130e01 67
    0x1003426140c2030100700002007040942d80d90340001c0d507106861503112402d58030310141c61300f40401c1c0704082c00282040e081956815015402256081c4a241c03003800001c0e108401d00300446080c45117006140110040b500100c0c4c01007042410343d01d1f224030031800c80315001e0355a03c0740b010580196003c002c403521011101400c110224501486108050b81c0f603803403003410118054426000140b042c9c0c0901140b01e0788010108101402a042d140024155040f40c10103490300700840500701c0301500c07194004007810603850700ca0700c81c1a0481c1d4260342c0780103c40e4444001100a40146a074a400d0b001c0203000c2610744905500c01004420744050095554081080b4004081d1440803082c00621034040c03549808a015000003922840000c240342184a20514009000340300718403120f80c005d1208410442007540114800750400319034401e90000d20382d0b46039016a1480110384c0250462005070200b10200f400c10620a1501d0004242c0381a40c0b103144d81080449103c0040075900b40e45a048241 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 501048030 1250 501046780 501046783
    0x1202060d1b0e0301060b19140a120b09061522170d1404181823010911042a031512230c0d0f0b0108150406090516090509 53
    0x20b042800a070001d10005141c040602014000c1e880714042c0c0c0f00c4040e07000007400b0722404801d500d08260300c1115481d100c0c0514010000381000340c000e43c0b0a498400c100850b40707046c1401c0e03031044100422034a8504c0301161044516004458045d0303400c204440c00c80643c0303162000000103032000d015401c1081050020852a01c6c10500d40039050105400100b21401c03160300482e01034500c040e00e200e4030400140b507098024160946030450110713218450030704000c81c1d01e081200045d071400c403051a404c06003c0c103500303d6201c814006c00001071101d40300c0f0700741442e4000307140b200031585480040b4452060044c24103c1181010700000b5074036107190481c00c9078000c107440540031100704580da51500d80c1d1030021598038040e040d40d07843c290011500d00d2080400000340501d0021300400342030036444c5000202c0c0204a00200c4801401714004107071540d0028580340182009102d00b10b5580310f40d11423000800d468102618140038007007481e400c034480050340100078120744000142e9407a0410105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 501049280 1250 501048030 501048047
    0xe060907030203040507060509192408060607020d08090a0335040b030928060b040c05250b15010806031203010b0a02030415030615050c071202060d1b 66
    0x28041c50b1040c020b00c00882c0b00040c612080c2e0301a81052651400700300c1c0085c0c40e99844e20308580311107044507408a000b040801e00d042d6400c200e920307440309842400409681805003200c425801c91010311842016140141e8451074580c000d00d001494006011f000c00c48920aa0b003095900d082041701c005d001400316200301c3c00103d1b514041c0e81d80000410f0309104c3e0340c0305910541241c0d0201002081804078140640408600c004040303015040c0c0000032040c1c0c800e42c400003622a0b91910309a4840e50402c1e020382d0340f000c1e020b41d881c0d81c907018050f42502d150183c450818840c900c1c000c5100c50008040202007400741c140d885050a00f484044001440c1035002401103019410a000c003800000d0440c0589043d04c03250001c85845a40540049245000f1540042c4400ca2008014803015405d130b0300c02d0741070351403604609184420314041980c441c4107901070085a0351181c0e80c10080c0305410216803092501c002c0c01280751a500700000001c0d91001c940d01c0380d4065003e00000c40e0990042444c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 501050530 1250 501049280 501049291
    0x50906180111010513060903030b031606020708030c060a1e140604050606070b060609180f070e03030c1015170c090106110c0d0f050307050105100501051c090c0506040e0609 76
    0x28072485c9001c40c004041007804480c02410141c451082c0c1c01054005e41000d00d0300040541298036003440c0f0706000064014611801025000300345c0003041d4010040b04036484400c1d4180207043c0303500c0d4030040344c00500d10601244000b410301c149040000c112402502c0c00e0854a4202c04201d003812400c000444101a0000303114000c204144000500d10035102c03035012101322070498030f408011011038500d1f51460790010340d2980700c8003040124416400b00901402c20350b0364401100f080720381031607540d209035040310544c0d6008801c1003a542403181c03c144040790404440c4208a03950b900d00d08020304040c01c1107887d60300301038501091410414a054010407140c900303041204102034000c7d4450305100080c0e405184800194001d02074011a90030f860703580070081781d503540340b1407e0813802044280c968176120081d02500140a40c031890070340b01e1400c26090310803075540700160355a0050000010440e920004100f0020b413a60f5680c0240008040c0c041403a0300d0341c42c01e0800c109000400814 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 501051780 1250 501050530 501050533
    0x60c0c0d0f170c04120f05070e0c07080a030605060c030c01050c041a0706020f0a0807030b0607030822060c09050102010b150f0a020c06030a090209090d0e10050906180111 75
    0x240c012980c0e92100d401155070a10b07004050a54460072103000c01481141c00c0101c5810041c04000100040200441d1029000300d065441c40754031000750a0a9074010382d0519180c0806000c103002090b144002062150514100055000d9540002c41c6c610b4003c07044611040c0c0010813030b100194801c0c0565548038080d090b1103480c150404426005842400c500111b01c0b0f500491203200b0020380d50b0480380c15600e0980b40700d0716640850401840da003800c4480c07000103420302c400e881081c1004001e032420b195158484d9016541c402201d408481d6400085503280c1e900c0741401800700c1da0500c1401e250207004e1340c900d02c540381008000f90a42e0140d65089001c0c903a010541d40740388805005032280c031504203200554802c1403000482c60101c040704025804940007050000400c200e074045d1890910942c1c1e80c007025550320500c6c90301c496001c00030302c0109480422a01091030503000c14003068230315007802070400a068010509030f13084503042c1d624bd0700c40410700b1500b41d84c0040000d400341540a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 501053030 1250 501051780 501051797
    0xc010c051c0b01021002130e04061b0f171e1f0608040c0b0906040f120303110a270816140a03120e01050904050a05070315210201030905060c0c0d 64
    0xe000075a990b851403507260310b0a80c045050b840b401c0d4281c440c803006020203110092281450f0400100414101c0c02c02000c03801460661042f0314043c1c20300c081d9201098450b0b80c450030b40040c6560344d41d200240340c85c06400c4500a0343c01207501001c0302e58003c5002462a00c042302c61400c0030400d014039034101c1c00038030450008000028100c410408103562520403031030b0300c6210440104446000d20b4000c900a80c11005020400d418010505401e407030082d941070122406418500145100d40258a0000307083c0030128002408000c5505103840d142c1c0801e0007003d0755404040c1d0400007401d00c0a4080f0284000800c441507882554411120089031040034040c916600c40501c0d03800c0b080c602052040000d0310004507030040b000da4603090b0014000344500e00e010001e100c0241000c072500b1000c02e00d410b07400d0b4044a030305002041540c00c0400402005042480300f0105602945004ca04154841c004500011030600c001d9010b4400f540c006d07600c0d12014024542000d00c5603815000300b00d0100d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 501054280 1250 501053030 501053051
    0x9240b0a0f0503100c02010e060702010e01050a0b0d020411041a0c0d0801061d130c120f180b06041116121d12010608160509090f12030c0c010c051c 65
    0x41804d1514140d10400068204032084069026003881007106005d40a6a020080100d8041d048a018106450000c01c0f00e45e81d0071103c4402c503981140c00581180007078809a005007015400325001114030400c01d418030b0782d01c1c0d881030030b4420015a600300d10580445c14501c4110200210190a074031030a10032201d6042103c020030000340c0f20b446100b007481d0400c047e22540c0310042610758810303080006002c0000c0410016001e4081c4da02c4046049203041c2d07240d1408409441805101100c109030f00111400c261940c1d40101310107052580e2007036a48104070240d40ca040300414107080180420440c10407282840381140034407100b03032424803004411800c850001117409540350038040b20f0f503030b17182200c0740301060050405821040c168403030548a42c0000c0c900c244d85a0880f002200d82c00030b070f5a95040119100c50003448488119406520061040c001400c09140e11003142610701c1d0520a6600500c2d0a540c0d1400c07600000c540c0000308040c900b00c810402101a2004400920007410032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 501055530 1250 501054280 501054283
    0x110c0604020613051305010617092109061603020d0c0206030a0c020f0604060204090b040608210c0303330901050108070c0c1419030503040909240b0a0f0503 69
    0x80000b88581e400140303140b401629050070307402521004c1c00c0100f0041c81081c0d00801000280201004030350f116110b40b1000c0d16103030b44940718101003000390000c00110080400c07501d500042103a001801800400940e403900c030082e00d1842120180d005810426080180c2480040348501d000c00c00e085848134090b842c1c02040725000340480e40005136111410000f282401c0428881101c0c41c0139900c10b002c00e002c219009007050310708012042000c0569003003008125903080c49210350b04c0c0c01000c00180c02c030764130901e80000420090380c0c1c13a00c3c02c459684800e0541d84100c409500b5084041042e406a407a400a00403001d2061880002071213080c1c00011a92081449698108000d24001401c81c901c41c0640c076100c1940b01b8045407255444410f007a841410180c5000d0203100c49110b2100001a40e1100340c00b101d030007001540c03500c0c0c2802d20308400341c00c0c07841c82a26030f00680c4203005890351200d4409500168034030360000d50080c0c0b44003000b0182e071440e80150800c1c02401300600040d0780 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 501056780 1250 501055530 501055543
    0x61b0206010b18040207120809070b161403090d03230301051804060b030a0b041101050a080a02070804030b040318080d1b230d0f0305160e040f020f0409110c 69
    0x2c0120f55a2100f03140030001d4042c5c0b14511005107040d40320380c8000120750704017206d42d0183c40075005843c01503458502da003415000d0b44064411208008800e240840e0744000c0403801c01184000340c0e032900084002041c2103d81e9550105c0c000713100d4422610300800380310103440c0e4601641200d02c0c99540f40c507000a260700000c0580e1180c1818860108040201aa20075241d410000e0155078540c021402d01283c003020484050380c2514044100005640c864812181c0360841c54903045403d440c2c00c1c940200039003000d4822620100c0070003001c00455055101c45d441284071b55140524441c80391040850f18040e03501c4a09075034800f254071030540e504039804070241c0c1d03c41446400350066a04240c0c1c2d180040700031517803d0a48010545041200102d0310417000724058880107148030f01d1b00340072022510201c9010421480d80386002460600c280c00e031103c90500103001244160380c04861404a138001d0300800141c0d100003c0800c00742c0c5a074020125180c014044090406005100007901d850 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 501058030 1250 501056780 501056797
    0x20a061e08131b090e011401080c090414030702090c04080115150c031407030807180f060804051e0304170115060c1524080d020d030c030f09061b0206010b 68
    0x65020f9803005085920324090000c211011091290410041800c0d0007080710011000110503908004a880340380061040c603501d8014040c0c8031590345903190b13961100741d00d140705d624600007041900c0150b501c40f00700500a0030700007602580d175480c01031900e003120030311001c1e04010004004e042241560001030742034246182e05010064184501c0d08a03962091126200d90020b408905542450f070b02101582c801c8140b6218440341d44103100d6192090749a900c6600c881808200b030500c0380c0d61003000703401e8205104030221101202035440c911500c400d501c03680e059a43c40850108a220303031540d5003401e09107480c0002c000d1462a0700503498401c42c035026010a00c40c0300c84894080160001c025050040070740010007000300c202c100d0107900841140c01c1d4841800d074802c0820900008600d1400313207035240d0002c250304180c084d0181c020340604001481495640d1009240207074590080040346885003000103a03200703d410b00b817080700764480d03000030856002e000144100520001190305c0c90 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 501059280 1250 501058030 501058043
    0x4050f180c0306010309020d0602070209070c330509060403120c09120c120b0f0f090c090c090d0804080618060a2004140f03030a0e0d020d020a061e0813 67
    0x307907155801a4007611b00c0c460300a40105221802206001c0030380e0141020318400c40321032842d9102e884046640800c0410050041d0b03841d036100d0041100004589007007002040c1040c10411102103043c0110f41c001c035100b41c40c0390000b034104010103038850302c0d5100990f00d1090030001d1280080c402850314210f40a241146002646030005105810050f48000c18402142c80c00740c40300c620f40040c2c076480c01c5c0c52942080348070f903004c610000c80324081c461203a040729004107409041c130010040c140c680541001400b00c420010480c564641e195048141c1c1e00403100c2c10f54070351401814500e0601e00404180ca071120715101d07a5194000071800581140c20301c0c0010908a500c900c0884c01d004107a6000134400400050024604c2840e0302016090002118a003811745202e60500d506da1140b0007440c00040c41000c100490b07464140034142d003007800a0030b4044aca00b660390100d4a1809150010404640c114800c88450000340b8440511802c06203803281003414201848501e074015850020f0a2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 501060530 1250 501059280 501059287
    0x60a050d0b1302031608070c0201050f070317070c23061f09020301150201241806080d210c051c0e070b0d060503010603170f0c01090804050f180c 64
    0xb95a801036148030000c90354400c650f00c0c00e140e0121108211901245000300300d14800040613517006040000c242a01a1205440d09140b903901148542c880c100441c2070211040b04c841c00340120901481c400d030301940f5010102481402c002070110144620301c11880c20031307402c01010013808628107030000108005174022140c41ca0400301c00c032160750001c0144e244040000a61049210000b00780c002e0075030000c00400345001600031040340641100e0203d03c951040c00c000c5205a02070649211b2010900010040e4441d07801e1400c100d031802c08040019065003010b800180e40906400103d15101d40402155521420242c0140075054078800001120301c660f42d000742c0d0030340010b0710740d289550230f60b1280c0751940300402c502d8001c2a9402071442c40d144010030707103003014030074030003540d404c890031a1800900300d809000d01e034004070000700142e4042c428840b5003202402540b80b40ca100c0c01001d9110750401007440a1880403c44651084403540380e801122514843c405030004003e0f056580d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 501061780 1250 501060530 501060551
    0x1d0f0c0c15091015030b042a17030a090e09030c061f050612010605160b072304180c09030c0f090506090c0909040203072705060102030c070b03150918010605060a050d 73
    0xc103810944a160b003100b04c0404d1078500b085000c0182303000d0b42c4680c20803000d800c1c2001c04540e500c2c0951a1044085209020140581d00300c0d00c007c01d03445440f007400c80e0328101140211508062003560100100d81600b80c5449910040700c04503800f51100b56011428814410382160b030308181849030b942400300c00100030062444000895501b103811803083c1490b401c02d450010f200e02030250b0b40e05a040004607868802001d0f40040b18210350208840310710159240814030001e102100c031042c24400c0310000000090015041c1c03c0060100209010140746001e04910550384001c0c2000e100704c0a80b400c01010095000595116010544118181e035079144003191400c03105402680520360100420f000031100040c01c1c241c81c1e8201c542c180b2a030785801e401a80d0302d018091103c4032075046440c2c1800f032489482c01959200408407040f0306894142c0700402e09005c0223039400b00c4421280c40100a0303a002c24050741004080696240f842c141e10501c00400c58050448451300715a00c85035000c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 501063030 1250 501061780 501061793
    0xb0138031e090a05060919032f0703060b04050705030423010f0213081501051002011e0605280504110702040c05131d0f0c0c15091015030b04 62
    0x42040c85070040349840b41800b405a981d105500c00e800c56141c800c640004444400120302c0502405848021051162890b44c054850103907180803841071003028030084280c18104101c8840224404d4080e210107410350030800291082c6551007400742d030514003400703055580882140d61182d0031050780711140a00c600c4061000240a0092603158280742c3c503240446115401400601410b605a40c055681c1d00310458a441e4121103211014240100412031814040401070035500c00b40300000e13a49950000060007802a0071300f118071950b0f550700c18005414201c2d11018102e000c004912a80c19008440d004945914042c080c0202e8944202d81d00c0300004c1c3c2e042d212200e40c000d0050000000007800104036400500f0070020903080c80800160840c030007500324081c001c400e465079030640d9958072035000480b40603003650400340041000407130300202407050040f00d582d400d440f44aa8140403218515040e403000465918070301c4c064030108a07400d81d4005400700c9521a0010046030b55508000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 501064280 1250 501063030 501063061
    0x604020d02071203240305060a0e0f0115060f030b2107120807120c0f0201030203100b030403120c03020901021506040603020607080d140708130c0b070b013803 70
    0x20b00c243c40d401c403200b60a41d0160440054503102030901e80090310b2215500080058070302c405440c98010001065019400350030035288074550300700311107065400b4090b103800c50b450f1407888640366881d581c0074441a40d015214884001c4140b500380001501400043c1c0524002c030000950010803d0030031000c000240080c0006048000c00c90509200074108240b03603a01c21002120703515510415640405e003d500d45a489980081d10030074040c1040d801074000750b0018186481800000c03000040d4003010400640c45035200e5035404071003255400840096920980c032038414180140940300f11668005599440403586036030813041c0703459680c08240107011580010307400100000d00041070105a0b0300414549846000030000110080404001d00b80c0580b43c1c14002030300328000c1034a02c44000240d100c030502520304500c0e035603600d201d401d016a0158000f01c1e0380700d513180300421583e041040350b64032031000c00a404034441040000c2c0b044d501d03207031800700e00028004000b0800c075000d550b640 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 501065530 1250 501064280 501064283
    0x61606020d1103060919241701150e0a090804090c08060405090d0c0c152c180403030f02031014060f040b0a0504051c050118110f03030702030a060b150a080604020d0207 74
    0x1240200c5034034581e039070702c003064021840c00b420001c00c8c074070709448144508280c03000303d81071041085092014603034083c4005840400d890b501c40400402151204000748020602504001400900394038041c000700801000144203503d40001c02c150031002054182d00011a49060284140c061501c542118a150454811000c4107581c5144580e00500710b0054080000001c5207441c035008034a42503040781d5075416402000b2070580c0603100c07024125268105100781408154440300c4020281260401c69030600f01c4404c1c15802c01c40b504074041440103908080da20340d03240a5411900043e5803045101c0c1e0f82c1e40a030700241074840e0300c0c403030300030380e0003074080201240807590039040303d9000e50b58440001da0361546000403101c80341c602d000c03000046640c8440c030100b51313110100070000f501581034141c0d0303010701040110000503502403010000c0c00d88129800240d803442041800b0300c0e520079141250305501c040004400140e04845085d5000b04125009070392180c7e00e22401c40680680d900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 501066780 1250 501065530 501065561
    0x902090103150e1803180402070f050a0b180105010b03040b2707091b0207090b01030609060e15030604030c0605070509120106080f01110306090402061606020d1103060919 75
    0x128801510382d003c54080c000078048150814a5040d03d140c4a108070340c00c4204012012020f80001d003001d801a1031f030640244000340c800d862a844980c00c21b4410f8000305e41101c064420048001407101087c240c00061070020410366040100b10001d501c0050405004e0710015800a42a40c40322518030426502a488031a07d884200c0100c60340c903460760088059141c10000110800c4010841c040701c1015558001c0031001d251642c035000030003010021504040d200d1030003064051050068034000c080c5644400e140341390032460086d41408032410240300307030003610501012030750120b24460240c1d08284005440c1d242c61005840c00e11070300301c4407030308901600ca083c0c0c02c045041d4070110032911380130140d134008143c82c01e60b182202e00740a440d8031070440a0000c51000c1c18491115a40244050b008524254034510702040f042c220400490b8599000100e405000105010b070080e00e4070315520150450519200250468000820711080c180c1c110141d49030105c3c00e070f004030365580b11000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 501068030 1250 501066780 501066821
    0x306022b0b1f02030306012102070302030903010c05040b0f0a05041d0403020609120717130816090501140618060d0606021c140a0c080a080f0a0c02070902090103 71
    0x4103084050116946101c1c0316648104100d451249141c403603100c50740656003e14035556441005440e003c03001c000c0d25006c0141c22204010391501440100f1401d80207800550300e81108100f01802d4030181c030703812010004107200800888000005070307a80760100082075500d80030186400c60300d40c091603100c81d0100564105040c1c008026104144c0a24040e900b80e420580e5414562551103900442c0c8003180802003103c0e0b0003182010300503184c2a04014aa9490401c12242500103400203802508a613041040c04001042186158a004144003c0b0030701c030a601d4004069030a202e06000b05000d8000003030a000406450502c4010b1194010103a0780c0301c660181500000b01110700071500584110380c8400b081d4144400c2e981350740d40107130340ca00e000400c10000040d030720341000c6120014481c02c0500880002c2c0020b000d003a1045d61591041c0c102d2a0070034031070007030041c040c20310462a80380014000c004c540c0414503c0a030b689a2034007596840e003050048000f840c0010003801a035070441d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 501069280 1250 501068030 501068107
    0x15030b03060c0705010c1110150b1b0d020a08090d2603060a0e04050307110612070e1f0c0b0705090301060305251203120204081006210804030602 64
    0x9502400400d8090b4008106010320305200b621030301d030712014656240d80051b64821054240742c021072002700103106090400d0b40c0e9400c5050f4603401c80380f008000c0200050a5069071001080152480180d600c02001d00e0340594440480511401e41014002e01410302c07800c0030b10405c0214110300c14042d2810b4207c1907180b0544400701e03002500c1842c407a036400749001444100810f0042d009980020103140351107426034480807104480f1502c1034108205001c8800c44103103074401c43d80300b40901d8447e4148010508104028107554403142c3d849012203280d04084554405540044d0320f60041c0c4240054898400554290080d4001185e1541c05c1c84070210070484041480001090a500c1d140211401200c4080d10308006000d4540d14071800400500032911030303008850035000c0d0380b90040c58183c503400040e0501340c88000c5074159544a032401c2007000c036507650703a00c54202c1c071100546c01c01c1d450b640c416405120b94440a0700c00c0da00400c004d912110403e01081c1d5803c4a450000c50500e0709 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 501070530 1250 501069280 501069301
    0x7050d0e030313120203070305030c13030f060614180a0f0f060314160b0a03021c05090c01090603020c030417100204060207090e010209090103140a1b05090c090a15030b0306 76
    0xf0010100c60a0b0129608400002e0000040d1145640d040c2c0b54141140c0d500d00d08040140c010b0903000940441e0a2400030225901c030300540e0505000c0d0700085202e600703080407000020285c445007401101070340520081700e4203610156402c1465000e0100f0700241280f406c00142400e13002407140b0f40e01e081c1c4004104616082059002c81001099804042031009003c00d1001c031031041a051000c100002c0d16560702c00d0780203084030840401802200412608000c00700e4038102d0b41c12040394426052050b013507030800c2c001d000404045c6020351511a1f005d0b9000c9d04c1340241d00c648100103003160a0208404000d00008a89803080a02107480e91ba0750640295140d00a22400000b13900d080803081d00804107000b2074600f01c00203040e10b1070742e91950380ca5050000030740400c005c1e42d005400c03001c1c00081150b83c10b00c82c1c10740101d400f2003d15050208200b2007a40c064802100c141042108440c00c0d00c4842003542224403103000c2001d000c0740c0c100300360041c05145c4a400e82c58024542000781d003000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 501071780 1250 501070530 501070561
    0x5030709050613141f05070f061b020c030624030703080f120702030a0206061005070b0106030501051201200c030c1504061b090306020c0c0a180c0f0807050d0e0303 72
    0x4004462010039004814014044851075140d070b00c4805e500d2100c00c00c68040d000815081c0c2c4244040c0d504150710352508021500500340c02558020f045402284044d41000ba0a03442d203001c50240a650800c1000c5110304e50040c1141100003001c90340310b945551b01413000d080110b420800490780c565140310510425030144290f00d0040c000880482d40040c07000060700c0000b4020b40080c80035071941070401c02d0b441d130b4040d112802c0040400020000802c0079000600030503041e240071402c0e5041400708110080b1a08041203983c0c58a0004401c6100107100d403030103250b505098645e50903405071498198850442c9008251103075070490070441081c2d07001d40b0700c500e0141e08100310300c0c07401404401e407041c08000d4020000b410301c081031000c10403a90080c040e1200c0e00c030846103058288000300310440d110364094200250280121b8005018a0003070002d00340c6240790400306107400800140003400050000820084041914810700c56140d000709510108070007125280d10b400c6040d40550403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 501073030 1250 501071780 501071789
    0x50c2104060e0703050607030b0d061d0d260402031203010f05030601060c051f15271803080601031d2a030a0f1515090605030705060a05030709050613 66
    0x919044048080301004036007801135075030010242045440b500800c40280c01070301510b642c816800c9000c070002402c140b2449200e900c504c540c02d00c1019040550b07074104201c4407044024010803003204400b801301d42001c4222000c82a03400c142c2c03902e440c00030034a0104100020f0290b0480000041a81d00304034499030100d42003102210060703a00c403a000c0743c0ea41e015510080c110350048074600c44d240f04c0c00d408161081e1440c01d000030600315200e2035184007501a40b02c01313401ca180b01c01032004101c01c00c0d9140340c00170382c2c508288840700002c0b04107525040c0303118015080214490114490360b11940148509101146040c611040b005140c65100c0c0d0034003000d08412140444108170014082c000300b2480f92004015000042c0c0765101ca5500d81c081510403159400c2581103001a020584a44040c000d81c02c001c03124100c2c02c01404000315403458200500c03c1d40301c541b080125945180440b03648100c20303e04a6202c3c1c80c0c0d401c0c103540346040c0307801c1254040c0d008500800c03c40c040e050000e0448 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 501074280 1250 501073030 501073043
    0x10b030a0501091401061b05072603070309120804050301023103121428110604050a140a0f06020a030f18082b1a0402031306050c2104 59
    0x42c2d03a03401d000d008445103981280d15007540540100007040c020511210100001180052000e40f00c2da142814401103070000203a204090300911854040c0c000d0182c00c05040c90000d51400c0d40680303010305022542c9c4140c400705034480302d00d242040180415140100800b034000d648030341c50a0300c51800744085102e40c1d18030340c11140400301e0300008803014004403078115200d5400907048503000c452080b00f10361034040c403540400c5400022900c11840710702040c14603810078941c04000c040101060307021000f96005a12000a11001c5100030444083d81644000c0b0b00103105000c3e00030324205010200c000d001c4047d491903040c14001141c0051a038080941d804200c0c2c840c8000c20b07030703040701c10b0045d401b00301c100c04401c080c000032020f50041488804400c1e500808004c09a20041d03490b0038015402d01d01038881c035104040c83d1044907e001603132421101541103142428009185205900000e4149512240810007003c100c1c4219020340c8129090000d00d051802c3d000c402100056804403840c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 501075530 1250 501074280 501074291
    0x1a010305130209010e0619030507060219050d051305092802040f1a040e010803070b0a0c02210d020f04030203100b060a05030406180317100f09110f03010b030a 70
    0x6500c0d1010103001d5003a401440c0b43c003540d0030840d0601d00b09200415641e00103442d8182401e0070100c640903040118414001000745a0410800a0509203442d014106844486030810009000441c880100003107a02e0050344508100102501d400010340c0b089400a942009125990029601618008207003400f025200c490640390203080784540d1041ca8880e140401050141d416141490391003030401544540c01e2545170200d000b0450401c1e031000724250300c00511138081290140c441540408580c030100884a84001d0203500e07045030013603128031603c0c001d03007409202c0342150aa900000d100c05007191900c0c5c1c5904061041d07030142c00141e00c20f204a24011030388030028010482c007410058a80390402580540903901a04041c1c402c81c3c1ca1602e030150024180100d49070084c0c901c1c0a5510b15400302c040b4210041640341c0a0951030507992402000d104001c0c1000f0301008507088030400080e440010b0b02100c00c14000c11b464112655000000024128103c2e000365000c0c1c108076008020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 501076780 1250 501075530 501075541
    0x106020d020601080d0512060d05012906041d0925090b04060620010b032406030d050a0c032a0203070e012718030908240c09131a010305 60
    0x2c5d0355100d00e01c3c102c002041004000744061504034031940140014010403c0c1c021995103044c2502c90b90140044011106028040c1980912040040c1c040301543d074240381c42e00b03264a003115107000d1281c926145d8403420104403081c0707081010180c05a04140204400f003601a00c50305026058806c0110050900026035502e02e4140304010031500962610084259203804408000121f20742d48500d03556a0480000d554900703000700e00505080c000e03d480d000b401840c03503000746c00300030f8980e81c002c1c1d0092400c1c1e6481c076000000c5030b8040d0007034144045108070900c0c2c00c0b80c00c40802440300d43c0503900c01e80c40e2614520f05582d000c40c0144210141d5841d04c2e15000030300e05010003440b4403421b0b440710002800041c4616400c2c3c0b08403218107007001c10000c0c031f2007845020440400c00102d00241401204120803142404640b1882c40d25080c1c0055041c00000c101c1100300e4060940040b2040010340300503603544403040c200c10000721540912407030300c0e0a03e40107404004800040d0110b41040c00050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 501078030 1250 501076780 501076783
    0x1503090f0f051b090c0412140709050117030702100e12070b070b0106021612060b030307030c12020307081909050a0803040f06030204050d060507050f0f0409060909020112090804030b0106020d02060108 88
    0x500c585812030b4083c0c102803414a00e00171034001a401a0f5407101602301c22080c0d0b0100b40a060090b0403440408201540344c00e103450a00b012603006405150824400d810050741ca14803070141c100a1407811015a9008000061344018050f180c1041480f510100045868502002e4503105000b400800056a0b0f9200240e880d881c1405204280321241030090180c0c0c1c0e00300845603401c6e40180000a00c2d2003600c2c02003071542c0d124000a80c003040e100901501003200104480c1301c03080e0184091410b00c0c01c0c96450381440d0042d41d1003da84035240c08881d1142902c28516540181401041d505c5601d5880301030303645030b178058090454880c3c0c4000380030a045000703000300e80848030094001c0700b00f403001d52a00700051001802000030030104000b1001e000c100ca1003e00030b01e021603000340340d81e48c1c034090030303c000c9603031660005065500380f52503900945c1c0c0194408481e44aa564045120765031440c103100d540c4156040141054648000030620540c002040701704660b4a0302265401d0342c0b26040c0300d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 501079136 1106 501078030 501078049
    0x60212010b0d0609110a03020c0c03011113050a0b03010306152304050f04020108061302040e04060504200604060e150c0a0312061503090f0f051b 64
    0x90b0076070385240b00e02401420a050104584200a503044103140111212803050543c0840c10b16503015043c000300c00c071060000d00030000404400f00700c0b81e468200b041000034a41200d90b020940741099450007040d10040c00400b42142c3c615610b070001b0380406901c0c1002c0c11b22009000980074481c081d4072a541131050400147ca5034000c043c0021030b0802050010300401c20700034000940d0b000503159820581c00c1d0380070311041440d80b146e080a48540d5110080c2e50b071402040105022183d40620b014500c199500c0b601d0080c5102014500400c8480386c55000310104000c1003158055180340d0b9080c8405031400400015480700800c4942000201350160b420031001c0208041d40001c01c80c43c0c00d48011000c100700750400d001d03030101c0e00031340e0640c5003896a00c2ca4031006111036040e100314450390040c40f40e00341d03100c03a10340030b5110740181c4c02460b014003a403541c4035018501078400 = true := by decide +kernel

theorem cover : BRFrame.Cov 500899280 501079136 := by
  have h0 := BRFrame.cov_init 500899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 500899280 ≤ n) (h2 : n < 501079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
