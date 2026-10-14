-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1426
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:55:32.987371+00:00
-- url     : https://prove2.me/submissions/80747769-82eb-483c-bc61-7f1e9609c0da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 256294964 ≤ n < 256474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 256296214 1250 256294964 256294979
    0x24020718201e0c030405120f0d1d0409060219090317070b01030807020402070f0507060801150f1d121c0311190c1e1b1a030a0f051303090806070807030c0e030601 71
    0x3104038023002d50b54021388901100c01445a203031990092042d135002401198040204001031210b40000c0795840d508000d20566202c00280e520803016081e22102c18452443c148006458802c403400107a0640130401003001500484880341542d82000915071070740600d20200740244078200c005031044d0070f030115801c10058002440403c3d203250b590782e03001a90381ca14000f8054800d40c014400803032844c4406484c01c5100741c811844081e02401c1c1e05881004c55000b080c1c2194109480482c1c58110061042d80c00e0401c00350050802c01510301004903106800e1200513501405000c0d40c003104088082e41601c5100f0032100f00d0154008948001039062840c8040208031880c0040301c400d02c1c90144410030402c2200700004441c0f040b00000c003c0c01000c00d81c0c401c194001070110070210368402c0050044241031140301c1c4140c4c0040e000d05408101410090005685503210b00d12a40c00041081440c55011000e035400007454100410310300c1d6004c50070345507003001980198044c41183c00000c1c005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 256297464 1250 256296214 256296223
    0x90b01150e090402090403020a021f080f01050d020909150115120e030415050c100b01110115050405071211030a0b030724020718201e0c03040512 64
    0x8031400806400c0280010806032001d1600030000e96220704680300140160901e182602da00a100307105540d0003c02d168000b507101c196000811600c1c001c0b4151804490740c2001020b9000310080c0110007040d03140a00045400c409503c0090250300140c0c040740401008100000d91464504004e01145d80c490a55044040e240014000025a004c4000b801c48001d0300ca01e10150b5011000355180c94200002101010b0007540540c08000e0f0411680c400144c045c0100395105525140c042410190000010051270b2007501d0088036900d00700040400c01c4040140c1012210251404903440c0c0d03607540c0544d1070510b90000e10030401d06009411181805480040d80b090040b03a0003001440d1103e424503039540101d0103480d2480885491f00c6004035003120b4042100c003030301e1040700c045586444480c07160611342c540f20a10b407521000b18410814401c401058040714201c200c6040c0180fa080e09040e0403440100c241c0e404100040c3c1c951060b1040c0304030b0f000380c840505031840703000200440e02e956 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 256298714 1250 256297464 256297469
    0x72d080a0e090615030601140d0f0b0a0b07060c0302220305010518060103080f130f080606010507050c0112061d0105130e1c05070c060216060f0903031101060306090b01 74
    0x14030414001c015440c0c9110098010b0320040c2560300c2a80300c1c500b801503140d1003e4441c9046c0700101c005508a00c200c3c1d0f00418099081c00e002007682e4a00120700c8080e5280b03658150702c1209000000c0c04845e0041050707892042e0003080c04901d40c48a51000d50092049106039030710505051804230240c3c44803d04441101d2040d0001c02290381c4407810390380d108810000040658000c0c000402c003144292010300340c8003c600d502c0a1402c9076014001403034850310740c0604243c9450031410410740d0070502907035500520078202145001101e0b591f05071100e05110440b810f1000380c0d07000c0604810145d002c800a0b20302d239180707550040011850740e034101500b485820f2041202c3c2c0381c404454502d60280480c0707411080000d00001032096030491080c1d85298105d02042004d001c00e6010078a00c0d11410024800c1d80c0207405103002d1038540782d8002c1d070240c0000c801c0c05000c54911a10f10b6000f04500c040700d4140c903120b1000c1100030403940c0900324550018100c54280356500d801e021501540604 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 256299964 1250 256298714 256298717
    0xd02060313140c0102030f0919171009080406030c0c060c05090909070302150d0213060309050f01062d0807081c03090b070806221a0a050303072d080a 66
    0x32182110b070682d42d0301c842055000340141c00a001104003800104090840d288006101043d4038a100e0300052103040b113030740b00700302440c0c800c5e45001c2c1c40b810038003041e01b900b98030f40070a11042d2183d03140d054161040c0d01c28201056900d2644030306091050b4880031084c0c1d804035040c41040c45403c0000c107682c1102c0e001d140310300141008140b40e1180000c814086960103802280b40459029040000790014070139040032a401f041181d000301040c4c90882c0140400b030720002800712076030074510701d886002c80e040d40c450781c5002414080c0415004e0392800b2100011103041482041040e0005400704a03480f000c868440e0b103c002c141c1000105611207590301c03071020903140c0b2450310f07000c40648a00180c0036011202420200d403580e84150b500503400702d00a4841c00100d081041c50181500310510054001560f440c0281240c02d5440c034503405c098011a5840703122421b00d40025102d20595000800c1c03000c1d00d00403081018566000c6140d4110203852021418103e8109041d41d40e201c944d1110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 256301214 1250 256299964 256299983
    0xe030412062f0f162003240f060d061404060b0402130e060f030a0506250822050a12140901050f09120a03020a020112020a0e040f020903070605040801050a0504051b0d02060313 77
    0x10152147c1c40f0701c2000f070a0407400d20403564854120382070400b8809889250044200d00011000c6655401880c0001e114103d12600703c0c54a41021000c030750030344103070314822030040018410441c07500111905980d0380c100c80004a40b10000001c13204140ca006d10b035054080c40d580c4005010022500e540700b40c40c0c00440d00350712001d80e0312046002c1e0f400142240460034010100d841840d1906000261040b074180900e004469034441d54500840507404644001140d01950764096000301604070118003a2007550908071041c001800034010f0020f0061034034001300c5c03c0304140e0b4030305400c05000b412820565540721050305009403505002c003401d03800f051075410082c8042c1002d01c2240c000200701c0e968101c0054614007000050006414a490410303002d0002d000c40766014002e03031008080325100d0a40d52071130701c0c442d0740c04d4840081c40982084d281200300008200049012110103661041000c4180e103004d00141040d5502e203000b030341154000c02088449240030399042d500c135021fa096a03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 256302464 1250 256301214 256301233
    0xf1d010512030d05060a05060316030b1e0d170307020a050613020a031b0906090e0114010f1205030d11070308130c0501030e030412062f0f162003 64
    0x140d821100c08040103610401242c0e507444080c4c2d00240c0c0203040107201040b425070361800220f050b08243c035420400d101e4a401c8108554051154200488090741d100c882280100c403510150030040c40700901a03030a0064901c200201d20000600c000f00c00f0300441d84034180b840c0005c0d83c42c2100310b011100c500c40d0601041d0100000f4906400303955009248144090961fa125290080d00b09005040002c841c00041040c50050013007070050440c0190001e501c5004500840c01c0d6404c0c540600c0f204446d680040c4900d14a541600060b508109148005071041d4603201d8518801c481317102c1c903c6880c082d00f00d140721002d00700512180d4040d956a00380ca8848007114008410503c4005180043c2804204050350003608000130b0006008e00f50790030196a9110600d29410001040711025902d40f650343c640a4020707807410034032003001b11860f0b05040010317401010b031007041f0a00c6c0070054082402140051101b50707403801907038001030304456001480652139105407513442561081c0960078a4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 256303714 1250 256302464 256302469
    0x20c03090411031f03150e010905060103121815030b012a0311060601120e2a040501080610091d19060506040e102c060a0513110108090102040f1d0105 66
    0x404050302e400003441c40340c1e103080c91880741c0181481c544001c010b5403101035200104002f07001080c02180151292070200d84c2100c801010046002681008a0015a001e200035601c0400305032040019050000300c1c2c0d4113140043e0b503807039603000c24a0b032514490204e42030307031181ca2415440c0052080c2c035a59520404850070b16110300d4200c031030a00168020500c0034114100e070300300640d004000819601c1c2c424a694003c005200303690301d888851040e0580344040b0381801d01c541401025030402801391801d03d004c0510340c6034103512403070000d20303115003402140c245080c1d1a14144100780e42124555903041b00a0032402e801c000055a0311858600080c01074141409039a04607401080a8640100e0403120900208008061034181140c05240c240800042110f02080d48030708200030411460301c5110324040c3e0b800208410000804400e90100050100c036070f401f480c403001d0074507446a1303803051007860080c0516800480b091111081c001485001c0490b180e56203400c1039202c2d101c80c0e88070307800d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 256304964 1250 256303714 256303771
    0x115091d040611040b040303031b0206010807030305090117070e040c030605130e10050f10080109020a15030f05010b070203070902160209070309050a06020301061d13020c0309041103 80
    0x84484004540d200103000501558054080c0059844000d03052945500030b410940d08107400860209503100030181c401174400c00010351150191004140640c10441925200d13601440f004050082c040b03440b070319907070144680c0d1610019180410314213150810001303081c50900301030a0700407483c00382048405031190044405441c1c01400d88d82007001c6440d4003c0081129a1050740e50303024144110350311000300c0c00b6503400b0385402d031751a140c5c1d4204120301c104010565800b03886542e25103007241c00180c681502c04411130b81e030b1742611150200341c0441a40585900030031031048518090011030482100c1e000fa00e011802030342241c61150f00c800d590f00407842213004a41c9904010400700300149030200d05250b00c4071051601103003000c80e55951038a000c114000c00c031001900400180b0110364041e8440807a642c20501c902051350252001c5040040c604103c3c503041e40c1c0014244a000c80200125802508050020001945c68105940041d042a20508400703621076443d04540304030a80c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 256306214 1250 256304964 256304999
    0xa0c02011106070219030c12080f090f1e03160c091d1e160b030a051e04030813150204032312090d0219050321041e0e011509 55
    0x80051031202d000c885d900c250b813846a80d0407020808a0201440083d520305a50f2103291200d855920460818400d2528000c10041503000c0c1d5600c40280031990712800200038141c0c1d085541080502640001043e00307520035550b14101c150011800f0710b04114054030943c0441b807003c40304006444000030040c00045224036500d1040d4407580610010079805070311481c6c500358240c22140fa00c4107105030510500300355808206158408001c0211851136406107541c4403141e0301c4001c03558540b1107049081044c0c003a2000e020004440005138640b1000c043c41009290403451030301c15422080d0b0325030b001e540076010865098140144c1c80c441e000b0403140c1040b954000f000500105c2030707007a0086055800000c0aa64805070000050340982c80701c110746c103d61a220b0080182c202d042170300303052400c56001800040032a140c4070516038442103405860031b80d04c0c1c805200c0100d50090106039030206050308889408079400c0e000090340e000c41d4548551915490300c4251126903a0080103403a07e40341c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 256307464 1250 256306214 256306217
    0x20703110a150f092d050706050304020112060b12040501020c030403060209040c0c02130c1e17070e0d0209090c0303030c1e070f3203071104061212140a0c0201110607 73
    0x81040703080754801105801c034200c0011940c02e00f010411b460b2145400701541c403a00c0454400800e2100f556884426100749920810f820b07c4014507243d21010f4510414020301040101440810200203007074044070314000d900c0040700c1c0c403641c4038244000258002c1113100c2c421403405298881c204d010301d070081304c500d4008010b5000c07480000c25071400342c610201c00e803042041140d15261059001d03800c3c01c25010b82665482e04000140003a00b02c1c00354040d000009000c115401d20180750b90750078120f540258184c1d400403c030348804602618100380c40f660b02e43d0501010080000b54480c2c1005000d0480440818424140d158681010148102c80018000c0200b48404c003011404070b0603a01c94410640d031070b8101346e400003614201d40000c051852401030300300103201d0003804030703809580090308421078082241c64070700281c1a1004800c0702004200035242d00044003d41c1c002d03684407804020203c8110381e03a416180d0002e0030310f00c080c90120b01181910408070b99454000416600c03405a9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 256308714 1250 256307464 256307483
    0x504050f04030f0804080702090c030a05090c030d27140a1a0d09051e1c1107090b0d060203011e06020105090607110c060f03060a0506120109020703110a150f09 70
    0x143c8100c408420080081e02d414030100201801600c0c0d4070959480340f56501fa43e15180d0600e150450b06640c000ba081c001160700c0103101d64041d541c0881c0c0d202c060840307400c110034800c17a06007a180b07010700000b001201c1d626000c0e800050703c140c0001c03003c01204080b00c12600e180c0d10750620b004041c400341d1440e420020140f1080c5080031066000c021158003906c1251203045e4080f550803181480301d00c441304e25821504075006c0c2003420301814a00304011b801c12009420386030004071391302c4c402c078030800300a152104e17141e0b0125180c1003030559030715402030010741d640e60312090b20000c15103c140c00d0120400321000b000502c98810301c109400340900c2c1c0003401d403684460f101203450400e03d185440070350081400c2c1c810a951042c0007400500312108120340c17289014810019580440c4e800540159020800c01c101911034101150540300c03280001038407100281822903d10790242d041c8002441010342e03c1060100e44000000701801c4400103100000216030905c2c2511002070000745103805 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 256309964 1250 256308714 256308737
    0x907030803060402040b0c0c0918060604150b040b04080c09010302060909040c09020706091a1003060507031d0a0b0a0204051e031606110c041a0f0307030c0605040504050f0403 77
    0x840c001107400502c020005810aa00c940d040e404d954000a2903400301e40c48000b8600c0705003445071440780d11440c407502c621502c0c0c01e800b486940714030b802042c29114a949074080492083c4a40c900409040080d91444e299a1503401c1c0d513039503a1280c0902c071701d90b12555142e00c065140c00712046060b25405071006052003104001e00030114000f8208542c031161080e0702042c0d6000510180c00120f01426020a030750000b03003445043d0144582c3e22180f050300341e404100010711402001c10480358040000142591070442c11802826107095501500c242c484200020748000110980c48078050940c4600b261a0320904508a100d41d21403e90000641d66140140007500210700186802c054243d425032112400d29a64202c034a401c00b07008601e010813082042c1d8010000e003c0c801c502a01c003084038000080c22061240e110310f000510444944181d000c403911f00f481900010b50f40459a1490141c03078440241864002d802070602491416000610104800703101c1c500542e010f44803082c0400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 256311214 1250 256309964 256309973
    0x10f050609040609020a0e18070807201515010201061505070303020702060c030a09060302030928050f0f16050f09070c120305161707050d0e0304180b010503090703 72
    0x410140407107920950316080081c60200da4002440c01071065641d40c0301c200004010003641409505450395010500307400c010311103030890390b00d0f0f40020304e5061010920880401900b14901940c1511072240510202140740201d0250401e005d460000c0b00049800c0810004a080300e45510a900444400d1070064a81c58041d07401400303854087d145c050726090f03035034000c5241d41d4840e9080110650001854107a5650b010f60650081e0113186030035449c50a12549071540c0d8400a681074200e4601c0d40500e10303506601c00000207031242d000f41541e01403264000c846495200101c6480c0150064032540708241e2009840201640e20007000e000070f0040210074060f000c80002e01c01000c0c018035114041c04178044110150a040b0b44c0d5902003623310f00100e00c848816000411041403103145c02e00002900c0b00038003440d40c465401c1c5080360700c40b046000346074003a0645030314404c843c3c0000100400d00a00b2110b2520101c58104408d00c5005100001128107101c1280c14580a8100401c1400082c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 256312464 1250 256311214 256311217
    0x903080103060218120309010e06030408220918020102060c0a020a1b0305030d090c0f031112030d230c0a05040911070210050d0509070b0708090414010b071a010f0506 73
    0x100c810280031303d440c48409021035080040e01003000700950000c5011405c42da0b02150350415030406403261415414244c2d280b50701f0f409034102c008006500c400c1c56210800005800d58010081d094040c40440400b0004050242e02241c041c1e0044c080c581c0090205c0b80d8480407100f61160350740c02885c03560b04540b6901c12540081e000c6074041d4440d0b03000080850307820809000705900a00001914842518101c020b4103856442600600e04100c0100007207541103e11451a1a06591b01100b1180d100106401d5100751a00c0c506854500b405000b000c9004510a07140c420b40c803d0320760059182c0205a440c240107055450000941c104801c0c0030040c2c0d01e82242c00c450714018001802c098596001820070001003507100002100466000300d002c5290250a400241d2140a04881424001c04201b2071043c0c02c005401c0d400700259000858440e980310030307692660045150003658551480384020340c00f03010262a600c6290030300d410910039640390141220820070640c045141303001c0901589 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 256313714 1250 256312464 256312477
    0xb0a081905071509080c0102060615130e090f0c0915010f090302040c1d0f100e1f08010302102f010e010e01020a02010f0501030213020f2b05070309030801030602 71
    0x110300a10320006100b01c21440390a0748811940c5803000402e0500b001d66180c441b40b6000d641c115031001e8144251030301d034075020301d0100014400c296503400801d000e41b584031071140e0007a410100100304210100c079003c1b4941c0100b40c00801543c40942c0eaa0003001800c0205039400a00003940005145c0c1c650300814075810022258103001840c2641da4001908545007154032401080d009000000c0285005980c10b0b541d1108440410300075501c00c000c0380f0800700c00709000e002c0c07113190902c0b0b1800c2d076503a00d00e0039540303101e00c0300c8170f501c20074aa00024a030345001c4c4803ca014107003106201407164003510780210382091004100d4040d081c800324241161143c201281c0b07a5541e1141c10b00401c80081c09440300d4196480c001507502c0302e03150802821140206850720000e4608001800166075140300080310080c840c1004d03031111105d10034400b0ba840351420204c0c0d0744041c90542c2d01c04030b00204005084d504035160803c10355a811b2000c2e019103d01020080000307504200520001e01d007603024016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 256314964 1250 256313714 256313723
    0x1091109070c0605150111163807030306060936054204050403020c1906080a0504030c031404050307121205130303030b03150f06040b0a0819 62
    0x988540c55100d8030211001a210000034905104261720f055800c90b98680d041c0fa400002000c80040248102c1800713010744c01003001d11441c0b2404013500c0b105030002a024101c1d0030000c601a00102c524481c5c4c13075807064000b03c011904050703000a1140c008d5402604440003030f20300140c0c01c0b10030208135070b0000c80c1c00d00e10681754801d0000c06001c1c0301c00d071042a2240011a480c080c1501e812780b00000400c521600154032058681031a40c0581d0310b2039030703800b00903109850110301602e6a20f026401c140341007030300c07030340001c501c007141ea040d80312480300c80f41182c005072180c444540700c509103002900d03c212406404940d001c40c501000a11682d2007500301070300c010b58141020348580c0013a0130011140e001c4400b01451a8114051042d000c0b180c143e15582070400604c0c0c151800c2c0c296201c02018440503041c5a0b44584411003510280701d014108a40d2000001052a0a49030b002d01e0030402d64601e030040e0b1419420380020b040c121034241c20340b202c01c40200700e2502c800510a000d02d542c01021039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 256316214 1250 256314964 256314977
    0x23f060411090c1b01230601030e011a1905030609060a0c030606090608040c03080f0a0e030a050607050a050c0d030e0c04060506041412010207060219030605060d05040602090306010f0602010e0109110907 89
    0x1e031042185071b4401c0d0055107902525549042a03400101034410080d08240903914081c014590040f04105a548444060302e0540d9280342d003803184032480b21294441500340c0901410800d2a00004c543c0714800c104c00981080381051101d011000c0754500c0c0501070100d14000001d1161a019099440e07009120360805c1c0c028623101c1c2e035070302d03016005258030000054000c6104281c09400840080035188284c000b4101d03c5210341362159903c0000c2c0100301840400075401030300c07a00c0b4004450f0144441d004030368001d02c08441c014000c051501c1e65060703a02443e80051024541800b07080203c400c0200894109401c103000441031104550740e003644040800f080c040c1802003800544280350040d800183c17035018011544ca00749007407070301c1241014035000c0240f003950380d08410380e4230507a1003841c002420340d140d1030503000a20564100a030302d8410600000b8081080407110803c1d110254020300c013007003801a03002d00303a0300028401019129080311080b01824921400769111001d0328103903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 256317464 1250 256316214 256316231
    0x80a0513020d0602030603010b0f0a0b03061c0309240f0e0d051b0103061d010e070504120b0a060803090102190203030910080105040506010c023f060411090c1b01 71
    0x290811460a812180240c0100404c00d05103020706c946e40030849c081d2900e541a00040d40080d107580c41030b0148249203480400818a00c1d15440c0312209100c00d10b4040190004041c103018048000901c500341c0d450307801030446c842801450300c0192800312951200426071001b4407090399004408044030303400800500d46080070650400c062000100e00c0b101460303490140e18001026181550002c4c040d200e510198603070604080c10843e0704454201e002c0045613119181c08441a10035607008000c0c0390101031041c014400c00106840c02011084c00c200803046c7c1d034020440d180d0081c0015103000d0380104c482041c001250310440ca0039a840181624500700c00000021605010b40c11020009139056005120b00d050074400c03940c02800908140c1400f010640c002038200000b03800b4041e8403824100940a1508083d42e50201012111881c204111105051135070301e400c2201e080d1002d40300351911400d40d04181540d00e00442e10300d00c4c40342c0340c0314030000d01d1404040880c040728038965031081e41 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 256318714 1250 256317464 256317469
    0x402090408091008011503060302030a0b0a06051f02101811040617030403112418040c0203090f1002331509060306060604150c080a05040e010f06080a051302 69
    0xb9081c510716140c64403055541814150106c3c04034140403182454a0300380203201603600002e8400038960310070101c00d01d940e101d2a1040161110364031054028549480300d2041c14070944d0301c18400002907080364100750901d01036100b0f42c5e40280f0355480044d4003482510109951a0080b0120940540081170080d036551a4042181b40502e49200302c2d00041814408c2100d080780400f103444046600c048946001843c42382810079081c02d001d90f007000000c25566038440807100a8041000030820085500c0c550000b940740e5010362225440740c007108501845070b190611107510592101d600421a61464171a69510340d0701c12592241040075810290514000078000d15215401d03071031443c00c0d800e002400f4840c0880000d0552480790f0045c0040240325103a40d81030b182180c00c4a60240c40740804500c083c4e490018040002e02010000225418160381000040c070850b0340000758420144c0c0d80e408509182c0419000d04800980608085030800c1072a4002c1d40c0c005079280f41a18011509030300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 256319964 1250 256318714 256318729
    0x711060403050609161401050702040b0a0f0f09090507060806010c0c080307031103180103021c020f040e0c0a021f1404060e0d020a020f040504051f09020a1a03040209040809 76
    0x204035080da0208081122000c030503c20140784117611404000d80300e0a160030084a841000c07a400d040041c00300705001956160303000342041c0c07039000e0305070445c07942c4414103e104145a4042e50510910008002561500600c1a600c299070041c000c0d11210341009802ca03658034010381420b0400a80d02d0301d480216a050926900074940c0200550f92004140380c094001c10340d4000c4100260414801d00044400416004071580000d03c0d00503034480341a0075560742107400b540c10f4070b417141c40402c0c5c0603011144140280140c07030140148040c1030343c823000c1e13881d200d22038404110011381021018030705130000c080e2015401b14582e2000300e035407841032444185103031044800751466a00c2d0b01510746007210038001c80700c1d40100751020304034484a42d00491119182030300610301a40d40e940016080c00410300c05101174403080b03801d0300d802c00e117581c40c1440540085507007a84100841140000d604031410540050809113450060840c0d81c0d61b002c0022b8080e0060040d42c074500204040155640c1741d41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 256321214 1250 256319964 256319969
    0x50a05090d03030618060e180c09040302010204170a05160b0f09030a02150a1116120804050a18050a0504150b0a0302041d060112020d1202010e0106030f02100c02090c07110604 77
    0x2500011586c1c03921005411402d0090042059030148c02071074410304901240081702d0b00002c0e40c0304800e0b91502d1034100c1c0207105a6004003082c0104458003075006074085814000c0707034028012a141181400c1040c03036290003e1242c01c1c00e03078504121901c4500c1d00d21004d0039030740a005050f600901820b0700800d5254401c0345d9450740b0114009929140203400986000340e540d12840144120a102219a00090103070f01402800240584d42c1ca810010004101c801522002c4e00d181d0203540e517410740e81c2c0c0442c2030400d0740c4503041c20240024510900d070b1055600c9507400190204006855500100042440d2100c2d5500700c4d000400100160310756014100724900769281c6c0c82c03000ca540c00005030402c841078000c02d245d07a00480f401b00c0584c0e605d03158800515001b41c0320f00340c80420b003176050740104050010f446040d405e005000081c444d00b4051802c94900035140059003000070001101c00382c0c04840700035808010540890007205815001d40b4500c4d218605030700394001c641b40058101d0b0000e5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 256322464 1250 256321214 256321259
    0x2040b070b0a0603050607030e01060f060e0102120c070312020c09040b060307060302040b070803060a0e04030201051905071421040c1a070f020405040201140316090501050a05090d030306 82
    0xd0340c0020010090486544140303595030800c01903056503116a00d4000203017040080513101d03c03250640030000e40c42007004180a106090030580d071042c024203c006102d00c0b141c05409401d2103080c15481c99011203030381c4921034024100c03d0b419542c88900e011607120804003103119610840b287d5454007000070b402640540940c1d4524a048020503103085565040101003600500041220a0306501641d10103640b020364207840f681c0d108040b60200c4c10f6580f01c4401c0010400c1444103140d019840b403401441d0740c2c035005541d0841d05242205803901030300c921001902010710b0301c528220090142200e40b241900c94081440d417108010b40b1510b0568065504907480c4408120f14071408035020f07102c2441030120b90525855844002c00c80141031070207805203448100050031603100c0d04804102985284056403a814105418000c0d00560744a480c0403e51503140815036602a205032030305004580d95031860000480c1c1031001041c2090704c102c05040e140c07500813a50800030843c84803243c403003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 256323714 1250 256322464 256322467
    0x1511030c0a140312010506030a020717091305010506070b190e0714040903050d05060a0e15010e0121110f16030e150a08070c080a0e010809010e0304121502040b 70
    0x99042c0a09110b107541040100c0e503100b0840380d190426000106411104226616034076a40c46909031400f0f03115a00d8024180320103603002c6071241d407800c409440020340030340e1080100850500c04808031442805031a0f840203092001302c001412889155034020b010010759a11510011000340a07504d0301580030b0910742042c003050000040300bc1301c02d000c003141103500388503040c0507403000341851140c400c00c0500310342c41c0c0300007503010348414541000421880032071416514040c1d06001100314000f41d039a0005282201c00000d81d0310490120060f0018108100c1c0c05407280000407006001064095a4a04082c40b0b00c90090481d10098400000148241440b551480c58000c040040d00541144103044c241600160341c5a08030507143c1e1502a41441100c64403808000e540d480c1d03240a000b04007001c0026004c1203154401e04107032050802783c035001e0158841d40081820b8504e4008801a00c1d4018802001041c1001d01e0b086134460246002841c01622039007958166401504850b01c840720 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 256324964 1250 256323714 256323733
    0x40210020f0f071a031003020d060605060a2609190203010608030a030905060714040605030402030a0605100f08030f16030519021e010c0c020907030f150911131511030c 74
    0x58165030004e68600301c0341c51071030741c075010b007440c40c40b00030900003c1e014860380340c0980100140c41d881000503290040547d034030352444802c020103000445040030340340a103803603401142d1409550818042c00250002c0d04e00d003824860076942c0c2481c03805060360305640304d46000a0203c410b02c000c207485210f9690114004245d420214a03018000d083c8000300810111030340e403008070b50f0302035405640e8a444d00d140c1e251a2800080d00d000000700028141178035110601c80306403a41e041c2d400841d00011150015917640b07ca20070386a006103881e103260410208140700c40078001076290314450307110b814040c0c00c1010140c9840107000b114403001026a0089100e1140045a035000c0840b0f00408070003071008126607803000781110705001c030007030240100c00080b0391254069003100d8201a204034007080071003100c00008440f81e181348155006a03207003540c44507242d0402021200700c450303490300881e051071800440c201c4250300c1c102000b0401c054000511060301c424030080068055581c0144070104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 256326214 1250 256324964 256324979
    0x903060906040b0408071104020313020306010b0a05070b1b030a0c1706060703110f010903080f070e0d300e030f070609091a0909060106170708040210020f0f07 70
    0x40038088010315841002004005000144141e51255211041c1078840500e868007a040c20100b0340c04560080c004000c010b2882c10030b84030384080b10300840131612640d0b41d8a0700412240f0600041a000a108201d0720002c6100141c0c0c054201200408140300051f0901c440041900141d42120740c66071121010780203244e02c0360050084900e008013564440c24138600091541c4103901004050204403070261141c844188004d1044201180007031202200500c0c2c010130201040314911011100c0c7c00110700b0340780c4200003613200c2c0d1a01034241407420400e0346520511441001d02080d8260504414195184003031400c003140c6055501e07a4207100805074105800c100301038000c040168003018080040320b0f880b41c6804211026a580042c9408110910544641c3da00f4080c581007048581880034074080019968100c0703c199a9002c1c07585d140d8900554804410b640000c0080c4000c00460094075050118032103150880c0101d0b480d01c0d40d440099410014154490806600320b80800c01c54030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 256327464 1250 256326214 256326223
    0x21c15050f01141201060e0c0403140705013f0204052409010e01051314090109090b0103020427030e010e030304030515060a0f09020301030309060f0e01050c0703060207080903 77
    0x140007a8460019903052242e18500c1075001040709102c0c0c040421301d2100101c017940900c01400c080b00c0782116500d40a5107842c01a0700c54401219900e0700003c88800f0003002194140603194140d482002c01c18440c07044003040c140f2000c1242c802860303183c143d030450a03405550110940844400f41e00c441c82e041c2000002e00b6540648001d0140f452030039034407003844804a0b200940b003400e14065040304000102c400c1d000340e000c20040030491140c08a0121000c054198070305000303e8049146a803609540c00948a0001000745510745110060005141940101c1c440100b082c2000c040c45441d0507502c01081591042034000c640c400010a545581c0001c156290706c40a400540c50503156548240d0384020b2030b41d003050343da0030b103101050b0030340c2d100e00102004015404941c0115a125603103580258000c0c4011004210701080c0003401a0291060041c98035454880b055400011401516035038840041c13500b0700d0240341400300018090b4405001541e00803882035031900d2040d414141350 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 256328714 1250 256327464 256327471
    0x1b07030c240c0b0a0b1305040b090f0a060216120c1b0b040510050f0a02010e210d050604060504060303030209090c0306060f0711180703050703020901020316021c1505 73
    0x89215005040410980103000600c045900c100100f0003075540484003401001683e03a0282c1c0301007056000c03003d803d0143c20540c0124050841005651100559180d8034401c01406840c81d0308144016400304c0d41c5a0b003c0d16140007441c508410112041e50780d1004400d2540014001c00c4d60a140b070018800b000c0c4801810450081c2a40002c43c10058611440d0055201d014490702400709460780c0c4620450079a404288594000b0fa22400386a201a0103000d4007400c0c1d407a5440b91413040c0954443c00d031807031104204800a524905880f01840340041c0500510b0580c00644800002a403501d13180320345030080d4001d660050300c0c0c0342c8080400400c82409442c0200744039082c018010385954403022900034030040c80c44c0940d240340c140b524500200d0008000c0d030f401204598007810029040040c00d110b54081d65080045907034122003901203004200c012801039100303003c052500301783c800d481c0000e140000c020807015000c24007003501a880c0210100d9a54180c00794000b00482e40d4000d0981 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 256329964 1250 256328714 256328759
    0x50d02030c1005090a0b1e070c0c030b040c0806090f07050d0804060c030309050102040306020309011b0912030c231002070206030604110c15061306030206030c1b07030c 74
    0x180211070425169105070445107941c01e40c0e0382d00d01060128001304600201c166010218032a60b1804400a07140c541e2404521508102088000f424031445030390340307015469100404c40241c5040d134485202c4024024021129240e00d8540840d04140c204841482640328800400030101c66000300744c24283d4551060303000d003042c1c121060000310b074030b0143e50680d0220f2410303084c501803505044000c1e041003000945039510014010062001d260011845803d10500034031507aa440200c40110400482c100c1c400240c0e400414441808200da003160003e001380741840c0c44c90b166844480540304001d559080e910031984061f14031900a00c8100c0b800500b00800b1030401c842c540120f0010f11000700350b00d00c00e030350b40e02c0c001d0f0240b41c0003400c0d01c96101d1a0000c071040140f10005907070320000c045c0e680e00e216500c0c85007582d072004101c1c01841c0a880c0d018003003e055031a2010b0061507500040f04502899071214042c807400101040220010f5018480300388101d850402c103c202205403844440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 256331214 1250 256329964 256329967
    0x903021e0f1b060403030302090307030c031104060605030402031c12050109050103110105030708061003020c0a0c050a1a0702040e1e0309010314071e0203190806040e071211041b0c050d0203 83
    0x190b65890b14203803021a0380505000d40e898003941d00003400d107403440e000103100da00b1030b4101100307000b440909102240d9042d5030800845c0d49550098401e0b01003103c0095041d80304101d4a0990340c50809140c08070a224244031a03081982c524a005540c000d80000718110741c2c41c401002400023400d600b0490110a0929a25500341072100803c284801009180541d10a802e4925914440d5040302d408400398419200e0039070f03840c5080c080002d41031142c0c9104408007480800e8884d0f01d00c48007002540f1b104140d030300c0d243c020350030310018048040d00d58040340a141103043d50f002800d8542d12500b2605405166210040c01c0050110707081c43d0850040d480c01c100030000c04540054039990f0941440030321000c81c06516030120f03e5032084510007004400714070004100b050700404818000e4208440a0000802010701c50b80e8500d05403048801402945032024007041103c1e000203410b00c4050030104245820300b42116a020b6000d10110001c0c0e13254800700140042441003296800d9184082c6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 256332464 1250 256331214 256331263
    0x240a090f0b030c12030a1803080a0e01080a020406020c012312070f0c0c14150a200111120a02070503031305100b03030328060602030a1103030601120903021e0f 70
    0x4c1d506d000d1640c440f82400b1b01800d4030303800d075030181480d00c00655000c1000c940e100e41d074000080203290046032490104800d0700204110341500c4c002e88007502d1066008062110880004440075450440b002104031510326040651000000003011026076842c03c074144d90400c400d00801c90340341501c0004c00c0021042c042000500c4c1d03030351400e0881e0300100082d100c0449040018082041104100c3c00054000075180042c03500710743c0200035130405000c082030604203c042107081e40c034402d90111a03198108200c00440790451039180d00010140c1e0014100f02d1b403540e500b45950b00c03c0d0f62840205c24203940b42401c201041180b407088000441e401d02040180c038020030f0766400094003000c14511140d106184207402064000000320000701d00b4000b042e130340c041c069200e0b403001c089040050044480c49a051000008482c0a0207043c0d4540b82d8016440052400800b4207980440c11805801d0600140319000c4203458600c64042b0003521407100d040805174580624a141e4400c2c0c1034484150 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 256333714 1250 256332464 256332499
    0x121b080c12040f051906060609081f0e19030201062d0510170c0c160b0307030902181504050703061409060d02101106010509240a090f0b030c 62
    0x2058000741d20041d0002c030f801c803602c0c00074200740c80d98041e00b0204070010040c2d000c2c803415400c00c1040312019241d40c8a01620351202c1e07034980e0700c40b07490129409030355100e080c844407240d03210210b622950810740d0342038080c0c0154111407401d10002500181c2d1600e109104100c0380300b0f001c03880d149025010004111200191060f2a903240c801c80d1310600301d42c01c0f07070420b89000d0007010421100c901074600140c544010f000716a5085a8107401c2c083c407565490f800000c1a8111201c180c0f02401c3c202c030705659030307080220080d00e10701c482207030060034044501040782452070100d0300410003000c3c184254102007080c0400c80720020589001c050410008000455503440031310401d1b0002e0300c03003040311750310440030604920301e5180080d041110701500e000791941c000c441c4114216981e09844103640da41c410840c807014240e030385040c0b0040c500d02003008401da0048418000001400310800140c0d0f039894030040f03407606100081c10b6030b01d900341401c540ca0300303016240c10ba07102240c40001c0c00c0a0543d2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 256334964 1250 256333714 256333747
    0x50612130215070303140a09051f020f030c0706110313060518031605010501050f011205070e0a09020a021c0c260d0e0d0903170a121b080c 61
    0x5400c144444120825500c0b9200355000b940301d008195075807244a450010028441070079040e0402c03246001040e4495200e0041d40204c5420400401c004580b080a034180242c007075030034206560342040103aa500c840f074009148030301d05040c83c05490381341ca070070454255202d442480e03950003410420842031046a212051610b6000800044d80d5513800c0f1320114200c034003481c403403c248030100d0190039241c10a10b031030520610801c024060343e6a91014820804111081103010481000c504a83e01440e9440507600454510f00440241c890f6800300390840d00301d030010650181c00003503461798180c04200310043c1001c848052003500a550b40010704203100341030010146a5030000d4001d04002280c06103000011398640076a640d1740c161a1a801031642500c8002203001316904140203502489000003202d41020013403120b00c200701d1020f8091b50103844088180a45412103402f100068400d43c8140010507246200c110315018010f0498603005140d011114810170000900034044607 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 256336214 1250 256334964 256334971
    0x3061e3408060f0d240b0604082802030d080c090a08030406030e150711151e16120f14130b160c0b061503040b0f060609090f100e0718050612 62
    0x900304100c1c4201d441050380500500410154850307c08100400c00c000c012440d07100060018000900181140e031600c14101004180a0340c0b6801a1040c042418000c0326021340c4008549131051520440b00b00286190010f41c1002090750700c0070405104090b018070031101c507400da40c00102040a40070700d6241ca00310006148108000e00c5500c90481d9000030854403002104000c412000b624018407000307800d04502c10148011b500f2000030881c04180d0407610884680d482d0740345000ea1201d10803035809800d4844000e181940d48203641d4850340c81c116141e030700a10003115811b018241c503007840c550405011b000b0b14201504066800c225a4102020600095108004031401d58441c8002a0304440b04262036220840c000100420002d007042000c0c86070300140c403070320315640701c8070144030407400b503403843c9500040d82c100072032010008070401d02e0340071380d8904850385506c0d10f6040d01180d9540584405012034402e01c084410f480d50310021102a107019200f460525230480740900007850040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 256337464 1250 256336214 256336253
    0x105060a080c19030c091b031103060405060a1205030c010f0e061801061203051b0d0c080c010e0d08090c090601090e060301150605040503061e3408060f0d 68
    0xe020016403954010f207100003117070044803045030f190780e4601a401130403d00140c40c0c095803628080180c0a4040e2140f500440c0d00c0f5406142581c1d50341061100901001e000302c0e9004d00110400106c00509051000740c00384114040c40e2658860301d1001d0949144400034809941031904075908041c000a940d43d10401c2000354039404a27481a040e401050300d604060b24850701180010107054100c001041c2441080d205411000081518151542d0884c02c40b500000c580415810104800901519001c010f03200009440380d948030710b85181000e030795503803008104400e040000e850001d21100b0a0322a094421124a00e080c600090101109009400c0c0222204020070300d56182540504580050200d04031034103522404060b15903085407103114464840c190015400702ca4101d4071030b0308400d6200c81481140c0701d01521115110100c0b902003850094501040d020b0100400c4244c840030245c1c64201d000d003040d03818441504801e10f4081d0140e2107189820f000a54000c8503040722075140b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 256338714 1250 256337464 256337479
    0x10050108010b09060f132102100806130905010e190b0f07020a14011803050301080d09081903021501030b0a05070824151c0e0a0f15060305010905070303020105060a080c 74
    0x1140c0050140e219a0342000c8882ca91141041d00a403c840e8010707448a80211000340e04140c90034270884103444100d4015410000c540403038080628583c01151550740300b07000114a4540c102002403514442c10b0301040c00c4007214581d40c051201210b09550842004084440649827600e000b075916014a80d00601c10000c0d004140c11b029002c0d0722003600c180300e0040c05400c0100f5803c0c01006a0800c6c001c00e17030300c0d015030507128200d80c0c0200c424004451841014280c0b80c401e0540d4407558a00240007a8198066401c004110071040d5218034042e40c41014034208906158818408850004184c030086c03201c050b051000f85002201d40580e04500380048010000100000c44d005944010040c10312220209d8104110003520052400440300303c142000792100351041e45a80388400b0f4005407141035454203010220b01c0c9001d000c001c09107040000300f5019682d0751090f084403030142c0e0a45694010f030a00b07008040d03083c00f82d2500130204413001010103090001190f00c8000300c14456225249 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 256339964 1250 256338714 256338727
    0x20309062a070f02180a0b040510051503071b050102070c0605040513090804053003030613020307031e0b1908030a0c052814060411120f0610050108010b09060f 70
    0x94211440c0840605c000090459041200400015101c410314448c403d070305102c00510004442144001104c0d0004c0004030b0100d103212207885260720140101e4200b10740d00a440d104003492907500d6414034400c500050391070703e81d401c0c50300c600942c0d0741006c1c041000c10481003109031f840044001c620000e16000068000030b52030301c02214403540e4800e6810400d0311034608017142103551995640210000a41c3c15807011690554a0b4031081311010b5000d800700b180710550301c0b8280d024651000c0281800100f00c503c213051410015a01c0b00d0001c40316880b00c2100205081c500c0002d4100c5006e004207000043c05c040000d61240100041c1200b0000b00b00421420b2190801114121108151105102c2d140300c0c2880200840089002d5070540c0340c1540003200e2590000340350b0b00c1550810b450200c14000c0303070204031407104004200d100710712418070050fa803004140609170144910310007411040f0718013000500340590580c802d00d41c198060002c8442500c980b0215505c101ca1220700d10703035070f50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 256341214 1250 256339964 256339969
    0x40501030c0207030210180b0301150503041b030f05161a070623090f0318010813060f05191b0305131203050604110a020d0e0112020309062a070f02 65
    0x84540d44060741c0440e030920080610341c0c00c00e4045501a019642247c5103a440326080d9080b4842885146130702d501803060f0800c094030420103150801c0c4104000c20004800751442644000e69400030b031061000d1021850800404214090100130503885003a2040c3c50b01c00c02882000182c0c481211a640c00244141003280907440440a4501078007901c1c40c0e8140c405000d600180100d5407071000344195031800c1e07000180042501d4000c003009a003044007880040045421102c003a10581c614042d1000c0d0400141c098000c00f800441d50640026840ca89241d00c80c107200c0041c540355414902d015207109050480848641358402d460a000c261526420f610014500b0880b601902140c1c54540d000c03182c0303030300d60080f9000300400c9500744822045a09405400d21401d03d144000d64000100081c02c0c90044203080c40c0401e050404248003821000580c040e0390040f83c1000c41d6412409c108509144100c4c0c070380d40d1404031508a03c10207840084641e0b018860420003074445480c01010300c0840d03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 256342464 1250 256341214 256341223
    0xa05072303120403020f09010e06060f19021b0117010e090c0a0305070f090b0f010e03010b10080105090c031009110d0e06070305090d0903081606091202071505040501030c02 76
    0x240541201d001c0d00c14460202a03070f410500080380710300c40d502009041468500b0f000d6060351080e0786507620644030b950401096a0003940f04084612040c080701000c044244414000a061500030789081d905400540c0e00c0d40030782c1080c440c18419441101d411038011074140c50306590480f0201c4d00c9644420744c0c07503407500000f0780000b0f502c040302090200c1081400705513a41140e1600240442d690384440000f01900d04990b03180340c001900003a468500d40c4035502948440030040c00010721000840d01103401c4002d880704980c04034020b0340042056041c501340b419888074a965550f415410002c0303103481d041d40c40b48501c2029a071100c04404803d840b031402c0710569061504104002d014032103202c0e0700c0e06000c03108100403a140c100010341088022074101c80c0700046940d5640494110b50781e01659400c040150b481422460b60b000700060110b108a04040b4092092424000441c0030001d1134034405030490362008004103040c002058100342914241c50003401c000c95850700422049241 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 256343714 1250 256342464 256342529
    0x902040902030303012909060a0f0905040e03090102070e04020f10050d140105010216060905061b070605120a0603050c09070507211b0f06020705120a080708090a0507 73
    0x14000013000294141046072658280b000c40c406c154200005070b040030500d40580107542d500000704000195400348104070000b1000134030300b0181d81181d29080482c04580410510040076800052500e4096130100568002001c80d14028681c1c3c0c645540400c5000d8501d0050501804d1a2b03505075103000c0c0120242d0380d0b040350000b4100416148050106000c042c28480c09015000b07407825000011b000b02c000d00c0079210691628580309246c1810b102150780544240019681071011a502c0e46c001806010024500d56403010b0700c8007034112452800d01409003400900d10b10b0204104001000403a04404004013100d00c0c40103580d6445080d01c1c81c0c407800384020209000c4043e00c040c0b049844012454251040c1d6131f1621078200680340940a40704030310003410f400500c0546900151240d0000c1c00c100380f040054488008a0340040c146640ac14010381d4041010039003048a01c0e85d124010303aa01004910003040038000c00e80f64503449404600404485015031400c3d161039103600f4a40024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 256344964 1250 256343714 256343719
    0x603040c0504231e06061314060c0102040306020901080601050c0d0518040c080708070908100b0a030c0305070911190315082b020d0504090c0c080403030c02030d050c100902040902 79
    0x80c1440d100b450303c26560502c0c0c1c45010071110500101705a030030035205841200d2180b140c207100f000c2c101000c1503030000c10503450319400384080003520b610324400e002400045129801c0580c072204048005000d4410080c0340904000060140d2155035000043c101403410840c10f15555646045090301d600c4030a0200540e002810221500880750303005204505c01c50312542c0d0006a0b454101c0120b6402189115400c483c0e4032002c400fa5100286611094036440c0c000c040440301c980c0c981c0c5031030b04400d00794410345140d0002c20041041c5011402221481c01c03551040d586000c820413034050540e0040101c001c20141d54192100e4110050141440940074000031120480c000152501c005030040b44e0044061041164a520160001508240c0c804c150b89500b403d00c2d00300708110000700009881c54080040b060580404591010001c1c8040d42c0280e80d1111800d4090050501e0a006800c0030010800d04124403400d04074041084844410b0303d11011458114900018000c1c08265101a5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 256346214 1250 256344964 256345031
    0x7061d0a050c010318020f0a03050604150b0301110d050a06030b1503011b0206070809030f03131101020d02030f1308031b070e06010c030c060e0a03030b010e0603040c0504 75
    0x2a841000000e945549910801c1115041c1849000440680741e80040c0b100e594080e03030800d6001031500c080a00340354400034240c250050307a25101c035840c0c031000b510203a854020120401c00ca41c502c9005020b200031054000744114020b40750210030b148114203000100d9a65400498000c52143e041940195000500040c0c103003851080c07a1250b41c1c02181080c443d43c078207409142c082040110040c106621900030b4803195840e100700362190400109030036010b010400000e142c464800300a54010680343e1481c1c1006102882d05000c0c48880701c940d0360655000ca92074511040c2c1c0041141c0084590a15042e01c2d02241e1004059680e000c0d0401f400380d00002c9540707206451284181d00d03076214481d044034016503850008040b0503400f0b03034032607001440d40350390400030034041c004862403075104680020340d40303001e107004605004208004900080c0c071a8444013003980e00000c81258000d044502b10318508240d624110005414400d03a409107494544c244807002d49200644509018a4910b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 256347464 1250 256346214 256346261
    0x30705070306050a0c080c0a3605152a0a0203030c2508072c0f041511030a0e07030206070c05030d09051804240203040c050102210706 59
    0xa00680030032114201e1441c0390030b190842c60b5210301111b80c091001400076510f0b100071000e086a00b03125000b144424000304480c010100311042c0d0761000c5200710382d00703130000320303400c01d0104441c01c4400400c5076048070013408200449501da0407100c0b02d002c0b000d5403800a0718250f0135258100400c0319800395143c0000304003040e50440200c0c00020a58034079400d0f014010304101d8603901c95030079019055050788440002d100d46584080049111901000d41d2001240e92112600044904484513117000701c0e40403e02040010941d054a00c1e00351910007400152810940200507020042c00e5040b00c41d100d11601546500a20007000a150007814039580c1320006c2c10482d101c5002c601c10703280288561031265100a02c0380b500802a110002c209010f0714a1082c42002641c0024001b51813030700a1000b0055075452400000110b06840030740940c6928090800c0e641060955104a0664114544d078080c04020120b00d0300017020007818007030f2903807030701c1c1002d00050003040740b800361880210300f51 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 256348714 1250 256347464 256347473
    0x15180613060303090e09070e01030305031902030a140c0a17100f0f0807050607030c02040e0c090a0c020606030a02010212071104050403030902030105070e090105100c0f0b180a05060a0b030307050703 87
    0x18201620002142d0f0030640e15500c10440c1d1f220210300c200c5010085e80344c01800060b2007040110b8210b500103d03c00306004a003500d960890344140c030310b0748003d40d80b680308140000c8041e030030721750003039400c040c1c24140b0700040c80280c04181c1c0d4000d07410401043c2c0002884144210500c1c00c0645010302011005984a01c595a1449824059075800d48a03401001805140120407601803e926980e83c1d02060155802d201c042c00899082140c28050074031146420f0302d4020f0f143d4440ca218030800b003106c041564010b824454082c01040c0260040100e40c005030340c00007501c5030704c2103583c250143ea45d0100c1c100a42500721510b40300340d10906040600082c1941500044c80003402103000300207039203c03100103030b40411401007920b0b081840e1600421803803801c100d10741e03000d404900b402c29540043d40e0701d0881c0d90034140e0084400d001807000780300080304006000c0800d0030080d001402c0d00001500c8642da1417070018089541ca54480021182a0300e0500c1522543c030307400342c01c40d0841d58480c580b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 256349964 1250 256348714 256348727
    0xd0513420501030b0a0e03091e091006110609070e190908030403080906060d060b0406080102030c2d0d0c110a03031e0b0f040203040227010e15180613060303 69
    0x100740c075502c1540c4003082080d17519204603400d244c1c41000a5182954280901001a0000c4004030700b080101440602544170680f00521810700000c101480c01d00300b03c4003920340d9a500019800c0350b48148104011700c0000184c031b00c15189185980c2040d40e42e08a98020b0f40c100140c03d40c61010b043c80d0607102001043d40c0554000da00c00e8981d00101d030f03950300e0b030030350303184c00c104c50290741302820305012004695158081d130f2000c00040c001040c51074490010301e09984c801c0c2d8030340b0311440e000158880c0306440e65404560005040d07205035201400700185040305d0050b105e0142c00b05a840001610013801110001c2050008105503100703e030450401a00800d100c0702c0c1c4016030750028030032075000c5031144641090808028a5101d446400300244002508000e2040380c00440d070042c1001e02010081e80142104c11004a1000b20741c1491862240c1840180249607a40c0b94101c0f0401c5d10790b140740342d0103c0c4142030b003000038141da181400504c1400c104005442ca192034240f010003403562100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 256351214 1250 256349964 256349969
    0x150e15040f150e0409020102150603030f040602160f03052a040e0c04060608100b1e03010b070302070906050d020d0c09051503071203050a180f0b0d0513420501 70
    0x407079203901c100580f010b1006854170410024010b0f0060062410000d02c0b2454440c0c000001404507800c2001142031684607902c1a04858090390000d01c0c8003c0709400e140d54040a0f12034082d19040f8246182d64542d6991405105204091100324400300031b41d807580d031108458880104103020224503256480e4a655651032800c0c010385c20303e00c01050031806403201c0390042e00e505100f8540390b46800221404c5406c01c03075029a100b4074040d41c005901400c0c4001e580a0700300942c4d01a41e580040c074000e0700e41181c82d8001c041c5142050410441c1c0d40e205641d00780c1a81d010340d180e8541002c18034200f040250203030046e424091901c800c0c041900c21900e20710b4131190b02641100c40072911104801c418140d02503008000030000c000b1040b20500c241260301004250b07060f24401e03141c940220450780401030300540c1c010701d404900100300a035203001d0309400404480400072030f25600d848405400140b0421400c0c46d0321a1010141c44c00c20301601074104101031422850f8040e00800a20041c080a1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 256352464 1250 256351214 256351217
    0x211a062803141b16050c090c0307170906070c08090d03031d060f040807170f030a0c030507020a1e2306061e01260901050a06150e15040f15 61
    0x340c0005425990030b0b0024506140314600031414138922a010031010600064101d801c0d0040310720680880e11a500014080c0b4440d0782029140e140c281c0c00185103844d0180a088022060310038000686000f08d40150000094645104c141120b414011000c0c41201001a0000303a0342000300c0600d039140c0c2c442481d1425000c02004447c0001c40740075590a000d80e012802043c40300042400122103100815145100b2500d61001c5000c0b0140521a0342007003c0c420f080d04000410441c80780050302ca840310200e42030a04004c14103020320025660198403900900f90600c8601c83c0407900800d91045000360392201500c20058600000349207000d80017034a421441c0300d560049451490101100000c600170000e80006ca903c580c00110744048010701044d0403540707261200b803d401c000300c213810300c07903500303c2d001107600d04000142e00c0880302d450380b2420321404031184500c111980808030090180d1700300c54441d5189440707130483c0d54505c5a03038014500052450320005a09040400d0a42d686009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 256353714 1250 256352464 256352501
    0x150403020c0609060d05090a0503210f040308061509030f0304090608060c030406090c03060c080708010f0b040303081f03050a2006030a0203040302010b060406211a062803 75
    0x105014003910f4040d0506142d40650f050141e03600d07590b0b49500c203603801907000301120a5864140c40d941d065510104001940d601c02d545002d41001c14840c4054100904a9101c61946081d85006100403070280141d4441c6440150880440c19203200fa240c50760b100030140c1d43e07050111100d050766030b4458850041098204000000c202c003000c05d4541c440e0078620351840c5103a0b00c40d95111b00504e45d40001719810118030002001107003891241080741c000607103580242c2c1c10040030180c40420164000244031200407818051098040252401c0340c0c0c0c14140b81ea40c0d5103c2400c601d407558031682504041d00400c05001080c041c0008030f0004450150301185080e400543c540d1070940307080c91310647c02c0b040804c0480c0b081d001e1030f401582d000d030081c800050600403a0001915940c441d1b805540001c034030740b40c801042c040c3d00d86080e10115050000b00101c116001003400303090206620103204100105000c0e500e484080d04e210301003070360841642e440d01b41403030010700184030044416002c00b51 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 256354964 1250 256353714 256353733
    0x70306060b09062a070b0909100302010e01200a080418090c060806010e0405010807050102071d22060507120605030307111012050408030406110424090815040302 71
    0x824411110391403030141405280501c0000c98004101324500983c090541c40c82d03050650103001d0044c10082d01c5104151950307582c0c40c904110b103000010305128400c5042500c1040181c2e086000f01da08811b003030030003c40c00355000c0c207150141e0710030404916080c002d042c101020000d0700070041040e20210707004004120008000b200c02c0341c101d80720040503000c89080c01e100003409103a4941e401901450403520144182c80464240e075403c1c2c1c01441154451078040c010707917805020080c09401c1c0c00b0320080c00c182c6c651603e54901d0b1005400d481c640007880140706c0e115481c0001601c038035a08000103114a08100701d009180038030941400301054600440410540303004021601e8980c1c00c0f240050303102200908014074000103641c2542400b481c52122106c0f24208d008951069004214007038892070301e409e040059034418040c45408200801c8103100007951103040c000c1e819041070442082c5a08c1400a481d00406908199464071039900b400c40c200b6846503107284a0b61184e0300303803a031524 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 256356214 1250 256354964 256354979
    0xf03021504030906031a0d0c030506010909020d080d06120506011d01060f080702190b010807091b1407060912120507050a05030606090405040c0e090705010e0904060906060807030606 80
    0x1034241d60040c0064901d45040081600c0381e00128a50364000303919a4018500e04001134801c0f94441c412207110200400030410b00c40103000042c0140400315040c0000c0c2100e5000544640840500900411020626480260b125070020001d0322022813400c1c0d006000d4100b5076030341c1c4800d01c03c8001c24010484174035140d0803600328044c129103558a58450150060f034080d200084010b00b084114400d00b1040d00382060020302e180e034014018418500c3c1941440032103030400c501a04110750240c1010003004200c040e5454403501c7c6080ea18101507903046202c038101283c410031802801d031509201d98581404220003030b51007249890340302c042592500d070b0004002c1da401107400c05c02140c000e2003100c0c0c40307a010f60000c683c0120002c10442c903107185100001c3c105d6109641c02d60b840c0051450034040400c0120b602c03604421043e00801d0910b103480300003010600200c1c91640200741c080c0104040040b59088482c5880e4441e1040c08040e031150407062307803194a840b0a07503406040c20400203041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 256357464 1250 256356214 256356253
    0x3370c060b0d021c05010905120a11030306220b130c0f0c0b16090b040b0301170f06060f0d05120901030b120c10020a081801120b01020a2604030f0302 66
    0x1e5000d0401c203004c055031180008a80401c01050301e180d52110302e4280012000c0c07182c0c0c04003080d080c3e030098440400c80d400a0200041ca484452a41d10400600101f039550f890000b00080505082400c4c03840b0540071200504541404030b034000700e42d0050351508181981103c080c244d040e46c5d41035003030301e041c030000c44403040807100c09001d0074075100c0032130f40c0002001c16075940b100281c00c14807440c959079050450154040c0e0702809076080007200500401c2a0039546881072003104d0001c20f441c69950b100c081c1c5901016007a984103540781a41d490f1192a1211040000c3d83c10006175082680000c180c00e0303096100d580c0840c00249407030030400e5649800c078000c3d001d0360804001000c0800001081c8070030059410303140c2055120711800c00c00025900700c02080c1004e031850107803d0300795403034001414009821644801c02420240c403084c050342c0c0040ea913102250040b0b0030300c03440031102004050702c0849902c807c840c014005004002d100355000e0394a000c030300c21350032680d111907482d1400004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 256358714 1250 256357464 256357489
    0x19051b0c090903090918010605060705030703021908030a0b01030603150c1206120f08070f030306030203070902030c1206040e0109111906140c0106120b0403020d030605010203370c060b 81
    0x842400000b0582820500046030800f21b001000003611684400c005207031a00904821107484c3d0000808030b040503414024004d000704601e1000e420400d655841c0041804014882d115240d50b80c100e1a040360300c40e4010310011034101c080310305141c040200b52400f8080b108140c40104d090224890307001515440fa080446103191a40b5000c01042d0f9100c0c11601007a0800b6141c07210103001d80c20118040103042d005440c82030b240041c213207103144140341c20060643d2000d0021441802002000302c041402c032024440c8094003041140da92000050091089000100d9198680a03090b030410a1400301000e400b2421141c401c240c80d0489002000442d660103684001b4400d4403030360440648a80c0a0300c806d0700b201001065054403981c1c41607804040c24015150072400200344070a150701402041c0c640a0349280c184440390a0000103903503481504541d0081c02060010010843c07040c19502c0d000e101c10350400801c405204900409a101002042d07c66500c3e00b18210200d15001c40071142 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 256359964 1250 256358714 256358719
    0x15041e0c02010614180604150e0a0501081501060e010908071805090c150a1218030e0307050901180e03030a150b03041a0402030309040c02030c010605090c19051b0c09090309 76
    0x40c2d40390480410745c100301c405010290030035216420000c07007202d40d4013414050190104010401d1900c3ea10300e07015281d0613406000d0503000030001640d01c0383c0208085041d250b07607007843ca98184950303004a03a007214950105801c0d024400020402100107400380119500503c400e20560300d40303052464403644000706a0380c1c8410640505d4244c410140c0240c024030140d4280400e050f11038039113181c1616a40d83c440100c0e14081c0702402c08141d0400d40141d14040c00360020a884d41c180b40100d105c0d00418010110b4a4030300b10702811454449030001d0034104081025240c490070120016005400080000c030400302030110041401064075095034402ca400c60005081005850b0b000f440350300000d00143d80501041224251503121707405850350f0107074598015503442e89101c880301d007195100d07002248518040c0341844212241181a03c03041ea0000110700c00c041c03980b00381600d4520503a0425503180452140c0e12003446004a107190442c0e0041c0c81e009140d6a680301f4054591041c90860369 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 256361214 1250 256359964 256359979
    0x2010b0102030412121e0302090114070b0f090a05071e0605030705030a0207020d02270603030c070b0a02160f0e011a070f050f010f090606050301020903030315041e0c02010614 77
    0x401040317201c2c410500b0b502c1e0354102481300c030f240940c003183c81481920340240482d4000a450f110341d43d0285c9518500f00960383c209003045e050f03548205c450400641041d400318918808504500418821a01d000b80d007c01111402541c4410030b401126084005003d51220884005001d5024401f102d01c1000583d440c946142d45602c40c6200942100d54141d8025580040d400010380b0b4a1074052444054115004060600c14400698808004214501a03001070000c284455000a442010b5400c0106440d40b1802982000c0380351500107014454480c8140900140d0724108407200420398104141c0401143e0302c80602950000380d0130070700c1d802d20a04020380c801107048040014070b0240320f4030950b444a00700c00c185900b501c0c4040411002071341e6503000c8004000c19846050002e000070b400070750411140710b001076264000205404a148441c4450707004a540701d078042d100d45800c207444820f04400000480b8001c0580e04000001356181110114000a05007401c04941c0001040f04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 256362464 1250 256361214 256361249
    0xa05040b0a0510050a061706030c03030d0209040f02040f06112109030a06060620070f03031407050318100305010302061605031606020a17010501050414031e0d02010b01020304 77
    0x1c60007494003c084034540045440041880e03942d40400700c0c0140300b2903960394001358159a05022240c00a05481e12a91002042262944011082d58000083c2810040c2c64041400c049800380250380c0b0f10701c0409100180200c4e114100c034020f142510300740d6956000c002c20074414180c0d5008407494034050584640c0703401440f100e00a00900003010082c0603141d40c030141c0d40d81d00302907555035081207010a4480040b990300c100129081143c0e07258800c0280001842d101c140400200d5501002c2d0403c40808071800314040703080100d80c0c0141c0d0001c12203503034180022652230750700d408020151040745041c08404481c1d01c81c3c060141603035002060603240c6060b908800b1492403000c0070407221400300303010b8a958082030411414105000303030009683c9041040c80205a852440200782c1156070140042c0309a9078000e0584040d91086011216154180c0d0000381c0380142e015002800c42d490903458000a44021400840b01c602540003400b044081900580c0c582c0503c0c0921500b450450210 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 256363714 1250 256362464 256362481
    0xa0323060f10030b0a08010c12230601090e04050a060b030102090f01030f0e01050c1201080d0905011404051018080307030c1101030b030a030207031703012d0b0c0a06050a05040b 78
    0xb4410034184030300700001c100030f05501165240c00658818890b80c0d546081d450882500f05281c140e00c11285c40741004012001c44e03405600060441500011a4280000030483e034000c5040d8000340181024070011071070981b600c2d0f690381c041400101c070490b0901c0c52401c8182414002e480400d54010904c404134a400303001100185141180710700b06a8840d0703c00345c1958002e111311401500c10a850540c2d400f410404010390003010b07403000d90240d000300103008000e5800800c080965109181a49501004d00c201c001c03607004541025030310800c0d80c00782c406016040b41c44051100400000e4441c0b180c2d4442c00c442d16805404009004030740b003140200c0c0000c80d003618018001c0d1050400089005084020918281d440a0102c0140c1c0c40b00005000740205d61800c03001080ca11a1424503560600d5000010b05000c0d80300210030100714120703a980c004401b8661400742002d014075646030544680310740c1e50b5040303019041c0c03044c0d0300d0030002c00e42a10307042c05640c1c801d030b81200074002c068a66844 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 256364964 1250 256363714 256363729
    0x70609050306070f03061205031e09030a12050409020a020606030d0915030f060806070f02011b12091103030d0209150f0913140703021801020c0307090f0b03030a0323060f 75
    0xc01e0170507580303800214005207000d1b0341c290580e019400964480b845501001c1482c1c50706008407031490011301604540390f600107402009039034882510000300254420603140c5000c2e54000c0700c01e04e40086160040d03581e002668603c0b80f40d08600315855082002e00c166078804003805a524804044c2c0c0100304540d010750440e02d100004407c0c0001d100b030341c841d66941840f4080d02c003000060301c100000c4050660900403030800c4000c81e40181c1003180ca107503000d0049100c8c030014524254450810400344001600c0200080704003406890b0345404224401d002544810f40d00c500c601e051801070702c0380824032015207085800c01084580f40c911800100055404100c1d41d1450058503010019607245140010a000e00510f44000d030700d81e460080c2d010b01803c0c0c480e00382d41c11941302c8415150b582d9000140241246ca861900080022417507000c04083e0500e494003982511002441c011080d42c541d00844100440000084204c15140c41110065500f03443d0158414000c000c98196443c1820 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 256366214 1250 256364964 256364987
    0x150102030403020406120b011505030105150706110319060b0f090a030602040f1802070201200111270a0803040501052b0b031b010c0f051f050907060905030607 70
    0x49908082d9070781e0008040c1d503604d4111468110300051004204144a5040f40c003400910002c4000c5410f280c5004140380414450076100350b40445403c1c00d010318075012a0700c0542c04c00014020709058840b031940d1a802500c030005108404484465603400503c2007500761050040005d2820703002c0e240021254100b4500194030400d000c0d000000503049100400c02401017410b485052850403401e01c030490076182180206900420040c0f0050b82c0c080b03407000d010400c5091000e01031641d040064018174500c515084005400160700402e0b040300d00000c000c8407840003c880e14400000180941c10420b4070a40c0c80c141d2092005010369030051303010702444a83c40091000d80c2202041c046220810302020441840c1c1d5280b01c10a90b050a06c04000201c410046160304101350b900000c0c00c0c000c4885015005a41284c400360410a0500018260010795910610b00369a5010781d40f000307000c280d500481510401000056042c0241036080860b000203010382119a07400800350381585165 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 256367464 1250 256366214 256366217
    0x3140403031d060c1510230d05030409020c030705070f1d0405010b0603180606010503061c0f0f0326040c0b0310150e090c03040b040807050a120324030305031501 71
    0x622046001d040304121080207621250210602c41c24100b69802410201f90030041203186070314000024030300750030001134920f601a0b030300c3d00c2030415a080481c21801117030446e0030290700010301d500c0a46000000350000ba40940700b56181d0320f55801c000749105400740700e41900c40c5048c800c24440c0f1303e0701001280c0c1c030900030000401d00d00c4605001811540c011516445091940c03105041410410411250300280a017402491403c0c620002000403400882d032502411240807818104840080c99180d100d51203161081880240d01e1b000d48a000c841a041c0380e641c0e6202403807041e1051841101e8041c41e041400c01e541c4600f0032640c0e0010b548024a0464404142580040d5100e5a0108840045100e541d4006904500800c00520301e0002c0c1002c20030507028410710001c13520414040e608140d02080655030f82405240a508214040102034040c220120b20310803800c1d01900881080c095002040e0402400360781000b400c48054000940040c80a000003100740c50300d038401881c90342c0705 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 256368714 1250 256367464 256367467
    0x170606040e010b0d2406020d11060118150b0712090501120b0d020d060608102c070b16060b04020c06150f0d05011d0304060f050d0e01020c0a03140403031d06 69
    0xc1005d00052066003100c0b82e045440d6000c010140d03061180c032013540300c1d0740f80c14018000300c0c000c1c650f030f11403040c042c58030b000744c94025544091006900c48988040d60103091551035a03100e000703038030f150080001904c00e484010083d011040c41840d00d10261307401615152482c3c03035004880401820408220354020111841c24030143c3d6802c4400e0740c1c494480c080124a02d401e0a00302c0d41803c40790220a82618101098144000b1000800145084880090b900f0442c00c4001480c64a1602e500004404c1d200103104004c60003072107988000710f030265106002c10704002d010b01c03040303100359020381005401c2607000c18010030341c0303014500e00c900b07004280c0304070b61080d40c000400030480d0f04422074841e9900d1b9480c0d48002d02036091000a0307503840010703504051405101824604081c4c0c0102e041040c00503c0101d1602c1c9076011841201000d00210f49603115200f04a40d1802091410380c040b51480c00e00e41d07482d111501c21074040d00d03416030f0b0b409001848500c00c44074004100c81c2445c1d01400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 256369964 1250 256368714 256368731
    0x10c1e0206010608130b390d0c0519020a0201080609070e092d040605060909120309011e0b010201200d0f09050114040c06080c190c05060106170606040e010b0d 70
    0xf40410680140600180301f007800c0355403401c0308a0088401d071034401e9007042c2da100e00c44000008042d01d02d458004a008144401050000c4403540305008204003440d80c804c010f403503960b90006011302094800c2c0c0300d00c0041d0b1112420080041e108440d250001080a01521840c1c280083e4440d000b504501c00b040c00c448402c24118141c1305030f00e1035440c1b0800700000700000e0000c0c50048c550862010341340a40a410103031405500c030707810751800422201e00040403c0322804d0075804440410710040360500c1542d001c58881c000307070109a4402e4015800c1ca603080154043c002c80b802c0400f460344c081d03e803401035100503501c040e1400c4411006900d07078038210b81001c00c0083c09010070f40c5140707048807031551420380787c01903021001d501312808001c881004c2180710380305030084503800501d00d1241c51401c40c0b00c1030f0440e03298000d0300c40141340e40256000003500d40c1c1c1040b4040d01d074100307c2401a015079101010301c40c00d402648075400350414110700400c507041c007803001440e44c180c2d242c6000c1440c40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 256371214 1250 256369964 256369973
    0x50903070e18240601110705090711010507031a1c0206030a0b01090603020903030a2a03121a0a030204050c07080301060e01080a09030c081317010c1e020601060813 72
    0x14122019107000c000164481e1502a040c803c8122403244103411042d1030400702a11200d000008001e07a0503c04840440441c400342004441c006040c000c03d4464a40b402c64001080f4810b1545010055801c5c0800309101c40e009010b918520781d01e8184c600b4040c5c0307001c2c00304a01101c421b601e1181d80701503c24054056101c841c011449144202408030300c143d140800146582d600307500031001c05105110b103503103a9174080b04540c20f40305a0300e000d005012403103550b2071845582da00d0002010903000d030403604054118020000c600310951003004000c440446010f90444000d0740700b0b07404588a6010700042c54903a1150f80c00070705d03181d50b2030f040001c40d90351442d165100b0303004540420051144080c0d250390009143d1307071003411914103000c00582564013600c1031104202c01841c4220204846c621900903581000c010308440300d000002507400301c8154000c0c0500c00000340052030740f40010349441d0303401c1c407010301c0e200085e4000d00c4d640c0c0c0381c49000c891805000c1d00780443c40301001888004107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 256372464 1250 256371214 256371239
    0x218030313140109030309090207030e1306050a0b070f12031e050f01170303040b063f06090d030f020f07050303100504060503030d02070c030203071206050703050c030705090307 78
    0x110860100112414204454680880e0200150401041341014800264044a00c408640c02c4200160700c4650038a01662654124025250030084c41d00d28041030403101d030000300031100151648034141d40c0301d49542d000352048220140c803225941c408080041c10701d01200502095a2a000414800e001e8031203554280031104c20b50b40315140c409103c0e0801a03d0441d074010020b6181100c0c007aa08040c80c03540382d010051016100c4642c000c00244142c960849040c0c9010740c6a024205131001c0c01010301c1104a9100b420450544c91509800c1a01e00054511700402e203040c000c080c40000c9580840203030a4605000b90b40d01e80130f01001e44507491070700142c048144100040d40c1c82c0d00d05140840e003101407039030200f071040f400e129040110b52000700071030340805100a4050b03620ba0450a2420076601554002900340c0b24814000442c0c128028100f41090320542040c442a110203000b10181c5609842c501100107040020688040c0039500030040f4000140030f0b40c44059035100c3c0700154 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 256373714 1250 256372464 256372477
    0xe070806010305150112080306030c04050c070b010509070801050d030905030109350d020a1715030d05120f1e10090c03090b0142120513030302180303 66
    0x880d03101800600800c4000d0040c01410086012120401c3d85480d03810459242c82407000b40030484000041001074809100c0103050701c1010700103004030b00308006900032980c8a200241e55059041c40003041d036103840c084a9000328050307994038905074209410041d4900b02e1800c12418403c80844c0080c19071002e0250717081240c040c160307601038001040ca010060782c52011544400703c4c24402002003480c03007079007580c101d041c0141005072039049641c402d5070340c1508454032703a01c04001e80040000c0b41108039403640b13040409074250b5010740840036083d101d90007201d03020741140030b07001c0006010412642c0c130154404800844045030399141124020850310503120314641d2041c0000a10042d0514010180003285d145030420503910903849840501006000c2e071030640140f01e41d000701000410082c4a00507010700ca221040c00e40260604c8144440940550041040031500103e459124860b2900c900c0001d19116a00711060307030708900031b6002d0214aa00880348516041031910100b000e44039 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 256374964 1250 256373714 256373729
    0x5060315190314010207030323010312050706110301060e0a1206050408070b0f090c03030708030610090f0b040302040f0c020a0b090124051f02031603031b030207140304050609130e07 80
    0x780d903031b0b02d414020296903940899a66810300c0100e40285e44402c44a92411a5000341520010002c41c01084686224009002e000e8500b00b07520706c05042003c0c00210304075246600d8a00c403040c03e031414400c01130b807a44504200b0241c401e00107404180b5a0700119442803282680c98a4050709030f9031a000b10605903a802046a109410080c400c3c004000c3d42c015000c0850040d800c01e41c2a035104800ba1000900c41e500910f40220450742c00c50107900c01d030b806007005110f20b0703103141e072240f1200c03a090700184426407050b42005c100560f158014031400040d0390b1180d025049110440c2c4698042c100c0140c0410040d42d40c901d002a00c1d45074101e4482183c180c071060003213800780303050104001c0300c2c107240321083c503003038a03039180d4980c10340000890304100500c0040c18a142082e04058000384400110010b0a4100d41030640b030345941980100103c510a400e0080814040442984e4034016802801d801160030001000246054140203c042d440c607100032075019040a074690030903031164403252 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 256376214 1250 256374964 256374967
    0x7080408030304110906060403140c0402280c02010c03050304030c14070e150f0120120a11010902011413050301060b07031106070f080a0b0d0c0f050603151903140102 73
    0x20007035580390121300c0f840c04803171002d0b580c11300380005001ea10481c40020212149103894500601c3c042c0f000d0486000010003c5403501d0900c0001ca490076941c9902011040400b8510362042c3c1c0141c2500e040290181c0d60b140c00081590b900b500c050b1700c05482501805140d03005140011001c00ca00b03036030800d200019140e07082c07805481c070100c0400507082d172000c00480c0b510003403252a43c54100ba0b25040c05d03e172101040c8403035044510121044d90380e40381d0b58090002410740c40c8243c00014900d80c04a5a190b415124541030709508903504184000d0000302c0c518a0300c2118807640000d00300e5000001c16100400d559200000e0844601c0d6020178142000400ca5005060b0000841e4080326a400007401091800080040c0030902d1221407009000c103840c007007400702801d5800200f8110001d441800d000e045403e0017034881400d0322500b80309180c01e403004142c9050200590f0f00070045480c884180c0d80030300c001c1014900110710000603000038210f002000c1490b0385e081d5204902c2160005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 256377464 1250 256376214 256376221
    0x6160311010c050301120f23160e150618030102160b130b0a05040303090f050f0601060f200c130203090c09041a040c1a030108010b0a0b120c070804080303 68
    0x35030960348003102c02000c0c000184010440c0901080461802c03c0e13002800951b030742258a401c0c3c4c0a44002e04c400e10f0540504101c0d420039180002d0400c40e80c500e006e51700c0480e1642d558100c0c041802c11a82d5051180d0781d6a401422800c001d4080c003036807800704409a091440010110f0b007260000e0b17200c14510b070300100111061145070b4220036000450440098503042444c0c41d000481e10002c0d0100074210b64840006041c140300b60301859085600243c1c0c000400064101a80e440d022450218118040c5000009032070b802100c0c5003018040a450308160fa92280e142c01045412034110a8801c2c0124008010795580c0d00c070740f200d401221111b0050b124101803881703524102800840300c4c0601c0101081c0804112400d4088600c610302c0294410702c0d80e110b04d00a0b00744402a03011a90440784082e5584240c00076402450503210980020848201c04a00f00013500d8494465607034401c0d001c00c503181405c104850100e45c0500e4105c08146401002c0c2e56000441d0701550103050030750030101c02d2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 256378714 1250 256377464 256377497
    0x10021c0207170a030c080a0e0a0b0a030c03020328020c070602100f060506181807020a1407150f0926010c02070b0d0b0117070c140f0615061603 63
    0x24040b0310000781d80104058000356801401581e002d103805884c54402041e8418110f1081039200c08040c80900b54078800b640e00c5807914075507040a030003140402d0806003002c6516201c2e01c2501d05c0f0303100d043c2003084070341140d22070200c0070440c0303503d1109000c4c0c081000c501801001c0140c0b13801001d40d6401010060324039603451040300d40800d100022242800b20800c0307070f559404181c0301c10010f1116a2002d82d0845000580342910500c01450034641c000308000343c0607004107404100602800c10140c0480c4201c0b900c0e030301c444c06800b07107010303d01c091801840181c0c8145c1c021302c181521400d26600c45a1500041c040a445044018516080d0885e031001440c0083c001e1b642c6001250004204d1241858030340c014078018210607042a9580b0315042855030710031035170020601c4071a510900d040c2440d0000804107050300c0c0e81520070841e04c00c00510161000100702e81084000350207401992103a1015407408880460280d80c4100184070707540109480b07030468182c0340d11948400d05422a500e14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 256379964 1250 256378714 256378739
    0x10f021317030f0904020a11150118140103111305010e161805060c0703170d0e0a1a04060902031507020f07051813240b09090c10021c0207 61
    0x161040d858105014480c04030242c3e1090f5030314400c08403009600e8940d500000c1f00c0d17010b200c582d8800710b44030710401c1050001109201c41d0580b18114560002000002d0028081e10b6000f403002e450301c41050b0040010546480e05c1000381d00000303100030b85d040310200a600680da82030308110a1210316000b8041d01012000c2001400c0e206410f01134480a402d16580c01755801610541c0c1c00364000113400c542e5004144010700240d0751180708400ca030340524500d141c0c1c640021300842255850910708080c1c45000017003080100354040108440710708600c44206c3c07111006030044818035140d05480f00140d1701408502034003010300c500d540d09032500712402444d01030345640320070307694003d07090500280c3c9a112691030705406010000880b911280001145010b0072034002d40342644070602c2202c105107200054080c01c494007000c0c030820344132404004403014240c0380041c55038081480083c0508101c42006240903250040d80c144606e42440c1082103611390101ca00140c000090070301c41d0010004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 256381214 1250 256379964 256379999
    0x6030c04050721200403060b0a0f060c17070302030c01060f060e060c0309120d021b0a031e0203030f0706110c031b0a021807030506150301090e010f0213 67
    0x19024001c0e03050164010340243c011140b080240b50101d600d609500500d9008120480300703010420f5124041c5141810085e0024082220301500348411f614051525816071000d8480210501d070189290040558183c0504c1100708d0b42c4280c07000b807480c515440301010b0030308103000e5005035581ea015004158211780131a0080d5080d14507041003440780560215503131040030000c0d0b0701315545101440c070003032840c00703400340640e4022903801a0a00c0d200020900302d400f0825502118a0384c3c03a90001029164501c0000b540c1094803c0c00c10404100c0060350300c525485101000d5a000038160080388c1594081a03d0501c2442c1c006841410002141324014400e00a200c07e0ba0420702c45070f48040e280e00c201c0c400007c400c1d08090003100120006d001509482c6c0e0300609404a440c0c0c400340d1074007107520842d050340201c1d2422000400b0b5080ca00b040d010000013452005113140e09210121004040e40112821190f5850207900403041852004050b03130a21341200488075440e01580400482c00c41 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 256382464 1250 256381214 256381219
    0x106030b09090309060d020c0615090a0506090a0c03090c0306020912031608090109080303090a1e050703032303040506041403120402010804021507060c020609030f0f090103021303060506030c 84
    0x80701003000380003020090390798180040350515981d811503024000a0b0203125484100303406141d00780900c08210710544000d00f01c00b40c442e45815034950516004a030300c02c0300c805801050b2800054841c11643d804a0427200c054203000a03a903403507403540c0041545030f4108940c56030f80000c1e80d100380e00d071000001c0c0a1080110040d03180006000041e40e03422510035004000e60340201e14031082d40c0c000e10544010b40282c10071070741c40307107810f04120f59140c1070240c0c1a80d100c07601044900040c6800c4441006003504200104030341441c40d40c003143d40040c00e007145900100344e2801c8005401e200301c01140980d000780c0040401c0d040500300806000f50244001420743c3c010089100c65203440400350b40d102ea02400c0c11003032541d03140049001c20020340ba840c031080c82c00090490400899500c20340e07801845030300301c034180c0e032700d03003002c244d5a01c00c450107a0a00c01052255550303070b9501000919003194189009420001080c0000000141365001164160307203520420440c1d00b0100038a22041d1401c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 256383714 1250 256382464 256382479
    0x1208041713030b060a120b061306050f121023150a09020304150e15010b0307050708090402040305030f0d180206040608151c1e2a0503070e0106030b 65
    0x52074a4070307078084a8440240900502000658182d940364210340040c890f807416020f9030340c024030300111601000c5912a02c129001e041c3c03903901d80507920403038013940d6002d400c04610350011020004032110f110050510782c030034514032507140e20300c40c05000d246807900c020313601c2c881641aa1140210000030f00c4105482a8141e90050719903900d0040b1044071110720700140d9a8556040800e0215402c2100c1042e0b5410544d07400a410300006003281030209080661000f0f0b42c0f640790003403d0348403e803109000a501440748001240040700107140105e0300400040ca8281d4903900c0c1410340d04151008281e400c000700e2500300d403800074010000702c240e000040b04401442c540c0083d405001d0380c041e10080007035034800500c0708444070001c071002035002000c1400c01440640740c058810411390044800400310303c500318042202914100f542035004000509131600640c1c03c0400d60301041070446007126400000500762420300c1500064600980d0100702c48d810090081d0a86142403c0140103041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 256384964 1250 256383714 256383727
    0x1050a0507090b0d1b170f09060a0c0219060c0809010b030a0b0601210c0201060806060307060309021c03020304170d1d0f3003181c12080417 62
    0x1d0008803001540c0b40342a40d203899426188066004000401c07080984480031082c608140350400039160010000d10070f200c2260740e0f80000e4941c130b014162094540c41e2702c8440803075030f003096039001602c1048c00c038070444061802c0040207045a00e00f0f074209507182561a80390030741841d8010740d881d9100c03140000a016580c103003c04640e407681d0124000d81401c2c549808503490740e1080d48081c201d0818040982c0c120b0261100e03407402820310f43c0407500558a445400a152807000c00e00f01d20400004018101c0586401015805415800d4007264400c94500003500c16031030a5050503e0b8500950046450b0350501c900030b01200c01340a021101540101c6942d24010303408004910000c43c41d00c1d42ca8400340e004408100140c0e000301401e64880300101200e03640c0300711070b907085481d1610b400c0e064440d061501101c0d13449220350750311182218426601c8920a0410910180884040038407400d001441520742540b0702d0384440204000403156000d00c0240080d4091807010b1150342c40c0e100d171800c06c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 256386214 1250 256384964 256384967
    0xc030609100b09041a0405160e0a0308120a02070203160302040c080123010e18240a061409100f110615040e07050409051e031603050702040902100207050301050a0507 73
    0x2400041c1803155485e003000842c00d0007168041c514180c0094014040e90802d09240750001c080034101100040030034885008030310b000c01c42d0b04112074000801c40d250085103881c021800800030204c82e001c40e000c114143c01a2010050a0505249402035280003803d48c410130064400c440c1a550030400a107005101c50740d0826044140d02c0c00b0205490304105400c001a54030714503c41c0e4040c0d00c9007000041c0940d03c05070800311445008034071002a9180c0d10000086c0c4401c2c00b0b41503240c0c02c000100b0090010a00510091401012260030b40341003d0109001550b5074062081c00c100182008209040c01504464440c00709040f0402500031450020b003141c9141c0a044890380c070607511f07407000c44071264040c800000504006442400700042d141844c56035030904803840001402841d0190004140108c1030303501030004840302c101c03074100c19103088420740c004c0c01060343e000f59207003018030043e6100c22005009011640107811802c2c6800c040508590005001100e5241854204a44603 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 256387464 1250 256386214 256386217
    0x10504060e040504110a080f121306050f09040f0207140a0b0619030c031a07030e030306010c0204020d090c090c050c1507090b0a05040f170a0b130501050c030609100b 73
    0x340650740043c0d81c0d521070609003001c405100b529070f000031107080c002c52003500104202120207114030484001c0e840b88200000a403054400b02c0030030001c0c1c01024401584101d00030540c405c60491898141010303540010b0440765450651000d10b50f0024040d400c0100940d0b941150401070300142070081c0d030649032200303640c0c80104942d100c0d0108503070301c200303460400e031100c000765400c40b1750220003507200d18114100c0c1c3c2a9401c0c1031040082c0200042c6103078030034001c4090807180500030310b0039070321020b0054070440c40c1c2000481c0d00039000e03c40c0714220005840380c000070038010030b000300300319140140340030898003c0105c05040080400858074180400078400b109406607596400c516651454122034050094000080d540400125240581e07404800b401c00d8401184003040101c6d942e000c264140080d00009000603048200208007040c8980341d2a80d00880d240302e50401d907001c82e5107850850b101190a40204580401440800c1c280854502d034409028540c40e00b4080c10820721102c103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 256388714 1250 256387464 256387487
    0x5090405060d020d12050403050a080408011b0207090c030623040b010509090114060c03070f0201080f090d0f031d03042d0e060d0c0b1209010203010506090103090501090804030b1501050406 83
    0x5040841e036503e0b440c5c600c180100c0e0300071038100c01034610841c618503040e035070b81c3c0c428801c0341015030a1907001c4142840743c05442c9c0512110350000c03d4803a03c1c0031740d080301800403241914203242d1345000009540002002034505404108032042c0d1131040c0e4000c010889401002c16130400030140302c2c1c10207548480c4001810340b0907960010140fa80c2240c0013607403134071900b43c110b0101e001c0422070100b0041a0b0100e1040130313100340c881207520754460018207069402110301085a60010f03005442d41c0307020f2181c80b924803420b8038010031400183d8114144054044001960030340c4005020000c0c4100754401344140703000d561104680c2d240b10089421000c00c28001c550304206002d000c0303001c0d82e8071080119081940324118034005a564020703038543c1c3c1c10005110340780d28004000a00c01344418804c483c1a280300400710340c14418600011001000780d00d03000c8409660302c0e280c120209044902601c001d61043d0000d58180c640b0b184403079540320010491505000041c441804840c0d00840380c10507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 256389964 1250 256388714 256388723
    0xc010c02010e160b030406060504020f071101030203040f120c05070609091508070e1e01060503041407050919200702100201020c030a030b1f0f1b050a0f0302150705090405060d020d 79
    0x88036100e031f04006005102c25884950310500c009291948801d075040540300d400d0007003000e040001280c1c070064050340300446000340544101148034000806400c9030441174040c903c0e1500d41c082c1241e4445180611a800203004104050b00810440e000c81c000d2000d207144840046145a207801031240d9144001e001d2101c090b00407500042c070341c401c1c50304500007a488140b51342000c3d50f541c0401070401d52081d07c045d42d1a622480120010f8640018030390b040700c0c409002e1006569540301d05440b02c0340c258624122140d100c10440301c038110a000804420203041030780d82e03501c03030440c4104014581b0000d08201036900600841c200e02d8030110a50340c406140d4100491101e22810010b061003681c0c00500040302c4001c00320f9040f05611003014884450789440c1c031500c260181916000600d45124000c0096000b240c06d6000141c040c410000c40c0d41c070070f004030f50248045581f00c9880030b8046810800040b03000c500c450f0145024001c0c0344c0c01070004d03a447c194289142c0c02040c0200c1c901c400280 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 256391214 1250 256389964 256389967
    0x603010b0303091f0507060609020909010501050c060103032106150e09010b0a0e061c0b0a1e03021201020c0a0f0203070f0e07180504141e0609180109080c010c02010e160b 75
    0x110136020307a003201c1c580d95000700204640c41d140c040340c1c1e000350032149001d4003030290480081515400340c0d04035091151180002c110580c6199000c4903c03000c03449a41911820600c90f0507803030101402103101800e0000300c42c01e02d904610000078520721034400d940c6c1c41910700100412000603040116150100715140014003a20f0f07400c0807488900c94070403000c0d240008141039660480c080c1d8441d4245240032252448a0b43c1e80300000b00a03414200e4481c03500b03c7c0804070070001131a000c4501d840021040300050306294050a01c03c2c20420100d2055594424000500301145030034407001c4c014240354000c040c1c41071f0409507414444280241000180400c5026050450411011040007000014024400f038100c08070f5040c030111003900c0711694080020002c903200c107407000c100e9109000c0680030b1200b9585020b03645410340d207040d040c90815580d40c40143c0110f01004010f0046504910000c148023100110007400c680d02c1c0284160160801032008502d85c2c43c001c4800200c030200d01502c1e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 256392464 1250 256391214 256391269
    0x3030b0102030415050307020105151305040213290a06080403050a1103160303060e0c03072703060c0f020a150e120d090228090504030c06140603010b030309 69
    0x180e1440c8159000505800c540444c4030b00384c00da01000031803041000d54000c5c095911034485038002038014111080d800709104000c4103080c00c95034001503115000401302c00c1001030f20344500045030291107188203410760269801c800c0d00c0307000090100301c180070b441c42c1e80e00b54540b1000500049025200030108000001c40c1c0c481d00380705c0c40c8810b18890b001425255180600c100a00c019006400110086403d101001461040180c00701d44a107804608141c9181e0302c1c1401280d8100710204a068031340840d2090202d181850b0140001451150310001145000e00c0d1002e02200d00041c001c1045501038001c11001404002c0c03464000b80c0520404246642140180c80c1004081ca5983d540c3d07a5002c0744c2e00c00341601c40c0d009006507034025100d024000c00c066030f0600d0031640f500e40741400d14440038001c019008440d400550311a000b840c00341c401c1d0400c0d6030b8003c15031701400712501c00d15490805010240c6400c1c4151404060f085005518101802021440186030b94481482480d441503d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 256393714 1250 256392464 256392467
    0x1080709021c0509010e0d0c0b0705030603070f0e0a050f040201090b0f0c06161107140105070f0803040f0507050d0f08030a1d070603050105040204051e0102010204050a090203151c03030b01 83
    0xa0000b860091800380400d140084000e4001c3c0703004a4907080318815160015074140c080c030201c0c24122380003000b510255803501e0041d21281e0004d04550b415204241c40014000401e03200c030b80190070150410b0120381000e1060b107054800181400081c100e482090100503a0071103510380c100c500c00050107450b02440b04c0361828500880007800b11030300410041100d0b034501c00e0703040405100d40b6240d06060150b1582203c1c5c0e01c90650040b40c104c441d03000024903056004001914203c1c1c03003003202c00140300607992801480d03082681c044658014030342803d07003000010f001d82e030b010740305c1502d802c156002c0d181c661510000b031010001d05285000004501210a030703070044080d04c180743c440c60b030109410348600c594446542c810703100000c0c541000847d041c0303032a008580c100e5000912282440221002c10080e400450401a0566508000c0020700d40c0369601d500c8001d0081550050f241d06d04108a800e2240c500341c500d0b8829841024402d000886111203450f44d260140360004290141100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 256394964 1250 256393714 256393747
    0x5030a0b04080c030d0f110a0f0e131407110f03040b0c03070c0e150405010f0315061701020d0b03070501170709090504060603031106010b0a0e0105190203031e0108070902 75
    0x1103030f5100c2c2c040001c022011074007542000800d007066410030060380e403000c01420042c0c051017900318001450034140c600001c0c0f00d45040e40009100400d401164a00303401440e08541c00b0425820080c0c21140400c180a9003101003000106030810184c44010b6481104640301d228a00804641d600c3c08a40280020810015541c040d45c1c4410742c42ca4013902e0f01a0012081c4084424030755440400a40b040039040034003d0307a040703c5034003082c1d03148142150b5544041034a80311014840951f00c800c0001c8074400e021070414902074980006a0391030300301e1507070400d485014224030300030b070b128010401060340d200c00b55150760402c5594840c1c080d22490001c507500c04455200558107401c0500f40010f1090383e038080c0d811a803003615a00040c80765030701c1c010785a403804d1050301c81900091040808003030107010310054a90051508500d041c40e600500c0003c0b03007945080d88016400481003144010302000002e021852444041340036626000e14107550300b6950140c0c14643d0780118010300e2544c107401c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 256396214 1250 256394964 256394977
    0x427051909150f05011a0702100e04022101051206060a09020f040b21010602060f0f0604060f03060e010e030f09010f030b180912090105040302040e15090606010f0905030a0b0408 78
    0xb01d092200001c41c80612001c0d180a01509266400d8540724611402c0e090381203400080e80a070020882080224080d200420310b040f05c0c80c4c2158003088005514038882d1030351400c52560090588140d4180f009100d1080c0005006503d0f581c4030301c2c1448090340d83c0500303041c103c8401c0f80380545c2d540f4400e80084940d010715401050304443c04240e41c03402403800242210014003103c0b1003091682ea0301412661034900303036581034040110b50085404003024840041e0b01c4000907001084143d50342e00500041d40690b4401e0341c0103a80c5407800e10051500380507242c40304c0b10b8280114144a50300522810601c9410720060502014010240016000e904080149070000340317040c4c14284e1003807102c889884111500e4000380581c003841140c030129081614810b02c41a51131a09140c11a424400181708503000d20107148100c101006a400040d2210b42c803841c9418080c0160307041040024004081001c40130084c0310120005016076100003403400031041d00103000004507255420424054070850 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 256397464 1250 256396214 256396253
    0x201020a08040602061b070f02012d050c012003010e09120c010e06010605130302150d02070507030c060806280510090513020301030b061e060427051909 67
    0x105002800130b40200d03506219140c482c07080340f0210000c1d490003d20384075141700140039002d40560480036500c6500b003104805142e003c103204040d5903402c1c80e8441740400740d000001610001d081c00142e0400e000c2c408070744020040000c60403501d0f004281280c0414001c681c1c40411520002d12000001c11100120012300300c1003542d60010716079200e002e42802c1d9030007a850702c100000041e4840c070660483d5102503810078800101ca045508001144011101c3e14410b200d0501c202241c0103060b20050038414030650041c1030305031035458402d04040403a1311040c1403144050800c0510340751035020a0324151242c020342c1d601a008040d034840407446801070f580048100003100c4119802c492590261203045880000c05040032106205030b2009000040440c41c1000100d51703e41803484103403004000d8611000c030b01c2d441084c08a017003900154440c0d440c901c0e250700504c0481c9030841ca0400e001c00460f40511642c6040e000041c0c40000c00c5400c404501d136a0320350740d000c1c4100c8003134200d2030f440c0c038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 256398714 1250 256397464 256397467
    0x150209090408030a14060f0d08070507060c05070905040803040b060409051213080109080706231017030a080402011404050406090510080a12030b0a1206060e1e130201020a08 76
    0x290030501c2e81c1da04200c0b9440015450700d01207900203091a04a1131203144002c0058804d000320006005240200c02402c460400041c09000b000842c1800444050002545e1380303603548015084c590f00d844403e40c04000511702e0003080c800414000811264481d4203c91010740704c0e12034501060051100000240142c02000c4c040070440140100402003003404103007040d6510f0f11384410900329129442c2c028a008030404c00741c00050010b41000044021a80c15001c940181c1842d141140504076290210801d080c10b01340b152540d00c00590b03045e01e000b00003d40c207203500d10102400ea0200540060306001d100c4140304032458020044801400c0c0c00781c02408555941c00e1060060101a2165201145070560210306a040014001c880981044090190a201c403000360001c100d00c460b1603802111608011504454044a02220910440002503664581f0a1003a05084050042840c0b00304611011030060846d8481070f0308812031a00c00010b10400e80300513440c14101d1803004022090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 256399964 1250 256398714 256398721
    0x5060d0b130c020303130804080304060915090b09040906020f0d0209040e0c061e1905070605060109050a03030e1c050f0c1009060806190909030e03010b030a15020909 73
    0x10180c0003404032100a0321030424030300e0071800d00c00c20354004400340700059205000240300e6045880482e2200e03070042035500c0c41e15450759601411a030068000c4008603c0e4600200081208405204d24544a51809100070350904065030701c948244541144a19190b883c108180240381c0e0481e0b80186d40c0d10000c0d40d440b034000d45004080e401c6080050300c03544c6485125103032240046990540103100400643c5851404801100b84102c0072040008100c0c0600c0714001000e07500c88076980100c51030319601d45944182c5845419244d00400d4941041702410b420406504c84031403400c1541e0381030403c01000070005010a00490404040075020300c0766010160a00c0700216200d54405449425244c60380000014440003914494140b0001601a002000418454442c0c2c1b908100014505c0d80e10066200d00d2000c5540903401c55600d4a944d0b2600d0820150007002d01600d490041e0000d01c0206a10400242ca80c094400301400d080c000e4490030600400c99070444100c02c1300181030310203d04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 256401214 1250 256399964 256399987
    0xa050c010f05241212031810020705010516120e101401061106101205160b130503010b0d0b0403140301090218040b151c0515012c010e0a0506 62
    0x2032416400800c451414210203a82c2000100c00d05200b1040b0f00400118141900c404400d0740010301441118540051f0710380d07507010503c1055112041a000035840b84c42c4d0741066800c540b8040c2c43e900004070a400e010783c401da0002002c0011075050980050140c40d800e44450070041c0311030000d0f000c1851b00e0002d041403503046a0f65410303100c0c2981d950000407521804565918820380710315500c941807d200308050b400c0000c4c81103000b4410003d5442e4480030202c041410101900000b2110201080c4104a0b01c1d10342c1c400c070024281280240005061030000c101c0d0b11040c94006405101c0c44400135041c14040c0b180910b11f442106050f55496940b000b40d40000d4200303140389825000d080030702c0b2042d0314050088802e10320008004a0ba8018003242c842c2d45680401d486103c400170b44144012034813440c1c401e152281031500f020f4a5201c1c030f10320006100703001045003a00c0c2900144141c01c0c540380384c82181940e81c542030820310100141e100000e80801f00c0c645c88143e00c040006103107850701 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 256402464 1250 256401214 256401241
    0x131802040305190f06021b0303182439090a0506071a090f031201030b0106020d0f0f021e1e01110706050a02040e070924050a050c010f05 60
    0x200c2c05282983c41d00180f10581d1000c80780e030140040c0600c111241d02c40d003c980746900400c503400341d25040d409404000703911141542c06c11100007001c040751042e1b111103500b003440808450041c02c49007445c610703402d1031800c0d84e0300d50107051440083c00070041800007844240140c3e00b040641c3ca01149410b0b0f02044022060f801103858500400c001e98000640d810140240c5410341d40c483c503180043e02c002c4c1980801000300400ca90520301c1006441c0a0b00c00e030910040a5084014000413901c0d81541091040c070b4806071300440440d48060b24800e03856901000c1420040c48600d068bc11101d00458221324050061903004881004a54080461400060b98681e41919a4000981a111079940d1400c8032030030a01c41454080c100209000600b55502040e4841c10950005003020740b0b030710307040003c031000701c1c2c0000114000041c244150889217061200511840b40b40d503094072542840245180103038110f25052000c003141d624401c0000f0f401181c041a0307414410032507071418030b540100d00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 256403714 1250 256402464 256402469
    0x1605030f07050d03020f1204050c09090109060b060a0504051903170c010c030603030e0f0a081603031206210501020d050a0209040e010b0907200f0a02090a050906010501030213180204 80
    0x1601c981da90f4119900c0c080e000f0b94140100c008881800e080f0300c404203410b80c0078000c100b203415000d4503480030b0880e41d80c501124010b61240d400000c42140030b15207001280d0030030850310300c5000240440d445140d0f0000845090382d50a603600004100501031000c1c1005194100600f801003000d550040d105000c1d014081c4a20800000c0c4041186900c0540446541c0d00010340003038001d1030040c189003040010802c100300c0c05031110071816a80c00c40750f410201068210340190039913031800c1043c5030340503440d0800700414038000c004252622080380c2c52054088001107004842000100c10b1140c03e41c152503110a40307160130310151600b2000d48001f903100740c48542c4254070b089a04100200140b064040c0f01401901c016200d03250541c0c2914036101a01142d4103081076032210490707651041c0003000c0f500c0c401c5001010001c0142c4100028010000c010301007061600d0200715032142c0000d8542e044520070309005a6031507110300c00f4000035032950001744004c5e080103118900c6040c1980107104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 256404964 1250 256403714 256403723
    0x1323030307031802090f130507031202150112060903030207080a0201150b180906040b1806091605070308060a1a07021201020f03190b100509040f020903121605030f07 73
    0xc1d90f205050145182e0074a000a504400e00f0300006107000580320401d600002d41d03050b6002c3c04003490fa0fa075850015660030880d64081c030305520003042034042010040d61060300c0c004907808d41c141100104410304904002d01100d0b1102d44500505000703504898005400410440d41c404032680042d000e002c40410071000300401d6000003500c500d04000340c501041044010030000c040400c02c110001c070001c0d00c043c0d030184d0b480b028408585c2c2c880305451919240386084800e5481d00d1010480c1080b40140600d034603052005603601c0e43e1342e108044542440d41414042810f80312000801c42d103c4181c1c1104030781c0e504226a070800c1480020250108510881340d00344101e800200541c01e0b400360348014440e0300030030301c00b01f00700300034041c0c00854440751120002405110b01c00012421203010030400042500001c05000b982864020450b40b0340c0c00c2c8000b98a462080f6012950758800c400120408503808907150030f024200d5140740b04116000000c8a880b00a103004a2401da80101d40c204c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 256406214 1250 256404964 256404971
    0x2702090a1512050c0a23130e060a0b0702010c06060503010e0f0c030d091a0c19020f041a040902030307060e010e07170601030b04210504050f0603010e132303030703 72
    0x1885804180036032881015900c040508080d032101e411b0f681c60000c80391807042d018041c82d1124110700f102026148404203042000703542850017420290100300941401e01405e4401c0c0284051780c0500c0488250582c2841c0c8007035552400d0420b0030081c16035030019a415404c0a80214a680c400604040b1001103602a500c0c031038108030415641d80200500100407866240c810012405030100040c1c556000e04015031410140524944c1042a21005032940403107089141080d400c000e0102100404240c034100103801900701141d103403941f480e0b0b00c20701c0340c0c0d210303c56002152018010341d0950b0707030300800502c14a00e15040c142d02030520b101c0d07da155442251030000d8000c0381a84601c1d1594500c00c0070301156401e40d100e1300105500184107403641a680b21403001c500030140210602e5070101ea9130b05440b0360801c820003012180c555a094400d02d0144014020980100b0003590045001c102980c00c0280350728001020000c024503a4101e81c0c0344024003138680304003100452007501960742c04c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 256407464 1250 256406214 256406237
    0x5061e0918070f090315020304080705240702010207032307020613031707030801030602280f0212092209050610030c050402280207180207050d02072702090a15 70
    0x4840c1e04c1c205100103000c00c0079240542c062035003a81e000355042801529001c2c601105900da0500d05613040604441003001070002002009510000d03540128941c4020761600c81c41e503d00034544d80309030030001d0400714010b4100d00880050011201101d50152100c1c2d11110300c41c10404e0580b2042c84180c030190a14030102c890381e0001c001b140c02d0a6170548074101e0b681d003552500340094100c2c1e012164205440f40c15500e00004101400b0004000c0c0d56482241c809a540001d00340354100c0316620b80800300380701501050783d440242c1140a02a00c440c1140c0c00c4020280e540909200ca4002c0c209016900c24013801c54040c000f46001d6134011a01c01498640d07d8041c80200d108059556881001000c2901240100d81c0c4802454217020700c11103000c0c0380c40b469503050110742d50280e00c003003d500089440800c4400c0c040104c0a06542c00603240c51450010305080c651056910b2011303201d81c2c1030b14101404440d6055800c003d03405400c0001d030031380303071103c001c030412094551b14023080c201240c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 256408714 1250 256407464 256407467
    0xf06060411040303022e020403241514030a0602030c04140d020604060503272805071806120606052d100905060c0a030801080705061e0918070f 63
    0x2c8808aa516900401e540c41003584200010f11402c0010010710441c1007928210510341d0000c2c0c40918082c0440ca618032942c50034080c51001e84000f040902c504080e0b0000700c010301c004c00d640c00c85001001c0c03200301d010b10702c2c006420b2000c6c0d00002890310b8404810301c0044141c29001d0002e0307580e06442c0b524550305040c01c20102040f00200254032100400062240034407a101541d00311440383d090303004640980c3c0180c68900884440300c6500d43c4409140b40100120200d451502101004080f00021040d01c8441c0c45900c43e00070413006030540360600300c8a10040d44108001e041101e0b00b51941c1a03940f0b4580c3c0504141d2040d5442041c04030411800300e03415800c0114204000360308803003400070020910070059000d21500c02070050082000070903071200c00051501002030006800300310071034070700985403c1060b001404d02d40e010800c140910380362034048a44031304134413107178103104100d5410705811803040391940794114420100041c1d0b0301203c508818003803009605e4008861801500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 256409964 1250 256408714 256408717
    0x61506090b04060509040207020d0521090d02010e01020a0c031101110607020a110a0906030c0f0e090a150e1617030915161403040e011a0306010e120f06060411 70
    0x40d1100001d401c2004120380c6014078020210140064409402e204040d00001e82414031224140d44030707040070300140c2e07a52800030510b0400c00c0d4101d4a0a04010f65240814040c8401030300081c103209009400d031000340e000b044400005503001303402501c0151240b51a500702003101403058003190607030280708030107507010484910400c940d50041101c4625512a6103030ba011a8600f90b402540414011a100b1035500664003d18003500450315010300d04281c101c00b0500d158080008480b03420141b00005070042960340e666030300301003040d0103007015880b6540144040c0342d048944c1d100e50720070784120181c1801900b0407900da1201c403415022100c502c0f0b036101d200c0e0f804140e9011301100ea240308030210041c007030841c0c043d184a2030030108107166685d2401d0510216a03138a140d001003420045204c090200c24050076021407019800c0600340e035071288030300001c1c02003418000110f1561405840d80d140301c2083e030205404540d08404022081e80e160141540c1d40c2d401b40303052040c035410300340c0c5140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 256411214 1250 256409964 256409969
    0xe0d020a1205030708130212030a0513060504080d0810050907020a11090601020a0209040503160f150b0916140a03090b0603031612050403060f0516030608061306020d02040306150609 80
    0x11038042171903a43e142012002040c40d18201c3c2d1060010807003c06507581003001d0000700400341ca41c1595030400d242800c0e104880c0317034040000c03c14100030170701401c02c0c085450701e174100460034881c0141e201c1c843d195007204040d802854000c8501310400055641c00900c1240c0b81e806041204e0043c05602d06005400c00c040301e510f405640020484001401d1048a0b980e000e80039000b520304080d4201c40042c0c82c501061015181c001540c080301c414407041500402600c40320304010020700d410a1b0124080c0c980040510701e41c1480c0b004110065806050142440c240154100760b84681104002d0000d188005050f01d88445001c001100350070000200c482c1e903282c1074260f40c1c006800c0e5444103048034a000440c0204807050000100181050144000b4101c0c08900481c0b5031500200c01005142003101103c10903042407010400c5d1075010411a03007048200080d1040101e1608207000688204a141620030340b0004000040c0011944a5035102070507001000130b41e41d5441d0304031007072507103030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 256412464 1250 256411214 256411217
    0x10602070501110a060614030d0e0a14061201030308100503070302061803070803040e0106080a051b0904061d040b310f0203010509010b09090a051207060e0d020a12050307 75
    0x150418051580148401142580000304640c001c42c2940ea0304d4051b90b100f40d20008030348500c9103a1401d01d207410b0103a1503000600e490000c18030b098070b10000c1d48010280c499440171507002c4407018803907100c0c03004403400c10000428041c0f46580d02d10300241000c004549000c070f901600c1401040500d0041800f40c1125001050a420501c841900c5150104074019003581442103050000f500c08061020300000d02a070000b0341d43c41d40c58450040c01441c0001c15a42032545010204461150b81400f0103146100340107000b03880300f400320301040041015800180c0300000c622040400f1101300f8541500c501d20403000c11340940c4956105010310324412540c0840c0041d02c00c1c0c406980a08503941c810090b0040074203e0040c2c2e080d4021030b0842c0c0703042c0da115607181d445800304a920b0414038100c5800110580090420352902c2d142d143e2120342c07410800e5440300c00081c02c0410300149400080655030701c1800c2c0c0e090016006c0c00a5500d4500540864a00c40707004061101c0d2405a001e0360320070b2146 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 256413714 1250 256412464 256412473
    0xa0203070504111b150601031803030509161811070c0b090f100522050a0b0306150a0503041217130302011d150a1104170705060a090603050f010602 65
    0x1e00c000c00c409403030080010f6100b660107005400c0101c2ca0b031101c88000713a500f080940260444400100d8501030300030981c0341070505280c0ca0100b40d643d450b1000c01c1d010781510f0001299202c0003030032810005480781c05214070302c0c42c01c0045050301050342d03015500c11980b00204094101003402d00064022a0409002041c1042d4100100e005c114018424090024003180508d04160b0014545150450b181c200040001c9400d00180590032030324002da031240f4000701181c0f0700e41390001d940c9803c035010b054181840480890307019115902c07141488941c0d451056180c010640b001442a001210140c51139000c0529128540b801210400c250801420480c07500380c1c0d58213040081d0161402c1d04508541d40c07a1001c0505a0503448884c034101d1184000d080c4a04101440d40c14802c0c002d06a020f8080c5410954000131035000111021a1028000c8500006080600c40d051007841c1e480103400590020302e00050503407241141064440070b03101080561260600c2c1c41d5010b40034021280560310 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 256414964 1250 256413714 256413719
    0x1e06060e130c02120c0a0c1202040b0a030209061003110a0315171908090d05030d0f0203130201030e0a060509010501090e19021e0414070219050601030b0a0603080a0e120a020307 78
    0x203044c2c00070400d0f5102c000c01c80380c0e000415500d4040700d080f103502801c0302e402d0410441c0c04500d030a0181c8800003108407800300f1b540d03040da0002201d010020740900e1103005102a006002d07404be801c603003120246600c00c1e40d2100281000075001e8034581a026422880902d40800c090881020700c80381030101e880240f91407800011a62031320002181c058483d024248070b9031005a03241c02c2400701440c42040596201d038200c200c1c880030348101d000f00011450061080051940c210790203500001d4091801150341800c80200034103065908030058841c074200001c01c900c2c1ba405422450480e8a03080c0304004200f049004991181c12001801c0140c2c8800c4105802502d4940588090a2a000382201e003000071000010102c1e44540124900d4414100c01c1068254050000c0c08481044101c080720009017551004e40b200030501005118011b0b00012441000c280e0348050301843d8070146c060743c0c0e113002c0d410240c010044400718502c40d00f0f00601c2640b440b04007050a004841d4080c005241290 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 256416214 1250 256414964 256414993
    0x15060f0503071b0c030318031707021c0f02030c06070b0712060906030b01030203060717160201090803010905040209010501021c0302070609050d05120c090904061e06060e130c02 78
    0x5001a103142d04100d24040108400141116101c440c1407041c40105040c51031490041c11445011a4080c0050307048403042010a4240b06100c50030f69041c40c505035161070b02c0c40080c1c4507510811a1102116034003561800700103020b101480828000c0301221440c2a000d03040000324811401c00078800c4c044000480da1650041c006d022000360305120100d0826110b610580031a1102c0d03000303030350400410b4010000d6040900c4003e0b0843e07401c2c07803e44d000040304030702900810b0001c0c0c03c0c202144200010040303040d200390300c1080c0342c41d40080e1700c030f03520b5a58048003000780100340c4059105001c110300004030366000250380c82a495144080391030744080240160001d4110034416111603480c0c1e03101ea8001981404101190500d548070b694840020446000750304d14014901040e01104000141c5150344409101da401580302e0720114261084001c0705c0300244400903041c4025041900210b14550400030f10f888031a01503417031098046580b00b03a1425541a400d07114090f80003181e03034441c0503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 256417464 1250 256416214 256416217
    0x120b0604062301090506030702071e0803090d080d05040606081005070801090c170414070b090105030402040f090b0c0904150f0312021e01020a090e071205180105010905070315060f05 80
    0x40c405051135184c650b035031004241c165000b1104000142c102c503405100c0d8284480b03400302810542059407040b02d090910241d07980c840e45296a00c02d000f00901001000050802c66503404030515060005040503c1c0c040d0141c44980207801b480c3c021441e2001440c0000c0c4603051254401ea640c80f140c0b81d20340300d503440c01821280038500030440c0c090b410382a059440f0800f0741c001c0e03110700b2104405d01307002400a41000d04a0308442140c00d810003c41c40940c2c1d004040c7c0c0d8000d038040307800081031448022048001c00c00c0c000d0080050b45030004010740d0500110103001810780c1920300340002a031000d02640d4402050080340d15424000c0002d10129445000381485d443c401d00484401298001e8401501c411175600c3c8051a9000660512040d50182d0508020910b100c003081c414104008041d04070000d0030480750a95036110001030f56020103044250640c0d660070000c010a50711084070501038801121900040782c03c0020055043d80c9488890b0202c1c0d00954948805035801c030400c0300c5a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 256418714 1250 256417464 256417529
    0x5071709010906090b182407030b1806040f060e010306020f09060c010618050403171b040308030402090610080705070201050d1a1201021e0d1401120b060406 69
    0x181d03598404080c0003401c5445000d920354001d920682440c90110f1800314600d260241c821103580041e21045581d490300380404c2407088402011a07150342da40c4100b10000e02101e16019803003013025a0340c181e400781c06420f03107000d41002d035428048035408000d00e109494852045241401100d0010008034030250b02618164401e1440b40e89007104007000500260851001c1d0402a50755040800c41c641c1011f41081c810a808a0107000c1864281c40103090801c140c44c0c0314020180c0d000010741078440c03540e5280709040d0318500300c1c5d03101c0e0340300e0500040b5608200d400324000d2401c08081051850300d440038110300c4940e680c03004503a07903035179800312a81d401480040341840f00038000d03001c500c3c00600500325614807000b080340c604040340d000c2040c02006054807008691041180143c1e245513900110203160594250703d548020318031024004040320360030a01c41007100d10000c03400c03000300c00c2d0441c400c0780a100e5510441d00c0392070800013115440d100381c240401410700380304403000d91445800c5a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 256419964 1250 256418714 256418731
    0x50c0309090405030406091e051c0c0b0c160f0506071406040f150b010e12072402070b0909071b0b04060c110604080f031012061e050717 60
    0x5004024000c03071074802041d60212100d42000c40d00b417042640c0011603900130058440700c211542c0e0320180c000650041401124012441a0013000e440c4800701c00c5481c1f610340c007d8000d0700702c82e911004821150800c407400d00030b81c0142c00d105c1c520702c6d80460300b13081a2402010034902541c505002c010250b4000300c01111032203031440c100e9189031002c1c00518421801540216200038007072601c20791794420315401c035a60130b01d801c02c00211640d214085503407042c41511000d5140b03203031207149031038030403140d000d443c40c00c40403041009603405c0c4400004001c441502122405030700c8078514541c6c0d0090390402c6400401e1400052450b0b03101d2080310740015124242203098502c1e54903900b032441000c55041c1c0d055500c1d801ca00440941c02240004c903840032501402d05402c266403045428880c0c505644040302010020402c54034191304003400030b040440c040d0720400000d02d04407001e031101074111405180c0b50554400c4100c0c0900825120315243d40d42d12001d88400110526091009015000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 256421214 1250 256419964 256419967
    0x150302031b0d1506090f02032401020c040f0c090e010305190201030e0303041109060616080703180314010507173405040906060c080a0507050c0a180e0d0c03050c03 72
    0x1002c00c3c8a50f03071400302505041000701e071031800c0c05007510030740e0b11351070740c04144038410010041800d4515861030f10103145503003006e81d00000701c03004074a000410501c459000b460701c021804400e609a0242335441140d4450501d641d40d14440040504002d12004d00103410011000c042201c034491030068080c814100068020100d0501c1c601c0c541088608441c5802da206001104cc40c000e040680d00c410210303052031901c84004000e09518180c0080188600030115000d01010301a5448623241c801c005059030349681e5a0500341180513660302c0b1050b45d9486d000205a10a109000e8078045180c0d462071010191204146104042400c005607529002c103609905000c8d82c0d6006444108d4010b0390300c5c01e450301e003003005d0f07003040341c8842c0e21a01c14407240c0404100040c10210646010410700e05046c1e80754042d50511500701004814642d62004070f2a0000c00c1c151030300200e4951401a88204002e003800c048081d0390303920a480c0c460800b04007030083c6000024401d10040891000040940e03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 256422464 1250 256421214 256421239
    0x1050a081b04140307090b03030f030c0c12030718051806030a080c0a060e0703170706060302030304032d02030c041d01061214120d020703051b010f150302031b 70
    0x400389a0010b0b004060f403000483c041d950307180b90811104d070181400e500304104540200000039030301c1c4100c00c4005680400800050b059100070810f407001444030a0549483c3c501c80040c0d1000d5074000c44000002c07400203045051b0f03851145690100343c400242c21261103900f984559694010300078801c83d494401c1914240c00160618054103040d040b403401041102028541001640c05921070848581d02c0350343d0400c04501c407030400440031003000d0180c0e95156100d0520101614041c5c2029405100002c0d00004000c0a03c00900da0f02035151246285801d804446400c0310010110195040d1303c0200a0700d41454654444004600c1f2000c00742c40b5001500151429150240e1118841e69054410030090007104001041c0130742201c800380100c0300d002e012542c002e02609502064040c0d0114010003018055002c550105100803003840c00490121141d60103040241801205142840710a66403094054420425a503004005c3c107080415103890503090144003880680c40880341c0250f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 256423714 1250 256422464 256422511
    0x10302031009261c060f0806100902031e0907210309060f050702041b170f041209050301090b0412050a17040606030b04031101050114011e1809060f120201050a08 71
    0x180c4c2100c1200c03d0010451500e40900c0182d015202d9200c510107400120400c00c40c141d00014200907509e003000016241d455078025070038021000603c1c0c00c91801d5140622041c0c07800007500c0d10464002d440340b1050701406900901c004d15200e00001c1c0401e0f00710100f440001c2c020221080c1c540790300c0c13600d9030611425400103001d44942141c885100702140000d10080f1341e11081c400070306d0000d4100070b2500c2c100020b140300b102c8402480980002043c1045449080c40f03181d4010041000400030312001000c0d00300b10281c1f0714250750481d842215210035450399801803007a0362110619881c0c0f03500049441070006211900100304031405980c079080070002401c41c030540d60003140256180030504142c404d084c0d007103c074181c00c11044800b541300041c03110b84e440b565211a800902da244082004211000c0d01c1400007100180d4420720044800b2138060f00c5a0300410448010b040e9902d0035075501d80c16028500c5140360040c0c0015010000742c1c00050013580f649411000b416247c10590f88124030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 256424964 1250 256423714 256423747
    0x190c091d0403260105040b010e0a0b28081602060c0403020d0809220b03010506090106111203070e0a05041103040803040503040803030a0c260720030703030501030203100926 76
    0x21038000300c21444018000d501b8148074030804c041c3e007070802d10440035640c3e00007051484240b044101010000a06030b089500760040da00300781d04005050010250b0350038010340584404c070b1b100d1801c0c01090b84c81c3c00c005440000d50707502488100c1401e624050a41c1c0074041310b004030321416620003908102900c0706803103000190f6282c107060541ca8030107200340c0d01140305840300141c40ca0300c40c0e8108014043c40c0d030780e07480380d45044684500300180706804884e1010708048001021060000c4044108000d050704460716640c0b400781103950710406a19078040004031000b003030100c80124024000a400038085400450700903008000300c030309103a9640c18107441e590080342d502d100f40d51a5090116038070303040003101002072003c4100c4950030320323202d0303030f0100041006004400304406810300c4640d00e1407200c0700209605403001581e0703503050303142000b4020b000c0c00c0c441240607200303102141c07149940d14407405980716840202011044011440e5540300c882d507a20810903071500b0010320003411301020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 256426214 1250 256424964 256425017
    0x151401020a0c06082d1302040902100203130f0e06010f0203070c0303031e0e1b010e03060a05090c010207080307080a090e1303020f0a081905040509190c091d0403 71
    0x107a584800d881c0a0720061182401c1c038070b20712440c01220117541071600c60b55540d544d22620840549080c3d203d0350000601819201c0000794010310500c9a0349515a8080300a0105008512400d5042540c80c2c25840410005c2c2c882c000c40c01408401040480d845035040c0c0300c0d500c038148120707400c2c08000c3c0c5038540050240e500c102c000c40d80c0c1e03001c2c0642080410300400510301c1c0c001c80410060315100b0800780c5620b204600e02d007051401047c8091640c1c003a407200811081c000d01125035900c0d2840038040246001e55501c41c0c41d12a500751424107600c0010001d095a60010103542000b05e999680c000c0ca40100603400240400d40f8004100402881d50842c400c60f145580d501011030035003406800d0814429203400260000c046010100c0c4144045803017561069121004e0011203400c1240c031030040e41c000c01e600138051800d00c1910100c0d203100340400c00880e04200200d03003603000c064454122505c55041d130060950000120400c00146059106d0f010f8281007040700a805803210281c82c684 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 256427464 1250 256426214 256426217
    0x30d0207110103060605090d080c0a03020c120c0112020a0201020d11120901110906070602070f0812010b03040b01091e0609020a1206050a0308181905010f03151401020a0c06 76
    0x2094140c144030541104001050080c24100401801c0001c010300c28441c10012500940c1c010454a003040508000c445112050006851000000723140c001d40740e51060854070f1049402850590703140d6808925800783d1340f030507183c0a01148417034102c4d4001e034201c851100155503080c0080903071801103004d43c808070b0084000b2203546032200702500040903000740c41105c0e142e150920030140003603070700112040c9800440316262500503a01c0c10030701910410000500d980c19070043c041c100f200e0720003d040f01c0c483e260080c100070b0f83c0301c04112105c0e010444028080c4d031020001000f803182c040c2d003c070100c24640e80310801d840030a03040c01c4090701c449501c50074205a0000e80341680341d9100c1a078010b19030f2801018850186004005810358040d80005070040354001040c1e002486034400f07440812002500082400c542450300810001141c41a0360204285a8140041d01d22034810502100750500c42202814104000401040c1740c80c800300e4158401c14030310401180d09080d04038000c2c81c05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 256428714 1250 256427464 256427467
    0xf0c020d20010504080c10060614070206070602041d070f080402010518031e0f070f1403070321030e06091b03160b0c010b10020d030209040204051207151107140103060305030d02 78
    0x10341307911850800007c00c003841c45858088180503080d07002502d480e1074041501c00b81d031201e8560000600d2441003a40081001d84001000200c42f14202c0c02a801d41c0740000c0b50210300c1d0307903248054a0a289500d890800a90460000b60040d805038002c0c01b940c2d040071858130340c9080d112000c00c2c44d000c4002500301d10f00d035105004441400080011000040c140340280160620b00509041c890a50b406450132100b001a585207540e1001c001e4178004680281d41805000d10214091070703030408002d06080081d00f4600000f030f100c04000740c0c060280b103098005250010040b840243c42801c2d5080c81d03945809503c048859030324070344001801401c0d4002c8410b82d00c20100c518142100c841000d004e0043e108851a00c40e45a00440c00390080b50700e5042c0075a03a034180c40b000a000f446260000b503440915000a102d210030300051607001d640c03806500002c01441841d00751240d66119560303a0050b40302c240e0a001030a01c07190074589401c4181000310701c42d9141d55419046800081e44444503990 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 256429964 1250 256428714 256428727
    0x9140109020306070309084f050a2303010f0903170f090312060607080403080a02011d03090f1f3212040f05030f070201030f0c020d2001050408 63
    0x4007404102d0300010217040400c145145580c0380351060240a51a080c20f122490856041112041500040c000070500b055074003c011190a010616400344002c030f2044c40d8800401c260030444000429140940282000301030380725072030452050191035454255407138003040d00d0721030103500842240f030f40700e612124903500f131002e13220905000041001d42940c180710103004600038084100c0d4404101c0011503002583e640d03012803406d00c1500001850303040001000000d0004030f00c06030101004d01e030b00034800f00201c03000f40509554058901101034004200c00061361500d40300300c4008030006002a0103107110180009662200341510030b000c9100660340a051311010104590100c2c410342d00003440d203109007400049802006401d91459a950740803400344844003c200000c5c03580907017100e80d154400003410085030070408040340070a0824004120600303003030040d8480e0100c55401026480c07411001105c1c0c8102001003400303401124160080d035006c0a004580c8140e0051b05655603034071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 256431214 1250 256429964 256429969
    0x801120f020a180e01050f043003020403150b0604050103090c05040207050c2d0103051332070b0706020a0507050a030507021203070b010e060a0e0109050402010f0c11130914010902 79
    0xc4c240c1300110b070b1591406080203c3c3d111000d00d01900950440c1c203915401360084c0100000041c0c0742260310054000501003e03c05600d0b40040040c2c0b4464514040394000c2116110141d6198095555110300140003d201035407199100c4010b050040302c50341d0780f40e035444003c02c04907400807409480582004500502c50308100c1d0f1144000400b00000300000b5034104070260082c4209000f041c10176840380701290b422040b00140c1292180c202c2001c4800080309103d03d559074094018084c056107070701c1c12041926001242e20f1080b40e4514035031030320308800780e65031000960000013110306010b410b200590108508100940041c0d100b515030564600e46401005558182290301c0303040d40c0c0c010404800003034401c1c0341c280d045a15040344140582c480e100000c07801101500581007000c21040005091034090b040030340214000c0e02e8203a00c200313081e81d04454190035600041d02c400304803400c21280742400c0b138080c80030001d2008005a600e1517036032148101d80c80c51a001c00c050307454410000a52 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 256432464 1250 256431214 256431221
    0xb0a091e1e06060c0b0c0715050718140d1101020307081c0b0a081c200601030b0a050f0708041502070f03080a18020108060d0516180b010801120f020a18 67
    0xd1510303080c9134140107290354410038400030007800340e08840000300b00c0c1c100704040105016854401200c0500c480e01e8002c0000b02242000691503219001d03101e400500401d0341c0d01030000243c80501402d0340d04c40c0b29101d0340401001190300364118801040200b0108180d14003811405140200340d801c01c0c030324502000c0c1529160074200d445401c500804100d5000006116145503613084140303828020900d5003a100c28006241130030f4184031160f0205010800410818140c910546a840064540d0142003003112021200c280c68035402c040400da22a00441810b9800342c4100d014001d0542070701000c10680c0c1020800703e03861098a107100c0c0c109a001a80198051008142001140300c0310004601c0c803042c045000e41403000540228616407154410422025000001c0781c16140442014407000d00c014800c2009560142c81e01014104c180c0c014401e9204050751140c0542c0d00300410701584003900c05e821203050501da00080016101c511041340202407115122030342d050a20125000e5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 256433714 1250 256432464 256432469
    0x10804021c1a0c0a0e010e04060f09060801110703231306110c10020304060507030504090e1c08060a0e07031d0102090a0e06090c1b0106080d11010b0a091e1e06 70
    0x1403841448004c000c154800c00c500f60040742480c00480e11f040d90804a0020243c940100121425001d0042036402007504842d01300c1d98124000c0110300700e240d240d0460350184260040010b10800d185801c4c60624071340030038180c0b1a0050983c44c289008841c0940409641c1c801d0000c40e0b419044105140401d00c28a1080030095455a000c0703114410001d44a21460103900144440401c0080c06d261040090307038094052001c0411085449459450742c07203040c45440c2801111044410b482d442c0308800560040d040a407400400600341083d41440c21801400c010030140c0d2600903032443c40340100380c64400b584010006035150b08070030510444141d207801100c65411420180500758540241c001d40c032080b166042030721880041403155403001505181c014560074000c01107010f0b0b030007040c0e0b50016009030b1600c480c044000800740d03090b03400b60812a81d02c00c480d414104480e40217a0044d0968610802c03c24010074010200c2208a9540310482d8010a01243d00b180c40c610780351150901 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 256434964 1250 256433714 256433731
    0x30e090601020d020d2304031406060118120f020301050f040201080705040305031207030e160f050a05030a120e040c0e0a0e060607081602060f072f010804021c1a 71
    0x4151403078003c06943c401c0d040c1803560404c8a00c11201000c01c1280d880400311a41100245507216501e0a00e2040c0b900e94400007046401031401185503503010f80d041c44448515024a09662441c2c060051440655018195681030741c0b5100080141c0d0284030b030701c1c420302125003220104d090a000042c8058030040ca001c0c1800001c00c4103202144000040d0b550750003045902c02c9656485c60030032070140000d04842da000d4440c00c402c03960310034900038170034080c4e64840460b151095964010009040d01c035100e0141c06801410090000c580714103c1000a611b960800d82d031001880030206e41200d0b09002c104001985001e1641290302d4259200c81c014203004124070000c0c00c2a5000913602d200f9200b0061450400145c110001c0c0c11114424103080d400030a0340740c9031061410b000a495101140480302401d40303c0d0300780c840010382041c40c01c14652410781102c41b20030010040d58004800740c0141c1e800340c080c8104444480f592008003044610440455240400e001030024003520040c00149 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 256436214 1250 256434964 256434973
    0x1090203061e131104090b18061e030d0905010210201b01021309140106080a0b040209030708031207030b060909250e0a0b07020d0609021804030e09060102 68
    0x14079601c80c0b03803000e402c5a60301c410b00c0050b082d07030780002c43d540c10f070044850703481e0300306200c0e1030201560001800481e44000000e10071400d81c0c608000010103841050500c4690800103c0c0881c10b0825110760001c0c19058140ea900000c40c00107483c10f11030018410000d070b0b58035010301042d6030602420155a0000e2070500449041142c400c40394900c80140300e44410012401c1096010700107041c100d0304540c90000c564034110304070130f11000071141c002c55400030300f0081c403c015904000c00c0103040f10407995404c111078440c003074500041d02036a444594416000c0c845550166001d0218000410100005541c2c42d03890f646600801c450060150045c14036000c00e0380c4242e00c8040846044000455103482c050b0348101c5038030500b1325030030b0b4078242000001d03076845c0351190802410303100c0940445042400c4d656a40c295542403090180094001c0345010310301c00055441d40140c00c001344021300c0d60504071a180a6005400400c940a0b0300180d05044403291600b0300343e42540e0480001e02c00b82 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 256437464 1250 256436214 256436221
    0xe01140f01030209090a0c030b041205030405060a0e070b03010f2907080d090506070918060506040306020a0c17030114010306030803150a0f0e010906060305010303020a0807020a05062101090203 85
    0x21550351814070010b4013690101000a016217828043d100810380e02c6048040c81ca512410310740c2c00f464045608807102820322111900d440d0240094078400e03980040204102c0d510f60901002400c42a40281800e10a00b000840d080c0012009036018103d2400310f000c00c0e525001c0004c180c9004052146001034041400179902000001261141a04003030015a030b2080504190300820b130048001e4144d02a440130b1050084c0d0120340c54045513031030021040c00140c9420300d40222000d0340305841e07100404100c00c10000e45c858000d81215503003410720000c0183c083c0c85001704500110061a0305500010051207140661966203000c00300030728042100310704642c0c40303840510026004c000904140850490a55035840326100548904080b62007400c0da900b540f45d00bc8002802003001c0c0380c0c1400d00120b0b186200c1c0c45401d040700e4250b401045250400d84070303c4400d900c41e00c000e0741c02c00002000401c1d241c031040d0007041c6c24030421000000e0f42001c4c1c1c421038590101030f04501c030814010002e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 256438714 1250 256437464 256437481
    0xd0504030b04060c1218021806030a0f1a0106020f0106090b09010e04060626010501091a0d03030f021602030607020a1709010203090d08031b19030b03030c010905010e0114 75
    0x59210ba4801c00009182041c68821788107036030401c0911071a01e0818000d000c0c07480c20010040312291003601c0100c8802154010340710100c1086500c1605584410310b90700c0030942e92040038201034041c2c0d030385c18101c43e4800344408186009070886005644441c54030150b02409129000003042c0700b044c02c01c481c4180708000380000c4010b00c60096044405008141800f44d182c0c807010041555400180c010b042910405d004c4400d55090300c5115443d0000001d80050707280a100900600390100316501c1400d001007202c1021000401d504050340c944d54420b0448061000b0700c650313200b043c50118009410320400d454998010702d9041150800d0f0030030000140940c00c8501c050f14000d840a442d40142e200407882e42c050003220030ba0042d6600d04c0e180a100a00c002580550303802d401d01c0b4a142c0581c00c07044880d110f2404522045562070352a00c0d403007071091340030000d010b100406aa18180c1011803040c00c0d00c0036910156081c0e55640130350103101409101303400c801f0351052032003601403910124 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 256439964 1250 256438714 256438733
    0x60806130c05101101050f100504140109090c090509060103060c0e0907030e011512050c030d021b0a030203060a050a06050d03050f0d11040b13090504081611030d03020c0d050403 78
    0x1e1a009543d0280034041890140c0d01c15038151044a008201510348845a591030680540301c40c00001d4205202003031904282c01500c0020038010311044240c1d180200190042c4030f8040265004c800e80040881c2420a44c00307924000c4502e48024441c0d5415420007000305d8004480c5501404107101e079030400354588480003940303c911400d00149800348103110034090b0505d10390100d015028400041500790200a240c110b9a00800c115030f078010303e01041c5a075401011205030013507440b140c6407c20260281c403450200f82d0b0041c00050a8030f9895000c6403a000c0b0a030388035450300342c9520400c4004569441030300002c0004603036102d60b032032180d2006000d9200d1a144407054020001d00c1c540111000d8104900300451180c50f66a540d58078420441e86403c00c50804c40e01071a4560005480c012a0007054011030704099001c3c070304030100c04209280e036500d010403a210a90020310600e55076090098103010040f0b900c0160361140701e0440c880c103207030651070b16506000c800d00051012072810074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 256441214 1250 256439964 256439969
    0xd0b010b0d110a08190e16030c080d1209020310090302010207031d01090603020309150103120305090a240615020705010915090e090a1b1d010b180f03010e01060806130c 74
    0xa28038507817075000020400c0548201590300d0392901c0382940a41e04040c1514610040340c1c0514484829103884250960b281d42840d40004005185418400a10349450b40141d407403600c010b00715440501000311003400e580c1004400c1d40580d50218010040c1a00008846002d962144240c0712a64039076001074280030755805001c2c1010b80c0403001510580c2c00f0012001b030100e813000901c2a943e968509030486401d8840484000303814140800c0c000760000486110041c6e00143c03407100441d5181e0703024010070002c00d020300e5580e100c01d4001580943c10030300808120b10344c2d020700812402c003000941030141c1c69004841e0081102028030708103078000c44940030341c1c482402403400c903100e40000b10314240380034030f0241081149140903c4040350700c0f20b10100701c803007900c0280304001007422030036110304c001d204200b03c1030313400c11543d2400080c2800852722540018090404401d64101007402c403140446003000c00d80d9160000d01922004200c60b81d44084003001c00009040716a44002100c1d5103403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 256442464 1250 256441214 256441231
    0x10615110109020904050303060a06031103010510020a02040f0b040605011e0513320d030e0603060406090203010b03010905341101020a090e060609090c090d0b010b0d110a08 76
    0x10054010300140c203400002e1515002411030b0308604280c1442500c0c1e50060b00c44520910714000b001903028080d01804d116a004554000d04507840c0005004482c5a60142c07a01180100740c20400143e6035071082c13004503004910b00041d0416004244012070b05140c001c541803282c204074901e40402c8441c3c21103e035615500e07040e61902c940300b00010b03000307004c0d4002c02a0408c4014030340d010110100f068070100506a4042002c0d0b038044424041d20703c1f42440090001040d45280191074248540190b4001d44050000a035a03a961169030040340c0083e004445260f40000c010010781d003590107041d4006600d03129803881c40341c42d1507041c0d03202c401140c014000c80c62030181e180c502c01c1c094045220240e40d80760003035554011881004242c5891800340c02c1101c0070107404240300b400c0404c191500300c00064030458403519440144092030300400c40d055805a9400e41c4d882c00104c080c0c034403e009203240329001d6156070a031403038032050758600032018015900034002c640c406030b0300030f00c5a074124200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 256443714 1250 256442464 256442477
    0x30a0609111e0102060a051608090c061605060c0406080f04020117070201200a050a1805031203040b060f1507020d06020c0a0309050d050d0f020f070f090509010615 72
    0xca2800010511045250a5110320620a001e141c0111000c5488441100744c2c00e440b00d6960b11000c41c3c00b16401560f02002501e036841c842c2c4250340c0640710b2190401000c004a07805403407460001076482d445440c103001055072103400001080000c2014a811080c4480c40d142000c0c14080000c100d460000c0c101c0b07069500c4c00000c5029a4041c008450300072000c1e100741c160314078100c50080c1c041d04291030341d14140d801c000210b81c5109030500030364a002000d070b0f44640c6800d64031101180c400300f181011018a1860a1001495035401c2060407201031005058940724981818030310f020b014000c087c1c500400b41d1660101056603030480042c130040c41c046449803214198004900b010b0700450000b8140e41c40020003043c0c150001903024100c034482c5e0744001c0d4098445041c0004442c10440046ca940d012480d070010840c018489001414a144102c418040e02542e200e46409440d900148103070504001c00c1c04502c06500030305a00503840c1000703115141c500541c1d1440c0e035000c4000c1314100700c407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 256444964 1250 256443714 256443731
    0x180d0e1206061020010903030b2d0402071403120403110a03020717030714010b2115060d0b01060e0103050603161a0705010515010e0d1e14010f09020a090b030a06 71
    0x840008000f04c00240082004200301d207030140040c1030b2020140d2083e01441f852203e0100114280200801c001d54050041104801030102a410101d07048400e103910450090a00c001000907003202c10145900450700d06190602901006083c030082d001904846801004240c001407140200c0b010b0b09111207660280d00c034414110300542e01c004250742c5c414068400c07010015040480310043c03c8800700708103807600181580500800c3d0ba128880d41000c24010303548009075040560008001c0e081d850210300940c1c40440c0b000090b0000c2021519802c92446107582c14031403070f98459001e070000c101100c004814500c4020480c4941708041c070400100c454410759110980c2c66496008009021a0800107800050030748514500e50008159800c2d00d041840c002001c016410380182070440c002042c4443c01b03070f400000507026615443e80b42c4040c814440d0901c00c0c2100346640c20300001c6e60451902c104104020140e200c40d072001e00789a05080c15541c00305030b500400d9030168002442d00c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 256446214 1250 256444964 256444997
    0x1504020d03110f0a030201060f0303080a1a09090105090601050108040f0b06030304170106230d030e0d0b04050a0b0604020309030901030218031f0612080f03180d0e12060610 76
    0x7000740090440760150300c0b000b03410030b43c00181003501240310760000d000880c0c8602030b01407030f20020710001e000a00700f85d001c07504240c2158070175501100718040e00900408103a0114510741070075141c030031080c2c1d9070b0410804840b4041c040103014240918015441e400c0c1500c2d02c512011003110040c1c8084010340c0807136001e0350100110b8005181050b40e401e41850400780c018001c00c0284284036541d88181040002856045990407180400070501080d00e40d00d42c40032282d090420391200d400203000c0c100710010407400030f0440d20461080c00201082c000c580741c15030200c4000340050740160b0050061003240314011090307414144007881c00503100e0781e5440024003840c444692031034041c080e034500510320742c2e01c007071100d5090101414140402a95003210303a4525189c40c0015220400174401e4450103c13040c0c3c011500a00e842c41c21310002c092507190f0307038105080c4500c440040303600021842014103028100b01c03500c040e00340c060200ca00c0c2c080040b661803004802d08504210b20000d034140d505 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 256447464 1250 256446214 256446227
    0xf040f031d0a0f030b0c04150f051e090319210905090c1b0304050603040b0a0e011a01020f030702090f091006080601051e0d030302030c041d0f01081504020d03 70
    0x300002410005450356505045000c07003c240803d0310050b42120000303048460031401c86040f034100c0c0d5810f4a156011283c122040b50070302c0c0151081000130000d20080300b0390344840a21801080040300c0e59640c2141c1051726054051316454403a100d440c041a000c0761203da14064503070112070140e010201182000c5071001c1c0e95400c00d9600031001c0e42030000482c07459014099a0b010ba440e032a800c0450f8201e800e50f00d0040d0711402c2c1d8031400400004d400200040c02994000e07041c402d021518034441c05a041c01c0d911081440000b29a0200704500650fa04003d50051150002c010f5480c010641d0045000284010000400c403800c220104640031403c001302f04211a180c01c040011a4451142c1911a0000e100e0144540c00c1c0700da010760b5010f480f50070406910300003003201d1603d0000355010340c00781d00010012109500288400a00c08414a010341081c240900050320307140360402d251400404180c00004450340084000710760601c840414035001901102c030381145c8a21441d088910 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 256448714 1250 256447464 256447517
    0x5011815031404050309040e03030f0a1109040c120609201b03070609020a06030c052b0606020a061104050901140a090908030601120c050403151b080f0f040f03 70
    0x2c1c1e503482010007042c0040400942072402d000c035000d004403141c0066840e07032804240c030040c2d8414419804101c1071142540400c480c41075080700d140c140603603800003408807002125070f2004107034941c407409440b2183d8880c0b000506911030041100d016066140c1c168902030040f003816184000884e43c1e28603121f495070100f074250718002c0301c3d551411880e10a01500314194100d0280d407a40101094450181c010820090901e68070030382070403030031400a100170280412584154010740e05182920084d0300403000030340360507001040a4045482d0841c111a00001300f0400e9001c240f10520050b074400c801c0f1411036040c04841d10005440720001007504400e98800148103281c86840001c001c24031020b584a002c00341ca03440d2050885001c05029501d103171101c400040d0080006200042c1d00c0700d0000d0301e02140802c00a29000c00111190049456a2440012441d00303000c104807141d0800c00d440c0e00c04c5240168083d00c0c2000e42e5a00e04502e42c00030000c0921419400300c440c640c084d1040c4061 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 256449964 1250 256448714 256448741
    0x6080c0f03041a1e09030f0702100c06020301081b0a030f0308070e0d200d02030601182705160e0f06041404060c030b0102060c070803090708060717010501181503 71
    0x900c0c00c01310744040214102c825511303080b604420001d1400f01c004801d9503543e0110028480c60702e0344650070882454102d540010500164000080208980e0b10146020300001c1e00180042d6040a0503038801040c100c1c6468030681e2106c0e002d0001405014a50443c5945828162555100c189090b2500e00c013015200350000c00d401c0da0f1100b03000008100b00c00e244c03007251013016000d4514052280c0c0d0079030020040e4142e17000038010480034440d00840c1040d00d06050300040e010042c2100c5408060345810300d000d6854440c036008051280c01e004044038010750400101456103050f5010640710b400400800031103050400040458440c2c1d0800d00043d41e0700c2d9074440a81c40d06240440041011034652400070f071401c010400a0750002601c0e502822001c0d0388a42072031803955a034100307a4070003408070425019a010004190303200304041401103901e500e0702e40840d582c4128207518800164444c9041101c4440e40c4140c0075489890720040da9640494a80400030b40c02080c0c0161000c0f20b200403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 256451214 1250 256449964 256450013
    0x7081e03150d121b0f05031804090c03030806010210020d0501080c0613090203060a05030303070918022511091303031401050619030b0a09020301090b0303030603060708090a0c060c050706080c0f0304 87
    0x501b00500130000704052400c009090007648429014081260b100c40d03030050004075121000d0012a004e82c501640c80072051040300c901481d240c0110007a6003211604100c02d5803034900502040005101000c1c0e40b5005035013550030850822a04034032800305101e0254010350001c080b900d03d0b120400e14102818000d0212692420000401401c0038442e12807200d840c81c4096609070144054000c8810448104480102200d81c00d0500031120542c4002200c009042d4144400d0a0f2a810505132040b0005480c001e50b4100c036050180a44038000301c03100c0816032850040c00035030b840100ba03e401d071082c60009500603454040c1071b00245a014031195105545503030010300300345150000d606136804000f0600c5205420410b060340e81c0010b69000354036810400018241c98480c5552550061100080720754000341501c40c09450005038120f10001000c540c041e1041c858100036840044c42203260248041c80c0c0b90180c007a80c0d0007a0740e80016803520010200d018440641d40c1528201c0380c028151 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 256452464 1250 256451214 256451243
    0x150f170609010b280317030f0901020901020d08100e0c03010602011505010807051b030d090507090204030b1f09020a17061e04020a050c0601060306080613020a050607081e03150d121b 80
    0x30101a00104c503851108c05ca01d0000070403151043c0203451818074103800a000e00295440140c40c0b441d4000c01e4003030f403203010420004490300c2c1c0c405564014103e081c800c1c0e640f541070910081c00d5500c80c1c0c000c0c101024070b8841c200441d9901ca43e17200c1d071202c10742c64101e849000f4101c0c0244c0c0302c41c1e81d4820082c1840f021404010200c0f190707004d0099a80320b001122440d030360301e0003c2401da010b20700c009403501c400000014541001803203444440c4000ea248041020348504181c1c017203030080048400040c600003000e01035400810540350b0015022a440b4800744504180c3c11400e06000c1d10301d90185070049070881415008205440e2600f212406a90071581c541e0300003401000c20384154881340c42800003003512051b078081342c440f41640141c0240001c904010a201c4954010a0220788a100c1000000d881c24400c0094840301d005c5141125601e00308030350b201041044049070036106049413813140b4006200041514140c40c901e0900704c0145812858080182c5c0000c080035096419000c0350 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 256453714 1250 256452464 256452503
    0x20427020c07061809110d110c01050a090611092115090a06150e070c032c150f09090603070b190201141306150f170609010b2803 57
    0x20071200d001d4100e281c4c1e60084d03840e00c995054640e50100030101040801202d180b0020380c2c0c10040c56403000304265443c21390b032104203900b110380459030b41d01d42ca541e8100341c1c410003840340682060103040034003680c10101c0103000100f070b51407a01c4824200410210381034a000c00c05100d1001140038100c000d850a1500b000303120348440300107104540300c61800d501c592801c68040710600942c1c65007015a0040c1e41c1e00d03401500d00307074207040d015824881c1c00c1043c02100e03400070310300341010105061141c8003520035500740b00c100520360242c41c2ea0500706104621008034500107a80c1e07104401c03203500c14503485000110f4101503403504905400740c8001400960211b03044510280050036038020001204624020200413100703840c08403107081e0140b407440102c0d42035086619181a11840c00b00c40e15070300c0200c446500c010768802281d0b5440d484903001484000d0100c294400c1080000b4400040038000059900040401401500c070030151583c039011414540310010f140e101c8482c02052180805 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 256454964 1250 256453714 256453727
    0xf030b010e090613020a03090b0603010c021509010204030c090b011d06180d05030a080f0708070905040c0306150f031103060d0f050f060f0906070249050703020d03020427020c0706 79
    0x506036000c0c9c0c1d9078408506203080503c1003000352141a40a0100000701c200300000041e8054075140702c84d134003400080082062015941e00405415000082041443c0009441c40d0f00d08443d100e075189070903000c0074940c0c596400b254080c0c640c1c60103142c105080180025808095801c0c0545584404200107031040c0c2c00c0b11900d4056150151546107942c2d4480e0203e0350400100c0c0e066002845000c02040b10303040c15084484001d84504022400340c0d140d819600032030803594000d40018254a2540024680610903510b00c05c01122000349507213807070808501d046220540007070125440020541c180b160900507118501b04000542e440e5042c801c641030501c10043d0f541e21a14040d801c0801d00c41400080c03049088180f80108160504c0188060030703c5020183c2042400407401c042035484101910b03000140d04a03507100d2a485d012503040091404482c00300e04c40a1510400051000308035021140c06850f04c64495401038240746090b24001c1d0240079029402489000c0300030810980105 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 256456214 1250 256454964 256454981
    0x308010303140c03070f050f0604030e04420902031003170c0d0f14070b04050114010b070b0606160b01030b061009050d02010504030b010303020d0f030b010e090613020a03 75
    0x2c0d501c54035100c44034410350403485242c00d90003240d03104200d9240003607808058181c0541c000c0055440c00032200744018200a02160110002072070a00e00c841c1c0303403402e44103401e040e640150512105941c0400c00c08103410342014030100910141403104d4810004140c040c0c00f1f019448401d40d04c90070b0403542015020010301040f070742203145203960b0707600c103610000380d4200ca01420018402d03c0381d020700940e00c44440e043d8103001c0242820007000e400b0007410080404900ca03415405140c03416051003404c40d028007002e420300000c44801007160310001026036280903000400c1110350b4407054005880d1744545e1040e540000c4520300030304240240811000c0c102d07401402c52a040d6511002008882ca1071000c507080801c0001ca024011810200e50070f0700407078810b0405501e026200e84030300407400d1003607000718016401081005036135944204c5036000e01407641002d0001c01c1c0c0c0000084c2c91400c1c800c155a0040084000080c0380356208e0501c0c082c3e0300b60445085503121340c2844020090003011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 256457464 1250 256456214 256456217
    0xd0206070f080910050a06090603030c1a010513020c0c0409081819031103010e03030f0901060509190b010903061d060c040803070b1906090606170f0c250308010303 72
    0x1e0000108a5000300d182070311900082c4050b00d042c40c4180c52070001404090480c0004554034000419491024031642003d540203480308180600382d407800c0026000d240c840281c000048400403c01d40d100c0301e142c0350148100420161f252001403c002e85005142c2410a50040c10042c0c410180103103640102200ca00d10b9042e90781082c100f50910641a004019421411003c20010008640303619014200070301c0c0280041200d9440c461241d28540080e500000d404071144140100c10b4000d1203190000c2400713955007055840c00510b844162810204203102403511004050002ea20a0305014040c66001303c081001c20f184440c45500452241d280314010710808010403486110340d0165011540d04400861500e0711940d92040320200240211503030340d0300d921540b03c1741e800d580600405030103642c0b0700154039440c14800a10803507101c40100c080544000920540c504c00300c180b26800300700050000ea545900c10518a16040f0007928000032034035080e031040405912000c0c1c2412a4041d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 256458714 1250 256457464 256457477
    0x7060905030616050301140609100503332110020c070609050609040b030a1a0a0b01080f040b090a020405100e010b040b090907031803030b09160e091003050d020607 72
    0xc02d07101042c1d50001501c3c12010880c01e000400c9130311052820314040c0d4801400c100e04002401020802080182d1a950081075020013040380c500800e04800f21410410504820480d040030500c0312090640d0b185030f8000d12040d580c0030500300a0455940d0045d588000303c601642100070010000d40103852203840c5030049010001c1c0080c440c0001c0c405860009050fa0b00d070500110401004000c0a440b00d0382600625500c40007241c54a02040c04a01c50058400c1e000d1601203005801c603000110101d05000e443c0007848044009502190350007a0f10000001840e150b1008840c0760510449000303500a0500d020020550040744d0304070201c1d41ca0104105040e6298078140030703240030311b000350b502c1244d050005106510300344c250180c202086d030400240c103a0f0000c000c0c03c422105044140d0102c0c0c0c80e0244070103141404000103030b01110051190400d00c59640c8020a91001c0c60304c018490360402001c01c40b40c460102448005507403001c12900c00088007200a9121030003100c500003c01d28 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 256459964 1250 256458714 256458721
    0x5060a230f0f03030d150e0103030f030c0c0f02130f1802040c0e15030c130e06030607090f0504050903091c03020f0d050405120f070f18140106080c0c070609050306 72
    0xc0c842110521a42c00402035400c080004030114003c0100c0c4a60131049400d80b8400140d0342d61004c0c526000c1c6010784d5400507600444100602641d55812000003001b1104000d0320102c1c1811020030082c0c0c0e41141d0a14201011002410181c12050403200e841d92400d800b124138000c10000e207404191090350240101f5054040954a20755a40b420980090400403245000303549070b00250b030b0059400c1c0560382420013401c624051040150421900c0200000174008249410010298800024075100e00481e05000e03103922500228807445001d0f9458038081410b9840a000f503e142510142010400909607044401000c013003d00941c00340c0111a00340c055070001103500010b00034541c954601c2c0c245404c062000c2c0d03400004041040303008140d110020700400344251402407c03d0080e030b01ea05c9052103440d5084500700d90304910028544903c1100301868404142e044a045040140c400d655808000035148241a1a01001d000b0180301088098001058605840090342116403d55 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 256461214 1250 256459964 256459969
    0x606030105010c0b220821090705011b0b0f060907050903030306010c1401050408090a060c0c05060a050c030f0406030507020102161e080f300a05060a230f 68
    0x21003801400d00261000d40d0210118520b00641a0030003900c0003c00d6a40d14420394031039002400841c2201e1032840000c02e540d111001200102130380b030446d240301e40541052046156103540e5880303824140440c0e411082d101400c400b0b803190b40131307400c0022801d4500c6e0840b180c0e212035808a940300c2c810001174001c202180c0c4540140d40d4801005030055133107460390401540c480811312011640d40c0300c0740c03e000700745107000e008090066204070000703600c4004003001c00a1445054100f0010451616540e2000c50440f480860480340c00703079842c0c3c2d0380b420102d00c01c42c5c0c1e0303100d4008204110700c00016a0703d4841311200c014000c850340750307a00704410b4403131000407820303403160001c02d900c40c140031004c2402188030440c013022000884800b040c00003c0319a100b14060f00860070801c640a008507030303c05039036603034a140c6421501c00c00b0940a680c41d6603c14150f03518004e018a00c202c0d0303840000601a403154a05d020260034580c64140401900c81120940c608040d10b1480c003901c0720002909550 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 256462464 1250 256461214 256461217
    0x3050109030f0c0f170403020d03020a0308060d05100b0316080607090f03080703030b031c110d080702120306010e090c03240d06020c030d0509071719020f0d0501060605120606 77
    0x45a03c4124154071200c55120840b0b1017071005a51012200108070000040e40c809401605043c42030b0054404100380b8280980b40e101c0040a503401170f4200c1c841c4400299010403007d1014851020014107600d50f000400d07d0a6607500e601814a03400000c04603500030001030b81c5120700001c1e07445100c83d98031124183c2110300d05104c000c04204003070000800090007508088074102e0b0160172034002c03203c00c174122192104003500302c2021404580f561f0223651000c0c05000b412078402d003013411080c10310050003951000241910001d00102002058403030b8420941e050001400030000030050414100318100c4d80d00958403100000d5401da251030003801071200c3c410310321500501051054081c3d4841c00081d50208404410a000130005280c02d1001031080e03a0240d03c0003002050740d42c0c20210b8029030517503803c0200e080f035030105640800440200f00b080e0a0142e056811002110b048808030704d03007501c5940010465400c00c0e001180c1140d00402410214010550103500c5895000610955 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 256463714 1250 256462464 256462487
    0x40906080a080d0506220e060f060a1a04030804030b0106021905100b04061a0c0d02031e0703170a0203090c09040b04060b13060801150509061021020403050109030f 72
    0x30000c02c2c0b1480f0a0004640d02840d4001005000318102c00c60000303085070398000c2c56102c20b01440d514201c2117a03d85081161550014140781002c0c4075042c2040002c1d00c900e25441000303030200304280d01003c03840345401500c1c01903900c00748154440da100c1c50b00e05a01038090003010010310814446441010340346500c0003c0390b804c840a400c8038119124818050941c13007031165002a2150b10000e90703a09040d40c285219a10000c542d40c584038584c8540e42004c1d07400030b29804652040c4000f00480d03005080300d0031004954510103580e1051440d007504c408110141d4100d041d618081001144152038005511a42c40c0e10140c8010b10709140401c00c41070801d8901411308400d450009000403440d600900c1410001071543c0c0004122140007020703510795401084099440784013100c50350900007440710203014212010307070040ca040d4000c141c1d80e4003041544003c003c0000a14114185008429400908400c2e03040d0350340c603240d081c0b860190204400c2180025041d00c0d0b0144600d2048090351074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 256464964 1250 256463714 256463723
    0x11031e031b06060915040608030f0c070e040804151103130303020c0307260109020a081b0907120504080904090b1b0309060103240c0c0b15060720090903040906080a 72
    0x1503848040103030b148821812007107a007181d47c1e0000842c1500c81000030308a00d13016004060358445500188504245840d805030f00c0b0111309106000014501030142c400307958621064040083e01c4180c01c275802c8803064005d0030305000010344001d01d805000c159500740c900a4003210182c4030341d01d06065031500e00d4803900303441c1c602d44194822042d09910b04481c00101540002c92003c4e404c0d00040c0c42060103911081241d8041e03105554000c0e181c0841c4a03e00e001141c4160032843c003003001134003049034201d070204420390f03030340000d001c01068405a4801c070030b0241040001c040a442d0603410540280c035403022908102c403c41003004091011244603030181400341400b40d2a507562800c1d0038002d035410801604000695801d5458035101d10980c60202c0d035184420380f14a4100300003207200261400ca042410101c0e109502e854120881d1212030340141079840501c0c02a43c01c400c0e04010580543e4458225418850034000010260099070380c07052042050b1030f51401644d54a1a4a640050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 256466214 1250 256464964 256464979
    0x31317090a060e030709020a02030c010b0109030f110a030605090d0e030105090c01080c04030b0a020306040b0d11010509030a0c060816030b01020705010c080d090c21080711031e031b0606 82
    0x214030392081c003144a00083c05001c8070220394035a2100030580e04485103100040e03101160900d40c00c0c0c0d0900950040107401e0070211446070844d1500d42c2c0102c420b6402030403030304555580201c01d8a5110707000c0000c1d9040442041035050194000d52101c2c0c020b0f500d0780008407011120300541c5010b01c102406120f90740020701001c510b200c010340b08600018540c0c0d51580041c440000424100c5088501c50071100500594928145003044103d5004200042c01214916109000038801d0580d01c000b24000b42001354440710b2510010786400e5000400030800b0030300341c2d0300141d5150040b000b1405914a186290100520a542201106d12988202d401a800400d0401070395005c0d1842110603406189110718041050101b0400d840031381d1800c5401c03040083d02002814112100600400300030301c800721401455840b60f0050b80560744010348010342c010701d2202203a0b0200540c14035075584d8680c0e52500c0807404051a12a004a56030b0707242c0000308034014100707a4010aa00384244002055803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 256467464 1250 256466214 256466219
    0x9060f0905010e2701090b072d120609111b12040605070f02030a030f08070f0804060b030102091302040504050f190b04110403060f0b010219060e030f031317090a 71
    0x59002220894110884138850b2800740002c28000c40e01030034042c0c6103100e890b007400b002c01000d5100010320b542d40c2250126003410000030415158844403c6440c25203200c4030802c894000900b00c036401482c0c00da180801c6000c1910a5030050195410349a020710031203a0004510b6031980d586810748030b0700b810108414485a4010400b03800e0203801a6404814100c495010918105094005038045030703041c2c0e00078a0050f804100744d07905c01c141d0301d40840d03003484881024081c5180900300030440d0340c491516542a0700c00350705440503400c005002d1244071202131406c0d00203501074051170b4003807400c110000c1d8000619070755141c0125036004500d006003442e8260100117001990066a00588490b0306070322040da02c03409440914041c1200103010f003c0c0045840445005c81e07407450540d040500c10010789042d074554003901542200d0082110300e00351001e1400e6104841c80c1c100320801c04003d011880030503030590801148a280b07801c1400300042c0410480d4003549034015400040108107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 256468714 1250 256467464 256467481
    0xf0b09180408120108031b2e1b050a09050105070309030f020d061d0106050d0209012601090c03150b15131a2802030d0c110709060f0905010e 62
    0x20180d10500490160b03040c43d52611980895400070380c8041c8051388042940c10880d10050300d505111050100100032450501018501c1480d03c0803a40c0300c00001c0300030b00320400030290050090b030700200e82154079050700c1420280164100700180000112032030408240e40d4007409c101c402180d007680f136259100c0d11315501c800e031130585000103d030042408803c00d0001203441c003929501c550b030264205054018180e0603821030b00b0307a5104600c01d8480b101454003688130300024030f066603569000c00e00c00c1e00c6066401c1c0343e140305d40340000602b5840c00851400f03110301214400d0070789206004000c40301031540158403d0b14412101960711001d18482c030780500000b980100100e030307480003140c40c5413696180300d4101c00c2034110315030380c00200004000c042c00380050b46100c481c1c80c0c41480c403901c80140e014000d43c0d90041d01032051003690b079202d801c5c48103401030001841842042040356030b07403030320b031003c103005400c0ca40b081d450b81a03004e002c080780030f9856000782d234166140b0708505030407a66622007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 256469964 1250 256468714 256468759
    0x8070f0810050915101403070e060105030405030c07030b180105090c04020927040203011506050f18060a20030412060b010c1a060109090c02030702190909030201060f0b09 75
    0x20041c84c422148011643d1410030f1001d4801c01c222440c0660081c6042800300c807500280d120a4420b400c02d9505020141d0351885164000d402032810646030780e02d03803400e00c0c51031003030040d52101441484400020041c503e107000e413081507035900c01c42203003c00e095901d081c1c6038255400e002c2034200c1088081a81410b0340600440d880040c810140d141d0340d80010b80012141403151132681580c2130401c015808c00340183e41d82c1d0f500843e40610714600d452402082c90141440d00c0422440001d9241114000782c40c60f44042271000701060f40e6041d803401d0290813045200440c14411070300b16a60248480c2c04810b590454495400c1c01c0e0300c0e002690344080040c00f01c05401d038180150071700c8000100e2410040a0007003000041e818105040420016010f4002a8040511a420001000c030102c2d070100c1a0340c4916415540202e082450b401201f41c51080e54100c54006841d0803011401d242c0d05410020854042c20342400141d0f071240c512081c0c91064288103600040001c000310f480840e03041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 256471214 1250 256469964 256469971
    0x81501050f0309011e09120f02070911030a0e3019050901090911040306091b18050604060506040e040203150a06030b060d05120f070213020301080d0915050a050d0c03050108070f081005 81
    0x10503680e18a0315400c1000331120303504c01e9019112804410000180c040b84900000c00305c100c00103000b1003820b48940d080e1418503001c0c111813070244001d240000e010030400e0350070b01d11140085000c03100428500034034a8003c0c04026002411144000602d10901d2040c00049442ea00b001031800d0b00390b442c1c04003d080c80749800c41c1c03034170001f041c0c50201d443c03228400710207410302c1122035024111031106203040e07480c060010392141e8035100301007059550300412201142c1000080700919500c500011b42040051100f010240030600200022104e4950001085d80d1048911925a841e01000c0c40080315518000410645c04076507001d1420812901a1100ca104c000850740750000c07660100f031413240c0503c092204103401000600c07083d207091004c100003503090314191407090b00c0c180d00800380c0d0700d00c0140341b41409400150444054070440c11124030140c0240300f80f00750f81400e40c00a000f0402442056118041c10601180e2042c102c0c090301c08440312200103092103038600e41c00400405014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 256472464 1250 256471214 256471217
    0x30c04022a0c1e03060703090302030d2a0801050612040512070501020703090e100306020f0d06030b060f01171f05090405061b070201081501050f0309011e09120f 71
    0x4454024081840994091001400d10003420600c1410818458241041250110f115070b200c400c0d03a1640d1000196a0350000c02c03444d0100d610480da040c140c0c210710900507051582c6082910046101442101066010840d40c0e80280000728800040700c50f50000e02403a980f01e20100940c0b01d1811101c03151540050040041d5816140241c0d207928195000702c0c0103c0c4d050350086848802d241e0021601c01c01000400b0a022140c500b0241040e0301c0d0210340001000554040f03801e020072400c0b02c040c0d8500c600d004400f04249a01c03030600061022003160b6552040c03200002e2000907511602d11801d400f03850324590308003522140c0050300e8400058584071905030041030002030755078a1031001c50055004a01405003800d08044c401c46921403214104858001000a1030060f40d110061950211544241415810314000100c540b4411241644504140401441071219040d8011301900c940e900f0b51041403800f4402034401e90b60410302c05091400c2403d010304446004004c071450b014440d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 256473714 1250 256472464 256472497
    0x608071217030906040b070e030a021e13090203010f090201050f0306010e04020a030f0507180b03090a021207330e04091b05011808120f040306060e060915030c0402 72
    0xd000c51102d400c11549007010350311010070302c0144011004003a8200650f49011001c0f110200b010944e5000c4420000340182c13054214140c2d508410042c5400546000704214219030038586040080c19920400768444e52802c41c01641850451081c034030f82c250b06844142c144020380d01c0948068200410b00d41c10f101034000710480c03035134440c4001c260480d07841e203001500d17819103030023070023144c50003400c1e134041c0021f41049443c50904042e51604072964040c107969a9030b107003c0b2840c10009800c8e0001e40280140080061351900801e5001c207980104010700f643c800ca48100c14030100309100100c541c606001e2810301850320410000e5400240600041010341840ea20310100c03807201c40c0e02c034040d08508802030200b907900181c5404881c6503c0300d0b621110b82440502503c450760981e5000c401880083c05010035101031055a0081d5000344041062640d07444d1704800180f0100c1c0d25500c5003d80d1800590a10720680b00701d4030344540500100303101d04000c0103004c020b5101c295a2140d5810 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 256474820 1106 256473714 256473743
    0x42018060607050109170406080903130e0c120a0f0c020307051510080708030a09090e0601030b0a09080c0708010c080f060105030705040915030201021006080712 71
    0x81280d400b660360006250544c010103030114020305d4008481034001003204035101800448035070380c40d1038006a90322110b440c8c49109903500f205034640c18010074840c0240d20015291712001e1551a0391829500c204400c08264040b50040f0403942c4a000007808020f40d4004c003031808100d0f0006606040c904da4505443d040007103891221409400d00180d0030484202c0c02500500d03800081d100300a0f11008216203ea0000000102080000c072000030078003001d209645100301c40d031015110300d900310742d00c021034081c002c0c0040c0462070300ea40c06a004150810010300c0d41c4c8201c180207041c1c1915110041d4259500141d0b00c4091082e00004c02c200c0c814070345103039644003e003440c101c2d41c4d03662951b0050710140110740100f15124501480580503100c400c0c4030700147d900076000c54006540441c148010b42d0082c6c01210030503084100c00f000710500c500e00c6600814810b8691a00845e0b = true := by decide +kernel

theorem cover : BRFrame.Cov 256294964 256474820 := by
  have h0 := BRFrame.cov_init 256294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 256294964 ≤ n) (h2 : n < 256474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
